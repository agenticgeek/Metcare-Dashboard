#!/usr/bin/env python3
"""METCARE live tracking dashboard: read-only GHL proxy + aggregator.

Run:  python3 server.py   (then open http://localhost:8765)
Config: .env with GHL_TOKEN and GHL_LOCATION_ID. The token never reaches the browser.
Campaign grouping rules live in campaigns.json (edit freely, reloaded on change).
"""
import json, os, re, sys, threading, time, urllib.parse, urllib.request, urllib.error
from collections import Counter, defaultdict
from datetime import datetime, timedelta, timezone
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from zoneinfo import ZoneInfo

HERE = os.path.dirname(os.path.abspath(__file__))
PARIS = ZoneInfo("Europe/Paris")
BASE = "https://services.leadconnectorhq.com"
HISTORY_DAYS = 120          # how far back contacts / appointments are kept
FAST_EVERY = 60             # seconds: contacts, payments, appointments, conversations
SLOW_EVERY = 300            # seconds: opportunities (full pull), forms
PEOPLE_EVERY = 600          # seconds: full contact-database pass (quality + campaign tags)
CAMP_FILE = os.path.join(HERE, "campaigns.json")


def load_env():
    p = os.path.join(HERE, ".env")
    if os.path.exists(p):
        for line in open(p):
            line = line.strip()
            if line and not line.startswith("#") and "=" in line:
                k, v = line.split("=", 1)
                os.environ.setdefault(k.strip(), v.strip().strip('"'))


load_env()
TOKEN = os.environ.get("GHL_TOKEN", "")
LOC = os.environ.get("GHL_LOCATION_ID", "")
PORT = int(os.environ.get("PORT", "8765"))
if not TOKEN or not LOC:
    sys.exit("Missing GHL_TOKEN / GHL_LOCATION_ID in .env")

HDR = {"Authorization": "Bearer " + TOKEN, "Version": "2021-07-28",
       "Accept": "application/json", "User-Agent": "metcare-dashboard/1.0"}


def ghl(path, **q):
    url = BASE + path + "?" + urllib.parse.urlencode({k: v for k, v in q.items() if v is not None})
    for attempt in range(4):
        try:
            with urllib.request.urlopen(urllib.request.Request(url, headers=HDR), timeout=30) as r:
                time.sleep(0.12)  # stay under the burst limit
                return json.load(r)
        except urllib.error.HTTPError as e:
            if e.code == 429 and attempt < 3:
                time.sleep(2 * (attempt + 1))
                continue
            raise RuntimeError("HTTP %s %s" % (e.code, e.read().decode()[:160]))
    raise RuntimeError("retries exhausted")


# ---------------------------------------------------------------- state
LOCK = threading.Lock()
S = {
    "contacts": {},       # id -> contact (last HISTORY_DAYS days)
    "people": {},         # id -> slim record for the WHOLE database (tags, flags)
    "people_ver": 0,
    "quality": None,
    "opps": [],
    "pipelines": [],
    "calendars": [],
    "events": [],
    "txns": [],
    "orders": [],
    "convs": [],
    "convs_total": 0,
    "forms_total": 0,
    "tags": 0,
    "contacts_total_seen": 0,
}
SYNC = {}   # source -> {ok, last, error, ms, rows}


def synced(name, fn):
    t0 = time.time()
    try:
        rows = fn()
        SYNC[name] = {"ok": True, "last": time.time(), "error": None, "rows": rows,
                      "ms": int((time.time() - t0) * 1000)}
    except Exception as e:  # keep serving last good data, flag the source
        prev = SYNC.get(name, {})
        SYNC[name] = {"ok": False, "last": prev.get("last"), "error": str(e)[:200],
                      "rows": prev.get("rows"), "ms": int((time.time() - t0) * 1000)}
        print("sync error", name, e, file=sys.stderr)


def iso(s):
    return datetime.fromisoformat(s.replace("Z", "+00:00"))


# ---------------------------------------------------------------- contact quality helpers
EMAIL_RE = re.compile(r"^[A-Za-z0-9._%+'\-]+@[A-Za-z0-9\-]+(\.[A-Za-z0-9\-]+)*\.[A-Za-z]{2,}$")
TYPO_DOMAINS = {"gmial.com", "gmai.com", "gamil.com", "gmail.con", "gmail.co", "gmil.com", "gmaill.com",
                "hotmial.com", "hotmail.con", "hotmal.com", "hotmai.com", "yaho.com", "yahooo.com",
                "yahoo.con", "outlok.com", "outlook.con", "orage.fr", "wanadoo.com", "free.com"}
# country calling code -> (allowed national lengths, mobile-number regex or None if unknown)
PHONE_RULES = {
    "33": ((9,), r"[67]"), "32": ((8, 9), r"4"), "41": ((9,), r"7[5-9]"), "212": ((9,), r"[67]"),
    "213": ((9,), r"[567]"), "216": ((8,), r"[2459]"), "590": ((9,), r"69[01]"), "596": ((9,), r"69[67]"),
    "594": ((9,), r"694"), "262": ((9,), r"69[23]"), "44": ((10,), r"7"), "34": ((9,), r"[67]"),
    "49": ((10, 11), r"1[567]"), "39": ((9, 10), r"3"), "351": ((9,), r"9"), "1": ((10,), None),
}


def classify_phone(raw):
    """-> (valid, kind, reason). kind: mobile | landline | unknown. Format check only, not a carrier lookup."""
    p = re.sub(r"[\s().\-]", "", raw or "")
    if p.startswith("00"):
        p = "+" + p[2:]
    if not p.startswith("+"):
        return False, None, "no_country_code"
    if not re.fullmatch(r"\+\d+", p):
        return False, None, "not_a_number"
    d = p[1:]
    if not 7 <= len(d) <= 15 or d[0] == "0":
        return False, None, "wrong_length"
    for n in (3, 2, 1):
        rule = PHONE_RULES.get(d[:n])
        if rule:
            lens, mob = rule
            nat = d[n:]
            if len(nat) not in lens:
                return False, None, "wrong_length"
            if mob is None:
                return True, "unknown", None
            return True, ("mobile" if re.match(mob, nat) else "landline"), None
    return True, "unknown", None


def optout(c, ch):
    return bool(c.get("dnd")) or ((c.get("dndSettings") or {}).get(ch) or {}).get("status") == "active"


def is_import(c):
    return any((a.get("medium") or "").lower() == "csv_import" for a in c.get("attributions") or [])


def is_test(c):
    em = (c.get("email") or "").lower()
    nm = (c.get("contactName") or "").lower()
    return ("agentum" in em or "agentum" in nm or nm.startswith("test") or " test" in nm
            or "mahnoorsaleem" in em or nm == "mahnoor saleem")


def tally(q, c, tags, rec):
    q["total"] += 1
    em = (c.get("email") or "").strip()
    if not em:
        q["email_missing"] += 1
    else:
        q["email_has"] += 1
        dom = em.rsplit("@", 1)[-1].lower()
        if not EMAIL_RE.match(em):
            q["email_malformed"] += 1
        elif dom in TYPO_DOMAINS:
            q["email_typo"] += 1
        elif "[email] - bounced" in tags or "[email] - spam" in tags:
            q["email_flagged"] += 1
        else:
            q["email_valid"] += 1
        if optout(c, "Email") or "[email] - unsubscribe" in tags:
            q["email_optout"] += 1
    ph = (c.get("phone") or "").strip()
    if not ph:
        q["phone_missing"] += 1
        return
    q["phone_has"] += 1
    ok, kind, reason = classify_phone(ph)
    if not ok:
        q["phone_invalid"] += 1
        q["phone_invalid_" + reason] += 1
        return
    q["phone_valid"] += 1
    q["phone_" + kind] += 1
    if kind in ("mobile", "unknown"):
        q["wa_likely"] += 1
        rec["wl"] = True
        if optout(c, "WhatsApp"):
            q["wa_optout"] += 1


def pull_wa_contacts():
    """Contacts whose most recent conversation channel is WhatsApp (a lower bound of reachable numbers)."""
    out, params, prev = set(), {"locationId": LOC, "limit": 100}, None
    for _ in range(150):
        d = ghl("/conversations/search", **params)
        cs = d.get("conversations", [])
        for c in cs:
            if c.get("lastMessageType") == "TYPE_WHATSAPP" and c.get("contactId"):
                out.add(c["contactId"])
        if len(cs) < 100:
            break
        nxt = cs[-1].get("lastMessageDate")
        if not nxt or nxt == prev:
            break
        prev = nxt
        params["startAfterDate"] = nxt
    return out


def sync_people():
    params = {"locationId": LOC, "limit": 100}
    people, q_all, q_noimp = {}, Counter(), Counter()
    while True:
        d = ghl("/contacts/", **params)
        cs = d.get("contacts", [])
        for c in cs:
            tags = [t.lower() for t in c.get("tags", [])]
            imp = is_import(c)
            rec = {"t": tags, "a": c["dateAdded"], "imp": imp, "test": is_test(c)}
            tally(q_all, c, tags, rec)
            if not imp:
                tally(q_noimp, c, tags, {})
            people[c["id"]] = rec
        m = d.get("meta", {})
        if not cs or not m.get("nextPageUrl"):
            break
        params["startAfter"], params["startAfterId"] = m["startAfter"], m["startAfterId"]
    wa_ok = True
    try:
        wa = pull_wa_contacts()
    except Exception as e:
        print("whatsapp conversations pull failed", e, file=sys.stderr)
        wa, wa_ok = set(), False
    for q, skip_imp in ((q_all, False), (q_noimp, True)):
        q["wa_confirmed"] = sum(1 for i, r in people.items()
                                if i in wa and r.get("wl") and not (skip_imp and r["imp"]))
    with LOCK:
        S["people"] = people
        S["people_ver"] += 1
        S["quality"] = {"all": dict(q_all), "noimp": dict(q_noimp), "wa_ok": wa_ok}
    return len(people)


def sync_contacts():
    cutoff = datetime.now(timezone.utc) - timedelta(days=HISTORY_DAYS)
    with LOCK:
        known_max = max((iso(c["dateAdded"]) for c in S["contacts"].values()), default=None)
    stop_before = (known_max - timedelta(days=2)) if known_max else cutoff
    params = {"locationId": LOC, "limit": 100}
    got = {}
    while True:
        d = ghl("/contacts/", **params)
        cs = d.get("contacts", [])
        for c in cs:
            got[c["id"]] = c
        oldest = min((iso(c["dateAdded"]) for c in cs), default=None)
        m = d.get("meta", {})
        if not cs or not m.get("nextPageUrl") or oldest < stop_before:
            break
        params["startAfter"], params["startAfterId"] = m["startAfter"], m["startAfterId"]
    total = d.get("meta", {}).get("total")
    with LOCK:
        S["contacts"].update(got)
        S["contacts"] = {k: v for k, v in S["contacts"].items() if iso(v["dateAdded"]) >= cutoff}
        if total:
            S["contacts_total_seen"] = total
    return len(S["contacts"])


def sync_meta():
    pl = ghl("/opportunities/pipelines", locationId=LOC).get("pipelines", [])
    cal = ghl("/calendars/", locationId=LOC).get("calendars", [])
    tags = ghl("/locations/%s/tags" % LOC).get("tags", [])
    with LOCK:
        S["pipelines"], S["calendars"], S["tags"] = pl, cal, len(tags)
    return len(pl)


def sync_opps():
    params = {"location_id": LOC, "limit": 100}
    out = []
    while True:
        d = ghl("/opportunities/search", **params)
        out += d.get("opportunities", [])
        m = d.get("meta", {})
        if not d.get("opportunities") or not m.get("nextPageUrl"):
            break
        params["startAfter"], params["startAfterId"] = m["startAfter"], m["startAfterId"]
    slim = []
    for o in out:  # drop contact PII; keep what the dashboard needs
        slim.append({k: o.get(k) for k in ("id", "pipelineId", "pipelineStageId", "status",
                                           "monetaryValue", "createdAt", "lastStatusChangeAt",
                                           "source", "name", "contactId")})
    with LOCK:
        S["opps"] = slim
    return len(slim)


def sync_payments():
    def pull(path):
        rows, off = [], 0
        while True:
            d = ghl(path, altId=LOC, altType="location", limit=100, offset=off)
            rows += d.get("data", [])
            off += 100
            if off >= d.get("totalCount", 0) or not d.get("data"):
                return rows
    tx, od = pull("/payments/transactions"), pull("/payments/orders")
    with LOCK:
        S["txns"], S["orders"] = tx, od
    return len(tx)


def sync_events():
    now = int(time.time() * 1000)
    start, end = now - HISTORY_DAYS * 86400000, now + 45 * 86400000
    with LOCK:
        cals = list(S["calendars"])
    ev = []
    for c in cals:
        try:
            d = ghl("/calendars/events", locationId=LOC, calendarId=c["id"], startTime=start, endTime=end)
        except RuntimeError as e:
            print("calendar", c.get("name"), e, file=sys.stderr)
            continue
        for e in d.get("events", []):
            if e.get("deleted"):
                continue
            ev.append({"id": e["id"], "cal": c["id"], "start": e.get("startTime"),
                       "added": e.get("dateAdded"), "status": e.get("appointmentStatus"),
                       "title": e.get("title", ""), "contact": e.get("contactId")})
    with LOCK:
        S["events"] = ev
    return len(ev)


def sync_convs():
    d = ghl("/conversations/search", locationId=LOC, limit=100)
    with LOCK:
        S["convs"] = [{"t": c.get("lastMessageType"), "d": c.get("lastMessageDate"),
                       "dir": c.get("lastMessageDirection")} for c in d.get("conversations", [])]
        S["convs_total"] = d.get("total", 0)
    return S["convs_total"]


def sync_forms():
    d = ghl("/forms/submissions", locationId=LOC, limit=1)
    with LOCK:
        S["forms_total"] = d.get("meta", {}).get("total", 0)
    return S["forms_total"]


def refresher():
    synced("Pipelines & calendars", sync_meta)
    synced("Contacts", sync_contacts)
    synced("Payments", sync_payments)
    synced("Appointments", sync_events)
    synced("Conversations", sync_convs)
    synced("Opportunities", sync_opps)
    synced("Forms", sync_forms)
    synced("Contact database", sync_people)
    last_slow = last_people = time.time()
    while True:
        time.sleep(FAST_EVERY)
        synced("Contacts", sync_contacts)
        synced("Payments", sync_payments)
        synced("Appointments", sync_events)
        synced("Conversations", sync_convs)
        if time.time() - last_slow >= SLOW_EVERY:
            synced("Pipelines & calendars", sync_meta)
            synced("Opportunities", sync_opps)
            synced("Forms", sync_forms)
            last_slow = time.time()
        if time.time() - last_people >= PEOPLE_EVERY:
            synced("Contact database", sync_people)
            last_people = time.time()


# ---------------------------------------------------------------- campaigns config
DEFAULT_CAMPAIGNS = [
    {"name": "Octobre Rose", "tags": ["rose"]},
    {"name": "Masterclass Praticienne", "tags": ["praticienne", "pro-lead-masterclass", "programme master class"]},
    {"name": "Masterclass Infirmière / Kiné", "tags": ["infirmi", "kin[eé]"]},
    {"name": "Patient Expert / Patient tunnel", "tags": ["patient expert", "patient_expert", "patient tunnel", "patient-lead", "patient-qualifie", "optin patient"]},
    {"name": "Webinaires", "tags": ["webinaire"]},
    {"name": "Post-Op Repair", "tags": ["post.?op repair"]},
    {"name": "Brazil Retreat / Destinations", "tags": ["destination", "guide (albanie|br[eé]sil|espagne|thailande)", "brazil"]},
    {"name": "Appel des Âmes", "tags": ["appel des (ames|âmes)", "r[eé]servation appel"]},
    {"name": "My IA", "tags": ["my ia", "ia assistant", r"^\[ia\]"]},
    {"name": "Full Body / Initiation (e-learning)", "tags": ["full.?body", "initiation", "prevente", "360ide"]},
    {"name": "Coaching Pro", "tags": ["coaching"]},
    {"name": "Black Friday", "tags": ["black friday"]},
    {"name": "Partenaires (Alma, Dohane)", "tags": ["alma", "dohane"]},
    {"name": "Site / Newsletter / Contact", "tags": ["newsletter", "site internet", "formulaire de contact"]},
    {"name": "Shop (Shopify)", "tags": ["shopify"]},
    {"name": "Chirurgiens (liste)", "tags": ["surgeons"]},
]
_CAMP_CACHE = {"key": None, "names": None, "idx": None}


def campaign_index(people, ver):
    """-> (campaign names in config order, {contact id: [names]}). Cached until the file or the people map changes."""
    if not os.path.exists(CAMP_FILE):
        with open(CAMP_FILE, "w") as f:
            json.dump({"_help": "Each campaign groups contacts whose tags match any regex (case-insensitive). "
                                "Edit and save; the dashboard reloads it.",
                       "campaigns": DEFAULT_CAMPAIGNS}, f, ensure_ascii=False, indent=1)
    key = (os.path.getmtime(CAMP_FILE), ver)
    if _CAMP_CACHE["key"] == key:
        return _CAMP_CACHE["names"], _CAMP_CACHE["idx"]
    try:
        raw = json.load(open(CAMP_FILE)).get("campaigns", [])
    except Exception as e:
        print("campaigns.json invalid:", e, file=sys.stderr)
        raw = DEFAULT_CAMPAIGNS
    cfg = []
    for c in raw:
        try:
            cfg.append((c["name"], [re.compile(x, re.I) for x in c.get("tags", [])]))
        except re.error as e:
            print("bad regex in campaign", c.get("name"), e, file=sys.stderr)
    idx = {}
    for cid, p in people.items():
        hit = [n for n, rx in cfg if any(r.search(t) for r in rx for t in p["t"])]
        if hit:
            idx[cid] = hit
    names = [n for n, _ in cfg]
    _CAMP_CACHE.update(key=key, names=names, idx=idx)
    return names, idx


# ---------------------------------------------------------------- aggregation
def pday(dt):
    return dt.astimezone(PARIS).date()


def mask(name):
    parts = (name or "").strip().split()
    if not parts:
        return "—"
    return parts[0].title() + (" " + parts[-1][0].upper() + "." if len(parts) > 1 else "")


COUNTRIES = [("+33", "France"), ("+32", "Belgium"), ("+41", "Switzerland"), ("+212", "Morocco"),
             ("+213", "Algeria"), ("+216", "Tunisia"), ("+590", "Guadeloupe"), ("+262", "Réunion"),
             ("+596", "Martinique"), ("+44", "UK"), ("+34", "Spain"), ("+1", "US/CA"),
             ("+352", "Luxembourg"), ("+49", "Germany"), ("+39", "Italy"), ("+351", "Portugal")]


def country(phone):
    p = phone or ""
    if not p:
        return "No phone"
    for pre, n in sorted(COUNTRIES, key=lambda x: -len(x[0])):
        if p.startswith(pre):
            return n
    return "Other"


# open opportunities parked in stages whose name says the deal is dead (GHL status stays "open")
LOST_STAGE_RE = re.compile(r"perdu|lost|non qualifi|pas int[ée]ress|erron|d[ée]sabonn|annul", re.I)


def series(days, today):
    return [today - timedelta(days=i) for i in range(days - 1, -1, -1)]


def build(days, exclude_test, exclude_import=True):
    today = datetime.now(PARIS).date()
    start = today - timedelta(days=days - 1)
    pstart = start - timedelta(days=days)
    daykeys = series(days, today)
    with LOCK:
        contacts = list(S["contacts"].values())
        people, ver, quality = S["people"], S["people_ver"], S["quality"]
        opps, pls, cals = list(S["opps"]), list(S["pipelines"]), list(S["calendars"])
        events, txns = list(S["events"]), list(S["txns"])
        convs, convs_total, forms_total = list(S["convs"]), S["convs_total"], S["forms_total"]

    # contact ids to leave out (CSV imports / test contacts), from the full database map + the 120-day cache
    excluded = set()
    for cid, p in people.items():
        if (exclude_import and p["imp"]) or (exclude_test and p["test"]):
            excluded.add(cid)
    for c in contacts:
        if (exclude_import and is_import(c)) or (exclude_test and is_test(c)):
            excluded.add(c["id"])
    n_import = sum(1 for c in contacts if is_import(c) and start <= pday(iso(c["dateAdded"])) <= today)
    contacts = [c for c in contacts if c["id"] not in excluded]
    opps = [o for o in opps if o.get("contactId") not in excluded]
    events = [e for e in events if e.get("contact") not in excluded]
    txns = [t for t in txns if t.get("contactId") not in excluded]

    def inr(d, a=start, b=today):
        return a <= d <= b

    # ---- contacts
    cin = [c for c in contacts if inr(pday(iso(c["dateAdded"])))]
    cprev = [c for c in contacts if inr(pday(iso(c["dateAdded"])), pstart, start - timedelta(days=1))]
    leads_day = Counter(pday(iso(c["dateAdded"])) for c in cin)
    src = Counter((c.get("source") or "(none)") for c in cin)
    seg = Counter(t for c in cin for t in c.get("tags", []) if not t.startswith("[email]"))
    ctry = Counter(country(c.get("phone")) for c in cin)

    def attributed(c):
        for a in c.get("attributions") or []:
            s = (a.get("utmSessionSource") or "").lower()
            if s and s not in ("crm workflows", "crm ui", "direct traffic", "manual"):
                return True
            if a.get("utmSource") or a.get("utmCampaign") or a.get("fbclid"):
                return True
        return False

    def paid_meta(c):
        for a in c.get("attributions") or []:
            blob = " ".join(str(a.get(k, "")) for k in ("utmSource", "medium", "utmSessionSource", "utmMedium")).lower()
            if any(w in blob for w in ("meta", "facebook", "instagram", "fb", "paid", "cpc")):
                return True
        return False

    health = {
        "total": len(cin),
        "with_source": sum(1 for c in cin if c.get("source")),
        "with_attribution": sum(1 for c in cin if attributed(c)),
        "meta_paid": sum(1 for c in cin if paid_meta(c)),
        "with_tunnel_tag": sum(1 for c in cin if any(t.startswith("tunnel:") for t in c.get("tags", []))),
        "with_phone": sum(1 for c in cin if c.get("phone")),
        "with_email": sum(1 for c in cin if c.get("email")),
    }

    # ---- appointments
    calname = {c["id"]: c.get("name", "?").strip() for c in cals}
    now = datetime.now(timezone.utc)

    def norm(e):
        st = (e.get("status") or "").lower()
        if st in ("showed", "noshow", "cancelled", "invalid"):
            return {"invalid": "cancelled"}.get(st, st)
        try:
            return "upcoming" if iso(e["start"]) > now else "unmarked"
        except Exception:
            return "unmarked"

    def booked_day(e):
        return pday(iso(e["added"])) if e.get("added") else None

    ein = [e for e in events if (booked_day(e) and inr(booked_day(e)))]
    eprev = [e for e in events if (booked_day(e) and inr(booked_day(e), pstart, start - timedelta(days=1)))]
    book_day = Counter(booked_day(e) for e in ein)
    held = [e for e in events if e.get("start") and inr(pday(iso(e["start"])))]
    by_cal = defaultdict(Counter)
    for e in held:
        by_cal[e["cal"]][norm(e)] += 1
        by_cal[e["cal"]]["total"] += 1
    cal_rows = []
    for cid, c in by_cal.items():
        decided = c["showed"] + c["noshow"]
        cal_rows.append({"name": calname.get(cid, cid), "total": c["total"], "showed": c["showed"],
                         "noshow": c["noshow"], "cancelled": c["cancelled"], "upcoming": c["upcoming"],
                         "unmarked": c["unmarked"], "show_rate": (c["showed"] / decided) if decided else None})
    cal_rows.sort(key=lambda r: -r["total"])
    tot = Counter(norm(e) for e in held)
    decided = tot["showed"] + tot["noshow"]
    upcoming = sorted((e for e in events if norm(e) == "upcoming"), key=lambda e: e["start"])[:8]

    # ---- payments
    OK = ("succeeded", "partially_refunded")

    def tday(t):
        return pday(iso(t["createdAt"]))

    def net(t):
        return float(t.get("amount") or 0) - float(t.get("amountRefunded") or 0)

    tin = [t for t in txns if inr(tday(t))]
    tprev = [t for t in txns if inr(tday(t), pstart, start - timedelta(days=1))]
    rev_day = defaultdict(float)
    for t in tin:
        if t.get("status") in OK:
            rev_day[tday(t)] += net(t)
    st = defaultdict(lambda: [0, 0.0])
    for t in tin:
        st[t.get("status", "?")][0] += 1
        st[t.get("status", "?")][1] += float(t.get("amount") or 0)
    ok_in = [t for t in tin if t.get("status") in OK]
    revenue = sum(net(t) for t in ok_in)
    revenue_prev = sum(net(t) for t in tprev if t.get("status") in OK)
    gross = sum(float(t.get("amount") or 0) for t in ok_in)
    pending = sum(float(t.get("amount") or 0) for t in tin if t.get("status") == "pending")
    refunded = sum(float(t.get("amountRefunded") or 0) for t in tin)
    by_product = defaultdict(lambda: [0, 0.0])
    by_method = defaultdict(lambda: [0, 0.0])
    for t in ok_in:
        k = t.get("entitySourceName") or t.get("entitySourceType") or "—"
        by_product[k][0] += 1
        by_product[k][1] += net(t)
        m = t.get("paymentProviderType") or t.get("entitySourceType") or "other"
        by_method[m][0] += 1
        by_method[m][1] += net(t)
    prod_rows = sorted(({"name": k, "sales": v[0], "amount": v[1]} for k, v in by_product.items()),
                       key=lambda r: -r["amount"])[:8]
    recent_pay = [{"at": t["createdAt"], "amount": float(t.get("amount") or 0), "status": t.get("status"),
                   "name": mask(t.get("contactName")), "src": t.get("entitySourceName") or t.get("entitySourceType")}
                  for t in sorted(txns, key=lambda t: t["createdAt"], reverse=True)[:8]]
    top_pay = [{"at": t["createdAt"], "amount": net(t), "name": mask(t.get("contactName")),
                "src": t.get("entitySourceName") or t.get("entitySourceType")}
               for t in sorted(ok_in, key=net, reverse=True)[:8]]
    # monthly received (last 12 calendar months, Paris)
    months = []
    y, m = today.year, today.month
    for _ in range(12):
        months.append("%04d-%02d" % (y, m))
        m -= 1
        if m == 0:
            y, m = y - 1, 12
    months.reverse()
    mon = {k: [0.0, 0] for k in months}
    for t in txns:
        if t.get("status") in OK:
            k = tday(t).strftime("%Y-%m")
            if k in mon:
                mon[k][0] += net(t)
                mon[k][1] += 1
    old_pending = [t for t in txns if t.get("status") == "pending" and (now - iso(t["createdAt"])).days >= 7]
    failed_in = [t for t in tin if t.get("status") == "failed"]
    finance = {
        "received": revenue, "gross": gross, "refunded": refunded, "sales": len(ok_in),
        "avg_ticket": (revenue / len(ok_in)) if ok_in else None,
        "pending": pending, "pending_n": sum(1 for t in tin if t.get("status") == "pending"),
        "failed": sum(float(t.get("amount") or 0) for t in failed_in), "failed_n": len(failed_in),
        "old_pending_n": len(old_pending),
        "old_pending": sum(float(t.get("amount") or 0) for t in old_pending),
        "monthly": [{"m": k, "amount": round(v[0], 2), "n": v[1]} for k, v in mon.items()],
        "methods": [{"name": k, "n": v[0], "amount": v[1]} for k, v in sorted(by_method.items(), key=lambda kv: -kv[1][1])],
        "top": top_pay,
    }

    # ---- pipelines
    stagename = {s["id"]: s["name"] for p in pls for s in p["stages"]}
    prow = {p["id"]: {"id": p["id"], "name": p["name"], "new": 0, "open": 0, "open_value": 0.0, "won": 0,
                      "won_value": 0.0, "lost": 0, "lost_total": 0, "won_total": 0, "won_value_total": 0.0,
                      "abandoned": 0, "stale": 0, "lost_stage": 0, "stages": Counter(), "order": [s["name"] for s in p["stages"]]}
            for p in pls}
    opps_day = Counter()
    n_new = n_new_prev = 0
    stale_cut = now - timedelta(days=90)
    for o in opps:
        r = prow.get(o["pipelineId"])
        if not r:
            continue
        created = pday(iso(o["createdAt"]))
        if inr(created):
            r["new"] += 1
            n_new += 1
            opps_day[created] += 1
        elif inr(created, pstart, start - timedelta(days=1)):
            n_new_prev += 1
        val = float(o.get("monetaryValue") or 0)
        chg = pday(iso(o["lastStatusChangeAt"]))
        if o["status"] == "open":
            r["open"] += 1
            r["open_value"] += val
            sname = stagename.get(o["pipelineStageId"], "?")
            r["stages"][sname] += 1
            if LOST_STAGE_RE.search(sname):
                r["lost_stage"] += 1
            if iso(o["createdAt"]) < stale_cut:
                r["stale"] += 1
        elif o["status"] == "won":
            r["won_total"] += 1
            r["won_value_total"] += val
            if inr(chg):
                r["won"] += 1
                r["won_value"] += val
        elif o["status"] == "lost":
            r["lost_total"] += 1
            if inr(chg):
                r["lost"] += 1
        elif o["status"] == "abandoned":
            r["abandoned"] += 1
    pipe_rows = []
    for r in prow.values():
        if r["new"] or r["open"] or r["won_total"] or r["lost_total"] or r["abandoned"]:
            r["stages"] = [{"name": nm, "n": r["stages"].get(nm, 0)} for nm in r["order"]]
            del r["order"]
            pipe_rows.append(r)
    pipe_rows.sort(key=lambda r: (-r["new"], -r["open"]))
    pt = {k: sum(r[k] for r in pipe_rows) for k in ("open", "open_value", "won", "won_value", "lost", "lost_total",
                                                    "won_total", "won_value_total", "abandoned", "stale", "new", "lost_stage")}

    # ---- campaigns (grouped by contact tags; see campaigns.json)
    names, cidx = campaign_index(people, ver)
    NOCAMP = "(no campaign tag)"
    crow = {n: {"name": n, "tagged": 0, "leads": 0, "bookings": 0, "held": 0, "showed": 0, "noshow": 0,
                "opps": 0, "open": 0, "open_value": 0.0, "won": 0, "lost": 0, "sales": 0, "revenue": 0.0}
            for n in names + [NOCAMP]}

    def cn(cid):
        return cidx.get(cid) or [NOCAMP]
    for cid, p in people.items():
        if cid in excluded:
            continue
        for n in cn(cid):
            crow[n]["tagged"] += 1
            if inr(pday(iso(p["a"]))):
                crow[n]["leads"] += 1
    for e in ein:
        for n in cn(e.get("contact")):
            crow[n]["bookings"] += 1
    for e in held:
        k = norm(e)
        for n in cn(e.get("contact")):
            crow[n]["held"] += 1
            if k == "showed":
                crow[n]["showed"] += 1
            elif k == "noshow":
                crow[n]["noshow"] += 1
    for o in opps:
        created = pday(iso(o["createdAt"]))
        chg = pday(iso(o["lastStatusChangeAt"]))
        for n in cn(o.get("contactId")):
            c = crow[n]
            if inr(created):
                c["opps"] += 1
            if o["status"] == "open":
                c["open"] += 1
                c["open_value"] += float(o.get("monetaryValue") or 0)
            elif o["status"] == "won" and inr(chg):
                c["won"] += 1
            elif o["status"] == "lost" and inr(chg):
                c["lost"] += 1
    for t in ok_in:
        for n in cn(t.get("contactId")):
            crow[n]["sales"] += 1
            crow[n]["revenue"] += net(t)
    camp_rows = []
    for c in crow.values():
        if c["tagged"] or c["bookings"] or c["revenue"]:
            dec = c["showed"] + c["noshow"]
            c["show_rate"] = (c["showed"] / dec) if dec else None
            camp_rows.append(c)
    camp_rows.sort(key=lambda c: (c["name"] == NOCAMP, -c["leads"], -c["revenue"]))

    # ---- conversations
    chan = Counter((c["t"] or "?").replace("TYPE_", "") for c in convs)

    daily = [{"d": d.isoformat(), "leads": leads_day.get(d, 0), "bookings": book_day.get(d, 0),
              "revenue": round(rev_day.get(d, 0), 2), "opps": opps_day.get(d, 0)} for d in daykeys]
    recent = sorted(contacts, key=lambda c: c["dateAdded"], reverse=True)[:10]

    qkey = "noimp" if exclude_import else "all"
    database = None
    if quality:
        database = {"q": quality[qkey], "wa_ok": quality["wa_ok"], "total_all": quality["all"].get("total", 0),
                    "imports": quality["all"].get("total", 0) - quality["noimp"].get("total", 0),
                    "excluding_imports": exclude_import}

    return {
        "generated": datetime.now(timezone.utc).isoformat(),
        "period": {"days": days, "from": start.isoformat(), "to": today.isoformat()},
        "exclude_test": exclude_test, "exclude_import": exclude_import, "imported": n_import,
        "sync": {k: {**v} for k, v in SYNC.items()},
        "kpis": {
            "leads": len(cin), "leads_prev": len(cprev),
            "opps": n_new, "opps_prev": n_new_prev,
            "bookings": len(ein), "bookings_prev": len(eprev),
            "held": len(held), "showed": tot["showed"], "noshow": tot["noshow"],
            "unmarked": tot["unmarked"], "cancelled": tot["cancelled"], "upcoming": tot["upcoming"],
            "show_rate": (tot["showed"] / decided) if decided else None,
            "revenue": revenue, "revenue_prev": revenue_prev, "pending": pending, "refunded": refunded,
            "sales": len(ok_in),
            "conversations": convs_total, "forms": forms_total,
            "contacts_total": S["contacts_total_seen"], "tags": S["tags"],
        },
        "daily": daily,
        "sources": [{"name": k, "n": v} for k, v in src.most_common(8)],
        "segments": [{"name": k, "n": v} for k, v in seg.most_common(10)],
        "countries": [{"name": k, "n": v} for k, v in ctry.most_common(8)],
        "health": health,
        "pipelines": pipe_rows,
        "pipeline_totals": pt,
        "campaigns": camp_rows,
        "finance": finance,
        "database": database,
        "calendars": cal_rows,
        "upcoming": [{"at": e["start"], "cal": calname.get(e["cal"], "?"), "who": mask(e["title"])} for e in upcoming],
        "payments": {"by_status": [{"status": k, "n": v[0], "amount": v[1]} for k, v in
                                   sorted(st.items(), key=lambda kv: -kv[1][1])],
                     "products": prod_rows, "recent": recent_pay},
        "recent_leads": [{"at": c["dateAdded"], "name": mask(c.get("contactName")),
                          "source": c.get("source") or "(none)",
                          "tags": [t for t in c.get("tags", []) if not t.startswith("[email]")][:2]} for c in recent],
        "channels": [{"name": k, "n": v} for k, v in chan.most_common()],
    }


# ---------------------------------------------------------------- http
class H(BaseHTTPRequestHandler):
    def log_message(self, *a):
        pass

    def send(self, code, body, ctype):
        self.send_response(code)
        self.send_header("Content-Type", ctype)
        self.send_header("Cache-Control", "no-store")
        self.send_header("Content-Length", str(len(body)))
        self.end_headers()
        self.wfile.write(body)

    def do_GET(self):
        u = urllib.parse.urlparse(self.path)
        if u.path == "/api/data":
            q = urllib.parse.parse_qs(u.query)
            days = min(max(int(q.get("days", ["30"])[0]), 1), HISTORY_DAYS)
            ex = q.get("test", ["1"])[0] != "0"
            imp = q.get("imp", ["1"])[0] != "0"
            if "Contacts" not in SYNC:
                return self.send(503, b'{"loading":true}', "application/json")
            try:
                body = json.dumps(build(days, ex, imp), ensure_ascii=False).encode()
            except Exception as e:  # never kill the server on a bad aggregation
                import traceback
                traceback.print_exc()
                return self.send(500, json.dumps({"error": str(e)}).encode(), "application/json")
            return self.send(200, body, "application/json")
        if u.path in ("/", "/index.html"):
            return self.send(200, open(os.path.join(HERE, "index.html"), "rb").read(), "text/html; charset=utf-8")
        self.send(404, b"not found", "text/plain")


if __name__ == "__main__":
    threading.Thread(target=refresher, daemon=True).start()
    print("METCARE dashboard on http://localhost:%d" % PORT)
    ThreadingHTTPServer(("127.0.0.1", PORT), H).serve_forever()
