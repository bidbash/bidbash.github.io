#!/usr/bin/env python3
"""BidBash points fetcher.

Runs in a GitHub Action every 10 minutes (see .github/workflows/points.yml). Standard library only.

  1. Once a day, loads the BBL|16 fixture list from CricketData.org (2 requests).
  2. While a match is on, pulls its scorecard every POLL_MINUTES (25 by default; 10 requests each on the free plan)
     and writes provisional points. Scorecards have no dot balls, so live bowling points can be low.
  3. When Cricsheet publishes the ball-by-ball file (usually a day or two later), rescores the match
     exactly and marks it final.
  4. Nudges every league's trade window clock.

Secrets come from the environment: CRICKETDATA_KEY, SUPABASE_URL, SUPABASE_SERVICE_KEY.
The scoring rules are read from the SCORING block in index.html, so there is one copy of them.
Names that can't be matched to a BidBash player are logged (and stored in `unmatched`), never guessed.
"""
import argparse
import csv
import io
import json
import os
import re
import sys
import unicodedata
import urllib.parse
import urllib.request
import zipfile
from datetime import datetime, timedelta, timezone

try:
    from zoneinfo import ZoneInfo
    SYD = ZoneInfo("Australia/Sydney")
except Exception:  # pragma: no cover
    SYD = timezone(timedelta(hours=11))

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
SEASON = "BBL16"
SERIES_NAME = "Big Bash League 2026-27"
CD_BASE = os.environ.get("CD_BASE", "https://api.cricapi.com/v1/")          # overridable for local tests
CS_ZIP = os.environ.get("CS_ZIP", "https://cricsheet.org/downloads/bbl_json.zip")
CS_PEOPLE = os.environ.get("CS_PEOPLE_URL", "https://cricsheet.org/register/people.csv")
# 25 minutes keeps one match inside the free 100 requests a day (about 8 scorecards at 10 requests each).
# On a paid plan set the POLL_MINUTES repository variable to 10.
POLL_MINUTES = int(os.environ.get("POLL_MINUTES", "25"))
SCORECARD_COST = 10          # CricketData charges 10 hits for a scorecard on the free plan
HIT_RESERVE = 5              # never spend the last few hits of the day


def log(*a):
    print(*a, flush=True)


def now_utc():
    return datetime.now(timezone.utc)


# ------------------------------------------------------------------ site data
def load_site(path=None):
    html = open(path or os.path.join(ROOT, "index.html"), encoding="utf-8").read()
    m = re.search(r"/\*SCORING_START\*/\s*const SCORING\s*=\s*(\{.*?\});\s*/\*SCORING_END\*/", html, re.S)
    if not m:
        raise SystemExit("SCORING block not found in index.html")
    scoring = json.loads(m.group(1))
    p = re.search(r"const PLAYERS = (\[.*?\n\]);", html, re.S)
    players = json.loads(p.group(1))
    return scoring, players


# ------------------------------------------------------------------ scoring
BOWLER_KINDS = {"bowled", "caught", "lbw", "stumped", "caught and bowled", "hit wicket"}


def blank():
    return dict(played=False, batted=False, bowled=False, runs=0, balls=0, dots=0, legal=0, conceded=0,
                wickets=0, maidens=0, wides=0, noballs=0, catches=0, runouts=0, stumpings=0)


def score(st, S):
    """Points for one player in one match. Returns (total, [[label, points], ...])."""
    if not st.get("played"):
        return 0.0, [["Did not play", 0]]
    items = []
    b, w, f = S["batting"], S["bowling"], S["fielding"]
    runs, balls = st.get("runs", 0), st.get("balls", 0)
    if runs:
        items.append(["%d run%s" % (runs, "" if runs == 1 else "s"), runs * b["perRun"]])
    if runs >= b["srMinRuns"] and balls > 0:
        sr = runs * 100.0 / balls
        for th, pts in b["srBands"]:
            if sr >= th:
                items.append(["Strike rate %.2f" % sr, pts])
                break
    for th, pts in b["runBonuses"]:
        if runs >= th:
            items.append(["%d+ runs" % th, pts])
            break
    wk = st.get("wickets", 0)
    if wk:
        items.append(["%d wicket%s" % (wk, "" if wk == 1 else "s"), wk * w["perWicket"]])
    if wk >= 3:
        items.append(["Every 3 wickets", (wk // 3) * w["perThreeWickets"]])
    if st.get("maidens"):
        items.append(["%d maiden%s" % (st["maidens"], "" if st["maidens"] == 1 else "s"), st["maidens"] * w["perMaiden"]])
    if st.get("dots"):
        items.append(["%d dot ball%s" % (st["dots"], "" if st["dots"] == 1 else "s"), st["dots"] * w["perDot"]])
    extras = st.get("wides", 0) + st.get("noballs", 0)
    if extras:
        items.append(["%d wide%s and no-ball%s" % (extras, "s" if extras != 1 else "", "s" if extras != 1 else ""), extras * w["perExtra"]])
    legal = st.get("legal", 0)
    if legal >= w["econMinBalls"]:
        econ = round(st.get("conceded", 0) * 6.0 / legal, 2)
        for th, pts in w["econBands"]:
            if econ <= th:
                items.append(["Economy %.2f" % econ, pts])
                break
    for key, label, rule in (("catches", "catch", "catch"), ("runouts", "run out", "runOut"), ("stumpings", "stumping", "stumping")):
        n = st.get(key, 0)
        if n:
            items.append(["%d %s%s" % (n, label, "" if n == 1 else ("es" if label == "catch" else "s")), n * f[rule]])
    total = float(sum(p for _, p in items))
    return total, items


# ------------------------------------------------------------------ name matching
def norm(s):
    s = re.sub(r"\s*\(.*?\)\s*", " ", s or "")          # "Tom Rogers (Stars)" -> "Tom Rogers"
    s = unicodedata.normalize("NFKD", s).encode("ascii", "ignore").decode()
    s = re.sub(r"[^a-zA-Z ]+", " ", s).lower()
    return re.sub(r"\s+", " ", s).strip()


class Matcher:
    """Maps outside player names and ids to BidBash player ids. Club decides ties (two Tom Rogers)."""

    def __init__(self, players, mapping=None):
        self.players = players
        self.mapping = dict(mapping or {})    # (source, ext_id) -> player id
        self.new = []                          # new (source, ext_id, pid, name) to save
        self.unmatched = []                    # (name, ext_id, team)
        self.by_club = {}
        for p in players:
            self.by_club.setdefault(p["team"], []).append(p)

    def _cands(self, name, club):
        n = norm(name)
        pool = self.by_club.get(club, [])
        exact = [p for p in pool if norm(p["name"]) == n]
        if exact:
            return exact
        toks = n.split()
        if not toks:
            return []
        last = toks[-1]
        raw = (name or "").split()
        # Cricsheet style "MR Marsh": leading capitals are initials
        initials = raw[0] if len(raw) > 1 and raw[0].isupper() and len(raw[0]) <= 3 else (toks[0][0] if len(toks) > 1 else "")
        same_last = [p for p in pool if norm(p["name"]).split()[-1] == last]
        if initials:
            same_last = [p for p in same_last if norm(p["name"])[0] == initials[0].lower()] or []
        return same_last

    def match(self, source, ext_id, name, club):
        key = (source, str(ext_id)) if ext_id else None
        if key and key in self.mapping:
            return self.mapping[key]
        c = self._cands(name, club)
        if len(c) == 1:
            pid = c[0]["id"]
            if key:
                self.mapping[key] = pid
                self.new.append((source, str(ext_id), pid, name))
            return pid
        self.unmatched.append((name, str(ext_id or ""), club))
        return None


# ------------------------------------------------------------------ CricketData.org
class CricketData:
    def __init__(self, key):
        self.key = key
        self.hits_today = None
        self.hits_limit = 100

    def get(self, endpoint, **params):
        params["apikey"] = self.key
        url = CD_BASE + endpoint + "?" + urllib.parse.urlencode(params)
        with urllib.request.urlopen(url, timeout=30) as r:
            d = json.loads(r.read().decode())
        info = d.get("info") or {}
        if "hitsToday" in info:
            self.hits_today, self.hits_limit = info.get("hitsToday"), info.get("hitsLimit", 100)
        if d.get("status") != "success":
            raise RuntimeError("CricketData %s failed: %s" % (endpoint, d.get("reason") or d.get("status")))
        return d

    def can_afford(self, cost):
        if self.hits_today is None:
            return True
        return self.hits_today + cost <= self.hits_limit - HIT_RESERVE


def overs_to_balls(o):
    whole = int(float(o))
    part = int(round((float(o) - whole) * 10))
    return whole * 6 + part


def parse_cd_scorecard(data, matcher):
    """Live scorecard -> {player_id: stats}. No dot balls in this feed."""
    stats = {}
    teams = data.get("teams") or []

    def st(pid):
        return stats.setdefault(pid, blank())

    for inn in data.get("scorecard") or []:
        bat_team = re.sub(r"\s+Inning.*$", "", inn.get("inning", "")).strip()
        field_team = next((t for t in teams if t != bat_team), "")

        def fielder(name, ext_id):
            return matcher.match("cricbuzz", ext_id, name, field_team)

        for b in inn.get("batting") or []:
            who = b.get("batsman") or {}
            pid = matcher.match("cricbuzz", who.get("cricbuzz_id") or who.get("id"), who.get("name"), bat_team)
            if pid:
                s = st(pid)
                s.update(played=True, batted=True)
                s["runs"] += int(b.get("r") or 0)
                s["balls"] += int(b.get("b") or 0)
            kind = (b.get("dismissal") or "").lower()
            text = b.get("dismissal-text") or ""
            if re.search(r"\bsub\b", text, re.I):
                continue                      # substitute fielders score nothing
            c = b.get("catcher") or {}
            if kind == "catch" and c:
                fp = fielder(c.get("name"), c.get("cricbuzz_id"))
                if fp:
                    st(fp)["catches"] += 1
                    st(fp)["played"] = True
            elif kind == "cb":
                bw = b.get("bowler") or {}
                fp = fielder(bw.get("name"), bw.get("cricbuzz_id"))
                if fp:
                    st(fp)["catches"] += 1
            elif kind in ("stumped", "stumping") and c:
                fp = fielder(c.get("name"), c.get("cricbuzz_id"))
                if fp:
                    st(fp)["stumpings"] += 1
                    st(fp)["played"] = True
            elif kind in ("runout", "run out"):
                m = re.search(r"run out \(([^)]*)\)", text, re.I)
                names = [n.strip() for n in m.group(1).split("/")] if m else []
                done = set()
                for n in names:
                    ext = c.get("cricbuzz_id") if c and norm(c.get("name")) == norm(n) else None
                    fp = fielder(n, ext)
                    if fp and fp not in done:
                        done.add(fp)
                        st(fp)["runouts"] += 1
                        st(fp)["played"] = True
                if not names and c:
                    fp = fielder(c.get("name"), c.get("cricbuzz_id"))
                    if fp:
                        st(fp)["runouts"] += 1
        for w in inn.get("bowling") or []:
            who = w.get("bowler") or {}
            pid = matcher.match("cricbuzz", who.get("cricbuzz_id") or who.get("id"), who.get("name"), field_team)
            if not pid:
                continue
            s = st(pid)
            s.update(played=True, bowled=True)
            s["legal"] += overs_to_balls(w.get("o") or 0)
            s["conceded"] += int(w.get("r") or 0)
            s["wickets"] += int(w.get("w") or 0)
            s["maidens"] += int(w.get("m") or 0)
            s["wides"] += int(w.get("wd") or 0)
            s["noballs"] += int(w.get("nb") or 0)
    return stats


# ------------------------------------------------------------------ Cricsheet
def load_people(raw):
    """Cricsheet register: person id -> cricbuzz id."""
    out = {}
    for row in csv.DictReader(io.StringIO(raw)):
        if row.get("key_cricbuzz"):
            out[row["identifier"]] = row["key_cricbuzz"]
    return out


def parse_cricsheet(match, matcher, people=None):
    """Ball-by-ball file -> {player_id: stats}. Exact: dots, maidens, wides, no-balls, every fielder."""
    info = match["info"]
    reg = (info.get("registry") or {}).get("people") or {}
    team_of = {}
    for team, names in (info.get("players") or {}).items():
        for n in names:
            team_of[n] = team
    raw = {n: blank() for n in team_of}
    came_in = set()

    def s(n):
        return raw.setdefault(n, blank())

    for inn in match.get("innings") or []:
        for over in inn.get("overs") or []:
            bowlers, legal, conceded = set(), 0, 0
            for d in over.get("deliveries") or []:
                for r in ((d.get("replacements") or {}).get("match") or []):
                    if r.get("in"):
                        came_in.add(r["in"])
                ex = d.get("extras") or {}
                wide, nb = "wides" in ex, "noballs" in ex
                bat, bwl = d["batter"], d["bowler"]
                s(bat)["batted"] = True
                s(d["non_striker"])["batted"] = True
                s(bwl)["bowled"] = True
                rb = d["runs"]["batter"]
                s(bat)["runs"] += rb
                if not wide:
                    s(bat)["balls"] += 1
                c = rb + ex.get("wides", 0) + ex.get("noballs", 0)
                s(bwl)["conceded"] += c
                if wide:
                    s(bwl)["wides"] += 1
                if nb:
                    s(bwl)["noballs"] += 1
                if not wide and not nb:
                    s(bwl)["legal"] += 1
                    legal += 1
                    if c == 0:
                        s(bwl)["dots"] += 1
                bowlers.add(bwl)
                conceded += c
                for wk in d.get("wickets") or []:
                    kind = wk.get("kind")
                    if kind in BOWLER_KINDS:
                        s(bwl)["wickets"] += 1
                    fielders = [f.get("name") for f in (wk.get("fielders") or []) if f.get("name") and not f.get("substitute")]
                    if kind == "caught" and fielders:
                        s(fielders[0])["catches"] += 1
                    elif kind == "caught and bowled":
                        s(bwl)["catches"] += 1
                    elif kind == "stumped" and fielders:
                        s(fielders[0])["stumpings"] += 1
                    elif kind == "run out":
                        for fn in dict.fromkeys(fielders):
                            s(fn)["runouts"] += 1
            if len(bowlers) == 1 and legal == 6 and conceded == 0:
                s(next(iter(bowlers)))["maidens"] += 1
    out = {}
    for name, st in raw.items():
        team = team_of.get(name)
        if not team:
            continue  # not in either XI (a substitute fielder): scores nothing
        # X-factor / impact replacements count as played only if they bat or bowl.
        st["played"] = (name not in came_in) or st["batted"] or st["bowled"]
        pid_ext = reg.get(name)
        cb = (people or {}).get(pid_ext) if pid_ext else None
        pid = matcher.mapping.get(("cricsheet", pid_ext)) if pid_ext else None
        if not pid and cb:
            pid = matcher.mapping.get(("cricbuzz", cb))
        if not pid:
            pid = matcher.match("cricsheet", pid_ext, name, team)
        elif pid_ext and ("cricsheet", pid_ext) not in matcher.mapping:
            matcher.mapping[("cricsheet", pid_ext)] = pid
            matcher.new.append(("cricsheet", pid_ext, pid, name))
        if pid:
            out[pid] = st
    return out


def find_cricsheet(zf, home, away, starts_at):
    want = {home, away}
    day = starts_at.astimezone(SYD).date()
    for name in zf.namelist():
        if not name.endswith(".json"):
            continue
        d = json.loads(zf.read(name))
        i = d["info"]
        if set(i.get("teams") or []) != want:
            continue
        try:
            md = datetime.strptime(i["dates"][0], "%Y-%m-%d").date()
        except Exception:
            continue
        if abs((md - day).days) <= 1:
            return d
    return None


# ------------------------------------------------------------------ Supabase REST
class DB:
    def __init__(self, url, key):
        self.url = url.rstrip("/") + "/rest/v1/"
        self.h = {"apikey": key, "Content-Type": "application/json"}
        if not key.startswith("sb_"):
            self.h["Authorization"] = "Bearer " + key   # legacy JWT service key

    def _req(self, method, path, body=None, extra=None):
        h = dict(self.h)
        h.update(extra or {})
        data = json.dumps(body).encode() if body is not None else None
        req = urllib.request.Request(self.url + path, data=data, headers=h, method=method)
        try:
            with urllib.request.urlopen(req, timeout=30) as r:
                txt = r.read().decode()
                return json.loads(txt) if txt else None
        except urllib.error.HTTPError as e:
            raise RuntimeError("Supabase %s %s: %s %s" % (method, path, e.code, e.read().decode()[:300]))

    def get(self, table, query):
        return self._req("GET", table + "?" + query)

    def upsert(self, table, rows, on_conflict):
        if rows:
            self._req("POST", table + "?on_conflict=" + on_conflict, rows,
                      {"Prefer": "resolution=merge-duplicates,return=minimal"})

    def patch(self, table, query, body):
        self._req("PATCH", table + "?" + query, body, {"Prefer": "return=minimal"})

    def rpc(self, fn, body=None):
        return self._req("POST", "rpc/" + fn, body or {})


# ------------------------------------------------------------------ rounds
def week_monday(dt_utc):
    local = dt_utc.astimezone(SYD)
    return (local - timedelta(days=local.weekday())).date()


def round_numbers(starts):
    """Rounds are Monday to Sunday weeks in Sydney time; round 1 holds the first game."""
    first = week_monday(min(starts))
    return [((week_monday(s) - first).days // 7) + 1 for s in starts]


def parse_time(s):
    s = s.replace("Z", "+00:00")
    d = datetime.fromisoformat(s)
    return d if d.tzinfo else d.replace(tzinfo=timezone.utc)


# ------------------------------------------------------------------ the run
def rows_for(fixture_id, stats, scoring, source):
    rows = []
    for pid, st in stats.items():
        total, items = score(st, scoring)
        rows.append({"fixture_id": fixture_id, "player_id": pid, "played": bool(st["played"]),
                     "points": total, "breakdown": items, "source": source,
                     "updated_at": now_utc().isoformat()})
    return rows


def run(args):
    scoring, players = load_site()
    db = DB(os.environ["SUPABASE_URL"], os.environ["SUPABASE_SERVICE_KEY"])
    cd = CricketData(os.environ["CRICKETDATA_KEY"])
    mapping = {(r["source"], r["ext_id"]): r["player_id"] for r in db.get("player_map", "select=source,ext_id,player_id")}
    matcher = Matcher(players, mapping)
    now = now_utc()

    # 1. fixture list, once a day
    meta = {r["key"]: r["value"] for r in db.get("meta", "select=key,value")}
    synced = meta.get("fixtures_synced", {}).get("at")
    if args.force_fixtures or not synced or now - parse_time(synced) > timedelta(hours=20):
        series = cd.get("series", offset=0, search="Big Bash League")
        sid = next((s["id"] for s in series["data"] if s["name"] == SERIES_NAME), None)
        if not sid:
            log("Series not found:", SERIES_NAME)
        else:
            info = cd.get("series_info", id=sid)
            ms = [m for m in info["data"]["matchList"] if m.get("dateTimeGMT")]
            starts = [parse_time(m["dateTimeGMT"]) for m in ms]
            rounds = round_numbers(starts) if starts else []
            rows = []
            for m, st, rd in zip(ms, starts, rounds):
                t = m.get("teams") or ["", ""]
                rows.append({"id": m["id"], "season": SEASON, "round": rd, "starts_at": st.isoformat(),
                             "home": t[0], "away": t[1] if len(t) > 1 else "", "name": m.get("name"),
                             "status": m.get("status"), "ended": bool(m.get("matchEnded"))})
            db.upsert("fixtures", rows, "id")
            log("Fixtures synced:", len(rows))
            db.upsert("meta", [{"key": "fixtures_synced", "value": {"at": now.isoformat(), "count": len(rows)}}], "key")

    fixtures = db.get("fixtures", "select=*&season=eq.%s&order=starts_at" % SEASON)

    # 2. live scorecards for matches in progress
    for f in fixtures:
        st_at = parse_time(f["starts_at"])
        if f["final"] or f["ended"] or not (st_at - timedelta(minutes=5) <= now <= st_at + timedelta(hours=6)):
            continue
        if f.get("fetched_at") and now - parse_time(f["fetched_at"]) < timedelta(minutes=POLL_MINUTES - 1):
            continue
        if not cd.can_afford(SCORECARD_COST):
            log("Skipping", f["name"], ": daily CricketData limit nearly used")
            continue
        try:
            d = cd.get("match_scorecard", id=f["id"])["data"]
        except Exception as e:
            log("Scorecard failed for", f["name"], e)
            continue
        stats = parse_cd_scorecard(d, matcher)
        db.upsert("player_points", rows_for(f["id"], stats, scoring, "live"), "fixture_id,player_id")
        db.patch("fixtures", "id=eq." + urllib.parse.quote(f["id"]),
                 {"fetched_at": now.isoformat(), "ended": bool(d.get("matchEnded")), "status": d.get("status")})
        log("Live points:", f["name"], len(stats), "players", "(ended)" if d.get("matchEnded") else "")

    # 3. exact points from Cricsheet once the match file is published
    pending = [f for f in fixtures if not f["final"] and parse_time(f["starts_at"]) < now - timedelta(hours=5)]
    if pending:
        zf = zipfile.ZipFile(io.BytesIO(urllib.request.urlopen(CS_ZIP, timeout=60).read()))
        people = load_people(urllib.request.urlopen(CS_PEOPLE, timeout=60).read().decode("utf-8"))
        for f in pending:
            m = find_cricsheet(zf, f["home"], f["away"], parse_time(f["starts_at"]))
            if not m:
                continue
            stats = parse_cricsheet(m, matcher, people)
            db.upsert("player_points", rows_for(f["id"], stats, scoring, "final"), "fixture_id,player_id")
            db.patch("fixtures", "id=eq." + urllib.parse.quote(f["id"]), {"final": True, "ended": True})
            log("Final points from Cricsheet:", f["name"], len(stats), "players")

    # 4. remember new name matches, log the ones we could not match
    db.upsert("player_map", [{"source": s, "ext_id": e, "player_id": p, "ext_name": n} for s, e, p, n in matcher.new], "source,ext_id")
    if matcher.unmatched:
        for n, e, t in sorted(set(matcher.unmatched)):
            log("UNMATCHED:", n, e, t)
        db.upsert("unmatched", [{"fixture_id": "-", "ext_name": n, "ext_id": e, "team": t}
                                for n, e, t in sorted(set(matcher.unmatched))], "fixture_id,ext_name")
    db.rpc("tick_all")
    db.upsert("meta", [{"key": "points_updated", "value": {"at": now_utc().isoformat(), "hitsToday": cd.hits_today,
                                                            "hitsLimit": cd.hits_limit}}], "key")
    log("Done. CricketData hits today:", cd.hits_today, "of", cd.hits_limit)


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--force-fixtures", action="store_true", help="reload the fixture list now")
    args = ap.parse_args()
    missing = [k for k in ("CRICKETDATA_KEY", "SUPABASE_URL", "SUPABASE_SERVICE_KEY") if not os.environ.get(k)]
    if missing:
        raise SystemExit("Missing secrets: " + ", ".join(missing))
    run(args)


if __name__ == "__main__":
    main()
