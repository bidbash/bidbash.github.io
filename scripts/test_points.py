#!/usr/bin/env python3
"""Tests for the scoring rules and both data feeds. Run: python3 scripts/test_points.py

The real-match test needs two cached files (it never spends API hits):
  CD_FINAL   CricketData scorecard JSON for the BBL|15 final (Scorchers v Sixers, 25 Jan 2026)
  CS_FINAL   Cricsheet ball-by-ball JSON for the same match (1493281.json in bbl_json.zip)
  CS_PEOPLE  optional, Cricsheet people.csv
"""
import json
import os
import sys
import unittest

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import points  # noqa: E402

S, PLAYERS = points.load_site()


def st(**kw):
    d = points.blank()
    d["played"] = True
    d.update(kw)
    return d


def pts(**kw):
    return points.score(st(**kw), S)[0]


class HandWorked(unittest.TestCase):
    def test_45_off_28(self):
        # 45 runs + strike rate 160.71 (25) = 70
        total, items = points.score(st(runs=45, balls=28), S)
        self.assertEqual(total, 70)
        self.assertIn(["Strike rate 160.71", 25], items)

    def test_3_for_22_off_4_with_9_dots_and_2_wides(self):
        # 3 wickets 60, every-3 bonus 10, 9 dots 9, 2 wides -2, economy 5.50 (15) = 92
        self.assertEqual(pts(legal=24, conceded=22, wickets=3, dots=9, wides=2), 92)

    def test_stumping(self):
        self.assertEqual(pts(stumpings=1), 15)

    def test_century_is_runs_plus_20_only(self):
        self.assertEqual(pts(runs=100, balls=80), 100 + 5 + 20)      # SR 125 -> 5, no extra 50+ bonus
        self.assertEqual(pts(runs=50, balls=50), 50 + 10)            # SR 100 -> nothing

    def test_strike_rate_edges(self):
        self.assertEqual(pts(runs=20, balls=12) - 20, 25)            # SR 166.67
        self.assertEqual(pts(runs=32, balls=20) - 32, 25)            # exactly 160
        self.assertEqual(pts(runs=30, balls=20) - 30, 20)            # exactly 150
        self.assertEqual(pts(runs=24, balls=20) - 24, 5)             # exactly 120
        self.assertEqual(pts(runs=23, balls=20) - 23, 0)             # 115
        self.assertEqual(pts(runs=19, balls=5), 19)                  # under 20 runs: no SR bonus

    def test_economy_edges(self):
        self.assertEqual(pts(legal=18, conceded=12), 25)             # 4.00
        self.assertEqual(pts(legal=24, conceded=17), 20)             # 4.25
        self.assertEqual(pts(legal=24, conceded=20), 20)             # 5.00
        self.assertEqual(pts(legal=24, conceded=21), 15)             # 5.25
        self.assertEqual(pts(legal=24, conceded=32), 5)              # 8.00
        self.assertEqual(pts(legal=24, conceded=33), 0)              # 8.25
        self.assertEqual(pts(legal=17, conceded=0), 0)               # under 3 overs: no economy bonus

    def test_six_wickets(self):
        self.assertEqual(pts(wickets=6, legal=6, conceded=50) - 6 * 20, 20)

    def test_maiden_and_extras(self):
        self.assertEqual(pts(maidens=1, noballs=1, wides=3), 15 - 4)

    def test_did_not_play_scores_nothing(self):
        d = points.blank()
        d.update(catches=2, runs=30)
        self.assertEqual(points.score(d, S)[0], 0)


class Feeds(unittest.TestCase):
    def match(self):
        return {"info": {"teams": ["A", "B"], "players": {"Perth Scorchers": ["MR Marsh", "AJ Turner"],
                                                        "Sydney Sixers": ["SA Abbott", "J Edwards"]},
                         "registry": {"people": {}}},
                "innings": [{"team": "Perth Scorchers", "overs": [{"over": 0, "deliveries": [
                    {"batter": "MR Marsh", "non_striker": "AJ Turner", "bowler": "SA Abbott", "runs": {"batter": 0, "extras": 0, "total": 0},
                     "wickets": [{"kind": "caught", "player_out": "MR Marsh", "fielders": [{"name": "Some Sub", "substitute": True}]}]},
                    {"batter": "AJ Turner", "non_striker": "MR Marsh", "bowler": "SA Abbott", "runs": {"batter": 0, "extras": 0, "total": 0},
                     "wickets": [{"kind": "run out", "player_out": "AJ Turner", "fielders": [{"name": "J Edwards"}, {"name": "SA Abbott"}]}]},
                ]}]}]}

    def test_substitute_catch_scores_nothing_and_shared_run_out(self):
        m = points.Matcher(PLAYERS)
        out = points.parse_cricsheet(self.match(), m)
        by_name = {p["id"]: p["name"] for p in PLAYERS}
        named = {by_name[k]: v for k, v in out.items()}
        self.assertEqual(named["Sean Abbott"]["wickets"], 1)       # the catch still counts as his wicket
        self.assertEqual(named["Sean Abbott"]["catches"], 0)       # but nobody gets the sub's catch
        self.assertEqual(named["Sean Abbott"]["runouts"], 1)       # both run-out fielders credited
        self.assertEqual(named["Jack Edwards"]["runouts"], 1)

    def test_two_tom_rogers_split_by_club(self):
        m = points.Matcher(PLAYERS)
        a = m.match("cricbuzz", "1", "Tom Rogers", "Melbourne Renegades")
        b = m.match("cricbuzz", "2", "Tom Rogers", "Melbourne Stars")
        names = {p["id"]: p["name"] for p in PLAYERS}
        self.assertEqual(names[a], "Tom Rogers (Renegades)")
        self.assertEqual(names[b], "Tom Rogers (Stars)")
        self.assertIsNone(m.match("cricbuzz", "3", "Tom Rogers", "Sydney Thunder"))
        self.assertEqual(len(m.unmatched), 1)


@unittest.skipUnless(os.environ.get("CD_FINAL") and os.environ.get("CS_FINAL"), "cached match files not given")
class RealMatch(unittest.TestCase):
    def test_bbl15_final(self):
        cd = json.load(open(os.environ["CD_FINAL"]))["data"]
        cs = json.load(open(os.environ["CS_FINAL"]))
        people = points.load_people(open(os.environ["CS_PEOPLE"]).read()) if os.environ.get("CS_PEOPLE") else None
        m1, m2 = points.Matcher(PLAYERS), points.Matcher(PLAYERS)
        live = points.parse_cd_scorecard(cd, m1)
        final = points.parse_cricsheet(cs, m2, people)
        names = {p["id"]: p for p in PLAYERS}
        print("\nBBL|15 final, Scorchers v Sixers. Players in the BidBash BBL|16 pool:")
        print("%-24s %-18s %6s %6s  %s" % ("Player", "BBL|16 club", "Live", "Final", "Final breakdown"))
        for pid in sorted(set(live) | set(final), key=lambda p: -points.score(final.get(p, points.blank()), S)[0]):
            lt = points.score(live.get(pid, points.blank()), S)[0] if pid in live else None
            ft, items = points.score(final.get(pid, points.blank()), S)
            print("%-24s %-18s %6s %6s  %s" % (names[pid]["name"], names[pid]["team"], "-" if lt is None else "%g" % lt, "%g" % ft,
                                              ", ".join("%s %+g" % (l, p) for l, p in items)))
        print("Unmatched in live feed:", sorted(set(m1.unmatched)))
        print("Unmatched in Cricsheet:", sorted(set(m2.unmatched)))
        # The two feeds agree on everything except dot balls (live has none).
        for pid in set(live) & set(final):
            a, b = live[pid], final[pid]
            for k in ("runs", "balls", "wickets", "catches", "stumpings", "legal", "conceded", "maidens"):
                self.assertEqual(a[k], b[k], "%s %s live %s final %s" % (names[pid]["name"], k, a[k], b[k]))


if __name__ == "__main__":
    unittest.main(verbosity=2)
