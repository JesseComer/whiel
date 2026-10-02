"""Every live benchmark input carries the contributor header the credit table assigns it."""
from collections import Counter
from pathlib import Path
import unittest

ROOT = Path(__file__).resolve().parents[1]
HEADER = "-- Benchmark contributors: "

# The credit table: the originator of a case and whoever wrote its current
# encoding, students before advisors, each alphabetical by last name.
TABLE = {
    "Jesse Comer, Fangzhu Shen": ["0001", "0013"],
    "Fangzhu Shen": ["0132", "0133", "0134", "0136", "0137"],
    "Fangzhu Shen, Leo Zhang": ["0115", "0117", "0119", "0123", "0125", "0128", "0130",
                                "0138", "0162", "0163"],
    "Leo Zhang, Val Tannen": ["4001", "4002", "4003", "4004", "4034", "4035", "4036",
                              "4037", "4040"],
    "Jesse Comer, Val Tannen": ["4041"],
}
DEFAULT = "Leo Zhang"


class ContributorHeaders(unittest.TestCase):
    def expected(self):
        named = {f"Example{suffix}": names for names, ids in TABLE.items() for suffix in ids}
        cases = sorted(p.parent.name for p in (ROOT / "Benchmark").glob("Example*/Input.lean"))
        self.assertTrue(set(named) <= set(cases), sorted(set(named) - set(cases)))
        return {case: named.get(case, DEFAULT) for case in cases}

    def test_every_header_matches_the_table(self):
        for case, names in self.expected().items():
            first = (ROOT / "Benchmark" / case / "Input.lean").read_text().split("\n", 1)[0]
            self.assertEqual(first, HEADER + names, case)

    def test_totals(self):
        totals = Counter(name for names in self.expected().values() for name in names.split(", "))
        self.assertEqual(dict(totals), {"Leo Zhang": 78, "Fangzhu Shen": 17,
                                        "Val Tannen": 10, "Jesse Comer": 3})


if __name__ == "__main__":
    unittest.main()
