# Author: Fangzhu Shen
"""Catalog parity, optional capabilities and one validated inventory."""

from pathlib import Path
import unittest

from agent_houdini.json_wire import encode
from agent_houdini.skills import SkillCatalog
from agent_houdini.tool_catalog import (
    KNOWN_QUERIES, ToolCatalog, default_catalog, tools_for_policy, validate_inventory,
)


FIXTURES = Path(__file__).resolve().parents[1] / "fixtures"


class ToolCatalogTests(unittest.TestCase):
    def test_default_catalog_matches_original_rust_bytes(self):
        expected = (FIXTURES / "default_tools.json").read_bytes()
        self.assertEqual(encode(tools_for_policy(), sort_keys=True), expected)
        self.assertEqual(default_catalog().tools_for_policy(), tools_for_policy())

    def test_local_skills_do_not_become_canonical_queries(self):
        catalog = ToolCatalog().with_skills(SkillCatalog.from_json(b'{"guide":"local"}'))
        self.assertEqual(catalog.names_for_policy([]), ["submit", "get_skill"])
        self.assertIsNone(catalog.query("get_skill"))
        self.assertIsNone(catalog.query("submit"))
        self.assertEqual(catalog.query("ledger"), "ledger")
        self.assertEqual(catalog.tools_for_policy([])[-1]["inputSchema"]["properties"]["id"]["enum"],
                         ["guide"])
        self.assertNotIn("get_skill", default_catalog().names_for_policy())

    def test_optional_unknown_queries_are_ignored_and_known_order_is_preserved(self):
        names = [tool["name"] for tool in tools_for_policy(["ledger", "optional_future", "history"])]
        self.assertEqual(names, ["ledger", "history", "submit"])
        self.assertEqual(default_catalog().names_for_policy(), [*KNOWN_QUERIES, "submit"])

    def test_the_advertised_inventory_is_validated_once_at_the_catalog(self):
        self.assertEqual(default_catalog().inventory(), [*KNOWN_QUERIES, "submit"])

    def test_native_inventory_bounds_are_explicit(self):
        for names in [[], ["ledger"], ["submit", "submit"], ["submit", "mcp.other"],
                      ["submit", "_hidden"], ["submit", "évil"], ["submit", "a" * 65],
                      ["submit", *["name" + str(index) for index in range(128)]]]:
            with self.subTest(names=names), self.assertRaises(ValueError):
                validate_inventory(names)
        self.assertEqual(validate_inventory(["submit", "get_skill", "read_twice"]),
                         ["submit", "get_skill", "read_twice"])


if __name__ == "__main__":
    unittest.main()
