#!/usr/bin/env python3
"""The Datalog text the report prints is the text the kernel checked.

Run them with `python3 -m unittest discover -s Benchmark/report/tests`.

The report prints each case's Datalog programs from its `Metadata.json`, and most of those
blocks carry a provenance that calls them kernel-checked. The programs themselves are stated a
second time in `Benchmark/<id>/Fidelity/<id>.lean`, inside `datalog![ … ]` blocks, and it is
that statement — not the metadata copy — the naive compiler and the kernel see. Nothing has so
far tied the two together, so the metadata copy could drift and the report would still call it
kernel-checked.

These tests close that gap. For every case whose fidelity module states `datalog![ … ]` blocks,
the rules of the module and the rules of the metadata blocks that claim to be kernel-checked are
parsed, normalised (comments dropped, rules rejoined across line breaks, the `;` and `.`
terminators dropped, whitespace collapsed) and compared as multisets: they must be equal, per
case. Relation and variable names are compared as written, so a renaming is a failure too.

The claim is checked in both directions:

* a block may say `kernel-checked` only when the module states its rules, and
* the module may state no rule that no kernel-checked block records,

so the wording the report prints never claims more than the fidelity proof establishes. A case
whose metadata carries further blocks under another provenance — the rules as the header comment
of `Input.lean` states them, a hand-written reading, a program the module does not compile — is
free to differ from the module in those blocks, and the report does not call them kernel-checked.
"""
from __future__ import annotations

import json
import re
import unittest
from collections import Counter
from pathlib import Path

CASES_DIR = Path(__file__).resolve().parents[2]
# The provenance wording that promises the block is what the kernel saw.
KERNEL_CHECKED = "kernel-checked"


def strip_comment(line: str) -> str:
    return re.sub(r"--.*$", "", line).strip()


def split_rules(text: str) -> list[str]:
    """The rules of one Datalog block, normalised, in the order they are written.

    A rule ends at its `;` or `.` terminator; the fidelity modules write one, the metadata
    copies usually do not, so a rule also ends at a line break once it is complete — it has a
    `:-`, its parentheses are balanced, and it ends in neither a comma nor the `:-` itself.
    That is what lets a rule broken over several lines in a module be read as one rule.
    """
    parts: list[str] = []
    buf = ""
    for raw in text.split("\n"):
        line = strip_comment(raw)
        if not line:
            if buf:
                parts.append(buf)
                buf = ""
            continue
        buf = f"{buf} {line}" if buf else line
        complete = line.endswith(";") or line.endswith(".")
        if not complete:
            complete = (":-" in buf and buf.count("(") == buf.count(")")
                        and not buf.endswith(",") and not buf.endswith(":-"))
        if complete:
            parts.append(buf)
            buf = ""
    if buf:
        parts.append(buf)
    rules = []
    for part in parts:
        rule = part.strip()
        while rule.endswith(";") or rule.endswith("."):
            rule = rule[:-1].rstrip()
        rule = re.sub(r"\s+", " ", rule).replace(" ,", ",").replace(" (", "(")
        if rule and ":-" in rule:
            rules.append(rule)
    return rules


def module_blocks(path: Path) -> list[str]:
    """The inside of every `datalog![ … ]` block of a fidelity module, in order."""
    text = path.read_text(encoding="utf-8")
    blocks = []
    for m in re.finditer(r"datalog!\[", text):
        start = text.index("[", m.start())
        depth, i = 0, start
        while i < len(text):
            if text[i] == "[":
                depth += 1
            elif text[i] == "]":
                depth -= 1
                if depth == 0:
                    break
            i += 1
        else:
            raise AssertionError(f"{path.name}: unbalanced datalog![ block")
        blocks.append(text[start + 1:i])
    return blocks


def is_case_dir(d: Path) -> bool:
    return d.is_dir() and (d / "Input.lean").exists() and (d / "Metadata.json").exists()


def corpus() -> list[tuple[str, dict, list[str]]]:
    """(case, metadata, module blocks) for every case; the block list is empty when there is none."""
    out = []
    for d in sorted(CASES_DIR.iterdir()):
        if not is_case_dir(d):
            continue
        meta = json.loads((d / "Metadata.json").read_text(encoding="utf-8"))
        fidelity = d / "Fidelity" / f"{d.name}.lean"
        out.append((d.name, meta, module_blocks(fidelity) if fidelity.exists() else []))
    return out


CORPUS = corpus()


def kernel_checked_blocks(meta: dict) -> list[dict]:
    return [b for b in (meta.get("datalog") or []) if KERNEL_CHECKED in b["provenance"]]


class ParserTest(unittest.TestCase):
    """The normalisation, on text written the way each of the two sides writes it."""

    def test_the_module_terminator_and_the_metadata_line_break_read_alike(self):
        self.assertEqual(split_rules("T(x, y) :- E(x, y);\nT(x, y) :- E(x, z), T(z, y);"),
                         split_rules("T(x, y) :- E(x, y)\nT(x, y) :- E(x, z), T(z, y)"))

    def test_a_rule_broken_over_several_lines_is_one_rule(self):
        self.assertEqual(split_rules("PathBF(x1, x2) :-\n  MPath(x1), Edge(x1, y1),\n  PathBF(y1, x2);"),
                         ["PathBF(x1, x2) :- MPath(x1), Edge(x1, y1), PathBF(y1, x2)"])

    def test_comments_and_spacing_are_dropped_but_names_are_not(self):
        self.assertEqual(split_rules("-- a heading\nT(x,  y)  :-  E(x, y).\n"),
                         ["T(x, y) :- E(x, y)"])
        self.assertNotEqual(split_rules("T(x, y) :- E(x, y)"), split_rules("T(a, b) :- E(a, b)"))

    def test_lines_that_are_not_rules_are_not_rules(self):
        self.assertEqual(split_rules("-- the program\n\n"), [])


class CoverageTest(unittest.TestCase):
    """Which cases the comparison covers, and which claims it is allowed to see."""

    def test_the_comparison_covers_the_cases_that_state_programs_in_their_module(self):
        covered = [c for c, _, blocks in CORPUS if blocks]
        self.assertGreaterEqual(len(covered), 40,
                                "the datalog![ ] blocks of the fidelity modules were not found")

    def test_no_case_claims_a_kernel_check_it_has_no_module_for(self):
        for case, meta, blocks in CORPUS:
            if blocks:
                continue
            self.assertEqual(kernel_checked_blocks(meta), [],
                             f"{case}: a block is called kernel-checked, but no fidelity module "
                             "states the programs the kernel would have checked")

    def test_a_module_that_states_programs_has_them_recorded_in_the_metadata(self):
        for case, meta, blocks in CORPUS:
            if not blocks:
                continue
            self.assertTrue(kernel_checked_blocks(meta),
                            f"{case}: the fidelity module states Datalog programs that the "
                            "metadata records under no kernel-checked block")


class RulesAgreeTest(unittest.TestCase):
    """The rules the report prints as kernel-checked are the rules the module states."""

    def test_the_two_statements_of_each_case_are_the_same_multiset_of_rules(self):
        for case, meta, blocks in CORPUS:
            if not blocks:
                continue
            with self.subTest(case=case):
                module = Counter(r for b in blocks for r in split_rules(b))
                recorded = Counter(r for b in kernel_checked_blocks(meta)
                                   for r in split_rules(b["text"]))
                self.assertFalse(sorted((module - recorded).elements()),
                                 f"{case}: the fidelity module states rules that no "
                                 "kernel-checked metadata block records")
                self.assertFalse(sorted((recorded - module).elements()),
                                 f"{case}: a kernel-checked metadata block records rules that "
                                 "the fidelity module does not state")

    def test_every_kernel_checked_block_is_stated_by_the_module(self):
        """Block by block, not only in the union, so a rule cannot move between blocks unseen."""
        for case, meta, blocks in CORPUS:
            if not blocks:
                continue
            module = Counter(r for b in blocks for r in split_rules(b))
            for b in kernel_checked_blocks(meta):
                with self.subTest(case=case, block=b["label"][:40]):
                    self.assertFalse(sorted((Counter(split_rules(b["text"])) - module).elements()),
                                     f"{case}: block {b['label']!r} is called kernel-checked but "
                                     "the fidelity module does not state all of its rules")


if __name__ == "__main__":
    unittest.main()
