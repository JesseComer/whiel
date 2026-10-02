#!/usr/bin/env python3
"""Tests for Benchmark/report/ra_to_fol.py.

Run them with `python3 -m unittest discover -s Benchmark/report/tests`.

`ra_to_fol.py` parses a `programAssert!` relational-algebra assertion, translates it to a
first-order-logic formula and renders it. The translation is not kernel-checked (unlike the
relational algebra itself), so its correctness rests on the tests here:

* `ParserTranslationTest` checks the parser and the hand-worked translation rules (nested
  `π`/`σ`/`×`, difference, union, multi-column projection with reordering and duplication,
  a string constant, and the `A (=|⊆|≠) ∅` special forms) against expected renderings.
* `LiveTreeTest` parses and translates every `inputPre`/`inputPost` in the live `Benchmark/`
  tree, so a construct the corpus starts using and this module cannot translate is caught
  here rather than by a silent skip in the report.
* `SemanticAgreementTest` is the key correctness test: it evaluates the *same* relational-
  algebra assertion two ways on small random finite databases — once with a tiny independent
  RA/Guard evaluator over the parsed AST (mirroring `RawRAExpr`/`Guard`'s Lean semantics
  in Databases/UnnamedRA and Whiel/Guard), and once with a tiny independent evaluator over the
  translated-and-simplified first-order formula — and asserts they agree. Because the
  generator and both evaluators are independent of `translate_ra`/`translate_guard`/
  `simplify`, agreement across many random instances is strong evidence the translation is
  semantically faithful, not just superficially plausible.
"""
from __future__ import annotations

import importlib.util
import itertools
import random
import sys
import unittest
from pathlib import Path

REPORT_DIR = Path(__file__).resolve().parents[1]
CASES_DIR = REPORT_DIR.parent


def _load(name: str, path: Path):
    spec = importlib.util.spec_from_file_location(name, path)
    mod = importlib.util.module_from_spec(spec)
    sys.modules[name] = mod
    spec.loader.exec_module(mod)
    return mod


F = _load("ra_to_fol_under_test", REPORT_DIR / "ra_to_fol.py")
BR = _load("build_report_under_test", REPORT_DIR / "build_report.py")


def translate(text: str, arities: dict) -> str:
    return F.translate_to_fol(text, arities)


class ParserTranslationTest(unittest.TestCase):
    """Hand-checked translations, including the task's own worked example."""

    def test_simple_atom(self):
        self.assertEqual(translate("(E ⊆ T)", {"E": 2, "T": 2}), "∀x y. (E(x,y) → T(x,y))")

    def test_equality_is_iff(self):
        self.assertEqual(translate("(E = T)", {"E": 2, "T": 2}), "∀x y. (E(x,y) ↔ T(x,y))")

    def test_disequality_is_negation(self):
        self.assertEqual(translate("(E ≠ T)", {"E": 2, "T": 2}), "¬∀x y. (E(x,y) ↔ T(x,y))")

    def test_selection_and_projection_unify_the_dangling_variable(self):
        # The task's own worked example: π[0] (σ[#1 = #2] (E × T)) reads as ∃y. E(x,y) ∧ T(y),
        # never with a dangling "y = z".
        got = translate("(S = (π[0] (σ[#1 = #2] (E × T))))", {"E": 2, "T": 1, "S": 1})
        self.assertEqual(got, "∀x. (S(x) ↔ ∃y. E(x,y) ∧ T(y))")
        self.assertNotIn("=", got.split("↔", 1)[1])

    def test_multi_column_projection_reorders_and_duplicates_columns(self):
        # π[3,0,0] over a quaternary relation: reordered, and column 0 duplicated. S has
        # arity 3, so its ∀-bound variables x,y,z stay distinct positions (S has three
        # independent argument slots); the duplication instead shows up as an explicit
        # "y = z" conjunct, since y and z are both forced to equal R's column 0.
        got = translate("(S = (π[3, 0, 0] R))", {"R": 4, "S": 3})
        self.assertEqual(got, "∀x y z. (S(x,y,z) ↔ (∃u v. R(y,u,v,x)) ∧ y = z)")

    def test_product_concatenates_columns_left_to_right(self):
        got = translate("(S = (A × B))", {"A": 1, "B": 2, "S": 3})
        self.assertEqual(got, "∀x y z. (S(x,y,z) ↔ A(x) ∧ B(y,z))")

    def test_union_is_disjunction(self):
        got = translate("(S = (A ∪ B))", {"A": 1, "B": 1, "S": 1})
        self.assertEqual(got, "∀x. (S(x) ↔ A(x) ∨ B(x))")

    def test_difference_is_conjunction_with_negation(self):
        got = translate("(S = (A ∖ B))", {"A": 1, "B": 1, "S": 1})
        self.assertEqual(got, "∀x. (S(x) ↔ A(x) ∧ ¬B(x))")

    def test_nested_pi_sigma_times_diff(self):
        # π[0] (σ[#1 = #2] (E × (A ∖ B))): a difference nested inside the product operand
        # of a selection that gets unified away by the projection.
        got = translate("(S = (π[0] (σ[#1 = #2] (E × (A ∖ B)))))", {"E": 2, "A": 1, "B": 1, "S": 1})
        self.assertEqual(got, "∀x. (S(x) ↔ ∃y. E(x,y) ∧ A(y) ∧ ¬B(y))")

    def test_string_constant_is_kept_explicit(self):
        # A constant can never be unified away by renaming, so it stays a visible equality.
        got = translate('(Root = { "root" })', {"Root": 1})
        self.assertEqual(got, '∀x. (Root(x) ↔ x = "root")')

    def test_equals_empty_is_negated_existence(self):
        got = translate("(Bad = ∅[2])", {"Bad": 2})
        self.assertEqual(got, "¬∃x y. Bad(x,y)")

    def test_subset_of_empty_is_negated_existence(self):
        got = translate("(Bad ⊆ ∅)", {"Bad": 2})
        self.assertEqual(got, "¬∃x y. Bad(x,y)")

    def test_not_equal_to_empty_is_existence(self):
        got = translate("(Bad ≠ ∅)", {"Bad": 2})
        self.assertEqual(got, "∃x y. Bad(x,y)")

    def test_empty_subset_of_anything_is_trivially_true(self):
        self.assertEqual(translate("(∅ ⊆ Bad)", {"Bad": 2}), "⊤")

    def test_conjunction_and_disjunction_and_negation(self):
        got = translate("((A ⊆ B) ∧ ((A ⊆ C) ∨ ¬(A ⊆ D)))", {"A": 1, "B": 1, "C": 1, "D": 1})
        self.assertEqual(
            got,
            "(∀x. (A(x) → B(x))) ∧ ((∀y. (A(y) → C(y))) ∨ ¬∀z. (A(z) → D(z)))",
        )

    def test_true_literal(self):
        self.assertEqual(translate("true", {}), "⊤")

    def test_bare_ra_construct_alone_is_rejected(self):
        # A guard must be a comparison/true/false/connective, never a bare RA expression.
        with self.assertRaises(F.FolError):
            translate("A", {"A": 1})

    def test_unknown_relation_fails_loudly(self):
        with self.assertRaises(F.FolError):
            translate("(A ⊆ B)", {"A": 1})

    def test_arity_mismatch_fails_loudly(self):
        with self.assertRaises(F.FolError):
            translate("(A ⊆ B)", {"A": 1, "B": 2})


class LiveTreeTest(unittest.TestCase):
    """Every input in the live Benchmark/ tree translates; a new construct must fail loudly."""

    def test_all_cases_translate_pre_and_post(self):
        cases = sorted(p for p in CASES_DIR.iterdir() if BR.is_case_dir(p))
        self.assertGreater(len(cases), 0, "no cases found under Benchmark/")
        failures = []
        for d in cases:
            parsed = BR.parse_input(d / "Input.lean")
            for field in ("pre", "post"):
                try:
                    F.translate_to_fol(parsed[field], parsed["arities"])
                except F.FolError as e:
                    failures.append(f"{d.name} {field}: {e}")
        self.assertEqual(failures, [], "cases that failed to translate:\n" + "\n".join(failures))


# ------------------------------------------------------------------------------------------
# Semantic agreement: two independent evaluators over small random finite databases.
# ------------------------------------------------------------------------------------------

DOMAIN = [0, 1, 2]


def eval_ra(node, inst: dict) -> set:
    """A tiny, independent evaluator of the parsed RA AST (mirrors Databases/UnnamedRA/Semantics.lean)."""
    if isinstance(node, F.RATop):
        return {()}
    if isinstance(node, F.RAEmpty):
        return set()
    if isinstance(node, F.RASingle):
        return {(node.d.value,)}
    if isinstance(node, F.RARel):
        return inst.get(node.name + ("∞" if node.prophecy else ""), set())
    if isinstance(node, F.RASelect):
        R = eval_ra(node.e, inst)
        return {t for t in R if eval_sel(node.sel, t)}
    if isinstance(node, F.RAProj):
        R = eval_ra(node.e, inst)
        return {tuple(t[i] for i in node.idxs) for t in R}
    if isinstance(node, F.RAProd):
        R1, R2 = eval_ra(node.e1, inst), eval_ra(node.e2, inst)
        return {t1 + t2 for t1 in R1 for t2 in R2}
    if isinstance(node, F.RAUnion):
        return eval_ra(node.e1, inst) | eval_ra(node.e2, inst)
    if isinstance(node, F.RADiff):
        return eval_ra(node.e1, inst) - eval_ra(node.e2, inst)
    raise AssertionError(f"unhandled RA node in test evaluator: {node!r}")


def eval_sel(sel, t: tuple) -> bool:
    if isinstance(sel, F.SelEqIdx):
        return t[sel.i] == t[sel.j]
    if isinstance(sel, F.SelEqConst):
        return t[sel.i] == sel.c.value
    if isinstance(sel, F.SelAnd):
        return eval_sel(sel.l, t) and eval_sel(sel.r, t)
    if isinstance(sel, F.SelOr):
        return eval_sel(sel.l, t) or eval_sel(sel.r, t)
    if isinstance(sel, F.SelNot):
        return not eval_sel(sel.s, t)
    raise AssertionError(f"unhandled Sel node in test evaluator: {sel!r}")


def eval_guard(g, inst: dict) -> bool:
    if isinstance(g, F.GTrue):
        return True
    if isinstance(g, F.GFalse):
        return False
    if isinstance(g, F.GAnd):
        return eval_guard(g.l, inst) and eval_guard(g.r, inst)
    if isinstance(g, F.GOr):
        return eval_guard(g.l, inst) or eval_guard(g.r, inst)
    if isinstance(g, F.GNot):
        return not eval_guard(g.g, inst)
    if isinstance(g, F.GCompare):
        L = set() if g.lhs is F.EMPTY else eval_ra(g.lhs, inst)
        R = set() if g.rhs is F.EMPTY else eval_ra(g.rhs, inst)
        if g.op == "=":
            return L == R
        if g.op == "⊆":
            return L <= R
        if g.op == "≠":
            return L != R
    raise AssertionError(f"unhandled Guard node in test evaluator: {g!r}")


def eval_fol(f, inst: dict, domain: list, env: dict) -> bool:
    """A tiny, independent evaluator of the translated Formula AST (brute-force over `domain`)."""
    if isinstance(f, F.FTrue):
        return True
    if isinstance(f, F.FFalse):
        return False
    if isinstance(f, F.Atom):
        args = tuple(a.value if isinstance(a, F.DataLit) else env[a] for a in f.args)
        return args in inst.get(f.pred, set())
    if isinstance(f, F.Eq):
        lhs = f.lhs.value if isinstance(f.lhs, F.DataLit) else env[f.lhs]
        rhs = f.rhs.value if isinstance(f.rhs, F.DataLit) else env[f.rhs]
        return lhs == rhs
    if isinstance(f, F.Not):
        return not eval_fol(f.f, inst, domain, env)
    if isinstance(f, F.And):
        return all(eval_fol(p, inst, domain, env) for p in f.parts)
    if isinstance(f, F.Or):
        return any(eval_fol(p, inst, domain, env) for p in f.parts)
    if isinstance(f, F.Implies):
        return (not eval_fol(f.l, inst, domain, env)) or eval_fol(f.r, inst, domain, env)
    if isinstance(f, F.Iff):
        return eval_fol(f.l, inst, domain, env) == eval_fol(f.r, inst, domain, env)
    if isinstance(f, F.Exists):
        return any(
            eval_fol(f.body, inst, domain, {**env, **dict(zip(f.varsl, combo))})
            for combo in itertools.product(domain, repeat=len(f.varsl))
        )
    if isinstance(f, F.Forall):
        return all(
            eval_fol(f.body, inst, domain, {**env, **dict(zip(f.varsl, combo))})
            for combo in itertools.product(domain, repeat=len(f.varsl))
        )
    raise AssertionError(f"unhandled Formula node in test evaluator: {f!r}")


def eval_guard_as_fol(g, arities: dict, inst: dict, domain: list) -> bool:
    formula = F.simplify(F.translate_guard(g, arities))
    return eval_fol(formula, inst, domain, {})


SCHEMA = {"A": 1, "B": 1, "C": 2, "D": 2, "E": 2}


def gen_ra(target_arity: int, depth: int, rnd: random.Random):
    """A random RA AST of exactly `target_arity`, biased toward shallow trees."""
    names_here = [n for n, a in SCHEMA.items() if a == target_arity]
    if depth <= 0 or rnd.random() < 0.35:
        if names_here and rnd.random() < 0.75:
            return F.RARel(rnd.choice(names_here))
        if target_arity == 0:
            return rnd.choice([F.RATop(), F.RAEmpty(0)])
        if target_arity == 1 and rnd.random() < 0.3:
            return F.RASingle(F.DataLit("num", rnd.choice(DOMAIN)))
        return F.RAEmpty(target_arity)

    kind = rnd.choice(["select", "proj", "prod", "union", "diff"])
    if kind == "select" and target_arity >= 1:
        inner = gen_ra(target_arity, depth - 1, rnd)
        if target_arity >= 2 and rnd.random() < 0.5:
            i, j = rnd.sample(range(target_arity), 2)
            sel = F.SelEqIdx(i, j)
        else:
            i = rnd.randrange(target_arity)
            sel = F.SelEqConst(i, F.DataLit("num", rnd.choice(DOMAIN)))
        return F.RASelect(sel, inner)
    if kind == "proj":
        src_arity = target_arity + rnd.choice([0, 1, 2])
        src_arity = max(src_arity, 1)
        inner = gen_ra(src_arity, depth - 1, rnd)
        idxs = [rnd.randrange(src_arity) for _ in range(target_arity)]
        return F.RAProj(idxs, inner)
    if kind == "prod":
        a = rnd.randint(0, target_arity)
        b = target_arity - a
        left = F.RATop() if a == 0 else gen_ra(a, depth - 1, rnd)
        right = F.RATop() if b == 0 else gen_ra(b, depth - 1, rnd)
        return F.RAProd(left, right)
    left = gen_ra(target_arity, depth - 1, rnd)
    right = gen_ra(target_arity, depth - 1, rnd)
    return F.RAUnion(left, right) if kind == "union" else F.RADiff(left, right)


def gen_guard(depth: int, rnd: random.Random):
    if depth <= 0 or rnd.random() < 0.4:
        arity = rnd.choice([0, 1, 2, 3])
        op = rnd.choice(["=", "⊆", "≠"])
        lhs = gen_ra(arity, 2, rnd)
        rhs = F.EMPTY if arity and rnd.random() < 0.15 else gen_ra(arity, 2, rnd)
        lhs = F.EMPTY if rhs is not F.EMPTY and rnd.random() < 0.1 else lhs
        return F.GCompare(op, lhs, rhs)
    kind = rnd.choice(["and", "or", "not"])
    if kind == "and":
        return F.GAnd(gen_guard(depth - 1, rnd), gen_guard(depth - 1, rnd))
    if kind == "or":
        return F.GOr(gen_guard(depth - 1, rnd), gen_guard(depth - 1, rnd))
    return F.GNot(gen_guard(depth - 1, rnd))


def random_instance(rnd: random.Random) -> dict:
    inst = {}
    for name, arity in SCHEMA.items():
        universe = list(itertools.product(DOMAIN, repeat=arity))
        k = rnd.randint(0, len(universe))
        inst[name] = set(rnd.sample(universe, k))
    return inst


class SemanticAgreementTest(unittest.TestCase):
    """The translated-and-simplified formula agrees with direct RA/Guard evaluation."""

    def test_random_guards_agree_on_random_instances(self):
        rnd = random.Random(20260918)
        trials = 300
        for trial in range(trials):
            g = gen_guard(depth=3, rnd=rnd)
            inst = random_instance(rnd)
            want = eval_guard(g, inst)
            got = eval_guard_as_fol(g, SCHEMA, inst, DOMAIN)
            self.assertEqual(
                got, want,
                f"trial {trial}: RA/FOL disagree on guard {g!r} over instance {inst!r}",
            )

    def test_real_corpus_cases_agree_on_random_instances(self):
        rnd = random.Random(1090162)
        sample = ["Example0162", "Example0130", "Example1030", "Example1088", "Example5033"]
        for case in sample:
            d = CASES_DIR / case
            parsed = BR.parse_input(d / "Input.lean")
            arities = parsed["arities"]
            for field in ("pre", "post"):
                g = F.parse_guard_text(parsed[field])
                for _ in range(20):
                    inst = {name: set(rnd.sample(
                        list(itertools.product(DOMAIN + ["root"], repeat=arity)),
                        rnd.randint(0, min(6, len(DOMAIN + ["root"]) ** arity)),
                    )) for name, arity in arities.items()}
                    want = eval_guard(g, inst)
                    got = eval_guard_as_fol(g, arities, inst, DOMAIN + ["root"])
                    self.assertEqual(
                        got, want,
                        f"{case} {field}: RA/FOL disagree over instance {inst!r}",
                    )


if __name__ == "__main__":
    unittest.main()
