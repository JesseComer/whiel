#!/usr/bin/env python3
"""Translate a `programAssert!` relational-algebra assertion to readable first-order logic.

`Benchmark/ExampleNNNN/Input.lean` states `inputPre` and `inputPost` inside
`programAssert![ ... ]`, in the relational-algebra surface syntax of
`Whiel/Concrete/Notation.lean` (`dbt_index_guard`/`dbt_index_ra`/`dbt_index_sel`): relation
names, `∅`, `∅[n]`, `∪`, `∖`, `×`, `π[i,j,...]` (0-based column projection, indices may repeat
or reorder), `σ[#i = #j]`/`σ[#i = c]` (row selection), the atoms `A ⊆ B`, `A = B`, `A ≠ B`,
`A (⊆|=|≠) ∅`, and the connectives `∧`, `∨`, `¬`. (`∩` is not part of this language: the
underlying AST has no intersection constructor, and no case uses it inside an assertion.)

This module parses that text into a small AST (`RA`/`Sel`/`Guard` node classes below),
translates it to a first-order-logic `Formula` AST over one free tuple of variables per
relation, simplifies it (folding `∧ True`/`∨ False`/`¬¬`, and eliminating the existential
witness a row-selection equality names, so `π[0] (σ[#1 = #2] (E × T))` reads as
`∃y. E(x,y) ∧ T(y)` rather than carrying a dangling `y = z`), and renders it as a Unicode
string. The rendering is a *reading aid* only: the relational-algebra text in `Input.lean`
remains the authority, and this module never changes it.

Any construct this module cannot translate raises `FolError` naming the offending text; the
report build must let that propagate and fail the build rather than skip the case silently.
"""
from __future__ import annotations

from dataclasses import dataclass, field
from typing import Union


class FolError(Exception):
    """A `programAssert!` assertion used a construct this module cannot translate."""


# ----------------------------------------------------------------------------------------
# Data literals (`Whiel.Concrete.Data`: `str`, `num`, `bool`)
# ----------------------------------------------------------------------------------------

@dataclass(frozen=True)
class DataLit:
    kind: str  # 'str' | 'num' | 'bool'
    value: object

    def render(self) -> str:
        if self.kind == "str":
            return f'"{self.value}"'
        if self.kind == "bool":
            return "true" if self.value else "false"
        return str(self.value)


# ----------------------------------------------------------------------------------------
# Tokenizer
# ----------------------------------------------------------------------------------------

_SYMBOLS = ["∅", "⊤", "σ", "π", "×", "∪", "∖", "⊆", "≠", "∧", "∨", "¬", "=", "(", ")", "[", "]",
            "{", "}", ",", "#", "∞"]
_SYMBOL_SET = set(_SYMBOLS)


@dataclass
class Token:
    kind: str  # 'sym' | 'ident' | 'num' | 'str'
    text: str
    value: object = None


def tokenize(text: str) -> list[Token]:
    toks: list[Token] = []
    i, n = 0, len(text)
    while i < n:
        c = text[i]
        if c.isspace():
            i += 1
            continue
        if c == '"':
            j = text.index('"', i + 1)
            toks.append(Token("str", text[i:j + 1], text[i + 1:j]))
            i = j + 1
            continue
        if c.isdigit():
            j = i
            while j < n and text[j].isdigit():
                j += 1
            toks.append(Token("num", text[i:j], int(text[i:j])))
            i = j
            continue
        # Symbols are checked before the identifier scan: two of them (σ, π) are Greek
        # letters, so `str.isalpha()` would otherwise swallow them as identifier starts.
        if c in _SYMBOL_SET:
            toks.append(Token("sym", c))
            i += 1
            continue
        if c.isalpha():
            j = i
            while j < n and (text[j].isalnum()) and text[j] not in _SYMBOL_SET:
                j += 1
            toks.append(Token("ident", text[i:j]))
            i = j
            continue
        raise FolError(f"unrecognized character {c!r} in assertion text: {text!r}")
    return toks


# ----------------------------------------------------------------------------------------
# Raw AST: RA expressions, selections, guards (mirrors `dbt_index_ra`/`dbt_index_sel`/
# `dbt_index_guard` in Whiel/Concrete/Notation.lean)
# ----------------------------------------------------------------------------------------

class RA:
    pass


@dataclass
class RATop(RA):
    pass


@dataclass
class RAEmpty(RA):
    n: int


@dataclass
class RASingle(RA):
    d: DataLit


@dataclass
class RARel(RA):
    name: str
    prophecy: bool = False


@dataclass
class RASelect(RA):
    sel: "Sel"
    e: RA


@dataclass
class RAProj(RA):
    idxs: list[int]
    e: RA


@dataclass
class RAProd(RA):
    e1: RA
    e2: RA


@dataclass
class RAUnion(RA):
    e1: RA
    e2: RA


@dataclass
class RADiff(RA):
    e1: RA
    e2: RA


class Sel:
    pass


@dataclass
class SelEqIdx(Sel):
    i: int
    j: int


@dataclass
class SelEqConst(Sel):
    i: int
    c: DataLit


@dataclass
class SelAnd(Sel):
    l: Sel
    r: Sel


@dataclass
class SelOr(Sel):
    l: Sel
    r: Sel


@dataclass
class SelNot(Sel):
    s: Sel


# A guard-level RA operand is either a real RA expression or the bare `∅` sugar token,
# which only ever appears as an immediate operand of `=`/`⊆`/`≠` (never nested).
EMPTY = object()


class Guard:
    pass


@dataclass
class GTrue(Guard):
    pass


@dataclass
class GFalse(Guard):
    pass


@dataclass
class GCompare(Guard):
    op: str  # '=' | '⊆' | '≠'
    lhs: Union[RA, object]
    rhs: Union[RA, object]


@dataclass
class GAnd(Guard):
    l: Guard
    r: Guard


@dataclass
class GOr(Guard):
    l: Guard
    r: Guard


@dataclass
class GNot(Guard):
    g: Guard


# ----------------------------------------------------------------------------------------
# Parser (recursive descent, precedences mirror the `syntax` declarations in Notation.lean)
# ----------------------------------------------------------------------------------------

class _Parser:
    def __init__(self, toks: list[Token]):
        self.toks = toks
        self.pos = 0

    def peek(self) -> Token | None:
        return self.toks[self.pos] if self.pos < len(self.toks) else None

    def at_sym(self, s: str) -> bool:
        t = self.peek()
        return t is not None and t.kind == "sym" and t.text == s

    def at_ident(self, s: str) -> bool:
        t = self.peek()
        return t is not None and t.kind == "ident" and t.text == s

    def at_bare_empty(self) -> bool:
        """True at the guard-level sugar token `∅` (not `∅[n]`, a normal RA empty literal)."""
        if not self.at_sym("∅"):
            return False
        nxt = self.toks[self.pos + 1] if self.pos + 1 < len(self.toks) else None
        return not (nxt is not None and nxt.kind == "sym" and nxt.text == "[")

    def advance(self) -> Token:
        t = self.peek()
        if t is None:
            raise FolError("unexpected end of assertion text")
        self.pos += 1
        return t

    def expect_sym(self, s: str) -> None:
        if not self.at_sym(s):
            got = self.peek()
            raise FolError(f"expected {s!r}, got {got.text if got else 'end of input'!r}")
        self.advance()

    # ---- data literal ----
    def parse_data_lit(self) -> DataLit:
        t = self.peek()
        if t is None:
            raise FolError("expected a data literal")
        if t.kind == "str":
            self.advance()
            return DataLit("str", t.value)
        if t.kind == "num":
            self.advance()
            return DataLit("num", t.value)
        if t.kind == "ident" and t.text in ("true", "false"):
            self.advance()
            return DataLit("bool", t.text == "true")
        raise FolError(f"unsupported data literal near {t.text!r}")

    # ---- Sel (dbt_index_sel) ----
    def parse_sel(self) -> Sel:
        return self._sel_or()

    def _sel_or(self) -> Sel:
        left = self._sel_and()
        while self.at_sym("∨"):
            self.advance()
            right = self._sel_and()
            left = SelOr(left, right)
        return left

    def _sel_and(self) -> Sel:
        left = self._sel_not()
        while self.at_sym("∧"):
            self.advance()
            right = self._sel_not()
            left = SelAnd(left, right)
        return left

    def _sel_not(self) -> Sel:
        if self.at_sym("¬"):
            self.advance()
            return SelNot(self._sel_not())
        return self._sel_atom()

    def _sel_atom(self) -> Sel:
        if self.at_sym("("):
            self.advance()
            s = self._sel_or()
            self.expect_sym(")")
            return s
        self.expect_sym("#")
        i = self._parse_nat()
        self.expect_sym("=")
        if self.at_sym("#"):
            self.advance()
            j = self._parse_nat()
            return SelEqIdx(i, j)
        c = self.parse_data_lit()
        return SelEqConst(i, c)

    def _parse_nat(self) -> int:
        t = self.peek()
        if t is None or t.kind != "num":
            raise FolError(f"expected a column index, got {t.text if t else 'end of input'!r}")
        self.advance()
        return t.value

    # ---- RA (dbt_index_ra) ----
    def parse_ra(self) -> RA:
        return self._ra_union_diff()

    def _ra_union_diff(self) -> RA:
        left = self._ra_prod()
        while self.at_sym("∪") or self.at_sym("∖"):
            op = self.advance().text
            right = self._ra_prod()
            left = RAUnion(left, right) if op == "∪" else RADiff(left, right)
        return left

    def _ra_prod(self) -> RA:
        left = self._ra_prefix()
        while self.at_sym("×"):
            self.advance()
            right = self._ra_prefix()
            left = RAProd(left, right)
        return left

    def _ra_prefix(self) -> RA:
        if self.at_sym("σ"):
            self.advance()
            self.expect_sym("[")
            sel = self.parse_sel()
            self.expect_sym("]")
            inner = self._ra_prefix()
            return RASelect(sel, inner)
        if self.at_sym("π"):
            self.advance()
            self.expect_sym("[")
            idxs = [self._parse_nat()]
            while self.at_sym(","):
                self.advance()
                idxs.append(self._parse_nat())
            self.expect_sym("]")
            inner = self._ra_prefix()
            return RAProj(idxs, inner)
        return self._ra_atom()

    def _ra_atom(self) -> RA:
        if self.at_sym("⊤"):
            self.advance()
            return RATop()
        if self.at_sym("∅"):
            self.advance()
            self.expect_sym("[")
            n = self._parse_nat()
            self.expect_sym("]")
            return RAEmpty(n)
        if self.at_sym("{"):
            self.advance()
            d = self.parse_data_lit()
            self.expect_sym("}")
            return RASingle(d)
        if self.at_sym("("):
            self.advance()
            e = self.parse_ra()
            self.expect_sym(")")
            return e
        t = self.peek()
        if t is not None and t.kind == "ident":
            self.advance()
            prophecy = False
            if self.at_sym("∞"):
                self.advance()
                prophecy = True
            return RARel(t.text, prophecy=prophecy)
        raise FolError(f"expected a relational-algebra expression near {t.text if t else 'end of input'!r}")

    # ---- Guard (dbt_index_guard) ----
    def parse_guard(self) -> Guard:
        return self._guard_or()

    def _guard_or(self) -> Guard:
        left = self._guard_and()
        while self.at_sym("∨"):
            self.advance()
            right = self._guard_and()
            left = GOr(left, right)
        return left

    def _guard_and(self) -> Guard:
        left = self._guard_not()
        while self.at_sym("∧"):
            self.advance()
            right = self._guard_not()
            left = GAnd(left, right)
        return left

    def _guard_not(self) -> Guard:
        if self.at_sym("¬"):
            self.advance()
            return GNot(self._guard_not())
        return self._guard_atom()

    def _rel_op(self) -> str:
        for s in ("=", "⊆", "≠"):
            if self.at_sym(s):
                self.advance()
                return s
        t = self.peek()
        raise FolError(f"expected '=', '⊆' or '≠', got {t.text if t else 'end of input'!r}")

    def _guard_atom(self) -> Guard:
        if self.at_ident("true"):
            self.advance()
            return GTrue()
        if self.at_ident("false"):
            self.advance()
            return GFalse()
        if self.at_bare_empty():
            # Bare `∅` (no `[n]`) is only valid here, as an immediate comparison operand.
            self.advance()
            op = self._rel_op()
            rhs = self.parse_ra()
            return GCompare(op, EMPTY, rhs)
        if self.at_sym("("):
            checkpoint = self.pos
            try:
                self.advance()
                inner = self._guard_or()
                self.expect_sym(")")
                return inner
            except FolError:
                self.pos = checkpoint
            # Fall through: the parenthesized text was a bare RA operand, not a guard.
        lhs = self.parse_ra()
        op = self._rel_op()
        if self.at_bare_empty():
            self.advance()
            return GCompare(op, lhs, EMPTY)
        rhs = self.parse_ra()
        return GCompare(op, lhs, rhs)


def parse_guard_text(text: str) -> Guard:
    toks = tokenize(text)
    p = _Parser(toks)
    g = p.parse_guard()
    if p.pos != len(toks):
        leftover = toks[p.pos].text
        raise FolError(f"unexpected trailing text starting at {leftover!r} in assertion: {text!r}")
    return g


# ----------------------------------------------------------------------------------------
# First-order-logic formula AST
# ----------------------------------------------------------------------------------------

class Var:
    """A column placeholder. Identity-compared; display names are assigned at render time."""
    __slots__ = ()


class Formula:
    pass


@dataclass
class FTrue(Formula):
    pass


@dataclass
class FFalse(Formula):
    pass


@dataclass
class Atom(Formula):
    pred: str
    # Ordinarily all `Var`; a `DataLit` can appear after the one-point rule substitutes a
    # constant for a variable that was also used as a relation argument elsewhere.
    args: list[Union[Var, DataLit]]


@dataclass
class Eq(Formula):
    # Ordinarily `lhs` is a `Var` and `rhs` a `Var` or `DataLit`; after the one-point rule
    # substitutes a constant for a variable, either side can end up a `DataLit`.
    lhs: Union[Var, DataLit]
    rhs: Union[Var, DataLit]


@dataclass
class Not(Formula):
    f: Formula


@dataclass
class And(Formula):
    parts: list[Formula]


@dataclass
class Or(Formula):
    parts: list[Formula]


@dataclass
class Implies(Formula):
    l: Formula
    r: Formula


@dataclass
class Iff(Formula):
    l: Formula
    r: Formula


@dataclass
class Exists(Formula):
    varsl: list[Var]
    body: Formula


@dataclass
class Forall(Formula):
    varsl: list[Var]
    body: Formula


# ----------------------------------------------------------------------------------------
# Substitution
# ----------------------------------------------------------------------------------------

def substitute(f: Formula, mapping: dict) -> Formula:
    """Replace each `Var` key of `mapping` by its value (a `Var` or `DataLit`) in `f`.

    `mapping` values that are themselves `DataLit` may only replace an `Eq`/`Atom` argument
    position, which is always sound here since every substitution site in this module maps
    freshly allocated, non-overlapping variables.
    """
    def sv(v):
        return mapping.get(v, v)

    if isinstance(f, (FTrue, FFalse)):
        return f
    if isinstance(f, Atom):
        return Atom(f.pred, [sv(a) for a in f.args])
    if isinstance(f, Eq):
        # `sv` is a no-op on a `DataLit` (it is never a mapping key), so this is safe
        # whichever side is currently a variable.
        return Eq(sv(f.lhs), sv(f.rhs))
    if isinstance(f, Not):
        return Not(substitute(f.f, mapping))
    if isinstance(f, And):
        return And([substitute(p, mapping) for p in f.parts])
    if isinstance(f, Or):
        return Or([substitute(p, mapping) for p in f.parts])
    if isinstance(f, Implies):
        return Implies(substitute(f.l, mapping), substitute(f.r, mapping))
    if isinstance(f, Iff):
        return Iff(substitute(f.l, mapping), substitute(f.r, mapping))
    if isinstance(f, Exists):
        return Exists([sv(v) for v in f.varsl], substitute(f.body, mapping))
    if isinstance(f, Forall):
        return Forall([sv(v) for v in f.varsl], substitute(f.body, mapping))
    raise FolError(f"substitute: unhandled formula node {f!r}")


def align_columns(cols_from: list, cols_to: list) -> tuple[dict, list]:
    """Build the substitution that renames `cols_from`'s variables to `cols_to`'s, for
    aligning two independently translated column lists of the same arity (the two sides of
    `∪`/`∖`/`=`/`⊆`).

    `cols_from` may repeat a variable (a duplicated or reordered projection index can make
    two of its columns literally the same variable, e.g. `π[0, 0] R`). A plain
    `dict(zip(cols_from, cols_to))` would then silently keep only the last pairing for that
    repeated key, losing the constraint the earlier position carried. Instead, only the
    first occurrence of a repeated variable is entered into the substitution, and every
    later occurrence contributes an explicit equality between the `cols_to` positions that
    correspond to it — since those `cols_to` variables (typically the outer ∀'s own bound
    variables) cannot themselves be merged into one without changing the atom's arity.
    """
    mapping: dict = {}
    extra: list[Formula] = []
    for v, target in zip(cols_from, cols_to):
        if v in mapping:
            extra.append(Eq(mapping[v], target))
        else:
            mapping[v] = target
    return mapping, extra


def _align_and_substitute(phi: Formula, cols_from: list, cols_to: list) -> Formula:
    mapping, extra = align_columns(cols_from, cols_to)
    phis = substitute(phi, mapping)
    return And([phis] + extra) if extra else phis


def _fresh_binder(cols: list, phi: Formula) -> tuple[list, Formula]:
    """Rebind `cols` to a tuple of guaranteed-distinct fresh variables before it becomes an
    independent quantifier's own bound-variable list (`Forall`'s or `Exists`' `varsl`).

    `cols` can already repeat a variable (e.g. the result of `π[0, 0] R`): that repetition
    faithfully carries a real constraint while it is only ever *read* positionally (as an
    atom's arguments, or realigned via `align_columns`), but a quantifier's own binder list
    must name independent variables — one for each dimension of the tuple being quantified
    over, or the printed `∀x x.` would silently (and wrongly) restrict the quantifier to the
    diagonal instead of stating a fact about the whole arity-`len(cols)` tuple. Any
    duplication in `cols` is instead turned into an explicit equality conjunct in `phi`.
    """
    fresh = [Var() for _ in cols]
    return fresh, _align_and_substitute(phi, cols, fresh)


# ----------------------------------------------------------------------------------------
# Translation: RA/Sel/Guard AST -> (columns, Formula) resp. Formula
# ----------------------------------------------------------------------------------------

def translate_sel(sel: Sel, cols: list[Var]) -> Formula:
    if isinstance(sel, SelEqIdx):
        return Eq(cols[sel.i], cols[sel.j])
    if isinstance(sel, SelEqConst):
        return Eq(cols[sel.i], sel.c)
    if isinstance(sel, SelAnd):
        return And([translate_sel(sel.l, cols), translate_sel(sel.r, cols)])
    if isinstance(sel, SelOr):
        return Or([translate_sel(sel.l, cols), translate_sel(sel.r, cols)])
    if isinstance(sel, SelNot):
        return Not(translate_sel(sel.s, cols))
    raise FolError(f"unsupported selection construct: {sel!r}")


def translate_ra(e: RA, arities: dict) -> tuple[list[Var], Formula]:
    if isinstance(e, RATop):
        return [], FTrue()
    if isinstance(e, RAEmpty):
        return [Var() for _ in range(e.n)], FFalse()
    if isinstance(e, RASingle):
        v = Var()
        return [v], Eq(v, e.d)
    if isinstance(e, RARel):
        if e.name not in arities:
            raise FolError(f"relation {e.name!r} is not in the schema")
        cols = [Var() for _ in range(arities[e.name])]
        pred = e.name + ("∞" if e.prophecy else "")
        return cols, Atom(pred, cols)
    if isinstance(e, RASelect):
        cols, phi = translate_ra(e.e, arities)
        sel_phi = translate_sel(e.sel, cols)
        return cols, And([phi, sel_phi])
    if isinstance(e, RAProj):
        cols, phi = translate_ra(e.e, arities)
        for idx in e.idxs:
            if not (0 <= idx < len(cols)):
                raise FolError(f"projection index {idx} out of range for arity {len(cols)}")
        new_cols = [cols[i] for i in e.idxs]
        kept = set(new_cols)
        exist_vars: list[Var] = []
        seen: set = set()
        for v in cols:
            if v not in kept and v not in seen:
                exist_vars.append(v)
                seen.add(v)
        body = Exists(exist_vars, phi) if exist_vars else phi
        return new_cols, body
    if isinstance(e, RAProd):
        cols1, phi1 = translate_ra(e.e1, arities)
        cols2, phi2 = translate_ra(e.e2, arities)
        return cols1 + cols2, And([phi1, phi2])
    if isinstance(e, RAUnion):
        cols1, phi1 = translate_ra(e.e1, arities)
        cols2, phi2 = translate_ra(e.e2, arities)
        if len(cols1) != len(cols2):
            raise FolError("union of relations with different arity")
        # Neither side's columns can be reused as-is for the union's own result columns: a
        # duplicate/reordered projection on one side (e.g. `π[0, 0] R`) constrains only that
        # side's disjunct, and forcing it onto the whole union would wrongly restrict every
        # tuple contributed by the OTHER side too. Both sides are realigned to a fresh,
        # guaranteed-independent tuple instead, same as a quantifier's own binder list.
        result_cols = [Var() for _ in cols1]
        phi1a = _align_and_substitute(phi1, cols1, result_cols)
        phi2a = _align_and_substitute(phi2, cols2, result_cols)
        return result_cols, Or([phi1a, phi2a])
    if isinstance(e, RADiff):
        cols1, phi1 = translate_ra(e.e1, arities)
        cols2, phi2 = translate_ra(e.e2, arities)
        if len(cols1) != len(cols2):
            raise FolError("difference of relations with different arity")
        phi2s = _align_and_substitute(phi2, cols2, cols1)
        return cols1, And([phi1, Not(phi2s)])
    raise FolError(f"unsupported relational-algebra construct: {e!r}")


def _translate_side(side, arities: dict) -> tuple[list[Var], Formula]:
    if side is EMPTY:
        return None, FFalse()  # arity is inferred from the other side by the caller
    return translate_ra(side, arities)


def translate_guard(g: Guard, arities: dict) -> Formula:
    if isinstance(g, GTrue):
        return FTrue()
    if isinstance(g, GFalse):
        return FFalse()
    if isinstance(g, GAnd):
        return And([translate_guard(g.l, arities), translate_guard(g.r, arities)])
    if isinstance(g, GOr):
        return Or([translate_guard(g.l, arities), translate_guard(g.r, arities)])
    if isinstance(g, GNot):
        return Not(translate_guard(g.g, arities))
    if isinstance(g, GCompare):
        if g.lhs is EMPTY and g.rhs is EMPTY:
            return FTrue() if g.op != "≠" else FFalse()
        if g.lhs is EMPTY:
            cols2, phi2 = translate_ra(g.rhs, arities)
            if g.op == "⊆":
                return FTrue()
            cols2, phi2 = _fresh_binder(cols2, phi2)
            base = Not(Exists(cols2, phi2)) if cols2 else Not(phi2)
            return Not(base) if g.op == "≠" else base
        if g.rhs is EMPTY:
            cols1, phi1 = translate_ra(g.lhs, arities)
            cols1, phi1 = _fresh_binder(cols1, phi1)
            base = Not(Exists(cols1, phi1)) if cols1 else Not(phi1)
            return Not(base) if g.op == "≠" else base
        cols1, phi1 = translate_ra(g.lhs, arities)
        cols2, phi2 = translate_ra(g.rhs, arities)
        if len(cols1) != len(cols2):
            raise FolError(f"comparison {g.op} between relations of different arity")
        binder = [Var() for _ in cols1]
        phi1a = _align_and_substitute(phi1, cols1, binder)
        phi2a = _align_and_substitute(phi2, cols2, binder)
        body = Iff(phi1a, phi2a) if g.op in ("=", "≠") else Implies(phi1a, phi2a)
        result = Forall(binder, body) if binder else body
        return Not(result) if g.op == "≠" else result
    raise FolError(f"unsupported guard construct: {g!r}")


# ----------------------------------------------------------------------------------------
# Simplification: constant folding, double-negation, and the one-point rule that turns a
# row-selection equality into a unified variable instead of a dangling `y = z` conjunct.
# ----------------------------------------------------------------------------------------

def _flatten(cls, parts: list[Formula]) -> list[Formula]:
    out = []
    for p in parts:
        if isinstance(p, cls):
            out.extend(p.parts)
        else:
            out.append(p)
    return out


def _occurs(v: Var, t) -> bool:
    return isinstance(t, Var) and t is v


def _eliminate_in_exists(varsl: list[Var], body: Formula) -> tuple[list[Var], Formula]:
    """One-point rule: `∃v,…. v = t ∧ φ` simplifies to `∃…. φ[v := t]` when `t` doesn't
    mention `v`. Only fires on an equality that is an unconditional top-level conjunct
    (never inside `∨`/`¬`), so an equality that is only conditionally true is left explicit.
    """
    remaining = list(varsl)
    conjuncts = _flatten(And, [body]) if isinstance(body, And) else [body]
    changed = True
    while changed:
        changed = False
        for i, c in enumerate(conjuncts):
            if not isinstance(c, Eq):
                continue
            lhs, rhs = c.lhs, c.rhs
            v, t = None, None
            if isinstance(lhs, Var) and lhs in remaining and not _occurs(lhs, rhs):
                v, t = lhs, rhs
            elif isinstance(rhs, Var) and rhs in remaining and not _occurs(rhs, lhs):
                v, t = rhs, lhs
            if v is None:
                continue
            mapping = {v: t}
            conjuncts = [substitute(cc, mapping) for j, cc in enumerate(conjuncts) if j != i]
            remaining = [x for x in remaining if x is not v]
            changed = True
            break
    if not conjuncts:
        new_body: Formula = FTrue()
    elif len(conjuncts) == 1:
        new_body = conjuncts[0]
    else:
        new_body = And(conjuncts)
    return remaining, new_body


def simplify(f: Formula) -> Formula:
    prev = None
    cur = f
    while prev is None or _formula_repr(cur) != _formula_repr(prev):
        prev = cur
        cur = _simplify_once(cur)
    return cur


def _simplify_once(f: Formula) -> Formula:
    if isinstance(f, (FTrue, FFalse, Atom)):
        return f
    if isinstance(f, Eq):
        if isinstance(f.lhs, Var) and isinstance(f.rhs, Var) and f.lhs is f.rhs:
            return FTrue()
        if isinstance(f.lhs, DataLit) and isinstance(f.rhs, DataLit):
            return FTrue() if f.lhs == f.rhs else FFalse()
        return f
    if isinstance(f, Not):
        inner = _simplify_once(f.f)
        if isinstance(inner, Not):
            return inner.f
        if isinstance(inner, FTrue):
            return FFalse()
        if isinstance(inner, FFalse):
            return FTrue()
        return Not(inner)
    if isinstance(f, And):
        parts = [_simplify_once(p) for p in f.parts]
        parts = _flatten(And, parts)
        if any(isinstance(p, FFalse) for p in parts):
            return FFalse()
        parts = [p for p in parts if not isinstance(p, FTrue)]
        if not parts:
            return FTrue()
        if len(parts) == 1:
            return parts[0]
        return And(parts)
    if isinstance(f, Or):
        parts = [_simplify_once(p) for p in f.parts]
        parts = _flatten(Or, parts)
        if any(isinstance(p, FTrue) for p in parts):
            return FTrue()
        parts = [p for p in parts if not isinstance(p, FFalse)]
        if not parts:
            return FFalse()
        if len(parts) == 1:
            return parts[0]
        return Or(parts)
    if isinstance(f, Implies):
        l = _simplify_once(f.l)
        r = _simplify_once(f.r)
        if isinstance(l, FFalse) or isinstance(r, FTrue):
            return FTrue()
        if isinstance(l, FTrue):
            return r
        if isinstance(r, FFalse):
            return _simplify_once(Not(l))
        return Implies(l, r)
    if isinstance(f, Iff):
        l = _simplify_once(f.l)
        r = _simplify_once(f.r)
        if isinstance(l, FTrue):
            return r
        if isinstance(r, FTrue):
            return l
        if isinstance(l, FFalse):
            return _simplify_once(Not(r))
        if isinstance(r, FFalse):
            return _simplify_once(Not(l))
        return Iff(l, r)
    if isinstance(f, Exists):
        body = _simplify_once(f.body)
        varsl, body = _eliminate_in_exists(f.varsl, body)
        if not varsl:
            return body
        return Exists(varsl, body)
    if isinstance(f, Forall):
        body = _simplify_once(f.body)
        if not f.varsl:
            return body
        if isinstance(body, Not):
            # ∀x̄.¬φ reads better as ¬∃x̄.φ (used by the `A ⊆ ∅`/`A = ∅` translations).
            return Not(Exists(f.varsl, body.f))
        return Forall(f.varsl, body)
    raise FolError(f"simplify: unhandled formula node {f!r}")


def _formula_repr(f: Formula) -> str:
    """A structural key for the simplification fixpoint check (identity-stable on Var)."""
    if isinstance(f, FTrue):
        return "T"
    if isinstance(f, FFalse):
        return "F"
    if isinstance(f, Atom):
        arg_keys = (a.render() if isinstance(a, DataLit) else str(id(a)) for a in f.args)
        return f"A{f.pred}(" + ",".join(arg_keys) + ")"
    if isinstance(f, Eq):
        lhs = f.lhs.render() if isinstance(f.lhs, DataLit) else str(id(f.lhs))
        rhs = f.rhs.render() if isinstance(f.rhs, DataLit) else str(id(f.rhs))
        return f"E{lhs}={rhs}"
    if isinstance(f, Not):
        return f"~({_formula_repr(f.f)})"
    if isinstance(f, And):
        return "(" + "&".join(_formula_repr(p) for p in f.parts) + ")"
    if isinstance(f, Or):
        return "(" + "|".join(_formula_repr(p) for p in f.parts) + ")"
    if isinstance(f, Implies):
        return f"({_formula_repr(f.l)}->{_formula_repr(f.r)})"
    if isinstance(f, Iff):
        return f"({_formula_repr(f.l)}<->{_formula_repr(f.r)})"
    if isinstance(f, Exists):
        return "E[" + ",".join(str(id(v)) for v in f.varsl) + "]." + _formula_repr(f.body)
    if isinstance(f, Forall):
        return "A[" + ",".join(str(id(v)) for v in f.varsl) + "]." + _formula_repr(f.body)
    raise FolError(f"_formula_repr: unhandled formula node {f!r}")


# ----------------------------------------------------------------------------------------
# Rendering
# ----------------------------------------------------------------------------------------

_NAME_SEED = ["x", "y", "z", "u", "v", "w"]


def _name_stream():
    for n in _NAME_SEED:
        yield n
    k = 1
    while True:
        yield f"x{k}"
        k += 1


# Precedence levels, loose to tight: Iff < Implies < Or < And < Not/Quantifier < Atom.
_PREC = {"Iff": 1, "Implies": 2, "Or": 3, "And": 4, "Not": 5, "Quant": 5, "Atom": 6}


def _prec(f: Formula) -> int:
    if isinstance(f, Iff):
        return _PREC["Iff"]
    if isinstance(f, Implies):
        return _PREC["Implies"]
    if isinstance(f, Or):
        return _PREC["Or"]
    if isinstance(f, And):
        return _PREC["And"]
    if isinstance(f, Not):
        return _PREC["Not"]
    if isinstance(f, (Exists, Forall)):
        return _PREC["Quant"]
    return _PREC["Atom"]


class _Renderer:
    def __init__(self):
        self.names: dict = {}
        self.stream = _name_stream()

    def name(self, v: Var) -> str:
        if v not in self.names:
            self.names[v] = next(self.stream)
        return self.names[v]

    def term(self, t) -> str:
        return t.render() if isinstance(t, DataLit) else self.name(t)

    def render(self, f: Formula) -> str:
        return self._go(f, is_last=True)

    @staticmethod
    def _is_quantifierish(f: Formula) -> bool:
        """True through a chain of `¬`: a bare or negated quantifier reads unboundedly far
        to the right (by the usual FOL convention that a quantifier's scope is everything
        syntactically after it), so it needs its own parentheses wherever something could
        follow it that must NOT fall inside that scope.
        """
        while isinstance(f, Not):
            f = f.f
        return isinstance(f, (Exists, Forall))

    def _wrap(self, f: Formula, parent_prec: int, is_last: bool) -> str:
        """Render `f` as an operand of a node with precedence `parent_prec`. `is_last` says
        whether nothing else in the enclosing formula's linear text follows `f`; only then
        may an unparenthesized quantifier inside `f` safely extend its scope rightward.
        """
        if self._is_quantifierish(f):
            needs = not is_last
        else:
            needs = _prec(f) < parent_prec
        inner_is_last = True if needs else is_last
        text = self._go(f, is_last=inner_is_last)
        return f"({text})" if needs else text

    def _wrap_antecedent(self, f: Formula, prec: int) -> str:
        """The left side of `→`/`↔`: never last (the arrow and right side always follow),
        and even same-precedence self-nesting (`(A → B) → C`) must be parenthesized since
        the arrow is not associative in the rendering.
        """
        needs = self._is_quantifierish(f) or _prec(f) <= prec
        inner_is_last = True if needs else False
        text = self._go(f, is_last=inner_is_last)
        return f"({text})" if needs else text

    def _go(self, f: Formula, is_last: bool) -> str:
        if isinstance(f, FTrue):
            return "⊤"
        if isinstance(f, FFalse):
            return "⊥"
        if isinstance(f, Atom):
            args = ",".join(self.term(a) for a in f.args)
            return f"{f.pred}({args})" if f.args else f.pred
        if isinstance(f, Eq):
            return f"{self.term(f.lhs)} = {self.term(f.rhs)}"
        if isinstance(f, Not):
            child = self._wrap(f.f, _PREC["Not"], is_last=is_last)
            return f"¬{child}"
        if isinstance(f, And):
            prec = _PREC["And"]
            n = len(f.parts)
            pieces = [self._wrap(p, prec, is_last=(is_last and i == n - 1)) for i, p in enumerate(f.parts)]
            return " ∧ ".join(pieces)
        if isinstance(f, Or):
            prec = _PREC["Or"]
            n = len(f.parts)
            pieces = [self._wrap(p, prec, is_last=(is_last and i == n - 1)) for i, p in enumerate(f.parts)]
            return " ∨ ".join(pieces)
        if isinstance(f, Implies):
            prec = _PREC["Implies"]
            lhs = self._wrap_antecedent(f.l, prec)
            rhs = self._wrap(f.r, prec, is_last=is_last)
            return f"{lhs} → {rhs}"
        if isinstance(f, Iff):
            prec = _PREC["Iff"]
            lhs = self._wrap_antecedent(f.l, prec)
            rhs = self._wrap(f.r, prec, is_last=is_last)
            return f"{lhs} ↔ {rhs}"
        if isinstance(f, Exists):
            names = " ".join(self.name(v) for v in f.varsl)
            body = self._wrap(f.body, _PREC["Or"] + 1, is_last=True)
            return f"∃{names}. {body}"
        if isinstance(f, Forall):
            names = " ".join(self.name(v) for v in f.varsl)
            body = self._wrap(f.body, _PREC["Or"] + 1, is_last=True)
            return f"∀{names}. {body}"
        raise FolError(f"render: unhandled formula node {f!r}")


def render_formula(f: Formula) -> str:
    return _Renderer().render(f)


# ----------------------------------------------------------------------------------------
# Public entry point
# ----------------------------------------------------------------------------------------

def translate_to_fol(text: str, arities: dict) -> str:
    """Parse, translate and render one `programAssert!` body (as extracted from
    `Input.lean`) to a first-order-logic reading. Raises `FolError` on any construct this
    module cannot translate; callers must let that fail the build loudly (never skip a
    case silently).
    """
    guard = parse_guard_text(text)
    formula = translate_guard(guard, arities)
    formula = simplify(formula)
    return render_formula(formula)
