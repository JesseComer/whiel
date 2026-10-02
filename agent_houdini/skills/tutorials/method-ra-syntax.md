---
id: method-ra-syntax
program_type: general-method
description: WHIEL assert![...] relational-algebra and assertion syntax that every candidate invariant must respect (new Whiel notation).
---

# method-ra-syntax

**Key insight:** Always wrap the operand of a prefix operator `σ[..]` / `π[..]` in parentheses when it is anything but a single relation, and especially when it meets a binary operator (`∪`, `∖`, `×`, `⊆`, `=`, `≠`). Conjunctions use `∧`.

**Final invariant (template):** `N/A (syntax reference)`

## Walkthrough

### RA operators

| Operator | Meaning |
|---|---|
| `E ∪ T` | set union (same arity) |
| `E × T` | product (arity(E) + arity(T)) |
| `E ∖ T` | set difference (same arity) |
| `σ[#i = #j] X` | selection: keep tuples with column `i` equal to column `j` (0-indexed) |
| `σ[#i = c] X` | selection: keep tuples whose column `i` equals the constant `c` |
| `π[i, j, ...] X` | projection: keep the listed columns, in that order |
| `∅[n]` | the empty relation of arity `n` (inside RA expressions) |
| `⊤` | the top relation; `{d}` a singleton holding data literal `d` |

### Composition cheat-sheet

Binary relation composition `X ; Y` is written:

```
π[0, 3] (σ[#1 = #2] (X × Y))
```

`X × Y` yields 4-column tuples; `σ[#1 = #2]` equates X's 2nd column with Y's 1st; `π[0, 3]` keeps X's 1st and Y's 2nd.

### The #1 parse-failure cause

`σ[..]` and `π[..]` are **prefix** operators. Parenthesize their operand:

```
WRONG:  π[0, 3] σ[#1 = #2] (E × T)
RIGHT:  π[0, 3] (σ[#1 = #2] (E × T))

WRONG:  π[0, 3] (σ[#1 = #2] (R × R)) ⊆ R       -- ok on the left, but...
RIGHT:  (π[0, 3] (σ[#1 = #2] (R × R))) ⊆ R      -- wrap the whole proj before ⊆
```

Every prefix-operator application that appears as an operand of `∪`/`∖`/`×`/`⊆`/`=`/`≠` must be wrapped in its own parentheses.

### There is NO intersection

The grammar has **no `∩`**. Do not use it. Express what you need with `∪`, `∖`, `×`, selection, and projection only.

### Empty relation

Inside an RA expression use `∅[n]` (arity annotated). The bare `∅` is allowed ONLY directly against a relation in a comparison: `e = ∅`, `∅ = e`, `e ⊆ ∅`, `∅ ⊆ e`, `e ≠ ∅`, `∅ ≠ e`.

### Assertion / guard syntax

| Form | Use |
|---|---|
| `E1 ⊆ E2` | subset |
| `E1 = E2` | equality |
| `E1 ≠ E2` | inequality |
| `φ ∧ ψ` | conjunction |
| `φ ∨ ψ` | disjunction |
| `¬φ` | negation |

Conjunctions may be written left-to-right (`A ∧ B ∧ C`); parenthesize freely for clarity (`(A) ∧ ((B) ∧ (C))`).

### Quantifying auxiliary relations

If you need a fresh relation not in the schema, introduce it existentially: `∃ X_n . φ` where the suffix `n ≥ 2` and the base name `X` is in the schema (it inherits `X`'s arity). For most invariants you only need the schema relations directly.

### Don't invent body expressions

When writing a def-equality clause (`S = ...`), transcribe the literal RHS of the loop body's assignment verbatim from the loop-only command. Don't "simplify" or substitute equivalents — the verifier treats syntactic siblings as distinct until Vampire proves them equal.

### Names

Use relation names exactly as the schema lists them (e.g. `E`, `T`, `T_2`, `TBound`). A name like `T_2` is a distinct schema relation, not a typo. Call `whiel_get_program` for the authoritative schema and the loop-only triple you must target.
