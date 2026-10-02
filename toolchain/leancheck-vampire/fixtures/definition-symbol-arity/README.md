# Introduced-definition-symbol arity regression fixtures

Each case directory preserves one leancheck job whose proof the pre-`0002`
binary emitted with an introduced `_sF` definition symbol at disagreeing
arities: declared `ι → ι` or `ι → ι → ι` in the section-variable telescope,
defined by a `let` over that many binders, and then applied to nothing, so
the proof failed to elaborate with `Type mismatch … has type ι → ι → ι but
is expected to have type ι`.

- `unpatched.lean`: the raw standard output of the pinned source before
  `0002` (commit `a75412b26`, binary SHA-256
  `4d7939a1ed1e129ce622d3ef0ea2dba15b49a56ee7dcce20333e2f8ac6560cec`).
- `patched.lean`: the raw standard output of the locked corrected binary,
  which elaborates with the pinned VampLean runtime.

The two outputs are not compared step by step: `0002` corrects the twee
goal transformation itself, so the corrected binary searches a different —
correct — problem and finds a different proof. What is pinned is that every
use of every introduced symbol in the corrected output agrees with its
declaration, that the uncorrected output does not, and that the family as a
whole still defines at least one introduced symbol *with* parameters, which
is the case the emitter's binder handling exists for.

| case | origin | direct profile |
| --- | --- | --- |
| `example0001-init_clause_0` | `Benchmark/Example0001/Certificate/VampireArtifacts/jobs/init_clause_0` | proves |
| `example1076-init_clause_0` | `Legacy/Benchmark2/Example1076/VampireArtifacts/attempt-0000/jobs/init_clause_0` | times out at 7 s and at 30 s |
| `probe-two-parameter-order` | written for this family; two lines of TPTP, no portfolio | n/a |

`example0001-init_clause_0` is the job the certification path labels
`casc_2025` in `framework2_certificate`'s mixed-profile test, and it is the
one whose failure to elaborate kept that label unusable. Its corrected
proof introduces no definition symbol at all — with `_allVars` populated,
the transformation correctly declines to define a linear subterm — so
`example1076-init_clause_0` carries the parameterised case: it is provable
under the CASC schedule and not under the direct one, and its corrected
proof defines `_sF57` and `_sF58` over one parameter each.

Both of those define their symbols over one parameter, which pins the
arity but says nothing about the *order* of two or more. `probe-two-parameter-order`
is the smallest problem that does. Its goal `? [X,Y] : p(f(Y,g(X)))` has a
subterm `f(Y, g(X))` that visits `Y` before `X`, so the transformation
gives the introduced symbol the parameter order `(Y, X)`, whose variable
indices descend. The corrected `let` is

```text
let «_sF0» v1 v0:= («_f» v1 («_g» v0))
have step7 : (∀ v0 v1 : ι, ((«_f» v1 («_g» v0))=(«_sF0» v1 v0))) := fun v1 v0 => rfl
```

An emitter that sorts the binder list by variable index writes
`let «_sF0» v0 v1 := («_f» v1 («_g» v0))` instead, which defines the symbol
with its arguments swapped against every use of it, and Lean rejects the
`rfl`. The case is run without the portfolio (`--twee_goal_transformation
full` on a single strategy) so that the proof is short and the binder list
is the only thing it is about.
