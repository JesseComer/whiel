# Layer A semantic API

Contract revision 2.0.0. The Rust-mediated
[proposer API](proposer-api.md) owns query authorization, finite-instance selection,
resource accounting and cancellation. Lean owns every admissibility and truth
answer. A proposer never receives a persistent-worker handle.

## Clause validation

`validate_clauses({"clauses": [source, ...]})` returns
`{"results": [{"source": canonical_source, "admitted": true}, ...]}`.
For an inadmissible source the entry instead has `admitted: false` and
`correctable: {code, message, item_index, path, offset}`. The last three diagnostic fields are required and nullable. Results preserve
source order.
The empty input returns an empty result list. The call performs no instance lookup
or evaluation. Any `instances` argument, even an empty list, is rejected as
`invalid_arguments` with the migration direction to `evaluate_clauses`.

## Clause evaluation

`evaluate_clauses({"clauses": [source, ...], "instances": selection})`
requires either `"all_retained"` or an array of tagged sources:

```json
[
  {"kind": "retained", "attempt": 17},
  {"kind": "supplied", "instance": {
    "carrier_keys": ["example canonical Data key"],
    "relations": [{"name": "example ambient relation", "rows": []}]
  }}
]
```

The strings in this illustrative payload are placeholders; use the task's
reported relation names and Lean's canonical Data keys. `instances: []` is valid;
omitted or null selection is an input error. Explicit sources preserve input
order and duplicates. `all_retained` selects available models newest first.
Unknown/nonrefuting retained IDs produce `no_refutation`; unavailable models are
reported in `skipped`, never assigned invented truth values.

The result has `results`, `instances`, `cost`, and `skipped`. Every successful
clause entry has `source`, `admitted: true`, and `holds: boolean[]`; each truth
vector aligns with returned `instances`. Inadmissible clauses have the same
`correctable` diagnostic as validation. Returned source labels have `kind` and
`source_index`; retained labels also have `attempt`. The source index refers to
the explicit array, or to the ordered retained-model selection. Skipped retained
labels include a reason and tuple count. No attempt ID is minted for supplied data.
`cost` is the checked product of source count and evaluated-instance count.

Supplied instances must cover the complete prophecy schema, including generated
relations. Lean requires unique relation names, correct arities, unique tuples,
canonical Data keys and a sorted, nonempty, duplicate-free carrier containing
all tuple cells. Empty relation tables are allowed. Structural well-formedness
implies nothing about reachability, preconditions, refutation or invalidity.
Malformed instance data produces `invalid_instance`, at call level if Lean's
batch diagnostic cannot identify a source. Ordinary bad input is not reported
as a broken worker. Real protocol/worker failures remain `tool_failed`.

Lean evaluates formulas exactly as supplied: no implicit weakest precondition,
prophecy substitution, collapse, program execution or rechecking of a retained
model's original antecedent. A maintenance countermodel can satisfy a clause
and falsify its weakest precondition. Role context comes from the saved
`countermodel` read, not from a guessed interpretation of a Boolean result.

Both calls reuse the internal `evaluate_clauses` worker operation (validation
supplies an empty instance list). Permissions are independent: evaluation may
parse and diagnose clauses even when the separate validation query is disabled.
Validation never permits evaluation implicitly. The ordinary consultation and
host limits apply; cost refusal is explicit and never silently truncates inputs.
Neither success nor error changes Houdini's clauses, levels, Core/Pending/Dead,
evidence dictionary, history/ledger, verification results or proposal epochs.
Request-local data and operational query accounting are separate from that state.

Counterexample checking is submission-only. There is no `evaluate_program`,
trace, direct solver, certificate or standalone counterexample-preflight query.

## A/B internal worker protocol: complete current inventory

Current dispatch is `Whiel/Synthesis/Runtime/FixedAmbientWorker.lean:1630–1727`;
Rust's closed enum is `whiel_runner/src/encoding/protocol.rs:54–91`.
The worker request/response binding includes task/source, scope, protocol,
request and name-environment identities. Rust's context validates the replies;
its crate-private `execute` rejects direct context-owned name extension and
shutdown (`encoding/context.rs:870`). Persistence does not grant C a worker
session of its own.

In the following table, W is `FixedAmbientWorker.lean`; other paths are under
`whiel_runner/src/framework2/`. Payloads are abbreviated for inventory purposes.
This is **not the proposer API table**. All raw worker operations remain private
to A/B. The two Layer A-facing proposer calls above are restricted B adapters.
A semantic operation being implemented in Lean does not grant C direct access
to it. Initialization, evidence checking, certification and process control are
engine-only unless a specifically listed proposer adapter invokes them.

| Worker operation | Request → result | Proposer reachability / owner | Evidence |
|---|---|---|---|
| `ping` | empty → ready | B lifecycle only | W:1633 |
| `describe` | empty → manifest, task/scope, relations, prophecy bindings, components | B bootstrap; relevant data already appears in the immutable push | W:411 |
| `extend_name_env` | constants, relations, next revision → acknowledged bindings | B-owned worker state; no C access; every name is Lean's own name for the symbol | W:493 |
| `admit_clauses` | clause sources and byte budget → canonical clause/component packages or diagnostic | B admission after proposal; no raw C query | W:877; `admission.rs:90` |
| `evaluate_clauses` | clauses, finite instances → diagnostics/canonical clauses/truth vectors and cost | Separate B validation/evaluation wrappers, using retained or caller-supplied instances | W:953; `evaluation_ops.rs:343` |
| `prepare_component` | clause sources, component identity → component body/support | B semantic preparation; no current production Rust wrapper found | W:997 |
| `prepare_task_pieces` | empty → task pieces | B search preparation/cache | W:1082; `pieces.rs:186` |
| `prepare_clause_pieces` | canonical sources/identities → clause pieces | B search preparation/cache | W:1131; `pieces.rs:241` |
| `prepare_support_block` | constant keys → ADOM/distinctness bodies and bindings | B search preparation/cache | W:1165; `pieces.rs:333` |
| `build_exact_obligation` | snapshot, selector → obligation/entailment identities | Lean reference; current Rust callers are tests | W:742; `solver.rs:332` |
| `prepare_exact_obligation` | snapshot, selector, obligation identity → bodies/support/axiom tags | B reference/differential obligation preparation | W:1234; `solver.rs:655` |
| `check_empty_counterexample` | bound exact job → checked empty-model result/definition | B semantic checking | W:1313; `solver.rs:749` |
| `validate_refutation` | bound exact job, interpretation → validated identities/truth/refutation flags | B evidence checking, not a proposer assertion | W:1347; `solver.rs:1118` |
| `extract_precondition_clauses` | empty → protected basis rows/identity/digest/theorem | B initialization | W:1401; `solver.rs:857` |
| `confirm_precondition_row` | bound exact job, source ordinal → checked row/route/theorem | B protected evidence | W:1435; `solver.rs:1004` |
| `emit_certificate` | snapshot → artifact/proof-job bundle | B certification | W:1471; `certificate_ops.rs:367` |
| `package_proof` | imports, job, namespace, raw output → packaged source/digest | B certification | W:1494; `certificate_ops.rs:436` |
| `validate_counterexample` | opaque input → validated instance/fuel/identity or typed rejection | B after candidate submission; no current advisory query | W:1563; `counterexample.rs:281` |
| `emit_invalid_certificate` | fuel, frozen instance/identity → invalidity bundle | B certification | W:1580; `certificate_ops.rs:399` |
| `shutdown` | empty → stopped | B lifecycle only | W:1718 |

## The name-binding contract

A symbol's solver-facing name is a total function of its wire key. Lean owns
that function: `Whiel/Vampire/SolverName.lean` gives each carrier a name, and
`Whiel/Vampire/SolverName/Concrete.lean` fixes it for the two production
carriers, where it is proved injective and a legal TPTP `lower_word`. A
relation is named by its clause source (`op_zE`, `oa_zS`, `yp_zT`, `of_z3`),
and a constant by `k`, a kind letter and an injective encoding of the value
(`kn42`, `kbt`, `kbf`, `ks` and an escape of the string into `[a-z0-9_]`).

Rust recomputes exactly that function from the wire key
(`whiel_runner/src/encoding/solver_name.rs`), because the name environment is
extended synchronously under a mutex and replayed forward to every worker in
the pool; there is no sanitizing pass and no collision suffix, and a key the
function cannot parse is refused rather than given an invented name. On the
fixed-ambient worker Lean remains the authority by validation: `extend_name_env`
refuses a binding whose name is not its own name for the symbol that binding's
key resolves to, so the two sides cannot drift apart silently there. Nothing
about the payload shapes changes with the naming, so neither the worker
protocol version nor the proposer `API_VERSION` moves with it.

Rust's module implements a third key grammar besides the two above: a
one-shot manifest relation key `rel:<Base>:<index>` is named
`r_<index>z<Base>` (decimal index, `z`, alphabetic base). Decoding is
unambiguous because the index is a run of digits immediately followed by the
literal `z`, so a reader takes the maximal digit prefix as the index, requires
`z` next, and reads the alphabetic remainder as the base — the base cannot be
mistaken for more index digits or for the delimiter, so the grammar is
injective. This grammar is used only on the legacy encoding-worker path
(`Whiel/Synthesis/Runtime/EncodingWorker.lean`, carrier `IndexAlphaName`),
where Lean's `SolverName.ofRepr` instance for that carrier is unproved and
spells the same key differently (`r_<Base>_<n>`); the worker there validates
a bound name's legality and the absence of repeats and cross-kind clashes,
but never compares it against `Vampire.solverName`, so the two spellings are
allowed to disagree.
