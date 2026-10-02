-- Author: Jesse Comer
import Lean

/-
  A `Job` is one complete Vampire problem to run.

  Jobs have opaque ids chosen by the Lean caller and optional
  scheduling conditions over earlier job outcomes. Rust treats
  ids as labels for policy references, artifact paths, and
  result reporting; it does not infer logical semantics from
  them.
-/

------------------------------------------------------------
-- Scheduler Conditions
------------------------------------------------------------

namespace Whiel

namespace Vampire

/- Outcomes used by the runner policy language. -/
inductive Outcome where
| proved
| refuted
| unknown
| timeout
| error
| skipped
deriving DecidableEq, Repr

namespace Outcome

/- Stable JSON spelling for runner outcomes. -/
def name : Outcome → String
| proved => "proved"
| refuted => "refuted"
| unknown => "unknown"
| timeout => "timeout"
| error => "error"
| skipped => "skipped"

/- JSON string for an outcome. -/
def toJson (outcome : Outcome) : Lean.Json :=
  Lean.Json.str outcome.name

end Outcome

/- Boolean scheduling condition over previous job outcomes. -/
inductive Condition where
| atom (job : String) (outcomes : List Outcome)
| all (conditions : List Condition)
| any (conditions : List Condition)
deriving Repr

namespace Condition

/- JSON object consumed by the Rust runner. -/
def toJson : Condition → Lean.Json
| atom job outcomes =>
    Lean.Json.mkObj
      [ ("job", Lean.Json.str job),
        ( "in",
          Lean.Json.arr
            ((outcomes.map Outcome.toJson).toArray)) ]
| all conditions =>
    Lean.Json.mkObj
      [ ( "and",
          Lean.Json.arr
            ((conditions.map toJson).toArray)) ]
| any conditions =>
    Lean.Json.mkObj
      [ ( "or",
          Lean.Json.arr
            ((conditions.map toJson).toArray)) ]

end Condition

end Vampire
end Whiel

------------------------------------------------------------
-- Jobs
------------------------------------------------------------

namespace Whiel

namespace Vampire

structure Job where
  id : String
  when? : Option Condition := none
  axioms : String
  conjecture : String

namespace Job

/- JSON fields for an optional scheduling condition. -/
def whenFields :
    Option Condition → List (String × Lean.Json)
| none => []
| some condition => [("when", condition.toJson)]

/- JSON object consumed by the Rust runner. -/
def toJson (job : Job) : Lean.Json :=
  Lean.Json.mkObj
    ([("id", Lean.Json.str job.id)] ++
      whenFields job.when? ++
      [ ("axioms", Lean.Json.str job.axioms),
        ("conjecture", Lean.Json.str job.conjecture) ])

end Job

end Vampire

end Whiel
