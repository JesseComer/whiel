-- Author: Jesse Comer
import Whiel.Synthesis.Enumerators.Registry
import Whiel.Synthesis.Enumerators.Fast.Freshness
import Whiel.Synthesis.Enumerators.Seeded.Freshness
import Whiel.Synthesis.Enumerators.Capped.Freshness
import Whiel.Synthesis.Runtime.ReferenceProposal
import Whiel.Synthesis.Runtime.FastProposal

/-
  The concrete realization tables, and their binding to the
  wire-level realization identifiers. Every entry's proofs
  come from its own realization's development: the reference
  supports itself (`ReferenceProposal.formulas_coversReference`),
  and the fast, seeded, and capped realizations are proved
  against the reference. No entry's registration depends on
  another realization's theorems.

  `provenEntry` maps every arm of the wire `Realization`
  inductive to a `RegisteredRealization`. The match is total,
  so adding a wire arm without a proven registry entry is a
  compile error in this module --- the gate the registry
  exists to provide. `provenEntry_id` and
  `provenEntry_version` couple each entry to its arm's
  transport identity, so the wire strings and the proved
  streams cannot drift apart silently.
-/

------------------------------------------------------------
-- Proven Entries
------------------------------------------------------------

namespace Whiel

namespace Synthesis

namespace Runtime

namespace FastProposal

open DisjunctiveClause
open Whiel.Synthesis.Enumerators

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Γ : UnnamedSchema A}
variable [LinearOrder A] [LinearOrder D]

/- The canonical reference realization, registered. -/
def referenceEntry :
    RegisteredRealization A D Γ where
  id := "lean-reference-v3"
  version := ReferenceProposal.version
  stream := fun alphabet _ =>
    ReferenceProposal.formulas alphabet
  covers := fun alphabet _ =>
    ReferenceProposal.formulas_coversReference alphabet
  nodup := fun alphabet _ stage =>
    ReferenceProposal.formulas_nodup alphabet stage

/- The fast v1 realization, registered. -/
def fastEntry :
    RegisteredRealization A D Γ where
  id := Fast.realizationId
  version := Fast.realizationVersion
  stream := fun alphabet _ =>
    Fast.outputThrough alphabet
  covers := fun alphabet _ =>
    Fast.coversReference alphabet
  nodup := fun alphabet _ stage =>
    Fast.outputThrough_nodup alphabet stage

/- The seeded two-stream realization, registered. -/
def seededEntry :
    RegisteredRealization A D Γ where
  id := Seeded.realizationId
  version := Seeded.realizationVersion
  stream := fun alphabet seeds =>
    Seeded.outputThroughSeeded alphabet seeds
  covers := fun alphabet seeds =>
    Seeded.seededCoversReference alphabet seeds
  nodup := fun alphabet seeds stage =>
    Seeded.outputThroughSeeded_nodup alphabet seeds stage

/-
  The capped seeded realization, registered at the default
  amnesty schedule, whose periodic full-admission stages
  witness the `Admitting` hypothesis by construction.
-/
def cappedEntry :
    RegisteredRealization A D Γ where
  id := Capped.realizationId
  version := Capped.realizationVersion
  stream := fun alphabet seeds =>
    Capped.outputThroughSeededCapped alphabet seeds
      (Capped.defaultSchedule seeds.card)
  covers := fun alphabet seeds =>
    Capped.cappedCoversReference alphabet seeds
      (Capped.defaultSchedule seeds.card)
      (Capped.defaultSchedule_admitting alphabet seeds)
  nodup := fun alphabet seeds stage =>
    Capped.outputThroughSeededCapped_nodup alphabet seeds
      (Capped.defaultSchedule seeds.card) stage

------------------------------------------------------------
-- Wire Binding
------------------------------------------------------------

/-
  Every wire realization arm resolves to a proven entry. A
  new arm without a registered proof fails to elaborate
  here.
-/
def Realization.provenEntry :
    Realization → RegisteredRealization A D Γ
| .referenceV3 => referenceEntry
| .fastV1 => fastEntry
| .seededV1 => seededEntry
| .cappedV1 => cappedEntry

/- Registered identities agree with transport identities. -/
theorem Realization.provenEntry_id
    (realization : Realization) :
    (Realization.provenEntry
      (A := A) (D := D) (Γ := Γ) realization).id =
      realization.id := by
  cases realization <;> rfl

/- Registered versions agree with transport versions. -/
theorem Realization.provenEntry_version
    (realization : Realization) :
    (Realization.provenEntry
      (A := A) (D := D) (Γ := Γ) realization).version =
      realization.version := by
  cases realization <;> rfl

end FastProposal

end Runtime

end Synthesis

end Whiel
