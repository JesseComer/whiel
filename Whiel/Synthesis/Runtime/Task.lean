-- Author: Jesse Comer
import Whiel.Cmd.PrettyPrint
import Whiel.Concrete.Data
import Whiel.Concrete.IndexAlphaName
import Whiel.Concrete.WhielNames.Notation
import Whiel.Concrete.WhielNames.Order
import Whiel.Hoare.Preproc
import Whiel.Hoare.ProphecySchema
import Mathlib.Data.Finset.Sort

/-
  Lean-evaluated synthesis-task transport.

  `taskJson%` evaluates the trusted input and preprocessing
  declarations. It derives each exact Lean expression
  reference from the syntax of the value it evaluates. Rust
  does not parse a second Whiel syntax tree.

  Key declarations include:
    * `Whiel.Synthesis.Runtime.TaskIdentity`
    * `taskJson%`
    * `liftedTaskJson%`
    * `Whiel.Synthesis.Runtime.writeTaskManifest`
-/

------------------------------------------------------------
-- Task Identity
------------------------------------------------------------

namespace Whiel
namespace Synthesis
namespace Runtime

/- Injective implementation key for a solver-visible symbol. -/
class SolverKey (α : Type) where
  key : α → String
  key_injective : Function.Injective key

namespace SolverKey

/- Sort finite values by their canonical solver keys. -/
def sortByKey
    {α : Type}
    [LinearOrder α]
    [SolverKey α]
    (values : Finset α) : List α :=
  values.sort.mergeSort fun left right =>
    key left < key right

/- Canonical solver keys in strict wire order. -/
def sortedKeys
    {α : Type}
    [LinearOrder α]
    [SolverKey α]
    (values : Finset α) : List String :=
  (sortByKey values).map key

/- Canonical key for one concrete Whiel domain value. -/
def dataKey : Concrete.Data → String
| .num n => "num:" ++ toString n
| .str s => "str:" ++ s
| .bool false => "bool:0"
| .bool true => "bool:1"

/- Canonical key for one concrete Whiel relation name. -/
def relationKey
    (name : Concrete.IndexAlphaName) : String :=
  "rel:" ++ name.baseName.value ++ ":" ++
    toString name.index

/- Decode one canonical concrete-domain key. -/
def dataOfKey? (key : String) : Option Concrete.Data :=
  match key.toList with
  | 'n' :: 'u' :: 'm' :: ':' :: payload =>
      String.ofList payload |>.toNat? |>.map Concrete.Data.num
  | 's' :: 't' :: 'r' :: ':' :: payload =>
      some (.str (String.ofList payload))
  | ['b', 'o', 'o', 'l', ':', '0'] =>
      some (.bool false)
  | ['b', 'o', 'o', 'l', ':', '1'] =>
      some (.bool true)
  | _ => none

/- Canonical concrete-domain keys round-trip through the decoder. -/
theorem dataOfKey?_dataKey
    (value : Concrete.Data) :
    dataOfKey? (dataKey value) = some value := by
  cases value with
  | num value =>
      simp only [dataKey, dataOfKey?, String.toList_append,
        Nat.toString_eq_repr, Nat.toList_repr]
      change Option.map Concrete.Data.num
          (String.ofList (Nat.toDigits 10 value)).toNat? =
        some (Concrete.Data.num value)
      rw [← Nat.toString_eq_ofList_toDigits]
      simp only [Nat.toString_eq_repr,
        Nat.toNat?_repr, Option.map_some]
  | str value =>
      simp [dataOfKey?, dataKey]
  | bool value =>
      cases value <;> simp [dataOfKey?, dataKey]

/- Concrete data keys uniquely identify values. -/
theorem dataKey_injective :
    Function.Injective dataKey := by
  intro left right h
  have hDecoded := congrArg dataOfKey? h
  simpa only [dataOfKey?_dataKey, Option.some.injEq] using hDecoded

/- Split two alphabetic bases at their first delimiter. -/
private theorem alphaDelimiter_eq
    {left right suffixLeft suffixRight : List Char}
    (hLeft : left.all Char.isAlpha = true)
    (hRight : right.all Char.isAlpha = true)
    (h : left ++ ':' :: suffixLeft =
      right ++ ':' :: suffixRight) :
    left = right ∧ suffixLeft = suffixRight := by
  induction left generalizing right with
  | nil =>
      cases right with
      | nil => simpa using h
      | cons head tail =>
          simp only [List.nil_append, List.cons_append] at h
          have hHead : head = ':' := by
            exact (List.cons.inj h).1.symm
          subst head
          simp at hRight
  | cons head tail ih =>
      cases right with
      | nil =>
          simp only [List.cons_append, List.nil_append] at h
          have hHead : head = ':' := (List.cons.inj h).1
          subst head
          simp at hLeft
      | cons other rest =>
          simp only [List.cons_append] at h
          have hHeads : head = other := (List.cons.inj h).1
          have hTails : tail ++ ':' :: suffixLeft =
              rest ++ ':' :: suffixRight :=
            (List.cons.inj h).2
          subst other
          have hLeftTail : tail.all Char.isAlpha = true := by
            have hBoth : head.isAlpha = true ∧
                tail.all Char.isAlpha = true := by
              simpa only [List.all_cons, Bool.and_eq_true]
                using hLeft
            exact hBoth.2
          have hRightTail : rest.all Char.isAlpha = true := by
            have hBoth : head.isAlpha = true ∧
                rest.all Char.isAlpha = true := by
              simpa only [List.all_cons, Bool.and_eq_true]
                using hRight
            exact hBoth.2
          have hRest := ih hLeftTail hRightTail hTails
          exact ⟨congrArg (List.cons head) hRest.1, hRest.2⟩

/- Concrete relation keys uniquely identify relation names. -/
theorem relationKey_injective :
    Function.Injective relationKey := by
  intro left right h
  cases left with
  | mk leftBase leftIndex =>
      cases right with
      | mk rightBase rightIndex =>
          have hList := congrArg String.toList h
          simp only [relationKey, String.toList_append] at hList
          have hWithoutPrefix :
              leftBase.value.toList ++ ':' :: leftIndex.repr.toList =
                rightBase.value.toList ++ ':' ::
                  rightIndex.repr.toList := by
            apply List.append_right_injective
              (s := "rel:".toList)
            simpa [List.append_assoc] using hList
          have hParts := alphaDelimiter_eq
            leftBase.isAlpha rightBase.isAlpha hWithoutPrefix
          have hBase : leftBase = rightBase := by
            cases leftBase
            cases rightBase
            congr
            exact String.toList_inj.mp hParts.1
          have hIndex : leftIndex = rightIndex := by
            apply Nat.repr_injective
            exact String.toList_inj.mp hParts.2
          cases hBase
          cases hIndex
          rfl

instance : SolverKey Concrete.Data where
  key := dataKey
  key_injective := dataKey_injective

instance : SolverKey Concrete.IndexAlphaName where
  key := relationKey
  key_injective := relationKey_injective

/- Program-name keys preserve every name constructor. -/
instance : SolverKey Concrete.ProgramNames where
  key := Concrete.ProgramNames.encode
  key_injective := Concrete.ProgramNames.encode_injective

/- Fixed-ambient keys preserve every name constructor. -/
instance : SolverKey Concrete.WhielNames where
  key := Concrete.WhielNames.encode
  key_injective := Concrete.WhielNames.encode_injective

end SolverKey

/- Exact implementation identity for one task export. -/
structure TaskIdentity where
  canonicalId : String
  moduleName : String
  namespaceName : String
  sourceSha256 : String
  semanticVersion : Nat := 1
  encodingVersion : Nat := 1

/- JSON whose expression references are syntax-bound. -/
structure BoundTaskManifest where
  private mk ::
  private json : Lean.Json

/- Read a bound manifest. -/
def BoundTaskManifest.toJson
    (manifest : BoundTaskManifest) : Lean.Json :=
  manifest.json

end Runtime
end Synthesis
end Whiel

------------------------------------------------------------
-- Task JSON
------------------------------------------------------------

namespace Whiel
namespace Synthesis
namespace Runtime

private def valueJson
    (expression display : String) : Lean.Json :=
  Lean.Json.mkObj
    [ ("expression", Lean.Json.str expression),
      ("display", Lean.Json.str display) ]

private def identityJson
    (identity : TaskIdentity) : Lean.Json :=
  Lean.Json.mkObj
    [ ("canonical_id",
        Lean.Json.str identity.canonicalId),
      ("module", Lean.Json.str identity.moduleName),
      ("namespace",
        Lean.Json.str identity.namespaceName),
      ("source_sha256",
        Lean.Json.str identity.sourceSha256) ]

private def keyListJson
    {α : Type}
    [SolverKey α]
    (values : List α) : Lean.Json :=
  Lean.Json.arr
    ((values.map
      (fun value => Lean.Json.str (SolverKey.key value))).toArray)

private def relationJson
    {A : Type}
    [RelationNames A]
    [SolverKey A]
    (Γ : UnnamedSchema A)
    (relation : Γ.syms) : Lean.Json :=
  Lean.Json.mkObj
    [ ("key", Lean.Json.str (SolverKey.key relation.1)),
      ("arity", Lean.Json.num (Γ.arity relation)) ]

private def sourceJson
    {A D : Type}
    [RelationNames A]
    [Domain D]
    [LinearOrder A]
    [LinearOrder D]
    [SolverKey A]
    [SolverKey D]
    {Γ : UnnamedSchema A}
    (sourceId expression noBoundExpression : String)
    (formula : AssertExpr D Γ) : Lean.Json :=
  Lean.Json.mkObj
    [ ("source_id", Lean.Json.str sourceId),
      ("expression", Lean.Json.str expression),
      ("no_bound_expression",
        Lean.Json.str noBoundExpression),
      ("constants",
        keyListJson (formula.constants.sort (· ≤ ·))),
      ("relations",
        keyListJson (formula.freeSymbols.sort (· ≤ ·))) ]

private def qfSourceJson
    {A D : Type}
    [RelationNames A]
    [Domain D]
    [LinearOrder A]
    [LinearOrder D]
    [SolverKey A]
    [SolverKey D]
    {Γ : UnnamedSchema A}
    (sourceId : String)
    (formula : QFAssertExpr D Γ) :
    Lean.Json :=
  Lean.Json.mkObj
    [ ("source_id", Lean.Json.str sourceId),
      ("constants",
        keyListJson (formula.constants.sort (· ≤ ·))),
      ("relations",
        keyListJson (formula.symbols.sort (· ≤ ·))) ]

private def solverJson
    {A D : Type}
    [RelationNames A]
    [Domain D]
    [LinearOrder A]
    [LinearOrder D]
    [SolverKey A]
    [SolverKey D]
    (Γ : UnnamedSchema A)
    (inputPre : AssertExpr D Γ)
    (inputCmd : Cmd D Γ)
    (inputPost : AssertExpr D Γ)
    (preprocExpression : String)
    (P : Hoare.Preproc (Γ := Γ)
      inputPre inputCmd inputPost) : Lean.Json :=
  let constants :=
    inputPre.constants ∪ inputCmd.constants ∪
      inputPost.constants ∪ P.loopPre.constants ∪
      P.loopGuard.constants ∪ P.loopCmd.constants ∪
      P.loopPost.constants
  Lean.Json.mkObj
    [ ("schema_relations",
        Lean.Json.arr
          ((Γ.syms.attach.sort).map
            (relationJson Γ) |>.toArray)),
      ("task_constants",
        keyListJson (constants.sort (· ≤ ·))),
      ("preprocessed_pre",
        sourceJson "task.preprocessed_pre"
          (preprocExpression ++ ".loopPre")
          (preprocExpression ++ ".loopPre_noBound")
          P.loopPre),
      ("preprocessed_post",
        sourceJson "task.preprocessed_post"
          (preprocExpression ++ ".loopPost")
          (preprocExpression ++ ".loopPost_noBound")
          P.loopPost),
      ("loop_guard",
        qfSourceJson "task.loop_guard" P.loopGuard),
      ("negated_loop_guard",
        qfSourceJson "task.negated_loop_guard"
          (QFAssertExpr.not P.loopGuard)) ]

/-
  Evaluate one trusted source triple and its supplied
  preprocessing evidence into the versioned Rust transport.
-/
private def taskJsonBound
    {A D : Type}
    [RelationNames A]
    [Domain D]
    [LinearOrder A]
    [LinearOrder D]
    [SolverKey A]
    [SolverKey D]
    (identity : TaskIdentity)
    (schemaExpression : String)
    (schema : UnnamedSchema A)
    (inputPreExpression : String)
    (inputPre : AssertExpr D schema)
    (inputCmdExpression : String)
    (inputCmd : Cmd D schema)
    (inputPostExpression : String)
    (inputPost : AssertExpr D schema)
    (preprocExpression : String)
    (P : Hoare.Preproc inputPre inputCmd inputPost) :
    BoundTaskManifest :=
  ⟨Lean.Json.mkObj
    [ ("format_version", Lean.Json.num 3),
      ("semantic_version",
        Lean.Json.num identity.semanticVersion),
      ("encoding_version",
        Lean.Json.num identity.encodingVersion),
      ("identity", identityJson identity),
      ("schema",
        valueJson
          schemaExpression
          schema.pretty),
      ("original",
        Lean.Json.mkObj
          [ ("pre",
              valueJson
                inputPreExpression
                inputPre.pretty),
            ("command",
              valueJson
                inputCmdExpression
                inputCmd.pretty),
            ("post",
              valueJson
                inputPostExpression
                inputPost.pretty) ]),
      ("preprocessed",
        Lean.Json.mkObj
          [ ("pre",
              valueJson
                (preprocExpression ++ ".loopPre")
                P.loopPre.pretty),
            ("command",
              valueJson
                (preprocExpression ++ ".loopCmd")
                P.loopCmd.pretty),
            ("post",
              valueJson
                (preprocExpression ++ ".loopPost")
                P.loopPost.pretty) ]),
      ("preprocessing_evidence",
        Lean.Json.mkObj
          [ ("expression",
              Lean.Json.str preprocExpression) ]),
      ("solver",
        solverJson schema inputPre inputCmd inputPost
          preprocExpression P) ]⟩

/-
  Evaluate one program-name input and its lifted loop into the
  versioned Rust transport. The `schema`, `preprocessed`, and
  `solver` sections describe the lifted loop over the computed
  prophecy schema with `WhielNames` solver keys; `original` is
  the raw triple, display-only.
-/
private def taskJsonLifted
    {D : Type}
    [Domain D]
    [LinearOrder D]
    [SolverKey D]
    {Gamma : UnnamedSchema Concrete.ProgramNames}
    (identity : TaskIdentity)
    (inputPreExpression : String)
    (inputPre : AssertExpr D Gamma)
    (inputCmdExpression : String)
    (inputCmd : Cmd D Gamma)
    (inputPostExpression : String)
    (inputPost : AssertExpr D Gamma)
    (preprocExpression : String)
    (P : Hoare.Preproc inputPre inputCmd inputPost) :
    BoundTaskManifest :=
  let loop := P.liftedLoop
  let loopExpression := preprocExpression ++ ".liftedLoop"
  let constants :=
    loop.pre.constants ∪ loop.guard.constants ∪
      loop.body.constants ∪ loop.post.constants
  ⟨Lean.Json.mkObj
    [ ("format_version", Lean.Json.num 4),
      ("semantic_version",
        Lean.Json.num identity.semanticVersion),
      ("encoding_version",
        Lean.Json.num identity.encodingVersion),
      ("identity", identityJson identity),
      ("schema",
        valueJson
          (preprocExpression ++ ".prophecySchema")
          P.prophecySchema.pretty),
      ("original",
        Lean.Json.mkObj
          [ ("pre",
              valueJson inputPreExpression inputPre.pretty),
            ("command",
              valueJson inputCmdExpression inputCmd.pretty),
            ("post",
              valueJson inputPostExpression inputPost.pretty) ]),
      ("preprocessed",
        Lean.Json.mkObj
          [ ("pre",
              valueJson
                (loopExpression ++ ".preAssert")
                loop.preAssert.pretty),
            ("command",
              valueJson
                (loopExpression ++ ".cmd")
                loop.cmd.pretty),
            ("post",
              valueJson
                (loopExpression ++ ".postAssert")
                loop.postAssert.pretty) ]),
      ("preprocessing_evidence",
        Lean.Json.mkObj
          [ ("expression",
              Lean.Json.str preprocExpression) ]),
      ("solver",
        Lean.Json.mkObj
          [ ("schema_relations",
              Lean.Json.arr
                ((P.prophecySchema.syms.attach.sort).map
                  (relationJson P.prophecySchema) |>.toArray)),
            ("task_constants",
              keyListJson (constants.sort (· ≤ ·))),
            ("preprocessed_pre",
              sourceJson "task.preprocessed_pre"
                (loopExpression ++ ".preAssert")
                (loopExpression ++ ".preAssert_noBound")
                loop.preAssert),
            ("preprocessed_post",
              sourceJson "task.preprocessed_post"
                (loopExpression ++ ".postAssert")
                (loopExpression ++ ".postAssert_noBound")
                loop.postAssert),
            ("loop_guard",
              qfSourceJson "task.loop_guard" loop.guard),
            ("negated_loop_guard",
              qfSourceJson "task.negated_loop_guard"
                (QFAssertExpr.not loop.guard)) ]) ]⟩

private def exactDeclarationName
    (declaration : Lean.Syntax) :
    Lean.MacroM Lean.Term := do
  let name := declaration.getId.toString
  unless name.contains '.' do
    Lean.Macro.throwErrorAt declaration
      "expected a fully qualified declaration name"
  pure ⟨Lean.Syntax.mkStrLit name⟩

syntax (name := taskJsonSyntax)
  "taskJson% " term ", " ident ", " ident ", " ident
    ", " ident ", " ident : term

macro_rules
  | `(taskJson% $identity:term,
      $schema:ident, $inputPre:ident, $inputCmd:ident,
      $inputPost:ident, $preproc:ident) => do
      let schemaName ← exactDeclarationName schema
      let inputPreName ← exactDeclarationName inputPre
      let inputCmdName ← exactDeclarationName inputCmd
      let inputPostName ← exactDeclarationName inputPost
      let preprocName ← exactDeclarationName preproc
      `(taskJsonBound
          $identity
          $schemaName $schema
          $inputPreName $inputPre
          $inputCmdName $inputCmd
          $inputPostName $inputPost
          $preprocName $preproc)

syntax (name := liftedTaskJsonSyntax)
  "liftedTaskJson% " term ", " ident ", " ident ", " ident
    ", " ident : term

macro_rules
  | `(liftedTaskJson% $identity:term,
      $inputPre:ident, $inputCmd:ident, $inputPost:ident,
      $preproc:ident) => do
      let inputPreName ← exactDeclarationName inputPre
      let inputCmdName ← exactDeclarationName inputCmd
      let inputPostName ← exactDeclarationName inputPost
      let preprocName ← exactDeclarationName preproc
      `(taskJsonLifted
          $identity
          $inputPreName $inputPre
          $inputCmdName $inputCmd
          $inputPostName $inputPost
          $preprocName $preproc)

/- Write one complete task transport file. -/
def writeTaskManifest
    (path : System.FilePath)
    (task : BoundTaskManifest) :
    IO Unit :=
  IO.FS.writeFile path
    ((Lean.Json.pretty
      task.json
      100) ++ "\n")

end Runtime
end Synthesis
end Whiel
