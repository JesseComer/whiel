-- Author: Jesse Comer
import Whiel.Concrete.Notation
import Whiel.Eval.CounterExample.ProgramInstance

/-
  Concrete instance notation over the `ProgramNames`
  carrier, completing the `programSch!`, `programAssert!`,
  `programQF!` and `programCmd!` family with `programInst!`.

  Key declarations include:
    * `programInst![...]`

  Grammar:

    programInst![ Γ ]
    programInst![ Γ | update ; update ; ... ]

  `Γ` is any term of type `UnnamedSchema ProgramNames`, and
  each update is one of

    X := []
    X := [[c, ...], [c, ...], ...]

  `X` is a relation identifier in the `program` spelling
  read by `Notation.programNameTerm`, the same reader
  `programSch!` and `programCmd!` use: `X` and `X_n` for the
  program symbol at index `0` and at a canonical positive
  index `n`, `X_aux` and `X_aux_n` for the auxiliary symbol,
  and the reserved `flag_i_n` for a flag. Each `c` is a
  domain constant in the `programCmd!` spellings: a decimal
  numeral is `Data.num`, a string literal is `Data.str`,
  `true` and `false` are `Data.bool`, and any other term is
  elaborated at type `Data`.

  A relation the notation does not mention is empty in the
  instance, `X := []` names an explicitly empty relation,
  and a nullary relation is written `X := [[]]`. Every name
  must be a symbol of `Γ`, no name may be repeated, and
  every row must have exactly the schema arity of its
  relation: a name or a row the schema does not admit is an
  elaboration error rather than a silently dropped row.

  The notation elaborates to
  `ProgramInstance.ofKeyedRows Γ` applied to the same keyed
  rows, with each relation's canonical
  `ProgramNames.encode` key computed at elaboration time.
  The equality between a `programInst!` instance and the
  corresponding `ofKeyedRows` instance is therefore `rfl`,
  and the notation kernel-reduces exactly as `ofKeyedRows`
  does: structural recursion only, with no `Acc.rec`, which
  is what an invalidity certificate's kernel check needs.
-/

------------------------------------------------------------
-- Program Instance Syntax
------------------------------------------------------------

declare_syntax_cat whiel_program_inst_update

syntax ident " := " "[" "]" : whiel_program_inst_update
syntax ident " := " "[" "[" term,* "]"
  ("," "[" term,* "]")* "]" :
  whiel_program_inst_update

syntax (name := whielProgramInstanceEmptyNotation)
  "programInst![" term "]" : term

syntax (name := whielProgramInstanceNotation)
  "programInst![" term " | " whiel_program_inst_update
    ("; " whiel_program_inst_update)* "]" :
  term

------------------------------------------------------------
-- Program Instance Elaboration
------------------------------------------------------------

namespace Whiel

namespace Concrete

namespace ProgramInstanceNotation

open Lean Elab Term Meta

/-
  One update read from the notation. `key` is the canonical
  `ProgramNames.encode` key of the relation and `arity` its
  schema arity; the rows are kept as surface terms until the
  whole instance is assembled.
-/
private structure Update where
  name : Syntax
  key : String
  arity : Nat
  rows : Array (Array Term)

/- One domain constant in the `programCmd!` spellings. -/
private def dataTerm (t : Term) : TermElabM Term := do
  match t with
  | `($s:str) => `(Whiel.Concrete.Data.str $s)
  | `($n:num) => `(Whiel.Concrete.Data.num $n)
  | _ =>
      match t.raw with
      | .ident _ _ id _ =>
          if id == ``Bool.true ||
              id == Name.mkSimple "true" then
            `(Whiel.Concrete.Data.bool Bool.true)
          else if id == ``Bool.false ||
              id == Name.mkSimple "false" then
            `(Whiel.Concrete.Data.bool Bool.false)
          else
            pure t
      | _ =>
          pure t

/-
  The canonical key and the schema arity of one relation
  identifier, both read off the elaborated name rather than
  respelled here: the key is `ProgramNames.encode` of the
  name the shared `program` reader produces, so the notation
  cannot drift from the codec the keyed rows use.
-/
private unsafe def keyAndArity
    (schema : Expr)
    (name : Syntax) :
    TermElabM (String × Option Nat) := do
  let nameTerm ←
    liftMacroM (Notation.programNameTerm name)
  let nameExpr ←
    Term.elabTermEnsuringType nameTerm
      (some (mkConst ``Whiel.Concrete.ProgramNames))
  Term.synthesizeSyntheticMVarsNoPostponing
  let nameExpr ← instantiateMVars nameExpr
  let keyExpr ←
    mkAppM ``Whiel.Concrete.ProgramNames.encode #[nameExpr]
  let arityExpr ←
    mkAppM ``UnnamedSchema.arity? #[schema, nameExpr]
  let pair ← mkAppM ``Prod.mk #[keyExpr, arityExpr]
  let pairType ←
    Term.elabType (← `(String × Option Nat))
  Meta.evalExpr (String × Option Nat) pairType pair

/- Read one update against the schema it updates. -/
private unsafe def elabUpdate
    (schema : Expr)
    (update : TSyntax `whiel_program_inst_update) :
    TermElabM Update := do
  let checked (name : Syntax) :
      TermElabM (String × Nat) := do
    match ← keyAndArity schema name with
    | (key, some arity) =>
        pure (key, arity)
    | (_, none) =>
        throwErrorAt name
          s!"unknown relation '{name.getId}': the schema \
            has no such symbol"
  match update with
  | `(whiel_program_inst_update| $X:ident := []) => do
      let (key, arity) ← checked X.raw
      return ⟨X.raw, key, arity, #[]⟩
  | `(whiel_program_inst_update|
      $X:ident := [[$xs:term,*] $[,
        [$xss:term,*]]*]) => do
      let (key, arity) ← checked X.raw
      let rows :=
        #[xs.getElems] ++
          xss.map fun row => row.getElems
      for row in rows do
        if row.size != arity then
          throwErrorAt update
            s!"relation '{X.getId}' has arity {arity} in \
              the schema, but a row of the notation has \
              {row.size} cells"
      return ⟨X.raw, key, arity, rows⟩
  | _ =>
      throwUnsupportedSyntax

/- Reject a relation the notation names twice. -/
private def checkDistinct
    (updates : Array Update) :
    TermElabM Unit := do
  let mut seen : Array String := #[]
  for update in updates do
    if seen.contains update.key then
      throwErrorAt update.name
        s!"relation '{update.name.getId}' is named twice"
    seen := seen.push update.key
  return ()

/-
  Assemble the checked updates as
  `ProgramInstance.ofKeyedRows` over the schema expression
  the updates were checked against, reused rather than
  elaborated a second time, so the notation and the
  keyed-row instance are the same value and their equality
  is `rfl`.
-/
private unsafe def elabProgramInstance
    (schemaTerm : Term)
    (updates : Array (TSyntax `whiel_program_inst_update))
    (expectedType? : Option Expr) :
    TermElabM Expr := do
  let schemaType ←
    Term.elabType
      (← `(UnnamedSchema Whiel.Concrete.ProgramNames))
  let schema ←
    Term.elabTermEnsuringType schemaTerm (some schemaType)
  Term.synthesizeSyntheticMVarsNoPostponing
  let schema ← instantiateMVars schema
  let parsed ← updates.mapM (elabUpdate schema)
  checkDistinct parsed
  let entries ← parsed.mapM fun update => do
    let rows ← update.rows.mapM fun row => do
      let cells ← row.mapM dataTerm
      `([$cells,*])
    `(($(quote update.key), [$rows,*]))
  let rowsType ←
    Term.elabType
      (← `(Whiel.Concrete.ProgramInstance.KeyedRows))
  let rows ←
    Term.elabTermEnsuringType (← `([$entries,*]))
      (some rowsType)
  Term.synthesizeSyntheticMVarsNoPostponing
  let rows ← instantiateMVars rows
  let result :=
    mkAppN
      (mkConst
        ``Whiel.Concrete.ProgramInstance.ofKeyedRows)
      #[schema, rows]
  Term.ensureHasType expectedType? result

@[term_elab whielProgramInstanceNotation]
unsafe def elabWhielProgramInstance :
    TermElab := fun stx expectedType? => do
  match stx with
  | `(programInst![$Γ:term |
      $update:whiel_program_inst_update
      $[; $updates:whiel_program_inst_update]*]) =>
      elabProgramInstance Γ (#[update] ++ updates)
        expectedType?
  | _ =>
      throwUnsupportedSyntax

@[term_elab whielProgramInstanceEmptyNotation]
unsafe def elabWhielProgramInstanceEmpty :
    TermElab := fun stx expectedType? => do
  match stx with
  | `(programInst![$Γ:term]) =>
      elabProgramInstance Γ #[] expectedType?
  | _ =>
      throwUnsupportedSyntax

end ProgramInstanceNotation

end Concrete

end Whiel
