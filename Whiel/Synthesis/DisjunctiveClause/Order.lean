-- Author: Jesse Comer
import Whiel.Synthesis.DisjunctiveClause.FullSpec
import Mathlib.Data.List.Lex
import Mathlib.Data.Sum.Order

/-
  Computable structural order for disjunctive literals.

  Constructor-tagged prefix lists serialize the syntax.
  Binary encodings include the first child's length. The
  serializers are proved injective before lexicographic
  order is lifted to literals. Atom proof fields are omitted
  only through proof irrelevance in the injectivity proof.

  Main declarations:
    * `StructuralOrder.literalCode`
    * `StructuralOrder.literalCode_injective`
    * `StructuralOrder.literalLinearOrder`
-/

------------------------------------------------------------
-- Structural Encoding Support
------------------------------------------------------------

namespace Whiel

namespace Synthesis

namespace DisjunctiveClause

namespace StructuralOrder

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Γ : UnnamedSchema A}

/- Ordered token alphabet for syntax serialization. -/
abbrev Token (A D : Type) :=
  Lex (Sum Nat (Lex (Sum A D)))

private def natToken
    (value : Nat) : Token A D :=
  toLex (Sum.inl value)

private def relationToken
    (relation : A) : Token A D :=
  toLex (Sum.inr (toLex (Sum.inl relation)))

private def domainToken
    (constant : D) : Token A D :=
  toLex (Sum.inr (toLex (Sum.inr constant)))

omit [RelationNames A] [Domain D] in
private theorem natToken_injective :
    Function.Injective
      (natToken (A := A) (D := D)) := by
  intro left right hEqual
  simpa [natToken] using hEqual

omit [RelationNames A] [Domain D] in
private theorem relationToken_injective :
    Function.Injective
      (relationToken (A := A) (D := D)) := by
  intro left right hEqual
  simpa [relationToken] using hEqual

omit [RelationNames A] [Domain D] in
private theorem domainToken_injective :
    Function.Injective
      (domainToken (A := A) (D := D)) := by
  intro left right hEqual
  simpa [domainToken] using hEqual

/- Length-delimited encoding of two recursive children. -/
private def pairCode
    (tag : Nat)
    (left right : List (Token A D)) :
    List (Token A D) :=
  natToken tag :: natToken left.length ::
    left ++ right

omit [RelationNames A] [Domain D] in
private theorem pairCode_injective
    {tag : Nat}
    {left right left' right' : List (Token A D)}
    (hEqual :
      pairCode (A := A) (D := D) tag left right =
        pairCode tag left' right') :
    left = left' ∧ right = right' := by
  have hTail := (List.cons.inj hEqual).2
  have hParts := List.cons.inj hTail
  have hLength : left.length = left'.length :=
    natToken_injective hParts.1
  exact List.append_inj hParts.2 hLength

end StructuralOrder

end DisjunctiveClause

end Synthesis

end Whiel

------------------------------------------------------------
-- Selection Conditions
------------------------------------------------------------

namespace Whiel

namespace Synthesis

namespace DisjunctiveClause

namespace StructuralOrder

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Γ : UnnamedSchema A}

private def selCode : Sel D → List (Token A D)
| .eqIdx left right =>
    [natToken 0, natToken left, natToken right]
| .eqConst index constant =>
    [natToken 1, natToken index, domainToken constant]
| .and left right =>
    pairCode 2 (selCode left) (selCode right)
| .or left right =>
    pairCode 3 (selCode left) (selCode right)
| .not child =>
    natToken 4 :: selCode child

omit [RelationNames A] in
private theorem selCode_injective :
    Function.Injective
      (selCode (A := A) (D := D)) := by
  intro left
  induction left with
  | eqIdx leftIndex rightIndex =>
      intro right hEqual
      cases right <;>
        simp_all [selCode, pairCode, natToken,
          domainToken]
  | eqConst index constant =>
      intro right hEqual
      cases right <;>
        simp_all [selCode, pairCode, natToken,
          domainToken]
  | and left right leftIH rightIH =>
      intro other hEqual
      cases other with
      | and otherLeft otherRight =>
          have hParts := pairCode_injective hEqual
          rw [leftIH hParts.1, rightIH hParts.2]
      | eqIdx leftIndex rightIndex =>
          simp [selCode, pairCode, natToken] at hEqual
      | eqConst index constant =>
          simp [selCode, pairCode, natToken] at hEqual
      | or otherLeft otherRight =>
          simp [selCode, pairCode, natToken] at hEqual
      | not child =>
          simp [selCode, pairCode, natToken] at hEqual
  | or left right leftIH rightIH =>
      intro other hEqual
      cases other with
      | or otherLeft otherRight =>
          have hParts := pairCode_injective hEqual
          rw [leftIH hParts.1, rightIH hParts.2]
      | eqIdx leftIndex rightIndex =>
          simp [selCode, pairCode, natToken] at hEqual
      | eqConst index constant =>
          simp [selCode, pairCode, natToken] at hEqual
      | and otherLeft otherRight =>
          simp [selCode, pairCode, natToken] at hEqual
      | not child =>
          simp [selCode, pairCode, natToken] at hEqual
  | not child childIH =>
      intro other hEqual
      cases other with
      | not otherChild =>
          rw [childIH ((List.cons.inj hEqual).2)]
      | eqIdx leftIndex rightIndex =>
          simp [selCode, natToken] at hEqual
      | eqConst index constant =>
          simp [selCode, natToken] at hEqual
      | and left right =>
          simp [selCode, pairCode, natToken] at hEqual
      | or left right =>
          simp [selCode, pairCode, natToken] at hEqual

end StructuralOrder

end DisjunctiveClause

end Synthesis

end Whiel

------------------------------------------------------------
-- Raw Relational-Algebra Expressions
------------------------------------------------------------

namespace Whiel

namespace Synthesis

namespace DisjunctiveClause

namespace StructuralOrder

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Γ : UnnamedSchema A}

private def rawCode :
    RawRAExpr A D → List (Token A D)
| .top => [natToken 10]
| .empty arity => [natToken 11, natToken arity]
| .rel relation => [natToken 12, relationToken relation]
| .single constant => [natToken 13, domainToken constant]
| .select condition child =>
    pairCode 14 (selCode condition) (rawCode child)
| .proj indices child =>
    pairCode 15 (indices.map natToken) (rawCode child)
| .prod left right =>
    pairCode 16 (rawCode left) (rawCode right)
| .union left right =>
    pairCode 17 (rawCode left) (rawCode right)
| .diff left right =>
    pairCode 18 (rawCode left) (rawCode right)

private theorem rawCode_injective :
    Function.Injective
      (rawCode (A := A) (D := D)) := by
  intro left
  induction left with
  | top =>
      intro right hEqual
      cases right <;>
        simp_all [rawCode, pairCode, natToken]
  | empty arity =>
      intro right hEqual
      cases right <;>
        simp_all [rawCode, pairCode, natToken,
          relationToken, domainToken]
  | rel relation =>
      intro right hEqual
      cases right <;>
        simp_all [rawCode, pairCode, natToken,
          relationToken, domainToken]
  | single constant =>
      intro right hEqual
      cases right <;>
        simp_all [rawCode, pairCode, natToken,
          relationToken, domainToken]
  | select condition child childIH =>
      intro other hEqual
      cases other with
      | select otherCondition otherChild =>
          have hParts := pairCode_injective hEqual
          rw [selCode_injective hParts.1,
            childIH hParts.2]
      | top =>
          simp [rawCode, pairCode, natToken] at hEqual
      | empty arity =>
          simp [rawCode, pairCode, natToken] at hEqual
      | rel relation =>
          simp [rawCode, pairCode, natToken] at hEqual
      | single constant =>
          simp [rawCode, pairCode, natToken] at hEqual
      | proj indices otherChild =>
          simp [rawCode, pairCode, natToken] at hEqual
      | prod left right =>
          simp [rawCode, pairCode, natToken] at hEqual
      | union left right =>
          simp [rawCode, pairCode, natToken] at hEqual
      | diff left right =>
          simp [rawCode, pairCode, natToken] at hEqual
  | proj indices child childIH =>
      intro other hEqual
      cases other with
      | proj otherIndices otherChild =>
          have hParts := pairCode_injective hEqual
          have hIndices : indices = otherIndices :=
            (List.map_injective_iff.mpr
              natToken_injective) hParts.1
          rw [hIndices, childIH hParts.2]
      | top =>
          simp [rawCode, pairCode, natToken] at hEqual
      | empty arity =>
          simp [rawCode, pairCode, natToken] at hEqual
      | rel relation =>
          simp [rawCode, pairCode, natToken] at hEqual
      | single constant =>
          simp [rawCode, pairCode, natToken] at hEqual
      | select condition otherChild =>
          simp [rawCode, pairCode, natToken] at hEqual
      | prod left right =>
          simp [rawCode, pairCode, natToken] at hEqual
      | union left right =>
          simp [rawCode, pairCode, natToken] at hEqual
      | diff left right =>
          simp [rawCode, pairCode, natToken] at hEqual
  | prod left right leftIH rightIH =>
      intro other hEqual
      cases other with
      | prod otherLeft otherRight =>
          have hParts := pairCode_injective hEqual
          rw [leftIH hParts.1, rightIH hParts.2]
      | top =>
          simp [rawCode, pairCode, natToken] at hEqual
      | empty arity =>
          simp [rawCode, pairCode, natToken] at hEqual
      | rel relation =>
          simp [rawCode, pairCode, natToken] at hEqual
      | single constant =>
          simp [rawCode, pairCode, natToken] at hEqual
      | select condition child =>
          simp [rawCode, pairCode, natToken] at hEqual
      | proj indices child =>
          simp [rawCode, pairCode, natToken] at hEqual
      | union otherLeft otherRight =>
          simp [rawCode, pairCode, natToken] at hEqual
      | diff otherLeft otherRight =>
          simp [rawCode, pairCode, natToken] at hEqual
  | union left right leftIH rightIH =>
      intro other hEqual
      cases other with
      | union otherLeft otherRight =>
          have hParts := pairCode_injective hEqual
          rw [leftIH hParts.1, rightIH hParts.2]
      | top =>
          simp [rawCode, pairCode, natToken] at hEqual
      | empty arity =>
          simp [rawCode, pairCode, natToken] at hEqual
      | rel relation =>
          simp [rawCode, pairCode, natToken] at hEqual
      | single constant =>
          simp [rawCode, pairCode, natToken] at hEqual
      | select condition child =>
          simp [rawCode, pairCode, natToken] at hEqual
      | proj indices child =>
          simp [rawCode, pairCode, natToken] at hEqual
      | prod otherLeft otherRight =>
          simp [rawCode, pairCode, natToken] at hEqual
      | diff otherLeft otherRight =>
          simp [rawCode, pairCode, natToken] at hEqual
  | diff left right leftIH rightIH =>
      intro other hEqual
      cases other with
      | diff otherLeft otherRight =>
          have hParts := pairCode_injective hEqual
          rw [leftIH hParts.1, rightIH hParts.2]
      | top =>
          simp [rawCode, pairCode, natToken] at hEqual
      | empty arity =>
          simp [rawCode, pairCode, natToken] at hEqual
      | rel relation =>
          simp [rawCode, pairCode, natToken] at hEqual
      | single constant =>
          simp [rawCode, pairCode, natToken] at hEqual
      | select condition child =>
          simp [rawCode, pairCode, natToken] at hEqual
      | proj indices child =>
          simp [rawCode, pairCode, natToken] at hEqual
      | prod otherLeft otherRight =>
          simp [rawCode, pairCode, natToken] at hEqual
      | union otherLeft otherRight =>
          simp [rawCode, pairCode, natToken] at hEqual

end StructuralOrder

end DisjunctiveClause

end Synthesis

end Whiel

------------------------------------------------------------
-- Checked Atoms and Literals
------------------------------------------------------------

namespace Whiel

namespace Synthesis

namespace DisjunctiveClause

namespace StructuralOrder

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Γ : UnnamedSchema A}

private def atomCode
    (atom : Atom D Γ) : List (Token A D) :=
  let kindTag :=
    match atom.kind with
    | .equality => 20
    | .containment => 21
  natToken kindTag :: natToken atom.arity ::
    natToken (rawCode atom.left).length ::
      rawCode atom.left ++ rawCode atom.right

private theorem atomCode_injective :
    Function.Injective
      (atomCode (A := A) (D := D) (Γ := Γ)) := by
  intro left right hEqual
  cases left with
  | mk leftKind leftArity leftExpr rightExpr
      leftWF rightWF =>
    cases right with
    | mk rightKind rightArity leftExpr'
        rightExpr' leftWF' rightWF' =>
      simp only [atomCode] at hEqual
      have hKindAndTail := List.cons.inj hEqual
      have hKind : leftKind = rightKind := by
        cases leftKind <;> cases rightKind <;>
          simp_all [natToken]
      subst rightKind
      have hArityAndTail :=
        List.cons.inj hKindAndTail.2
      have hArity : leftArity = rightArity :=
        natToken_injective hArityAndTail.1
      subst rightArity
      have hParts := List.cons.inj hArityAndTail.2
      have hLength :
          (rawCode leftExpr).length =
            (rawCode leftExpr').length :=
        natToken_injective hParts.1
      have hExprs :=
        List.append_inj hParts.2 hLength
      have hLeft : leftExpr = leftExpr' :=
        rawCode_injective hExprs.1
      have hRight : rightExpr = rightExpr' :=
        rawCode_injective hExprs.2
      subst leftExpr'
      subst rightExpr'
      rfl

/- Structural serialization of a checked literal. -/
def literalCode
    (literal : Literal D Γ) :
    List (Token A D) :=
  let signTag :=
    match literal.sign with
    | .positive => 30
    | .negative => 31
  natToken signTag :: atomCode literal.atom

/- Literal serialization is injective. -/
theorem literalCode_injective :
    Function.Injective
      (literalCode (A := A) (D := D) (Γ := Γ)) := by
  intro left right hEqual
  cases left with
  | mk leftSign leftAtom =>
    cases right with
    | mk rightSign rightAtom =>
      simp only [literalCode] at hEqual
      have hParts := List.cons.inj hEqual
      have hSign : leftSign = rightSign := by
        cases leftSign <;> cases rightSign <;>
          simp_all [natToken]
      subst rightSign
      have hAtom : leftAtom = rightAtom :=
        atomCode_injective hParts.2
      subst rightAtom
      rfl

/-
  Computable structural literal order. Relation names and
  constants use their supplied lawful orders.
-/
@[reducible] def literalLinearOrder
    [LinearOrder A] [LinearOrder D] :
    LinearOrder (Literal D Γ) := by
  letI : LinearOrder (Lex (Sum A D)) :=
    Sum.Lex.linearOrder
  letI : LinearOrder (Token A D) :=
    Sum.Lex.linearOrder
  letI : LinearOrder (List (Token A D)) :=
    inferInstance
  exact
    LinearOrder.lift'
      literalCode literalCode_injective

end StructuralOrder

end DisjunctiveClause

end Synthesis

end Whiel
