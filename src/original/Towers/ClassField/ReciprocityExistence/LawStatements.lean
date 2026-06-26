import Towers.ClassField.LocalReciprocity.DualityConclusion
import Towers.ClassField.LocalBrauer.DivisionAlgebraInvariant
import Towers.ClassField.Reciprocity.ArtinMapStatements
import Mathlib.Algebra.DirectSum.Module

/-!
# Statements for Chapter VII, Section 8

The two parts of Theorem 8.1 use different objects: the global Artin map on
ideles, and relative `H²` (equivalently the relative Brauer group).  The
predicates below keep them separate.  The two equations in
`CupInvariantDiagram` are exactly the left and right squares in the
proof of Lemma 8.5.
-/

namespace Towers.CField.RExist

open Towers.CField.LFTheory
open Towers.CField.LRecip
open Towers.CField.LBrauer
open Towers.CField.Ideles
open Towers.CField.Recip

noncomputable section

universe u v w

/-- **Theorem VII.8.1(a).** The product of the local Artin maps is trivial on
every principal idele.  The existing global Artin predicate supplies the
local factors and their continuity. -/
def GlobalReciprocityLaw
    (K : Type u) [Field K] [NumberField K] : Prop :=
  ∀ phi : IdeleGroup (NumberField.RingOfIntegers K) K →*
      AbsoluteAbelianGalois K,
    ContinuousGlobalArtin phi →
      TrivialPrincipalIdeles (NumberField.RingOfIntegers K) K
        (AbsoluteAbelianGalois K) phi

/-- **Theorem VII.8.1(b).** The sum of the local invariants of every localized
relative `H²` class is zero.  The direct-sum-valued map includes the assertion
that only finitely many localizations are nonzero. -/
def GlobalInvariantReciprocity
    {index H2 : Type u} [AddCommGroup H2]
    (LocalH2 : index → Type v) [∀ place, AddCommGroup (LocalH2 place)]
    (localize : H2 →+ DirectSum index LocalH2)
    (sumInvariant : DirectSum index LocalH2 →+ LocalInvariant) : Prop :=
  ∀ beta, sumInvariant (localize beta) = 0

/-- **Theorem VII.8.1, both clauses.** -/
def GlobalSumReciprocity
    (K : Type u) [Field K] [NumberField K]
    {index H2 : Type u} [AddCommGroup H2]
    (LocalH2 : index → Type v) [∀ place, AddCommGroup (LocalH2 place)]
    (localize : H2 →+ DirectSum index LocalH2)
    (sumInvariant : DirectSum index LocalH2 →+ LocalInvariant) : Prop :=
  GlobalReciprocityLaw K ∧
    GlobalInvariantReciprocity LocalH2 localize sumInvariant

/-- The left square in the proof of Lemma VII.8.5: cup product by
`delta chi` commutes with the principal embedding from the field to the
ideles. -/
def CupProductNaturality
    {P I G : Type u} {FieldH2 : Type v} {IdeleH2 : Type w}
    [CommGroup P] [CommGroup I] [CommGroup G]
    [AddCommGroup FieldH2] [AddCommGroup IdeleH2]
    (principal : P →* I) (fieldToIdele : FieldH2 →+ IdeleH2)
    (fieldCupBoundary : CharacterModule (Additive G) → Additive P →+ FieldH2)
    (ideleCupBoundary : CharacterModule (Additive G) → Additive I →+ IdeleH2) : Prop :=
  ∀ chi a, fieldToIdele (fieldCupBoundary chi (Additive.ofMul a)) =
    ideleCupBoundary chi (Additive.ofMul (principal a))

/-- The right square in the proof of Lemma VII.8.5, obtained place by place
from Proposition III.3.6: character evaluation of the global Artin symbol is
the sum of the local invariants of cup product by `delta chi`. -/
def CupInvariantComparison
    {I G : Type u} {IdeleH2 : Type w} [CommGroup I] [CommGroup G]
    [AddCommGroup IdeleH2]
    (artin : I →* G)
    (ideleCupBoundary : CharacterModule (Additive G) → Additive I →+ IdeleH2)
    (sumInvariant : IdeleH2 →+ LocalInvariant) : Prop :=
  ∀ chi a, sumInvariant (ideleCupBoundary chi (Additive.ofMul a)) =
    chi (Additive.ofMul (artin a))

/-- The complete cup-product/local-invariant diagram in Lemma VII.8.5. -/
def CupInvariantDiagram
    {P I G : Type u} {FieldH2 : Type v} {IdeleH2 : Type w}
    [CommGroup P] [CommGroup I] [CommGroup G]
    [AddCommGroup FieldH2] [AddCommGroup IdeleH2]
    (principal : P →* I) (artin : I →* G)
    (fieldToIdele : FieldH2 →+ IdeleH2)
    (fieldCupBoundary : CharacterModule (Additive G) → Additive P →+ FieldH2)
    (ideleCupBoundary : CharacterModule (Additive G) → Additive I →+ IdeleH2)
    (sumInvariant : IdeleH2 →+ LocalInvariant) : Prop :=
  CupProductNaturality principal fieldToIdele fieldCupBoundary ideleCupBoundary ∧
    CupInvariantComparison artin ideleCupBoundary sumInvariant

/-- **Lemma VII.8.5, forward implication.** The sum formula and the cup-product
diagram imply triviality of the Artin map on principal elements. -/
theorem product_reciprocity_sum
    {P I G : Type u} {FieldH2 : Type v} {IdeleH2 : Type w}
    [CommGroup P] [CommGroup I] [CommGroup G]
    [AddCommGroup FieldH2] [AddCommGroup IdeleH2]
    (principal : P →* I) (artin : I →* G)
    (fieldToIdele : FieldH2 →+ IdeleH2)
    (fieldCupBoundary : CharacterModule (Additive G) → Additive P →+ FieldH2)
    (ideleCupBoundary : CharacterModule (Additive G) → Additive I →+ IdeleH2)
    (sumInvariant : IdeleH2 →+ LocalInvariant)
    (hdiagram : CupInvariantDiagram principal artin fieldToIdele
      fieldCupBoundary ideleCupBoundary sumInvariant)
    (hsum : ∀ chi a,
      sumInvariant (fieldToIdele
        (fieldCupBoundary chi (Additive.ofMul a))) = 0) :
    ∀ a, artin (principal a) = 1 := by
  intro a
  apply forall_rational_character
  intro chi
  rw [← hdiagram.2 chi (principal a), ← hdiagram.1 chi a, hsum]
  exact (map_zero chi).symm

/-- **Lemma VII.8.5, cyclic converse in its algebraic form.** If an injective
character makes cup product by `delta chi` surjective (in the book it is an
isomorphism), principal reciprocity forces the invariant sum to vanish on all
field `H²` classes. -/
theorem sum_reciprocity_product
    {P I G : Type u} {FieldH2 : Type v} {IdeleH2 : Type w}
    [CommGroup P] [CommGroup I] [CommGroup G]
    [AddCommGroup FieldH2] [AddCommGroup IdeleH2]
    (principal : P →* I) (artin : I →* G)
    (fieldToIdele : FieldH2 →+ IdeleH2)
    (fieldCupBoundary : CharacterModule (Additive G) → Additive P →+ FieldH2)
    (ideleCupBoundary : CharacterModule (Additive G) → Additive I →+ IdeleH2)
    (sumInvariant : IdeleH2 →+ LocalInvariant)
    (hdiagram : CupInvariantDiagram principal artin fieldToIdele
      fieldCupBoundary ideleCupBoundary sumInvariant)
    (chi : CharacterModule (Additive G))
    (hcup : Function.Surjective (fieldCupBoundary chi))
    (hprincipal : ∀ a, artin (principal a) = 1) :
    ∀ beta, sumInvariant (fieldToIdele beta) = 0 := by
  intro beta
  obtain ⟨a, rfl⟩ := hcup beta
  change sumInvariant (fieldToIdele
    (fieldCupBoundary chi (Additive.ofMul a.toMul))) = 0
  rw [hdiagram.1 chi a.toMul,
    hdiagram.2 chi (principal a.toMul), hprincipal]
  exact map_zero chi

/-- **Lemma VII.8.6.** If every absolute Brauer class is split by a cyclic
cyclotomic extension, and the invariant sum formula holds for every class
split by such an extension, then it holds for every class. -/
theorem invariant_cyclic_cyclotomic
    {AbsoluteClass : Type v} {Extension : Type u}
    (IsCyclicCyclotomic : Extension → Prop)
    (ISBy : AbsoluteClass → Extension → Prop)
    (HasInvariantSumZero : AbsoluteClass → Prop)
    (hsplit : ∀ beta, ∃ E, IsCyclicCyclotomic E ∧ ISBy beta E)
    (hcyclic : ∀ E, IsCyclicCyclotomic E →
      ∀ beta, ISBy beta E → HasInvariantSumZero beta) :
    ∀ beta, HasInvariantSumZero beta := by
  intro beta
  obtain ⟨E, hE, hbeta⟩ := hsplit beta
  exact hcyclic E hE beta hbeta

end

end Towers.CField.RExist
