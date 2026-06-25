import Towers.ClassField.ReciprocityExistence.PlaceCompletion

/-!
# Chapter VII, Section 8, Lemma 8.5

This file states the two implications of Lemma VII.8.5 for the actual
finite-layer Artin map, relative Brauer group, localization map, and sum of
local invariants used in Theorem VII.8.1.  The cup-product datum is precisely
the commutative diagram constructed in the printed proof.
-/

namespace Towers.CField.RExist

open scoped IsMulCommutative
open NumberField
open Towers.CField.LFTheory
open Towers.CField.Ideles
open Towers.CField.Recip

noncomputable section

universe u

variable (K : Type u) [Field K] [NumberField K]

noncomputable local instance (E : FASubext K) : NumberField E.1 :=
  NumberField.of_module_finite K E.1

/-- **Lemma VII.8.5, forward implication.**  For a finite abelian extension,
the invariant-sum formula implies that the product of the local Artin maps
is trivial on principal ideles. -/
theorem reciprocity_invariant_sum
    (E : FASubext K)
    (phi : IdeleGroup (NumberField.RingOfIntegers K) K →*
      AbsoluteAbelianGalois K)
    (data : BData K)
    (cup : CupProductData K E phi data)
    (hsum : InvariantSumReciprocity K data E.1) :
    TrivialPrincipalIdeles
      (NumberField.RingOfIntegers K) K Gal(E.1/K)
      ((localAbelianRestriction E).comp phi) := by
  exact product_reciprocity_sum
    (principalIdele (NumberField.RingOfIntegers K) K)
    ((localAbelianRestriction E).comp phi)
    (relativeLocalization K data E.1)
    cup.fieldCup cup.ideleCup
    (BData.sumInvariant K data)
    ⟨cup.naturality, cup.localInvariantComparison⟩
    (fun chi a => hsum (cup.fieldCup chi (Additive.ofMul a)).toMul)

/-- **Lemma VII.8.5, cyclic converse.**  For a cyclic extension, triviality
of the Artin product on principal ideles implies the invariant-sum formula.
The needed surjectivity is the cyclic periodicity assertion carried by the
canonical cup-product datum, exactly as in the printed proof. -/
theorem invariant_sum_reciprocity
    (E : FASubext K)
    (phi : IdeleGroup (NumberField.RingOfIntegers K) K →*
      AbsoluteAbelianGalois K)
    (data : BData K)
    (cup : CupProductData K E phi data)
    (hcyclic : IsCyclic Gal(E.1/K))
    (hprincipal : TrivialPrincipalIdeles
      (NumberField.RingOfIntegers K) K Gal(E.1/K)
      ((localAbelianRestriction E).comp phi)) :
    InvariantSumReciprocity K data E.1 := by
  obtain ⟨chi, hchi⟩ := cup.cyclic_surjective hcyclic
  exact sum_reciprocity_product
    (principalIdele (NumberField.RingOfIntegers K) K)
    ((localAbelianRestriction E).comp phi)
    (relativeLocalization K data E.1)
    cup.fieldCup cup.ideleCup
    (BData.sumInvariant K data)
    ⟨cup.naturality, cup.localInvariantComparison⟩
    chi hchi (fun a => hprincipal a)

end

end Towers.CField.RExist
