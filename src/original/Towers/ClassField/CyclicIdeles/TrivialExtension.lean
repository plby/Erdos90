import Towers.ClassField.CyclicIdeles.NormalSubgroupBridge
import Towers.ClassField.NormIndex.CanonicalTateFormula
import Towers.ClassField.HasseNorm.ClassH1
import Towers.ClassField.BrauerLocalization.IdeleIdealSupport

/-!
# Chapter VII, Section 5, Lemma 5.4: the trivial extension

The degree-one base case is already contained in the cyclic argument for
Theorem 5.1.  Indeed, its Galois group has one element and is therefore
cyclic; the analytic second inequality and the Section 4 comparison then
give all three claims at once.
-/

namespace Towers.CField.CIdeles

open Towers.CField.DDensit
open Towers.CField.ARecip
open Towers.CField.Ideles
open Towers.CField.ICohomo
open Towers.CField.NIndex
open Towers.CField.HNorm
open Towers.CField.RCGroups

noncomputable section

universe u v

/-- The previous analytic and cyclic results supply the order-one base case
used in the `p`-group induction. -/
theorem trivial_previous_results
    (h49 : (∀ (K : Type u) [Field K] [NumberField K]
          (L : NFExt K) (m : Modulus K),
          IsGalois K L.carrier →
            Finite (IdealsPrimeTo (NumberField.RingOfIntegers K) K m.finiteSupport ⧸
              extensionRaySubgroup L m) ∧
            (extensionRaySubgroup L m).index ≤
              Module.finrank K L.carrier))
    (htranslate : IdealInequalityBridge.{u})
    (h43 : (∀ (K L : Type u) [Field K] [Field L] [NumberField K] [NumberField L]
          [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
          [IsCyclic Gal(L/K)],
          letI : Fintype Gal(L/K) := Fintype.ofFinite Gal(L/K)
          letI : CommGroup Gal(L/K) := IsCyclic.commGroup
          HerbrandQuotientValue
            (classCokernelRepresentation (K := K) (L := L))
            (Module.finrank K L : ℚ)))
    (hindex : TateIndexBridge.{u})
    (hresize : ScalarResizingBridge.{u}) :
    TrivialExtensionBridge.{u} := by
  intro K L _ _ _ _ _ _ _ hdegree
  have hcard : Nat.card Gal(L/K) = 1 := by
    rw [IsGalois.card_aut_eq_finrank, hdegree]
  letI : Subsingleton Gal(L/K) :=
    (Nat.card_eq_one_iff_unique.mp hcard).1
  letI : IsCyclic Gal(L/K) := inferInstance
  exact claims_second_inequality
    h43 hindex hresize K L
      (idele_index_finrank h49 htranslate K L)

private theorem norm_surjective_subsingleton
    {k : Type v} {G : Type u} [CommRing k] [Group G] [Fintype G] [Subsingleton G]
    (A : Rep.{u, v, u} k G) :
    Function.Surjective (normCoinvariantsInvariants A) := by
  intro y
  refine ⟨Representation.Coinvariants.mk A.ρ y.1, ?_⟩
  apply Subtype.ext
  change A.ρ.norm y.1 = y.1
  letI : Unique G :=
    { default := 1
      uniq := fun _ ↦ Subsingleton.elim _ _ }
  rw [Representation.norm, LinearMap.sum_apply, Fintype.sum_unique]
  exact y.2 default

private theorem tate_zero_subsingleton
    {k : Type v} {G : Type u} [CommRing k] [Group G] [Fintype G] [Subsingleton G]
    (A : Rep.{u, v, u} k G) : Subsingleton (tateZero A) := by
  apply Submodule.Quotient.subsingleton_iff.mpr
  exact LinearMap.range_eq_top.mpr
    (norm_surjective_subsingleton A)

set_option maxHeartbeats 3000000 in
-- The cyclic idèle-class package unfolds several nested quotient representations.
/-- The degree-one base case, with all of its earlier inputs discharged.
The idèle index is one because the Tate-zero norm for a singleton Galois
group is onto. -/
theorem trivialExtensionBridge : TrivialExtensionBridge.{u} := by
  intro K L _ _ _ _ _ _ _ hdegree
  have hcard : Nat.card Gal(L/K) = 1 := by
    rw [IsGalois.card_aut_eq_finrank, hdegree]
  letI : Subsingleton Gal(L/K) :=
    (Nat.card_eq_one_iff_unique.mp hcard).1
  letI : IsCyclic Gal(L/K) := inferInstance
  letI : Fintype Gal(L/K) := Fintype.ofFinite Gal(L/K)
  let A : Rep ℤ Gal(L/K) :=
    classCokernelRepresentation (K := K) (L := L)
  letI : Subsingleton (tateZero A) :=
    tate_zero_subsingleton A
  letI : Unique (tateZero A) :=
    { default := 0
      uniq := fun _ ↦ Subsingleton.elim _ _ }
  have hindexEq :
      (principalIdeles (NumberField.RingOfIntegers K) K ⊔
        ideleNormSubgroup (K := K) (L := L)).index = 1 := by
    rw [← tateIndexBridge K L]
    exact Nat.card_unique
  apply claims_second_inequality
    Towers.CField.BLoc.ideleHerbrandQuotient
    tateIndexBridge scalarResizingBridge K L
  rw [hdegree, hindexEq]

end

end Towers.CField.CIdeles
