import Towers.NumberTheory.Locals.CompleteDVRHenselian
import Towers.NumberTheory.Locals.TeichmullerLifts
import Towers.NumberTheory.Locals.UnramifiedExtensions
import Towers.ClassField.LocalBrauer.IntegralModelFrobenius

/-!
# Frobenius splitting from an abstract unramified integral model

The Teichmuller argument used for the explicit adjoining-root construction
only depends on the extension integer ring being Henselian and on the size of
its residue field.  This file records that argument independently of the
chosen presentation.
-/

namespace Towers.CField.LBrauer

noncomputable section

open Polynomial IsLocalRing

universe u

/-- A finite free formally unramified local algebra over a complete local
ring is Henselian. -/
theorem henselian_free_formally
    (A U : Type u) [CommRing A] [IsLocalRing A]
    [CommRing U] [IsLocalRing U] [Algebra A U]
    [IsLocalHom (algebraMap A U)] [Module.Finite A U] [Module.Free A U]
    [Algebra.FormallyUnramified A U]
    [IsAdicComplete (maximalIdeal A) A] :
    HenselianLocalRing U :=
  henselian_formally_unramified A U

/-- If a Henselian local ring has `q ^ n` residue classes, its Teichmuller
representatives split `X ^ (q ^ n) - X`. -/
theorem frobenius_splits_card
    (U : Type u) [CommRing U] [IsDomain U] [HenselianLocalRing U]
    [Fintype (ResidueField U)] (q n : ℕ) [NeZero n]
    (hcard : Fintype.card (ResidueField U) = q ^ n)
    (hq : 1 < q) :
    (X ^ q ^ n - X : U[X]).Splits := by
  classical
  choose lift hliftRoot hliftResidue using fun a0 : ResidueField U =>
    Towers.NumberTheory.Milne.exists_teichmullerLift U a0
  have hliftInjective : Function.Injective lift := by
    intro a0 b0 hab
    have := congrArg (residue U) hab
    simpa only [hliftResidue] using this
  let P : U[X] := X ^ q ^ n - X
  have hliftRootP (a0 : ResidueField U) : P.IsRoot (lift a0) := by
    rw [hcard] at hliftRoot
    simpa [P] using hliftRoot a0
  let roots : Finset U := Finset.univ.image lift
  have hrootsCard : roots.card = q ^ n := by
    rw [Finset.card_image_of_injective _ hliftInjective,
      Finset.card_univ, hcard]
  have hPmonic : P.Monic := by
    dsimp [P]
    apply monic_X_pow_sub
    rw [degree_X]
    exact_mod_cast (Nat.one_lt_pow (NeZero.ne n) hq)
  have hPnatDegree : P.natDegree = q ^ n := by
    dsimp [P]
    rw [natDegree_sub_eq_left_of_natDegree_lt]
    · exact natDegree_X_pow (q ^ n)
    · simpa using Nat.one_lt_pow (NeZero.ne n) hq
  have hrootsSub : roots ⊆ P.roots.toFinset := by
    intro x hx
    rw [Finset.mem_image] at hx
    obtain ⟨a0, -, rfl⟩ := hx
    rw [Multiset.mem_toFinset, mem_roots]
    · exact hliftRootP a0
    · exact hPmonic.ne_zero
  have hrootsLower : q ^ n ≤ P.roots.card := by
    calc
      q ^ n = roots.card := hrootsCard.symm
      _ ≤ P.roots.toFinset.card := Finset.card_le_card hrootsSub
      _ ≤ P.roots.card := Multiset.toFinset_card_le _
  change P.Splits
  rw [splits_iff_card_roots]
  exact Nat.le_antisymm (card_roots' P) <| by
    simpa [hPnatDegree] using hrootsLower

/-- A finite unramified extension of complete DVRs splits the Frobenius
polynomial determined by its fraction-field degree.  This formulation is
independent of a monogenic or adjoining-root presentation. -/
theorem splits_fraction_dvr
    (A U K E : Type u)
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CommRing U] [IsDomain U] [IsLocalRing U]
    [Algebra A U] [Module.Finite A U] [Module.Free A U]
    [IsLocalHom (algebraMap A U)] [Algebra.FormallyUnramified A U]
    [IsAdicComplete (maximalIdeal A) A]
    [Finite (ResidueField A)]
    [Field K] [Algebra A K] [IsFractionRing A K]
    [Field E] [Algebra U E] [IsFractionRing U E]
    [Algebra K E] [Algebra A E]
    [IsScalarTower A U E] [IsScalarTower A K E]
    (n : ℕ) [NeZero n] (hdegree : Module.finrank K E = n) :
    (((X ^ (Nat.card (ResidueField A)) ^ n - X : A[X]).map
      (algebraMap A K)).map (algebraMap K E)).Splits := by
  have hAE : Function.Injective (algebraMap A E) := by
    rw [IsScalarTower.algebraMap_eq A K E]
    exact (algebraMap K E).injective.comp (IsFractionRing.injective A K)
  have hAU : Function.Injective (algebraMap A U) := by
    intro x y hxy
    apply hAE
    rw [IsScalarTower.algebraMap_eq A U E]
    exact congrArg (algebraMap U E) hxy
  letI : FaithfulSMul A U :=
    (faithfulSMul_iff_algebraMap_injective A U).2 hAU
  letI : Algebra.IsIntegral A U := Algebra.IsIntegral.of_finite A U
  letI : IsDedekindDomain U := isDedekindDomain.of_formallyUnramified A U
  have hUNotField : ¬ IsField U := by
    intro hU
    exact IsDiscreteValuationRing.not_isField A
      (isField_of_isIntegral_of_isField hAU hU)
  letI : IsDiscreteValuationRing U :=
    ((IsDiscreteValuationRing.TFAE U hUNotField).out 2 0).mp
      (inferInstance : IsDedekindDomain U)
  letI : HenselianLocalRing U :=
    henselian_free_formally A U
  letI : Algebra.IsUnramifiedAt A (maximalIdeal U) :=
    unramified_maximal_formally A U
  letI : (maximalIdeal U).LiesOver (maximalIdeal A) :=
    (Ideal.liesOver_iff _ _).mpr
      (maximalIdeal_comap (algebraMap A U)).symm
  have hresdegree : Module.finrank (ResidueField A) (ResidueField U) = n := by
    rw [← hdegree]
    exact (
      Towers.NumberTheory.Milne.finrank_unramified_local
        (R := A) (S := U) (K := K) (L := E) (maximalIdeal A)
        (IsDiscreteValuationRing.not_a_field A)
        (IsDiscreteValuationRing.not_a_field U)).symm
  letI : Module.Finite (ResidueField A) (ResidueField U) :=
    Module.finite_of_finrank_pos (by
      rw [hresdegree]
      exact NeZero.pos n)
  letI : Finite (ResidueField U) := Module.finite_of_finite (ResidueField A)
  letI : Fintype (ResidueField A) := Fintype.ofFinite _
  letI : Fintype (ResidueField U) := Fintype.ofFinite _
  let q := Nat.card (ResidueField A)
  have hcard : Fintype.card (ResidueField U) = q ^ n := by
    calc
      Fintype.card (ResidueField U) =
          Fintype.card (ResidueField A) ^
            Module.finrank (ResidueField A) (ResidueField U) :=
        Module.card_eq_pow_finrank
      _ = Fintype.card (ResidueField A) ^ n := by rw [hresdegree]
      _ = q ^ n := by rw [Fintype.card_eq_nat_card]
  have hq : 1 < q := by
    simpa [q, Nat.card_eq_fintype_card] using
      Fintype.one_lt_card (α := ResidueField A)
  have hsplitU : (X ^ q ^ n - X : U[X]).Splits :=
    frobenius_splits_card U q n hcard hq
  have hmaps : (algebraMap K E).comp (algebraMap A K) =
      (algebraMap U E).comp (algebraMap A U) :=
    (IsScalarTower.algebraMap_eq A K E).symm.trans
      (IsScalarTower.algebraMap_eq A U E)
  rw [map_map, hmaps]
  simpa [q, map_map] using hsplitU.map (algebraMap U E)

/-- Generator form of the abstract DVR splitting theorem.  Integrality of
the generator supplies finiteness of `A[e]`; torsion-freeness over the DVR
then supplies the finite free module needed for completeness. -/
theorem frobenius_splits_generator
    (A K E : Type u)
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [IsAdicComplete (maximalIdeal A) A]
    [Finite (ResidueField A)]
    [Field K] [Algebra A K] [IsFractionRing A K]
    [Field E] [Algebra K E] [Module.Finite K E]
    [Algebra A E] [IsScalarTower A K E]
    (e : E) (hgen : Algebra.adjoin K ({e} : Set E) = ⊤)
    (he : IsIntegral A e)
    (hlocal : IsLocalRing (Algebra.adjoin A ({e} : Set E)))
    (hunramified : Algebra.FormallyUnramified A
      (Algebra.adjoin A ({e} : Set E)))
    (n : ℕ) [NeZero n] (hdegree : Module.finrank K E = n) :
    ((X ^ (Nat.card (ResidueField A)) ^ n - X : K[X]).map
      (algebraMap K E)).Splits := by
  let U := Algebra.adjoin A ({e} : Set E)
  letI : IsLocalRing U := hlocal
  letI : Module.Finite A U :=
    Algebra.finite_adjoin_simple_of_isIntegral he
  have hAE : Function.Injective (algebraMap A E) := by
    rw [IsScalarTower.algebraMap_eq A K E]
    exact (algebraMap K E).injective.comp (IsFractionRing.injective A K)
  have hAU : Function.Injective (algebraMap A U) := by
    intro x y hxy
    apply hAE
    have h := congrArg U.val hxy
    simpa [U] using h
  letI : Module.IsTorsionFree A U :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr hAU
  letI : Module.Free A U := Module.free_of_finite_type_torsion_free'
  letI : Algebra.IsIntegral A U := Algebra.IsIntegral.of_finite A U
  letI : IsLocalHom (algebraMap A U) :=
    Algebra.IsIntegral.isLocalHom A U
  letI : Algebra.FormallyUnramified A U := hunramified
  letI : IsFractionRing U E :=
    fraction_adjoin_top A K E e hgen
  letI : IsScalarTower A U E := IsScalarTower.of_algebraMap_eq' rfl
  have hsplit :=
    splits_fraction_dvr
      A U K E n hdegree
  simpa using hsplit

end

end Towers.CField.LBrauer
