import Submission.ClassField.LocalBrauer.CanonicalUnramifiedFrobenius
import Submission.ClassField.LocalBrauer.CanonicalUnramifiedData
import Submission.ClassField.LocalBrauer.FiniteExtensionData
import Submission.ClassField.LocalBrauer.IntegralModelFrobenius
import Submission.ClassField.LocalBrauer.UnramifiedH2
import Submission.ClassField.LocalBrauer.UnitH2
import Submission.ClassField.NormCorrespondence.SubgroupOpenClosed
import Submission.ClassField.CohomologyOps.ExtensionsSecondCohomology
import Submission.NumberTheory.Locals.ClosureRootsUnity
import Submission.NumberTheory.Locals.TeichmullerLifts
import Submission.FieldTheory.CentralEmbeddingPresentation
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed


/-!
# Local realization for tame central embedding problems

This file builds the local arithmetic input used in the central cubic
Koch--Shafarevich argument.  The construction follows the standard proof of
the tame local presentation: pass to a canonical unramified extension, use
its residue-field roots of unity, and then adjoin an Eisenstein radical.
-/

noncomputable section

namespace Submission
namespace TBluepr

open Polynomial
open Submission.CField.LBrauer
open Submission.CField.CProduca

attribute [local instance] Units.mulDistribMulActionRight

universe u v w

variable (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K]
  [ValuativeRel K] [IsNonarchimedeanLocalField K]
  [Valuation.Compatible (NormedField.valuation (K := K))]
  [CharZero K]

/-- Conjugation by an element of the embedded abelian kernel acts trivially
on that kernel. -/
theorem conj_act_inl
    {N E Q : Type u} [CommGroup N] [Group E] [Group Q]
    (S : GroupExtension N E Q) (n : N) :
    S.conjAct (S.inl n) = 1 := by
  ext m
  apply S.inl_injective
  rw [S.inl_conjAct_comm]
  simp only [MulAut.one_apply]
  rw [← map_mul, mul_comm n m, map_mul]
  group

/-- For an extension with abelian kernel, conjugation on the kernel descends
from the middle group to the quotient. -/
@[implicit_reducible]
noncomputable def groupExtensionAction
    {N E Q : Type u} [CommGroup N] [Group E] [Group Q]
    (S : GroupExtension N E Q) : MulDistribMulAction Q N := by
  let s : S.Section := S.surjInvRightHom
  letI : SMul Q N := ⟨fun q n => S.conjAct (s q) n⟩
  letI : MulDistribMulAction E N :=
    MulDistribMulAction.compHom N S.conjAct
  have hcompat (e : E) (n : N) : S.rightHom e • n = e • n := by
    have hker : e * (s (S.rightHom e))⁻¹ ∈ S.rightHom.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv,
        GroupExtension.Section.rightHom_section]
      exact mul_inv_cancel _
    rw [← S.range_inl_eq_ker_rightHom] at hker
    obtain ⟨m, hm⟩ := hker
    have he : e = S.inl m * s (S.rightHom e) := by
      calc
        e = (e * (s (S.rightHom e))⁻¹) * s (S.rightHom e) := by group
        _ = S.inl m * s (S.rightHom e) := by rw [← hm]
    change S.conjAct (s (S.rightHom e)) n = S.conjAct e n
    have hconj : S.conjAct e = S.conjAct (s (S.rightHom e)) := by
      calc
        S.conjAct e = S.conjAct (S.inl m * s (S.rightHom e)) :=
          congrArg S.conjAct he
        _ = S.conjAct (s (S.rightHom e)) := by
          rw [map_mul, conj_act_inl, one_mul]
    exact congrArg (fun a : MulAut N => a n) hconj.symm
  let hMulAction : MulAction Q N :=
    S.rightHom_surjective.mulActionLeft S.rightHom hcompat
  exact
    { hMulAction with
      smul_one := by
        intro q
        obtain ⟨e, rfl⟩ := S.rightHom_surjective q
        rw [hcompat]
        exact smul_one e
      smul_mul := by
        intro q a b
        obtain ⟨e, rfl⟩ := S.rightHom_surjective q
        rw [hcompat, hcompat, hcompat]
        exact smul_mul' e a b }

@[simp]
theorem extension_action_smul
    {N E Q : Type u} [CommGroup N] [Group E] [Group Q]
    (S : GroupExtension N E Q) (e : E) (n : N) :
    @HSMul.hSMul E N N
        (@instHSMul E N
          (MulDistribMulAction.compHom N S.conjAct).toSMul) e n =
      @HSMul.hSMul Q N N
        (@instHSMul Q N (groupExtensionAction S).toSMul)
          (S.rightHom e) n := by
  change S.conjAct e n = S.conjAct
    (S.surjInvRightHom (S.rightHom e)) n
  have hker : e * (S.surjInvRightHom (S.rightHom e))⁻¹ ∈
      S.rightHom.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv,
      GroupExtension.Section.rightHom_section]
    exact mul_inv_cancel _
  rw [← S.range_inl_eq_ker_rightHom] at hker
  obtain ⟨m, hm⟩ := hker
  have he : e = S.inl m * S.surjInvRightHom (S.rightHom e) := by
    calc
      e = (e * (S.surjInvRightHom (S.rightHom e))⁻¹) *
          S.surjInvRightHom (S.rightHom e) := by group
      _ = S.inl m * S.surjInvRightHom (S.rightHom e) := by rw [← hm]
  have hconj : S.conjAct e =
      S.conjAct (S.surjInvRightHom (S.rightHom e)) := by
    calc
      S.conjAct e = S.conjAct
          (S.inl m * S.surjInvRightHom (S.rightHom e)) :=
        congrArg S.conjAct he
      _ = S.conjAct (S.surjInvRightHom (S.rightHom e)) := by
        rw [map_mul, conj_act_inl, one_mul]
  exact congrArg (fun a : MulAut N => a n) hconj

omit [CharZero K] in
/-- An integer prime to the residue-field cardinality is a unit in the
valuation ring of a nonarchimedean local field. -/
theorem cast_coprime_card
    (n : ℕ) (hn : (localResidueCard K).Coprime n) :
    IsUnit (n : Valuation.integer (ValuativeRel.valuation K)) := by
  let A := Valuation.integer (ValuativeRel.valuation K)
  let k := IsLocalRing.ResidueField A
  letI : Finite k := local_field_residue K
  letI : Fintype k := Fintype.ofFinite k
  apply (IsLocalRing.residue_ne_zero_iff_isUnit (n : A)).mp
  change (n : k) ≠ 0
  intro hzero
  let p := ringChar k
  have hp : Nat.Prime p := CharP.char_is_prime k p
  letI : Fact p.Prime := ⟨hp⟩
  have hpn : p ∣ n := (CharP.cast_eq_zero_iff k p n).mp hzero
  have hpq : p ∣ localResidueCard K := by
    let eResidue := IsLocalRing.ResidueField.mapEquiv
      (valuativeIntegerNorm K)
    have hcard : Nat.card k = localResidueCard K := by
      unfold localResidueCard
      exact Nat.card_congr eResidue.toEquiv
    rw [← hcard, Nat.card_eq_fintype_card]
    exact (prime_dvd_char_iff_dvd_card p).mp (dvd_refl p)
  have hpgcd : p ∣ Nat.gcd (localResidueCard K) n := Nat.dvd_gcd hpq hpn
  rw [hn.gcd_eq_one] at hpgcd
  exact hp.not_dvd_one hpgcd

omit [CharZero K] in
/-- A nonarchimedean local field contains every root of unity whose order
divides the order of its residue-field unit group. -/
theorem primitive_dvd_residue
    (e : ℕ) [NeZero e]
    (he : e ∣ localResidueCard K - 1) :
    (primitiveRoots e K).Nonempty := by
  let A := Valuation.integer (ValuativeRel.valuation K)
  let k := IsLocalRing.ResidueField A
  letI : HenselianLocalRing A :=
    integer_henselian_ring K
  letI : Finite k := local_field_residue K
  letI : Fintype k := Fintype.ofFinite k
  let eResidue := IsLocalRing.ResidueField.mapEquiv
    (valuativeIntegerNorm K)
  have hcard : Nat.card k = localResidueCard K := by
    unfold localResidueCard
    exact Nat.card_congr eResidue.toEquiv
  obtain ⟨g, hg⟩ :=
    IsCyclic.exists_ofOrder_eq_natCard (α := kˣ)
  have hgorder : orderOf g = localResidueCard K - 1 := by
    rw [hg, Nat.card_units, hcard]
  let g₀ : kˣ := g ^ (orderOf g / e)
  have hg₀order : orderOf g₀ = e := by
    apply orderOf_pow_orderOf_div
    · rw [hgorder]
      exact (Nat.sub_pos_of_lt (one_local_card K)).ne'
    · simpa [hgorder] using he
  let a₀ : k := g₀
  let a : A :=
    Submission.NumberTheory.Milne.teichmullerLift A a₀
  let q := Fintype.card k
  have haq : a ^ q = a := by
    exact sub_eq_zero.mp (by
      simpa [a, q, Polynomial.IsRoot.def] using
        Submission.NumberTheory.Milne.teichmuller_lift_root A a₀)
  have haPowRoot : (X ^ q - X : A[X]).IsRoot (a ^ e) := by
    rw [Polynomial.IsRoot.def, eval_sub, eval_pow, eval_X, sub_eq_zero]
    rw [← pow_mul, Nat.mul_comm e q, pow_mul, haq]
  have hOneRoot : (X ^ q - X : A[X]).IsRoot 1 := by
    simp [Polynomial.IsRoot.def]
  have haResiduePow : IsLocalRing.residue A (a ^ e) =
      IsLocalRing.residue A 1 := by
    rw [map_pow, map_one]
    rw [show IsLocalRing.residue A a = a₀ by
      exact Submission.NumberTheory.Milne.residue_teichmullerLift A a₀]
    change ((g₀ : k) ^ e) = 1
    have hg₀pow : g₀ ^ e = 1 := by
      rw [← hg₀order]
      exact pow_orderOf_eq_one g₀
    exact congrArg Units.val hg₀pow
  have haPow : a ^ e = 1 :=
    Submission.NumberTheory.Milne.teichmullerLift_unique A
      haPowRoot hOneRoot haResiduePow
  have haOrderDvd : orderOf a ∣ e := orderOf_dvd_of_pow_eq_one haPow
  have heOrderDvd : e ∣ orderOf a := by
    have hmap := orderOf_map_dvd (IsLocalRing.residue A).toMonoidHom a
    change orderOf (IsLocalRing.residue A a) ∣ orderOf a at hmap
    have hresidue : IsLocalRing.residue A a = a₀ :=
      Submission.NumberTheory.Milne.residue_teichmullerLift A a₀
    rw [hresidue, show orderOf a₀ = e by
      change orderOf (g₀ : k) = e
      rw [orderOf_units, hg₀order]] at hmap
    exact hmap
  have haPrimitive : IsPrimitiveRoot a e := by
    rw [IsPrimitiveRoot.iff_orderOf]
    exact Nat.dvd_antisymm haOrderDvd heOrderDvd
  refine ⟨(a : K), (mem_primitiveRoots (NeZero.pos e)).2 ?_⟩
  exact haPrimitive.map_of_injective
    (f := (A.subtype : A →+* K)) Subtype.val_injective

set_option maxHeartbeats 3000000 in
-- Reconstructing the canonical integral residue model is instance-heavy.
set_option synthInstance.maxHeartbeats 1000000 in
omit [CharZero K] in
/-- Arithmetic Frobenius raises every prime-to-residue-characteristic root
of unity to the residue-cardinality power. -/
theorem arithmetic_frobenius_primitive
    (f e : ℕ) [NeZero f] [NeZero e]
    (zeta : canonicalUnramifiedLevel K f)
    (hzeta : IsPrimitiveRoot zeta e)
    (hcoprime : (localResidueCard K).Coprime e) :
    canonicalArithmeticFrobenius K f zeta =
      zeta ^ localResidueCard K := by
  let E := canonicalUnramifiedLevel K f
  letI : Algebra.IsAlgebraic K E := Algebra.IsAlgebraic.of_finite K E
  letI : NontriviallyNormedField E :=
    FLExt.nontriviallyNormedField K E
  letI : NormedAlgebra K E := spectralNorm.normedAlgebra K E
  letI : IsUltrametricDist E := IsUltrametricDist.of_normedAlgebra K
  letI : ValuativeRel E := FLExt.valuativeRel K E
  letI : Valuation.Compatible (NormedField.valuation (K := E)) :=
    Valuation.Compatible.ofValuation (NormedField.valuation (K := E))
  letI : IsNonarchimedeanLocalField E :=
    FLExt.nonarchimedeanLocalField K E
  let A := Valuation.integer (ValuativeRel.valuation K)
  let N := Valuation.integer (NormedField.valuation (K := E))
  letI : Algebra A N := valuativeSpectralAlgebra K E
  obtain ⟨hFinite, hUnramified, hTower, hClosure⟩ :=
    level_spectral_data K f
  letI : Module.Finite A N := hFinite
  letI : Algebra.FormallyUnramified A N := hUnramified
  letI : IsScalarTower A N E := hTower
  letI : IsIntegralClosure N A E := hClosure
  letI : IsDiscreteValuationRing A :=
    discrete_valuation_ring K
  letI : IsDiscreteValuationRing N := by
    exact IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing
      (valuativeIntegerNorm E)
  letI : Algebra.IsIntegral A N := Algebra.IsIntegral.of_finite A N
  letI : FaithfulSMul A N :=
    (faithfulSMul_iff_algebraMap_injective A N).2 <| by
      intro a b hab
      apply Subtype.ext
      apply (algebraMap K E).injective
      simpa only [IsScalarTower.algebraMap_apply] using
        congrArg (algebraMap N E) hab
  letI : IsLocalHom (algebraMap A N) :=
    Algebra.IsIntegral.isLocalHom A N
  letI : (IsLocalRing.maximalIdeal N).LiesOver
      (IsLocalRing.maximalIdeal A) :=
    (Ideal.liesOver_iff _ _).mpr
      (IsLocalRing.maximalIdeal_comap (algebraMap A N)).symm
  letI : Algebra.IsUnramifiedAt A (IsLocalRing.maximalIdeal N) := by
    change Algebra.FormallyUnramified A
      (Localization.AtPrime (IsLocalRing.maximalIdeal N))
    infer_instance
  letI : IsFractionRing A K :=
    (Valuation.integer.integers (ValuativeRel.valuation K)).isFractionRing
  letI : IsFractionRing N E :=
    (Valuation.integer.integers
      (NormedField.valuation (K := E))).isFractionRing
  let G := Gal(E/K)
  letI : MulSemiringAction G N :=
    IsIntegralClosure.MulSemiringAction A K E N
  letI : IsGaloisGroup G A N :=
    IsGaloisGroup.of_isFractionRing G A N K E
  let k := IsLocalRing.ResidueField A
  let l := IsLocalRing.ResidueField N
  letI : Finite k := local_field_residue K
  letI : Fintype k := Fintype.ofFinite k
  letI : Module.Finite k l := inferInstance
  letI : Finite l := Module.finite_of_finite k
  letI : Fintype l := Fintype.ofFinite l
  have rootInteger (z : E) (hz : z ^ e = 1) : z ∈ N := by
    rw [Valuation.mem_integer_iff]
    have he0 : e ≠ 0 := NeZero.ne e
    exact ((pow_eq_one_iff_of_nonneg
      (bot_le : 0 ≤ NormedField.valuation z) he0).mp (by
        rw [← map_pow, hz, map_one])).le
  let zetaInt : N := ⟨zeta, rootInteger zeta hzeta.pow_eq_one⟩
  have hFrobPow : (canonicalArithmeticFrobenius K f zeta) ^ e = 1 := by
    have h := congrArg (canonicalArithmeticFrobenius K f) hzeta.pow_eq_one
    simpa using h
  let frobInt : N :=
    ⟨canonicalArithmeticFrobenius K f zeta, rootInteger _ hFrobPow⟩
  have hPowPow : (zeta ^ localResidueCard K) ^ e = 1 := by
    rw [← pow_mul, Nat.mul_comm, pow_mul, hzeta.pow_eq_one, one_pow]
  let powInt : N :=
    ⟨zeta ^ localResidueCard K, rootInteger _ hPowPow⟩
  have hres : IsLocalRing.residue N frobInt =
      IsLocalRing.residue N powInt := by
    have hred := galois_residue_field
      (IsDiscreteValuationRing.not_a_field A)
      (IsDiscreteValuationRing.not_a_field N)
      (canonicalArithmeticFrobenius K f) zetaInt
    change (canonicalUnramifiedResidue K f
        (canonicalArithmeticFrobenius K f))
          (IsLocalRing.residue N zetaInt) =
      IsLocalRing.residue N
        (canonicalArithmeticFrobenius K f • zetaInt) at hred
    rw [canonical_unramified_frobenius,
      FiniteField.coe_frobeniusAlgEquivOfAlgebraic] at hred
    have hsmul : canonicalArithmeticFrobenius K f • zetaInt = frobInt := by
      apply Subtype.ext
      simpa [zetaInt, frobInt] using
        (algebraMap.coe_smul' (B := N) (C := E)
          (canonicalArithmeticFrobenius K f) zetaInt)
    let eResidue := IsLocalRing.ResidueField.mapEquiv
      (valuativeIntegerNorm K)
    have hcard : Fintype.card k = localResidueCard K := by
      unfold localResidueCard
      rw [← Nat.card_eq_fintype_card]
      exact Nat.card_congr eResidue.toEquiv
    calc
      IsLocalRing.residue N frobInt =
          IsLocalRing.residue N
            (canonicalArithmeticFrobenius K f • zetaInt) := by rw [hsmul]
      _ = (IsLocalRing.residue N zetaInt) ^ Fintype.card k := hred.symm
      _ = (IsLocalRing.residue N zetaInt) ^ localResidueCard K := by rw [hcard]
      _ = IsLocalRing.residue N powInt := by
        rw [← map_pow]
        congr 1
  have heUnitA : IsUnit (e : A) :=
    cast_coprime_card K e hcoprime
  have heUnitN : IsUnit (e : N) := by
    simpa using heUnitA.map (algebraMap A N)
  have hInt : frobInt = powInt :=
    Submission.NumberTheory.Milne.residue_nat_cast
      heUnitN
      (by apply Subtype.ext; exact hFrobPow)
      (by apply Subtype.ext; exact hPowPow) hres
  exact congrArg Subtype.val hInt

/-- If `e` divides `q^f - 1`, the canonical unramified extension of degree
`f` contains a primitive `e`th root of unity. -/
theorem level_primitive_root
    (f e : ℕ) [NeZero f] [NeZero e]
    (he : e ∣ localResidueCard K ^ f - 1) :
    (primitiveRoots e (canonicalUnramifiedLevel K f)).Nonempty := by
  let Ω := SeparableClosure K
  obtain ⟨zeta, hzeta⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω e
  have hqpos : 0 < localResidueCard K ^ f :=
    pow_pos (Nat.zero_lt_one.trans (one_local_card K)) f
  have hzeta_sub : zeta ^ (localResidueCard K ^ f - 1) = 1 :=
    (hzeta.pow_eq_one_iff_dvd _).2 he
  have hzeta_frob : zeta ^ localResidueCard K ^ f = zeta := by
    calc
      zeta ^ localResidueCard K ^ f =
          zeta ^ ((localResidueCard K ^ f - 1) + 1) := by
            rw [Nat.sub_add_cancel hqpos]
      _ = zeta ^ (localResidueCard K ^ f - 1) * zeta := by rw [pow_succ]
      _ = zeta := by rw [hzeta_sub, one_mul]
  have hzeta_root :
      ((localFrobeniusPolynomial K f).map (algebraMap K Ω)).IsRoot zeta := by
    simp [localFrobeniusPolynomial, IsRoot, hzeta_frob]
  have hzeta_mem :
      zeta ∈ (canonicalUnramifiedLevel K f : IntermediateField K Ω) := by
    apply FiniteGaloisIntermediateField.subset_adjoin K
    rw [(local_frobenius_monic K (NeZero.pos f)).mem_rootSet]
    simpa [IsRoot, aeval_def] using hzeta_root
  let zetaLevel : canonicalUnramifiedLevel K f := ⟨zeta, hzeta_mem⟩
  refine ⟨zetaLevel, ?_⟩
  apply (mem_primitiveRoots (NeZero.pos e)).2
  apply IsPrimitiveRoot.of_map_of_injective
      (f := (canonicalUnramifiedLevel K f : IntermediateField K Ω).val)
  · simpa [zetaLevel] using hzeta
  · exact Subtype.val_injective

set_option maxHeartbeats 1000000 in
-- Extra heartbeats are needed for the large search space in this proof.
omit [CharZero K] in
/-- The norm on integer units from every positive canonical unramified level
is surjective.  This is the local arithmetic input for killing a central
unit-valued factor set. -/
theorem level_integer_surjective
    (f : ℕ) [NeZero f] :
    let E := canonicalUnramifiedLevel K f
    letI : Algebra.IsAlgebraic K E := Algebra.IsAlgebraic.of_finite K E
    letI : NontriviallyNormedField E :=
      FLExt.nontriviallyNormedField K E
    letI : NormedAlgebra K E := spectralNorm.normedAlgebra K E
    letI : IsUltrametricDist E := IsUltrametricDist.of_normedAlgebra K
    letI : ValuativeRel E := FLExt.valuativeRel K E
    letI : Valuation.Compatible (NormedField.valuation (K := E)) :=
      Valuation.Compatible.ofValuation (NormedField.valuation (K := E))
    letI : IsNonarchimedeanLocalField E :=
      FLExt.nonarchimedeanLocalField K E
    Function.Surjective (FLExt.integerUnitNorm K E) := by
  let E := canonicalUnramifiedLevel K f
  letI : Algebra.IsAlgebraic K E := Algebra.IsAlgebraic.of_finite K E
  letI : NontriviallyNormedField E :=
    FLExt.nontriviallyNormedField K E
  letI : NormedAlgebra K E := spectralNorm.normedAlgebra K E
  letI : IsUltrametricDist E := IsUltrametricDist.of_normedAlgebra K
  letI : ValuativeRel E := FLExt.valuativeRel K E
  letI : Valuation.Compatible (NormedField.valuation (K := E)) :=
    Valuation.Compatible.ofValuation (NormedField.valuation (K := E))
  letI : IsNonarchimedeanLocalField E :=
    FLExt.nonarchimedeanLocalField K E
  obtain ⟨hResidueAlgebra, hUnit, _horder, _hIntegerData⟩ :=
    unramified_level_data K f
  letI : Algebra
      (IsLocalRing.ResidueField
        (Valuation.integer (ValuativeRel.valuation K)))
      (IsLocalRing.ResidueField
        (Valuation.integer (ValuativeRel.valuation E))) := hResidueAlgebra
  let hLocal : UnramifiedLocalData K E
      (FLExt.integerUnitNorm K E) :=
    FLExt.unramified_data_unit
      K E hResidueAlgebra hUnit
  exact unramified_units_surjective K E
    (FLExt.integerUnitNorm K E) hLocal

set_option maxHeartbeats 1000000 in
-- Extra heartbeats are needed for the large search space in this proof.
omit [CharZero K] in
/-- Every finite-order unit of the base field is a field norm from a positive
canonical unramified level. -/
theorem unramified_level_one
    (f n : ℕ) [NeZero f] [NeZero n] (z : Kˣ) (hz : z ^ n = 1) :
    let E := canonicalUnramifiedLevel K f
    letI : Algebra.IsAlgebraic K E := Algebra.IsAlgebraic.of_finite K E
    letI : NontriviallyNormedField E :=
      FLExt.nontriviallyNormedField K E
    letI : NormedAlgebra K E := spectralNorm.normedAlgebra K E
    letI : IsUltrametricDist E := IsUltrametricDist.of_normedAlgebra K
    letI : ValuativeRel E := FLExt.valuativeRel K E
    letI : Valuation.Compatible (NormedField.valuation (K := E)) :=
      Valuation.Compatible.ofValuation (NormedField.valuation (K := E))
    letI : IsNonarchimedeanLocalField E :=
      FLExt.nonarchimedeanLocalField K E
    ∃ v : (Valuation.integer (ValuativeRel.valuation E))ˣ,
      Algebra.norm K
        (((v : Valuation.integer (ValuativeRel.valuation E)) : E)) = z := by
  let E := canonicalUnramifiedLevel K f
  letI : Algebra.IsAlgebraic K E := Algebra.IsAlgebraic.of_finite K E
  letI : NontriviallyNormedField E :=
    FLExt.nontriviallyNormedField K E
  letI : NormedAlgebra K E := spectralNorm.normedAlgebra K E
  letI : IsUltrametricDist E := IsUltrametricDist.of_normedAlgebra K
  letI : ValuativeRel E := FLExt.valuativeRel K E
  letI : Valuation.Compatible (NormedField.valuation (K := E)) :=
    Valuation.Compatible.ofValuation (NormedField.valuation (K := E))
  letI : IsNonarchimedeanLocalField E :=
    FLExt.nonarchimedeanLocalField K E
  have hzAdd : n • Additive.ofMul z = 0 := by
    apply Additive.toMul.injective
    simpa only [toMul_nsmul, toMul_ofMul, toMul_zero] using hz
  have hzOrderN :
      n • localUnitOrder K (Additive.ofMul z) = 0 := by
    rw [← map_nsmul, hzAdd, map_zero]
  have hzOrder : localUnitOrder K (Additive.ofMul z) = 0 :=
    (nsmul_eq_zero_iff_right (NeZero.ne n)).mp hzOrderN
  obtain ⟨u, hu⟩ :=
    integer_order_zero K z hzOrder
  obtain ⟨v, hv⟩ :=
    level_integer_surjective K f u
  refine ⟨v, ?_⟩
  rw [← FLExt.integer_norm_coe, hv]
  exact congrArg Units.val hu

/-- A finite-order coefficient map into field units, regarded as a map into
valuation-integer units. -/
noncomputable def coefficientIntegerUnits
    {C : Type v} {F : Type w} [CommGroup C] [Field F] [ValuativeRel F]
    (n : ℕ) [NeZero n] (phi : C →* Fˣ)
    (hpow : ∀ c, (phi c) ^ n = 1) :
    C →* (Valuation.integer (ValuativeRel.valuation F))ˣ :=
  (Submission.CField.LFTheory.localInteger F).comp
    (phi.codRestrict
      (Submission.CField.LFTheory.localUnitSubgroup F) (by
        intro c
        change ValuativeRel.valuation F ((phi c : Fˣ) : F) = 1
        apply (pow_eq_one_iff_of_nonneg
          (bot_le : 0 ≤ ValuativeRel.valuation F ((phi c : Fˣ) : F))
          (NeZero.ne n)).mp
        rw [← map_pow]
        rw [show ((phi c : Fˣ) : F) ^ n = 1 from
          congrArg Units.val (hpow c), map_one]))

@[simp]
theorem integer_units_coe
    {C : Type v} {F : Type w} [CommGroup C] [Field F] [ValuativeRel F]
    (n : ℕ) [NeZero n] (phi : C →* Fˣ)
    (hpow : ∀ c, (phi c) ^ n = 1) (c : C) :
    ((((coefficientIntegerUnits n phi hpow c :
        (Valuation.integer (ValuativeRel.valuation F))ˣ) :
          Valuation.integer (ValuativeRel.valuation F)) : F)) =
      ((phi c : Fˣ) : F) := rfl

/-- Inclusion of valuation-integer units into field units. -/
noncomputable def integerUnitsField
    (F : Type w) [Field F] [ValuativeRel F] :
    (Valuation.integer (ValuativeRel.valuation F))ˣ →* Fˣ :=
  Units.map
    (Valuation.integer (ValuativeRel.valuation F)).subtype.toMonoidHom

@[simp]
theorem integer_units_coefficient
    {C : Type v} {F : Type w} [CommGroup C] [Field F] [ValuativeRel F]
    (n : ℕ) [NeZero n] (phi : C →* Fˣ)
    (hpow : ∀ c, (phi c) ^ n = 1) (c : C) :
    integerUnitsField F
        (coefficientIntegerUnits n phi hpow c) = phi c := by
  apply Units.ext
  rfl

/-- Equivariance of the integer-unit factor of an equivariant finite-order
coefficient map. -/
theorem integer_units_equivariant
    {G : Type u} {C : Type v} {F : Type w}
    [Group G] [CommGroup C] [Field F] [ValuativeRel F]
    [MulDistribMulAction G C] [MulSemiringAction G F]
    [MulSemiringAction G (Valuation.integer (ValuativeRel.valuation F))]
    (n : ℕ) [NeZero n]
    (hcoe : ∀ (sigma : G)
      (z : (Valuation.integer (ValuativeRel.valuation F))ˣ),
      (((sigma • z :
          (Valuation.integer (ValuativeRel.valuation F))ˣ) :
            Valuation.integer (ValuativeRel.valuation F)) : F) =
        sigma • (((z :
          (Valuation.integer (ValuativeRel.valuation F))ˣ) :
            Valuation.integer (ValuativeRel.valuation F)) : F))
    (phi : C →* Fˣ)
    (hphi : ∀ (sigma : G) (c : C), phi (sigma • c) = sigma • phi c)
    (hpow : ∀ c, (phi c) ^ n = 1) :
    ∀ (sigma : G) (c : C),
      coefficientIntegerUnits n phi hpow (sigma • c) =
        sigma • coefficientIntegerUnits n phi hpow c := by
  intro sigma c
  apply Units.ext
  apply Subtype.ext
  change ((phi (sigma • c) : Fˣ) : F) =
    (((sigma • coefficientIntegerUnits n phi hpow c :
        (Valuation.integer (ValuativeRel.valuation F))ˣ) :
          Valuation.integer (ValuativeRel.valuation F)) : F)
  rw [hcoe]
  exact congrArg Units.val (hphi sigma c)

/-- The inclusion of integer units into field units is equivariant whenever
the action on the valuation ring is the restriction of the field action. -/
theorem integer_field_equivariant
    {G : Type u} {F : Type w} [Group G] [Field F] [ValuativeRel F]
    [MulSemiringAction G F]
    [MulSemiringAction G (Valuation.integer (ValuativeRel.valuation F))]
    (hcoe : ∀ (sigma : G)
      (z : (Valuation.integer (ValuativeRel.valuation F))ˣ),
      (((sigma • z :
          (Valuation.integer (ValuativeRel.valuation F))ˣ) :
            Valuation.integer (ValuativeRel.valuation F)) : F) =
        sigma • (((z :
          (Valuation.integer (ValuativeRel.valuation F))ˣ) :
            Valuation.integer (ValuativeRel.valuation F)) : F)) :
    ∀ (sigma : G)
      (z : (Valuation.integer (ValuativeRel.valuation F))ˣ),
      integerUnitsField F (sigma • z) =
        sigma • integerUnitsField F z := by
  intro sigma z
  apply Units.ext
  exact hcoe sigma z

/-- A finite-order coefficient map factors through valuation-integer units.
If integer-unit-valued `H²` vanishes, its image in field-unit-valued `H²`
vanishes as well. -/
theorem h_units_subsingleton
    {G : Type u} {C : Type v} {F : Type w}
    [Group G] [CommGroup C] [Field F] [ValuativeRel F]
    [MulDistribMulAction G C] [MulSemiringAction G F]
    [MulSemiringAction G (Valuation.integer (ValuativeRel.valuation F))]
    [Subsingleton (MHTwo G
      (Valuation.integer (ValuativeRel.valuation F))ˣ)]
    (n : ℕ) [NeZero n]
    (hcoe : ∀ (sigma : G)
      (z : (Valuation.integer (ValuativeRel.valuation F))ˣ),
      (((sigma • z :
          (Valuation.integer (ValuativeRel.valuation F))ˣ) :
            Valuation.integer (ValuativeRel.valuation F)) : F) =
        sigma • (((z :
          (Valuation.integer (ValuativeRel.valuation F))ˣ) :
            Valuation.integer (ValuativeRel.valuation F)) : F))
    (phi : C →* Fˣ)
    (hphi : ∀ sigma c, phi (sigma • c) = sigma • phi c)
    (hpow : ∀ c, (phi c) ^ n = 1)
    (x : MHTwo G C) :
    MHTwo.mapCoefficientsHom phi hphi x = 1 := by
  let phiInteger : C →*
      (Valuation.integer (ValuativeRel.valuation F))ˣ :=
    coefficientIntegerUnits n phi hpow
  have hphiInteger (sigma : G) (c : C) :
      phiInteger (sigma • c) = sigma • phiInteger c := by
    apply Units.ext
    apply Subtype.ext
    change ((phi (sigma • c) : Fˣ) : F) =
      (((sigma • phiInteger c :
          (Valuation.integer (ValuativeRel.valuation F))ˣ) :
            Valuation.integer (ValuativeRel.valuation F)) : F)
    rw [hcoe]
    exact congrArg Units.val (hphi sigma c)
  let integerToField :
      (Valuation.integer (ValuativeRel.valuation F))ˣ →* Fˣ :=
    integerUnitsField F
  have hintegerToField (sigma : G)
      (z : (Valuation.integer (ValuativeRel.valuation F))ˣ) :
      integerToField (sigma • z) = sigma • integerToField z := by
    apply Units.ext
    exact hcoe sigma z
  have hcomp : integerToField.comp phiInteger = phi := by
    ext c
    rfl
  have hcomposite (sigma : G) (c : C) :
      (integerToField.comp phiInteger) (sigma • c) =
        sigma • (integerToField.comp phiInteger) c := by
    change integerToField (phiInteger (sigma • c)) =
      sigma • integerToField (phiInteger c)
    rw [hphiInteger, hintegerToField]
  let unitClass : MHTwo G
      (Valuation.integer (ValuativeRel.valuation F))ˣ :=
    MHTwo.mapCoefficientsHom phiInteger hphiInteger x
  have hunitClass : unitClass = 1 := Subsingleton.elim _ _
  calc
    MHTwo.mapCoefficientsHom phi hphi x =
        MHTwo.mapCoefficientsHom (integerToField.comp phiInteger)
          hcomposite x := by
            cases hcomp
            rfl
    _ = MHTwo.mapCoefficientsHom integerToField hintegerToField
          unitClass := by
            symm
            exact MHTwo.coefficients_hom_comp
              phiInteger integerToField hphiInteger hintegerToField
                hcomposite x
    _ = 1 := by rw [hunitClass, map_one]

set_option synthInstance.maxHeartbeats 1000000 in
-- Extra heartbeats are needed for the typeclass search in this proof.
set_option maxHeartbeats 1200000 in
omit [CharZero K] in
/-- An equivariant finite-order coefficient map into a canonical unramified
level induces the zero map on multiplicative `H²`. -/
theorem canonical_unramified_level
    (f n : ℕ) [NeZero f] [NeZero n] :
    let E := canonicalUnramifiedLevel K f
    letI : Algebra.IsAlgebraic K E := Algebra.IsAlgebraic.of_finite K E
    letI : NontriviallyNormedField E :=
      FLExt.nontriviallyNormedField K E
    letI : NormedAlgebra K E := spectralNorm.normedAlgebra K E
    letI : IsUltrametricDist E := IsUltrametricDist.of_normedAlgebra K
    letI : ValuativeRel E := FLExt.valuativeRel K E
    letI : MulSemiringAction Gal(E/K)
        (Valuation.integer (ValuativeRel.valuation E)) :=
      FLExt.integerGaloisAction K E
    ∀ {C : Type u} [CommGroup C] [MulDistribMulAction Gal(E/K) C]
      (phi : C →* Eˣ)
      (hphi : ∀ sigma c, phi (sigma • c) = sigma • phi c)
      (_hpow : ∀ c, (phi c) ^ n = 1)
      (x : MHTwo Gal(E/K) C),
      MHTwo.mapCoefficientsHom phi hphi x = 1 := by
  let E := canonicalUnramifiedLevel K f
  letI : Algebra.IsAlgebraic K E := Algebra.IsAlgebraic.of_finite K E
  letI : NontriviallyNormedField E :=
    FLExt.nontriviallyNormedField K E
  letI : NormedAlgebra K E := spectralNorm.normedAlgebra K E
  letI : IsUltrametricDist E := IsUltrametricDist.of_normedAlgebra K
  letI : ValuativeRel E := FLExt.valuativeRel K E
  letI : Valuation.Compatible (NormedField.valuation (K := E)) :=
    Valuation.Compatible.ofValuation (NormedField.valuation (K := E))
  letI : IsNonarchimedeanLocalField E :=
    FLExt.nonarchimedeanLocalField K E
  letI : (NormedField.valuation (K := K)).HasExtension
      (NormedField.valuation (K := E)) :=
    spectralValuationExtension K E
  letI : (ValuativeRel.valuation K).HasExtension
      (ValuativeRel.valuation E) :=
    FLExt.valuativeSpectralExtension K E
  letI : MulSemiringAction Gal(E/K)
      (Valuation.integer (ValuativeRel.valuation E)) :=
    FLExt.integerGaloisAction K E
  letI : Subsingleton (MHTwo Gal(E/K)
      (Valuation.integer (ValuativeRel.valuation E))ˣ) :=
    level_integer_subsingleton K f
  change ∀ {C : Type u} [CommGroup C]
      [MulDistribMulAction Gal(E/K) C]
      (phi : C →* Eˣ)
      (hphi : ∀ sigma c, phi (sigma • c) = sigma • phi c)
      (hpow : ∀ c, (phi c) ^ n = 1)
      (x : MHTwo Gal(E/K) C),
      MHTwo.mapCoefficientsHom phi hphi x = 1
  intro C _ _ phi hphi hpow x
  exact h_units_subsingleton
    (n := n)
    (hcoe := fun sigma z ↦ algebraMap.coe_smul'
      (B := Valuation.integer (ValuativeRel.valuation E))
      (C := E) sigma (z : Valuation.integer (ValuativeRel.valuation E)))
    phi hphi hpow x

/-- A finite tame pair automa supplies the root of unity in the
canonical unramified level whose degree is the Frobenius quotient order. -/
theorem tame_level_primitive
    {G : Type u} [Group G] [Finite G] (x y : G)
    (hcoprime : (localResidueCard K).Coprime (orderOf x))
    (hconj : y * x * y⁻¹ = x ^ localResidueCard K) :
    let H : Subgroup G := Subgroup.closure ({x, y} : Set G)
    let I : Subgroup H := (Subgroup.zpowers x).subgroupOf H
    letI : I.Normal := tame_inertia_closure
      x y (localResidueCard K) hcoprime hconj
    (primitiveRoots (orderOf x)
      (canonicalUnramifiedLevel K (Nat.card (H ⧸ I)))).Nonempty := by
  let H : Subgroup G := Subgroup.closure ({x, y} : Set G)
  let I : Subgroup H := (Subgroup.zpowers x).subgroupOf H
  letI : I.Normal := tame_inertia_closure
    x y (localResidueCard K) hcoprime hconj
  let f := Nat.card (H ⧸ I)
  let e := orderOf x
  letI : NeZero f := ⟨(Nat.card_pos : 0 < Nat.card (H ⧸ I)).ne'⟩
  letI : NeZero e := ⟨(orderOf_pos x).ne'⟩
  apply level_primitive_root K f e
  exact tame_inertia_dvd
    x y (localResidueCard K) (Nat.zero_lt_one.trans (one_local_card K))
      hcoprime hconj

/-- The unramified quotient attached to a finite tame pair.  It kills the
inertia generator and sends the Frobenius generator to canonical arithmetic
Frobenius. -/
noncomputable def tamePairUnramified
    {G : Type u} [Group G] [Finite G] (x y : G)
    (hcoprime : (localResidueCard K).Coprime (orderOf x))
    (hconj : y * x * y⁻¹ = x ^ localResidueCard K) :
    let H : Subgroup G := Subgroup.closure ({x, y} : Set G)
    let I : Subgroup H := (Subgroup.zpowers x).subgroupOf H
    letI : I.Normal := tame_inertia_closure
      x y (localResidueCard K) hcoprime hconj
    H →* Gal(canonicalUnramifiedLevel K (Nat.card (H ⧸ I))/K) := by
  let H : Subgroup G := Subgroup.closure ({x, y} : Set G)
  let xH : H := ⟨x, Subgroup.subset_closure (Set.mem_insert x {y})⟩
  let yH : H := ⟨y, Subgroup.subset_closure
    (Set.mem_insert_of_mem x (Set.mem_singleton y))⟩
  let I : Subgroup H := (Subgroup.zpowers x).subgroupOf H
  letI : I.Normal := tame_inertia_closure
    x y (localResidueCard K) hcoprime hconj
  let f := Nat.card (H ⧸ I)
  letI : NeZero f := ⟨(Nat.card_pos : 0 < Nat.card (H ⧸ I)).ne'⟩
  let q : H →* H ⧸ I := QuotientGroup.mk' I
  let eQ : Multiplicative (ZMod f) ≃* H ⧸ I :=
    zmodMulEquivOfGenerator (g := q yH) (by
      intro z
      rw [tame_frobenius_zpowers
        x y (localResidueCard K) hcoprime hconj]
      exact Subgroup.mem_top z) rfl
  exact (levelZMod K f).toMonoidHom.comp
    (eQ.symm.toMonoidHom.comp q)

omit [CharZero K] in
theorem tame_pair_unramified
    {G : Type u} [Group G] [Finite G] (x y : G)
    (hcoprime : (localResidueCard K).Coprime (orderOf x))
    (hconj : y * x * y⁻¹ = x ^ localResidueCard K)
    (h : Subgroup.closure ({x, y} : Set G)) :
    let H : Subgroup G := Subgroup.closure ({x, y} : Set G)
    let I : Subgroup H := (Subgroup.zpowers x).subgroupOf H
    letI : I.Normal := tame_inertia_closure
      x y (localResidueCard K) hcoprime hconj
    tamePairUnramified K x y hcoprime hconj h = 1 ↔ h ∈ I := by
  let H : Subgroup G := Subgroup.closure ({x, y} : Set G)
  let I : Subgroup H := (Subgroup.zpowers x).subgroupOf H
  letI : I.Normal := tame_inertia_closure
    x y (localResidueCard K) hcoprime hconj
  let f := Nat.card (H ⧸ I)
  letI : NeZero f := ⟨(Nat.card_pos : 0 < Nat.card (H ⧸ I)).ne'⟩
  let q : H →* H ⧸ I := QuotientGroup.mk' I
  let yH : H := ⟨y, Subgroup.subset_closure
    (Set.mem_insert_of_mem x (Set.mem_singleton y))⟩
  let eQ : Multiplicative (ZMod f) ≃* H ⧸ I :=
    zmodMulEquivOfGenerator (g := q yH) (by
      intro z
      rw [tame_frobenius_zpowers
        x y (localResidueCard K) hcoprime hconj]
      exact Subgroup.mem_top z) rfl
  let eU := levelZMod K f
  change eU (eQ.symm (q h)) = 1 ↔ h ∈ I
  constructor
  · intro hz
    have hzQ : eQ.symm (q h) = 1 := by
      apply eU.injective
      simpa using hz
    have hq : q h = 1 := by
      apply eQ.symm.injective
      simpa using hzQ
    exact (QuotientGroup.eq_one_iff h).mp hq
  · intro hh
    have hq : q h = 1 := (QuotientGroup.eq_one_iff h).2 hh
    rw [hq, map_one, map_one]

omit [CharZero K] in
@[simp]
theorem tame_base_inertia
    {G : Type u} [Group G] [Finite G] (x y : G)
    (hcoprime : (localResidueCard K).Coprime (orderOf x))
    (hconj : y * x * y⁻¹ = x ^ localResidueCard K) :
    let H : Subgroup G := Subgroup.closure ({x, y} : Set G)
    let I : Subgroup H := (Subgroup.zpowers x).subgroupOf H
    letI : I.Normal := tame_inertia_closure
      x y (localResidueCard K) hcoprime hconj
    letI : NeZero (Nat.card (H ⧸ I)) :=
      ⟨(Nat.card_pos : 0 < Nat.card (H ⧸ I)).ne'⟩
    tamePairUnramified K x y hcoprime hconj
        (⟨x, Subgroup.subset_closure (Set.mem_insert x {y})⟩ : H) = 1 := by
  exact (tame_pair_unramified K x y hcoprime hconj _).2
    (Subgroup.mem_zpowers x)

omit [CharZero K] in
@[simp]
theorem tame_pair_frobenius
    {G : Type u} [Group G] [Finite G] (x y : G)
    (hcoprime : (localResidueCard K).Coprime (orderOf x))
    (hconj : y * x * y⁻¹ = x ^ localResidueCard K) :
    let H : Subgroup G := Subgroup.closure ({x, y} : Set G)
    let I : Subgroup H := (Subgroup.zpowers x).subgroupOf H
    letI : I.Normal := tame_inertia_closure
      x y (localResidueCard K) hcoprime hconj
    letI : NeZero (Nat.card (H ⧸ I)) :=
      ⟨(Nat.card_pos : 0 < Nat.card (H ⧸ I)).ne'⟩
    tamePairUnramified K x y hcoprime hconj
        (⟨y, Subgroup.subset_closure
          (Set.mem_insert_of_mem x (Set.mem_singleton y))⟩ : H) =
      canonicalArithmeticFrobenius K (Nat.card (H ⧸ I)) := by
  let H : Subgroup G := Subgroup.closure ({x, y} : Set G)
  let I : Subgroup H := (Subgroup.zpowers x).subgroupOf H
  letI : I.Normal := tame_inertia_closure
    x y (localResidueCard K) hcoprime hconj
  let f := Nat.card (H ⧸ I)
  letI : NeZero f := ⟨(Nat.card_pos : 0 < Nat.card (H ⧸ I)).ne'⟩
  let q : H →* H ⧸ I := QuotientGroup.mk' I
  let yH : H := ⟨y, Subgroup.subset_closure
    (Set.mem_insert_of_mem x (Set.mem_singleton y))⟩
  let eQ : Multiplicative (ZMod f) ≃* H ⧸ I :=
    zmodMulEquivOfGenerator (g := q yH) (by
      intro z
      rw [tame_frobenius_zpowers
        x y (localResidueCard K) hcoprime hconj]
      exact Subgroup.mem_top z) rfl
  change levelZMod K f
      (eQ.symm (q yH)) = canonicalArithmeticFrobenius K f
  rw [zmodMulEquivOfGenerator_symm_apply_generator,
    level_frobenius_z]

/-- The tame pair as an extension of its canonical unramified quotient by
the cyclic inertia subgroup. -/
noncomputable def tamePairExtension
    {G : Type u} [Group G] [Finite G] (x y : G)
    (hcoprime : (localResidueCard K).Coprime (orderOf x))
    (hconj : y * x * y⁻¹ = x ^ localResidueCard K) :
    let H : Subgroup G := Subgroup.closure ({x, y} : Set G)
    let I : Subgroup H := (Subgroup.zpowers x).subgroupOf H
    letI : I.Normal := tame_inertia_closure
      x y (localResidueCard K) hcoprime hconj
    GroupExtension I H
      Gal(canonicalUnramifiedLevel K (Nat.card (H ⧸ I))/K) := by
  let H : Subgroup G := Subgroup.closure ({x, y} : Set G)
  let I : Subgroup H := (Subgroup.zpowers x).subgroupOf H
  letI : I.Normal := tame_inertia_closure
    x y (localResidueCard K) hcoprime hconj
  let f := Nat.card (H ⧸ I)
  letI : NeZero f := ⟨(Nat.card_pos : 0 < Nat.card (H ⧸ I)).ne'⟩
  let p := tamePairUnramified K x y hcoprime hconj
  refine
    { inl := I.subtype
      rightHom := p
      inl_injective := Subtype.val_injective
      range_inl_eq_ker_rightHom := ?_
      rightHom_surjective := ?_ }
  · ext h
    rw [MonoidHom.mem_range, MonoidHom.mem_ker]
    constructor
    · rintro ⟨i, rfl⟩
      exact (tame_pair_unramified
        K x y hcoprime hconj _).2 i.property
    · intro hh
      refine ⟨⟨h, (tame_pair_unramified
        K x y hcoprime hconj h).1 hh⟩, rfl⟩
  · intro sigma
    let q : H →* H ⧸ I := QuotientGroup.mk' I
    let yH : H := ⟨y, Subgroup.subset_closure
      (Set.mem_insert_of_mem x (Set.mem_singleton y))⟩
    let eQ : Multiplicative (ZMod f) ≃* H ⧸ I :=
      zmodMulEquivOfGenerator (g := q yH) (by
        intro z
        rw [tame_frobenius_zpowers
          x y (localResidueCard K) hcoprime hconj]
        exact Subgroup.mem_top z) rfl
    let eU := levelZMod K f
    obtain ⟨z, hz⟩ := eU.surjective sigma
    obtain ⟨w, hw⟩ := eQ.symm.surjective z
    obtain ⟨h, hh⟩ := QuotientGroup.mk'_surjective I w
    refine ⟨h, ?_⟩
    change eU (eQ.symm (q h)) = sigma
    rw [hh, hw, hz]

end TBluepr
end Submission
