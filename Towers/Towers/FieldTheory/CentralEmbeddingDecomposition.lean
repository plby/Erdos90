import Towers.FieldTheory.CentralEmbeddingPresentation
import Towers.NumberTheory.Galois.FrobeniusElement

/-!
# Tame generators of a number-field decomposition group

An arithmetic Frobenius generates the decomposition quotient by inertia.
Consequently, a chosen generator of tame inertia together with that exact
Frobenius generates the whole decomposition group.  This is the arithmetic
bridge from a killed Koch relator to a local splitting of a central embedding
problem.
-/

namespace Towers
namespace TBluepr

open Towers.NumberTheory.Milne
open scoped Pointwise

noncomputable section

local instance rationalIntegerGaloisAction
    {L : Type*} [Field L] [Algebra ℚ L] [FiniteDimensional ℚ L]
    [IsGalois ℚ L] :
    MulSemiringAction Gal(L/ℚ) (NumberField.RingOfIntegers L) :=
  IsIntegralClosure.MulSemiringAction ℤ ℚ L (NumberField.RingOfIntegers L)

/-- An arithmetic Frobenius belongs to the decomposition group at its
prime. -/
theorem arith_frob_decomposition
    {L : Type*} [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (P : Ideal (NumberField.RingOfIntegers L)) [P.IsPrime]
    (sigma : Gal(L/ℚ))
    (hsigma : IsArithFrobAt ℤ sigma P) :
    sigma ∈ MulAction.stabilizer (Gal(L/ℚ)) P := by
  rw [MulAction.mem_stabilizer_iff]
  ext x
  rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem]
  have h := Ideal.ext_iff.mp hsigma.comap_eq (sigma⁻¹ • x)
  rw [Ideal.mem_comap, MulSemiringAction.toAlgHom_apply] at h
  have hcancel : sigma • (sigma⁻¹ • x) = x := by simp
  rw [hcancel] at h
  exact h.symm

/-- The image of an arithmetic Frobenius generates the decomposition group
modulo inertia. -/
theorem arith_frob_generates
    {L : Type*} [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    {q : ℕ} (hq : Nat.Prime q)
    (P : Ideal (NumberField.RingOfIntegers L)) [P.IsPrime]
    [P.LiesOver (Ideal.rationalPrimeIdeal q)]
    (sigma : Gal(L/ℚ))
    (hsigma : IsArithFrobAt ℤ sigma P) :
    let D := MulAction.stabilizer (Gal(L/ℚ)) P
    let I := (P.inertia (Gal(L/ℚ))).subgroupOf D
    let sigmaD : D := ⟨sigma,
      arith_frob_decomposition P sigma hsigma⟩
    Subgroup.zpowers (QuotientGroup.mk' I sigmaD) = ⊤ := by
  classical
  let p : Ideal ℤ := P.under ℤ
  letI : p.IsPrime := inferInstance
  letI : P.LiesOver p := ⟨rfl⟩
  have hpq : p = Ideal.rationalPrimeIdeal q :=
    (P.over_def (Ideal.rationalPrimeIdeal q)).symm
  have hp : p ≠ ⊥ := by
    rw [hpq]
    dsimp [Ideal.rationalPrimeIdeal]
    exact mt Ideal.span_singleton_eq_bot.mp (by exact_mod_cast hq.ne_zero)
  letI : p.IsMaximal := Ring.HasFiniteQuotients.maximalOfPrime hp
  have hP : P ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot hp P
  letI : P.IsMaximal := Ring.DimensionLEOne.maximalOfPrime hP inferInstance
  letI : Field (ℤ ⧸ p) := Ideal.Quotient.field p
  letI : Field (NumberField.RingOfIntegers L ⧸ P) :=
    Ideal.Quotient.field P
  letI : Finite (ℤ ⧸ p) := Ring.HasFiniteQuotients.finiteQuotient hp
  letI : Fintype (ℤ ⧸ p) := Fintype.ofFinite _
  letI : Finite (NumberField.RingOfIntegers L ⧸ P) := inferInstance
  letI : Fintype (NumberField.RingOfIntegers L ⧸ P) := Fintype.ofFinite _
  letI : Finite Gal(L/ℚ) := IsGaloisGroup.finite Gal(L/ℚ) ℚ L
  letI : IsGaloisGroup Gal(L/ℚ) ℤ (NumberField.RingOfIntegers L) :=
    IsGaloisGroup.of_isFractionRing
      Gal(L/ℚ) ℤ (NumberField.RingOfIntegers L) ℚ L
  let D := MulAction.stabilizer Gal(L/ℚ) P
  let I := (P.inertia Gal(L/ℚ)).subgroupOf D
  let sigmaD : D :=
    ⟨sigma,
      arith_frob_decomposition P sigma hsigma⟩
  let e : D ⧸ I ≃*
      Gal((NumberField.RingOfIntegers L ⧸ P)/(ℤ ⧸ p)) :=
    Ideal.Quotient.stabilizerQuotientInertiaEquiv Gal(L/ℚ) p P
  let frob : Gal((NumberField.RingOfIntegers L ⧸ P)/(ℤ ⧸ p)) :=
    FiniteField.frobeniusAlgEquivOfAlgebraic
      (ℤ ⧸ p) (NumberField.RingOfIntegers L ⧸ P)
  have heq : e (QuotientGroup.mk' I sigmaD) = frob := by
    apply AlgEquiv.ext
    rintro ⟨x⟩
    change Ideal.Quotient.mk P (sigma • x) = frob (Ideal.Quotient.mk P x)
    change Ideal.Quotient.mk P (sigma • x) =
      Ideal.Quotient.mk P x ^ Fintype.card (ℤ ⧸ p)
    simpa [Nat.card_eq_fintype_card] using hsigma.mk_apply x
  have hfrobOrder : orderOf frob =
      Module.finrank (ℤ ⧸ p) (NumberField.RingOfIntegers L ⧸ P) :=
    FiniteField.orderOf_frobeniusAlgEquivOfAlgebraic
      (ℤ ⧸ p) (NumberField.RingOfIntegers L ⧸ P)
  have horder : orderOf (QuotientGroup.mk' I sigmaD) = Nat.card (D ⧸ I) := by
    calc
      orderOf (QuotientGroup.mk' I sigmaD) = orderOf frob := by
        rw [← e.orderOf_eq, heq]
      _ = Module.finrank (ℤ ⧸ p)
          (NumberField.RingOfIntegers L ⧸ P) := hfrobOrder
      _ = Nat.card
          Gal((NumberField.RingOfIntegers L ⧸ P)/(ℤ ⧸ p)) := by
        rw [IsGalois.card_aut_eq_finrank]
      _ = Nat.card (D ⧸ I) := Nat.card_congr e.symm.toEquiv
  apply Subgroup.eq_top_of_card_eq
  rw [Nat.card_zpowers, horder]

/-- A specified tame inertia generator and a specified arithmetic Frobenius
generate the decomposition subgroup. -/
theorem arith_frob_generate
    {L : Type*} [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    {q : ℕ} (hq : Nat.Prime q)
    (P : Ideal (NumberField.RingOfIntegers L)) [P.IsPrime]
    [P.LiesOver (Ideal.rationalPrimeIdeal q)]
    (tau : P.inertia Gal(L/ℚ))
    (htau : Subgroup.closure ({tau} : Set (P.inertia Gal(L/ℚ))) = ⊤)
    (sigma : Gal(L/ℚ))
    (hsigma : IsArithFrobAt ℤ sigma P) :
    Subgroup.closure ({(tau : Gal(L/ℚ)), sigma} : Set Gal(L/ℚ)) =
      MulAction.stabilizer Gal(L/ℚ) P := by
  let D := MulAction.stabilizer Gal(L/ℚ) P
  let I := (P.inertia Gal(L/ℚ)).subgroupOf D
  let tauD : D := ⟨tau, Ideal.inertia_le_stabilizer P tau.property⟩
  let tauI : I := ⟨tauD, tau.property⟩
  let sigmaD : D :=
    ⟨sigma,
      arith_frob_decomposition P sigma hsigma⟩
  let eI : I ≃* P.inertia Gal(L/ℚ) :=
    Subgroup.subgroupOfEquivOfLe (Ideal.inertia_le_stabilizer P)
  have hetau : eI tauI = tau := rfl
  have htauZ : Subgroup.zpowers tau = ⊤ :=
    (Subgroup.zpowers_eq_closure tau).trans htau
  have htauIZ : Subgroup.zpowers tauI = ⊤ := by
    apply top_unique
    intro x _
    have hex : eI x ∈ Subgroup.zpowers tau := by
      rw [htauZ]
      exact Subgroup.mem_top _
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hex
    apply Subgroup.mem_zpowers_iff.mpr
    refine ⟨n, ?_⟩
    apply eI.injective
    rw [map_zpow, hetau]
    exact hn
  have hsigmaZ : Subgroup.zpowers (QuotientGroup.mk' I sigmaD) = ⊤ :=
    arith_frob_generates hq P sigma hsigma
  simpa [D, I, tauI, tauD, sigmaD] using
    (closure_pair_cyclic
      D I tauI sigmaD htauIZ hsigmaZ)

end

end TBluepr
end Towers
