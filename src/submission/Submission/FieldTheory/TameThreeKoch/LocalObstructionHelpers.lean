import Submission.FieldTheory.TameThreeKoch.PrimitiveRootBrauer


open scoped Pointwise Topology commutatorElement

noncomputable section

namespace Submission
namespace TBluepr

universe u v

open NumberField
open Submission.NumberTheory.Milne
open Submission.CField.LBrauer

attribute [local instance]
  part2FiniteGaloisIntermediateFieldFiniteDimensional
  part2FiniteGaloisIntermediateFieldIsGalois
  part2AlgebraicClosureAlgebraic
  part2AlgebraicClosureNormal
  algebraicClosureIsGalois

/-!
# Helpers for the finite local obstruction calculation

These lemmas isolate reusable algebraic, ideal-theoretic, and finite-field
steps from the ramified-prime local obstruction proof.
-/

theorem obstruction_stabilizer_bot
    {K : Type} [Field K] [Algebra ℚ K] [NumberField K]
    [FiniteDimensional ℚ K] [IsGalois ℚ K] [Normal ℚ K]
    (e : rationalCubeField ≃ₐ[ℚ] K)
    (P : IsDedekindDomain.HeightOneSpectrum
      (NumberField.RingOfIntegers K))
    (hbot : MulAction.stabilizer Gal(rationalCubeField/ℚ)
      (P.asIdeal.comap (NumberField.RingOfIntegers.mapAlgEquiv e)) = ⊥) :
    MulAction.stabilizer Gal(K/ℚ) P.asIdeal = ⊥ := by
  let eO := NumberField.RingOfIntegers.mapAlgEquiv e
  let Pc : Ideal (NumberField.RingOfIntegers rationalCubeField) :=
    P.asIdeal.comap eO
  have hPcmap : Pc.map eO = P.asIdeal := by
    exact Ideal.map_comap_eq_self_of_equiv eO P.asIdeal
  apply (Subgroup.eq_bot_iff_forall _).2
  intro sigma hsigma
  let sigmaC : Gal(rationalCubeField/ℚ) :=
    (AlgEquiv.autCongr e).symm sigma
  have hmapAction := ideal_alg_smul e sigmaC Pc
  have hmapEq : (sigmaC • Pc).map eO = Pc.map eO := by
    change (sigmaC • Pc).map
        (NumberField.RingOfIntegers.mapRingEquiv e.toRingEquiv) =
      Pc.map (NumberField.RingOfIntegers.mapRingEquiv e.toRingEquiv)
    rw [hmapAction]
    have hsigmaCongr : (AlgEquiv.autCongr e) sigmaC = sigma := by
      exact (AlgEquiv.autCongr e).apply_symm_apply sigma
    rw [hsigmaCongr]
    change sigma • Pc.map eO = Pc.map eO
    rw [hPcmap]
    exact MulAction.mem_stabilizer_iff.mp hsigma
  have hker : RingHom.ker eO.toRingHom = ⊥ := by
    apply Ideal.ext
    intro x
    simp
  have hsigmaC : sigmaC • Pc = Pc := by
    have hsup :=
      (Ideal.map_eq_iff_sup_ker_eq_of_surjective eO.toRingHom
        eO.surjective).mp hmapEq
    simpa [hker] using hsup
  have hsigmaCone : sigmaC = 1 := by
    have hm : sigmaC ∈ MulAction.stabilizer
        Gal(rationalCubeField/ℚ) Pc :=
      MulAction.mem_stabilizer_iff.mpr hsigmaC
    rw [show MulAction.stabilizer Gal(rationalCubeField/ℚ) Pc = ⊥
      from hbot] at hm
    exact hm
  calc
    sigma = (AlgEquiv.autCongr e) sigmaC := by
      exact ((AlgEquiv.autCongr e).apply_symm_apply sigma).symm
    _ = (AlgEquiv.autCongr e) 1 := by rw [hsigmaCone]
    _ = 1 := map_one (AlgEquiv.autCongr e)

theorem obstruction_dvd_projection
    {G H : Type*} [Group G] [Finite G] [Group H]
    (p : G →* H) (hcentral : p.ker ≤ Subgroup.center G)
    (x y : G) (r f : ℕ) (k : ℤ)
    (hr : 0 < r) (hconj : y * x * y⁻¹ = x ^ r)
    (hprojection : p (y ^ f) = p (x ^ k)) :
    orderOf x ∣ r ^ f - 1 := by
  let c := y ^ f * (x ^ k)⁻¹
  have hc : c ∈ p.ker := by
    rw [MonoidHom.mem_ker]
    dsimp only [c]
    rw [map_mul, map_inv, hprojection]
    group
  have hcComm : c * x = x * c := by
    exact (Subgroup.mem_center_iff.mp (hcentral hc) x).symm
  have hyPowComm : y ^ f * x = x * y ^ f := by
    dsimp only [c] at hcComm
    apply mul_right_cancel (b := x ^ k)
    calc
      (y ^ f * x) * x ^ k =
          (y ^ f * (x ^ k)⁻¹) * x * (x ^ k * x ^ k) := by
        group
      _ = x * (y ^ f * (x ^ k)⁻¹) * (x ^ k * x ^ k) := by
        rw [hcComm]
      _ = (x * y ^ f) * x ^ k := by
        group
  have hyConjTrivial : y ^ f * x * (y ^ f)⁻¹ = x := by
    rw [hyPowComm]
    group
  have hxPowEq : x ^ (r ^ f) = x := by
    rw [← tame_conjugation_pow x y r f hconj]
    exact hyConjTrivial
  have hrPowPos : 0 < r ^ f := pow_pos hr f
  have hxPowSub : x ^ (r ^ f - 1) = 1 := by
    apply mul_right_cancel (b := x)
    calc
      x ^ (r ^ f - 1) * x = x ^ (r ^ f) := by
        rw [← pow_succ, Nat.sub_add_cancel hrPowPos]
      _ = x := hxPowEq
      _ = 1 * x := by rw [one_mul]
  exact (orderOf_dvd_iff_pow_eq_one).2 hxPowSub

theorem obstruction_zmod_generator
    {G : Type*} [Group G] (I : Subgroup G) (n : ℕ) [NeZero n]
    (e : Multiplicative (ZMod n) ≃* I) :
    orderOf ((e CyclicH2.generator : I) : G) = n := by
  calc
    orderOf ((e CyclicH2.generator : I) : G) =
        orderOf (e CyclicH2.generator) := Subgroup.orderOf_coe _
    _ = orderOf CyclicH2.generator := e.orderOf_eq _
    _ = addOrderOf (1 : ZMod n) := by rfl
    _ = n := ZMod.addOrderOf_one n

theorem obstruction_abs_deg
    {K : Type*} [Field K] [NumberField K]
    (P : IsDedekindDomain.HeightOneSpectrum
      (NumberField.RingOfIntegers K))
    (r : ℕ) (hr : Nat.Prime r)
    (hPover : P.asIdeal.LiesOver (Ideal.rationalPrimeIdeal r))
    (hinertia : (Ideal.rationalPrimeIdeal r).inertiaDeg P.asIdeal = 1) :
    Ideal.absNorm P.asIdeal = r := by
  letI : P.asIdeal.LiesOver (Ideal.span ({(r : ℤ)} : Set ℤ)) := by
    simpa [Ideal.rationalPrimeIdeal] using hPover
  have hinertiaSpan :
      (Ideal.span ({(r : ℤ)} : Set ℤ)).inertiaDeg P.asIdeal = 1 := by
    simpa [Ideal.rationalPrimeIdeal] using hinertia
  rw [Ideal.absNorm_eq_pow_inertiaDeg' P.asIdeal hr, hinertiaSpan, pow_one]

theorem obstruction_abs_norm
    {K : Type*} [Field K] [NumberField K]
    (P : Ideal (NumberField.RingOfIntegers K)) (r : ℕ)
    (hP : Ideal.absNorm P = r) :
    Nat.card (NumberField.RingOfIntegers K ⧸ P) = r := by
  rw [← Submodule.cardQuot_apply, ← Ideal.absNorm_apply, hP]

theorem obstruction_int_prime
    {K : Type*} [Field K] [NumberField K]
    (P : Ideal (NumberField.RingOfIntegers K)) (r : ℕ)
    (hunder : P.under ℤ = Ideal.rationalPrimeIdeal r) :
    Nat.card (ℤ ⧸ P.under ℤ) = r := by
  rw [hunder, ← Submodule.cardQuot_apply, ← Ideal.absNorm_apply,
    abs_rational_ideal]

theorem obstruction_stabilizer_top
    (G B : Type*) [Group G] [CommRing B] [IsLocalRing B]
    [MulSemiringAction G B] :
    MulAction.stabilizer G (IsLocalRing.maximalIdeal B) = ⊤ := by
  apply top_unique
  intro sigma _
  rw [MulAction.mem_stabilizer_iff]
  let esigma : B ≃+* B := MulSemiringAction.toRingAut _ _ sigma
  exact IsLocalRing.map_ringEquiv_maximalIdeal esigma

theorem obstruction_zpowers_card
    {G : Type*} [Group G] [Finite G] (g : G)
    (horder : orderOf g = Nat.card G) :
    Subgroup.zpowers g = ⊤ := by
  apply Subgroup.eq_top_of_card_eq
  rw [Nat.card_zpowers, horder]

theorem obstruction_frobenius_card
    {k K Q : Type*} [Field k] [Field K] [Fintype k] [Finite K]
    [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    [Group Q] [Finite Q]
    (e : Q ≃* Gal(K/k)) (sigma : Q)
    (hsigma : e sigma =
      FiniteField.frobeniusAlgEquivOfAlgebraic k K) :
    orderOf sigma = Nat.card Q := by
  calc
    orderOf sigma = orderOf
        (FiniteField.frobeniusAlgEquivOfAlgebraic k K) := by
      rw [← e.orderOf_eq, hsigma]
    _ = Module.finrank k K :=
      FiniteField.orderOf_frobeniusAlgEquivOfAlgebraic k K
    _ = Nat.card Gal(K/k) := by
      rw [IsGalois.card_aut_eq_finrank]
    _ = Nat.card Q := Nat.card_congr e.symm.toEquiv

theorem obstruction_nat_galois
    {k K Q : Type*} [Field k] [Field K] [Finite k] [Finite K]
    [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    [Group Q] [Finite Q] (e : Q ≃* Gal(K/k)) :
    Nat.card K = Nat.card k ^ Nat.card Q := by
  letI := Fintype.ofFinite k
  letI := Fintype.ofFinite K
  calc
    Nat.card K = Nat.card k ^ Module.finrank k K := by
      simpa only [Nat.card_eq_fintype_card] using
        (Module.card_eq_pow_finrank (K := k) (V := K))
    _ = Nat.card k ^ Nat.card Gal(K/k) := by
      rw [IsGalois.card_aut_eq_finrank]
    _ = Nat.card k ^ Nat.card Q := by
      rw [Nat.card_congr e.symm.toEquiv]

theorem obstruction_coprime_sub
    (r f : ℕ) (hr : r ≠ 0) :
    (r ^ f).Coprime (r ^ f - 1) := by
  exact (Nat.coprime_self_sub_right
    (Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ hr))).2
      (Nat.coprime_one_right _)

end TBluepr
end Submission
