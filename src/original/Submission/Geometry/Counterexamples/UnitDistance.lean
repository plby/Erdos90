import Submission.Geometry.LatticeAveraging


open Filter
open scoped Pointwise EuclideanGeometry Topology

noncomputable section

open NumberField
open Ideal

namespace Submission

/-- We model the Euclidean plane as `ℂ`. -/
abbrev Point : Type :=
  ℂ

/-- Two points of the plane are at unit distance when their Euclidean distance is `1`. -/
def IsUnitDistance (z w : Point) : Prop :=
  dist z w = 1

/-- The oriented unit-distance edges determined by a finite planar point set. -/
def orientedUnitEdges (P : Finset Point) : Finset (Point × Point) :=
  by
    classical
    exact P.offDiag.filter fun e ↦ IsUnitDistance e.1 e.2

/--
Given a finite set of points, this function counts the number of **unordered pairs** of distinct
points that are at a distance of exactly `1` from each other.
-/
def distancePairsCount (P : Finset Point) : ℕ :=
  (P.offDiag.filter fun p => dist p.1 p.2 = 1).card / 2

structure DistancePointData (d : ℕ → ℕ) (CX A B : ℝ) where
  P : ℕ → Finset Point
  lower : ∀ j : ℕ, CX ^ d j ≤ ((P j).card : ℝ)
  upper : ∀ j : ℕ, ((P j).card : ℝ) ≤ A ^ d j
  edges : ∀ j : ℕ, B ^ d j / 2 ≤ (distancePairsCount (P j) : ℝ)

structure DistanceTowerConstruction (T : SplitTotallyTower.{0}) where
  d : ℕ → ℕ
  CX : ℝ
  A : ℝ
  B : ℝ
  hd : d = fun j => Module.finrank ℚ (T.fields j)
  hCX_gt : 1 < CX
  hA_gt : 1 < A
  hBA : A < B
  pointData : DistancePointData d CX A B

/--
The scalar parameters chosen in the proof of the main theorem for a fixed tower:
the root-discriminant/class-number constants, the finite split-prime set, the
auxiliary integer `q`, and the geometric constants `C_U, R, C_X, A, B`.
-/
structure DistanceGrowthData (T : SplitTotallyTower.{0}) where
  ρ : ℝ
  H : ℝ
  S : Finset ℕ
  q : ℕ
  CU : ℝ
  R : ℝ
  CX : ℝ
  A : ℝ
  B : ℝ
  hρ : 0 < ρ
  hρ_ge : 1 ≤ ρ
  hρ_cm : ∀ j : ℕ, 2 * rootDiscriminant (T.fields j) ≤ ρ
  hpi_two_rho : Real.pi < 2 * ρ
  hH : 1 < H
  hH_def : H = classNumberBound ρ
  hS_split : ∀ p ∈ S, p ∈ T.splitPrimes
  hCU_def : CU = ((2 : ℝ) ^ S.card) / H
  hCU_growth : 1 < CU * (Real.pi / (2 * ρ))
  hq_def : q = (S.prod fun p => p) ^ 2
  hq_pos : 0 < q
  hR_gt : 1 < R
  hCX_def : CX = 2 * Real.pi * (R - 1) ^ (2 : ℕ) * (q : ℝ) ^ (2 : ℕ) / ρ
  hA_def : A = (1 + 2 * R * (q : ℝ)) ^ (2 : ℕ)
  hB_def : B = CU * CX
  hCX_gt : 1 < CX
  h_cx : CX < A
  hA_gt : 1 < A
  hBA : A < B

/-- Membership in the scaled module `q⁻¹ O_K`. -/
def ScaledRingIntegers
    (K : Type*) [Field K] [NumberField K] (q : ℕ) (x : K) : Prop :=
  ∃ a : NumberField.RingOfIntegers K,
    algebraMap (NumberField.RingOfIntegers K) K a = (q : K) * x

lemma scaled_integers_add
    {K : Type*} [Field K] [NumberField K] {q : ℕ} {x y : K}
    (hx : ScaledRingIntegers K q x) (hy : ScaledRingIntegers K q y) :
    ScaledRingIntegers K q (x + y) := by
  rcases hx with ⟨ax, hax⟩
  rcases hy with ⟨ay, hay⟩
  refine ⟨ax + ay, ?_⟩
  rw [map_add, hax, hay]
  ring

lemma distance_rho_tower
    (T : SplitTotallyTower.{0}) :
    ∃ ρ H : ℝ,
      0 < ρ ∧ 1 ≤ ρ ∧
      (∀ j : ℕ, 2 * rootDiscriminant (T.fields j) ≤ ρ) ∧
      Real.pi < 2 * ρ ∧
      H = classNumberBound ρ ∧ 1 < H := by
  rcases T.rootDiscriminant_bounded with ⟨ρ0, hρ0⟩
  let ρF : ℝ := max 1 ρ0
  let ρ : ℝ := 2 * ρF
  let H : ℝ := classNumberBound ρ
  have hρ_ge : 1 ≤ ρ := by
    dsimp [ρ, ρF]
    have hρF_ge : 1 ≤ max 1 ρ0 := le_max_left _ _
    nlinarith
  have hρ : 0 < ρ := lt_of_lt_of_le zero_lt_one hρ_ge
  have hρ_cm : ∀ j : ℕ, 2 * rootDiscriminant (T.fields j) ≤ ρ := by
    intro j
    dsimp [ρ, ρF]
    have hj : rootDiscriminant (T.fields j) ≤ ρ0 := hρ0 j
    nlinarith [le_max_right 1 ρ0, hj]
  have hρ_two : 2 ≤ ρ := by
    dsimp [ρ, ρF]
    have hρF_ge : 1 ≤ max 1 ρ0 := le_max_left _ _
    nlinarith
  have hpi_two_rho : Real.pi < 2 * ρ := by
    have hpi_lt_four : Real.pi < 4 := Real.pi_lt_four
    nlinarith
  have hH : 1 < H := by
    dsimp [H]
    exact class_number_bound hρ_ge
  exact ⟨ρ, H, hρ, hρ_ge, hρ_cm, hpi_two_rho, rfl, hH⟩

lemma distance_split_set
    (splitPrimes : Set ℕ) (hsplit_inf : splitPrimes.Infinite)
    (H ρ : ℝ) (hH : 1 < H) (hρ : 0 < ρ) :
    ∃ S : Finset ℕ,
      (∀ p ∈ S, p ∈ splitPrimes) ∧
      1 < (((2 : ℝ) ^ S.card) / H) * (Real.pi / (2 * ρ)) := by
  let p : ℝ := Real.pi / (2 * ρ)
  have hp : 0 < p := by
    dsimp [p]
    positivity
  have hH_pos : 0 < H := by
    linarith
  have hpow_tendsto : Tendsto (fun n : ℕ ↦ (2 : ℝ) ^ n) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  have hpow_eventually : ∀ᶠ n : ℕ in atTop, H / p + 1 ≤ (2 : ℝ) ^ n :=
    (Filter.tendsto_atTop.mp hpow_tendsto) (H / p + 1)
  rcases Filter.mem_atTop_sets.mp hpow_eventually with ⟨N, hN⟩
  rcases hsplit_inf.exists_subset_card_eq N with ⟨S, hS_subset, hScard⟩
  refine ⟨S, ?_, ?_⟩
  · intro q hq
    exact hS_subset (by simpa using hq)
  · have hNbound : H / p + 1 ≤ (2 : ℝ) ^ N := hN N le_rfl
    have hHp_lt : H / p < (2 : ℝ) ^ N := by
      linarith
    have hHp_mul : H < (2 : ℝ) ^ N * p := by
      rwa [div_lt_iff₀ hp] at hHp_lt
    have hmain : 1 < (((2 : ℝ) ^ N) * p) / H := by
      rw [one_lt_div hH_pos]
      exact hHp_mul
    simpa [p, hScard, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hmain

lemma unit_distance_radius
    (CU ρ : ℝ) (q : ℕ)
    (hρ : 0 < ρ) (hq : 0 < q)
    (hpi_two_rho : Real.pi < 2 * ρ)
    (hCU_growth : 1 < CU * (Real.pi / (2 * ρ))) :
    ∃ R : ℝ,
      1 < R ∧
      1 < (2 * Real.pi * (R - 1) ^ (2 : ℕ) * (q : ℝ) ^ (2 : ℕ) / ρ) ∧
        (2 * Real.pi * (R - 1) ^ (2 : ℕ) * (q : ℝ) ^ (2 : ℕ) / ρ) <
        (1 + 2 * R * (q : ℝ)) ^ (2 : ℕ) ∧
        1 < (1 + 2 * R * (q : ℝ)) ^ (2 : ℕ) ∧
        (1 + 2 * R * (q : ℝ)) ^ (2 : ℕ) <
        CU * (2 * Real.pi * (R - 1) ^ (2 : ℕ) * (q : ℝ) ^ (2 : ℕ) / ρ) := by
  let qr : ℝ := q
  have hqr : 0 < qr := by
    dsimp [qr]
    exact_mod_cast hq
  let K : ℝ := CU * (2 * Real.pi * qr ^ (2 : ℕ) / ρ)
  have hK_gt : 4 * qr ^ (2 : ℕ) < K := by
    dsimp [K]
    have hmul :=
      mul_lt_mul_of_pos_right hCU_growth (by positivity : 0 < 4 * qr ^ (2 : ℕ))
    have hleft :
        (4 * qr ^ (2 : ℕ) : ℝ) * 1 <
          (4 * qr ^ (2 : ℕ)) * (CU * (Real.pi / (2 * ρ))) :=
      by simpa [mul_assoc, mul_left_comm, mul_comm] using hmul
    have hrewrite :
        (4 * qr ^ (2 : ℕ) : ℝ) * (CU * (Real.pi / (2 * ρ))) =
          CU * (2 * Real.pi * qr ^ (2 : ℕ) / ρ) := by
      field_simp [hρ.ne']
      ring
    simpa [hrewrite] using hleft
  have hK_pos : 0 < K := by
    have hfourpos : 0 < 4 * qr ^ (2 : ℕ) := by
      positivity
    linarith
  let δ : ℝ := K - 4 * qr ^ (2 : ℕ)
  have hδ : 0 < δ := by
    dsimp [δ]
    linarith
  let M : ℝ := max (2 + ρ / (2 * Real.pi * qr ^ (2 : ℕ)))
    (max (4 * (K + 2 * qr) / δ) (2 / δ))
  rcases exists_nat_gt M with ⟨N, hN⟩
  refine ⟨N, ?_, ?_, ?_, ?_, ?_⟩
  · have hN_lower : 2 + ρ / (2 * Real.pi * qr ^ (2 : ℕ)) < (N : ℝ) := by
      have hM_le : 2 + ρ / (2 * Real.pi * qr ^ (2 : ℕ)) ≤ M := by
        dsimp [M]
        exact le_max_left _ _
      linarith
    have hfrac_pos : 0 < ρ / (2 * Real.pi * qr ^ (2 : ℕ)) := by
      positivity
    linarith
  · have hN_lower : 2 + ρ / (2 * Real.pi * qr ^ (2 : ℕ)) < (N : ℝ) := by
      have hM_le : 2 + ρ / (2 * Real.pi * qr ^ (2 : ℕ)) ≤ M := by
        dsimp [M]
        exact le_max_left _ _
      linarith
    have hNm1_gt : ρ / (2 * Real.pi * qr ^ (2 : ℕ)) < (N : ℝ) - 1 := by
      linarith
    have hNm1_gt_one : 1 < (N : ℝ) - 1 := by
      have hfrac_pos : 0 < ρ / (2 * Real.pi * qr ^ (2 : ℕ)) := by
        positivity
      linarith
    have hsq_gt :
        ρ / (2 * Real.pi * qr ^ (2 : ℕ)) < ((N : ℝ) - 1) ^ (2 : ℕ) := by
      have hlt2 : (N : ℝ) - 1 < ((N : ℝ) - 1) ^ (2 : ℕ) := by
        nlinarith
      exact lt_trans hNm1_gt hlt2
    have hmul :
        ρ < 2 * Real.pi * ((N : ℝ) - 1) ^ (2 : ℕ) * qr ^ (2 : ℕ) := by
      have hpos : 0 < 2 * Real.pi * qr ^ (2 : ℕ) := by
        positivity
      rw [div_lt_iff₀ hpos] at hsq_gt
      simpa [mul_assoc, mul_left_comm, mul_comm] using hsq_gt
    rw [one_lt_div hρ]
    simpa [qr, mul_assoc, mul_left_comm, mul_comm] using hmul
  · have hN_lower : 2 + ρ / (2 * Real.pi * qr ^ (2 : ℕ)) < (N : ℝ) := by
      have hM_le : 2 + ρ / (2 * Real.pi * qr ^ (2 : ℕ)) ≤ M := by
        dsimp [M]
        exact le_max_left _ _
      linarith
    have hNm1_pos : 0 < (N : ℝ) - 1 := by
      have hfrac_pos : 0 < ρ / (2 * Real.pi * qr ^ (2 : ℕ)) := by
        positivity
      linarith
    have hshift_lt : 2 * ((N : ℝ) - 1) * qr < 1 + 2 * (N : ℝ) * qr := by
      linarith
    have hcore_lt :
        4 * ((N : ℝ) - 1) ^ (2 : ℕ) * qr ^ (2 : ℕ) <
          (1 + 2 * (N : ℝ) * qr) ^ (2 : ℕ) := by
      have hsq :
          (2 * ((N : ℝ) - 1) * qr) ^ (2 : ℕ) <
            (1 + 2 * (N : ℝ) * qr) ^ (2 : ℕ) := by
        nlinarith
      have hcore_eq :
          (2 * ((N : ℝ) - 1) * qr) ^ (2 : ℕ) =
            4 * ((N : ℝ) - 1) ^ (2 : ℕ) * qr ^ (2 : ℕ) := by
        ring
      rw [hcore_eq] at hsq
      exact hsq
    have hfactor_lt_one : Real.pi / (2 * ρ) < 1 := by
      have hden : 0 < 2 * ρ := by positivity
      rw [div_lt_iff₀ hden]
      linarith
    have hcore_pos : 0 < 4 * ((N : ℝ) - 1) ^ (2 : ℕ) * qr ^ (2 : ℕ) := by
      positivity
    have hscaled_lt :
        (Real.pi / (2 * ρ)) * (4 * ((N : ℝ) - 1) ^ (2 : ℕ) * qr ^ (2 : ℕ)) <
          1 * (4 * ((N : ℝ) - 1) ^ (2 : ℕ) * qr ^ (2 : ℕ)) := by
      nlinarith
    have hrewrite :
        2 * Real.pi * ((N : ℝ) - 1) ^ (2 : ℕ) * qr ^ (2 : ℕ) / ρ =
          (Real.pi / (2 * ρ)) * (4 * ((N : ℝ) - 1) ^ (2 : ℕ) * qr ^ (2 : ℕ)) := by
      field_simp [hρ.ne']
      ring
    rw [hrewrite]
    exact lt_trans hscaled_lt (by simpa using hcore_lt)
  · have hN_lower : 2 + ρ / (2 * Real.pi * qr ^ (2 : ℕ)) < (N : ℝ) := by
      have hM_le : 2 + ρ / (2 * Real.pi * qr ^ (2 : ℕ)) ≤ M := by
        dsimp [M]
        exact le_max_left _ _
      linarith
    have hfrac_pos : 0 < ρ / (2 * Real.pi * qr ^ (2 : ℕ)) := by
      positivity
    have hN_gt_two : 2 < (N : ℝ) := by
      linarith
    have hqR_pos : 0 < 2 * (N : ℝ) * qr := by
      positivity
    have hbase : 1 < 1 + 2 * (N : ℝ) * qr := by
      linarith
    have hsq : 1 < (1 + 2 * (N : ℝ) * qr) * (1 + 2 * (N : ℝ) * qr) := by
      nlinarith [hbase]
    simpa [pow_two] using hsq
  · have hR_big : max (4 * (K + 2 * qr) / δ) (2 / δ) < (N : ℝ) := by
      have hM_le : max (4 * (K + 2 * qr) / δ) (2 / δ) ≤ M := by
        dsimp [M]
        exact le_max_right _ _
      linarith
    have hN_lower : 2 + ρ / (2 * Real.pi * qr ^ (2 : ℕ)) < (N : ℝ) := by
      have hM_le : 2 + ρ / (2 * Real.pi * qr ^ (2 : ℕ)) ≤ M := by
        dsimp [M]
        exact le_max_left _ _
      linarith
    have hfrac_pos : 0 < ρ / (2 * Real.pi * qr ^ (2 : ℕ)) := by
      positivity
    have hN_gt_two : 2 < (N : ℝ) := by
      linarith
    have hR_big1 : 4 * (K + 2 * qr) / δ < (N : ℝ) := by
      have : 4 * (K + 2 * qr) / δ ≤ max (4 * (K + 2 * qr) / δ) (2 / δ) := le_max_left _ _
      linarith
    have hR_big2 : 2 / δ < (N : ℝ) := by
      have : 2 / δ ≤ max (4 * (K + 2 * qr) / δ) (2 / δ) := le_max_right _ _
      linarith
    have hdeltaR : 2 < δ * (N : ℝ) := by
      have hdeltaR' : 2 < (N : ℝ) * δ := by
        rwa [div_lt_iff₀ hδ] at hR_big2
      simpa [mul_comm] using hdeltaR'
    have hlin : 2 * (K + 2 * qr) < δ * (N : ℝ) / 2 := by
      have htmp' : 4 * (K + 2 * qr) < (N : ℝ) * δ := by
        rwa [div_lt_iff₀ hδ] at hR_big1
      have htmp : 4 * (K + 2 * qr) < δ * (N : ℝ) := by
        simpa [mul_comm] using htmp'
      linarith
    have hquad :
        0 < δ * (N : ℝ) ^ (2 : ℕ) - 2 * (K + 2 * qr) * (N : ℝ) - 1 := by
      have hN_pos : 0 < (N : ℝ) := by
        linarith
      have hdelta_half : 1 < δ * (N : ℝ) / 2 := by
        linarith
      have hquad_left : 1 < δ * (N : ℝ) ^ (2 : ℕ) / 2 := by
        have hmul :
            (N : ℝ) * 1 < (N : ℝ) * (δ * (N : ℝ) / 2) := by
          exact mul_lt_mul_of_pos_left hdelta_half hN_pos
        have hEq : (N : ℝ) * (δ * (N : ℝ) / 2) = δ * (N : ℝ) ^ (2 : ℕ) / 2 := by
          ring
        have hmul' : (N : ℝ) < δ * (N : ℝ) ^ (2 : ℕ) / 2 := by
          simpa [one_mul, hEq] using hmul
        linarith
      have hquad_right : 2 * (K + 2 * qr) * (N : ℝ) < δ * (N : ℝ) ^ (2 : ℕ) / 2 := by
        have hmul := mul_lt_mul_of_pos_right hlin hN_pos
        simpa [pow_two, mul_assoc, mul_left_comm, mul_comm, div_eq_mul_inv] using hmul
      linarith
    have hfinal :
        (1 + 2 * (N : ℝ) * qr) ^ (2 : ℕ) <
          K * ((N : ℝ) - 1) ^ (2 : ℕ) := by
      have hpoly :
          0 <
            (K * ((N : ℝ) - 1) ^ (2 : ℕ)) - (1 + 2 * (N : ℝ) * qr) ^ (2 : ℕ) := by
        have hEq :
            (K * ((N : ℝ) - 1) ^ (2 : ℕ)) - (1 + 2 * (N : ℝ) * qr) ^ (2 : ℕ) =
              δ * (N : ℝ) ^ (2 : ℕ) - 2 * (K + 2 * qr) * (N : ℝ) + (K - 1) := by
          dsimp [δ]
          ring
        rw [hEq]
        linarith [hK_pos, hquad]
      linarith
    simpa [K, qr, pow_two, mul_assoc, mul_left_comm, mul_comm, div_eq_mul_inv] using hfinal

lemma distance_scalar_tower
    (T : SplitTotallyTower.{0}) :
    Nonempty (DistanceGrowthData T) := by
  rcases distance_rho_tower T with
      ⟨ρ, H, hρ, hρ_ge, hρ_cm, hpi_two_rho, hH_def, hH⟩
  rcases distance_split_set T.splitPrimes T.splitPrimes_infinite H ρ hH hρ with
      ⟨S, hS_split, hS_growth⟩
  let CU : ℝ := ((2 : ℝ) ^ S.card) / H
  have hCU_growth : 1 < CU * (Real.pi / (2 * ρ)) := by
    simpa [CU]
      using hS_growth
  let q : ℕ := (S.prod fun p => p) ^ 2
  have hprod_pos : 0 < S.prod fun p => p := by
    refine Finset.prod_pos ?_
    intro p hp
    rcases T.splitPrimes_spec (hS_split p hp) with ⟨hp_prime, -, -⟩
    exact hp_prime.pos
  have hq_pos : 0 < q := by
    dsimp [q]
    exact pow_pos hprod_pos 2
  rcases unit_distance_radius CU ρ q hρ hq_pos hpi_two_rho hCU_growth with
      ⟨R, hR_gt, hCX_gt_raw, hCX_lt_A_raw, hA_gt_raw, hBA_raw⟩
  let CX : ℝ := 2 * Real.pi * (R - 1) ^ (2 : ℕ) * (q : ℝ) ^ (2 : ℕ) / ρ
  let A : ℝ := (1 + 2 * R * (q : ℝ)) ^ (2 : ℕ)
  let B : ℝ := CU * CX
  have hCX_gt : 1 < CX := by
    simpa [CX] using hCX_gt_raw
  have h_cx : CX < A := by
    simpa [CX, A] using hCX_lt_A_raw
  have hA_gt : 1 < A := by
    simpa [A] using hA_gt_raw
  have hBA : A < B := by
    simpa [A, B, CX] using hBA_raw
  exact ⟨{
    ρ := ρ
    H := H
    S := S
    q := q
    CU := CU
    R := R
    CX := CX
    A := A
    B := B
    hρ := hρ
    hρ_ge := hρ_ge
    hρ_cm := hρ_cm
    hpi_two_rho := hpi_two_rho
    hH := hH
    hH_def := hH_def
    hS_split := hS_split
    hCU_def := rfl
    hCU_growth := hCU_growth
    hq_def := rfl
    hq_pos := hq_pos
    hR_gt := hR_gt
    hCX_def := rfl
    hA_def := rfl
    hB_def := rfl
    hCX_gt := hCX_gt
    h_cx := h_cx
    hA_gt := hA_gt
    hBA := hBA
  }⟩

lemma distance_cu_pos
    {T : SplitTotallyTower.{0}} (data : DistanceGrowthData T) :
    0 < data.CU := by
  have hfactor : 0 < Real.pi / (2 * data.ρ) := by
    have hden : 0 < 2 * data.ρ := by
      nlinarith [data.hρ]
    exact div_pos Real.pi_pos hden
  have hmul_pos : 0 < data.CU * (Real.pi / (2 * data.ρ)) := by
    linarith [data.hCU_growth]
  by_contra hCU
  have hCU_nonpos : data.CU ≤ 0 := le_of_not_gt hCU
  have hmul_nonpos : data.CU * (Real.pi / (2 * data.ρ)) ≤ 0 := by
    nlinarith
  linarith

def cmIPoly (F : Type*) [Field F] : Polynomial F :=
  Polynomial.X ^ 2 + 1

def cmAdjoinI (F : Type*) [Field F] [NumberField F] :
    NumberField.InfinitePlace F :=
  Classical.choice (inferInstance : Nonempty (NumberField.InfinitePlace F))

lemma distanceCMI
    (F : Type*) [Field F] [NumberField F] [NumberField.IsTotallyReal F] (x : F) :
    x ^ (2 : ℕ) ≠ (-1 : F) := by
  intro hx
  have hwreal :
      NumberField.ComplexEmbedding.IsReal (cmAdjoinI F).embedding := by
    exact (NumberField.InfinitePlace.isReal_iff).1
      (NumberField.IsTotallyReal.isReal (cmAdjoinI F))
  have hconj :
      NumberField.ComplexEmbedding.conjugate (cmAdjoinI F).embedding =
        (cmAdjoinI F).embedding := by
    exact (NumberField.ComplexEmbedding.isReal_iff).1 hwreal
  have hsq :
      ((cmAdjoinI F).embedding x) ^ (2 : ℕ) = (-1 : ℂ) := by
    simpa using congrArg (fun y : F => (cmAdjoinI F).embedding y) hx
  have hfixed :
      (starRingEnd ℂ) ((cmAdjoinI F).embedding x) =
        (cmAdjoinI F).embedding x := by
    simpa using congrArg (fun φ : F →+* ℂ => φ x) hconj
  rcases Complex.conj_eq_iff_real.1 hfixed with ⟨r, hr⟩
  have hr2c : ((r : ℂ) ^ (2 : ℕ)) = (-1 : ℂ) := by
    simpa [hr] using hsq
  have hr2 : r ^ (2 : ℕ) = (-1 : ℝ) := by
    exact_mod_cast hr2c
  nlinarith [sq_nonneg r]

lemma cm_i_irreducible
    (F : Type*) [Field F] [NumberField F] [NumberField.IsTotallyReal F] :
    Irreducible (cmIPoly F) := by
  have hmonic : (cmIPoly F).Monic := by
    dsimp [cmIPoly]
    simpa using
      (Polynomial.monic_X_pow_add (p := (1 : Polynomial F)) (n := 2) (by simp))
  have hfdeg : (cmIPoly F).natDegree = 2 := by
    simpa [cmIPoly] using
      (Polynomial.natDegree_X_pow_add_C (n := 2) (r := (1 : F)))
  have hf_ne_one : cmIPoly F ≠ 1 := by
    intro h1
    have : (cmIPoly F).natDegree = 0 := by
      simp [h1]
    omega
  refine (Polynomial.irreducible_of_monic hmonic hf_ne_one).2 ?_
  intro g h hg hh hmul
  by_contra htriv
  push Not at htriv
  have hg_pos : 0 < g.natDegree := (hg.natDegree_pos).2 htriv.1
  have hh_pos : 0 < h.natDegree := (hh.natDegree_pos).2 htriv.2
  have hsum : g.natDegree + h.natDegree = 2 := by
    rw [← hfdeg, ← hmul, Polynomial.Monic.natDegree_mul hg hh]
  have hlin : g.natDegree = 1 ∨ h.natDegree = 1 := by
    omega
  cases hlin with
  | inl hg1 =>
      rcases (Polynomial.natDegree_eq_one.1 hg1) with ⟨a, ha, b, rfl⟩
      have hroot :
          Polynomial.eval (-b / a)
              ((Polynomial.C a * Polynomial.X + Polynomial.C b) * h) = 0 := by
        rw [Polynomial.eval_mul]
        have hlinear :
            Polynomial.eval (-b / a)
                (Polynomial.C a * Polynomial.X + Polynomial.C b : Polynomial F) = 0 := by
          rw [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
            Polynomial.eval_X, Polynomial.eval_C]
          field_simp [ha]
          ring
        simp [hlinear]
      have hfroot : Polynomial.eval (-b / a) (cmIPoly F) = 0 := by
        rw [← hmul]
        exact hroot
      have hsquare : (-b / a : F) ^ (2 : ℕ) = (-1 : F) := by
        have hadd : (-b / a : F) ^ (2 : ℕ) + 1 = 0 := by
          simpa [cmIPoly, pow_two] using hfroot
        exact eq_neg_of_add_eq_zero_left hadd
      exact (distanceCMI F (-b / a)) hsquare
  | inr hh1 =>
      rcases (Polynomial.natDegree_eq_one.1 hh1) with ⟨a, ha, b, rfl⟩
      have hroot :
          Polynomial.eval (-b / a)
              (g * (Polynomial.C a * Polynomial.X + Polynomial.C b)) = 0 := by
        rw [Polynomial.eval_mul]
        have hlinear :
            Polynomial.eval (-b / a)
                (Polynomial.C a * Polynomial.X + Polynomial.C b : Polynomial F) = 0 := by
          rw [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
            Polynomial.eval_X, Polynomial.eval_C]
          field_simp [ha]
          ring
        simp [hlinear]
      have hfroot : Polynomial.eval (-b / a) (cmIPoly F) = 0 := by
        rw [← hmul]
        exact hroot
      have hsquare : (-b / a : F) ^ (2 : ℕ) = (-1 : F) := by
        have hadd : (-b / a : F) ^ (2 : ℕ) + 1 = 0 := by
          simpa [cmIPoly, pow_two] using hfroot
        exact eq_neg_of_add_eq_zero_left hadd
      exact (distanceCMI F (-b / a)) hsquare

lemma cmIConjugation
    {F : Type*} [Field F] [NumberField F] [NumberField.IsTotallyReal F]
    {K : Type*} [Field K]
    (ι : F →+* K) (ii : K)
    (hii : ii ^ (2 : ℕ) = (-1 : K))
    (hspan : ∀ z : K, ∃ a b : F, z = ι a + ι b * ii) :
    ∃ c : K ≃+* K,
      (∀ a : F, c (ι a) = ι a) ∧
      c ii = -ii ∧
      (∀ σ : K →+* ℂ, ∀ x : K, σ (c x) = star (σ x)) := by
  /-
  Paper step: `K = F(i)` carries the conjugation involution fixing `F` and
  sending `i` to `-i`; under every complex embedding this agrees with complex
  conjugation.
  -/
  classical
  have hcoeff_unique :
      ∀ {a b a' b' : F},
        ι a + ι b * ii = ι a' + ι b' * ii → a = a' ∧ b = b' := by
    intro a b a' b' hEq
    have hb : b = b' := by
      by_contra hbb
      have hden : ι (b' - b) ≠ 0 := by
        exact (map_ne_zero ι).2 (sub_ne_zero.mpr (by simpa [eq_comm] using hbb))
      have hsolve' : ii = (ι (a - a')) / ι (b' - b) := by
        apply (eq_div_iff hden).2
        calc
          ii * ι (b' - b) = ι (b' - b) * ii := by ring
          _ = ι a - ι a' := by
            calc
              ι (b' - b) * ii = (ι b' - ι b) * ii := by simp [map_sub]
              _ = (ι a' + ι b' * ii) - (ι a' + ι b * ii) := by ring
              _ = (ι a + ι b * ii) - (ι a' + ι b * ii) := by rw [hEq]
              _ = ι a - ι a' := by ring
          _ = ι (a - a') := by simp [map_sub]
      have hsolve : ii = ι ((a - a') / (b' - b)) := by
        simpa [map_sub, map_div] using hsolve'
      have hsquareK : ι (((a - a') / (b' - b)) ^ (2 : ℕ)) = ι (-1 : F) := by
        have hsquareK' : (ι ((a - a') / (b' - b))) ^ (2 : ℕ) = (-1 : K) := by
          simpa [hsolve] using hii
        simpa [map_pow, map_neg] using hsquareK'
      have hsquare : ((a - a') / (b' - b)) ^ (2 : ℕ) = (-1 : F) := by
        exact ι.injective hsquareK
      exact distanceCMI F _ hsquare
    have ha : a = a' := by
      have hsame : ι a + ι b * ii = ι a' + ι b * ii := by simpa [hb] using hEq
      apply ι.injective
      exact add_right_cancel hsame
    exact ⟨ha, hb⟩
  have hspanPair : ∀ z : K, ∃ ab : F × F, z = ι ab.1 + ι ab.2 * ii := by
    intro z
    rcases hspan z with ⟨a, b, hz⟩
    exact ⟨⟨a, b⟩, hz⟩
  let coeff : K → F × F := fun z => Classical.choose (hspanPair z)
  have hcoeff_spec : ∀ z : K, z = ι (coeff z).1 + ι (coeff z).2 * ii := by
    intro z
    exact Classical.choose_spec (hspanPair z)
  let cFun : K → K := fun z => ι (coeff z).1 - ι (coeff z).2 * ii
  have hc_repr : ∀ a b : F, cFun (ι a + ι b * ii) = ι a - ι b * ii := by
    intro a b
    dsimp [cFun]
    have hpair' : (coeff (ι a + ι b * ii)).1 = a ∧ (coeff (ι a + ι b * ii)).2 = b := by
      exact hcoeff_unique (by simpa using (hcoeff_spec (ι a + ι b * ii)).symm)
    rcases hpair' with ⟨ha, hb⟩
    simp [ha, hb]
  have hc_zero : cFun 0 = 0 := by
    have := hc_repr 0 0
    simpa using this
  have hc_one : cFun 1 = 1 := by
    have := hc_repr 1 0
    simpa using this
  have hc_add : ∀ x y : K, cFun (x + y) = cFun x + cFun y := by
    intro x y
    rcases hspan x with ⟨a, b, rfl⟩
    rcases hspan y with ⟨a', b', rfl⟩
    rw [show (ι a + ι b * ii) + (ι a' + ι b' * ii) =
        ι (a + a') + ι (b + b') * ii by
          simp [map_add]
          ring,
      hc_repr, hc_repr, hc_repr]
    simp [map_add]
    ring
  have hc_mul : ∀ x y : K, cFun (x * y) = cFun x * cFun y := by
    intro x y
    rcases hspan x with ⟨a, b, rfl⟩
    rcases hspan y with ⟨a', b', rfl⟩
    have hmul_left :
        (ι a + ι b * ii) * (ι a' + ι b' * ii) =
          ι (a * a' - b * b') + ι (a * b' + b * a') * ii := by
      have hii' : ii * ii = (-1 : K) := by simpa [pow_two] using hii
      calc
        (ι a + ι b * ii) * (ι a' + ι b' * ii)
            =
                ι a * ι a' +
                  (ι a * ι b' + ι b * ι a') * ii +
                    (ι b * ι b') * (ii * ii) := by
              ring
        _ = ι a * ι a' + (ι a * ι b' + ι b * ι a') * ii - (ι b * ι b') := by rw [hii']; ring
        _ = ι (a * a' - b * b') + ι (a * b' + b * a') * ii := by
          simp [map_add, map_mul, map_sub]
          ring
    have hmul_right :
        (ι a - ι b * ii) * (ι a' - ι b' * ii) =
          ι (a * a' - b * b') - ι (a * b' + b * a') * ii := by
      have hii' : ii * ii = (-1 : K) := by simpa [pow_two] using hii
      calc
        (ι a - ι b * ii) * (ι a' - ι b' * ii)
            =
                ι a * ι a' -
                  (ι a * ι b' + ι b * ι a') * ii +
                    (ι b * ι b') * (ii * ii) := by
              ring
        _ = ι a * ι a' - (ι a * ι b' + ι b * ι a') * ii - (ι b * ι b') := by rw [hii']; ring
        _ = ι (a * a' - b * b') - ι (a * b' + b * a') * ii := by
          simp [map_add, map_mul, map_sub]
          ring
    rw [hmul_left, hc_repr, hc_repr, hc_repr, hmul_right]
  have hc_involutive : ∀ x : K, cFun (cFun x) = x := by
    intro x
    rcases hspan x with ⟨a, b, rfl⟩
    have hneg_repr : ι a + -(ι b * ii) = ι a + ι (-b) * ii := by
      simp [map_neg]
    rw [hc_repr, sub_eq_add_neg, hneg_repr, hc_repr]
    simp
  let c : K ≃+* K :=
    RingEquiv.ofBijective
      ({ toFun := cFun
         map_zero' := hc_zero
         map_one' := hc_one
         map_add' := hc_add
         map_mul' := hc_mul } : K →+* K)
      (by
        refine ⟨RingHom.injective _, ?_⟩
        intro x
        exact ⟨cFun x, hc_involutive x⟩)
  refine ⟨c, ?_, ?_, ?_⟩
  · intro a
    change cFun (ι a) = ι a
    have := hc_repr a 0
    simpa using this
  · change cFun ii = -ii
    have := hc_repr 0 1
    simpa using this
  · intro σ x
    rcases hspan x with ⟨a, b, rfl⟩
    have hsigma_base : ∀ t : F, star (σ (ι t)) = σ (ι t) := by
      intro t
      have hreal_embedding : NumberField.ComplexEmbedding.IsReal (σ.comp ι) :=
        NumberField.IsTotallyReal.complexEmbedding_isReal (σ.comp ι)
      have hconj : NumberField.ComplexEmbedding.conjugate (σ.comp ι) = σ.comp ι :=
        (NumberField.ComplexEmbedding.isReal_iff).mp hreal_embedding
      simpa [NumberField.ComplexEmbedding.conjugate_coe_eq] using
        congrArg (fun τ : F →+* ℂ => τ t) hconj
    have hsigma_ii : star (σ ii) = -σ ii := by
      have hsquare : (σ ii) ^ (2 : ℕ) = (-1 : ℂ) := by
        simpa using congrArg σ hii
      have him : ((σ ii) ^ (2 : ℕ)).im = ((-1 : ℂ)).im := congrArg Complex.im hsquare
      have hre : ((σ ii) ^ (2 : ℕ)).re = ((-1 : ℂ)).re := congrArg Complex.re hsquare
      have him' : (σ ii).re * (σ ii).im + (σ ii).im * (σ ii).re = 0 := by
        simpa [pow_two, Complex.mul_re, Complex.mul_im] using him
      have hre' : (σ ii).re * (σ ii).re - (σ ii).im * (σ ii).im = -1 := by
        simpa [pow_two, Complex.mul_re, Complex.mul_im] using hre
      have hmul : (σ ii).re * (σ ii).im = 0 := by
        linarith
      have hre0_or_him0 : (σ ii).re = 0 ∨ (σ ii).im = 0 := mul_eq_zero.mp hmul
      have hre0 : (σ ii).re = 0 := by
        cases hre0_or_him0 with
        | inl h => exact h
        | inr h =>
            nlinarith [hre', sq_nonneg ((σ ii).re)]
      apply Complex.ext
      · simp [hre0]
      · simp
    change σ (cFun (ι a + ι b * ii)) = star (σ (ι a + ι b * ii))
    rw [hc_repr]
    simp [map_sub, map_add, map_mul, star_add, star_mul, hsigma_base, hsigma_ii]
    ring

/--
Integral arithmetic input for the CM extension `K = F(i)`: if a rational prime
`p ≡ 1 (mod 4)` splits completely in `F`, then it also splits completely in
`K`. This packages the paper's use of the fact that `X^2 + 1` splits modulo
such primes together with the integral control on `F(i) / F`.
-/
def cmIInput
    {F : Type*} [Field F] [NumberField F]
    {K : Type*} [Field K] [NumberField K]
    [Algebra F K] [IsScalarTower ℚ F K] : Prop :=
  ∀ {p : ℕ}, Nat.Prime p → p % 4 = 1 → splitsCompletely F p → splitsCompletely K p

lemma cm_i_base
    {F : Type*} [Field F] [NumberField F] [NumberField.IsTotallyReal F]
    {K : Type*} [Field K] [Algebra F K]
    (ii : K) (hii : ii ^ (2 : ℕ) = (-1 : K)) (a : F) :
    algebraMap F K a ≠ ii := by
  intro ha
  have hsquareK : algebraMap F K (a ^ (2 : ℕ)) = algebraMap F K (-1 : F) := by
    calc
      algebraMap F K (a ^ (2 : ℕ)) = (algebraMap F K a) ^ (2 : ℕ) := by simp
      _ = ii ^ (2 : ℕ) := by rw [ha]
      _ = (-1 : K) := hii
      _ = algebraMap F K (-1 : F) := by simp
  have hsquare : a ^ (2 : ℕ) = (-1 : F) := by
    exact (RingHom.injective (algebraMap F K)) hsquareK
  exact (distanceCMI F a) hsquare

/--
The explicit `F`-basis `1, i` for a field presented as `F(i)`.

We build this basis using the algebra structure induced by the chosen embedding
`ι : F →+* K`.
-/
noncomputable def cmIBasis
    {F : Type*} [Field F] [NumberField F] [NumberField.IsTotallyReal F]
    {K : Type*} [Field K] [Algebra F K]
    (ι : F →+* K) (hι : algebraMap F K = ι)
    (ii : K)
    (hii : ii ^ (2 : ℕ) = (-1 : K))
    (hspan : ∀ z : K, ∃ a b : F, z = ι a + ι b * ii) :
    Module.Basis (Fin 2) F K := by
  let v : Fin 2 → K := ![ii, (1 : K)]
  have hli : LinearIndependent F v := by
    refine (linearIndependent_fin2).2 ?_
    refine ⟨one_ne_zero, ?_⟩
    intro a
    simpa [v, hι, Algebra.smul_def] using
      cm_i_base (ii := ii) hii a
  have hsp : ⊤ ≤ Submodule.span F (Set.range v) := by
    intro z _
    rcases hspan z with ⟨a, b, rfl⟩
    have ha : a • v 1 ∈ Submodule.span F (Set.range v) :=
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨1, rfl⟩)
    have hb : b • v 0 ∈ Submodule.span F (Set.range v) :=
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩)
    simpa [v, hι, Algebra.smul_def, mul_comm, mul_left_comm, mul_assoc,
      add_comm, add_left_comm, add_assoc] using
      Submodule.add_mem (Submodule.span F (Set.range v)) hb ha
  exact Module.Basis.mk hli hsp

lemma level_cm_adjoin
    {F : Type*} [Field F] [NumberField F] [NumberField.IsTotallyReal F]
    {K : Type*} [Field K] [Algebra F K]
    (ι : F →+* K) (hι : algebraMap F K = ι)
    (ii : K)
    (hii : ii ^ (2 : ℕ) = (-1 : K))
    (hspan : ∀ z : K, ∃ a b : F, z = ι a + ι b * ii) :
    Module.finrank F K = 2 := by
  let b := cmIBasis
    (ι := ι) (hι := hι) (ii := ii) hii hspan
  simpa using (Module.finrank_eq_card_basis b)

lemma cm_i_extension
    {F : Type*} [Field F] [NumberField F] [NumberField.IsTotallyReal F]
    {K : Type*} [Field K] [Algebra F K]
    (ι : F →+* K) (hι : algebraMap F K = ι)
    (ii : K)
    (hii : ii ^ (2 : ℕ) = (-1 : K))
    (hspan : ∀ z : K, ∃ a b : F, z = ι a + ι b * ii) :
    Algebra.IsQuadraticExtension F K := by
  exact Algebra.IsQuadraticExtension.mk
    (level_cm_adjoin
      (ι := ι) (hι := hι) (ii := ii) hii hspan)

/--
Ramification and inertia step for the split-prime argument.

This isolates the local arithmetic input: once `p ≡ 1 (mod 4)` and the
relative discriminant is supported only at `2`, every prime of `K` above `p`
has ramification index and inertia degree equal to `1`.
-/
lemma level_cm_i
    {F : Type*} [Field F] [NumberField F] [NumberField.IsTotallyReal F]
    {K : Type*} [Field K] [NumberField K] [Algebra F K]
    (ι : F →+* K) (_hι : algebraMap F K = ι)
    (ii : K)
    (_hii : ii ^ (2 : ℕ) = (-1 : K))
    (_hspan : ∀ z : K, ∃ a b : F, z = ι a + ι b * ii)
    (hquadratic : Algebra.IsQuadraticExtension F K)
    {p : ℕ} (hp : Nat.Prime p) (_hp_mod : p % 4 = 1)
    (_hsplitF : splitsCompletely F p)
    {Q : Ideal (NumberField.RingOfIntegers F)}
    (hQ : Q ∈ Ideal.primesOver (rationalPrimeIdeal p) (NumberField.RingOfIntegers F)) :
    (Ideal.primesOver Q (NumberField.RingOfIntegers K)).ncard ≤ 2 := by
  letI : Algebra.IsQuadraticExtension F K := hquadratic
  have hp0 : rationalPrimeIdeal p ≠ (⊥ : Ideal ℤ) := by
    simp [rationalPrimeIdeal, hp.ne_zero]
  have hQ0 : Q ≠ ⊥ := Ideal.ne_bot_of_mem_primesOver hp0 hQ
  have hQmax : Q.IsMaximal := hQ.1.isMaximal hQ0
  letI : Q.IsPrime := hQ.1
  letI : Q.IsMaximal := hQmax
  letI : NoZeroSMulDivisors (NumberField.RingOfIntegers F)
      (NumberField.RingOfIntegers K) := by
    refine ⟨?_⟩
    intro c x hcx
    exact smul_eq_zero.mp hcx
  have hcard_le :
      (IsDedekindDomain.primesOverFinset Q (NumberField.RingOfIntegers K)).card ≤ Module.finrank
        F K := by
    simpa using
      (Ideal.card_primesOverFinset_le_finrank
        (p := Q) (S := NumberField.RingOfIntegers K) (K := F) (L := K) hQ0)
  have hs : (Ideal.primesOver Q (NumberField.RingOfIntegers K)).Finite := Set.toFinite _
  have htoFinset :
      IsDedekindDomain.primesOverFinset Q (NumberField.RingOfIntegers K) = hs.toFinset := by
    ext P
    rw [IsDedekindDomain.mem_primesOverFinset_iff hQ0]
    simp
  have hcard_eq :
      (IsDedekindDomain.primesOverFinset Q (NumberField.RingOfIntegers K)).card =
        (Ideal.primesOver Q (NumberField.RingOfIntegers K)).ncard := by
    rw [htoFinset, ← Set.ncard_eq_toFinset_card
      (s := Ideal.primesOver Q (NumberField.RingOfIntegers K)) (hs := hs)]
  rw [← hcard_eq]
  refine le_trans hcard_le ?_
  simp [Algebra.IsQuadraticExtension.finrank_eq_two F K]

lemma cm_i_card
    {F : Type*} [Field F] [NumberField F]
    {p : ℕ} (hp : Nat.Prime p)
    (hsplitF : splitsCompletely F p)
    {Q : Ideal (NumberField.RingOfIntegers F)}
    (hQ : Q ∈ Ideal.primesOver (rationalPrimeIdeal p) (NumberField.RingOfIntegers F)) :
    Nat.card (NumberField.RingOfIntegers F ⧸ Q) = p := by
  classical
  have hp0 : rationalPrimeIdeal p ≠ (⊥ : Ideal ℤ) := by
    simp [rationalPrimeIdeal, hp.ne_zero]
  have hQ0 : Q ≠ ⊥ := Ideal.ne_bot_of_mem_primesOver hp0 hQ
  have hQmax : Q.IsMaximal := hQ.1.isMaximal hQ0
  letI : Q.IsPrime := hQ.1
  letI : Q.IsMaximal := hQmax
  let k := NumberField.RingOfIntegers F ⧸ Q
  letI : Field k := Ideal.Quotient.field Q
  letI : Fintype k := Fintype.ofFinite k
  have hQ_inertia : Ideal.inertiaDeg (rationalPrimeIdeal p) Q = 1 :=
    (hsplitF.2 Q hQ).2
  have hQ_abs : Ideal.absNorm Q = p := by
    have hQ_lies_span : Q.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ)) := by
      simpa [rationalPrimeIdeal] using hQ.2
    letI : Q.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ)) := hQ_lies_span
    have htmp := Ideal.absNorm_eq_pow_inertiaDeg' Q hp
    have hQ_inertia' : (Ideal.span ({(p : ℤ)} : Set ℤ)).inertiaDeg Q = 1 := by
      simpa [rationalPrimeIdeal] using hQ_inertia
    rw [hQ_inertia', pow_one] at htmp
    exact htmp
  have hQ_card_nat : Nat.card k = p := by
    dsimp [k]
    calc
      Nat.card (NumberField.RingOfIntegers F ⧸ Q) = Ideal.absNorm Q := by
        simp [Ideal.absNorm_apply, Submodule.cardQuot_apply]
      _ = p := hQ_abs
  simpa [k] using hQ_card_nat

lemma cm_i_square
    {F : Type*} [Field F] [NumberField F]
    {p : ℕ} (hp : Nat.Prime p) (hp_mod : p % 4 = 1)
    (hsplitF : splitsCompletely F p)
    {Q : Ideal (NumberField.RingOfIntegers F)}
    (hQ : Q ∈ Ideal.primesOver (rationalPrimeIdeal p) (NumberField.RingOfIntegers F)) :
    IsSquare (-1 : NumberField.RingOfIntegers F ⧸ Q) := by
  classical
  have hp0 : rationalPrimeIdeal p ≠ (⊥ : Ideal ℤ) := by
    simp [rationalPrimeIdeal, hp.ne_zero]
  have hQ0 : Q ≠ ⊥ := Ideal.ne_bot_of_mem_primesOver hp0 hQ
  have hQmax : Q.IsMaximal := hQ.1.isMaximal hQ0
  letI : Q.IsPrime := hQ.1
  letI : Q.IsMaximal := hQmax
  let k := NumberField.RingOfIntegers F ⧸ Q
  letI : Field k := Ideal.Quotient.field Q
  letI : Fintype k := Fintype.ofFinite k
  have hQ_card_nat : Nat.card k = p :=
    cm_i_card (F := F) hp hsplitF hQ
  have hQ_card : Fintype.card k = p := by
    rw [← Nat.card_eq_fintype_card, hQ_card_nat]
  have hmod : Fintype.card k % 4 ≠ 3 := by
    rw [hQ_card]
    omega
  exact (FiniteField.isSquare_neg_one_iff (F := k)).2 hmod

lemma cm_adjoin_i
    {F : Type*} [Field F] [NumberField F]
    {K : Type*} [Field K] [NumberField K] [Algebra F K]
    (ι : F →+* K) (hι : algebraMap F K = ι)
    (c : K ≃+* K)
    (hc_base : ∀ a : F, c (ι a) = ι a)
    {Q : Ideal (NumberField.RingOfIntegers F)}
    {P : Ideal (NumberField.RingOfIntegers K)}
    (hPmem : P ∈ Ideal.primesOver Q (NumberField.RingOfIntegers K)) :
    Ideal.map
        (NumberField.RingOfIntegers.mapRingEquiv c :
          NumberField.RingOfIntegers K →+* NumberField.RingOfIntegers K)
        P ∈ Ideal.primesOver Q (NumberField.RingOfIntegers K) := by
  let cO : NumberField.RingOfIntegers K ≃+* NumberField.RingOfIntegers K :=
    NumberField.RingOfIntegers.mapRingEquiv c
  letI : P.IsPrime := hPmem.1
  have hcO_fix_base :
      ∀ z : NumberField.RingOfIntegers F,
        cO (algebraMap (NumberField.RingOfIntegers F)
              (NumberField.RingOfIntegers K) z) =
          algebraMap (NumberField.RingOfIntegers F)
            (NumberField.RingOfIntegers K) z := by
    intro z
    ext
    change c (algebraMap F K (z : F)) = algebraMap F K (z : F)
    simpa [hι] using hc_base (z : F)
  refine ⟨?_, ?_⟩
  · rw [Ideal.map_comap_of_equiv (f := cO) (I := P)]
    exact Ideal.IsPrime.comap cO.symm
  · refine Ideal.LiesOver.mk ?_
    have hunder :
        Ideal.under (NumberField.RingOfIntegers F)
            (Ideal.map
              (cO : NumberField.RingOfIntegers K →+* NumberField.RingOfIntegers K) P) =
          Ideal.under (NumberField.RingOfIntegers F) P := by
      ext z
      constructor
      · intro hz
        rw [Ideal.mem_comap] at hz
        rw [Ideal.mem_comap]
        have hz' :=
          (Ideal.mem_map_iff_of_surjective
            (f := (cO : NumberField.RingOfIntegers K →+* NumberField.RingOfIntegers K))
            (hf := cO.surjective) (I := P)
            (y := algebraMap (NumberField.RingOfIntegers F)
              (NumberField.RingOfIntegers K) z)).1 hz
        rcases hz' with ⟨y, hyP, hyc⟩
        have hyz :
            y =
              algebraMap (NumberField.RingOfIntegers F)
                (NumberField.RingOfIntegers K) z := by
          apply cO.injective
          simpa [hcO_fix_base z] using hyc
        simpa [hyz] using hyP
      · intro hz
        rw [Ideal.mem_comap] at hz ⊢
        exact
          (Ideal.mem_map_iff_of_surjective
            (f := (cO : NumberField.RingOfIntegers K →+* NumberField.RingOfIntegers K))
            (hf := cO.surjective) (I := P)
            (y := algebraMap (NumberField.RingOfIntegers F)
              (NumberField.RingOfIntegers K) z)).2
            ⟨algebraMap (NumberField.RingOfIntegers F)
                (NumberField.RingOfIntegers K) z,
              hz, hcO_fix_base z⟩
    calc
      Q = Ideal.under (NumberField.RingOfIntegers F) P := hPmem.2.over
      _ =
          Ideal.under (NumberField.RingOfIntegers F)
            (Ideal.map
              (cO : NumberField.RingOfIntegers K →+* NumberField.RingOfIntegers K) P) := by
          symm
          exact hunder

lemma distance_cm_i
    {A : Type*} [CommRing A]
    {B : Type*} [CommRing B] [Algebra A B]
    {I : Ideal A} {J : Ideal B} [J.LiesOver I]
    (z : A) (u : A ⧸ I)
    (huz : Ideal.Quotient.mk I z = u)
    (hu_sq : u ^ (2 : ℕ) = (-1 : A ⧸ I)) :
    (Ideal.Quotient.mk J (algebraMap A B z)) ^ (2 : ℕ) = (-1 : B ⧸ J) := by
  have huz_sq_zero : Ideal.Quotient.mk I (z ^ (2 : ℕ) + 1) = 0 := by
    calc
      Ideal.Quotient.mk I (z ^ (2 : ℕ) + 1) =
          (Ideal.Quotient.mk I z) ^ (2 : ℕ) + 1 := by
            simp
      _ = u * u + 1 := by simp [huz, pow_two]
      _ = u ^ (2 : ℕ) + 1 := by simp [pow_two]
      _ = (-1 : A ⧸ I) + 1 := by rw [← hu_sq]
      _ = 0 := by exact neg_add_cancel (1 : A ⧸ I)
  have huz_mem_I : z ^ (2 : ℕ) + 1 ∈ I := by
    exact (Ideal.Quotient.eq_zero_iff_mem).1 huz_sq_zero
  have huz_mem_J : algebraMap A B (z ^ (2 : ℕ) + 1) ∈ J := by
    exact
      (Ideal.mem_of_liesOver
        (A := A) (B := B) (P := J) (p := I) (x := z ^ (2 : ℕ) + 1)).mp huz_mem_I
  have huzJ_zero :
      (Ideal.Quotient.mk J (algebraMap A B z)) ^ (2 : ℕ) + 1 = 0 := by
    calc
      (Ideal.Quotient.mk J (algebraMap A B z)) ^ (2 : ℕ) + 1 =
          Ideal.Quotient.mk J (algebraMap A B (z ^ (2 : ℕ) + 1)) := by
            simp [pow_two, map_add, map_mul]
      _ = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr huz_mem_J
  exact (eq_neg_iff_add_eq_zero).2 huzJ_zero

lemma distance_adjoin_i
    {R : Type*} [CommRing R]
    (x u : R)
    (hx_sq : x ^ (2 : ℕ) = (-1 : R))
    (hu_sq : u ^ (2 : ℕ) = (-1 : R)) :
    (x - u) * (x + u) = 0 := by
  calc
    (x - u) * (x + u) = x ^ (2 : ℕ) - u ^ (2 : ℕ) := by ring
    _ = (-1 : R) - (-1 : R) := by rw [hx_sq, hu_sq]
    _ = 0 := by abel

lemma cm_i_neg
    {R : Type*} [Field R] {x u : R}
    (hfactor : (x - u) * (x + u) = 0) :
    x = u ∨ x = -u := by
  rcases mul_eq_zero.mp hfactor with hxu | hxu
  · exact Or.inl (sub_eq_zero.mp hxu)
  · exact Or.inr ((eq_neg_iff_add_eq_zero).2 hxu)

lemma cm_i_fix
    {R : Type*} [Ring R] (c : R →+* R) {x u : R}
    (hx_in_base : x = u ∨ x = -u)
    (hu_fix : c u = u)
    (hu_neg_fix : c (-u) = -u) :
    c x = x := by
  rcases hx_in_base with rfl | rfl
  · exact hu_fix
  · exact hu_neg_fix

lemma distance_cm_fix
    {R : Type*} [Ring R] (c : R →+* R) {x : R}
    (hfixx : c x = x) (hnegx : c x = -x) :
    x = -x := by
  calc
    x = c x := hfixx.symm
    _ = -x := hnegx

lemma cm_i_or
    {R : Type*} [Ring R] {x u : R}
    (hx_in_base : x = u ∨ x = -u)
    (hx_eq_neg : x = -x) :
    u = -u := by
  rcases hx_in_base with hxbase | hxbase
  · calc
      u = x := hxbase.symm
      _ = -x := hx_eq_neg
      _ = -u := by rw [hxbase]
  · have hneg : -u = u := by
      calc
        -u = x := hxbase.symm
        _ = -x := hx_eq_neg
        _ = -(-u) := by rw [hxbase]
        _ = u := by simp
    exact hneg.symm

lemma cm_i_split
    {F : Type*} [Field F] [NumberField F] [NumberField.IsTotallyReal F]
    {K : Type*} [Field K] [NumberField K] [Algebra F K]
    (ι : F →+* K) (hι : algebraMap F K = ι)
    (ii : K)
    (_hii : ii ^ (2 : ℕ) = (-1 : K))
    (_hspan : ∀ z : K, ∃ a b : F, z = ι a + ι b * ii)
    (_hquadratic : Algebra.IsQuadraticExtension F K)
    {p : ℕ} (hp : Nat.Prime p) (hp_mod : p % 4 = 1)
    (hsplitF : splitsCompletely F p)
    {Q : Ideal (NumberField.RingOfIntegers F)}
    (hQ : Q ∈ Ideal.primesOver (rationalPrimeIdeal p) (NumberField.RingOfIntegers F)) :
    1 < (Ideal.primesOver Q (NumberField.RingOfIntegers K)).ncard := by
  classical
  set n := (Ideal.primesOver Q (NumberField.RingOfIntegers K)).ncard with hn
  by_contra hlt
  have hn_le_one : n ≤ 1 := by
    exact Nat.not_lt.mp (by simpa [hn] using hlt)
  have hp0 : rationalPrimeIdeal p ≠ (⊥ : Ideal ℤ) := by
    simp [rationalPrimeIdeal, hp.ne_zero]
  have hQ0 : Q ≠ ⊥ := Ideal.ne_bot_of_mem_primesOver hp0 hQ
  have hQmax : Q.IsMaximal := hQ.1.isMaximal hQ0
  letI : Q.IsPrime := hQ.1
  letI : Q.IsMaximal := hQmax
  have hn_ne_zero :
      (Ideal.primesOver Q (NumberField.RingOfIntegers K)).ncard ≠ 0 :=
    IsDedekindDomain.primesOver_ncard_ne_zero Q (NumberField.RingOfIntegers K)
  obtain ⟨c, hc_base, hc_ii, _hc_embed⟩ :=
    cmIConjugation (ι := ι) (ii := ii) _hii _hspan
  let cO : NumberField.RingOfIntegers K ≃+* NumberField.RingOfIntegers K :=
    NumberField.RingOfIntegers.mapRingEquiv c
  have hPnonempty :
      (Ideal.primesOver Q (NumberField.RingOfIntegers K)).Nonempty := by
    exact Set.nonempty_of_ncard_ne_zero hn_ne_zero
  rcases hPnonempty with ⟨P, hPmem⟩
  have hP0 : P ≠ ⊥ := Ideal.ne_bot_of_mem_primesOver hQ0 hPmem
  have hPmax : P.IsMaximal := hPmem.1.isMaximal hP0
  letI : P.IsPrime := hPmem.1
  letI : P.IsMaximal := hPmax
  letI : P.LiesOver Q := hPmem.2
  let k := NumberField.RingOfIntegers F ⧸ Q
  let κ := NumberField.RingOfIntegers K ⧸ P
  letI : Field k := Ideal.Quotient.field Q
  letI : Fintype k := Fintype.ofFinite k
  letI : Field κ := Ideal.Quotient.field P
  letI : Algebra k κ := by
    dsimp [k, κ]
    infer_instance
  have hQ_card_nat : Nat.card k = p := by
    simpa [k] using
      cm_i_card (F := F) hp hsplitF hQ
  have hQ_card : Fintype.card k = p := by
    rw [← Nat.card_eq_fintype_card, hQ_card_nat]
  have hk_sq_neg_one : IsSquare (-1 : k) := by
    simpa [k] using
      cm_i_square
        (F := F) hp hp_mod hsplitF hQ
  rcases hk_sq_neg_one with ⟨u, hu_sq⟩
  have hu_sq' : u ^ (2 : ℕ) = (-1 : k) := by
    simpa [pow_two, mul_comm] using hu_sq.symm
  have h_integral_Z : IsIntegral ℤ ii := by
    refine ⟨Polynomial.X ^ (2 : ℕ) + 1,
      by
        simpa using
          (Polynomial.monic_X_pow_add_C (a := (1 : ℤ)) (n := 2)
            (by decide : (2 : ℕ) ≠ 0)), ?_⟩
    simp [_hii]
  let xO : NumberField.RingOfIntegers K := ⟨ii, h_integral_Z⟩
  set x : κ := Ideal.Quotient.mk P xO with hxdef
  have hxO_sq : xO ^ (2 : ℕ) = (-1 : NumberField.RingOfIntegers K) := by
    ext
    simp [xO, _hii]
  have hx_sq : x ^ (2 : ℕ) = (-1 : κ) := by
    rw [hxdef]
    change Ideal.Quotient.mk P (xO ^ (2 : ℕ)) = (-1 : κ)
    simp [hxO_sq]
  have hcO_fix_base :
      ∀ z : NumberField.RingOfIntegers F,
        cO (algebraMap (NumberField.RingOfIntegers F)
              (NumberField.RingOfIntegers K) z) =
          algebraMap (NumberField.RingOfIntegers F)
            (NumberField.RingOfIntegers K) z := by
    intro z
    ext
    change c (algebraMap F K (z : F)) = algebraMap F K (z : F)
    simpa [hι] using hc_base (z : F)
  have hcO_xO : cO xO = -xO := by
    ext
    change c ii = -ii
    exact hc_ii
  have hmap_mem :
      Ideal.map (cO : NumberField.RingOfIntegers K →+* NumberField.RingOfIntegers K) P ∈
        Ideal.primesOver Q (NumberField.RingOfIntegers K) :=
    cm_adjoin_i
      (ι := ι) (hι := hι) c hc_base hPmem
  have hsubs :
      (Ideal.primesOver Q (NumberField.RingOfIntegers K)).Subsingleton := by
    rw [← Set.ncard_le_one_iff_subsingleton]
    simpa [hn] using hn_le_one
  have hmapP_eq :
      Ideal.map (cO : NumberField.RingOfIntegers K →+* NumberField.RingOfIntegers K) P = P :=
    hsubs hmap_mem hPmem
  let cκ : κ ≃+* κ :=
    Ideal.quotientEquiv P P cO hmapP_eq.symm
  obtain ⟨z, huz⟩ := Ideal.Quotient.mk_surjective u
  let uκ : κ :=
    Ideal.Quotient.mk P
      (algebraMap (NumberField.RingOfIntegers F)
        (NumberField.RingOfIntegers K) z)
  have huκ_fix : cκ uκ = uκ := by
    change
      cκ (Ideal.Quotient.mk P
        (algebraMap (NumberField.RingOfIntegers F)
          (NumberField.RingOfIntegers K) z)) =
        Ideal.Quotient.mk P
          (algebraMap (NumberField.RingOfIntegers F)
            (NumberField.RingOfIntegers K) z)
    rw [Ideal.quotientEquiv_mk]
    exact congrArg (Ideal.Quotient.mk P) (hcO_fix_base z)
  have huκ_neg_fix : cκ (-uκ) = -uκ := by
    change
      cκ (Ideal.Quotient.mk P
        (-(algebraMap (NumberField.RingOfIntegers F)
          (NumberField.RingOfIntegers K) z))) =
        Ideal.Quotient.mk P
          (-(algebraMap (NumberField.RingOfIntegers F)
            (NumberField.RingOfIntegers K) z))
    rw [Ideal.quotientEquiv_mk]
    exact congrArg (Ideal.Quotient.mk P) (by rw [map_neg, hcO_fix_base z])
  have huκ_sq : uκ ^ (2 : ℕ) = (-1 : κ) := by
    simpa [uκ] using
      distance_cm_i
        (A := NumberField.RingOfIntegers F)
        (B := NumberField.RingOfIntegers K)
        (I := Q) (J := P) z u huz hu_sq'
  have hfactor : (x - uκ) * (x + uκ) = 0 := by
    exact
      distance_adjoin_i
        x uκ hx_sq huκ_sq
  have hx_in_base : x = uκ ∨ x = -uκ := by
    exact cm_i_neg hfactor
  have hfixx : cκ x = x := by
    exact
      cm_i_fix
        cκ hx_in_base huκ_fix huκ_neg_fix
  have hnegx : cκ x = -x := by
    rw [hxdef]
    change cκ (Ideal.Quotient.mk P xO) = Ideal.Quotient.mk P (-xO)
    rw [Ideal.quotientEquiv_mk]
    exact congrArg (Ideal.Quotient.mk P) hcO_xO
  have hx_eq_neg : x = -x := by
    exact distance_cm_fix cκ hfixx hnegx
  have hk_char_ne_two : ringChar k ≠ 2 := by
    intro hk2
    have hk_even : Fintype.card k % 2 = 0 :=
      FiniteField.even_card_of_char_two hk2
    rw [hQ_card] at hk_even
    omega
  have huκ_eq : algebraMap k κ u = uκ := by
    rw [← huz]
    rfl
  have huκ_eq_neg : uκ = -uκ := by
    exact
      cm_i_or
        hx_in_base hx_eq_neg
  have hk_neg_one_ne_one : (-1 : k) ≠ (1 : k) :=
    Ring.neg_one_ne_one_of_char_ne_two hk_char_ne_two
  have hu_add_zero : u + u = 0 := by
    apply (algebraMap k κ).injective
    have hsum : uκ + uκ = uκ + (-uκ) := congrArg (fun t : κ => uκ + t) huκ_eq_neg
    calc
      algebraMap k κ (u + u) = algebraMap k κ u + algebraMap k κ u := by
        exact (algebraMap k κ).map_add u u
      _ = uκ + algebraMap k κ u := by rw [huκ_eq]
      _ = uκ + uκ := by rw [huκ_eq]
      _ = uκ + (-uκ) := hsum
      _ = (0 : κ) := add_neg_cancel uκ
      _ = algebraMap k κ 0 := by
        symm
        exact (algebraMap k κ).map_zero
  have hk_bad : (-1 : k) = 1 := by
    have hu_eq_neg : u = -u := (eq_neg_iff_add_eq_zero).2 hu_add_zero
    have humul : u * u = u * (-u) := congrArg (fun t : k => u * t) hu_eq_neg
    calc
      (-1 : k) = u * u := hu_sq
      _ = u * (-u) := humul
      _ = -(u * u) := by rw [mul_neg]
      _ = -(-1 : k) := by rw [hu_sq]
      _ = 1 := neg_neg (1 : k)
  exact hk_neg_one_ne_one hk_bad

lemma distance_cm_adjoin
    {F : Type*} [Field F] [NumberField F] [NumberField.IsTotallyReal F]
    {K : Type*} [Field K] [NumberField K] [Algebra F K]
    (ι : F →+* K) (hι : algebraMap F K = ι)
    (ii : K)
    (_hii : ii ^ (2 : ℕ) = (-1 : K))
    (_hspan : ∀ z : K, ∃ a b : F, z = ι a + ι b * ii)
    (hquadratic : Algebra.IsQuadraticExtension F K)
    {p : ℕ} (hp : Nat.Prime p) (hp_mod : p % 4 = 1)
    (hsplitF : splitsCompletely F p)
    {Q : Ideal (NumberField.RingOfIntegers F)}
    (hQ : Q ∈ Ideal.primesOver (rationalPrimeIdeal p) (NumberField.RingOfIntegers F)) :
    (Ideal.primesOver Q (NumberField.RingOfIntegers K)).ncard = 2 := by
  have hupper :
      (Ideal.primesOver Q (NumberField.RingOfIntegers K)).ncard ≤ 2 :=
    level_cm_i
      (ι := ι) (_hι := hι) (ii := ii) (_hii := _hii) (_hspan := _hspan)
      (hquadratic := hquadratic) hp hp_mod hsplitF hQ
  have hlower :
      1 < (Ideal.primesOver Q (NumberField.RingOfIntegers K)).ncard :=
    cm_i_split
      (ι := ι) (hι := hι) (ii := ii) (_hii := _hii) (_hspan := _hspan)
      (_hquadratic := hquadratic) hp hp_mod hsplitF hQ
  omega

lemma cm_i_inertia
    {F : Type*} [Field F] [NumberField F] [NumberField.IsTotallyReal F]
    {K : Type*} [Field K] [NumberField K] [Algebra F K]
    (ι : F →+* K) (hι : algebraMap F K = ι)
    (ii : K)
    (_hii : ii ^ (2 : ℕ) = (-1 : K))
    (_hspan : ∀ z : K, ∃ a b : F, z = ι a + ι b * ii)
    (hquadratic : Algebra.IsQuadraticExtension F K)
    {p : ℕ} (hp : Nat.Prime p) (hp_mod : p % 4 = 1)
    (hsplitF : splitsCompletely F p) :
    ∀ P ∈ Ideal.primesOver (rationalPrimeIdeal p) (NumberField.RingOfIntegers K),
      Ideal.ramificationIdx (rationalPrimeIdeal p) P = 1 ∧
        Ideal.inertiaDeg (rationalPrimeIdeal p) P = 1 := by
  intro P hP
  letI : Algebra.IsQuadraticExtension F K := hquadratic
  haveI : IsGalois F K := Algebra.IsQuadraticExtension.isGalois F K
  let Q : Ideal (NumberField.RingOfIntegers F) := Ideal.under (NumberField.RingOfIntegers F) P
  have hPprime : P.IsPrime := hP.1
  letI : P.IsPrime := hPprime
  have hP_lies_p : P.LiesOver (rationalPrimeIdeal p) := hP.2
  have hQprime : Q.IsPrime := by
    dsimp [Q, Ideal.under]
    exact Ideal.comap_isPrime (algebraMap (NumberField.RingOfIntegers F)
      (NumberField.RingOfIntegers K)) P
  have hQ_lies_p : Q.LiesOver (rationalPrimeIdeal p) := by
    refine Ideal.LiesOver.mk ?_
    dsimp [Q, Ideal.under]
    rw [Ideal.comap_comap]
    have hcomp :
        (algebraMap (NumberField.RingOfIntegers F) (NumberField.RingOfIntegers K)).comp
          (Int.castRingHom (NumberField.RingOfIntegers F)) =
          algebraMap ℤ (NumberField.RingOfIntegers K) := by
      simpa using
        (IsScalarTower.algebraMap_eq ℤ
          (NumberField.RingOfIntegers F) (NumberField.RingOfIntegers K)).symm
    simpa [hcomp] using hP_lies_p.over
  have hQmem : Q ∈ Ideal.primesOver (rationalPrimeIdeal p) (NumberField.RingOfIntegers F) :=
    ⟨hQprime, hQ_lies_p⟩
  have hp0 : rationalPrimeIdeal p ≠ (⊥ : Ideal ℤ) := by
    simp [rationalPrimeIdeal, hp.ne_zero]
  have hQ0 : Q ≠ ⊥ := Ideal.ne_bot_of_mem_primesOver hp0 hQmem
  have hQmax : Q.IsMaximal := hQprime.isMaximal hQ0
  letI : Q.IsPrime := hQprime
  letI : Q.IsMaximal := hQmax
  have hP_lies_Q : P.LiesOver Q := Ideal.LiesOver.mk rfl
  letI : P.LiesOver Q := hP_lies_Q
  have hrelcount : (Ideal.primesOver Q (NumberField.RingOfIntegers K)).ncard = 2 :=
    distance_cm_adjoin
      (ι := ι) (hι := hι) (ii := ii) (_hii := _hii) (_hspan := _hspan)
      (hquadratic := hquadratic) hp hp_mod hsplitF hQmem
  have hrelformula := Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn
    (p := Q) hQ0 (NumberField.RingOfIntegers K) (Gal(K / F))
  have hcardG : Nat.card Gal(K / F) = 2 := by
    simpa [Algebra.IsQuadraticExtension.finrank_eq_two F K] using
      (IsGalois.card_aut_eq_finrank F K)
  have hprodIn : Q.ramificationIdxIn (NumberField.RingOfIntegers K) *
      Q.inertiaDegIn (NumberField.RingOfIntegers K) = 1 := by
    have hrelformula' := hrelformula
    rw [hrelcount, hcardG] at hrelformula'
    exact Nat.eq_of_mul_eq_mul_left (by decide : 0 < 2) hrelformula'
  have hramifIn_one : Q.ramificationIdxIn (NumberField.RingOfIntegers K) = 1 := by
    exact Nat.eq_one_of_dvd_one ⟨Q.inertiaDegIn (NumberField.RingOfIntegers K), hprodIn.symm⟩
  have hinertiaIn_one : Q.inertiaDegIn (NumberField.RingOfIntegers K) = 1 := by
    rw [Nat.mul_comm] at hprodIn
    exact Nat.eq_one_of_dvd_one
      ⟨Q.ramificationIdxIn (NumberField.RingOfIntegers K), hprodIn.symm⟩
  have hramif_rel :
      Ideal.ramificationIdx Q P = 1 := by
    calc
      Ideal.ramificationIdx Q P = Q.ramificationIdxIn (NumberField.RingOfIntegers K) := by
            symm
            exact Ideal.ramificationIdxIn_eq_ramificationIdx
              (p := Q) (P := P) (G := Gal(K / F))
      _ = 1 := hramifIn_one
  have hinertia_rel : Q.inertiaDeg P = 1 := by
    calc
      Q.inertiaDeg P = Q.inertiaDegIn (NumberField.RingOfIntegers K) := by
        symm
        exact Ideal.inertiaDegIn_eq_inertiaDeg (p := Q) (P := P) (G := Gal(K / F))
      _ = 1 := hinertiaIn_one
  rcases hsplitF.2 Q hQmem with ⟨hramif_base, hinertia_base⟩
  have hmapQ_ne_bot :
      Ideal.map
          (algebraMap (NumberField.RingOfIntegers F) (NumberField.RingOfIntegers K))
          Q ≠ ⊥ := by
    intro hbot
    have hle : Q ≤ RingHom.ker (algebraMap (NumberField.RingOfIntegers F)
        (NumberField.RingOfIntegers K)) :=
      (Ideal.map_eq_bot_iff_le_ker
        (algebraMap (NumberField.RingOfIntegers F) (NumberField.RingOfIntegers K))).1 hbot
    have hker :
        RingHom.ker
            (algebraMap (NumberField.RingOfIntegers F) (NumberField.RingOfIntegers K)) =
          ⊥ := by
      apply SetLike.ext
      intro x
      rw [RingHom.mem_ker, Ideal.mem_bot]
      constructor
      · intro hx
        exact (FaithfulSMul.algebraMap_injective (NumberField.RingOfIntegers F)
          (NumberField.RingOfIntegers K)) (by simpa using hx)
      · intro hx
        simp [hx]
    apply hQ0
    exact bot_unique (hker ▸ hle)
  have hmapp_ne_bot :
      Ideal.map
        (algebraMap ℤ (NumberField.RingOfIntegers K)) (rationalPrimeIdeal p) ≠ ⊥ := by
    intro hbot
    have hle :
        rationalPrimeIdeal p ≤
          RingHom.ker (algebraMap ℤ (NumberField.RingOfIntegers K)) :=
      (Ideal.map_eq_bot_iff_le_ker
          (algebraMap ℤ (NumberField.RingOfIntegers K))).1 hbot
    have hker : RingHom.ker (algebraMap ℤ (NumberField.RingOfIntegers K)) = ⊥ := by
      apply SetLike.ext
      intro x
      rw [RingHom.mem_ker, Ideal.mem_bot]
      constructor
      · intro hx
        exact (FaithfulSMul.algebraMap_injective ℤ
          (NumberField.RingOfIntegers K)) (by simpa using hx)
      · intro hx
        simp [hx]
    apply hp0
    exact bot_unique (hker ▸ hle)
  have hmapQ_le_P :
      Ideal.map
          (algebraMap (NumberField.RingOfIntegers F) (NumberField.RingOfIntegers K))
          Q ≤ P := by
    exact Ideal.map_comap_le
  have hp_int : Prime (p : ℤ) := by
    exact (Int.prime_iff_natAbs_prime).2 (by simpa using hp)
  have hprimeIdeal : (rationalPrimeIdeal p).IsPrime := by
    simpa [rationalPrimeIdeal] using
      (Ideal.span_singleton_prime (p := (p : ℤ)) (by exact_mod_cast hp.ne_zero)).2 hp_int
  have hpmax : (rationalPrimeIdeal p).IsMaximal := hprimeIdeal.isMaximal hp0
  letI : (rationalPrimeIdeal p).IsMaximal := hpmax
  have hramif_abs := Ideal.ramificationIdx_algebra_tower
    (p := rationalPrimeIdeal p) (P := Q) (Q := P) hmapQ_ne_bot hmapp_ne_bot hmapQ_le_P
  have hinertia_abs := Ideal.inertiaDeg_algebra_tower (p := rationalPrimeIdeal p) (P := Q) (I := P)
  constructor
  · rw [hramif_abs, hramif_base, one_mul, hramif_rel]
  · rw [hinertia_abs, hinertia_base, one_mul, hinertia_rel]

/--
Counting step for the split-prime argument.

This isolates the part of the paper that turns the local splitting of each
prime of `F` above `p` into the global count of primes of `K` above `p`.
-/
lemma cm_i_count
    {F : Type*} [Field F] [NumberField F] [NumberField.IsTotallyReal F]
    {K : Type*} [Field K] [NumberField K] [Algebra F K]
    (ι : F →+* K) (hι : algebraMap F K = ι)
    (ii : K)
    (hii : ii ^ (2 : ℕ) = (-1 : K))
    (hspan : ∀ z : K, ∃ a b : F, z = ι a + ι b * ii)
    (hquadratic : Algebra.IsQuadraticExtension F K)
    {p : ℕ} (hp : Nat.Prime p) (hp_mod : p % 4 = 1)
    (hsplitF : splitsCompletely F p) :
    (Ideal.primesOver (rationalPrimeIdeal p) (NumberField.RingOfIntegers K)).ncard =
      Module.finrank ℚ K := by
  have hp0 : rationalPrimeIdeal p ≠ (⊥ : Ideal ℤ) := by
    simp [rationalPrimeIdeal, hp.ne_zero]
  have hp_int : Prime (p : ℤ) := by
    exact (Int.prime_iff_natAbs_prime).2 (by simpa using hp)
  have hprimeIdeal : (rationalPrimeIdeal p).IsPrime := by
    simpa [rationalPrimeIdeal] using
      (Ideal.span_singleton_prime (p := (p : ℤ)) (by exact_mod_cast hp.ne_zero)).2 hp_int
  have hmax : (rationalPrimeIdeal p).IsMaximal := hprimeIdeal.isMaximal hp0
  letI : (rationalPrimeIdeal p).IsMaximal := hmax
  have hsum := Ideal.sum_ramification_inertia
    (S := NumberField.RingOfIntegers K) (K := ℚ) (L := K) (p := rationalPrimeIdeal p) hp0
  have hterm :
      ∀ P ∈ IsDedekindDomain.primesOverFinset (rationalPrimeIdeal p) (NumberField.RingOfIntegers K),
        Ideal.ramificationIdx (rationalPrimeIdeal p) P *
          Ideal.inertiaDeg (rationalPrimeIdeal p) P = 1 := by
    intro P hP
    have hP' : P ∈ Ideal.primesOver (rationalPrimeIdeal p) (NumberField.RingOfIntegers K) := by
      exact (IsDedekindDomain.mem_primesOverFinset_iff hp0 (NumberField.RingOfIntegers K)).1 hP
    rcases cm_i_inertia
      (ι := ι) (hι := hι) (ii := ii) (_hii := hii) (_hspan := hspan)
      (hquadratic := hquadratic) hp hp_mod hsplitF P hP' with ⟨he, hf⟩
    have he' :
        Ideal.ramificationIdx (rationalPrimeIdeal p) P = 1 := by
      simpa using he
    rw [he', hf]
  have hcard :
      (Ideal.primesOver (rationalPrimeIdeal p) (NumberField.RingOfIntegers K)).ncard =
        (IsDedekindDomain.primesOverFinset (rationalPrimeIdeal p) (NumberField.RingOfIntegers
          K)).card := by
    have hfinite :
        (Ideal.primesOver (rationalPrimeIdeal p) (NumberField.RingOfIntegers K)).Finite :=
      IsDedekindDomain.primesOver_finite (rationalPrimeIdeal p) (NumberField.RingOfIntegers K)
    rw [Set.ncard_eq_toFinset_card _ hfinite]
    congr 1
    apply Finset.ext
    intro P
    rw [
      Set.Finite.mem_toFinset hfinite,
      IsDedekindDomain.mem_primesOverFinset_iff hp0 (NumberField.RingOfIntegers K)
    ]
  have hsum' :
      ∑ P ∈ IsDedekindDomain.primesOverFinset (rationalPrimeIdeal p) (NumberField.RingOfIntegers
        K), 1 =
        Module.finrank ℚ K := by
    calc
      ∑ P ∈ IsDedekindDomain.primesOverFinset (rationalPrimeIdeal p) (NumberField.RingOfIntegers
        K), 1
        = ∑ P ∈ IsDedekindDomain.primesOverFinset (rationalPrimeIdeal p)
          (NumberField.RingOfIntegers K),
            Ideal.ramificationIdx (rationalPrimeIdeal p) P *
            Ideal.inertiaDeg (rationalPrimeIdeal p) P := by
              symm
              apply Finset.sum_congr rfl
              intro P hP
              exact hterm P hP
      _ = Module.finrank ℚ K := hsum
  calc
    (Ideal.primesOver (rationalPrimeIdeal p) (NumberField.RingOfIntegers K)).ncard
      = (IsDedekindDomain.primesOverFinset (rationalPrimeIdeal p) (NumberField.RingOfIntegers
        K)).card := hcard
    _ = ∑ P ∈ IsDedekindDomain.primesOverFinset (rationalPrimeIdeal p)
      (NumberField.RingOfIntegers K), 1 :=
      Finset.card_eq_sum_ones _
    _ = Module.finrank ℚ K := hsum'

/--
The hard integral-arithmetic step for `K = F(i)`: when `p ≡ 1 (mod 4)` and
`p` splits completely in `F`, the polynomial `X^2 + 1` splits over the residue
fields above `p`, and the integral control on `F(i) / F` lets that splitting
lift to `K`.
-/
lemma cm_i_input
    {F : Type*} [Field F] [NumberField F] [NumberField.IsTotallyReal F]
    {K : Type*} [Field K] [NumberField K]
    [Algebra F K] [IsScalarTower ℚ F K]
    (ι : F →+* K) (ii : K)
    (hii : ii ^ (2 : ℕ) = (-1 : K))
    (hspan : ∀ z : K, ∃ a b : F, z = ι a + ι b * ii) :
    cmIInput (F := F) (K := K) := by
  intro p hp hp_mod hsplitF
  letI : Algebra F K := ι.toAlgebra
  have hquadratic : Algebra.IsQuadraticExtension F K :=
    cm_i_extension
      (ι := ι) (hι := rfl) (ii := ii) hii hspan
  refine ⟨?_, ?_⟩
  · exact cm_i_count
      (ι := ι) (hι := rfl) (ii := ii) hii hspan hquadratic hp hp_mod hsplitF
  · exact cm_i_inertia
      (ι := ι) (hι := rfl) (ii := ii) hii hspan hquadratic hp hp_mod hsplitF

lemma cmICompletely
    {F : Type*} [Field F] [NumberField F] [NumberField.IsTotallyReal F]
    {K : Type*} [Field K] [NumberField K]
    [Algebra F K] [IsScalarTower ℚ F K]
    (ι : F →+* K) (ii : K)
    (_hii : ii ^ (2 : ℕ) = (-1 : K))
    (_hspan : ∀ z : K, ∃ a b : F, z = ι a + ι b * ii) :
    cmIInput (F := F) (K := K) →
    ∀ {p : ℕ}, Nat.Prime p → p % 4 = 1 →
      splitsCompletely F p → splitsCompletely K p := by
  /-
  Paper step: when `p ≡ 1 (mod 4)` and `p` splits completely in `F`, the
  polynomial `X^2 + 1` splits over each residue field above `p`, so those primes
  split in `K = F(i)` as well.
  -/
  intro hintegral p hp_prime hp_mod hsplitF
  exact hintegral hp_prime hp_mod hsplitF

/--
For a fixed level `j`, the paper adjoins `i` to `F_j` to obtain a CM field
`K_j = F_j(i)`. This lemma packages exactly the field-theoretic properties of
that auxiliary field that are used in the `U_j` construction.
-/
lemma distance_cm_tower
    (T : SplitTotallyTower.{0}) (j : ℕ) :
    ∃ (K : Type) (_ : Field K) (_ : NumberField K)
      (ι : T.fields j →+* K) (ii : K) (c : K ≃+* K),
      ii ^ (2 : ℕ) = (-1 : K) ∧
      (∀ z : K, ∃ a b : T.fields j, z = ι a + ι b * ii) ∧
      (∀ a : T.fields j, c (ι a) = ι a) ∧
      c ii = -ii ∧
      (∀ σ : K →+* ℂ, ∀ x : K, σ (c x) = star (σ x)) ∧
      (∀ {p : ℕ}, Nat.Prime p → p % 4 = 1 →
        splitsCompletely (T.fields j) p → splitsCompletely K p) := by
  letI : NumberField.IsTotallyReal (T.fields j) := T.totallyReal j
  let fF : Polynomial (T.fields j) := cmIPoly (T.fields j)
  have hirr : Irreducible fF := by
    simpa [fF] using
      cm_i_irreducible (T.fields j)
  letI : Fact (Irreducible fF) := ⟨hirr⟩
  letI hmonic_fF : fF.Monic := by
    dsimp [fF, cmIPoly]
    simpa using
      (Polynomial.monic_X_pow_add (p := (1 : Polynomial (T.fields j))) (n := 2) (by simp))
  have hdeg_fF : fF.degree = 2 := by
    dsimp [fF, cmIPoly]
    simpa using
      (Polynomial.degree_X_pow_add_C (n := 2) (a := (1 : T.fields j)) (by norm_num : 0 < 2))
  let K := AdjoinRoot fF
  letI : Field K := inferInstance
  let fdFK : FiniteDimensional (T.fields j) K := by
    have hf_ne_zero : fF ≠ 0 := hirr.ne_zero
    exact Module.Basis.finiteDimensional_of_finite
      (AdjoinRoot.powerBasis (f := fF) hf_ne_zero).basis
  letI : FiniteDimensional (T.fields j) K := fdFK
  let fdQK : FiniteDimensional ℚ K := by
    exact FiniteDimensional.trans ℚ (T.fields j) K
  let charK : CharZero K := by
    refine charZero_of_inj_zero ?_
    intro n hn
    have h_inj : Function.Injective (algebraMap ℚ K) := RingHom.injective (algebraMap ℚ K)
    have hq : (n : ℚ) = 0 := h_inj (by simpa using hn)
    norm_num at hq
    exact hq
  let numberFieldK : NumberField K := { to_charZero := charK, to_finiteDimensional := fdQK }
  have hii : AdjoinRoot.root fF ^ (2 : ℕ) = (-1 : K) := by
    have h := AdjoinRoot.eval₂_root fF
    rw [show fF = Polynomial.X ^ 2 + (1 : Polynomial (T.fields j)) by
      dsimp [fF, cmIPoly],
      Polynomial.eval₂_add, Polynomial.eval₂_pow, Polynomial.eval₂_X] at h
    simp only [Polynomial.eval₂_one, pow_two] at h
    simpa [pow_two] using eq_neg_of_add_eq_zero_left h
  have hspan : ∀ z : K,
      ∃ a b : T.fields j, z = AdjoinRoot.of fF a + AdjoinRoot.of fF b * AdjoinRoot.root fF := by
    intro z
    refine AdjoinRoot.induction_on (f := fF) z ?_
    intro p
    let r : Polynomial (T.fields j) := p %ₘ fF
    have hr_eq : AdjoinRoot.mk fF r = AdjoinRoot.mk fF p := by
      have hleft := AdjoinRoot.mk_leftInverse hmonic_fF (AdjoinRoot.mk fF p)
      simpa [r, AdjoinRoot.modByMonicHom_mk] using hleft
    have hrdeg : r.degree < 2 := by
      dsimp [r]
      simpa [hdeg_fF] using Polynomial.degree_modByMonic_lt p hmonic_fF
    have hrpoly : r = Polynomial.C (r.coeff 0) + Polynomial.C (r.coeff 1) * Polynomial.X := by
      ext n
      rcases n with _ | _ | n
      · simp [r]
      · simp [r]
      · have hcoeff_ge2 : ∀ m : ℕ, 2 ≤ m → r.coeff m = 0 :=
          (Polynomial.degree_lt_iff_coeff_zero r 2).1 hrdeg
        have hr0 : r.coeff (n + 2) = 0 := hcoeff_ge2 (n + 2) (by omega)
        simp [hr0]
    refine ⟨r.coeff 0, r.coeff 1, ?_⟩
    calc
      AdjoinRoot.mk fF p = AdjoinRoot.mk fF r := hr_eq.symm
      _ = AdjoinRoot.of fF (r.coeff 0) + AdjoinRoot.of fF (r.coeff 1) * AdjoinRoot.root fF := by
        rw [hrpoly]
        simp
  obtain ⟨c, hc_fix, hc_ii, hc_star⟩ :=
    cmIConjugation
      (ι := AdjoinRoot.of fF) (ii := AdjoinRoot.root fF) hii hspan
  letI : IsScalarTower ℚ (T.fields j) K := by infer_instance
  have hintegral :
      cmIInput (F := T.fields j) (K := K) :=
    cm_i_input
      (ι := AdjoinRoot.of fF) (ii := AdjoinRoot.root fF) hii hspan
  have hsplit :
      ∀ {p : ℕ}, Nat.Prime p → p % 4 = 1 →
        splitsCompletely (T.fields j) p → splitsCompletely K p :=
    cmICompletely
      (ι := AdjoinRoot.of fF) (ii := AdjoinRoot.root fF) hii hspan hintegral
  exact ⟨K, inferInstance, numberFieldK, AdjoinRoot.of fF, AdjoinRoot.root fF, c,
    hii, hspan, hc_fix, hc_ii, hc_star, hsplit⟩

lemma cm_i_tower
    (T : SplitTotallyTower.{0}) (j : ℕ)
    {K : Type*} [Field K] [NumberField K]
    (ι : T.fields j →+* K) (ii : K)
    (hii : ii ^ (2 : ℕ) = (-1 : K))
    (hspan : ∀ z : K, ∃ a b : T.fields j, z = ι a + ι b * ii) :
    NumberField.IsTotallyComplex K ∧
      NumberField.InfinitePlace.nrComplexPlaces K = Module.finrank ℚ (T.fields j) := by
  /-
  Paper step: because `F_j` is totally real and `K_j = F_j(i)` is obtained by
  adjoining a square root of `-1`, the extension is CM, hence totally complex,
  and has exactly `d_j = [F_j : ℚ]` complex places.
  -/
  classical
  let F := T.fields j
  letI : Algebra F K := ι.toAlgebra
  have hno_real_embedding : ∀ φ : K →+* ℂ, ¬NumberField.ComplexEmbedding.IsReal φ := by
    intro φ hφ
    let φR : K →+* ℝ := hφ.embedding
    have hsq : φR ii ^ (2 : ℕ) = (-1 : ℝ) := by
      simpa using congrArg φR hii
    have hnonneg : 0 ≤ φR ii ^ (2 : ℕ) := sq_nonneg (φR ii)
    nlinarith
  have htotallyComplex : NumberField.IsTotallyComplex K := by
    rw [NumberField.isTotallyComplex_iff]
    intro w
    have hw_not_real : ¬w.IsReal := by
      intro hw
      exact hno_real_embedding w.embedding ((NumberField.InfinitePlace.isReal_iff).1 hw)
    exact (NumberField.InfinitePlace.not_isReal_iff_isComplex (w := w)).1 hw_not_real
  have hii_not_mem_range : ii ∉ Set.range ι := by
    intro hii_mem
    rcases hii_mem with ⟨a, rfl⟩
    have hsq : a ^ (2 : ℕ) = (-1 : F) := by
      apply ι.injective
      simpa using hii
    let φ : F →+* ℂ := NumberField.ComplexEmbedding.lift F (algebraMap ℚ ℂ)
    have hφ_real_place : (NumberField.InfinitePlace.mk φ).IsReal := by
      exact
        ((NumberField.isTotallyReal_iff F).1 (T.totallyReal j))
          (NumberField.InfinitePlace.mk φ)
    have hφ_real : NumberField.ComplexEmbedding.IsReal φ :=
      (NumberField.InfinitePlace.isReal_mk_iff).1 hφ_real_place
    let φR : F →+* ℝ := hφ_real.embedding
    have hsq_real : φR a ^ (2 : ℕ) = (-1 : ℝ) := by
      simpa using congrArg φR hsq
    have hnonneg : 0 ≤ φR a ^ (2 : ℕ) := sq_nonneg (φR a)
    nlinarith
  let spanMap : (Fin 2 → F) →ₗ[F] K :=
    { toFun := fun v => ι (v 0) + ι (v 1) * ii
      map_add' := by
        intro v w
        change ι (v 0 + w 0) + ι (v 1 + w 1) * ii =
          (ι (v 0) + ι (v 1) * ii) + (ι (w 0) + ι (w 1) * ii)
        simp [add_mul, add_assoc, add_left_comm]
      map_smul' := by
        intro a v
        change ι (a * v 0) + ι (a * v 1) * ii = ι a * (ι (v 0) + ι (v 1) * ii)
        simp [mul_add, mul_left_comm, mul_comm] }
  have hspanMap_surj : Function.Surjective spanMap := by
    intro z
    rcases hspan z with ⟨a, b, rfl⟩
    refine ⟨![a, b], ?_⟩
    simp [spanMap]
  letI : Module.Finite F (Fin 2 → F) := Module.Finite.of_basis (Pi.basisFun F (Fin 2))
  letI : Module.Finite F K := Module.Finite.of_surjective spanMap hspanMap_surj
  have hfinrank_le : Module.finrank F K ≤ 2 := by
    have hrange : spanMap.range = ⊤ := (LinearMap.range_eq_top).2 hspanMap_surj
    calc
      Module.finrank F K = Module.finrank F ↥spanMap.range := by
        symm
        exact LinearEquiv.finrank_eq (LinearEquiv.ofTop spanMap.range hrange)
      _ ≤ Module.finrank F (Fin 2 → F) := LinearMap.finrank_range_le spanMap
      _ = 2 := by
        rw [Module.finrank_eq_card_basis (Pi.basisFun F (Fin 2)), Fintype.card_fin]
  have hlinind : LinearIndependent F ![(1 : K), ii] := by
    rw [LinearIndependent.pair_iff' one_ne_zero]
    intro a ha
    apply hii_not_mem_range
    refine ⟨a, ?_⟩
    simpa [Algebra.smul_def] using ha
  have hfinrank_ge : 2 ≤ Module.finrank F K := by
    simpa using LinearIndependent.fintype_card_le_finrank hlinind
  have hfinrank_eq : Module.finrank F K = 2 := le_antisymm hfinrank_le hfinrank_ge
  have hfinrank_mul :
      Module.finrank ℚ K = 2 * Module.finrank ℚ F := by
    calc
      Module.finrank ℚ K = Module.finrank ℚ F * Module.finrank F K := by
        symm
        exact Module.finrank_mul_finrank ℚ F K
      _ = Module.finrank ℚ F * 2 := by rw [hfinrank_eq]
      _ = 2 * Module.finrank ℚ F := by ring
  have hnrReal : NumberField.InfinitePlace.nrRealPlaces K = 0 := by
    have hcard_zero :
        Fintype.card { φ : K →+* ℂ // NumberField.ComplexEmbedding.IsReal φ } = 0 := by
      apply Fintype.card_eq_zero_iff.2
      refine ⟨?_⟩
      intro φ
      exact hno_real_embedding φ.1 φ.2
    rw [← NumberField.InfinitePlace.card_real_embeddings K]
    exact hcard_zero
  have hnrComplex : NumberField.InfinitePlace.nrComplexPlaces K = Module.finrank ℚ F := by
    have hcount :
        2 * NumberField.InfinitePlace.nrComplexPlaces K = 2 * Module.finrank ℚ F := by
      calc
        2 * NumberField.InfinitePlace.nrComplexPlaces K = Module.finrank ℚ K := by
          have h :=
            NumberField.InfinitePlace.card_add_two_mul_card_eq_rank K
          rwa [hnrReal, zero_add] at h
        _ = 2 * Module.finrank ℚ F := hfinrank_mul
    omega
  exact ⟨htotallyComplex, hnrComplex⟩

lemma cm_discriminant_tower
    (T : SplitTotallyTower.{0}) (j : ℕ)
    {K : Type*} [Field K] [NumberField K]
    (ι : T.fields j →+* K) (ii : K)
    (hii : ii ^ (2 : ℕ) = (-1 : K))
    (hspan : ∀ z : K, ∃ a b : T.fields j, z = ι a + ι b * ii) :
    rootDiscriminant K ≤ 2 * rootDiscriminant (T.fields j) := by
  letI : NumberField.IsTotallyReal (T.fields j) := T.totallyReal j
  letI : Algebra (T.fields j) K := ι.toAlgebra
  letI : IsScalarTower ℚ (T.fields j) K :=
    IsScalarTower.of_algebraMap_eq fun x => by simp
  let F := T.fields j
  let A := NumberField.RingOfIntegers F
  let B := NumberField.RingOfIntegers K
  have hroot_bound_aux :
      ∀ {d DK DF : ℕ}, 0 < d →
        (DK : ℝ) ≤ (4 : ℝ) ^ d * (DF : ℝ) ^ (2 : ℕ) →
        Real.rpow (DK : ℝ) (1 / (((2 * d : ℕ) : ℝ))) ≤
          2 * Real.rpow (DF : ℝ) (1 / (d : ℝ)) := by
    intro d DK DF hd h
    have hDK_nonneg : 0 ≤ (DK : ℝ) := by positivity
    have hexp_nonneg : 0 ≤ 1 / (((2 * d : ℕ) : ℝ)) := by positivity
    refine le_trans (Real.rpow_le_rpow hDK_nonneg h hexp_nonneg) ?_
    have hfour : (((4 : ℝ) ^ d) ^ (1 / (((2 * d : ℕ) : ℝ))) : ℝ) = 2 := by
      have hdz : (((2 * d : ℕ) : ℝ)) ≠ 0 := by
        exact_mod_cast (Nat.mul_pos (by decide) hd).ne'
      calc
        (((4 : ℝ) ^ d) ^ (1 / (((2 * d : ℕ) : ℝ))) : ℝ)
            = (((2 : ℝ) ^ (2 * d : ℕ)) ^ (1 / (((2 * d : ℕ) : ℝ))) : ℝ) := by
                rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, ← pow_mul]
        _ = (2 : ℝ) ^ ((((2 * d : ℕ) : ℝ)) * (1 / (((2 * d : ℕ) : ℝ)))) := by
              rw [show ((2 : ℝ) ^ (2 * d : ℕ)) = Real.rpow (2 : ℝ) (((2 * d : ℕ) : ℝ)) by
                    simpa using (Real.rpow_natCast (2 : ℝ) (2 * d)).symm]
              simpa [mul_comm] using
                (Real.rpow_mul (by positivity) (((2 * d : ℕ) : ℝ))
                  (1 / (((2 * d : ℕ) : ℝ)))).symm
        _ = (2 : ℝ) ^ (1 : ℝ) := by field_simp [hdz]
        _ = 2 := by simp
    have hDfpow :
        ((((DF : ℝ) ^ (2 : ℕ)) ^ (1 / (((2 * d : ℕ) : ℝ))) : ℝ)) =
          Real.rpow (DF : ℝ) (1 / (d : ℝ)) := by
      calc
        ((((DF : ℝ) ^ (2 : ℕ)) ^ (1 / (((2 * d : ℕ) : ℝ))) : ℝ))
            = Real.rpow (Real.rpow (DF : ℝ) (2 : ℝ)) (1 / (((2 * d : ℕ) : ℝ))) := by
                simp
        _ = Real.rpow (DF : ℝ) ((2 : ℝ) * (1 / (((2 * d : ℕ) : ℝ)))) := by
              simpa [mul_comm] using
                (Real.rpow_mul (show 0 ≤ (DF : ℝ) by positivity) (2 : ℝ)
                  (1 / (((2 * d : ℕ) : ℝ)))).symm
        _ = Real.rpow (DF : ℝ) (1 / (d : ℝ)) := by
              congr 1
              have hdz : (d : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hd)
              field_simp [hdz]
              norm_num
    have hmul_nonneg1 : 0 ≤ (4 : ℝ) ^ d := by positivity
    have hmul_nonneg2 : 0 ≤ (DF : ℝ) ^ (2 : ℕ) := by positivity
    rw [Real.mul_rpow hmul_nonneg1 hmul_nonneg2, hfour, hDfpow]
  have h_integral_F : IsIntegral F ii := by
    refine ⟨Polynomial.X ^ (2 : ℕ) + 1,
      by
        simpa using
          Polynomial.monic_X_pow_add_C (1 : F) (by decide : (2 : ℕ) ≠ 0), ?_⟩
    simp [hii]
  have h_integral_Z : IsIntegral ℤ ii := by
    refine ⟨Polynomial.X ^ (2 : ℕ) + 1,
      by
        simpa using
          Polynomial.monic_X_pow_add_C (1 : ℤ) (by decide : (2 : ℕ) ≠ 0), ?_⟩
    simp [hii]
  have htop : Algebra.adjoin F ({ii} : Set K) = ⊤ := by
    refine top_le_iff.mp ?_
    intro z hz
    rcases hspan z with ⟨a, b, rfl⟩
    exact Subalgebra.add_mem _ (Subalgebra.algebraMap_mem _ a)
      (Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ b)
        (Algebra.subset_adjoin (by simp)))
  let pb : PowerBasis F K := PowerBasis.ofAdjoinEqTop h_integral_F htop
  have hdeg2_poly : (Polynomial.X ^ (2 : ℕ) + (1 : Polynomial F)).natDegree = 2 := by
    simpa using (Polynomial.natDegree_X_pow_add_C (n := 2) (r := (1 : F)))
  have hle_dim : pb.dim ≤ 2 := by
    have htmp := PowerBasis.dim_le_natDegree_of_root pb
      (by simpa using Polynomial.X_pow_add_C_ne_zero (n := 2) (hn := by decide) (a := (1 : F)))
      (by simp [pb, PowerBasis.ofAdjoinEqTop_gen, hii])
    rw [hdeg2_poly] at htmp
    exact htmp
  have hne_dim_one : pb.dim ≠ 1 := by
    intro h1
    have hii_range : ∃ a : F, ii = algebraMap F K a := by
      obtain ⟨f, hfdeg, hfeq⟩ := pb.exists_eq_aeval pb.gen
      use f.coeff 0
      have hgen : pb.gen = ii := by simp [pb, PowerBasis.ofAdjoinEqTop_gen]
      rw [← hgen, hfeq, Polynomial.aeval_eq_sum_range' hfdeg]
      simp [h1, Algebra.smul_def]
    have hsurj : Function.Surjective ι := by
      rcases hii_range with ⟨c, hc0⟩
      have hc : ii = ι c := by simpa using hc0
      intro z
      rcases hspan z with ⟨a, b, rfl⟩
      refine ⟨a + b * c, ?_⟩
      simp [map_add, map_mul, hc]
    let e : F ≃+* K := RingEquiv.ofBijective ι ⟨ι.injective, hsurj⟩
    letI : NumberField.IsTotallyReal K := NumberField.IsTotallyReal.ofRingEquiv e
    let φ : K →+* ℂ := Classical.choice inferInstance
    let hφ := NumberField.IsTotallyReal.complexEmbedding_isReal φ
    have h1c : φ ii ^ (2 : ℕ) = (-1 : ℂ) := by
      simpa using congrArg φ hii
    have h1r : (hφ.embedding ii) ^ (2 : ℕ) = (-1 : ℝ) := by
      apply Complex.ofReal_injective
      simpa [NumberField.ComplexEmbedding.IsReal.coe_embedding_apply] using h1c
    nlinarith [sq_nonneg (hφ.embedding ii)]
  have hdim_pos : 0 < pb.dim := PowerBasis.dim_pos pb
  have hdim : pb.dim = 2 := by
    omega
  have hfinrank_FK : Module.finrank F K = 2 := by
    simpa [hdim] using (PowerBasis.finrank pb)
  have hminpoly_F : minpoly F ii = Polynomial.X ^ (2 : ℕ) + 1 := by
    symm
    apply minpoly.unique F ii
    · simpa using Polynomial.monic_X_pow_add_C (1 : F) (by decide : (2 : ℕ) ≠ 0)
    · simp [hii]
    · intro q hqmonic hqroot
      have hpb := PowerBasis.dim_le_natDegree_of_root (pb := pb) (p := q) hqmonic.ne_zero hqroot
      have hdegq : 2 ≤ q.natDegree := by simpa [hdim] using hpb
      have hqne : q ≠ 0 := hqmonic.ne_zero
      rw [Polynomial.degree_eq_natDegree (by
          simpa using Polynomial.X_pow_add_C_ne_zero (n := 2) (hn := by decide) (a := (1 : F))),
        Polynomial.degree_eq_natDegree hqne, hdeg2_poly]
      exact_mod_cast hdegq
  let x : B := ⟨ii, h_integral_Z⟩
  have hx_sq : x ^ (2 : ℕ) = (-1 : B) := by
    ext
    simp [x, hii]
  have h_integral_A : IsIntegral A ii := by
    refine ⟨Polynomial.X ^ (2 : ℕ) + 1,
      by
        simpa using
          Polynomial.monic_X_pow_add_C (1 : A) (by decide : (2 : ℕ) ≠ 0), ?_⟩
    simp [hii]
  have hminpoly_A_ii : minpoly A ii = Polynomial.X ^ (2 : ℕ) + 1 := by
    apply Polynomial.map_injective (algebraMap A F) (IsFractionRing.injective A F)
    rw [← minpoly.isIntegrallyClosed_eq_field_fractions' F h_integral_A, hminpoly_F]
    simp
  have hminpoly_A_x : minpoly A x = Polynomial.X ^ (2 : ℕ) + 1 := by
    let fBK : B →ₐ[A] K :=
      { toRingHom := algebraMap B K
        commutes' := by
          intro a
          rfl }
    have hAlg :
        minpoly A (fBK x) = minpoly A x :=
      minpoly.algHom_eq fBK (IsFractionRing.injective B K) x
    have hAlg' : minpoly A ii = minpoly A x := by
      simpa [x] using hAlg
    rw [hminpoly_A_ii] at hAlg'
    simpa using hAlg'.symm
  have htop_x : Algebra.adjoin F ({(algebraMap B K) x} : Set K) = ⊤ := by
    simpa [x] using htop
  have hdiff_mem : ((2 : B) * x) ∈ differentIdeal A B := by
    have hmem := aeval_derivative_mem_differentIdeal A F K x htop_x
    have hmem' : (((1 + 1 : B) * x)) ∈ differentIdeal A B := by
      simpa [hminpoly_A_x] using hmem
    convert hmem' using 1
    ring
  have hnorm_x : ((Algebra.norm ℤ) x).natAbs = 1 := by
    have hx_sq' : x * x = (-1 : B) := by simpa [pow_two] using hx_sq
    have hmul1 : x * (-x) = 1 := by
      calc
        x * (-x) = -(x * x) := by ring
        _ = -(-1 : B) := by rw [hx_sq']
        _ = 1 := by norm_num
    have hmul2 : (-x) * x = 1 := by
      calc
        (-x) * x = -(x * x) := by ring
        _ = -(-1 : B) := by rw [hx_sq']
        _ = 1 := by norm_num
    have hx_unit : IsUnit x := ⟨⟨x, -x, hmul1, hmul2⟩, rfl⟩
    have hnorm_unit : IsUnit ((Algebra.norm ℤ) x) := IsUnit.map (Algebra.norm ℤ) hx_unit
    rcases Int.isUnit_iff.mp hnorm_unit with h | h
    · simp [h]
    · simp [h]
  have hnorm_two : (Algebra.norm ℤ) (2 : B) = (2 : ℤ) ^ Module.finrank ℚ K := by
    apply Rat.intCast_inj.mp
    rw [Algebra.coe_norm_int]
    simpa using (Algebra.norm_algebraMap (R := ℚ) (S := K) (2 : ℚ))
  have hnorm_two_x : ((Algebra.norm ℤ) ((2 : B) * x)).natAbs = 2 ^ Module.finrank ℚ K := by
    rw [map_mul, Int.natAbs_mul, hnorm_x, mul_one, hnorm_two]
    simp
  have hdiff_le : Ideal.absNorm (differentIdeal A B) ≤ 2 ^ Module.finrank ℚ K := by
    have hdivZ :
        ↑(Ideal.absNorm (differentIdeal A B)) ∣
          ((2 ^ Module.finrank ℚ K : ℕ) : ℤ) := by
      rw [← hnorm_two_x, Int.dvd_natAbs]
      exact Ideal.absNorm_dvd_norm_of_mem hdiff_mem
    have hdivN : Ideal.absNorm (differentIdeal A B) ∣ 2 ^ Module.finrank ℚ K :=
      Int.natCast_dvd_natCast.mp hdivZ
    exact Nat.le_of_dvd (pow_pos (by decide) _) hdivN
  have hfinrank_QK : Module.finrank ℚ K = Module.finrank ℚ F * Module.finrank F K := by
    exact (Module.finrank_mul_finrank ℚ F K).symm
  have hfinrank_QK' : Module.finrank ℚ K = 2 * Module.finrank ℚ F := by
    rw [hfinrank_QK, hfinrank_FK, mul_comm]
  have hdiscr_nat :
      (NumberField.discr K).natAbs =
        Ideal.absNorm (differentIdeal A B) * (NumberField.discr F).natAbs ^ (2 : ℕ) := by
    rw [
      NumberField.natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow F A K B,
      hfinrank_FK
    ]
  have hdiff_le' : Ideal.absNorm (differentIdeal A B) ≤ 4 ^ Module.finrank ℚ F := by
    calc
      Ideal.absNorm (differentIdeal A B) ≤ 2 ^ Module.finrank ℚ K := hdiff_le
      _ = 2 ^ (2 * Module.finrank ℚ F) := by rw [hfinrank_QK']
      _ = 4 ^ Module.finrank ℚ F := by
            rw [pow_mul]
            norm_num
  have hnat_bound :
      (NumberField.discr K).natAbs ≤
        4 ^ Module.finrank ℚ F * (NumberField.discr F).natAbs ^ (2 : ℕ) := by
    rw [hdiscr_nat]
    exact Nat.mul_le_mul_right _ hdiff_le'
  rw [rootDiscriminant, absDiscriminant, rootDiscriminant, absDiscriminant]
  rw [← Int.cast_abs, ← Nat.cast_natAbs, ← Int.cast_abs, ← Nat.cast_natAbs]
  have hdegF_pos : 0 < Module.finrank ℚ F := Module.finrank_pos
  have hcast_bound :
      ((NumberField.discr K).natAbs : ℝ) ≤
        ((4 : ℕ) ^ Module.finrank ℚ F : ℝ) *
          (((NumberField.discr F).natAbs : ℝ) ^ (2 : ℕ)) := by
    exact_mod_cast hnat_bound
  have hdeg_cast : (Module.finrank ℚ K : ℝ) = ((2 * Module.finrank ℚ F : ℕ) : ℝ) := by
    exact_mod_cast hfinrank_QK'
  rw [hdeg_cast]
  exact hroot_bound_aux hdegF_pos hcast_bound

lemma cm_completely_tower
    (T : SplitTotallyTower.{0}) (j : ℕ)
    {K : Type*} [Field K] [NumberField K]
    (ι : T.fields j →+* K) (ii : K)
    (_hii : ii ^ (2 : ℕ) = (-1 : K))
    (_hspan : ∀ z : K, ∃ a b : T.fields j, z = ι a + ι b * ii)
    (hsplit_bridge :
      ∀ {p : ℕ}, Nat.Prime p → p % 4 = 1 →
        splitsCompletely (T.fields j) p → splitsCompletely K p)
    {p : ℕ} (hp_prime : Nat.Prime p) (hp_mod : p % 4 = 1)
    (hsplitF : splitsCompletely (T.fields j) p) :
    splitsCompletely K p := by
  exact hsplit_bridge hp_prime hp_mod hsplitF

lemma level_cm_tower
    (T : SplitTotallyTower.{0}) (data : DistanceGrowthData T) (j : ℕ) :
    ∃ (K : Type) (_ : Field K) (_ : NumberField K) (_ : NumberField.IsTotallyComplex K),
      NumberField.InfinitePlace.nrComplexPlaces K = Module.finrank ℚ (T.fields j) ∧
      rootDiscriminant K ≤ data.ρ ∧
      (∀ p ∈ data.S, Nat.Prime p ∧ p % 4 = 1 ∧ splitsCompletely K p) := by
  rcases distance_cm_tower T j with
      ⟨K, hFieldK, hNumberFieldK, ι, ii, c, hii, hspan, hc_base, hc_ii, hc_embed,
        hsplit_bridge⟩
  letI := hFieldK
  letI := hNumberFieldK
  rcases cm_i_tower T j ι ii hii hspan with
      ⟨hTotallyComplexK, hcomplex⟩
  letI := hTotallyComplexK
  have hroot_two :
      rootDiscriminant K ≤ 2 * rootDiscriminant (T.fields j) :=
    cm_discriminant_tower T j ι ii hii hspan
  have hroot :
      rootDiscriminant K ≤ data.ρ :=
    le_trans hroot_two (data.hρ_cm j)
  refine ⟨K, hFieldK, hNumberFieldK, hTotallyComplexK, hcomplex, hroot, ?_⟩
  intro p hp
  rcases T.splitPrimes_spec (data.hS_split p hp) with ⟨hp_prime, hp_mod, hsplitF_all⟩
  refine ⟨hp_prime, hp_mod, ?_⟩
  exact
    cm_completely_tower
      T j ι ii hii hspan hsplit_bridge hp_prime hp_mod (hsplitF_all j)

lemma distance_level_bound
    {T : SplitTotallyTower.{0}} (data : DistanceGrowthData T) (j : ℕ)
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
    (hcomplex :
      NumberField.InfinitePlace.nrComplexPlaces K = Module.finrank ℚ (T.fields j))
    (hroot : rootDiscriminant K ≤ data.ρ) :
    (NumberField.classNumber K : ℝ) ≤ data.H ^ Module.finrank ℚ (T.fields j) := by
  have hbound :
      (NumberField.classNumber K : ℝ) ≤
        classNumberBound data.ρ ^ NumberField.InfinitePlace.nrComplexPlaces K :=
    numbers_discriminant_families data.hρ_ge hroot
  calc
    (NumberField.classNumber K : ℝ) ≤
        classNumberBound data.ρ ^ NumberField.InfinitePlace.nrComplexPlaces K := hbound
    _ = data.H ^ Module.finrank ℚ (T.fields j) := by
        rw [← data.hH_def, hcomplex]

lemma distance_level_cu
    {T : SplitTotallyTower.{0}} (data : DistanceGrowthData T) (j : ℕ)
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
    (hcomplex :
      NumberField.InfinitePlace.nrComplexPlaces K = Module.finrank ℚ (T.fields j))
    (hclass :
      (NumberField.classNumber K : ℝ) ≤ data.H ^ Module.finrank ℚ (T.fields j)) :
    data.CU ^ Module.finrank ℚ (T.fields j) ≤
      (((2 : ℝ) ^ data.S.card) ^ NumberField.InfinitePlace.nrComplexPlaces K) /
        (NumberField.classNumber K : ℝ) := by
  let d : ℕ := Module.finrank ℚ (T.fields j)
  have hnum_nonneg : 0 ≤ (((2 : ℝ) ^ data.S.card) ^ d) := by
    positivity
  have hH_pos : 0 < data.H := by
    linarith [data.hH]
  have hHpow_pos : 0 < data.H ^ d := by
    exact pow_pos hH_pos d
  have hclass_pos : 0 < (NumberField.classNumber K : ℝ) := by
    exact_mod_cast NumberField.classNumber_pos K
  have hdiv :
      (((2 : ℝ) ^ data.S.card) ^ d) / data.H ^ d ≤
        (((2 : ℝ) ^ data.S.card) ^ d) / (NumberField.classNumber K : ℝ) := by
    rw [div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left
      ((inv_le_inv₀ hHpow_pos hclass_pos).2 hclass) hnum_nonneg
  calc
    data.CU ^ Module.finrank ℚ (T.fields j) =
        (((2 : ℝ) ^ data.S.card) ^ d) / data.H ^ d := by
          dsimp [d]
          rw [data.hCU_def, div_pow]
    _ ≤ (((2 : ℝ) ^ data.S.card) ^ d) / (NumberField.classNumber K : ℝ) := hdiv
    _ = (((2 : ℝ) ^ data.S.card) ^ NumberField.InfinitePlace.nrComplexPlaces K) /
          (NumberField.classNumber K : ℝ) := by
            rw [hcomplex]

/--
Every number field has at least one complex embedding. This is the embedding
used to project the CM construction to the plane.
-/
lemma distance_complex_embedding
    (K : Type) [Field K] [NumberField K] :
    Nonempty (K →+* ℂ) := by
  let σ : K →ₐ[ℚ] ℂ := IsAlgClosed.lift (R := ℚ) (S := K) (M := ℂ)
  exact ⟨σ.toRingHom⟩

/-- The conjugation `c` on `K` preserves the ring of integers. -/
def distanceCMIntegers
    {K : Type*} [Field K] [NumberField K] (c : K ≃+* K) :
    NumberField.RingOfIntegers K ≃+* NumberField.RingOfIntegers K := by
  let cQ : K ≃ₐ[ℚ] K :=
    { toRingEquiv := c
      commutes' := by
        intro q
        exact map_ratCast c q }
  let cQsymm : K ≃ₐ[ℚ] K :=
    { toRingEquiv := c.symm
      commutes' := by
        intro q
        exact map_ratCast c.symm q }
  refine
    { toFun := fun x => ⟨c x.1, ?_⟩
      invFun := fun x => ⟨c.symm x.1, ?_⟩
      left_inv := ?_
      right_inv := ?_
      map_mul' := ?_
      map_add' := ?_ }
  · change IsIntegral ℤ (c ↑x)
    exact IsIntegral.map cQ x.2
  · change IsIntegral ℤ (c.symm ↑x)
    exact IsIntegral.map cQsymm x.2
  · intro x
    ext
    simp
  · intro x
    ext
    simp
  · intro x y
    ext
    exact map_mul c _ _
  · intro x y
    ext
    exact map_add c _ _

lemma distance_cm_commutes
    {K : Type*} [Field K] [NumberField K] (c : K ≃+* K) (z : ℤ) :
    distanceCMIntegers c
      ((algebraMap ℤ (NumberField.RingOfIntegers K)) z) =
    algebraMap ℤ (NumberField.RingOfIntegers K) z := by
  ext
  change c ((algebraMap ℤ (NumberField.RingOfIntegers K)) z : K) = _
  simp

lemma cm_conjugation_integers
    {K : Type*} [Field K] [NumberField K] (c : K ≃+* K)
    (P : Ideal (NumberField.RingOfIntegers K)) :
    Ideal.under ℤ
        (Ideal.map
          (distanceCMIntegers c :
            NumberField.RingOfIntegers K →+* NumberField.RingOfIntegers K) P) =
      Ideal.under ℤ P := by
  ext z
  constructor
  · intro hz
    rw [Ideal.mem_comap] at hz
    rw [Ideal.mem_comap]
    have hz' :=
      (Ideal.mem_map_iff_of_surjective
        (f :=
          (distanceCMIntegers c :
            NumberField.RingOfIntegers K →+* NumberField.RingOfIntegers K))
        (hf := (distanceCMIntegers c).surjective) (I := P)
        (y := algebraMap ℤ (NumberField.RingOfIntegers K) z)).1 hz
    rcases hz' with ⟨x, hx, hxc⟩
    have hxz : x = algebraMap ℤ (NumberField.RingOfIntegers K) z := by
      apply (distanceCMIntegers c).injective
      simpa [distance_cm_commutes c z] using hxc
    simpa [hxz] using hx
  · intro hz
    rw [Ideal.mem_comap] at hz ⊢
    exact
      (Ideal.mem_map_iff_of_surjective
        (f :=
          (distanceCMIntegers c :
            NumberField.RingOfIntegers K →+* NumberField.RingOfIntegers K))
        (hf := (distanceCMIntegers c).surjective) (I := P)
        (y := algebraMap ℤ (NumberField.RingOfIntegers K) z)).2
        ⟨algebraMap ℤ (NumberField.RingOfIntegers K) z, hz,
          distance_cm_commutes c z⟩

lemma level_cm_involutive
    {F : Type*} [Field F] {K : Type*} [Field K]
    (ι : F →+* K) (ii : K) (c : K ≃+* K)
    (hc_base : ∀ a : F, c (ι a) = ι a)
    (hc_ii : c ii = -ii)
    (hspan : ∀ z : K, ∃ a b : F, z = ι a + ι b * ii) :
    Function.Involutive c := by
  intro z
  rcases hspan z with ⟨a, b, rfl⟩
  simp [map_add, map_mul, hc_base, hc_ii, mul_comm]

lemma distance_cm_involutive
    {F : Type*} [Field F] {K : Type*} [Field K] [NumberField K]
    (ι : F →+* K) (ii : K) (c : K ≃+* K)
    (hc_base : ∀ a : F, c (ι a) = ι a)
    (hc_ii : c ii = -ii)
    (hspan : ∀ z : K, ∃ a b : F, z = ι a + ι b * ii) :
    Function.Involutive (distanceCMIntegers c) := by
  intro x
  ext
  exact level_cm_involutive ι ii c hc_base hc_ii hspan x

lemma cm_commutes_base
    {F : Type*} [Field F] [NumberField F]
    {K : Type*} [Field K] [NumberField K] [Algebra F K]
    (c : K ≃+* K)
    (hc_base : ∀ a : F, c (algebraMap F K a) = algebraMap F K a)
    (x : NumberField.RingOfIntegers F) :
    distanceCMIntegers c
        (algebraMap (NumberField.RingOfIntegers F) (NumberField.RingOfIntegers K) x) =
      algebraMap (NumberField.RingOfIntegers F) (NumberField.RingOfIntegers K) x := by
  ext
  change
    c ((((algebraMap (NumberField.RingOfIntegers F) (NumberField.RingOfIntegers K)) x :
        NumberField.RingOfIntegers K) : K)) =
      ((((algebraMap (NumberField.RingOfIntegers F) (NumberField.RingOfIntegers K)) x :
        NumberField.RingOfIntegers K) : K))
  simpa using hc_base (x : F)

lemma distance_cm_base
    {F : Type*} [Field F] [NumberField F]
    {K : Type*} [Field K] [NumberField K] [Algebra F K]
    (c : K ≃+* K)
    (hc_base : ∀ a : F, c (algebraMap F K a) = algebraMap F K a)
    (P : Ideal (NumberField.RingOfIntegers K)) :
    Ideal.under (NumberField.RingOfIntegers F)
        (Ideal.map
          (distanceCMIntegers c :
            NumberField.RingOfIntegers K →+* NumberField.RingOfIntegers K) P) =
      Ideal.under (NumberField.RingOfIntegers F) P := by
  ext z
  constructor
  · intro hz
    rw [Ideal.mem_comap] at hz
    rw [Ideal.mem_comap]
    have hz' :=
      (Ideal.mem_map_iff_of_surjective
        (f :=
          (distanceCMIntegers c :
            NumberField.RingOfIntegers K →+* NumberField.RingOfIntegers K))
        (hf := (distanceCMIntegers c).surjective) (I := P)
        (y := algebraMap (NumberField.RingOfIntegers F) (NumberField.RingOfIntegers K) z)).1 hz
    rcases hz' with ⟨x, hx, hxc⟩
    have hxz :
        x = algebraMap (NumberField.RingOfIntegers F) (NumberField.RingOfIntegers K) z := by
      apply (distanceCMIntegers c).injective
      simpa [cm_commutes_base
        (c := c) hc_base z] using hxc
    simpa [hxz] using hx
  · intro hz
    rw [Ideal.mem_comap] at hz ⊢
    exact
      (Ideal.mem_map_iff_of_surjective
        (f :=
          (distanceCMIntegers c :
            NumberField.RingOfIntegers K →+* NumberField.RingOfIntegers K))
        (hf := (distanceCMIntegers c).surjective) (I := P)
        (y := algebraMap (NumberField.RingOfIntegers F) (NumberField.RingOfIntegers K) z)).2
        ⟨algebraMap (NumberField.RingOfIntegers F) (NumberField.RingOfIntegers K) z, hz,
          cm_commutes_base
            (c := c) hc_base z⟩

lemma distance_cm_integers
    {F : Type*} [Field F] [NumberField F]
    {K : Type*} [Field K] [NumberField K] [Algebra F K]
    (c : K ≃+* K)
    (hc_base : ∀ a : F, c (algebraMap F K a) = algebraMap F K a)
    (Q : Ideal (NumberField.RingOfIntegers F))
    {P : Ideal (NumberField.RingOfIntegers K)}
    (hP : P ∈ Ideal.primesOver Q (NumberField.RingOfIntegers K)) :
    Ideal.map
        (distanceCMIntegers c :
          NumberField.RingOfIntegers K →+* NumberField.RingOfIntegers K) P ∈
      Ideal.primesOver Q (NumberField.RingOfIntegers K) := by
  rcases hP with ⟨hPprime, hPover⟩
  refine ⟨?_, ?_⟩
  · rw [Ideal.map_comap_of_equiv (f := distanceCMIntegers c) (I := P)]
    letI : (P : Ideal (NumberField.RingOfIntegers K)).IsPrime := hPprime
    exact Ideal.IsPrime.comap (distanceCMIntegers c).symm
  · refine Ideal.LiesOver.mk ?_
    calc
      Q = Ideal.under (NumberField.RingOfIntegers F) P := hPover.over
      _ =
          Ideal.under (NumberField.RingOfIntegers F)
            (Ideal.map
              (distanceCMIntegers c :
                NumberField.RingOfIntegers K →+* NumberField.RingOfIntegers K) P) := by
          symm
          exact
          distance_cm_base
              (c := c) hc_base P

lemma cm_adjoin_fix
    {F : Type*} [Field F] [NumberField F]
    {K : Type*} [Field K] [NumberField K] [Algebra F K]
    (ι : F →+* K) (hι : algebraMap F K = ι)
    (ii : K)
    (_hii : ii ^ (2 : ℕ) = (-1 : K))
    (c : K ≃+* K)
    (hc_base : ∀ a : F, c (ι a) = ι a)
    (hc_ii : c ii = -ii)
    {p : ℕ} (hp : Nat.Prime p) (hp_mod : p % 4 = 1)
    (hsplitF : splitsCompletely F p)
    {Q : Ideal (NumberField.RingOfIntegers F)}
    (hQ : Q ∈ Ideal.primesOver (rationalPrimeIdeal p) (NumberField.RingOfIntegers F))
    {P : Ideal (NumberField.RingOfIntegers K)}
    (hPmem : P ∈ Ideal.primesOver Q (NumberField.RingOfIntegers K)) :
    Ideal.map
        (distanceCMIntegers c :
          NumberField.RingOfIntegers K →+* NumberField.RingOfIntegers K) P ≠ P := by
  intro hmapP_eq
  have hp0 : rationalPrimeIdeal p ≠ (⊥ : Ideal ℤ) := by
    simp [rationalPrimeIdeal, hp.ne_zero]
  have hQ0 : Q ≠ ⊥ := Ideal.ne_bot_of_mem_primesOver hp0 hQ
  have hQmax : Q.IsMaximal := hQ.1.isMaximal hQ0
  letI : Q.IsPrime := hQ.1
  letI : Q.IsMaximal := hQmax
  have hP0 : P ≠ ⊥ := Ideal.ne_bot_of_mem_primesOver hQ0 hPmem
  have hPmax : P.IsMaximal := hPmem.1.isMaximal hP0
  letI : P.IsPrime := hPmem.1
  letI : P.IsMaximal := hPmax
  letI : P.LiesOver Q := hPmem.2
  let k := NumberField.RingOfIntegers F ⧸ Q
  let κ := NumberField.RingOfIntegers K ⧸ P
  letI : Field k := Ideal.Quotient.field Q
  letI : Fintype k := Fintype.ofFinite k
  letI : Field κ := Ideal.Quotient.field P
  letI : Algebra k κ := by
    dsimp [k, κ]
    infer_instance
  have hQ_card_nat : Nat.card k = p := by
    simpa [k] using
      cm_i_card (F := F) hp hsplitF hQ
  have hQ_card : Fintype.card k = p := by
    rw [← Nat.card_eq_fintype_card, hQ_card_nat]
  have hk_sq_neg_one : IsSquare (-1 : k) := by
    simpa [k] using
      cm_i_square
        (F := F) hp hp_mod hsplitF hQ
  rcases hk_sq_neg_one with ⟨u, hu_sq⟩
  have hu_sq' : u ^ (2 : ℕ) = (-1 : k) := by
    simpa [pow_two, mul_comm] using hu_sq.symm
  have hu_sq'' : u * u = (-1 : k) := by
    simpa [pow_two] using hu_sq'
  have h_integral_Z : IsIntegral ℤ ii := by
    refine ⟨Polynomial.X ^ (2 : ℕ) + 1,
      by
        simpa using
          (Polynomial.monic_X_pow_add_C (a := (1 : ℤ)) (n := 2)
            (by decide : (2 : ℕ) ≠ 0)), ?_⟩
    simp [_hii]
  let xO : NumberField.RingOfIntegers K := ⟨ii, h_integral_Z⟩
  set x : κ := Ideal.Quotient.mk P xO with hxdef
  have hxO_sq : xO ^ (2 : ℕ) = (-1 : NumberField.RingOfIntegers K) := by
    ext
    simp [xO, _hii]
  have hx_sq : x ^ (2 : ℕ) = (-1 : κ) := by
    rw [hxdef]
    change Ideal.Quotient.mk P (xO ^ (2 : ℕ)) = (-1 : κ)
    simp [hxO_sq]
  have hcO_fix_base :
      ∀ z : NumberField.RingOfIntegers F,
        distanceCMIntegers c
            (algebraMap (NumberField.RingOfIntegers F)
              (NumberField.RingOfIntegers K) z) =
          algebraMap (NumberField.RingOfIntegers F)
            (NumberField.RingOfIntegers K) z := by
    intro z
    simpa [hι] using
      cm_commutes_base
        (F := F) (K := K) c (fun a => by simpa [hι] using hc_base a) z
  have hcO_xO :
      distanceCMIntegers c xO = -xO := by
    ext
    change c ii = -ii
    exact hc_ii
  let cκ : κ ≃+* κ :=
    Ideal.quotientEquiv P P
      (distanceCMIntegers c) hmapP_eq.symm
  obtain ⟨z, huz⟩ := Ideal.Quotient.mk_surjective u
  let uκ : κ :=
    Ideal.Quotient.mk P
      (algebraMap (NumberField.RingOfIntegers F)
        (NumberField.RingOfIntegers K) z)
  have huκ_fix : cκ uκ = uκ := by
    change
      cκ (Ideal.Quotient.mk P
        (algebraMap (NumberField.RingOfIntegers F)
          (NumberField.RingOfIntegers K) z)) =
        Ideal.Quotient.mk P
          (algebraMap (NumberField.RingOfIntegers F)
            (NumberField.RingOfIntegers K) z)
    rw [Ideal.quotientEquiv_mk]
    exact congrArg (Ideal.Quotient.mk P) (hcO_fix_base z)
  have huκ_neg_fix : cκ (-uκ) = -uκ := by
    change
      cκ (Ideal.Quotient.mk P
        (-(algebraMap (NumberField.RingOfIntegers F)
          (NumberField.RingOfIntegers K) z))) =
        Ideal.Quotient.mk P
          (-(algebraMap (NumberField.RingOfIntegers F)
            (NumberField.RingOfIntegers K) z))
    rw [Ideal.quotientEquiv_mk]
    exact congrArg (Ideal.Quotient.mk P) (by rw [map_neg, hcO_fix_base z])
  have huκ_sq : uκ ^ (2 : ℕ) = (-1 : κ) := by
    simpa [uκ] using
      distance_cm_i
        (A := NumberField.RingOfIntegers F)
        (B := NumberField.RingOfIntegers K)
        (I := Q) (J := P) z u huz hu_sq'
  have hfactor : (x - uκ) * (x + uκ) = 0 := by
    exact
      distance_adjoin_i
        x uκ hx_sq huκ_sq
  have hx_in_base : x = uκ ∨ x = -uκ := by
    exact cm_i_neg hfactor
  have hfixx : cκ x = x := by
    exact
      cm_i_fix
        cκ hx_in_base huκ_fix huκ_neg_fix
  have hnegx : cκ x = -x := by
    rw [hxdef]
    change cκ (Ideal.Quotient.mk P xO) = Ideal.Quotient.mk P (-xO)
    rw [Ideal.quotientEquiv_mk]
    exact congrArg (Ideal.Quotient.mk P) hcO_xO
  have hx_eq_neg : x = -x := by
    exact distance_cm_fix cκ hfixx hnegx
  have hk_char_ne_two : ringChar k ≠ 2 := by
    intro hk2
    have hk_even : Fintype.card k % 2 = 0 :=
      FiniteField.even_card_of_char_two hk2
    rw [hQ_card] at hk_even
    omega
  have huκ_eq : algebraMap k κ u = uκ := by
    rw [← huz]
    rfl
  have huκ_eq_neg : uκ = -uκ := by
    exact
      cm_i_or
        hx_in_base hx_eq_neg
  have hk_neg_one_ne_one : (-1 : k) ≠ (1 : k) :=
    Ring.neg_one_ne_one_of_char_ne_two hk_char_ne_two
  have hu_add_zero : u + u = 0 := by
    apply (algebraMap k κ).injective
    have hsum : uκ + uκ = uκ + (-uκ) :=
      congrArg (fun t : κ => uκ + t) huκ_eq_neg
    calc
      algebraMap k κ (u + u) = algebraMap k κ u + algebraMap k κ u := by
        exact (algebraMap k κ).map_add u u
      _ = uκ + algebraMap k κ u := by rw [huκ_eq]
      _ = uκ + uκ := by rw [huκ_eq]
      _ = uκ + (-uκ) := hsum
      _ = (0 : κ) := add_neg_cancel uκ
      _ = algebraMap k κ 0 := by
        symm
        exact (algebraMap k κ).map_zero
  have hk_bad : (-1 : k) = 1 := by
    have hu_eq_neg : u = -u := (eq_neg_iff_add_eq_zero).2 hu_add_zero
    have humul : u * u = u * (-u) := congrArg (fun t : k => u * t) hu_eq_neg
    calc
      (-1 : k) = u * u := hu_sq''.symm
      _ = u * (-u) := humul
      _ = -(u * u) := by rw [mul_neg]
      _ = -(-1 : k) := by rw [hu_sq'']
      _ = 1 := neg_neg (1 : k)
  exact hk_neg_one_ne_one hk_bad

def distanceLevelCM
    {F : Type*} [Field F]
    {K : Type*} [Field K] [Algebra F K]
    (c : K ≃+* K)
    (hc_base : ∀ a : F, c (algebraMap F K a) = algebraMap F K a) :
    K ≃ₐ[F] K where
  toRingEquiv := c
  commutes' := hc_base

lemma distance_cm_refl
    {F : Type*} [Field F]
    {K : Type*} [Field K] [NumberField K] [Algebra F K]
    (ii : K) (c : K ≃+* K)
    (hii : ii ^ (2 : ℕ) = (-1 : K))
    (hc_base : ∀ a : F, c (algebraMap F K a) = algebraMap F K a)
    (hc_ii : c ii = -ii) :
    distanceLevelCM (F := F) (K := K) c hc_base ≠ AlgEquiv.refl := by
  intro h
  have hii_ne_zero : ii ≠ 0 := by
    intro hii_zero
    simp [hii_zero] at hii
  have hEq : c ii = ii := by
    simpa using congrArg (fun f : K ≃ₐ[F] K => f ii) h
  have hneg : ii = -ii := by simpa [hEq] using hc_ii
  have hone : (1 : K) = (-1 : K) := by
    apply mul_right_cancel₀ hii_ne_zero
    calc
      (1 : K) * ii = ii := by ring
      _ = -ii := hneg
      _ = (-1 : K) * ii := by ring
  norm_num at hone

lemma cm_gal_restrict
    {F : Type*} [Field F] [NumberField F]
    {K : Type*} [Field K] [NumberField K]
    [Algebra F K] [FiniteDimensional F K]
    (c : K ≃+* K)
    (hc_base : ∀ a : F, c (algebraMap F K a) = algebraMap F K a) :
    AlgEquiv.ofRingEquiv
        (f := distanceCMIntegers c)
        (cm_commutes_base
          (F := F) (K := K) c hc_base)
          =
      galRestrict (NumberField.RingOfIntegers F) F K (NumberField.RingOfIntegers K)
        (distanceLevelCM (F := F) (K := K) c hc_base) := by
  ext x
  change
    c (((x : NumberField.RingOfIntegers K) : K)) =
      (((galRestrict (NumberField.RingOfIntegers F) F K (NumberField.RingOfIntegers K)
        (distanceLevelCM (F := F) (K := K) c hc_base) x :
          NumberField.RingOfIntegers K) : K))
  symm
  exact algebraMap_galRestrict_apply
    (A := NumberField.RingOfIntegers F) (K := F) (L := K) (B := NumberField.RingOfIntegers K)
    (σ := distanceLevelCM (F := F) (K := K) c hc_base) x

lemma distance_cm_primes
    {K : Type*} [Field K] [NumberField K] (c : K ≃+* K)
    (p : ℕ) {P : Ideal (NumberField.RingOfIntegers K)}
    (hP : P ∈ Ideal.primesOver (rationalPrimeIdeal p) (NumberField.RingOfIntegers K)) :
    Ideal.map
        (distanceCMIntegers c :
          NumberField.RingOfIntegers K →+* NumberField.RingOfIntegers K) P ∈
      Ideal.primesOver (rationalPrimeIdeal p) (NumberField.RingOfIntegers K) := by
  rcases hP with ⟨hPprime, hPover⟩
  refine ⟨?_, ?_⟩
  · rw [Ideal.map_comap_of_equiv (f := distanceCMIntegers c) (I := P)]
    letI : (P : Ideal (NumberField.RingOfIntegers K)).IsPrime := hPprime
    exact Ideal.IsPrime.comap (distanceCMIntegers c).symm
  · refine Ideal.LiesOver.mk ?_
    calc
      rationalPrimeIdeal p = Ideal.under ℤ P := hPover.over
      _ =
          Ideal.under ℤ
            (Ideal.map
              (distanceCMIntegers c :
                NumberField.RingOfIntegers K →+* NumberField.RingOfIntegers K) P) := by
          symm
          exact cm_conjugation_integers c P

/--
The field conjugation `c` induces an involution on the finite set of prime ideals
of `O_K` lying above a rational prime `p`.
-/
lemma distance_extract_primes
    {T : SplitTotallyTower.{0}} (data : DistanceGrowthData T) (j : ℕ)
    {K : Type*} [Field K] [NumberField K]
    (ι : T.fields j →+* K) (ii : K) (c : K ≃+* K)
    (_hii : ii ^ (2 : ℕ) = (-1 : K))
    (hspan : ∀ z : K, ∃ a b : T.fields j, z = ι a + ι b * ii)
    (hc_base : ∀ a : T.fields j, c (ι a) = ι a)
    (hc_ii : c ii = -ii)
    (p : ℕ) (_hpS : p ∈ data.S) :
    ∃ τ : Equiv.Perm {P : Ideal (NumberField.RingOfIntegers K) //
        P ∈ Ideal.primesOver (rationalPrimeIdeal p) (NumberField.RingOfIntegers K)},
      ∀ P, (τ P : Ideal (NumberField.RingOfIntegers K)) =
        Ideal.map
          (distanceCMIntegers c :
            NumberField.RingOfIntegers K →+* NumberField.RingOfIntegers K) P.1 := by
  let τ : Equiv.Perm {P : Ideal (NumberField.RingOfIntegers K) //
      P ∈ Ideal.primesOver (rationalPrimeIdeal p) (NumberField.RingOfIntegers K)} :=
    { toFun := fun P => ⟨Ideal.map
        (distanceCMIntegers c :
          NumberField.RingOfIntegers K →+* NumberField.RingOfIntegers K) P.1,
        distance_cm_primes c p P.2⟩
      invFun := fun P => ⟨Ideal.map
        (distanceCMIntegers c :
          NumberField.RingOfIntegers K →+* NumberField.RingOfIntegers K) P.1,
        distance_cm_primes c p P.2⟩
      left_inv := by
        intro P
        apply Subtype.ext
        change
          Ideal.map
              (distanceCMIntegers c :
                NumberField.RingOfIntegers K →+* NumberField.RingOfIntegers K)
              (Ideal.map
                (distanceCMIntegers c :
                  NumberField.RingOfIntegers K →+* NumberField.RingOfIntegers K) P.1) =
            P.1
        rw [Ideal.map_map]
        have hcomp :
            ((distanceCMIntegers c :
                NumberField.RingOfIntegers K →+* NumberField.RingOfIntegers K).comp
              (distanceCMIntegers c :
                NumberField.RingOfIntegers K →+* NumberField.RingOfIntegers K)) =
              RingHom.id (NumberField.RingOfIntegers K) := by
          ext x
          exact congrArg (fun y : NumberField.RingOfIntegers K => (y : K))
            (distance_cm_involutive
              ι ii c hc_base hc_ii hspan x)
        rw [hcomp, Ideal.map_id]
      right_inv := by
        intro P
        apply Subtype.ext
        change
          Ideal.map
              (distanceCMIntegers c :
                NumberField.RingOfIntegers K →+* NumberField.RingOfIntegers K)
              (Ideal.map
                (distanceCMIntegers c :
                  NumberField.RingOfIntegers K →+* NumberField.RingOfIntegers K) P.1) =
            P.1
        rw [Ideal.map_map]
        have hcomp :
            ((distanceCMIntegers c :
                NumberField.RingOfIntegers K →+* NumberField.RingOfIntegers K).comp
              (distanceCMIntegers c :
                NumberField.RingOfIntegers K →+* NumberField.RingOfIntegers K)) =
              RingHom.id (NumberField.RingOfIntegers K) := by
          ext x
          exact congrArg (fun y : NumberField.RingOfIntegers K => (y : K))
            (distance_cm_involutive
              ι ii c hc_base hc_ii hspan x)
        rw [hcomp, Ideal.map_id] }
  refine ⟨τ, ?_⟩
  intro P
  rfl
/--
For every split prime `p` from the fixed set `S`, the bridge hypothesis upgrades
the `F_j`-level splitting information to the full ideal-theoretic splitting data
inside the CM field `K`.
-/
lemma distance_level_cm
    {T : SplitTotallyTower.{0}} (data : DistanceGrowthData T) (j : ℕ)
    {K : Type*} [Field K] [NumberField K]
    (hsplit_bridge :
      ∀ {p : ℕ}, Nat.Prime p → p % 4 = 1 →
        splitsCompletely (T.fields j) p → splitsCompletely K p)
    (hS_splitF : ∀ p ∈ data.S, Nat.Prime p ∧ p % 4 = 1 ∧ splitsCompletely (T.fields j) p) :
    ∀ p ∈ data.S,
      Nat.Prime p ∧ p % 4 = 1 ∧
      (Ideal.primesOver (rationalPrimeIdeal p) (NumberField.RingOfIntegers K)).ncard =
        Module.finrank ℚ K ∧
      (∀ P ∈ Ideal.primesOver (rationalPrimeIdeal p) (NumberField.RingOfIntegers K),
        Ideal.ramificationIdx (rationalPrimeIdeal p) P = 1 ∧
          Ideal.inertiaDeg (rationalPrimeIdeal p) P = 1) := by
  intro p hpS
  rcases hS_splitF p hpS with ⟨hp_prime, hp_mod, hsplitF⟩
  rcases hsplit_bridge hp_prime hp_mod hsplitF with ⟨hcard, hlocal⟩
  exact ⟨hp_prime, hp_mod, hcard, hlocal⟩

/--
This is the stronger `K`-valued version of the unit-set construction. It keeps
the full CM-field elements, rather than only their projection to the plane, and
records that *every* complex embedding has modulus `1` on these elements.
-/
lemma complex_abs_cm
    {K : Type*} [Field K] (c : K ≃+* K)
    (hc_embed : ∀ σ : K →+* ℂ, ∀ x : K, σ (c x) = star (σ x))
    {u : K} (hu : u * c u = 1) (σ : K →+* ℂ) :
    ‖σ u‖ = 1 := by
  have hσ :
      σ u * star (σ u) = (1 : ℂ) := by
    calc
      σ u * star (σ u) = σ u * σ (c u) := by rw [hc_embed σ u]
      _ = σ (u * c u) := by rw [map_mul]
      _ = 1 := by rw [hu, map_one]
  have hnormSqC : ((Complex.normSq (σ u) : ℂ)) = 1 := by
    simpa [Complex.mul_conj] using hσ
  have hnormSq : Complex.normSq (σ u) = 1 :=
    Complex.ofReal_injective hnormSqC
  have hnormSq' : ‖σ u‖ ^ (2 : ℕ) = 1 := by
    simpa [Complex.normSq_eq_norm_sq] using hnormSq
  have hnorm_nonneg : 0 ≤ ‖σ u‖ := norm_nonneg _
  nlinarith

lemma embeddings_have_cm
    {K : Type*} [Field K] (c : K ≃+* K)
    (hc_embed : ∀ σ : K →+* ℂ, ∀ x : K, σ (c x) = star (σ x))
    (U : Finset K)
    (hU : ∀ u ∈ U, u * c u = 1) :
    ∀ u ∈ U, ∀ σ : K →+* ℂ, ‖σ u‖ = 1 := by
  intro u hu σ
  exact complex_abs_cm c hc_embed (hU u hu) σ

/--
Package an injective finite family of CM raw-unit candidates into an actual
`Finset K`, preserving the cardinality lower bound and the defining properties.
-/
lemma package_indexed_finset
    {T : SplitTotallyTower.{0}} (data : DistanceGrowthData T) (_j : ℕ)
    {K : Type*} [Field K] [NumberField K]
    (c : K ≃+* K)
    {n : ℕ} (u : Fin n → K) (hu_inj : Function.Injective u)
    (hcard :
      (((2 : ℝ) ^ data.S.card) ^ NumberField.InfinitePlace.nrComplexPlaces K) /
          (NumberField.classNumber K : ℝ) ≤ n)
    (hu_mul_conj : ∀ a : Fin n, u a * c (u a) = 1)
    (hu_scaled : ∀ a : Fin n, ScaledRingIntegers K data.q (u a)) :
    ∃ U : Finset K,
      (((2 : ℝ) ^ data.S.card) ^ NumberField.InfinitePlace.nrComplexPlaces K) /
          (NumberField.classNumber K : ℝ) ≤ (U.card : ℝ) ∧
      (∀ u' ∈ U, u' * c u' = 1) ∧
      (∀ u' ∈ U, ScaledRingIntegers K data.q u') := by
  classical
  let U : Finset K := Finset.univ.image u
  have hU_card : U.card = Fintype.card (Fin n) := by
    simp [U, Finset.card_image_of_injective, hu_inj]
  refine ⟨U, ?_, ?_, ?_⟩
  · calc
      (((2 : ℝ) ^ data.S.card) ^ NumberField.InfinitePlace.nrComplexPlaces K) /
            (NumberField.classNumber K : ℝ) ≤ (n : ℝ) := by
              exact_mod_cast hcard
      _ = (Fintype.card (Fin n) : ℝ) := by simp
      _ = (U.card : ℝ) := by rw [hU_card]
  · intro u' hu'
    rcases Finset.mem_image.mp hu' with ⟨a, ha, rfl⟩
    exact hu_mul_conj a
  · intro u' hu'
    rcases Finset.mem_image.mp hu' with ⟨a, ha, rfl⟩
    exact hu_scaled a

lemma extract_large_fibre
    {T : SplitTotallyTower.{0}} (data : DistanceGrowthData T)
    {K : Type*} [Field K] [NumberField K] (c : K ≃+* K)
    {m : ℕ} (A0 : Fin m → NonzeroIntegersIdeal K)
    (hA0_card :
      (((2 : ℝ) ^ data.S.card) ^ NumberField.InfinitePlace.nrComplexPlaces K) ≤ m)
    (hA0_inj : Function.Injective A0)
    (hA0_mul_conj :
      ∀ a : Fin m,
        (A0 a : Ideal (NumberField.RingOfIntegers K)) *
            Ideal.map
              (distanceCMIntegers c :
                NumberField.RingOfIntegers K →+* NumberField.RingOfIntegers K)
              (A0 a : Ideal (NumberField.RingOfIntegers K)) =
          Ideal.span
            ({((data.S.prod fun p => p) : NumberField.RingOfIntegers K)} :
              Set (NumberField.RingOfIntegers K))) :
    ∃ n : ℕ, ∃ A : Fin n → NonzeroIntegersIdeal K,
      (((2 : ℝ) ^ data.S.card) ^ NumberField.InfinitePlace.nrComplexPlaces K) /
          (NumberField.classNumber K : ℝ) ≤ n ∧
      Function.Injective A ∧
      (∃ C : ClassGroup (NumberField.RingOfIntegers K),
        ∀ a : Fin n, ClassGroup.mk0 (A a) = C) ∧
      (∀ a : Fin n,
        (A a : Ideal (NumberField.RingOfIntegers K)) *
            Ideal.map
              (distanceCMIntegers c :
                NumberField.RingOfIntegers K →+* NumberField.RingOfIntegers K)
              (A a : Ideal (NumberField.RingOfIntegers K)) =
          Ideal.span
            ({((data.S.prod fun p => p) : NumberField.RingOfIntegers K)} :
              Set (NumberField.RingOfIntegers K))) := by
  classical
  let cls : Fin m → ClassGroup (NumberField.RingOfIntegers K) :=
    fun a => ClassGroup.mk0 (A0 a)
  let q : ℝ :=
    (((2 : ℝ) ^ data.S.card) ^ NumberField.InfinitePlace.nrComplexPlaces K) /
      (NumberField.classNumber K : ℝ)
  have hq_le_sum :
      Fintype.card (ClassGroup (NumberField.RingOfIntegers K)) • q ≤
        ∑ _ : Fin m, (1 : ℝ) := by
    have hclass_pos : 0 < (NumberField.classNumber K : ℝ) := by
      exact_mod_cast NumberField.classNumber_pos K
    rw [nsmul_eq_mul]
    calc
      (Fintype.card (ClassGroup (NumberField.RingOfIntegers K)) : ℝ) * q =
          (NumberField.classNumber K : ℝ) * q := by rfl
      _ = (((2 : ℝ) ^ data.S.card) ^ NumberField.InfinitePlace.nrComplexPlaces K) := by
          dsimp [q]
          field_simp [hclass_pos.ne']
      _ ≤ m := hA0_card
      _ = ∑ _ : Fin m, (1 : ℝ) := by simp
  obtain ⟨C, hC⟩ :=
    Fintype.exists_le_sum_fiber_of_nsmul_le_sum
      (f := cls) (w := fun _ : Fin m => (1 : ℝ)) (b := q) hq_le_sum
  let s : Finset (Fin m) := Finset.univ.filter fun a => cls a = C
  have hs_card : q ≤ (s.card : ℝ) := by
    have hC' :
        q ≤ Finset.sum (Finset.univ.filter fun x => cls x = C) (fun _ => (1 : ℝ)) := by
      simpa using hC
    calc
      q ≤ Finset.sum (Finset.univ.filter fun x => cls x = C) (fun _ => (1 : ℝ)) := hC'
      _ = Finset.sum s (fun _ => (1 : ℝ)) := by simp [s]
      _ = (s.card : ℝ) := by simp
  let A : Fin s.card → NonzeroIntegersIdeal K := fun a => A0 (s.equivFin.symm a)
  refine ⟨s.card, A, hs_card, ?_, ?_, ?_⟩
  · intro a b hab
    apply s.equivFin.symm.injective
    exact Subtype.ext (hA0_inj (by simpa [A] using hab))
  · refine ⟨C, ?_⟩
    intro a
    simpa [A, cls] using (Finset.mem_filter.mp (s.equivFin.symm a).2).2
  · intro a
    simpa [A] using hA0_mul_conj (s.equivFin.symm a)

/--
Reduced arithmetic step for the CM raw-unit candidates.

At this point the tower-level splitting hypotheses have already been converted
into explicit ideal-theoretic split-prime data inside `K`. The only remaining
work is the class-group construction from `Erdos90a.tex`: build the squarefree
ideals `A_η`, choose a large ideal-class fibre, and then pass from
`(\alpha_A) = A A₀⁻¹` to the indexed family `u_A = α_A / c(α_A)`.
-/
lemma nr_complex_places
    {T : SplitTotallyTower.{0}} (data : DistanceGrowthData T) (j : ℕ)
    {K : Type*} [Field K] [NumberField K]
    (ι : T.fields j →+* K) (ii : K)
    (_hii : ii ^ (2 : ℕ) = (-1 : K))
    (hspan : ∀ z : K, ∃ a b : T.fields j, z = ι a + ι b * ii)
    {p : ℕ} (hpS : p ∈ data.S) :
    Nat.card {Q : Ideal (NumberField.RingOfIntegers (T.fields j)) //
        Q ∈ Ideal.primesOver (rationalPrimeIdeal p)
          (NumberField.RingOfIntegers (T.fields j))} =
      NumberField.InfinitePlace.nrComplexPlaces K := by
  classical
  let F := T.fields j
  let OF := NumberField.RingOfIntegers F
  let Sset : Set (Ideal OF) := Ideal.primesOver (rationalPrimeIdeal p) OF
  letI : NumberField.IsTotallyReal F := T.totallyReal j
  rcases
      cm_i_tower
        (T := T) (j := j) (K := K) (ι := ι) (ii := ii) (hii := _hii) (hspan := hspan) with
    ⟨_hTotallyComplex, hcomplexK⟩
  rcases T.splitPrimes_spec (data.hS_split p hpS) with ⟨hp_prime, _hp_mod, hsplitAll⟩
  have hsplitF : splitsCompletely F p := hsplitAll j
  have hp0 : rationalPrimeIdeal p ≠ (⊥ : Ideal ℤ) := by
    simp [rationalPrimeIdeal, hp_prime.ne_zero]
  have hp_int : Prime (p : ℤ) := by
    exact (Int.prime_iff_natAbs_prime).2 (by simpa using hp_prime)
  have hprimeIdeal : (rationalPrimeIdeal p).IsPrime := by
    simpa [rationalPrimeIdeal] using
      (Ideal.span_singleton_prime (p := (p : ℤ)) (by exact_mod_cast hp_prime.ne_zero)).2 hp_int
  letI : (rationalPrimeIdeal p).IsMaximal := hprimeIdeal.isMaximal hp0
  have hSset :
      Sset.ncard = Module.finrank ℚ F := by
    simpa [Sset] using hsplitF.1
  have hfinite : Sset.Finite := IsDedekindDomain.primesOver_finite (rationalPrimeIdeal p) OF
  letI : Fintype Sset := hfinite.fintype
  calc
    Nat.card Sset = Fintype.card Sset := Nat.card_eq_fintype_card
    _ = hfinite.toFinset.card := by
      exact Fintype.card_of_finset' hfinite.toFinset (fun Q => Set.Finite.mem_toFinset hfinite)
    _ = Sset.ncard := by
      symm
      exact Set.ncard_eq_toFinset_card Sset hfinite
    _ = Module.finrank ℚ F := hSset
    _ = NumberField.InfinitePlace.nrComplexPlaces K := by
      simpa [F] using hcomplexK.symm

lemma distance_level_relative
    {T : SplitTotallyTower.{0}} (data : DistanceGrowthData T) (j : ℕ)
    {K : Type*} [Field K] [NumberField K] [Algebra (T.fields j) K]
    (ι : T.fields j →+* K) (hι : algebraMap (T.fields j) K = ι) (ii : K)
    (_hii : ii ^ (2 : ℕ) = (-1 : K))
    (hspan : ∀ z : K, ∃ a b : T.fields j, z = ι a + ι b * ii)
    {p : ℕ} (hpS : p ∈ data.S)
    {Q : Ideal (NumberField.RingOfIntegers (T.fields j))}
    (hQ : Q ∈ Ideal.primesOver (rationalPrimeIdeal p)
      (NumberField.RingOfIntegers (T.fields j))) :
    Nat.card {P : Ideal (NumberField.RingOfIntegers K) //
        P ∈ Ideal.primesOver Q (NumberField.RingOfIntegers K)} = 2 := by
  classical
  let F := T.fields j
  let OF := NumberField.RingOfIntegers F
  let OK := NumberField.RingOfIntegers K
  letI : NumberField.IsTotallyReal F := T.totallyReal j
  let hquadratic : Algebra.IsQuadraticExtension F K :=
    cm_i_extension (ι := ι) (hι := hι) (ii := ii) _hii hspan
  rcases T.splitPrimes_spec (data.hS_split p hpS) with ⟨hp_prime, hp_mod, hsplitAll⟩
  have hsplitF : splitsCompletely F p := hsplitAll j
  let Sset : Set (Ideal OK) := Ideal.primesOver Q OK
  have hp0 : rationalPrimeIdeal p ≠ (⊥ : Ideal ℤ) := by
    simp [rationalPrimeIdeal, hp_prime.ne_zero]
  have hQ0 : Q ≠ ⊥ := Ideal.ne_bot_of_mem_primesOver hp0 hQ
  letI : Q.IsMaximal := hQ.1.isMaximal hQ0
  have hSset : Sset.ncard = 2 := by
    simpa [Sset, F, OF, OK] using
      distance_cm_adjoin
        (ι := ι) (hι := hι) (ii := ii) (_hii := _hii) (_hspan := hspan)
        (hquadratic := hquadratic) hp_prime hp_mod hsplitF hQ
  have hfinite : Sset.Finite := IsDedekindDomain.primesOver_finite Q OK
  letI : Fintype Sset := hfinite.fintype
  calc
    Nat.card Sset = Fintype.card Sset := Nat.card_eq_fintype_card
    _ = hfinite.toFinset.card := by
      exact Fintype.card_of_finset' hfinite.toFinset (fun P => Set.Finite.mem_toFinset hfinite)
    _ = Sset.ncard := by
      symm
      exact Set.ncard_eq_toFinset_card Sset hfinite
    _ = 2 := hSset

lemma distance_conjugate_self
    {T : SplitTotallyTower.{0}} (data : DistanceGrowthData T) (j : ℕ)
    {K : Type*} [Field K] [NumberField K] [Algebra (T.fields j) K]
    (ι : T.fields j →+* K) (hι : algebraMap (T.fields j) K = ι) (ii : K) (c : K ≃+* K)
    (_hii : ii ^ (2 : ℕ) = (-1 : K))
    (_hspan : ∀ z : K, ∃ a b : T.fields j, z = ι a + ι b * ii)
    (hc_base : ∀ a : T.fields j, c (ι a) = ι a)
    (hc_ii : c ii = -ii)
    {p : ℕ} (hpS : p ∈ data.S)
    {Q : Ideal (NumberField.RingOfIntegers (T.fields j))}
    (hQ : Q ∈ Ideal.primesOver (rationalPrimeIdeal p)
      (NumberField.RingOfIntegers (T.fields j)))
    {P : Ideal (NumberField.RingOfIntegers K)}
    (hP : P ∈ Ideal.primesOver Q (NumberField.RingOfIntegers K)) :
    Ideal.map
        (distanceCMIntegers c :
          NumberField.RingOfIntegers K →+* NumberField.RingOfIntegers K) P ≠ P := by
  let F := T.fields j
  rcases T.splitPrimes_spec (data.hS_split p hpS) with ⟨hp_prime, hp_mod, hsplitAll⟩
  have hsplitF : splitsCompletely F p := hsplitAll j
  simpa [F] using
    cm_adjoin_fix
      (ι := ι) (hι := hι) (ii := ii) (_hii := _hii)
      c hc_base hc_ii hp_prime hp_mod hsplitF hQ hP

structure DistanceLevelData
    {T : SplitTotallyTower.{0}} (data : DistanceGrowthData T) (j : ℕ)
    {K : Type*} [Field K] [NumberField K] [Algebra (T.fields j) K]
    (c : K ≃+* K) where
  d : ℕ
  hd : d = NumberField.InfinitePlace.nrComplexPlaces K
  Q : data.S.attach → Fin d → Ideal (NumberField.RingOfIntegers (T.fields j))
  P : data.S.attach → Fin d → Ideal (NumberField.RingOfIntegers K)
  Q_mem :
    ∀ s : data.S.attach, ∀ a : Fin d,
      Q s a ∈ Ideal.primesOver (rationalPrimeIdeal s.1)
        (NumberField.RingOfIntegers (T.fields j))
  Q_injective : ∀ s : data.S.attach, Function.Injective (Q s)
  Q_surjective :
    ∀ s : data.S.attach, ∀ Q' : Ideal (NumberField.RingOfIntegers (T.fields j)),
      Q' ∈ Ideal.primesOver (rationalPrimeIdeal s.1)
        (NumberField.RingOfIntegers (T.fields j)) →
      ∃ a : Fin d, Q s a = Q'
  P_mem :
    ∀ s : data.S.attach, ∀ a : Fin d,
      P s a ∈ Ideal.primesOver (Q s a) (NumberField.RingOfIntegers K)
  P_conj_ne :
    ∀ s : data.S.attach, ∀ a : Fin d,
      Ideal.map
          (distanceCMIntegers c :
            NumberField.RingOfIntegers K →+* NumberField.RingOfIntegers K)
          (P s a) ≠
        P s a

lemma distance_indexed_primes
    {T : SplitTotallyTower.{0}} (data : DistanceGrowthData T) (j : ℕ)
    {K : Type*} [Field K] [NumberField K]
    (ι : T.fields j →+* K) (ii : K) (c : K ≃+* K)
    (_hii : ii ^ (2 : ℕ) = (-1 : K))
    (hspan : ∀ z : K, ∃ a b : T.fields j, z = ι a + ι b * ii)
    (hc_base : ∀ a : T.fields j, c (ι a) = ι a)
    (hc_ii : c ii = -ii) :
    letI : Algebra (T.fields j) K := ι.toAlgebra
    Nonempty (DistanceLevelData data j c) := by
  classical
  letI : Algebra (T.fields j) K := ι.toAlgebra
  let d := NumberField.InfinitePlace.nrComplexPlaces K
  let OF := NumberField.RingOfIntegers (T.fields j)
  let OK := NumberField.RingOfIntegers K
  let p : data.S.attach → ℕ := fun s => s.1
  have hp_mem : ∀ s : data.S.attach, p s ∈ data.S := by
    intro s
    exact s.1.2
  have hp_prime : ∀ s : data.S.attach, Nat.Prime (p s) := by
    intro s
    exact (T.splitPrimes_spec (data.hS_split (p s) (hp_mem s))).1
  let QSet : data.S.attach → Set (Ideal OF) := fun s =>
    Ideal.primesOver (rationalPrimeIdeal (p s)) OF
  have hQfinite : ∀ s : data.S.attach, (QSet s).Finite := by
    intro s
    letI : (rationalPrimeIdeal (p s)).IsMaximal := rational_ideal_maximal (hp_prime s)
    simpa [QSet, p] using IsDedekindDomain.primesOver_finite (rationalPrimeIdeal (p s)) OF
  let QEquiv : (s : data.S.attach) → {Q : Ideal OF // Q ∈ QSet s} ≃ Fin d := by
    intro s
    letI : Fintype {Q : Ideal OF // Q ∈ QSet s} := (hQfinite s).fintype
    have hcard_nat : Nat.card {Q : Ideal OF // Q ∈ QSet s} = d := by
      simpa [QSet, d, OF, p] using
        nr_complex_places
          (T := T) (data := data) (j := j)
          (ι := ι) (ii := ii) _hii hspan (hpS := hp_mem s)
    have hcard : Fintype.card {Q : Ideal OF // Q ∈ QSet s} = d := by
      calc
        Fintype.card {Q : Ideal OF // Q ∈ QSet s}
            = Nat.card {Q : Ideal OF // Q ∈ QSet s} := by
                symm
                exact Nat.card_eq_fintype_card
        _ = d := hcard_nat
    exact Fintype.equivFinOfCardEq hcard
  let Q : data.S.attach → Fin d → Ideal OF := fun s a => ((QEquiv s).symm a).1
  have hQ_mem : ∀ s : data.S.attach, ∀ a : Fin d, Q s a ∈ QSet s := by
    intro s a
    exact ((QEquiv s).symm a).2
  have hQ_injective : ∀ s : data.S.attach, Function.Injective (Q s) := by
    intro s a b hab
    apply (QEquiv s).symm.injective
    exact Subtype.ext hab
  have hQ_surjective :
      ∀ s : data.S.attach, ∀ Q' : Ideal OF, Q' ∈ QSet s → ∃ a : Fin d, Q s a = Q' := by
    intro s Q' hQ'
    refine ⟨QEquiv s ⟨Q', hQ'⟩, ?_⟩
    simp [Q]
  let PSet : (s : data.S.attach) → Fin d → Set (Ideal OK) := fun s a =>
    Ideal.primesOver (Q s a) OK
  have hPfinite : ∀ s : data.S.attach, ∀ a : Fin d, (PSet s a).Finite := by
    intro s a
    letI : (rationalPrimeIdeal (p s)).IsMaximal := rational_ideal_maximal (hp_prime s)
    have hp0 :
        rationalPrimeIdeal (p s) ≠ (⊥ : Ideal ℤ) :=
      rational_ne_bot (hp_prime s)
    have hQ0 : Q s a ≠ ⊥ := Ideal.ne_bot_of_mem_primesOver hp0 (hQ_mem s a)
    letI : (Q s a).IsMaximal := (hQ_mem s a).1.isMaximal hQ0
    simpa [PSet] using IsDedekindDomain.primesOver_finite (Q s a) OK
  let PEquiv :
      (s : data.S.attach) → (a : Fin d) →
        {P : Ideal OK // P ∈ PSet s a} ≃ Fin 2 := by
    intro s a
    letI : Fintype {P : Ideal OK // P ∈ PSet s a} := (hPfinite s a).fintype
    have hcard_nat : Nat.card {P : Ideal OK // P ∈ PSet s a} = 2 := by
      simpa [PSet, OK] using
        distance_level_relative
          (T := T) (data := data) (j := j)
          (ι := ι) (hι := rfl) (ii := ii) _hii hspan (hpS := hp_mem s) (hQ := hQ_mem s a)
    have hcard : Fintype.card {P : Ideal OK // P ∈ PSet s a} = 2 := by
      calc
        Fintype.card {P : Ideal OK // P ∈ PSet s a}
            = Nat.card {P : Ideal OK // P ∈ PSet s a} := by
                symm
                exact Nat.card_eq_fintype_card
        _ = 2 := hcard_nat
    exact Fintype.equivFinOfCardEq hcard
  let P : data.S.attach → Fin d → Ideal OK := fun s a => ((PEquiv s a).symm 0).1
  have hP_mem : ∀ s : data.S.attach, ∀ a : Fin d, P s a ∈ PSet s a := by
    intro s a
    exact ((PEquiv s a).symm 0).2
  have hP_conj_ne :
      ∀ s : data.S.attach, ∀ a : Fin d,
        Ideal.map
            (distanceCMIntegers c :
              NumberField.RingOfIntegers K →+* NumberField.RingOfIntegers K)
            (P s a) ≠
          P s a := by
    intro s a
    exact
      distance_conjugate_self
        (T := T) (data := data) (j := j)
        (ι := ι) (hι := rfl) (ii := ii) (c := c)
        _hii hspan hc_base hc_ii (hpS := hp_mem s) (hQ := hQ_mem s a) (hP := hP_mem s a)
  refine ⟨{
    d := d
    hd := rfl
    Q := Q
    P := P
    Q_mem := ?_
    Q_injective := hQ_injective
    Q_surjective := ?_
    P_mem := ?_
    P_conj_ne := hP_conj_ne
  }⟩
  · intro s a
    simpa [QSet] using hQ_mem s a
  · intro s Q' hQ'
    exact hQ_surjective s Q' hQ'
  · intro s a
    simpa [PSet] using hP_mem s a

lemma rational_ideal {p q : ℕ} :
    rationalPrimeIdeal p = rationalPrimeIdeal q ↔ p = q := by
  constructor
  · intro h
    have hassoc : Associated (p : ℤ) (q : ℤ) := by
      simpa [rationalPrimeIdeal] using
        (Ideal.span_singleton_eq_span_singleton.mp h)
    have hnatAbs : (p : ℤ).natAbs = (q : ℤ).natAbs :=
      (Int.natAbs_eq_iff_associated).2 hassoc
    simpa using hnatAbs
  · intro h
    simp [h]

abbrev DistanceLevelIndex
    {T : SplitTotallyTower.{0}} {data : DistanceGrowthData T} {j : ℕ}
    {K : Type*} [Field K] [NumberField K] [Algebra (T.fields j) K]
    {c : K ≃+* K}
    (hpair : DistanceLevelData data j c) : Type :=
  data.S.attach × Fin hpair.d

def distanceLevelChoice
    {T : SplitTotallyTower.{0}} {data : DistanceGrowthData T} {j : ℕ}
    {K : Type*} [Field K] [NumberField K] [Algebra (T.fields j) K]
    (c : K ≃+* K)
    (hpair : DistanceLevelData data j c)
    (b : Bool) (i : DistanceLevelIndex hpair) :
    Ideal (NumberField.RingOfIntegers K) :=
  if b then
    Ideal.map
      (distanceCMIntegers c :
        NumberField.RingOfIntegers K →+* NumberField.RingOfIntegers K)
      (hpair.P i.1 i.2)
  else
    hpair.P i.1 i.2

def distanceLevelIdeal
    {T : SplitTotallyTower.{0}} {data : DistanceGrowthData T} {j : ℕ}
    {K : Type*} [Field K] [NumberField K] [Algebra (T.fields j) K]
    (c : K ≃+* K)
    (hpair : DistanceLevelData data j c)
    (η : DistanceLevelIndex hpair → Bool) :
    Ideal (NumberField.RingOfIntegers K) :=
  ∏ i : DistanceLevelIndex hpair,
    distanceLevelChoice c hpair (η i) i

lemma cm_conjugation_involutive
    {T : SplitTotallyTower.{0}} {j : ℕ}
    {K : Type*} [Field K] [NumberField K]
    (ι : T.fields j →+* K) (ii : K) (c : K ≃+* K)
    (hc_base : ∀ a : T.fields j, c (ι a) = ι a)
    (hc_ii : c ii = -ii)
    (hspan : ∀ z : K, ∃ a b : T.fields j, z = ι a + ι b * ii)
    (I : Ideal (NumberField.RingOfIntegers K)) :
    Ideal.map
        (distanceCMIntegers c :
          NumberField.RingOfIntegers K →+* NumberField.RingOfIntegers K)
        (Ideal.map
          (distanceCMIntegers c :
            NumberField.RingOfIntegers K →+* NumberField.RingOfIntegers K) I) =
      I := by
  rw [Ideal.map_map]
  have hcomp :
      ((distanceCMIntegers c :
          NumberField.RingOfIntegers K →+* NumberField.RingOfIntegers K).comp
        (distanceCMIntegers c :
          NumberField.RingOfIntegers K →+* NumberField.RingOfIntegers K)) =
        RingHom.id (NumberField.RingOfIntegers K) := by
    ext x
    exact congrArg (fun y : NumberField.RingOfIntegers K => (y : K))
      (distance_cm_involutive
        ι ii c hc_base hc_ii hspan x)
  rw [hcomp, Ideal.map_id]

lemma distance_level_split
    {T : SplitTotallyTower.{0}} (data : DistanceGrowthData T) (j : ℕ)
    {K : Type*} [Field K] [NumberField K] [Algebra (T.fields j) K]
    (ι : T.fields j →+* K) (hι : algebraMap (T.fields j) K = ι) (ii : K)
    (_hii : ii ^ (2 : ℕ) = (-1 : K))
    (hspan : ∀ z : K, ∃ a b : T.fields j, z = ι a + ι b * ii)
    {p : ℕ} (hpS : p ∈ data.S)
    {Q : Ideal (NumberField.RingOfIntegers (T.fields j))}
    (hQ : Q ∈ Ideal.primesOver (rationalPrimeIdeal p)
      (NumberField.RingOfIntegers (T.fields j)))
    {P : Ideal (NumberField.RingOfIntegers K)}
    (hP : P ∈ Ideal.primesOver Q (NumberField.RingOfIntegers K)) :
    Ideal.ramificationIdx Q P = 1 := by
  let F := T.fields j
  let OF := NumberField.RingOfIntegers F
  let OK := NumberField.RingOfIntegers K
  letI : NumberField.IsTotallyReal F := T.totallyReal j
  let hquadratic : Algebra.IsQuadraticExtension F K :=
    cm_i_extension (ι := ι) (hι := hι) (ii := ii) _hii hspan
  letI : Algebra.IsQuadraticExtension F K := hquadratic
  haveI : IsGalois F K := Algebra.IsQuadraticExtension.isGalois F K
  rcases T.splitPrimes_spec (data.hS_split p hpS) with ⟨hp_prime, hp_mod, hsplitAll⟩
  have hsplitF : splitsCompletely F p := hsplitAll j
  have hp0 : rationalPrimeIdeal p ≠ (⊥ : Ideal ℤ) := rational_ne_bot hp_prime
  have hQ0 : Q ≠ ⊥ := Ideal.ne_bot_of_mem_primesOver hp0 hQ
  have hP0 : P ≠ ⊥ := Ideal.ne_bot_of_mem_primesOver hQ0 hP
  letI : Q.IsPrime := hQ.1
  letI : Q.IsMaximal := hQ.1.isMaximal hQ0
  letI : P.IsPrime := hP.1
  letI : P.IsMaximal := hP.1.isMaximal hP0
  letI : P.LiesOver Q := hP.2
  have hrelcount : (Ideal.primesOver Q OK).ncard = 2 := by
    simpa [F, OF, OK] using
      distance_cm_adjoin
        (ι := ι) (hι := hι) (ii := ii) (_hii := _hii) (_hspan := hspan)
        (hquadratic := hquadratic) hp_prime hp_mod hsplitF hQ
  have hrelformula := Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn
    (p := Q) hQ0 OK (Gal(K / F))
  have hcardG : Nat.card Gal(K / F) = 2 := by
    simpa [Algebra.IsQuadraticExtension.finrank_eq_two F K] using
      (IsGalois.card_aut_eq_finrank F K)
  have hprodIn : Q.ramificationIdxIn OK * Q.inertiaDegIn OK = 1 := by
    have hrelformula' := hrelformula
    rw [hrelcount, hcardG] at hrelformula'
    exact Nat.eq_of_mul_eq_mul_left (by decide : 0 < 2) hrelformula'
  have hramifIn_one : Q.ramificationIdxIn OK = 1 := by
    exact Nat.eq_one_of_dvd_one ⟨Q.inertiaDegIn OK, hprodIn.symm⟩
  calc
    Ideal.ramificationIdx Q P = Q.ramificationIdxIn OK := by
          symm
          exact Ideal.ramificationIdxIn_eq_ramificationIdx
            (p := Q) (P := P) (G := Gal(K / F))
    _ = 1 := hramifIn_one

lemma distance_choice_base
    {T : SplitTotallyTower.{0}} {data : DistanceGrowthData T} {j : ℕ}
    {K : Type*} [Field K] [NumberField K] [Algebra (T.fields j) K]
    (ι : T.fields j →+* K) (hι : algebraMap (T.fields j) K = ι) (ii : K) (c : K ≃+* K)
    (_hii : ii ^ (2 : ℕ) = (-1 : K))
    (hc_base : ∀ a : T.fields j, c (ι a) = ι a)
    (hpair : DistanceLevelData data j c)
    (b : Bool) (i : DistanceLevelIndex hpair) :
    distanceLevelChoice c hpair b i ∈
      Ideal.primesOver (hpair.Q i.1 i.2) (NumberField.RingOfIntegers K) := by
  by_cases hb : b
  · subst hb
    simpa [distanceLevelChoice] using
      distance_cm_integers
        (F := T.fields j) (K := K) c
        (fun a => by simpa [hι] using hc_base a)
        (hpair.Q i.1 i.2) (hpair.P_mem i.1 i.2)
  · simpa [distanceLevelChoice, hb] using hpair.P_mem i.1 i.2

lemma distance_level_q
    {T : SplitTotallyTower.{0}} (data : DistanceGrowthData T) (j : ℕ)
    {K : Type*} [Field K] [NumberField K] [Algebra (T.fields j) K]
    (ι : T.fields j →+* K) (hι : algebraMap (T.fields j) K = ι) (ii : K) (c : K ≃+* K)
    (_hii : ii ^ (2 : ℕ) = (-1 : K))
    (hspan : ∀ z : K, ∃ a b : T.fields j, z = ι a + ι b * ii)
    (hc_base : ∀ a : T.fields j, c (ι a) = ι a)
    (_hc_ii : c ii = -ii)
    (hpair : DistanceLevelData data j c)
    (i : DistanceLevelIndex hpair) :
    (hpair.P i.1 i.2 : Ideal (NumberField.RingOfIntegers K)) *
        Ideal.map
          (distanceCMIntegers c :
            NumberField.RingOfIntegers K →+* NumberField.RingOfIntegers K)
          (hpair.P i.1 i.2) =
      Ideal.map
        (algebraMap (NumberField.RingOfIntegers (T.fields j))
          (NumberField.RingOfIntegers K))
        (hpair.Q i.1 i.2) := by
  classical
  let F := T.fields j
  letI : Field F := T.instField j
  letI : NumberField F := T.instNumberField j
  let OF := NumberField.RingOfIntegers F
  let OK := NumberField.RingOfIntegers K
  let cO : OK →+* OK := distanceCMIntegers c
  have hp_prime : Nat.Prime i.1.1 := (T.splitPrimes_spec (data.hS_split i.1.1 i.1.1.2)).1
  have hp0 : rationalPrimeIdeal i.1.1 ≠ (⊥ : Ideal ℤ) := rational_ne_bot hp_prime
  have hQ0 : hpair.Q i.1 i.2 ≠ ⊥ := Ideal.ne_bot_of_mem_primesOver hp0 (hpair.Q_mem i.1 i.2)
  letI : (hpair.Q i.1 i.2).IsPrime := (hpair.Q_mem i.1 i.2).1
  letI : (hpair.Q i.1 i.2).IsMaximal := (hpair.Q_mem i.1 i.2).1.isMaximal hQ0
  let Pfin : Finset (Ideal OK) := (IsDedekindDomain.primesOver_finite (hpair.Q i.1 i.2) OK).toFinset
  have hcard_finset :
      Pfin.card = 2 := by
    calc
      Pfin.card = Fintype.card {P : Ideal OK // P ∈ Ideal.primesOver (hpair.Q i.1 i.2) OK} := by
        symm
        exact Fintype.card_of_finset' Pfin
          (fun P => (Set.Finite.mem_toFinset (IsDedekindDomain.primesOver_finite (hpair.Q i.1
            i.2) OK)))
      _ = Nat.card {P : Ideal OK // P ∈ Ideal.primesOver (hpair.Q i.1 i.2) OK} := by
        symm
        exact Nat.card_eq_fintype_card
      _ = 2 := by
        simpa [OK] using
          distance_level_relative
            (T := T) (data := data) (j := j)
            (ι := ι) (hι := hι) (ii := ii) _hii hspan
            (hpS := i.1.1.2) (hQ := hpair.Q_mem i.1 i.2)
  have hconj_mem :
      Ideal.map cO (hpair.P i.1 i.2) ∈ Ideal.primesOver (hpair.Q i.1 i.2) OK := by
    simpa [distanceLevelChoice] using
      distance_choice_base
        (ι := ι) (hι := hι) (ii := ii) (c := c) (_hii := _hii)
        (hc_base := hc_base) hpair true i
  have htwo_eq :
      {hpair.P i.1 i.2, Ideal.map cO (hpair.P i.1 i.2)} =
        Pfin := by
    refine Finset.eq_of_subset_of_card_le ?_ ?_
    · intro P hP
      simp only [Finset.mem_insert, Finset.mem_singleton] at hP
      rcases hP with rfl | rfl
      · exact (Set.Finite.mem_toFinset (IsDedekindDomain.primesOver_finite (hpair.Q i.1 i.2) OK)).2
          (hpair.P_mem i.1 i.2)
      · exact (Set.Finite.mem_toFinset (IsDedekindDomain.primesOver_finite (hpair.Q i.1 i.2)
        OK)).2 hconj_mem
    · rw [hcard_finset]
      rw [Finset.card_pair (hpair.P_conj_ne i.1 i.2).symm]
  have hramif_one :
      ∀ P ∈ Pfin,
        Ideal.ramificationIdx (hpair.Q i.1 i.2) P = 1 := by
    intro P hP
    have hPset : P ∈ Ideal.primesOver (hpair.Q i.1 i.2) OK :=
      (Set.Finite.mem_toFinset (IsDedekindDomain.primesOver_finite (hpair.Q i.1 i.2) OK)).1 hP
    exact
      distance_level_split
        (T := T) (data := data) (j := j)
        (ι := ι) (hι := hι) (ii := ii) _hii hspan
        (hpS := i.1.1.2) (hQ := hpair.Q_mem i.1 i.2) (hP := hPset)
  calc
    (hpair.P i.1 i.2 : Ideal OK) *
        Ideal.map cO (hpair.P i.1 i.2) =
      ∏ P ∈ Pfin, P := by
        rw [← htwo_eq]
        rw [Finset.prod_insert]
        · rw [Finset.prod_singleton]
        · simpa [Finset.mem_singleton] using (hpair.P_conj_ne i.1 i.2).symm
    _ =
      ∏ P ∈ Pfin,
        P ^ Ideal.ramificationIdx (hpair.Q i.1 i.2) P := by
      apply Finset.prod_congr rfl
      intro P hP
      rw [hramif_one P hP, pow_one]
    _ = Ideal.map (algebraMap OF OK) (hpair.Q i.1 i.2) := by
      symm
      simpa [Pfin, OF, OK] using
        (Ideal.map_algebraMap_eq_finsetProd_pow
          (R := NumberField.RingOfIntegers K) (p := hpair.Q i.1 i.2) hQ0)

lemma distance_level_base
    {T : SplitTotallyTower.{0}} (data : DistanceGrowthData T) (j : ℕ)
    {K : Type*} [Field K] [NumberField K] [Algebra (T.fields j) K]
    (ii : K) (c : K ≃+* K)
    (_hii : ii ^ (2 : ℕ) = (-1 : K))
    (hpair : DistanceLevelData data j c)
    (s : data.S.attach) :
    ∏ a : Fin hpair.d, hpair.Q s a =
      Ideal.span
        ({((s.1 : ℕ) : NumberField.RingOfIntegers (T.fields j))} :
          Set (NumberField.RingOfIntegers (T.fields j))) := by
  classical
  let F := T.fields j
  let OF := NumberField.RingOfIntegers F
  have hp_prime : Nat.Prime s.1 := (T.splitPrimes_spec (data.hS_split s.1 s.1.2)).1
  have hp0 : rationalPrimeIdeal s.1 ≠ (⊥ : Ideal ℤ) := rational_ne_bot hp_prime
  letI : (rationalPrimeIdeal s.1).IsMaximal := rational_ideal_maximal hp_prime
  have hsplitF : splitsCompletely F s.1 := (T.splitPrimes_spec (data.hS_split s.1 s.1.2)).2.2 j
  let Qfin : Finset (Ideal OF) := (IsDedekindDomain.primesOver_finite (rationalPrimeIdeal s.1)
    OF).toFinset
  have himage :
      (Finset.univ.image (hpair.Q s)) = Qfin := by
    apply Finset.ext
    intro Q
    constructor
    · intro hQ
      rcases Finset.mem_image.mp hQ with ⟨a, -, rfl⟩
      exact (Set.Finite.mem_toFinset (IsDedekindDomain.primesOver_finite (rationalPrimeIdeal
        s.1) OF)).2
        (hpair.Q_mem s a)
    · intro hQ
      have hQset : Q ∈ Ideal.primesOver (rationalPrimeIdeal s.1) OF :=
        (Set.Finite.mem_toFinset (IsDedekindDomain.primesOver_finite (rationalPrimeIdeal s.1)
          OF)).1 hQ
      rcases hpair.Q_surjective s Q hQset with ⟨a, rfl⟩
      exact Finset.mem_image.mpr ⟨a, Finset.mem_univ a, rfl⟩
  have hprod_primes :
      ∏ a : Fin hpair.d, hpair.Q s a =
        ∏ Q ∈ Qfin, Q := by
    rw [← himage]
    symm
    refine Finset.prod_image ?_
    intro a _ b _ hab
    exact hpair.Q_injective s hab
  calc
    ∏ a : Fin hpair.d, hpair.Q s a =
        ∏ Q ∈ Qfin,
          Q ^ Ideal.ramificationIdx (rationalPrimeIdeal s.1) Q := by
          rw [hprod_primes]
          apply Finset.prod_congr rfl
          intro Q hQ
          have hQset : Q ∈ Ideal.primesOver (rationalPrimeIdeal s.1) OF :=
            (Set.Finite.mem_toFinset (IsDedekindDomain.primesOver_finite (rationalPrimeIdeal
              s.1) OF)).1 hQ
          rw [(hsplitF.2 Q hQset).1, pow_one]
    _ = Ideal.map (algebraMap ℤ OF) (rationalPrimeIdeal s.1) := by
      symm
      simpa [Qfin, OF, F] using
        (Ideal.map_algebraMap_eq_finsetProd_pow
          (R := NumberField.RingOfIntegers (T.fields j)) (p := rationalPrimeIdeal s.1) hp0)
    _ = Ideal.span
        ({((s.1 : ℕ) : OF)} : Set OF) := by
          rw [rationalPrimeIdeal, Ideal.map_span, Set.image_singleton]
          congr 1
          simp

lemma distance_choice_ideal
    {T : SplitTotallyTower.{0}} {data : DistanceGrowthData T} {j : ℕ}
    {K : Type*} [Field K] [NumberField K] [Algebra (T.fields j) K]
    (ι : T.fields j →+* K) (hι : algebraMap (T.fields j) K = ι) (ii : K) (c : K ≃+* K)
    (_hii : ii ^ (2 : ℕ) = (-1 : K))
    (hc_base : ∀ a : T.fields j, c (ι a) = ι a)
    (hpair : DistanceLevelData data j c)
    {bi bj : Bool} {i j' : DistanceLevelIndex hpair} :
    distanceLevelChoice c hpair bi i =
        distanceLevelChoice c hpair bj j' ↔
      i = j' ∧ bi = bj := by
  let F := T.fields j
  let OF := NumberField.RingOfIntegers F
  constructor
  · intro hij
    have hi_mem :=
      distance_choice_base
        (ι := ι) (hι := hι) (ii := ii) (c := c) (_hii := _hii)
        (hc_base := hc_base) hpair bi i
    have hj_mem :=
      distance_choice_base
        (ι := ι) (hι := hι) (ii := ii) (c := c) (_hii := _hii)
        (hc_base := hc_base) hpair bj j'
    have hQ_eq : hpair.Q i.1 i.2 = hpair.Q j'.1 j'.2 := by
      calc
        hpair.Q i.1 i.2 =
            Ideal.under OF (distanceLevelChoice c hpair bi i) := hi_mem.2.over
        _ = Ideal.under OF (distanceLevelChoice c hpair bj j') := by rw [hij]
        _ = hpair.Q j'.1 j'.2 := hj_mem.2.over.symm
    have hp_eq : (i.1.1 : ℕ) = (j'.1.1 : ℕ) := by
      have hr_eq :
          rationalPrimeIdeal (i.1.1 : ℕ) = rationalPrimeIdeal (j'.1.1 : ℕ) := by
        calc
          rationalPrimeIdeal i.1.1 =
              Ideal.under ℤ (hpair.Q i.1 i.2) := (hpair.Q_mem i.1 i.2).2.over
          _ = Ideal.under ℤ (hpair.Q j'.1 j'.2) := by rw [hQ_eq]
          _ = rationalPrimeIdeal j'.1.1 := (hpair.Q_mem j'.1 j'.2).2.over.symm
      exact (rational_ideal.mp hr_eq)
    have hs_eq_inner : (i.1.1 : data.S) = j'.1.1 := Subtype.ext hp_eq
    have hs_eq : i.1 = j'.1 := Subtype.ext hs_eq_inner
    have ha_eq : i.2 = j'.2 := by
      apply hpair.Q_injective i.1
      simpa [hs_eq] using hQ_eq
    have hij_idx : i = j' := by
      cases i
      cases j'
      cases hs_eq
      cases ha_eq
      rfl
    cases bi <;> cases bj
    · exact ⟨hij_idx, rfl⟩
    · exfalso
      have hbad :
          Ideal.map
              (distanceCMIntegers c :
                NumberField.RingOfIntegers K →+* NumberField.RingOfIntegers K)
              (hpair.P i.1 i.2) =
            hpair.P i.1 i.2 := by
        simpa [distanceLevelChoice, hij_idx] using hij.symm
      exact (hpair.P_conj_ne i.1 i.2) hbad
    · exfalso
      have hbad :
          Ideal.map
              (distanceCMIntegers c :
                NumberField.RingOfIntegers K →+* NumberField.RingOfIntegers K)
              (hpair.P i.1 i.2) =
            hpair.P i.1 i.2 := by
        simpa [distanceLevelChoice, hij_idx] using hij
      exact (hpair.P_conj_ne i.1 i.2) hbad
    · exact ⟨hij_idx, rfl⟩
  · rintro ⟨rfl, rfl⟩
    rfl

lemma distance_level_choice
    {T : SplitTotallyTower.{0}} (data : DistanceGrowthData T) (j : ℕ)
    {K : Type*} [Field K] [NumberField K] [Algebra (T.fields j) K]
    (ι : T.fields j →+* K) (hι : algebraMap (T.fields j) K = ι) (ii : K) (c : K ≃+* K)
    (_hii : ii ^ (2 : ℕ) = (-1 : K))
    (hspan : ∀ z : K, ∃ a b : T.fields j, z = ι a + ι b * ii)
    (hc_base : ∀ a : T.fields j, c (ι a) = ι a)
    (_hc_ii : c ii = -ii)
    (hpair : DistanceLevelData data j c)
    (b : Bool) (i : DistanceLevelIndex hpair) :
    distanceLevelChoice c hpair b i *
        Ideal.map
          (distanceCMIntegers c :
            NumberField.RingOfIntegers K →+* NumberField.RingOfIntegers K)
          (distanceLevelChoice c hpair b i) =
      Ideal.map
        (algebraMap (NumberField.RingOfIntegers (T.fields j))
          (NumberField.RingOfIntegers K))
        (hpair.Q i.1 i.2) := by
  cases b
  · simpa [distanceLevelChoice] using
      distance_level_q
        (T := T) (data := data) (j := j)
        (ι := ι) (hι := hι) (ii := ii) (c := c)
        _hii hspan hc_base _hc_ii hpair i
  · have hmapmap :
        Ideal.map
            (distanceCMIntegers c :
              NumberField.RingOfIntegers K →+* NumberField.RingOfIntegers K)
            (Ideal.map
              (distanceCMIntegers c :
                NumberField.RingOfIntegers K →+* NumberField.RingOfIntegers K)
              (hpair.P i.1 i.2)) =
          hpair.P i.1 i.2 :=
      cm_conjugation_involutive
        (T := T) (j := j) (ι := ι) (ii := ii) (c := c)
        hc_base _hc_ii hspan (hpair.P i.1 i.2)
    calc
      distanceLevelChoice c hpair true i *
          Ideal.map
            (distanceCMIntegers c :
              NumberField.RingOfIntegers K →+* NumberField.RingOfIntegers K)
            (distanceLevelChoice c hpair true i)
          =
        Ideal.map
            (distanceCMIntegers c :
              NumberField.RingOfIntegers K →+* NumberField.RingOfIntegers K)
            (hpair.P i.1 i.2) *
          Ideal.map
            (distanceCMIntegers c :
              NumberField.RingOfIntegers K →+* NumberField.RingOfIntegers K)
            (Ideal.map
              (distanceCMIntegers c :
                NumberField.RingOfIntegers K →+* NumberField.RingOfIntegers K)
              (hpair.P i.1 i.2)) := by
              simp [distanceLevelChoice]
      _ =
        Ideal.map
            (distanceCMIntegers c :
              NumberField.RingOfIntegers K →+* NumberField.RingOfIntegers K)
            (hpair.P i.1 i.2) *
          hpair.P i.1 i.2 := by rw [hmapmap]
      _ =
        (hpair.P i.1 i.2 : Ideal (NumberField.RingOfIntegers K)) *
          Ideal.map
            (distanceCMIntegers c :
              NumberField.RingOfIntegers K →+* NumberField.RingOfIntegers K)
            (hpair.P i.1 i.2) := by ac_rfl
      _ =
        Ideal.map
          (algebraMap (NumberField.RingOfIntegers (T.fields j))
            (NumberField.RingOfIntegers K))
          (hpair.Q i.1 i.2) := by
            exact
              distance_level_q
                (T := T) (data := data) (j := j)
                (ι := ι) (hι := hι) (ii := ii) (c := c)
                _hii hspan hc_base _hc_ii hpair i

lemma distance_level_conj
    {T : SplitTotallyTower.{0}} (data : DistanceGrowthData T) (j : ℕ)
    {K : Type*} [Field K] [NumberField K] [Algebra (T.fields j) K]
    (ι : T.fields j →+* K) (hι : algebraMap (T.fields j) K = ι) (ii : K) (c : K ≃+* K)
    (_hii : ii ^ (2 : ℕ) = (-1 : K))
    (hspan : ∀ z : K, ∃ a b : T.fields j, z = ι a + ι b * ii)
    (hc_base : ∀ a : T.fields j, c (ι a) = ι a)
    (_hc_ii : c ii = -ii)
    (hpair : DistanceLevelData data j c)
    (η : DistanceLevelIndex hpair → Bool) :
    distanceLevelIdeal c hpair η *
        Ideal.map
          (distanceCMIntegers c :
            NumberField.RingOfIntegers K →+* NumberField.RingOfIntegers K)
          (distanceLevelIdeal c hpair η) =
      Ideal.span
        ({((data.S.prod fun p => p) : NumberField.RingOfIntegers K)} :
          Set (NumberField.RingOfIntegers K)) := by
  classical
  let F := T.fields j
  let OF := NumberField.RingOfIntegers F
  let OK := NumberField.RingOfIntegers K
  let cO : OK →+* OK := distanceCMIntegers c
  have hmap_family :
      Ideal.map cO (distanceLevelIdeal c hpair η) =
        ∏ i : DistanceLevelIndex hpair,
          Ideal.map cO (distanceLevelChoice c hpair (η i) i) := by
    unfold distanceLevelIdeal
    exact
      map_prod (Ideal.mapHom cO)
        (fun i : DistanceLevelIndex hpair =>
          distanceLevelChoice c hpair (η i) i)
        Finset.univ
  calc
    distanceLevelIdeal c hpair η *
        Ideal.map cO (distanceLevelIdeal c hpair η) =
      ∏ i : DistanceLevelIndex hpair,
        (distanceLevelChoice c hpair (η i) i *
          Ideal.map cO (distanceLevelChoice c hpair (η i) i)) := by
            rw [hmap_family]
            unfold distanceLevelIdeal
            rw [← Finset.prod_mul_distrib]
    _ =
      ∏ i : DistanceLevelIndex hpair,
        Ideal.map (algebraMap OF OK) (hpair.Q i.1 i.2) := by
          exact Fintype.prod_congr _ _
            (fun i =>
              distance_level_choice
                (T := T) (data := data) (j := j)
                (ι := ι) (hι := hι) (ii := ii) (c := c)
                _hii hspan hc_base _hc_ii hpair (η i) i)
    _ =
      ∏ s : data.S.attach, ∏ a : Fin hpair.d,
        Ideal.map (algebraMap OF OK) (hpair.Q s a) := by
          simpa [DistanceLevelIndex] using
            (Fintype.prod_prod_type (fun i : data.S.attach × Fin hpair.d =>
              Ideal.map (algebraMap OF OK) (hpair.Q i.1 i.2)))
    _ =
      ∏ s : data.S.attach,
        Ideal.map (algebraMap OF OK)
          (Ideal.span ({((s.1 : ℕ) : OF)} : Set OF)) := by
          exact Fintype.prod_congr _ _ (fun s => by
            calc
              ∏ a : Fin hpair.d, Ideal.map (algebraMap OF OK) (hpair.Q s a) =
                  Ideal.map (algebraMap OF OK) (∏ a : Fin hpair.d, hpair.Q s a) := by
                    exact
                      (map_prod (Ideal.mapHom (algebraMap OF OK))
                        (fun a : Fin hpair.d => hpair.Q s a) Finset.univ).symm
              _ =
                  Ideal.map (algebraMap OF OK)
                    (Ideal.span ({((s.1 : ℕ) : OF)} : Set OF)) := by
                      rw [distance_level_base
                        (T := T) (data := data) (j := j)
                        (ii := ii) (c := c) _hii hpair s])
    _ =
      ∏ s : data.S.attach, Ideal.span ({((s.1 : ℕ) : OK)} : Set OK) := by
        exact Fintype.prod_congr _ _ (fun s => by
          rw [Ideal.map_span, Set.image_singleton]
          rw [map_natCast (algebraMap OF OK) (s.1 : ℕ)])
    _ =
      Ideal.span ({((data.S.prod fun p => p) : OK)} : Set OK) := by
        calc
          ∏ s : data.S.attach, Ideal.span ({((s.1 : ℕ) : OK)} : Set OK)
              = ∏ s ∈ data.S.attach.attach, Ideal.span ({((s.1.1 : ℕ) : OK)} : Set OK) := by
                  rw [Finset.univ_eq_attach]
          _ = ∏ s ∈ data.S.attach, Ideal.span ({((s.1 : ℕ) : OK)} : Set OK) := by
                  simpa using
                    (Finset.prod_attach data.S.attach
                      (fun s : { x : ℕ // x ∈ data.S } =>
                        Ideal.span ({((s.1 : ℕ) : OK)} : Set OK)))
          _ = Ideal.span ({((data.S.attach.prod fun s => (s.1 : ℕ)) : OK)} : Set OK) := by
                  simpa using
                    (Ideal.prod_span_singleton data.S.attach
                      (fun s => ((s.1 : ℕ) : OK)))
          _ = Ideal.span ({((data.S.prod fun p => p) : OK)} : Set OK) := by
                  have hprod :
                      ∏ s ∈ data.S.attach, ((s.1 : ℕ) : OK) =
                        ∏ p ∈ data.S, ((p : ℕ) : OK) := by
                    simpa using (Finset.prod_attach data.S (fun p : ℕ => ((p : ℕ) : OK)))
                  simpa using congrArg (fun x : OK => Ideal.span ({x} : Set OK)) hprod

lemma distance_level_injective
    {T : SplitTotallyTower.{0}} (data : DistanceGrowthData T) (j : ℕ)
    {K : Type*} [Field K] [NumberField K] [Algebra (T.fields j) K]
    (ι : T.fields j →+* K) (hι : algebraMap (T.fields j) K = ι) (ii : K) (c : K ≃+* K)
    (_hii : ii ^ (2 : ℕ) = (-1 : K))
    (hc_base : ∀ a : T.fields j, c (ι a) = ι a)
    (hpair : DistanceLevelData data j c) :
    Function.Injective (distanceLevelIdeal c hpair) := by
  classical
  let F := T.fields j
  let OF := NumberField.RingOfIntegers F
  let OK := NumberField.RingOfIntegers K
  intro η θ hEq
  funext i
  let J : Ideal OK := distanceLevelChoice c hpair (η i) i
  have hJ_mem :
      J ∈ Ideal.primesOver (hpair.Q i.1 i.2) OK := by
    dsimp [J]
    exact
      distance_choice_base
        (ι := ι) (hι := hι) (ii := ii) (c := c) (_hii := _hii)
        (hc_base := hc_base) hpair (η i) i
  have hp_prime_i : Nat.Prime i.1.1 := (T.splitPrimes_spec (data.hS_split i.1.1 i.1.1.2)).1
  have hQ0_i : hpair.Q i.1 i.2 ≠ ⊥ := by
    exact Ideal.ne_bot_of_mem_primesOver (rational_ne_bot hp_prime_i)
      (hpair.Q_mem i.1 i.2)
  have hJ0 : J ≠ ⊥ := Ideal.ne_bot_of_mem_primesOver hQ0_i hJ_mem
  have hJprime : J.IsPrime := hJ_mem.1
  have hη_le : distanceLevelIdeal c hpair η ≤ J := by
    dsimp [distanceLevelIdeal, J]
    rw [Fintype.prod_eq_mul_prod_compl i
      (fun j => distanceLevelChoice c hpair (η j) j)]
    exact Ideal.mul_le_right
  have hθ_le : distanceLevelIdeal c hpair θ ≤ J := by
    rw [← hEq]
    exact hη_le
  have hθ_factor_le :
      ∃ j : DistanceLevelIndex hpair,
        distanceLevelChoice c hpair (θ j) j ≤ J := by
    have hθ_le' :
        ∏ j ∈ (Finset.univ : Finset (DistanceLevelIndex hpair)),
          distanceLevelChoice c hpair (θ j) j ≤ J := by
      simpa [distanceLevelIdeal] using hθ_le
    have hiff := Ideal.IsPrime.prod_le
      (s := (Finset.univ : Finset (DistanceLevelIndex hpair)))
      (f := fun j => distanceLevelChoice c hpair (θ j) j)
      hJprime
    rcases hiff.mp hθ_le' with ⟨j, -, hjle⟩
    exact ⟨j, hjle⟩
  rcases hθ_factor_le with ⟨j, hjle⟩
  have hj_mem :
      distanceLevelChoice c hpair (θ j) j ∈
        Ideal.primesOver (hpair.Q j.1 j.2) OK := by
    exact
      distance_choice_base
        (ι := ι) (hι := hι) (ii := ii) (c := c) (_hii := _hii)
        (hc_base := hc_base) hpair (θ j) j
  have hp_prime_j : Nat.Prime j.1.1 := (T.splitPrimes_spec (data.hS_split j.1.1 j.1.1.2)).1
  have hQ0_j : hpair.Q j.1 j.2 ≠ ⊥ := by
    exact Ideal.ne_bot_of_mem_primesOver (rational_ne_bot hp_prime_j)
      (hpair.Q_mem j.1 j.2)
  have hj0 :
      distanceLevelChoice c hpair (θ j) j ≠ ⊥ :=
    Ideal.ne_bot_of_mem_primesOver hQ0_j hj_mem
  have hjmax :
      (distanceLevelChoice c hpair (θ j) j).IsMaximal :=
    hj_mem.1.isMaximal hj0
  have hchoice_eq :
      distanceLevelChoice c hpair (θ j) j = J :=
    Ideal.IsMaximal.eq_of_le hjmax hJprime.ne_top hjle
  have hij :
      i = j ∧ η i = θ j := by
    exact
      (distance_choice_ideal
        (ι := ι) (hι := hι) (ii := ii) (c := c) (_hii := _hii)
        (hc_base := hc_base) hpair).1 hchoice_eq.symm
  simpa [hij.1] using hij.2

lemma indexed_cm_split
    {T : SplitTotallyTower.{0}} (data : DistanceGrowthData T) (j : ℕ)
    {K : Type*} [Field K] [NumberField K]
    (ι : T.fields j →+* K) (ii : K) (c : K ≃+* K)
    (hii : ii ^ (2 : ℕ) = (-1 : K))
    (hspan : ∀ z : K, ∃ a b : T.fields j, z = ι a + ι b * ii)
    (hc_base : ∀ a : T.fields j, c (ι a) = ι a)
    (_hc_ii : c ii = -ii)
    (hpair :
      letI : Algebra (T.fields j) K := ι.toAlgebra
      DistanceLevelData data j c) :
    ∃ m : ℕ, ∃ A0 : Fin m → NonzeroIntegersIdeal K,
      (((2 : ℝ) ^ data.S.card) ^ NumberField.InfinitePlace.nrComplexPlaces K) ≤ m ∧
      Function.Injective A0 ∧
      (∀ a : Fin m,
        (A0 a : Ideal (NumberField.RingOfIntegers K)) *
            Ideal.map
              (distanceCMIntegers c :
                NumberField.RingOfIntegers K →+* NumberField.RingOfIntegers K)
              (A0 a : Ideal (NumberField.RingOfIntegers K)) =
          Ideal.span
            ({((data.S.prod fun p => p) : NumberField.RingOfIntegers K)} :
              Set (NumberField.RingOfIntegers K))) := by
  classical
  letI : Algebra (T.fields j) K := ι.toAlgebra
  let OK := NumberField.RingOfIntegers K
  let Index : Type := DistanceLevelIndex hpair
  let Sign : Type := Index → Bool
  let m : ℕ := Fintype.card Sign
  let e : Fin m ≃ Sign := (Fintype.equivFinOfCardEq rfl).symm
  have hprincipal :
      ∀ η : Sign,
        distanceLevelIdeal c hpair η *
            Ideal.map
              (distanceCMIntegers c :
                OK →+* OK)
              (distanceLevelIdeal c hpair η) =
          Ideal.span ({((data.S.prod fun p => p) : OK)} : Set OK) := by
    intro η
    exact
      distance_level_conj
        (T := T) (data := data) (j := j)
        (ι := ι) (hι := rfl) (ii := ii) (c := c)
        hii hspan hc_base _hc_ii hpair η
  have hprod_pos : 0 < data.S.prod fun p => p := by
    refine Finset.prod_pos ?_
    intro p hp
    exact Nat.Prime.pos ((T.splitPrimes_spec (data.hS_split p hp)).1)
  have hprincipal_ne_bot :
      Ideal.span ({((data.S.prod fun p => p) : OK)} : Set OK) ≠ ⊥ := by
    have hcast_ne_zero : (data.S.prod fun p => (p : OK)) ≠ 0 := by
      refine Finset.prod_ne_zero_iff.mpr ?_
      intro p hp
      exact Nat.cast_ne_zero.mpr (Nat.Prime.ne_zero ((T.splitPrimes_spec (data.hS_split p hp)).1))
    simpa [Ideal.span_singleton_eq_bot] using hcast_ne_zero
  let A0 : Fin m → NonzeroIntegersIdeal K := fun a =>
    let I : Ideal OK := distanceLevelIdeal c hpair (e a)
    have hI0 : I ≠ ⊥ := by
      intro hI0
      have hzero :
          (⊥ : Ideal OK) = Ideal.span ({((data.S.prod fun p => p) : OK)} : Set OK) := by
        simpa [I, hI0] using hprincipal (e a)
      exact hprincipal_ne_bot hzero.symm
    ⟨I, mem_nonZeroDivisors_iff_ne_zero.mpr hI0⟩
  have hm_card : m = 2 ^ (data.S.card * hpair.d) := by
    dsimp [m, Sign, Index, DistanceLevelIndex]
    simp [Fintype.card_prod]
  have hcard :
      (((2 : ℝ) ^ data.S.card) ^ NumberField.InfinitePlace.nrComplexPlaces K) ≤ m := by
    have hm_real : (2 : ℝ) ^ (data.S.card * hpair.d) = m := by
      exact_mod_cast hm_card.symm
    apply le_of_eq
    calc
      (((2 : ℝ) ^ data.S.card) ^ NumberField.InfinitePlace.nrComplexPlaces K)
          = (2 : ℝ) ^ (data.S.card * NumberField.InfinitePlace.nrComplexPlaces K) := by
              rw [pow_mul]
      _ = (2 : ℝ) ^ (data.S.card * hpair.d) := by simp [hpair.hd]
      _ = m := hm_real
  have hA0_inj : Function.Injective A0 := by
    intro a b hab
    apply e.injective
    exact
      distance_level_injective
        (T := T) (data := data) (j := j)
        (ι := ι) (hι := rfl) (ii := ii) (c := c)
        hii hc_base hpair
        (congrArg (fun I : NonzeroIntegersIdeal K => (I : Ideal OK)) hab)
  have hA0_mul :
      ∀ a : Fin m,
        (A0 a : Ideal OK) *
            Ideal.map
              (distanceCMIntegers c :
                OK →+* OK)
              (A0 a : Ideal OK) =
          Ideal.span ({((data.S.prod fun p => p) : OK)} : Set OK) := by
    intro a
    exact hprincipal (e a)
  exact ⟨m, A0, hcard, hA0_inj, hA0_mul⟩

lemma indexed_cm_family
    {T : SplitTotallyTower.{0}} (data : DistanceGrowthData T) (j : ℕ)
    {K : Type*} [Field K] [NumberField K]
    (ι : T.fields j →+* K) (ii : K) (c : K ≃+* K)
    (_hii : ii ^ (2 : ℕ) = (-1 : K))
    (hspan : ∀ z : K, ∃ a b : T.fields j, z = ι a + ι b * ii)
    (hc_base : ∀ a : T.fields j, c (ι a) = ι a)
    (hc_ii : c ii = -ii)
    (_hS_splitK :
      ∀ p ∈ data.S,
        Nat.Prime p ∧ p % 4 = 1 ∧
        (Ideal.primesOver (rationalPrimeIdeal p) (NumberField.RingOfIntegers K)).ncard =
          Module.finrank ℚ K ∧
        (∀ P ∈ Ideal.primesOver (rationalPrimeIdeal p) (NumberField.RingOfIntegers K),
          Ideal.ramificationIdx (rationalPrimeIdeal p) P = 1 ∧
            Ideal.inertiaDeg (rationalPrimeIdeal p) P = 1)) :
    ∃ m : ℕ, ∃ A0 : Fin m → NonzeroIntegersIdeal K,
      (((2 : ℝ) ^ data.S.card) ^ NumberField.InfinitePlace.nrComplexPlaces K) ≤ m ∧
      Function.Injective A0 ∧
      (∀ a : Fin m,
        (A0 a : Ideal (NumberField.RingOfIntegers K)) *
            Ideal.map
              (distanceCMIntegers c :
                NumberField.RingOfIntegers K →+* NumberField.RingOfIntegers K)
              (A0 a : Ideal (NumberField.RingOfIntegers K)) =
          Ideal.span
            ({((data.S.prod fun p => p) : NumberField.RingOfIntegers K)} :
              Set (NumberField.RingOfIntegers K))) := by
  letI : Algebra (T.fields j) K := ι.toAlgebra
  rcases
      distance_indexed_primes
        data j ι ii c _hii hspan hc_base hc_ii with
    ⟨hpair⟩
  exact
    indexed_cm_split
      data j ι ii c _hii hspan hc_base hc_ii hpair

lemma distance_promote_cm
    {T : SplitTotallyTower.{0}} (data : DistanceGrowthData T) (j : ℕ)
    {K : Type*} [Field K] [NumberField K]
    (ι : T.fields j →+* K) (ii : K) (c : K ≃+* K)
    (_hii : ii ^ (2 : ℕ) = (-1 : K))
    (hspan : ∀ z : K, ∃ a b : T.fields j, z = ι a + ι b * ii)
    (hc_base : ∀ a : T.fields j, c (ι a) = ι a)
    (hc_ii : c ii = -ii)
    (hS_splitK :
      ∀ p ∈ data.S,
        Nat.Prime p ∧ p % 4 = 1 ∧
        (Ideal.primesOver (rationalPrimeIdeal p) (NumberField.RingOfIntegers K)).ncard =
          Module.finrank ℚ K ∧
        (∀ P ∈ Ideal.primesOver (rationalPrimeIdeal p) (NumberField.RingOfIntegers K),
          Ideal.ramificationIdx (rationalPrimeIdeal p) P = 1 ∧
            Ideal.inertiaDeg (rationalPrimeIdeal p) P = 1)) :
    ∃ n : ℕ, ∃ A : Fin n → NonzeroIntegersIdeal K,
      (((2 : ℝ) ^ data.S.card) ^ NumberField.InfinitePlace.nrComplexPlaces K) /
          (NumberField.classNumber K : ℝ) ≤ n ∧
      Function.Injective A ∧
      (∃ C : ClassGroup (NumberField.RingOfIntegers K),
        ∀ a : Fin n, ClassGroup.mk0 (A a) = C) ∧
      (∀ a : Fin n,
        (A a : Ideal (NumberField.RingOfIntegers K)) *
            Ideal.map
              (distanceCMIntegers c :
                NumberField.RingOfIntegers K →+* NumberField.RingOfIntegers K)
              (A a : Ideal (NumberField.RingOfIntegers K)) =
          Ideal.span
            ({((data.S.prod fun p => p) : NumberField.RingOfIntegers K)} :
              Set (NumberField.RingOfIntegers K))) := by
  rcases
      indexed_cm_family
        data j ι ii c _hii hspan hc_base hc_ii hS_splitK with
    ⟨m, A0, hA0_card, hA0_inj, hA0_mul_conj⟩
  exact
    extract_large_fibre
      data c A0 hA0_card hA0_inj hA0_mul_conj

lemma distance_indexed_cm
    {T : SplitTotallyTower.{0}} (data : DistanceGrowthData T) (j : ℕ)
    {K : Type*} [Field K] [NumberField K]
    (ι : T.fields j →+* K) (ii : K) (c : K ≃+* K)
    (_hii : ii ^ (2 : ℕ) = (-1 : K))
    (hspan : ∀ z : K, ∃ a b : T.fields j, z = ι a + ι b * ii)
    (hc_base : ∀ a : T.fields j, c (ι a) = ι a)
    (hc_ii : c ii = -ii)
    (hS_splitK :
      ∀ p ∈ data.S,
        Nat.Prime p ∧ p % 4 = 1 ∧
        (Ideal.primesOver (rationalPrimeIdeal p) (NumberField.RingOfIntegers K)).ncard =
          Module.finrank ℚ K ∧
        (∀ P ∈ Ideal.primesOver (rationalPrimeIdeal p) (NumberField.RingOfIntegers K),
          Ideal.ramificationIdx (rationalPrimeIdeal p) P = 1 ∧
            Ideal.inertiaDeg (rationalPrimeIdeal p) P = 1)) :
    ∃ n : ℕ, ∃ A : Fin n → NonzeroIntegersIdeal K,
      (((2 : ℝ) ^ data.S.card) ^ NumberField.InfinitePlace.nrComplexPlaces K) /
          (NumberField.classNumber K : ℝ) ≤ n ∧
      Function.Injective A ∧
      (∃ C : ClassGroup (NumberField.RingOfIntegers K),
        ∀ a : Fin n, ClassGroup.mk0 (A a) = C) ∧
      (∀ a : Fin n,
        (A a : Ideal (NumberField.RingOfIntegers K)) *
            Ideal.map
              (distanceCMIntegers c :
                NumberField.RingOfIntegers K →+* NumberField.RingOfIntegers K)
              (A a : Ideal (NumberField.RingOfIntegers K)) =
          Ideal.span
            ({((data.S.prod fun p => p) : NumberField.RingOfIntegers K)} :
              Set (NumberField.RingOfIntegers K))) := by
  exact
    distance_promote_cm
      data j ι ii c _hii hspan hc_base hc_ii hS_splitK

/--
Choose principal generators for the quotient fractional ideals `A a * A₀⁻¹`
once a nonempty family of ideals is known to lie in a single class-group fibre.
-/
lemma distance_same_cm
    {K : Type*} [Field K] [NumberField K]
    {n : ℕ} (hn : 0 < n)
    (A : Fin n → NonzeroIntegersIdeal K)
    (hA_class :
      ∃ C : ClassGroup (NumberField.RingOfIntegers K), ∀ a : Fin n, ClassGroup.mk0 (A a) = C) :
    ∃ α : Fin n → K,
      (∀ a : Fin n, α a ≠ 0) ∧
      (∀ a : Fin n,
        let F :
            FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers K)) K :=
          ((((FractionalIdeal.mk0 K) (A a)) *
                ((FractionalIdeal.mk0 K) (A ⟨0, hn⟩))⁻¹ :
              (FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers K)) K)ˣ) :
            FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers K)) K)
        F =
          FractionalIdeal.spanSingleton
            (nonZeroDivisors (NumberField.RingOfIntegers K)) (α a)) := by
  classical
  let a0 : Fin n := ⟨0, hn⟩
  have hclass0 : ∀ a : Fin n, ClassGroup.mk0 (A a) = ClassGroup.mk0 (A a0) := by
    rcases hA_class with ⟨C, hC⟩
    intro a
    rw [hC a, hC a0]
  have hex :
      ∀ a : Fin n,
        ∃ x : K,
          let F :
              FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers K)) K :=
            ((((FractionalIdeal.mk0 K) (A a)) *
                  ((FractionalIdeal.mk0 K) (A a0))⁻¹ :
                (FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers K)) K)ˣ) :
              FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers K)) K)
          F =
            FractionalIdeal.spanSingleton
              (nonZeroDivisors (NumberField.RingOfIntegers K)) x := by
    intro a
    let F :
        FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers K)) K :=
      ((((FractionalIdeal.mk0 K) (A a)) *
            ((FractionalIdeal.mk0 K) (A a0))⁻¹ :
          (FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers K)) K)ˣ) :
        FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers K)) K)
    have h1 :
        ClassGroup.mk K
          ((FractionalIdeal.mk0 K) (A a) *
            ((FractionalIdeal.mk0 K) (A a0))⁻¹) = 1 := by
      rw [map_mul, ClassGroup.mk_mk0, map_inv, ClassGroup.mk_mk0, hclass0 a]
      simp
    have hpr : ((F : Submodule (NumberField.RingOfIntegers K) K)).IsPrincipal := by
      simpa [F] using (ClassGroup.mk_eq_one_iff).1 h1
    rcases (FractionalIdeal.isPrincipal_iff F).1 hpr with ⟨x, hx⟩
    exact ⟨x, hx⟩
  choose α hα using hex
  refine ⟨α, ?_, hα⟩
  intro a
  let F :
      FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers K)) K :=
    ((((FractionalIdeal.mk0 K) (A a)) *
          ((FractionalIdeal.mk0 K) (A a0))⁻¹ :
        (FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers K)) K)ˣ) :
      FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers K)) K)
  have hF_ne_zero : F ≠ 0 := by
    exact Units.ne_zero (((FractionalIdeal.mk0 K) (A a)) * ((FractionalIdeal.mk0 K) (A a0))⁻¹)
  intro hzero
  have hF_zero : F = 0 := by
    simpa [F, hzero] using hα a
  exact hF_ne_zero hF_zero

/--
The ideal-theoretic identity from Step 2 of the paper proof: the principal
ideal generated by the raw-unit candidate `α a / c(α a)` is the square of the
quotient ideal `A a * A₀⁻¹`.
-/
def distanceLevelFormula
    {K : Type*} [Field K] [NumberField K]
    (c : K ≃+* K)
    {n : ℕ} (A : Fin n → NonzeroIntegersIdeal K) (α : Fin n → K)
    (hn : 0 < n) : Prop :=
  ∀ a : Fin n,
    let F :
        FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers K)) K :=
      ((((FractionalIdeal.mk0 K) (A a)) *
            ((FractionalIdeal.mk0 K) (A ⟨0, hn⟩))⁻¹ :
          (FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers K)) K)ˣ) :
        FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers K)) K)
    FractionalIdeal.spanSingleton
      (nonZeroDivisors (NumberField.RingOfIntegers K)) ((α a) / c (α a)) = F * F

/--
Step 1 of the paper proof: define `u a := α a / c(α a)` and verify
`u a * c (u a) = 1`.
-/
lemma distance_level_candidates
    {K : Type*} [Field K] [NumberField K]
    (c : K ≃+* K)
    {n : ℕ} (α : Fin n → K)
    (hc_involutive : Function.Involutive c)
    (hα_ne : ∀ a : Fin n, α a ≠ 0) :
    ∀ a : Fin n, (α a / c (α a)) * c (α a / c (α a)) = 1 := by
  intro a
  have hcα_ne : c (α a) ≠ 0 := by
    simpa using hα_ne a
  calc
    (α a / c (α a)) * c (α a / c (α a))
        = (α a / c (α a)) * (c (α a) / c (c (α a))) := by
            rw [map_div₀]
    _ = (α a / c (α a)) * (c (α a) / α a) := by
          rw [hc_involutive (α a)]
    _ = 1 := by
          field_simp [hα_ne a, hcα_ne]

/--
Step 2 of the paper proof: combine the principal-ideal identities for `α a`
with the CM product formula for the ideals `A a` to identify `(u a)`.
-/
lemma distance_candidates_formula
    {T : SplitTotallyTower.{0}} (data : DistanceGrowthData T)
    {K : Type*} [Field K] [NumberField K]
    (c : K ≃+* K)
    {n : ℕ} (A : Fin n → NonzeroIntegersIdeal K) (α : Fin n → K)
    (hn : 0 < n)
    (hα_principal :
      ∀ a : Fin n,
        let F :
            FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers K)) K :=
          ((((FractionalIdeal.mk0 K) (A a)) *
                ((FractionalIdeal.mk0 K) (A ⟨0, hn⟩))⁻¹ :
              (FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers K)) K)ˣ) :
            FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers K)) K)
        F =
          FractionalIdeal.spanSingleton
            (nonZeroDivisors (NumberField.RingOfIntegers K)) (α a))
    (hA_conj_prod :
      ∀ a : Fin n,
        (A a : Ideal (NumberField.RingOfIntegers K)) *
            Ideal.map
              (distanceCMIntegers c :
                NumberField.RingOfIntegers K →+* NumberField.RingOfIntegers K)
              (A a : Ideal (NumberField.RingOfIntegers K)) =
          Ideal.span
            ({((data.S.prod fun p => p) : NumberField.RingOfIntegers K)} :
              Set (NumberField.RingOfIntegers K))) :
    distanceLevelFormula c A α hn := by
  intro a
  let a0 : Fin n := ⟨0, hn⟩
  let O := NumberField.RingOfIntegers K
  let φ := distanceCMIntegers c
  let I0 : Ideal O := A a0
  let Ia : Ideal O := A a
  let J0 : Ideal O := Ideal.map (φ : O →+* O) I0
  let Ja : Ideal O := Ideal.map (φ : O →+* O) Ia
  let F :
      FractionalIdeal (nonZeroDivisors O) K :=
    ((((FractionalIdeal.mk0 K) (A a)) *
          ((FractionalIdeal.mk0 K) (A a0))⁻¹ :
        (FractionalIdeal (nonZeroDivisors O) K)ˣ) :
      FractionalIdeal (nonZeroDivisors O) K)
  let M : Ideal O :=
    Ideal.span ({((data.S.prod fun p => p) : O)} : Set O)
  change FractionalIdeal.spanSingleton (nonZeroDivisors O) ((α a) / c (α a)) = F * F
  have hFα : F = FractionalIdeal.spanSingleton (nonZeroDivisors O) (α a) := by
    simpa [F, a0, O] using hα_principal a
  have hI0_ne : (I0 : FractionalIdeal (nonZeroDivisors O) K) ≠ 0 := by
    apply FractionalIdeal.coeIdeal_ne_zero.mpr
    change (A a0 : Ideal (NumberField.RingOfIntegers K)) ≠ ⊥
    exact mem_nonZeroDivisors_iff_ne_zero.mp (A a0).2
  have hspanα_mul_I0 :
      FractionalIdeal.spanSingleton (nonZeroDivisors O) (α a) *
          (I0 : FractionalIdeal (nonZeroDivisors O) K) =
        Ia := by
    calc
      FractionalIdeal.spanSingleton (nonZeroDivisors O) (α a) *
          (I0 : FractionalIdeal (nonZeroDivisors O) K)
          = F * (I0 : FractionalIdeal (nonZeroDivisors O) K) := by rw [hFα]
      _ = ((((Ia : FractionalIdeal (nonZeroDivisors O) K) *
              (I0 : FractionalIdeal (nonZeroDivisors O) K)⁻¹)) *
            (I0 : FractionalIdeal (nonZeroDivisors O) K)) := by
            rfl
      _ = (Ia : FractionalIdeal (nonZeroDivisors O) K) *
            ((I0 : FractionalIdeal (nonZeroDivisors O) K)⁻¹ *
              (I0 : FractionalIdeal (nonZeroDivisors O) K)) := by
            ac_rfl
      _ = (Ia : FractionalIdeal (nonZeroDivisors O) K) * 1 := by
            rw [inv_mul_cancel₀ hI0_ne]
      _ = Ia := by simp
  have hsec_eq :
      Ideal.span ({((IsLocalization.sec (nonZeroDivisors O) (α a)).1 : O)} : Set O) * I0 =
        Ideal.span ({((IsLocalization.sec (nonZeroDivisors O) (α a)).2 : O)} : Set O) * Ia := by
    simpa [I0, Ia] using
      (FractionalIdeal.spanSingleton_mul_coeIdeal_eq_coeIdeal
        (K := K) (I := I0) (J := Ia) (z := α a)).mp hspanα_mul_I0
  have hsec_map :
      Ideal.span
          ({(φ ((IsLocalization.sec (nonZeroDivisors O) (α a)).1) : O)} : Set O) *
        J0 =
        Ideal.span
            ({(φ ((IsLocalization.sec (nonZeroDivisors O) (α a)).2) : O)} :
              Set O) *
          Ja := by
    simpa [J0, Ja, Ideal.map_mul, Ideal.map_span, Set.image_singleton] using
      congrArg (Ideal.map (φ : O →+* O)) hsec_eq
  have hsec_den_ne :
      (φ ((IsLocalization.sec (nonZeroDivisors O) (α a)).2) : O) ∈ nonZeroDivisors O := by
    rw [mem_nonZeroDivisors_iff_ne_zero]
    exact
      (map_ne_zero_iff (φ : O →+* O) φ.injective).2
        (mem_nonZeroDivisors_iff_ne_zero.mp (IsLocalization.sec (nonZeroDivisors O) (α a)).2.prop)
  have hcα_mk' :
      c (α a) =
        IsLocalization.mk' K
          (φ ((IsLocalization.sec (nonZeroDivisors O) (α a)).1))
          ⟨φ ((IsLocalization.sec (nonZeroDivisors O) (α a)).2), hsec_den_ne⟩ := by
    calc
      c (α a)
          = c
              (IsLocalization.mk' K
                ((IsLocalization.sec (nonZeroDivisors O) (α a)).1)
                ((IsLocalization.sec (nonZeroDivisors O) (α a)).2)) := by
              rw [IsLocalization.mk'_sec]
      _ = c
            (((algebraMap O K) ((IsLocalization.sec (nonZeroDivisors O) (α a)).1)) /
              ((algebraMap O K) ((IsLocalization.sec (nonZeroDivisors O) (α a)).2))) := by
            rw [IsFractionRing.mk'_eq_div]
      _ = c ((algebraMap O K) ((IsLocalization.sec (nonZeroDivisors O) (α a)).1)) /
            c ((algebraMap O K) ((IsLocalization.sec (nonZeroDivisors O) (α a)).2)) := by
            rw [map_div₀]
      _ =
          IsLocalization.mk' K
            (φ ((IsLocalization.sec (nonZeroDivisors O) (α a)).1))
            ⟨φ ((IsLocalization.sec (nonZeroDivisors O) (α a)).2), hsec_den_ne⟩ := by
            rw [IsFractionRing.mk'_eq_div]
            rfl
  have hspancα_mul_J0 :
      FractionalIdeal.spanSingleton (nonZeroDivisors O) (c (α a)) *
          (J0 : FractionalIdeal (nonZeroDivisors O) K) =
        Ja := by
    have htmp :
        FractionalIdeal.spanSingleton (nonZeroDivisors O)
            (IsLocalization.mk' K
              (φ ((IsLocalization.sec (nonZeroDivisors O) (α a)).1))
              ⟨φ ((IsLocalization.sec (nonZeroDivisors O) (α a)).2), hsec_den_ne⟩) *
            (J0 : FractionalIdeal (nonZeroDivisors O) K) =
          Ja := by
      simpa [J0, Ja] using
        (FractionalIdeal.mk'_mul_coeIdeal_eq_coeIdeal
          (K := K) (I := J0) (J := Ja)
          (x := φ ((IsLocalization.sec (nonZeroDivisors O) (α a)).1))
          (y := φ ((IsLocalization.sec (nonZeroDivisors O) (α a)).2))
          hsec_den_ne).mpr hsec_map
    simpa [hcα_mk'] using htmp
  have hm_nat_ne_zero : data.S.prod (fun p => p) ≠ 0 := by
    intro hm0
    exact (Nat.ne_of_gt data.hq_pos) (by rw [data.hq_def, hm0]; norm_num)
  have hM_ne : (M : FractionalIdeal (nonZeroDivisors O) K) ≠ 0 := by
    apply FractionalIdeal.coeIdeal_ne_zero.mpr
    change Ideal.span ({((data.S.prod fun p => p) : O)} : Set O) ≠ ⊥
    intro hbot
    have hcast0 : data.S.prod (fun p => (p : O)) = 0 := by
      simpa using Ideal.span_singleton_eq_bot.mp hbot
    have hnat0 : data.S.prod (fun p => p) = 0 := by
      apply Nat.cast_injective (R := O)
      rw [Finset.prod_natCast]
      simpa using hcast0
    exact hm_nat_ne_zero hnat0
  have hM0 :
      (M : FractionalIdeal (nonZeroDivisors O) K) =
        (I0 : FractionalIdeal (nonZeroDivisors O) K) *
          (J0 : FractionalIdeal (nonZeroDivisors O) K) := by
    simpa [M, I0, J0, a0, O, φ] using
      congrArg (fun I : Ideal O => (I : FractionalIdeal (nonZeroDivisors O) K))
        (hA_conj_prod a0).symm
  have hMa :
      (Ia : FractionalIdeal (nonZeroDivisors O) K) * (Ja : FractionalIdeal (nonZeroDivisors O) K) =
        (M : FractionalIdeal (nonZeroDivisors O) K) := by
    simpa [M, Ia, Ja, O, φ] using
      congrArg (fun I : Ideal O => (I : FractionalIdeal (nonZeroDivisors O) K))
        (hA_conj_prod a)
  have hmul_M :
      (FractionalIdeal.spanSingleton (nonZeroDivisors O) (α a) *
          FractionalIdeal.spanSingleton (nonZeroDivisors O) (c (α a))) *
        (M : FractionalIdeal (nonZeroDivisors O) K) =
      (M : FractionalIdeal (nonZeroDivisors O) K) := by
    calc
      (FractionalIdeal.spanSingleton (nonZeroDivisors O) (α a) *
            FractionalIdeal.spanSingleton (nonZeroDivisors O) (c (α a))) *
          (M : FractionalIdeal (nonZeroDivisors O) K)
          =
          (FractionalIdeal.spanSingleton (nonZeroDivisors O) (α a) *
              FractionalIdeal.spanSingleton (nonZeroDivisors O) (c (α a))) *
            ((I0 : FractionalIdeal (nonZeroDivisors O) K) *
              (J0 : FractionalIdeal (nonZeroDivisors O) K)) := by
            rw [hM0]
      _ =
          (FractionalIdeal.spanSingleton (nonZeroDivisors O) (α a) *
              (I0 : FractionalIdeal (nonZeroDivisors O) K)) *
            (FractionalIdeal.spanSingleton (nonZeroDivisors O) (c (α a)) *
              (J0 : FractionalIdeal (nonZeroDivisors O) K)) := by
            ac_rfl
      _ = (Ia : FractionalIdeal (nonZeroDivisors O) K) *
            (Ja : FractionalIdeal (nonZeroDivisors O) K) := by
            rw [hspanα_mul_I0, hspancα_mul_J0]
      _ = (M : FractionalIdeal (nonZeroDivisors O) K) := hMa
  have hspan_mul_one :
      FractionalIdeal.spanSingleton (nonZeroDivisors O) (α a) *
        FractionalIdeal.spanSingleton (nonZeroDivisors O) (c (α a)) = 1 := by
    have hmul_M' :
        (FractionalIdeal.spanSingleton (nonZeroDivisors O) (α a) *
            FractionalIdeal.spanSingleton (nonZeroDivisors O) (c (α a))) *
          (M : FractionalIdeal (nonZeroDivisors O) K) =
        1 * (M : FractionalIdeal (nonZeroDivisors O) K) := by
      calc
        (FractionalIdeal.spanSingleton (nonZeroDivisors O) (α a) *
              FractionalIdeal.spanSingleton (nonZeroDivisors O) (c (α a))) *
            (M : FractionalIdeal (nonZeroDivisors O) K)
            = (M : FractionalIdeal (nonZeroDivisors O) K) := hmul_M
        _ = 1 * (M : FractionalIdeal (nonZeroDivisors O) K) := by simp
    exact mul_right_cancel₀ hM_ne hmul_M'
  have hspanc_inv :
      FractionalIdeal.spanSingleton (nonZeroDivisors O) (c (α a)) =
        (FractionalIdeal.spanSingleton (nonZeroDivisors O) (α a))⁻¹ := by
    exact (inv_eq_of_mul_eq_one_right hspan_mul_one).symm
  calc
    FractionalIdeal.spanSingleton (nonZeroDivisors O) ((α a) / c (α a))
        =
          FractionalIdeal.spanSingleton (nonZeroDivisors O) (α a) /
            FractionalIdeal.spanSingleton (nonZeroDivisors O) (c (α a)) := by
          rw [FractionalIdeal.spanSingleton_div_spanSingleton]
    _ =
        FractionalIdeal.spanSingleton (nonZeroDivisors O) (α a) *
          (FractionalIdeal.spanSingleton (nonZeroDivisors O) (c (α a)))⁻¹ := by
          rw [div_eq_mul_inv]
    _ =
        FractionalIdeal.spanSingleton (nonZeroDivisors O) (α a) *
          FractionalIdeal.spanSingleton (nonZeroDivisors O) (α a) := by
          rw [hspanc_inv]
          simp
    _ = F * F := by
          simp [hFα]

/--
Step 3 of the paper proof: the principal-ideal formula from Step 2 forces the
raw-unit candidates to be distinct.
-/
lemma distance_candidates_injective
    {K : Type*} [Field K] [NumberField K]
    (c : K ≃+* K)
    {n : ℕ} (A : Fin n → NonzeroIntegersIdeal K) (α : Fin n → K)
    (hn : 0 < n)
    (hA_inj : Function.Injective A)
    (hprincipal : distanceLevelFormula c A α hn) :
    Function.Injective (fun a => α a / c (α a)) := by
  intro a b hab
  let A0 : NonzeroIntegersIdeal K := A ⟨0, hn⟩
  let U0 :
      (FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers K)) K)ˣ :=
    (FractionalIdeal.mk0 K) A0
  let U :
      Fin n →
        (FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers K)) K)ˣ :=
    fun i => ((FractionalIdeal.mk0 K) (A i)) * U0⁻¹
  have hspan :
      FractionalIdeal.spanSingleton
          (nonZeroDivisors (NumberField.RingOfIntegers K)) (α a / c (α a)) =
        FractionalIdeal.spanSingleton
          (nonZeroDivisors (NumberField.RingOfIntegers K)) (α b / c (α b)) := by
    simpa using
      congrArg
        (FractionalIdeal.spanSingleton
          (nonZeroDivisors (NumberField.RingOfIntegers K)))
        hab
  have hsqUVal :
      ((((FractionalIdeal.mk0 K) (A a)) * ((FractionalIdeal.mk0 K) (A ⟨0, hn⟩))⁻¹ :
            (FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers K)) K)ˣ) :
          FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers K)) K) *
          ((((FractionalIdeal.mk0 K) (A a)) * ((FractionalIdeal.mk0 K) (A ⟨0, hn⟩))⁻¹ :
              (FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers K)) K)ˣ) :
            FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers K)) K) =
        ((((FractionalIdeal.mk0 K) (A b)) * ((FractionalIdeal.mk0 K) (A ⟨0, hn⟩))⁻¹ :
            (FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers K)) K)ˣ) :
          FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers K)) K) *
          ((((FractionalIdeal.mk0 K) (A b)) * ((FractionalIdeal.mk0 K) (A ⟨0, hn⟩))⁻¹ :
              (FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers K)) K)ˣ) :
            FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers K)) K) := by
    rw [← hprincipal a, ← hprincipal b]
    exact hspan
  have hsqU : U a * U a = U b * U b := by
    apply Units.ext
    simpa [U, U0, A0] using hsqUVal
  have hUa : U a * U0 = (FractionalIdeal.mk0 K) (A a) := by
    dsimp [U, U0]
    simp [mul_assoc]
  have hUb : U b * U0 = (FractionalIdeal.mk0 K) (A b) := by
    dsimp [U, U0]
    simp [mul_assoc]
  have hmul : U a * ((FractionalIdeal.mk0 K) (A a)) = U b * ((FractionalIdeal.mk0 K) (A b)) := by
    have htmp : U a * (U a * U0) = U b * (U b * U0) := by
      simpa [mul_assoc] using congrArg (fun x => x * U0) hsqU
    rw [hUa, hUb] at htmp
    exact htmp
  have hmulVal :=
    congrArg
      (fun u :
        (FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers K)) K)ˣ =>
          (u :
            FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers K)) K))
      hmul
  dsimp [U, U0, A0] at hmulVal
  have htmp :
      ((((A a : Ideal (NumberField.RingOfIntegers K)) :
            FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers K)) K) *
            (((FractionalIdeal.mk0 K) (A ⟨0, hn⟩))⁻¹ :
              (FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers K)) K)ˣ)) *
          ((A a : Ideal (NumberField.RingOfIntegers K)) :
            FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers K)) K)) =
        ((((A b : Ideal (NumberField.RingOfIntegers K)) :
            FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers K)) K) *
            (((FractionalIdeal.mk0 K) (A ⟨0, hn⟩))⁻¹ :
              (FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers K)) K)ˣ)) *
          ((A b : Ideal (NumberField.RingOfIntegers K)) :
            FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers K)) K)) := by
    simpa [FractionalIdeal.coe_mk0] using hmulVal
  have htmp2 :
      ((((A a : Ideal (NumberField.RingOfIntegers K)) :
            FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers K)) K) *
          ((A a : Ideal (NumberField.RingOfIntegers K)) :
            FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers K)) K)) *
          ((((FractionalIdeal.mk0 K) (A ⟨0, hn⟩))⁻¹ :
              (FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers K)) K)ˣ) :
            FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers K)) K)) =
        ((((A b : Ideal (NumberField.RingOfIntegers K)) :
            FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers K)) K) *
          ((A b : Ideal (NumberField.RingOfIntegers K)) :
            FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers K)) K)) *
          ((((FractionalIdeal.mk0 K) (A ⟨0, hn⟩))⁻¹ :
              (FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers K)) K)ˣ) :
            FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers K)) K)) := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using htmp
  have hsqAVal :
      (((A a : Ideal (NumberField.RingOfIntegers K)) :
          FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers K)) K) *
        ((A a : Ideal (NumberField.RingOfIntegers K)) :
          FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers K)) K)) =
      (((A b : Ideal (NumberField.RingOfIntegers K)) :
          FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers K)) K) *
        ((A b : Ideal (NumberField.RingOfIntegers K)) :
          FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers K)) K)) := by
    exact (Units.mul_left_inj (((FractionalIdeal.mk0 K) (A ⟨0, hn⟩))⁻¹)).mp htmp2
  have hsqA :
      (A a : Ideal (NumberField.RingOfIntegers K)) ^ 2 =
        (A b : Ideal (NumberField.RingOfIntegers K)) ^ 2 := by
    apply FractionalIdeal.coeIdeal_injective (K := K)
    simpa [pow_two] using hsqAVal
  have hAeq : A a = A b := by
    apply Subtype.ext
    exact (pow_left_injective (n := 2) (by decide)) hsqA
  exact hA_inj hAeq

/--
Step 4 of the paper proof: the principal-ideal formula and `q = m^2` imply the
raw-unit candidates lie in `q⁻¹ O_K`.
-/
lemma candidates_scaled_integers
    {T : SplitTotallyTower.{0}} (data : DistanceGrowthData T)
    {K : Type*} [Field K] [NumberField K]
    (c : K ≃+* K)
    {n : ℕ} (A : Fin n → NonzeroIntegersIdeal K) (α : Fin n → K)
    (hn : 0 < n)
    (hA_conj_prod :
      ∀ a : Fin n,
        (A a : Ideal (NumberField.RingOfIntegers K)) *
            Ideal.map
              (distanceCMIntegers c :
                NumberField.RingOfIntegers K →+* NumberField.RingOfIntegers K)
              (A a : Ideal (NumberField.RingOfIntegers K)) =
          Ideal.span
            ({((data.S.prod fun p => p) : NumberField.RingOfIntegers K)} :
              Set (NumberField.RingOfIntegers K)))
    (hprincipal : distanceLevelFormula c A α hn) :
    ∀ a : Fin n, ScaledRingIntegers K data.q (α a / c (α a)) := by
  intro a
  let a0 : Fin n := ⟨0, hn⟩
  let F : FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers K)) K :=
    ((((FractionalIdeal.mk0 K) (A a)) *
          ((FractionalIdeal.mk0 K) (A a0))⁻¹ :
        (FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers K)) K)ˣ) :
      FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers K)) K)
  let m : NumberField.RingOfIntegers K := ((data.S.prod fun p => p) : NumberField.RingOfIntegers K)
  let spanm :
      FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers K)) K :=
    FractionalIdeal.spanSingleton
      (nonZeroDivisors (NumberField.RingOfIntegers K)) (m : K)
  have hprincipal' :
      FractionalIdeal.spanSingleton
          (nonZeroDivisors (NumberField.RingOfIntegers K)) (α a / c (α a)) = F * F := by
    simpa [a0, F] using hprincipal a
  have hm_le_A0 :
      (Ideal.span ({m} : Set (NumberField.RingOfIntegers K)) :
        Ideal (NumberField.RingOfIntegers K)) ≤
      (A a0 : Ideal (NumberField.RingOfIntegers K)) := by
    rw [← hA_conj_prod a0]
    exact Ideal.mul_le_right
  have hspanm_le_A0 :
      spanm ≤ (A a0 : Ideal (NumberField.RingOfIntegers K)) := by
    simpa [spanm] using
      (show
        (((Ideal.span ({m} : Set (NumberField.RingOfIntegers K)) :
            Ideal (NumberField.RingOfIntegers K)) :
            FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers K)) K) ≤
          (A a0 : Ideal (NumberField.RingOfIntegers K))) from
          (FractionalIdeal.coeIdeal_le_coeIdeal (K := K)).2 hm_le_A0)
  have hA0_ne_zero :
      (((A a0 : Ideal (NumberField.RingOfIntegers K)) :
          FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers K)) K) ≠ 0) := by
    exact
      (FractionalIdeal.coeIdeal_ne_zero (K := K)).2
        (mem_nonZeroDivisors_iff_ne_zero.mp (A a0).2)
  have hA0_mul_inv :
      (((A a0 : Ideal (NumberField.RingOfIntegers K)) :
          FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers K)) K) *
        (((A a0 : Ideal (NumberField.RingOfIntegers K)) :
          FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers K)) K)⁻¹)) = 1 := by
    exact mul_inv_cancel₀ hA0_ne_zero
  have hA0F_eq_Aa :
      ((A a0 : Ideal (NumberField.RingOfIntegers K)) :
          FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers K)) K) * F =
        (A a : Ideal (NumberField.RingOfIntegers K)) := by
    calc
      ((A a0 : Ideal (NumberField.RingOfIntegers K)) :
          FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers K)) K) * F
          =
            ((A a : Ideal (NumberField.RingOfIntegers K)) :
                FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers K)) K) *
              (((A a0 : Ideal (NumberField.RingOfIntegers K)) :
                  FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers K)) K) *
                (((A a0 : Ideal (NumberField.RingOfIntegers K)) :
                  FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers K)) K)⁻¹)) := by
            simp [F, a0, mul_left_comm]
      _ = (A a : Ideal (NumberField.RingOfIntegers K)) := by
            rw [hA0_mul_inv, mul_one]
  have hspanmF_le_one :
      spanm * F ≤
        (1 : FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers K)) K) := by
    calc
      spanm * F ≤ (A a0 : Ideal (NumberField.RingOfIntegers K)) * F := by
        simpa [mul_comm] using (mul_le_mul_right hspanm_le_A0 F)
      _ = (A a : Ideal (NumberField.RingOfIntegers K)) := hA0F_eq_Aa
      _ ≤ 1 := by
        simpa using
          (FractionalIdeal.coeIdeal_le_one
            (S := nonZeroDivisors (NumberField.RingOfIntegers K))
            (P := K) (I := (A a : Ideal (NumberField.RingOfIntegers K))))
  have hsquare_le_one :
      (spanm * F) * (spanm * F) ≤
        (1 : FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers K)) K) := by
    calc
      (spanm * F) * (spanm * F) ≤ (spanm * F) * 1 := by
        simpa using
          (mul_le_mul_right hspanmF_le_one (spanm * F))
      _ = 1 * (spanm * F) := by simp [mul_comm]
      _ ≤ 1 * 1 := by
        simpa using
          (mul_le_mul_right hspanmF_le_one
            (1 : FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers K)) K))
      _ = 1 := by simp
  have hqK : (data.q : K) = (m : K) ^ (2 : ℕ) := by
    simpa [m] using congrArg (fun x : ℕ => (x : K)) data.hq_def
  have hscaled_mem :
      ((data.q : K) * (α a / c (α a))) ∈
        (1 : FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers K)) K) := by
    apply (FractionalIdeal.spanSingleton_le_iff_mem).1
    calc
      FractionalIdeal.spanSingleton
          (nonZeroDivisors (NumberField.RingOfIntegers K)) ((data.q : K) * (α a / c (α a)))
          =
            FractionalIdeal.spanSingleton
              (nonZeroDivisors (NumberField.RingOfIntegers K)) (data.q : K) *
              FractionalIdeal.spanSingleton
                (nonZeroDivisors (NumberField.RingOfIntegers K)) (α a / c (α a)) := by
              rw [FractionalIdeal.spanSingleton_mul_spanSingleton]
      _ =
            FractionalIdeal.spanSingleton
              (nonZeroDivisors (NumberField.RingOfIntegers K)) ((m : K) ^ (2 : ℕ)) *
              FractionalIdeal.spanSingleton
                (nonZeroDivisors (NumberField.RingOfIntegers K)) (α a / c (α a)) := by
              rw [hqK]
      _ =
            FractionalIdeal.spanSingleton
              (nonZeroDivisors (NumberField.RingOfIntegers K)) ((m : K) ^ (2 : ℕ)) * (F * F) := by
              rw [hprincipal']
      _ =
            (FractionalIdeal.spanSingleton
                (nonZeroDivisors (NumberField.RingOfIntegers K)) (m : K) *
              FractionalIdeal.spanSingleton
                (nonZeroDivisors (NumberField.RingOfIntegers K)) (m : K)) * (F * F) := by
              rw [pow_two, ← FractionalIdeal.spanSingleton_mul_spanSingleton]
      _ = (spanm * F) * (spanm * F) := by
              dsimp [spanm]
              ac_rfl
      _ ≤ 1 := hsquare_le_one
  rcases (FractionalIdeal.mem_one_iff
    (S := nonZeroDivisors (NumberField.RingOfIntegers K))).1 hscaled_mem with ⟨b, hb⟩
  exact ⟨b, hb⟩

/--
Convert chosen principal quotient generators `α a` into the raw-unit candidates
`u a = α a / c(α a)`.
-/
lemma indexed_cm_generators
    {T : SplitTotallyTower.{0}} (data : DistanceGrowthData T)
    {K : Type*} [Field K] [NumberField K]
    (c : K ≃+* K)
    {n : ℕ} (A : Fin n → NonzeroIntegersIdeal K) (α : Fin n → K)
    (_hn : 0 < n)
    (_hc_involutive : Function.Involutive c)
    (_hα_ne : ∀ a : Fin n, α a ≠ 0)
    (_hα_principal :
      ∀ a : Fin n,
        let F :
            FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers K)) K :=
          ((((FractionalIdeal.mk0 K) (A a)) *
                ((FractionalIdeal.mk0 K) (A ⟨0, _hn⟩))⁻¹ :
              (FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers K)) K)ˣ) :
            FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers K)) K)
        F =
          FractionalIdeal.spanSingleton
            (nonZeroDivisors (NumberField.RingOfIntegers K)) (α a))
    (_hA_inj : Function.Injective A)
    (_hA_conj_prod :
      ∀ a : Fin n,
        (A a : Ideal (NumberField.RingOfIntegers K)) *
            Ideal.map
              (distanceCMIntegers c :
                NumberField.RingOfIntegers K →+* NumberField.RingOfIntegers K)
              (A a : Ideal (NumberField.RingOfIntegers K)) =
          Ideal.span
            ({((data.S.prod fun p => p) : NumberField.RingOfIntegers K)} :
              Set (NumberField.RingOfIntegers K))) :
    ∃ u : Fin n → K,
      Function.Injective u ∧
      (∀ a : Fin n, u a * c (u a) = 1) ∧
      (∀ a : Fin n, ScaledRingIntegers K data.q (u a)) := by
  let u : Fin n → K := fun a => α a / c (α a)
  have hu_principal : distanceLevelFormula c A α _hn :=
    distance_candidates_formula
      data c A α _hn _hα_principal _hA_conj_prod
  refine ⟨u, ?_, ?_, ?_⟩
  · simpa [u] using
      distance_candidates_injective
        c A α _hn _hA_inj hu_principal
  · simpa [u] using
      distance_level_candidates
        c α _hc_involutive _hα_ne
  · simpa [u] using
      candidates_scaled_integers
        data c A α _hn _hA_conj_prod hu_principal

lemma indexed_same_cm
    {T : SplitTotallyTower.{0}} (data : DistanceGrowthData T) (_j : ℕ)
    {K : Type*} [Field K] [NumberField K]
    (c : K ≃+* K)
    {n : ℕ} (A : Fin n → NonzeroIntegersIdeal K)
    (_hcard :
      (((2 : ℝ) ^ data.S.card) ^ NumberField.InfinitePlace.nrComplexPlaces K) /
          (NumberField.classNumber K : ℝ) ≤ n)
    (_hc_involutive : Function.Involutive c)
    (_hA_inj : Function.Injective A)
    (_hA_class :
      ∃ C : ClassGroup (NumberField.RingOfIntegers K), ∀ a : Fin n, ClassGroup.mk0 (A a) = C)
    (_hA_conj_prod :
      ∀ a : Fin n,
        (A a : Ideal (NumberField.RingOfIntegers K)) *
            Ideal.map
              (distanceCMIntegers c :
                NumberField.RingOfIntegers K →+* NumberField.RingOfIntegers K)
              (A a : Ideal (NumberField.RingOfIntegers K)) =
          Ideal.span
            ({((data.S.prod fun p => p) : NumberField.RingOfIntegers K)} :
              Set (NumberField.RingOfIntegers K))) :
    ∃ u : Fin n → K,
      Function.Injective u ∧
      (∀ a : Fin n, u a * c (u a) = 1) ∧
      (∀ a : Fin n, ScaledRingIntegers K data.q (u a)) := by
  have hnum_pos :
      0 < (((2 : ℝ) ^ data.S.card) ^ NumberField.InfinitePlace.nrComplexPlaces K) := by
    positivity
  have hclass_pos : 0 < (NumberField.classNumber K : ℝ) := by
    exact_mod_cast NumberField.classNumber_pos K
  have hlower_pos :
      0 <
        (((2 : ℝ) ^ data.S.card) ^ NumberField.InfinitePlace.nrComplexPlaces K) /
          (NumberField.classNumber K : ℝ) := by
    exact div_pos hnum_pos hclass_pos
  have hn : 0 < n := by
    by_contra hn_pos
    have hn0 : n = 0 := Nat.eq_zero_of_not_pos hn_pos
    have hle0 :
        (((2 : ℝ) ^ data.S.card) ^ NumberField.InfinitePlace.nrComplexPlaces K) /
            (NumberField.classNumber K : ℝ) ≤ 0 := by
      simpa [hn0] using _hcard
    linarith
  rcases
      distance_same_cm
        (K := K) hn A _hA_class with
    ⟨α, hα_ne, hα_principal⟩
  exact
    indexed_cm_generators
      data c A α hn _hc_involutive hα_ne hα_principal _hA_inj _hA_conj_prod

lemma level_indexed_cm
    {T : SplitTotallyTower.{0}} (data : DistanceGrowthData T) (j : ℕ)
    {K : Type*} [Field K] [NumberField K]
    (ι : T.fields j →+* K) (ii : K) (c : K ≃+* K)
    (hii : ii ^ (2 : ℕ) = (-1 : K))
    (hspan : ∀ z : K, ∃ a b : T.fields j, z = ι a + ι b * ii)
    (hc_base : ∀ a : T.fields j, c (ι a) = ι a)
    (hc_ii : c ii = -ii)
    (hS_splitK :
      ∀ p ∈ data.S,
        Nat.Prime p ∧ p % 4 = 1 ∧
        (Ideal.primesOver (rationalPrimeIdeal p) (NumberField.RingOfIntegers K)).ncard =
          Module.finrank ℚ K ∧
        (∀ P ∈ Ideal.primesOver (rationalPrimeIdeal p) (NumberField.RingOfIntegers K),
          Ideal.ramificationIdx (rationalPrimeIdeal p) P = 1 ∧
            Ideal.inertiaDeg (rationalPrimeIdeal p) P = 1)) :
    ∃ n : ℕ, ∃ u : Fin n → K,
      (((2 : ℝ) ^ data.S.card) ^ NumberField.InfinitePlace.nrComplexPlaces K) /
          (NumberField.classNumber K : ℝ) ≤ n ∧
      Function.Injective u ∧
      (∀ a : Fin n, u a * c (u a) = 1) ∧
      (∀ a : Fin n, ScaledRingIntegers K data.q (u a)) := by
  have hc_involutive : Function.Involutive c :=
    level_cm_involutive ι ii c hc_base hc_ii hspan
  rcases
      distance_indexed_cm
        data j ι ii c hii hspan hc_base hc_ii hS_splitK with
    ⟨n, A, hcard, hA_inj, hA_class, hA_conj_prod⟩
  rcases
      indexed_same_cm
        data j c A hcard hc_involutive hA_inj hA_class hA_conj_prod with
    ⟨u, hu_inj, hu_mul_conj, hu_scaled⟩
  exact ⟨n, u, hcard, hu_inj, hu_mul_conj, hu_scaled⟩

/--
Arithmetic construction step for the CM raw-unit candidates.

This is the part of the paper proof that uses the split primes from `S`, the
class group of `K`, and generators of principal quotients `A A₀⁻¹` to build an
injective family `a ↦ u_a` with `u_a * c(u_a) = 1` and `u_a ∈ q⁻¹ O_K`.
-/
lemma distance_level_indexed
    {T : SplitTotallyTower.{0}} (data : DistanceGrowthData T) (j : ℕ)
    {K : Type*} [Field K] [NumberField K]
    (ι : T.fields j →+* K) (ii : K) (c : K ≃+* K)
    (hii : ii ^ (2 : ℕ) = (-1 : K))
    (hspan : ∀ z : K, ∃ a b : T.fields j, z = ι a + ι b * ii)
    (hc_base : ∀ a : T.fields j, c (ι a) = ι a)
    (hc_ii : c ii = -ii)
    (hsplit_bridge :
      ∀ {p : ℕ}, Nat.Prime p → p % 4 = 1 →
        splitsCompletely (T.fields j) p → splitsCompletely K p)
    (hS_splitF : ∀ p ∈ data.S, Nat.Prime p ∧ p % 4 = 1 ∧ splitsCompletely (T.fields j) p) :
    ∃ n : ℕ, ∃ u : Fin n → K,
      (((2 : ℝ) ^ data.S.card) ^ NumberField.InfinitePlace.nrComplexPlaces K) /
          (NumberField.classNumber K : ℝ) ≤ n ∧
      Function.Injective u ∧
      (∀ a : Fin n, u a * c (u a) = 1) ∧
      (∀ a : Fin n, ScaledRingIntegers K data.q (u a)) := by
  have hS_splitK :
      ∀ p ∈ data.S,
        Nat.Prime p ∧ p % 4 = 1 ∧
        (Ideal.primesOver (rationalPrimeIdeal p) (NumberField.RingOfIntegers K)).ncard =
          Module.finrank ℚ K ∧
        (∀ P ∈ Ideal.primesOver (rationalPrimeIdeal p) (NumberField.RingOfIntegers K),
          Ideal.ramificationIdx (rationalPrimeIdeal p) P = 1 ∧
            Ideal.inertiaDeg (rationalPrimeIdeal p) P = 1) :=
    distance_level_cm
      data j hsplit_bridge hS_splitF
  exact
    level_indexed_cm
      data j ι ii c hii hspan hc_base hc_ii hS_splitK

/--
Auxiliary construction step for
`distance_elements_cm`.

The remaining work is the ideal-class argument from `Erdos90a.tex`: for each
`p ∈ S`, choose one prime from every conjugate pair above `p`, partition the
resulting squarefree ideals by ideal class, and then form `u_A = α_A / c(α_A)`
inside a large class-group fibre.
-/
lemma distance_candidate_cm
    {T : SplitTotallyTower.{0}} (data : DistanceGrowthData T) (j : ℕ)
    {K : Type*} [Field K] [NumberField K]
    (ι : T.fields j →+* K) (ii : K) (c : K ≃+* K)
    (hii : ii ^ (2 : ℕ) = (-1 : K))
    (hspan : ∀ z : K, ∃ a b : T.fields j, z = ι a + ι b * ii)
    (hc_base : ∀ a : T.fields j, c (ι a) = ι a)
    (hc_ii : c ii = -ii)
    (hsplit_bridge :
      ∀ {p : ℕ}, Nat.Prime p → p % 4 = 1 →
        splitsCompletely (T.fields j) p → splitsCompletely K p)
    (hS_splitF : ∀ p ∈ data.S, Nat.Prime p ∧ p % 4 = 1 ∧ splitsCompletely (T.fields j) p) :
    ∃ U : Finset K,
      (((2 : ℝ) ^ data.S.card) ^ NumberField.InfinitePlace.nrComplexPlaces K) /
          (NumberField.classNumber K : ℝ) ≤ (U.card : ℝ) ∧
      (∀ u ∈ U, u * c u = 1) ∧
      (∀ u ∈ U, ScaledRingIntegers K data.q u) := by
  rcases
      distance_level_indexed
        data j ι ii c hii hspan hc_base hc_ii hsplit_bridge hS_splitF with
    ⟨n, u, hcard, hu_inj, hu_mul_conj, hu_scaled⟩
  exact
    package_indexed_finset
      data j c u hu_inj hcard hu_mul_conj hu_scaled

lemma distance_elements_cm
    {T : SplitTotallyTower.{0}} (data : DistanceGrowthData T) (j : ℕ)
    {K : Type*} [Field K] [NumberField K]
    (ι : T.fields j →+* K) (ii : K) (c : K ≃+* K)
    (hii : ii ^ (2 : ℕ) = (-1 : K))
    (hspan : ∀ z : K, ∃ a b : T.fields j, z = ι a + ι b * ii)
    (hc_base : ∀ a : T.fields j, c (ι a) = ι a)
    (hc_ii : c ii = -ii)
    (hc_embed : ∀ σ : K →+* ℂ, ∀ x : K, σ (c x) = star (σ x))
    (hsplit_bridge :
      ∀ {p : ℕ}, Nat.Prime p → p % 4 = 1 →
        splitsCompletely (T.fields j) p → splitsCompletely K p)
    (hS_splitF : ∀ p ∈ data.S, Nat.Prime p ∧ p % 4 = 1 ∧ splitsCompletely (T.fields j) p) :
    ∃ U : Finset K,
      (((2 : ℝ) ^ data.S.card) ^ NumberField.InfinitePlace.nrComplexPlaces K) /
          (NumberField.classNumber K : ℝ) ≤ (U.card : ℝ) ∧
      (∀ u ∈ U, ∀ σ : K →+* ℂ, ‖σ u‖ = 1) ∧
      (∀ u ∈ U, ScaledRingIntegers K data.q u) := by
  rcases
      distance_candidate_cm
        data j ι ii c hii hspan hc_base hc_ii hsplit_bridge hS_splitF with
    ⟨U, hU_lower, hU_mul_conj, hU_scaled⟩
  refine ⟨U, hU_lower, ?_, hU_scaled⟩
  exact
    embeddings_have_cm
      c hc_embed U hU_mul_conj

/--
Inside a CM field `K = F_j(i)` with its conjugation involution `c`, the split
primes from `S` give rise to a large family of elements `u_A ∈ K` satisfying
`|σ(u_A)| = 1` for every complex embedding `σ`.
-/
lemma distance_set_cm
    {T : SplitTotallyTower.{0}} (data : DistanceGrowthData T) (j : ℕ)
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
    (ι : T.fields j →+* K) (ii : K) (c : K ≃+* K)
    (hcomplex :
      NumberField.InfinitePlace.nrComplexPlaces K = Module.finrank ℚ (T.fields j))
    (hroot : rootDiscriminant K ≤ data.ρ)
    (hii : ii ^ (2 : ℕ) = (-1 : K))
    (hspan : ∀ z : K, ∃ a b : T.fields j, z = ι a + ι b * ii)
    (hc_base : ∀ a : T.fields j, c (ι a) = ι a)
    (hc_ii : c ii = -ii)
    (hc_embed : ∀ σ : K →+* ℂ, ∀ x : K, σ (c x) = star (σ x))
    (hsplit_bridge :
      ∀ {p : ℕ}, Nat.Prime p → p % 4 = 1 →
        splitsCompletely (T.fields j) p → splitsCompletely K p)
    (hS_splitF : ∀ p ∈ data.S, Nat.Prime p ∧ p % 4 = 1 ∧ splitsCompletely (T.fields j) p) :
    ∃ U : Finset Point,
      data.CU ^ Module.finrank ℚ (T.fields j) ≤ (U.card : ℝ) ∧
      ∀ u ∈ U, IsUnitDistance 0 u := by
  let σ : K →+* ℂ := (IsAlgClosed.lift (R := ℚ) (S := K) (M := ℂ)).toRingHom
  rcases
      distance_elements_cm
        data j ι ii c hii hspan hc_base hc_ii hc_embed hsplit_bridge hS_splitF with
      ⟨U0, hU0_lower, hU0_unit, hU0_scaled⟩
  have hclass :
      (NumberField.classNumber K : ℝ) ≤ data.H ^ Module.finrank ℚ (T.fields j) :=
    distance_level_bound data j hcomplex hroot
  have hlower :
      data.CU ^ Module.finrank ℚ (T.fields j) ≤
        (((2 : ℝ) ^ data.S.card) ^ NumberField.InfinitePlace.nrComplexPlaces K) /
          (NumberField.classNumber K : ℝ) :=
    distance_level_cu data j hcomplex hclass
  let U : Finset Point := U0.image σ
  have hσinj : Function.Injective σ := RingHom.injective σ
  have hU_card : U.card = U0.card := by
    simp [U, Finset.card_image_of_injective, hσinj]
  refine ⟨U, ?_, ?_⟩
  · calc
      data.CU ^ Module.finrank ℚ (T.fields j)
          ≤ (((2 : ℝ) ^ data.S.card) ^ NumberField.InfinitePlace.nrComplexPlaces K) /
              (NumberField.classNumber K : ℝ) := hlower
      _ ≤ (U0.card : ℝ) := hU0_lower
      _ = (U.card : ℝ) := by simp [hU_card]
  · intro u hu
    rcases Finset.mem_image.mp hu with ⟨u0, hu0, rfl⟩
    rw [IsUnitDistance, dist_eq_norm]
    simpa using hU0_unit u0 hu0 σ

lemma distance_level_tower
    (T : SplitTotallyTower.{0}) (data : DistanceGrowthData T) (j : ℕ) :
    ∃ Uj : Finset Point,
      data.CU ^ Module.finrank ℚ (T.fields j) ≤ (Uj.card : ℝ) ∧
      ∀ u ∈ Uj, IsUnitDistance 0 u := by
  rcases distance_cm_tower T j with
      ⟨K, hFieldK, hNumberFieldK, ι, ii, c, hii, hspan, hc_base, hc_ii, hc_embed,
        hsplit_bridge⟩
  letI := hFieldK
  letI := hNumberFieldK
  rcases cm_i_tower T j ι ii hii hspan with
      ⟨hTotallyComplexK, hcomplex⟩
  letI := hTotallyComplexK
  have hroot_two :
      rootDiscriminant K ≤ 2 * rootDiscriminant (T.fields j) :=
    cm_discriminant_tower T j ι ii hii hspan
  have hroot :
      rootDiscriminant K ≤ data.ρ :=
    le_trans hroot_two (data.hρ_cm j)
  have hS_splitF :
      ∀ p ∈ data.S,
        Nat.Prime p ∧ p % 4 = 1 ∧
          splitsCompletely (T.fields j) p := by
    intro p hp
    rcases T.splitPrimes_spec (data.hS_split p hp) with ⟨hp_prime, hp_mod, hsplitF_all⟩
    exact ⟨hp_prime, hp_mod, hsplitF_all j⟩
  exact
    distance_set_cm
      data j ι ii c hcomplex hroot hii hspan hc_base hc_ii hc_embed hsplit_bridge hS_splitF

lemma distance_scalar_cx
    {T : SplitTotallyTower.{0}} (data : DistanceGrowthData T) :
    data.CX < data.A := by
  exact data.h_cx

/--
Choice of one complex embedding from each conjugate pair, indexed by `Fin d`.
This is the coordinate system used to identify the CM Minkowski embedding with
the file's concrete space `ComplexSpace d = Fin d → ℂ`.
-/
structure DMData
    (K : Type*) [Field K] [NumberField K] (d : ℕ) where
  placeEquiv : Fin d ≃ NumberField.InfinitePlace K

namespace DMData

def embedding
    {K : Type*} [Field K] [NumberField K] {d : ℕ}
    (data : DMData K d) (i : Fin d) : K →+* ℂ :=
  (data.placeEquiv i).embedding

def minkowskiMap
    {K : Type*} [Field K] [NumberField K] {d : ℕ}
    (data : DMData K d) : K →+* ComplexSpace d where
  toFun x := fun i => data.embedding i x
  map_zero' := by
    ext i
    simp [embedding]
  map_one' := by
    ext i
    simp [embedding]
  map_add' := by
    intro x y
    ext i
    simp [embedding]
  map_mul' := by
    intro x y
    ext i
    simp [embedding]

end DMData

/-- The closed polydisc `B_r = {z : ℂ^d : |z_i| ≤ r for all i}`. -/
def unitDistancePolydisc (d : ℕ) (r : ℝ) : Set (ComplexSpace d) :=
  {z | ∀ i : Fin d, ‖z i‖ ≤ r}

/--
Choose one complex embedding from each conjugate pair and identify the set of
chosen embeddings with `Fin d`, where `d` is the number of complex places.
-/
lemma distance_minkowski_data
    {T : SplitTotallyTower.{0}} (j : ℕ)
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
    (hcomplex :
      NumberField.InfinitePlace.nrComplexPlaces K = Module.finrank ℚ (T.fields j)) :
    Nonempty (DMData K (Module.finrank ℚ (T.fields j))) := by
  classical
  let d := Module.finrank ℚ (T.fields j)
  have hcard :
      Fintype.card (NumberField.InfinitePlace K) = d := by
    calc
      Fintype.card (NumberField.InfinitePlace K) =
          NumberField.InfinitePlace.nrRealPlaces K +
            NumberField.InfinitePlace.nrComplexPlaces K := by
            simpa using
              NumberField.InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces (K := K)
      _ = 0 + NumberField.InfinitePlace.nrComplexPlaces K := by
            rw [NumberField.IsTotallyComplex.nrRealPlaces_eq_zero (K := K)]
      _ = d := by
            simpa [d] using hcomplex
  refine ⟨⟨Fintype.equivOfCardEq (by simpa [d] using hcard.symm)⟩⟩

/--
The Minkowski map attached to the chosen complex embeddings is injective.
-/
lemma distance_minkowski_injective
    {K : Type*} [Field K] [NumberField K] {d : ℕ}
    (mdata : DMData K d) :
    Function.Injective mdata.minkowskiMap := by
  intro x y hxy
  let w : NumberField.InfinitePlace K := Classical.choice inferInstance
  let i : Fin d := mdata.placeEquiv.symm w
  exact RingHom.injective (mdata.embedding i) (congrFun hxy i)

/--
The image of `q⁻¹ O_K` under the chosen Minkowski map is a lattice in
`ComplexSpace d`.
-/
lemma distance_scaled_lattice
    {T : SplitTotallyTower.{0}} (data : DistanceGrowthData T) (j : ℕ)
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
    (mdata : DMData K (Module.finrank ℚ (T.fields j))) :
    ∃ Λ : CLattic (Module.finrank ℚ (T.fields j)),
      ∀ z : ComplexSpace (Module.finrank ℚ (T.fields j)),
        z ∈ Λ.subgroup ↔
          ∃ x : K, ScaledRingIntegers K data.q x ∧ mdata.minkowskiMap x = z := by
  classical
  let qUnit : Kˣ := Units.mk0 ((data.q : K)⁻¹) <| inv_ne_zero <| by
    exact_mod_cast Nat.ne_of_gt data.hq_pos
  let I : (FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers K)) K)ˣ :=
    toPrincipalIdeal (NumberField.RingOfIntegers K) K qUnit
  let complexPlaceEquiv :
      Fin (Module.finrank ℚ (T.fields j)) ≃
        {w : NumberField.InfinitePlace K // NumberField.InfinitePlace.IsComplex w} :=
    { toFun := fun i =>
        ⟨mdata.placeEquiv i, NumberField.IsTotallyComplex.isComplex (mdata.placeEquiv i)⟩
      invFun := fun w => mdata.placeEquiv.symm w.1
      left_inv := by
        intro i
        simp
      right_inv := by
        intro w
        ext
        simp }
  letI :
      IsEmpty {w : NumberField.InfinitePlace K // NumberField.InfinitePlace.IsReal w} := by
    rw [← Fintype.card_eq_zero_iff]
    simp [NumberField.IsTotallyComplex.nrRealPlaces_eq_zero (K := K)]
  let e0 :
      NumberField.mixedEmbedding.mixedSpace K ≃ₗ[ℝ]
        ({w : NumberField.InfinitePlace K // NumberField.InfinitePlace.IsComplex w} → ℂ) :=
    LinearEquiv.uniqueProd (R := ℝ)
      (M := {w : NumberField.InfinitePlace K // NumberField.InfinitePlace.IsComplex w} → ℂ)
      (M₂ := {w : NumberField.InfinitePlace K // NumberField.InfinitePlace.IsReal w} → ℝ)
  let e1 :
      ({w : NumberField.InfinitePlace K //
        NumberField.InfinitePlace.IsComplex w} → ℂ) ≃ₗ[ℝ]
        ComplexSpace (Module.finrank ℚ (T.fields j)) :=
    LinearEquiv.funCongrLeft ℝ ℂ complexPlaceEquiv
  let e : NumberField.mixedEmbedding.mixedSpace K ≃ₗ[ℝ]
      ComplexSpace (Module.finrank ℚ (T.fields j)) := e0.trans e1
  let b :
      Module.Basis (Module.Free.ChooseBasisIndex ℤ I) ℝ
        (ComplexSpace (Module.finrank ℚ (T.fields j))) :=
    (NumberField.mixedEmbedding.fractionalIdealLatticeBasis K I).map e
  let subgroup :
      AddSubgroup (ComplexSpace (Module.finrank ℚ (T.fields j))) :=
    (Submodule.span ℤ (Set.range b)).toAddSubgroup
  have hqK : (data.q : K) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt data.hq_pos
  have hI_mem :
      ∀ {x : K},
        x ∈
            (I : FractionalIdeal
              (nonZeroDivisors (NumberField.RingOfIntegers K)) K) ↔
          ScaledRingIntegers K data.q x := by
    intro x
    rw [show (I : FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers K)) K) =
        FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers K))
          ((data.q : K)⁻¹) by
      simp [I, qUnit]]
    rw [FractionalIdeal.mem_spanSingleton]
    constructor
    · rintro ⟨a, ha⟩
      refine ⟨a, ?_⟩
      have ha' := congrArg (fun t : K => (data.q : K) * t) ha
      simpa [Algebra.smul_def, hqK, mul_comm, mul_left_comm, mul_assoc] using ha'
    · rintro ⟨a, ha⟩
      refine ⟨a, ?_⟩
      have ha' := congrArg (fun t : K => t * ((data.q : K)⁻¹)) ha
      simpa [Algebra.smul_def, hqK, mul_comm, mul_left_comm, mul_assoc] using ha'
  have he_apply (x : K) : e (NumberField.mixedEmbedding K x) = mdata.minkowskiMap x := by
    ext i
    simp [e, e0, e1, complexPlaceEquiv,
      DMData.minkowskiMap, DMData.embedding]
  refine ⟨
    { subgroup := subgroup
      countable_subgroup := by
        change Countable (Submodule.span ℤ (Set.range b))
        infer_instance
      discrete_subgroup := by
        change DiscreteTopology (Submodule.span ℤ (Set.range b))
        infer_instance
      fundamentalDomain := ZSpan.fundamentalDomain b
      isFundamentalDomain := by
        simpa using ZSpan.isAddFundamentalDomain b MeasureTheory.volume
      positive_covolume := by
        have hne : MeasureTheory.volume (ZSpan.fundamentalDomain b) ≠ 0 := by
          exact ZSpan.measure_fundamentalDomain_ne_zero b
        have hlt : MeasureTheory.volume (ZSpan.fundamentalDomain b) < ⊤ := by
          exact Bornology.IsBounded.measure_lt_top (ZSpan.fundamentalDomain_isBounded b)
        simpa [setVolume] using ENNReal.toReal_pos hne (ne_of_lt hlt) }, ?_⟩
  intro z
  change z ∈ Submodule.span ℤ (Set.range b) ↔
    ∃ x : K, ScaledRingIntegers K data.q x ∧ mdata.minkowskiMap x = z
  rw [← ZSpan.map (b := NumberField.mixedEmbedding.fractionalIdealLatticeBasis K I) e]
  rw [Submodule.mem_map_equiv]
  rw [NumberField.mixedEmbedding.mem_span_fractionalIdealLatticeBasis (K := K) (I := I)]
  constructor
  · rintro ⟨x, hxI, hxz⟩
    refine ⟨x, (hI_mem.mp hxI), ?_⟩
    have hxz' := congrArg e hxz
    simpa [he_apply x] using hxz'
  · rintro ⟨x, hx, hxz⟩
    refine ⟨x, (hI_mem.mpr hx), ?_⟩
    apply e.injective
    simpa [he_apply x] using hxz

/--
Exact covolume formula for the lattice `Φ(q⁻¹ O_K)` in the CM Minkowski
embedding.
-/
noncomputable def unit_distance_complex
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyComplex K] {d : ℕ}
    (mdata : DMData K d) :
    Fin d ≃ {w : NumberField.InfinitePlace K // NumberField.InfinitePlace.IsComplex w} where
  toFun i := ⟨mdata.placeEquiv i, NumberField.IsTotallyComplex.isComplex _⟩
  invFun w := mdata.placeEquiv.symm w.1
  left_inv i := by simp
  right_inv w := by
    ext
    simp

/--
Identify the totally complex mixed space with the chosen complex coordinate space
`ComplexSpace d = Fin d → ℂ`.
-/
noncomputable def distance_mixed_complex
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyComplex K] {d : ℕ}
    (mdata : DMData K d) :
    NumberField.mixedEmbedding.mixedSpace K ≃L[ℝ] ComplexSpace d := by
  classical
  let e := unit_distance_complex mdata
  have hreal0 :
      Fintype.card {w : NumberField.InfinitePlace K // NumberField.InfinitePlace.IsReal w} = 0 := by
    exact NumberField.IsTotallyComplex.nrRealPlaces_eq_zero (K := K)
  haveI : IsEmpty {w : NumberField.InfinitePlace K // NumberField.InfinitePlace.IsReal w} :=
    Fintype.card_eq_zero_iff.mp hreal0
  exact
    (ContinuousLinearEquiv.uniqueProd ℝ
      (({w : NumberField.InfinitePlace K // NumberField.InfinitePlace.IsComplex w} → ℂ))
      (({w : NumberField.InfinitePlace K // NumberField.InfinitePlace.IsReal w} → ℝ))).trans
      ((ContinuousLinearEquiv.piCongrLeft ℝ
        (fun _ : {w : NumberField.InfinitePlace K // NumberField.InfinitePlace.IsComplex w} => ℂ)
        e).symm)

@[simp] lemma mixed_complex_embedding
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyComplex K] {d : ℕ}
    (mdata : DMData K d) (x : K) :
    distance_mixed_complex mdata (NumberField.mixedEmbedding K x) = mdata.minkowskiMap x := by
  classical
  ext i
  change ((NumberField.mixedEmbedding K x).2 ((unit_distance_complex mdata) i)) =
    ((unit_distance_complex mdata i).1).embedding x
  exact
    NumberField.mixedEmbedding.mixedEmbedding_apply_isComplex (K := K) x
      (unit_distance_complex mdata i)

lemma distance_scaled_covolume
    {T : SplitTotallyTower.{0}} (data : DistanceGrowthData T) (j : ℕ)
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
    (mdata : DMData K (Module.finrank ℚ (T.fields j)))
    (Λ : CLattic (Module.finrank ℚ (T.fields j)))
    (hΛ :
      ∀ z : ComplexSpace (Module.finrank ℚ (T.fields j)),
        z ∈ Λ.subgroup ↔
          ∃ x : K, ScaledRingIntegers K data.q x ∧ mdata.minkowskiMap x = z) :
    Λ.covolume =
      (rootDiscriminant K / (2 * (data.q : ℝ) ^ (2 : ℕ))) ^
        Module.finrank ℚ (T.fields j) := by
  classical
  let d := Module.finrank ℚ (T.fields j)
  let S : Submonoid (NumberField.RingOfIntegers K) :=
    nonZeroDivisors (NumberField.RingOfIntegers K)
  let I : FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers K)) K :=
    FractionalIdeal.spanSingleton S ((data.q : K)⁻¹)
  have hqK_ne : (data.q : K) ≠ 0 := by
    exact_mod_cast data.hq_pos.ne'
  have hqR_ne : (data.q : ℝ) ≠ 0 := by
    exact_mod_cast data.hq_pos.ne'
  let Iu : (FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers K)) K)ˣ :=
    ⟨I, I⁻¹,
      by
        dsimp [I]
        exact
          FractionalIdeal.spanSingleton_mul_inv (R₁ := NumberField.RingOfIntegers K)
            (K := K) (x := ((data.q : K)⁻¹)) (inv_ne_zero hqK_ne)
      ,
      by
        dsimp [I]
        exact
          FractionalIdeal.spanSingleton_inv_mul (R₁ := NumberField.RingOfIntegers K)
            (K := K) (x := ((data.q : K)⁻¹)) (inv_ne_zero hqK_ne)⟩
  let e : ComplexSpace d ≃L[ℝ] NumberField.mixedEmbedding.mixedSpace K :=
    (distance_mixed_complex mdata).symm
  letI : DiscreteTopology (NumberField.mixedEmbedding.idealLattice K Iu) := by
    classical
    rw [← NumberField.mixedEmbedding.span_idealLatticeBasis (K := K) (I := Iu)]
    infer_instance
  letI : IsZLattice ℝ (NumberField.mixedEmbedding.idealLattice K Iu) := by
    classical
    simp_rw [← NumberField.mixedEmbedding.span_idealLatticeBasis (K := K) (I := Iu)]
    infer_instance
  let L :
      Submodule ℤ (ComplexSpace d) :=
    ZLattice.comap ℝ (NumberField.mixedEmbedding.idealLattice K Iu) e.toLinearMap
  letI : DiscreteTopology L := by
    dsimp [L]
    infer_instance
  letI : IsZLattice ℝ L := by
    dsimp [L]
    infer_instance
  letI : Module.Free ℤ L := ZLattice.module_free ℝ L
  letI : Module.Finite ℤ L := ZLattice.module_finite ℝ L
  let bL := Module.Free.chooseBasis ℤ L
  letI : Countable Λ.subgroup := Λ.countable_subgroup
  letI : DiscreteTopology Λ.subgroup := Λ.discrete_subgroup
  letI : Countable L.toAddSubgroup := by
    change Countable L
    infer_instance
  have hL :
      ∀ z : ComplexSpace d,
        z ∈ L.toAddSubgroup ↔
          ∃ x : K, ScaledRingIntegers K data.q x ∧ mdata.minkowskiMap x = z := by
    intro z
    change
      (distance_mixed_complex mdata).symm z ∈
          NumberField.mixedEmbedding.idealLattice K Iu ↔
        ∃ x : K, ScaledRingIntegers K data.q x ∧ mdata.minkowskiMap x = z
    rw [NumberField.mixedEmbedding.mem_idealLattice]
    constructor
    · rintro ⟨x, hxI, hxz⟩
      change x ∈ I at hxI
      rcases (FractionalIdeal.mem_spanSingleton S).1 hxI with ⟨a, ha⟩
      have hxscaled : ScaledRingIntegers K data.q x := by
        refine ⟨a, ?_⟩
        have hmul := congrArg (fun t : K => (data.q : K) * t) ha
        simpa [Algebra.smul_def, hqK_ne, mul_assoc, mul_left_comm, mul_comm] using hmul
      have hz' : mdata.minkowskiMap x = z := by
        simpa [mixed_complex_embedding] using
          congrArg (distance_mixed_complex mdata) hxz
      exact ⟨x, hxscaled, hz'⟩
    · rintro ⟨x, hxscaled, rfl⟩
      refine ⟨x, ?_, ?_⟩
      · change x ∈ I
        rcases hxscaled with ⟨a, ha⟩
        rw [(FractionalIdeal.mem_spanSingleton S)]
        refine ⟨a, ?_⟩
        have hmul := congrArg (fun t : K => t * ((data.q : K)⁻¹)) ha
        simpa [Algebra.smul_def, hqK_ne, mul_assoc, mul_left_comm, mul_comm] using hmul
      · apply (distance_mixed_complex mdata).injective
        calc
          (distance_mixed_complex mdata) ((NumberField.mixedEmbedding K) x) =
              mdata.minkowskiMap x :=
            mixed_complex_embedding (mdata := mdata) x
          _ = (distance_mixed_complex mdata)
                ((distance_mixed_complex mdata).symm (mdata.minkowskiMap x)) := by
              simp
  have hsub : Λ.subgroup = L.toAddSubgroup := by
    ext z
    exact (hΛ z).trans (hL z).symm
  have hfdL :
      MeasureTheory.IsAddFundamentalDomain L.toAddSubgroup
        (ZSpan.fundamentalDomain (bL.ofZLatticeBasis ℝ)) MeasureTheory.volume := by
    simpa [L] using
      (ZLattice.isAddFundamentalDomain bL
        (MeasureTheory.volume : MeasureTheory.Measure (ComplexSpace d)))
  have hfd :
      MeasureTheory.IsAddFundamentalDomain Λ.subgroup
        (ZSpan.fundamentalDomain (bL.ofZLatticeBasis ℝ)) MeasureTheory.volume := by
    exact hsub.symm ▸ hfdL
  have hΛ_eq :
      Λ.covolume = setVolume (ZSpan.fundamentalDomain (bL.ofZLatticeBasis ℝ)) := by
    unfold CLattic.covolume setVolume
    exact congrArg ENNReal.toReal (Λ.isFundamentalDomain.measure_eq hfd)
  have hL_eq :
      setVolume (ZSpan.fundamentalDomain (bL.ofZLatticeBasis ℝ)) = ZLattice.covolume L := by
    symm
    unfold setVolume
    simpa [L] using
      (ZLattice.covolume_eq_measure_fundamentalDomain L
        (MeasureTheory.volume : MeasureTheory.Measure (ComplexSpace d))
        (ZLattice.isAddFundamentalDomain bL
          (MeasureTheory.volume : MeasureTheory.Measure (ComplexSpace d))))
  have hmeasurePres_symm :
      MeasureTheory.MeasurePreserving
        ((distance_mixed_complex mdata).symm)
        (MeasureTheory.volume : MeasureTheory.Measure (ComplexSpace d))
        (MeasureTheory.volume :
          MeasureTheory.Measure (NumberField.mixedEmbedding.mixedSpace K)) := by
    have hmeas :
        MeasureTheory.MeasurePreserving
          ((distance_mixed_complex mdata).toHomeomorph.toMeasurableEquiv)
          (MeasureTheory.volume :
            MeasureTheory.Measure (NumberField.mixedEmbedding.mixedSpace K))
          (MeasureTheory.volume : MeasureTheory.Measure (ComplexSpace d)) := by
      let R :=
        ({w : NumberField.InfinitePlace K // NumberField.InfinitePlace.IsReal w} → ℝ)
      let C :=
        ({w : NumberField.InfinitePlace K // NumberField.InfinitePlace.IsComplex w} → ℂ)
      have hreal0 :
          Fintype.card
              {w : NumberField.InfinitePlace K // NumberField.InfinitePlace.IsReal w} = 0 := by
        exact NumberField.IsTotallyComplex.nrRealPlaces_eq_zero (K := K)
      haveI : IsEmpty {w : NumberField.InfinitePlace K // NumberField.InfinitePlace.IsReal w} :=
        Fintype.card_eq_zero_iff.mp hreal0
      letI : MeasureTheory.IsProbabilityMeasure
          (MeasureTheory.volume : MeasureTheory.Measure R) := by
        have hvol :
            (MeasureTheory.volume : MeasureTheory.Measure R) =
              MeasureTheory.Measure.dirac 0 := by
          simpa [R] using (MeasureTheory.Measure.volume_pi_eq_dirac (x := (0 : R)))
        rw [hvol]
        infer_instance
      have hsnd : MeasureTheory.MeasurePreserving
          ((ContinuousLinearEquiv.uniqueProd ℝ C R).toHomeomorph.toMeasurableEquiv)
          (MeasureTheory.volume : MeasureTheory.Measure (R × C))
          (MeasureTheory.volume : MeasureTheory.Measure C) := by
        simpa [R, C] using
          (MeasureTheory.measurePreserving_snd
            (μ := (MeasureTheory.volume : MeasureTheory.Measure R))
            (ν := (MeasureTheory.volume : MeasureTheory.Measure C)))
      have hpi :
          MeasureTheory.MeasurePreserving
            (((ContinuousLinearEquiv.piCongrLeft ℝ
              (fun
                _ :
                  {w : NumberField.InfinitePlace K //
                    NumberField.InfinitePlace.IsComplex w} => ℂ)
              (unit_distance_complex mdata)).symm :
                C ≃L[ℝ] ComplexSpace d).toHomeomorph.toMeasurableEquiv)
            (MeasureTheory.volume : MeasureTheory.Measure C)
            (MeasureTheory.volume : MeasureTheory.Measure (ComplexSpace d)) := by
        have hforward :
            MeasureTheory.MeasurePreserving
              (((ContinuousLinearEquiv.piCongrLeft ℝ
                (fun
                  _ :
                    {w : NumberField.InfinitePlace K //
                      NumberField.InfinitePlace.IsComplex w} => ℂ)
                (unit_distance_complex mdata)) :
                  ComplexSpace d ≃L[ℝ] C).toHomeomorph.toMeasurableEquiv)
              (MeasureTheory.volume : MeasureTheory.Measure (ComplexSpace d))
              (MeasureTheory.volume : MeasureTheory.Measure C) := by
          simpa using
            (MeasureTheory.volume_measurePreserving_piCongrLeft
              (fun
                _ :
                  {w : NumberField.InfinitePlace K //
                    NumberField.InfinitePlace.IsComplex w} => ℂ)
              (unit_distance_complex mdata))
        exact MeasureTheory.MeasurePreserving.symm _ hforward
      change MeasureTheory.MeasurePreserving
        ((((ContinuousLinearEquiv.piCongrLeft ℝ
            (fun
              _ :
                {w : NumberField.InfinitePlace K //
                  NumberField.InfinitePlace.IsComplex w} => ℂ)
            (unit_distance_complex mdata)).symm :
              C ≃L[ℝ] ComplexSpace d).toHomeomorph.toMeasurableEquiv) ∘
          ((ContinuousLinearEquiv.uniqueProd ℝ C R).toHomeomorph.toMeasurableEquiv))
        (MeasureTheory.volume : MeasureTheory.Measure (R × C))
        (MeasureTheory.volume : MeasureTheory.Measure (ComplexSpace d))
      exact hpi.comp hsnd
    exact
      MeasureTheory.MeasurePreserving.symm
        ((distance_mixed_complex mdata).toHomeomorph.toMeasurableEquiv) hmeas
  have hcov_comap :
      ZLattice.covolume L =
        ZLattice.covolume (NumberField.mixedEmbedding.idealLattice K Iu) := by
    simpa [L] using
      (ZLattice.covolume_comap
        (L := NumberField.mixedEmbedding.idealLattice K Iu)
        (ν := (MeasureTheory.volume : MeasureTheory.Measure (ComplexSpace d)))
        (μ := (MeasureTheory.volume :
          MeasureTheory.Measure (NumberField.mixedEmbedding.mixedSpace K)))
        (e := e)
        hmeasurePres_symm)
  have hnrComplex : NumberField.InfinitePlace.nrComplexPlaces K = d := by
    have hcard :
        Fintype.card (NumberField.InfinitePlace K) = d := by
      simpa [d] using (Fintype.card_congr mdata.placeEquiv).symm
    have hcard' :
        Fintype.card (NumberField.InfinitePlace K) =
          NumberField.InfinitePlace.nrComplexPlaces K := by
      calc
        Fintype.card (NumberField.InfinitePlace K) =
            NumberField.InfinitePlace.nrRealPlaces K +
              NumberField.InfinitePlace.nrComplexPlaces K := by
              simpa using
                NumberField.InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces (K := K)
        _ = NumberField.InfinitePlace.nrComplexPlaces K := by
              rw [NumberField.IsTotallyComplex.nrRealPlaces_eq_zero (K := K), zero_add]
    exact hcard'.symm.trans hcard
  have hfinrankK : Module.finrank ℚ K = 2 * d := by
    calc
      Module.finrank ℚ K = 2 * NumberField.InfinitePlace.nrComplexPlaces K := by
        simpa using (NumberField.IsTotallyComplex.finrank (K := K))
      _ = 2 * d := by rw [hnrComplex]
  have hIabs_rat :
      FractionalIdeal.absNorm I = ((data.q : ℚ) ^ Module.finrank ℚ K)⁻¹ := by
    rw [FractionalIdeal.absNorm_span_singleton (R := NumberField.RingOfIntegers K)
      ((data.q : K)⁻¹)]
    have hpow_nonneg : 0 ≤ (data.q : ℚ) ^ Module.finrank ℚ K := by positivity
    rw [Algebra.norm_inv]
    have hnorm : Algebra.norm ℚ (data.q : K) = (data.q : ℚ) ^ Module.finrank ℚ K := by
      simpa using (Algebra.norm_algebraMap (R := ℚ) (S := K) (data.q : ℚ))
    rw [hnorm]
    rw [abs_of_nonneg (inv_nonneg.mpr hpow_nonneg)]
  have hIabs :
      ((FractionalIdeal.absNorm I : ℚ) : ℝ) =
        ((data.q : ℝ) ^ Module.finrank ℚ K)⁻¹ := by
    simpa using congrArg (fun q : ℚ => (q : ℝ)) hIabs_rat
  have hd_pos : 0 < d := by
    exact Module.finrank_pos
  have hrootpow :
      rootDiscriminant K ^ d = Real.sqrt (absDiscriminant K) := by
    unfold rootDiscriminant absDiscriminant
    rw [hfinrankK]
    have hA_nonneg : 0 ≤ |(NumberField.discr K : ℝ)| := abs_nonneg _
    have h2d_ne : (((2 * d : ℕ) : ℝ)) ≠ 0 := by positivity
    calc
      (Real.rpow |(NumberField.discr K : ℝ)| (1 / (((2 * d : ℕ) : ℝ)))) ^ d
          = Real.rpow |(NumberField.discr K : ℝ)|
              ((1 / (((2 * d : ℕ) : ℝ))) * d) := by
              rw [show
                (Real.rpow |(NumberField.discr K : ℝ)| (1 / (((2 * d : ℕ) : ℝ)))) ^ d =
                  Real.rpow
                    (Real.rpow |(NumberField.discr K : ℝ)| (1 / (((2 * d : ℕ) : ℝ))))
                    (d : ℝ) by
                    exact
                      (Real.rpow_natCast
                        (Real.rpow |(NumberField.discr K : ℝ)|
                          (1 / (((2 * d : ℕ) : ℝ)))) d).symm]
              simpa [mul_comm] using
                (Real.rpow_mul hA_nonneg (1 / (((2 * d : ℕ) : ℝ))) (d : ℝ)).symm
      _ = Real.rpow |(NumberField.discr K : ℝ)| (1 / (2 : ℝ)) := by
            congr 1
            field_simp [h2d_ne]
            rw [Nat.cast_mul]
            ring
      _ = Real.sqrt |(NumberField.discr K : ℝ)| := by
            simp [Real.sqrt_eq_rpow]
  calc
    Λ.covolume = setVolume (ZSpan.fundamentalDomain (bL.ofZLatticeBasis ℝ)) := hΛ_eq
    _ = ZLattice.covolume L := hL_eq
    _ = ZLattice.covolume (NumberField.mixedEmbedding.idealLattice K Iu) := hcov_comap
    _ = (FractionalIdeal.absNorm (Iu : FractionalIdeal S K) : ℝ) *
          (2⁻¹ : ℝ) ^ NumberField.InfinitePlace.nrComplexPlaces K *
          Real.sqrt |(NumberField.discr K : ℝ)| := by
          simpa using (NumberField.mixedEmbedding.covolume_idealLattice (K := K) Iu)
    _ = ((data.q : ℝ) ^ Module.finrank ℚ K)⁻¹ *
          (2⁻¹ : ℝ) ^ d * Real.sqrt (absDiscriminant K) := by
          rw [show (Iu : FractionalIdeal S K) = I by rfl]
          rw [hIabs, hnrComplex]
          rw [absDiscriminant]
    _ = (rootDiscriminant K / (2 * (data.q : ℝ) ^ (2 : ℕ))) ^ d := by
          rw [hfinrankK, ← hrootpow]
          rw [div_pow, mul_pow, pow_mul, inv_pow]
          field_simp [hqR_ne]

/--
Root-discriminant upper bound turned into the scalar covolume estimate used in
the paper.
-/
lemma scaled_lattice_covolume
    {T : SplitTotallyTower.{0}} (data : DistanceGrowthData T) (j : ℕ)
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
    (hroot : rootDiscriminant K ≤ data.ρ)
    (mdata : DMData K (Module.finrank ℚ (T.fields j)))
    (Λ : CLattic (Module.finrank ℚ (T.fields j)))
    (hΛ :
      ∀ z : ComplexSpace (Module.finrank ℚ (T.fields j)),
        z ∈ Λ.subgroup ↔
          ∃ x : K, ScaledRingIntegers K data.q x ∧ mdata.minkowskiMap x = z) :
    Λ.covolume ≤
      (data.ρ / (2 * (data.q : ℝ) ^ (2 : ℕ))) ^ Module.finrank ℚ (T.fields j) := by
  rw [distance_scaled_covolume data j mdata Λ hΛ]
  have hroot_nonneg : 0 ≤ rootDiscriminant K := by
    unfold rootDiscriminant
    exact Real.rpow_nonneg (by unfold absDiscriminant; positivity) _
  have hbase_nonneg : 0 ≤ rootDiscriminant K / (2 * (data.q : ℝ) ^ (2 : ℕ)) := by
    exact div_nonneg hroot_nonneg (by positivity)
  exact
    pow_le_pow_left₀
      hbase_nonneg
      (div_le_div_of_nonneg_right hroot (by positivity))
      _

/-- The closed polydisc is measurable. -/
lemma distance_measurable_polydisc
    {d : ℕ} {r : ℝ} :
    MeasurableSet (unitDistancePolydisc d r) := by
  classical
  by_cases h : Nonempty (Fin d)
  · letI := h
    have hEq :
        unitDistancePolydisc d r = Metric.closedBall (0 : ComplexSpace d) r := by
      ext z
      simp [unitDistancePolydisc, Metric.mem_closedBall, dist_eq_norm,
        pi_norm_le_iff_of_nonempty]
    rw [hEq]
    exact measurableSet_closedBall
  · haveI : IsEmpty (Fin d) := not_nonempty_iff.mp h
    have hEq : unitDistancePolydisc d r = (Set.univ : Set (ComplexSpace d)) := by
      ext z
      simp [unitDistancePolydisc]
    rw [hEq]
    exact MeasurableSet.univ

/-- The closed polydisc is bounded. -/
lemma distance_set_polydisc
    {d : ℕ} {r : ℝ} (_hr : 0 ≤ r) :
    IsBoundedSet (unitDistancePolydisc d r) := by
  classical
  by_cases h : Nonempty (Fin d)
  · letI := h
    have hEq :
        unitDistancePolydisc d r = Metric.closedBall (0 : ComplexSpace d) r := by
      ext z
      simp [unitDistancePolydisc, Metric.mem_closedBall, dist_eq_norm,
        pi_norm_le_iff_of_nonempty]
    refine ⟨r, ?_⟩
    intro z hz
    have hz' : z ∈ Metric.closedBall (0 : ComplexSpace d) r := by simpa [hEq] using hz
    simpa [Metric.mem_closedBall, dist_eq_norm] using hz'
  · haveI : IsEmpty (Fin d) := not_nonempty_iff.mp h
    refine ⟨0, ?_⟩
    intro z hz
    have hz0 : z = 0 := Subsingleton.elim _ _
    simp [hz0]

/-- The volume of the radius-`r` polydisc is `(π r^2)^d`. -/
lemma distance_volume_polydisc
    {d : ℕ} {r : ℝ} (hr : 0 ≤ r) :
    setVolume (unitDistancePolydisc d r) = (Real.pi * r ^ (2 : ℕ)) ^ d := by
  classical
  by_cases h : Nonempty (Fin d)
  · letI := h
    have hEq :
        unitDistancePolydisc d r = Metric.closedBall (0 : ComplexSpace d) r := by
      ext z
      simp [unitDistancePolydisc, Metric.mem_closedBall, dist_eq_norm,
        pi_norm_le_iff_of_nonempty]
    have hvol :
        MeasureTheory.volume (Metric.closedBall (0 : ComplexSpace d) r) =
          ∏ _ : Fin d, MeasureTheory.volume (Metric.closedBall (0 : ℂ) r) := by
      simpa using MeasureTheory.volume_pi_closedBall (fun _ : Fin d => (0 : ℂ)) hr
    rw [setVolume, hEq, hvol, Finset.prod_const]
    simp [Complex.volume_closedBall, hr, pow_two, mul_comm, mul_left_comm]
  · haveI : IsEmpty (Fin d) := not_nonempty_iff.mp h
    have hd0 : d = 0 := by
      by_contra hd0
      exact h (Fin.pos_iff_nonempty.mp (Nat.pos_of_ne_zero hd0))
    subst hd0
    have hpoly0 : unitDistancePolydisc 0 r = (Set.univ : Set (Fin 0 → ℂ)) := by
      ext z
      simp [unitDistancePolydisc]
    have hUniv :
        (Set.univ : Set (Fin 0 → ℂ)) =
          Set.pi Set.univ (fun _ : Fin 0 => (Set.univ : Set ℂ)) := by
      ext z
      simp
    rw [hpoly0, setVolume, hUniv, MeasureTheory.volume_pi_pi]
    simp

/--
Applying the averaging lemma to the inner polydisc `B_{R-1}` yields a translate
containing at least `C_X^d` lattice points.
-/
lemma distance_polydisc_translate
    {T : SplitTotallyTower.{0}} (data : DistanceGrowthData T) (j : ℕ)
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
    (hroot : rootDiscriminant K ≤ data.ρ)
    (mdata : DMData K (Module.finrank ℚ (T.fields j)))
    (Λ : CLattic (Module.finrank ℚ (T.fields j)))
    (hΛ :
      ∀ z : ComplexSpace (Module.finrank ℚ (T.fields j)),
        z ∈ Λ.subgroup ↔
          ∃ x : K, ScaledRingIntegers K data.q x ∧ mdata.minkowskiMap x = z) :
    ∃ t : ComplexSpace (Module.finrank ℚ (T.fields j)),
      latticePointCount Λ
          (translateSet t
            (unitDistancePolydisc (Module.finrank ℚ (T.fields j)) (data.R - 1))) ≥
        data.CX ^ Module.finrank ℚ (T.fields j) := by
  let d := Module.finrank ℚ (T.fields j)
  let Ω := unitDistancePolydisc d (data.R - 1)
  have hR_nonneg : 0 ≤ data.R - 1 := by linarith [data.hR_gt]
  have hΩ_bounded : IsBoundedSet Ω := by
    simpa [Ω] using distance_set_polydisc (d := d) hR_nonneg
  have hΩ_measurable : MeasurableSet Ω := by
    simpa [Ω] using distance_measurable_polydisc (d := d) (r := data.R - 1)
  rcases averaging_lattice Λ Ω hΩ_bounded hΩ_measurable with ⟨t, ht⟩
  refine ⟨t, ?_⟩
  have hvol :
      setVolume Ω = (Real.pi * (data.R - 1) ^ (2 : ℕ)) ^ d := by
    simpa [Ω] using distance_volume_polydisc (d := d) hR_nonneg
  have hcovol :
      Λ.covolume ≤ (data.ρ / (2 * (data.q : ℝ) ^ (2 : ℕ))) ^ d := by
    simpa [d] using scaled_lattice_covolume data j hroot mdata Λ hΛ
  have hρ_pos : 0 < data.ρ := data.hρ
  have hq_pos : 0 < (data.q : ℝ) := by exact_mod_cast data.hq_pos
  have hq2_pos : 0 < 2 * (data.q : ℝ) ^ (2 : ℕ) := by positivity
  have hB_pos : 0 <
      (data.ρ / (2 * (data.q : ℝ) ^ (2 : ℕ))) ^ d := by
    positivity
  have hnum_nonneg : 0 ≤ (Real.pi * (data.R - 1) ^ (2 : ℕ)) ^ d := by
    positivity
  have hinv :
      ((data.ρ / (2 * (data.q : ℝ) ^ (2 : ℕ))) ^ d)⁻¹ ≤ Λ.covolume⁻¹ := by
    exact (inv_le_inv₀ hB_pos Λ.positive_covolume).2 hcovol
  have havg :
      data.CX ^ d ≤ setVolume Ω / Λ.covolume := by
    rw [hvol, div_eq_mul_inv]
    have hmul :
        (Real.pi * (data.R - 1) ^ (2 : ℕ)) ^ d *
            ((data.ρ / (2 * (data.q : ℝ) ^ (2 : ℕ))) ^ d)⁻¹ ≤
          (Real.pi * (data.R - 1) ^ (2 : ℕ)) ^ d * Λ.covolume⁻¹ := by
      exact mul_le_mul_of_nonneg_left hinv hnum_nonneg
    have hbase :
        (Real.pi * (data.R - 1) ^ (2 : ℕ)) /
            (data.ρ / (2 * (data.q : ℝ) ^ (2 : ℕ))) =
          data.CX := by
      rw [data.hCX_def]
      field_simp [hρ_pos.ne', hq2_pos.ne']
    have hcalc :
        (Real.pi * (data.R - 1) ^ (2 : ℕ)) ^ d *
            ((data.ρ / (2 * (data.q : ℝ) ^ (2 : ℕ))) ^ d)⁻¹ =
          data.CX ^ d := by
      rw [← div_eq_mul_inv, ← div_pow, hbase]
    rw [← hcalc]
    exact hmul
  exact le_trans havg ht

/--
Extract a finite subset of `K` from a finite set of lattice points in the image
of `q⁻¹ O_K`, keeping track of both the cardinality and the defining region in
`ComplexSpace d`.
-/
lemma extract_lattice_points
    {T : SplitTotallyTower.{0}} (data : DistanceGrowthData T) (j : ℕ)
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
    (mdata : DMData K (Module.finrank ℚ (T.fields j)))
    (Λ : CLattic (Module.finrank ℚ (T.fields j)))
    (hΛ :
      ∀ z : ComplexSpace (Module.finrank ℚ (T.fields j)),
        z ∈ Λ.subgroup ↔
          ∃ x : K, ScaledRingIntegers K data.q x ∧ mdata.minkowskiMap x = z)
    (Ω : Set (ComplexSpace (Module.finrank ℚ (T.fields j))))
    (hΩ_bounded : IsBoundedSet Ω) :
    ∃ Y : Finset K,
      (Y.card : ℝ) = latticePointCount Λ Ω ∧
      (∀ x ∈ Y, ScaledRingIntegers K data.q x ∧ mdata.minkowskiMap x ∈ Ω) := by
  classical
  let P := ↥(latticePointSet Λ Ω)
  letI : Fintype P := (lattice_point_bounded Λ Ω hΩ_bounded).fintype
  have hrep :
      ∀ z : P, ∃ x : K,
        ScaledRingIntegers K data.q x ∧
          mdata.minkowskiMap x =
            ((z.1 : Λ.subgroup) : ComplexSpace (Module.finrank ℚ (T.fields j))) :=
    by
      intro z
      exact (hΛ (((z.1 : Λ.subgroup) : ComplexSpace (Module.finrank ℚ (T.fields j))))).1 z.1.2
  choose rep hrep_scaled hrep_map using hrep
  have hrep_inj : Function.Injective rep := by
    intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    calc
      ((a.1 : Λ.subgroup) : ComplexSpace (Module.finrank ℚ (T.fields j))) =
          mdata.minkowskiMap (rep a) := (hrep_map a).symm
      _ = mdata.minkowskiMap (rep b) := by rw [hab]
      _ = ((b.1 : Λ.subgroup) : ComplexSpace (Module.finrank ℚ (T.fields j))) := hrep_map b
  let Y : Finset K := (Finset.univ : Finset P).image rep
  refine ⟨Y, ?_, ?_⟩
  · rw [latticePointCount]
    calc
      (Y.card : ℝ) = ((Finset.univ : Finset P).card : ℝ) := by
        exact_mod_cast Finset.card_image_of_injective (s := Finset.univ) (f := rep) hrep_inj
      _ = (((latticePointSet Λ Ω).encard).toNat : ℝ) := by
        change ((Fintype.card P : ℕ) : ℝ) = ((Nat.card P : ℕ) : ℝ)
        exact congrArg (fun n : ℕ => (n : ℝ)) (Nat.card_eq_fintype_card (α := P)).symm
  · intro x hx
    rcases Finset.mem_image.mp hx with ⟨z, -, rfl⟩
    refine ⟨hrep_scaled z, ?_⟩
    rw [hrep_map z]
    change z.1 ∈ latticePointSet Λ Ω
    exact z.2

/--
Images of distinct points of `q⁻¹ O_K` under the Minkowski embedding are
separated in at least one coordinate by `q⁻¹`.
-/
lemma scaled_images_separated
    {T : SplitTotallyTower.{0}} (data : DistanceGrowthData T) (j : ℕ)
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
    (mdata : DMData K (Module.finrank ℚ (T.fields j))) :
    ∀ {x y : K}, x ≠ y →
      ScaledRingIntegers K data.q x →
      ScaledRingIntegers K data.q y →
      ∃ i : Fin (Module.finrank ℚ (T.fields j)),
        (1 : ℝ) / (data.q : ℝ) ≤
          ‖mdata.minkowskiMap x i - mdata.minkowskiMap y i‖ := by
  classical
  intro x y hxy hx hy
  by_contra hsep
  push Not at hsep
  rcases hx with ⟨ax, hax⟩
  rcases hy with ⟨ay, hay⟩
  let a : NumberField.RingOfIntegers K := ax - ay
  have ha_cast : (a : K) = (data.q : K) * (x - y) := by
    change
      (algebraMap (NumberField.RingOfIntegers K) K ax) -
          algebraMap (NumberField.RingOfIntegers K) K ay =
        (data.q : K) * (x - y)
    rw [hax, hay, mul_sub]
  have hqK_ne : (data.q : K) ≠ 0 := Nat.cast_ne_zero.mpr data.hq_pos.ne'
  have ha_ne : a ≠ 0 := by
    intro ha0
    have hmul_zero : (data.q : K) * (x - y) = 0 := by
      have hcoe_zero : ((a : NumberField.RingOfIntegers K) : K) = 0 := by
        simpa using congrArg (fun z : NumberField.RingOfIntegers K => (z : K)) ha0
      simpa [ha_cast] using hcoe_zero
    exact hxy (sub_eq_zero.mp ((mul_eq_zero.mp hmul_zero).resolve_left hqK_ne))
  let w0 : NumberField.InfinitePlace K := Classical.choice inferInstance
  have hplace_lt_one : ∀ w : NumberField.InfinitePlace K, w a < 1 := by
    intro w
    let i : Fin (Module.finrank ℚ (T.fields j)) := mdata.placeEquiv.symm w
    have hi : mdata.placeEquiv i = w := by
      simp [i]
    have hcoord :
        ‖mdata.minkowskiMap x i - mdata.minkowskiMap y i‖ <
          (1 : ℝ) / (data.q : ℝ) :=
      hsep i
    have hqR_pos : 0 < (data.q : ℝ) := by
      exact_mod_cast data.hq_pos
    have hmul_lt_one :
        (data.q : ℝ) *
            ‖mdata.minkowskiMap x i - mdata.minkowskiMap y i‖ < 1 := by
      have hmul := (lt_div_iff₀ hqR_pos).mp hcoord
      simpa [mul_comm] using hmul
    calc
      w a = ‖mdata.embedding i (a : K)‖ := by
        simpa [DMData.embedding, hi] using
          (NumberField.InfinitePlace.norm_embedding_eq (w := w) (x := (a : K))).symm
      _ = ‖mdata.embedding i ((data.q : K) * (x - y))‖ := by
        rw [ha_cast]
      _ = ‖(data.q : ℂ) * mdata.embedding i (x - y)‖ := by
        simp [map_mul]
      _ = (data.q : ℝ) * ‖mdata.embedding i (x - y)‖ := by
        rw [Complex.norm_mul]
        simp
      _ = (data.q : ℝ) * ‖mdata.minkowskiMap x i - mdata.minkowskiMap y i‖ := by
        simp [DMData.minkowskiMap, DMData.embedding, map_sub]
      _ < 1 := hmul_lt_one
  have hw0_ge : 1 ≤ w0 a :=
    NumberField.InfinitePlace.one_le_of_lt_one (w := w0) ha_ne (fun z _ => hplace_lt_one z)
  have hw0_lt : w0 a < 1 := hplace_lt_one w0
  exact (not_lt_of_ge hw0_ge) hw0_lt

/--
Generic packing bound for a finite subset of a translate of a polydisc, under a
coordinatewise separation hypothesis.
-/
lemma distance_polydisc_packing
    {d : ℕ} (R δ : ℝ) (t : ComplexSpace d) (X : Finset (ComplexSpace d))
    (hδ : 0 < δ)
    (hX_mem : ∀ x ∈ X, x ∈ translateSet t (unitDistancePolydisc d R))
    (hsep :
      ∀ {x y : ComplexSpace d}, x ∈ X → y ∈ X → x ≠ y →
        ∃ i : Fin d, δ ≤ ‖x i - y i‖) :
    (X.card : ℝ) ≤ ((R + δ / 2) / (δ / 2)) ^ (2 * d) := by
  classical
  by_cases hfin : Nonempty (Fin d)
  · letI := hfin
    by_cases hX_empty : X = ∅
    · simp [hX_empty]
      have hpow_nonneg :
          0 ≤ ((((R + δ / 2) / (δ / 2)) ^ d) ^ (2 : ℕ)) := by
        positivity
      simpa [pow_mul, Nat.mul_comm] using hpow_nonneg
    · let r : ℝ := δ / 2
      have hr_pos : 0 < r := by
        dsimp [r]
        linarith
      obtain ⟨x0, hx0⟩ := Finset.nonempty_iff_ne_empty.mpr hX_empty
      have hx0_mem : x0 ∈ translateSet t (unitDistancePolydisc d R) := hX_mem x0 hx0
      have hR_nonneg : 0 ≤ R := by
        have hx0_coord : ∀ i : Fin d, ‖x0 i - t i‖ ≤ R := by
          simpa [translateSet, unitDistancePolydisc] using hx0_mem
        exact le_trans (norm_nonneg _) (hx0_coord (Classical.choice hfin))
      have houter_nonneg : 0 ≤ R + r := add_nonneg hR_nonneg hr_pos.le
      have houter_eq :
          translateSet t (unitDistancePolydisc d (R + r)) = Metric.closedBall t (R + r) := by
        ext z
        simp [translateSet, unitDistancePolydisc, Metric.mem_closedBall, dist_eq_norm,
          pi_norm_le_iff_of_nonempty]
      have houter_vol :
          setVolume (translateSet t (unitDistancePolydisc d (R + r))) =
            (Real.pi * (R + r) ^ (2 : ℕ)) ^ d := by
        rw [houter_eq, setVolume]
        have hvol :
            MeasureTheory.volume (Metric.closedBall t (R + r)) =
              ∏ i : Fin d, MeasureTheory.volume (Metric.closedBall (t i) (R + r)) := by
          simpa using MeasureTheory.volume_pi_closedBall t houter_nonneg
        rw [hvol, ENNReal.toReal_prod]
        simp [Complex.volume_closedBall, houter_nonneg, pow_two, mul_comm]
      have houter_ne_top :
          MeasureTheory.volume (translateSet t (unitDistancePolydisc d (R + r))) ≠ ⊤ := by
        rw [houter_eq]
        have hvol :
            MeasureTheory.volume (Metric.closedBall t (R + r)) =
              ∏ i : Fin d, MeasureTheory.volume (Metric.closedBall (t i) (R + r)) := by
          simpa using MeasureTheory.volume_pi_closedBall t houter_nonneg
        rw [hvol]
        exact ENNReal.prod_ne_top fun i hi => by
          rw [Complex.volume_closedBall]
          exact ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top) (by simp)
      have hsmall_vol :
          ∀ x : ComplexSpace d,
            setVolume (Metric.ball x r) = (Real.pi * r ^ (2 : ℕ)) ^ d := by
        intro x
        rw [setVolume]
        have hvol :
            MeasureTheory.volume (Metric.ball x r) =
              ∏ i : Fin d, MeasureTheory.volume (Metric.ball (x i) r) := by
          simpa using MeasureTheory.volume_pi_ball x hr_pos
        rw [hvol, ENNReal.toReal_prod]
        simp [Complex.volume_ball, hr_pos.le, pow_two, mul_comm]
      have hsmall_real :
          ∀ x : ComplexSpace d,
            MeasureTheory.volume.real (Metric.ball x r) = (Real.pi * r ^ (2 : ℕ)) ^ d := by
        intro x
        simpa [setVolume, MeasureTheory.measureReal_def] using hsmall_vol x
      have hpair :
          Set.PairwiseDisjoint (↑X : Set (ComplexSpace d)) (fun x => Metric.ball x r) := by
        intro x hx y hy hxy
        refine Set.disjoint_left.2 ?_
        intro z hzx hzy
        obtain ⟨i, hi_sep⟩ := hsep hx hy hxy
        have hzx_coord : ∀ j : Fin d, ‖z j - x j‖ < r := by
          have hzx_dist : dist z x < r := by
            simpa [Metric.mem_ball] using hzx
          simpa [dist_eq_norm] using (dist_pi_lt_iff hr_pos).1 hzx_dist
        have hzy_coord : ∀ j : Fin d, ‖z j - y j‖ < r := by
          have hzy_dist : dist z y < r := by
            simpa [Metric.mem_ball] using hzy
          simpa [dist_eq_norm] using (dist_pi_lt_iff hr_pos).1 hzy_dist
        have hlt : ‖x i - y i‖ < δ := by
          have hxz : ‖x i - z i‖ < r := by
            simpa [norm_sub_rev] using hzx_coord i
          have hzy' : ‖z i - y i‖ < r := hzy_coord i
          calc
            ‖x i - y i‖ = ‖(x i - z i) + (z i - y i)‖ := by ring_nf
            _ ≤ ‖x i - z i‖ + ‖z i - y i‖ := norm_add_le _ _
            _ < r + r := add_lt_add hxz hzy'
            _ = δ := by
              dsimp [r]
              ring
        exact (not_lt_of_ge hi_sep) hlt
      have hunion_subset :
          (⋃ x ∈ X, Metric.ball x r) ⊆ translateSet t (unitDistancePolydisc d (R + r)) := by
        intro z hz
        simp only [Set.mem_iUnion] at hz
        rcases hz with ⟨x, hxX, hzx⟩
        have hx_mem : x ∈ translateSet t (unitDistancePolydisc d R) := hX_mem x hxX
        have hx_coord : ∀ i : Fin d, ‖x i - t i‖ ≤ R := by
          simpa [translateSet, unitDistancePolydisc] using hx_mem
        have hzx_coord : ∀ i : Fin d, ‖z i - x i‖ < r := by
          have hzx_dist : dist z x < r := by
            simpa [Metric.mem_ball] using hzx
          simpa [dist_eq_norm] using (dist_pi_lt_iff hr_pos).1 hzx_dist
        change ∀ i : Fin d, ‖z i - t i‖ ≤ R + r
        intro i
        calc
          ‖z i - t i‖ = ‖(z i - x i) + (x i - t i)‖ := by ring_nf
          _ ≤ ‖z i - x i‖ + ‖x i - t i‖ := norm_add_le _ _
          _ ≤ r + R := add_le_add (le_of_lt (hzx_coord i)) (hx_coord i)
          _ = R + r := by ring
      have hunion_vol :
          setVolume (⋃ x ∈ X, Metric.ball x r) =
            (X.card : ℝ) * (Real.pi * r ^ (2 : ℕ)) ^ d := by
        change MeasureTheory.volume.real (⋃ x ∈ X, Metric.ball x r) =
            (X.card : ℝ) * (Real.pi * r ^ (2 : ℕ)) ^ d
        rw [MeasureTheory.measureReal_biUnion_finset (μ := MeasureTheory.volume) hpair
          (fun x hx => measurableSet_ball)]
        calc
          ∑ x ∈ X, MeasureTheory.volume.real (Metric.ball x r) =
              ∑ x ∈ X, (Real.pi * r ^ (2 : ℕ)) ^ d := by
                apply Finset.sum_congr rfl
                intro x hx
                exact hsmall_real x
          _ = (X.card : ℝ) * (Real.pi * r ^ (2 : ℕ)) ^ d := by
                rw [Finset.sum_const, nsmul_eq_mul]
      have hcompare :
          (X.card : ℝ) * (Real.pi * r ^ (2 : ℕ)) ^ d ≤
            (Real.pi * (R + r) ^ (2 : ℕ)) ^ d := by
        calc
          (X.card : ℝ) * (Real.pi * r ^ (2 : ℕ)) ^ d =
              setVolume (⋃ x ∈ X, Metric.ball x r) := hunion_vol.symm
          _ ≤ setVolume (translateSet t (unitDistancePolydisc d (R + r))) := by
                change MeasureTheory.volume.real (⋃ x ∈ X, Metric.ball x r) ≤
                    MeasureTheory.volume.real (translateSet t (unitDistancePolydisc d (R + r)))
                exact MeasureTheory.measureReal_mono hunion_subset houter_ne_top
          _ = (Real.pi * (R + r) ^ (2 : ℕ)) ^ d := houter_vol
      have hfactor_pos : 0 < (Real.pi * r ^ (2 : ℕ)) ^ d := by
        positivity
      have hscale :
          ((R + r) / r) ^ (2 * d) * (Real.pi * r ^ (2 : ℕ)) ^ d =
            (Real.pi * (R + r) ^ (2 : ℕ)) ^ d := by
        have hr_ne : r ≠ 0 := by
          linarith
        calc
          ((R + r) / r) ^ (2 * d) * (Real.pi * r ^ (2 : ℕ)) ^ d =
              (((R + r) / r) ^ (2 : ℕ)) ^ d * (Real.pi * r ^ (2 : ℕ)) ^ d := by
                rw [← pow_mul]
          _ = ((((R + r) / r) ^ (2 : ℕ)) * (Real.pi * r ^ (2 : ℕ))) ^ d := by
                rw [← mul_pow]
          _ = (Real.pi * (R + r) ^ (2 : ℕ)) ^ d := by
                congr 1
                field_simp [Real.pi_ne_zero, hr_ne]
      have hfinal :
          (X.card : ℝ) ≤ ((R + r) / r) ^ (2 * d) := by
        have hcompare' :
            (X.card : ℝ) * (Real.pi * r ^ (2 : ℕ)) ^ d ≤
              ((R + r) / r) ^ (2 * d) * (Real.pi * r ^ (2 : ℕ)) ^ d := by
          simpa [hscale] using hcompare
        exact le_of_mul_le_mul_right hcompare' hfactor_pos
      simpa [r] using hfinal
  · haveI : IsEmpty (Fin d) := not_nonempty_iff.mp hfin
    have hd0 : d = 0 := by
      by_contra hd0
      exact hfin (Fin.pos_iff_nonempty.mp (Nat.pos_of_ne_zero hd0))
    subst hd0
    have hcard_le : X.card ≤ 1 := by
      refine Finset.card_le_one.mpr ?_
      intro x hx y hy
      exact Subsingleton.elim _ _
    simpa using (show (X.card : ℝ) ≤ (1 : ℝ) from by exact_mod_cast hcard_le)

/--
At the `K`-level, the geometric part of the paper constructs large inner sets
`Y_j` and outer sets `X_j`, with the key shift-closure property
`x + u ∈ X_j` for every `x ∈ Y_j` and every unit element `u ∈ U`.
-/
lemma container_geometry_cm
    {T : SplitTotallyTower.{0}} (data : DistanceGrowthData T) (j : ℕ)
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
    (hcomplex :
      NumberField.InfinitePlace.nrComplexPlaces K = Module.finrank ℚ (T.fields j))
    (hroot : rootDiscriminant K ≤ data.ρ)
    (U : Finset K)
    (hU_allEmb : ∀ u ∈ U, ∀ σ : K →+* ℂ, ‖σ u‖ = 1)
    (hU_scaled : ∀ u ∈ U, ScaledRingIntegers K data.q u) :
    ∃ Y X : Finset K,
      data.CX ^ Module.finrank ℚ (T.fields j) ≤ (Y.card : ℝ) ∧
      ((X.card : ℝ) ≤ data.A ^ Module.finrank ℚ (T.fields j)) ∧
      (∀ x ∈ Y, ScaledRingIntegers K data.q x) ∧
      (∀ x ∈ X, ScaledRingIntegers K data.q x) ∧
      (∀ x ∈ Y, x ∈ X) ∧
      (∀ x ∈ Y, ∀ u ∈ U, x + u ∈ X) := by
  classical
  let d := Module.finrank ℚ (T.fields j)
  rcases distance_minkowski_data (T := T) j hcomplex with ⟨mdata⟩
  rcases distance_scaled_lattice data j mdata with ⟨Λ, hΛ⟩
  rcases distance_polydisc_translate data j hroot mdata Λ hΛ with ⟨t, ht⟩
  let Ωin : Set (ComplexSpace d) :=
    translateSet t (unitDistancePolydisc d (data.R - 1))
  let Ωout : Set (ComplexSpace d) :=
    translateSet t (unitDistancePolydisc d data.R)
  have hR_nonneg : 0 ≤ data.R := by
    linarith [data.hR_gt]
  have hR1_nonneg : 0 ≤ data.R - 1 := by
    linarith [data.hR_gt]
  have hΩin_bounded : IsBoundedSet Ωin := by
    simpa [Ωin] using
      bounded_set_translate
        (t := t)
        (Ω := unitDistancePolydisc d (data.R - 1))
        (distance_set_polydisc (d := d) hR1_nonneg)
  have hΩout_bounded : IsBoundedSet Ωout := by
    simpa [Ωout] using
      bounded_set_translate
        (t := t)
        (Ω := unitDistancePolydisc d data.R)
        (distance_set_polydisc (d := d) hR_nonneg)
  have hΩsubset : Ωin ⊆ Ωout := by
    intro z hz
    dsimp [Ωin, Ωout, translateSet, unitDistancePolydisc] at hz ⊢
    intro i
    exact le_trans (hz i) (by linarith)
  let Pout := ↥(latticePointSet Λ Ωout)
  let Pin := ↥(latticePointSet Λ Ωin)
  letI : Fintype Pout :=
    (lattice_point_bounded Λ Ωout hΩout_bounded).fintype
  letI : Fintype Pin :=
    (lattice_point_bounded Λ Ωin hΩin_bounded).fintype
  let innerToOuter : Pin ↪ Pout :=
    { toFun := fun z => ⟨z.1, hΩsubset z.2⟩
      inj' := by
        intro a b h
        apply Subtype.ext
        exact congrArg (fun z : Pout => z.1) h }
  have hrepOut :
      ∀ z : Pout, ∃ x : K,
        ScaledRingIntegers K data.q x ∧
          mdata.minkowskiMap x = ((z.1 : Λ.subgroup) : ComplexSpace d) := by
    intro z
    exact (hΛ (((z.1 : Λ.subgroup) : ComplexSpace d))).1 z.1.2
  choose repOut hrepOut_scaled hrepOut_map using hrepOut
  have hrepOut_inj : Function.Injective repOut := by
    intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    calc
      ((a.1 : Λ.subgroup) : ComplexSpace d) = mdata.minkowskiMap (repOut a) :=
        (hrepOut_map a).symm
      _ = mdata.minkowskiMap (repOut b) := by rw [hab]
      _ = ((b.1 : Λ.subgroup) : ComplexSpace d) := hrepOut_map b
  have hrepIn_inj : Function.Injective (fun z : Pin => repOut (innerToOuter z)) := by
    intro a b hab
    exact innerToOuter.injective (hrepOut_inj hab)
  let X : Finset K := (Finset.univ : Finset Pout).image repOut
  let Y : Finset K := (Finset.univ : Finset Pin).image fun z => repOut (innerToOuter z)
  have hX_card :
      (X.card : ℝ) = latticePointCount Λ Ωout := by
    rw [latticePointCount]
    calc
      (X.card : ℝ) = ((Finset.univ : Finset Pout).card : ℝ) := by
        exact_mod_cast
          Finset.card_image_of_injective (s := Finset.univ) (f := repOut) hrepOut_inj
      _ = (((latticePointSet Λ Ωout).encard).toNat : ℝ) := by
        change ((Fintype.card Pout : ℕ) : ℝ) = ((Nat.card Pout : ℕ) : ℝ)
        exact congrArg (fun n : ℕ => (n : ℝ)) (Nat.card_eq_fintype_card (α := Pout)).symm
  have hY_card :
      (Y.card : ℝ) = latticePointCount Λ Ωin := by
    rw [latticePointCount]
    calc
      (Y.card : ℝ) = ((Finset.univ : Finset Pin).card : ℝ) := by
        exact_mod_cast
          Finset.card_image_of_injective
            (s := Finset.univ) (f := fun z : Pin => repOut (innerToOuter z)) hrepIn_inj
      _ = (((latticePointSet Λ Ωin).encard).toNat : ℝ) := by
        change ((Fintype.card Pin : ℕ) : ℝ) = ((Nat.card Pin : ℕ) : ℝ)
        exact congrArg (fun n : ℕ => (n : ℝ)) (Nat.card_eq_fintype_card (α := Pin)).symm
  have hY_lower : data.CX ^ d ≤ (Y.card : ℝ) := by
    have ht' : data.CX ^ d ≤ latticePointCount Λ Ωin := by
      simpa [d, Ωin] using ht
    calc
      data.CX ^ d ≤ latticePointCount Λ Ωin := ht'
      _ = (Y.card : ℝ) := hY_card.symm
  let outEmb : Pout ↪ ComplexSpace d :=
    { toFun := fun z => ((z.1 : Λ.subgroup) : ComplexSpace d)
      inj' := by
        intro a b h
        apply Subtype.ext
        apply Subtype.ext
        exact h }
  let Qout : Finset (ComplexSpace d) := (Finset.univ : Finset Pout).map outEmb
  have hQout_mem :
      ∀ z ∈ Qout, z ∈ translateSet t (unitDistancePolydisc d data.R) := by
    intro z hz
    rcases Finset.mem_map.mp hz with ⟨w, -, rfl⟩
    exact w.2
  have hQout_sep :
      ∀ {z w : ComplexSpace d}, z ∈ Qout → w ∈ Qout → z ≠ w →
        ∃ i : Fin d, (1 : ℝ) / (data.q : ℝ) ≤ ‖z i - w i‖ := by
    intro z w hz hw hzw
    rcases Finset.mem_map.mp hz with ⟨a, -, rfl⟩
    rcases Finset.mem_map.mp hw with ⟨b, -, rfl⟩
    have hab : repOut a ≠ repOut b := by
      intro habeq
      apply hzw
      calc
        ((a.1 : Λ.subgroup) : ComplexSpace d) = mdata.minkowskiMap (repOut a) :=
          (hrepOut_map a).symm
        _ = mdata.minkowskiMap (repOut b) := by rw [habeq]
        _ = ((b.1 : Λ.subgroup) : ComplexSpace d) := hrepOut_map b
    simpa [hrepOut_map a, hrepOut_map b] using
      scaled_images_separated
        (T := T) (data := data) (j := j) (mdata := mdata) hab
        (hrepOut_scaled a) (hrepOut_scaled b)
  have hqinv_pos : 0 < (1 : ℝ) / (data.q : ℝ) := by
    have hq_pos : 0 < (data.q : ℝ) := by
      exact_mod_cast data.hq_pos
    exact one_div_pos.mpr hq_pos
  have hQout_bound :
      (Qout.card : ℝ) ≤
        ((data.R + ((1 : ℝ) / (data.q : ℝ)) / 2) / (((1 : ℝ) / (data.q : ℝ)) / 2)) ^
          (2 * d) := by
    exact
      distance_polydisc_packing
        data.R ((1 : ℝ) / (data.q : ℝ)) t Qout hqinv_pos hQout_mem hQout_sep
  have hratio :
      (data.R + ((1 : ℝ) / (data.q : ℝ)) / 2) / (((1 : ℝ) / (data.q : ℝ)) / 2) =
        1 + 2 * data.R * (data.q : ℝ) := by
    have hq_ne : (data.q : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt data.hq_pos)
    field_simp [hq_ne]
    ring
  have hA_pow :
      (1 + 2 * data.R * (data.q : ℝ)) ^ (2 * d) = data.A ^ d := by
    rw [data.hA_def, pow_mul]
  have hXQout_card : X.card = Qout.card := by
    calc
      X.card = (Finset.univ : Finset Pout).card := by
        exact Finset.card_image_of_injective (s := Finset.univ) (f := repOut) hrepOut_inj
      _ = Qout.card := by
        simp [Qout, outEmb]
  have hX_upper : (X.card : ℝ) ≤ data.A ^ d := by
    calc
      (X.card : ℝ) = (Qout.card : ℝ) := by exact_mod_cast hXQout_card
      _ ≤
          ((data.R + ((1 : ℝ) / (data.q : ℝ)) / 2) / (((1 : ℝ) / (data.q : ℝ)) / 2)) ^
            (2 * d) := hQout_bound
      _ = (1 + 2 * data.R * (data.q : ℝ)) ^ (2 * d) := by rw [hratio]
      _ = data.A ^ d := hA_pow
  have hY_scaled' : ∀ x ∈ Y, ScaledRingIntegers K data.q x := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨z, -, rfl⟩
    exact hrepOut_scaled (innerToOuter z)
  have hX_scaled' : ∀ x ∈ X, ScaledRingIntegers K data.q x := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨z, -, rfl⟩
    exact hrepOut_scaled z
  have hY_subset : ∀ x ∈ Y, x ∈ X := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨z, -, rfl⟩
    simp [X]
  have hshift : ∀ x ∈ Y, ∀ u ∈ U, x + u ∈ X := by
    intro x hx u hu
    rcases Finset.mem_image.mp hx with ⟨z, -, rfl⟩
    have hx_scaled : ScaledRingIntegers K data.q (repOut (innerToOuter z)) :=
      hrepOut_scaled (innerToOuter z)
    have hxu_scaled : ScaledRingIntegers K data.q (repOut (innerToOuter z) + u) :=
      scaled_integers_add hx_scaled (hU_scaled u hu)
    have hz_inner : ((z.1 : Λ.subgroup) : ComplexSpace d) ∈ Ωin := z.2
    have hz_rep :
        mdata.minkowskiMap (repOut (innerToOuter z)) = ((z.1 : Λ.subgroup) : ComplexSpace d) := by
      simpa [innerToOuter] using hrepOut_map (innerToOuter z)
    have hxu_mem : mdata.minkowskiMap (repOut (innerToOuter z) + u) ∈ Ωout := by
      dsimp [Ωin, Ωout, translateSet, unitDistancePolydisc] at hz_inner ⊢
      intro i
      have hu_norm : ‖mdata.embedding i u‖ = 1 := hU_allEmb u hu (mdata.embedding i)
      have hcoord :
          (mdata.minkowskiMap (repOut (innerToOuter z) + u) - t) i =
            ((((z.1 : Λ.subgroup) : ComplexSpace d) - t) i) + mdata.embedding i u := by
        calc
          (mdata.minkowskiMap (repOut (innerToOuter z) + u) - t) i
              = (mdata.minkowskiMap (repOut (innerToOuter z) + u)) i - t i := by
                  rfl
          _ = (mdata.minkowskiMap (repOut (innerToOuter z)) i + mdata.minkowskiMap u i) - t i := by
                simp
          _ = (((z.1 : Λ.subgroup) : ComplexSpace d) i + mdata.embedding i u) - t i := by
                rw [hz_rep]
                rfl
          _ = (((z.1 : Λ.subgroup) : ComplexSpace d) i - t i) + mdata.embedding i u := by
                abel
          _ = ((((z.1 : Λ.subgroup) : ComplexSpace d) - t) i) + mdata.embedding i u := by
                rfl
      calc
        ‖(mdata.minkowskiMap (repOut (innerToOuter z) + u) - t) i‖
            = ‖((((z.1 : Λ.subgroup) : ComplexSpace d) - t) i) + mdata.embedding i u‖ := by
                rw [hcoord]
        _ ≤ ‖(((z.1 : Λ.subgroup) : ComplexSpace d) - t) i‖ + ‖mdata.embedding i u‖ := by
              exact norm_add_le _ _
        _ = ‖(((z.1 : Λ.subgroup) : ComplexSpace d) - t) i‖ + 1 := by rw [hu_norm]
        _ ≤ (data.R - 1) + 1 := by
              gcongr
              simpa using (hz_inner i)
        _ = data.R := by ring
    have hxu_subgroup :
        mdata.minkowskiMap (repOut (innerToOuter z) + u) ∈ Λ.subgroup := by
      exact
        (hΛ (mdata.minkowskiMap (repOut (innerToOuter z) + u))).2
          ⟨repOut (innerToOuter z) + u, hxu_scaled, rfl⟩
    let zout : Pout :=
      ⟨⟨mdata.minkowskiMap (repOut (innerToOuter z) + u), hxu_subgroup⟩, hxu_mem⟩
    have hzout_eq : repOut zout = repOut (innerToOuter z) + u := by
      apply distance_minkowski_injective mdata
      simpa [zout] using hrepOut_map zout
    simpa [X, hzout_eq] using
      (Finset.mem_image.mpr ⟨zout, Finset.mem_univ _, rfl⟩ :
        repOut zout ∈ (Finset.univ : Finset Pout).image repOut)
  refine ⟨Y, X, ?_, ?_, hY_scaled', hX_scaled', hY_subset, hshift⟩
  · simpa [d] using hY_lower
  · simpa [d] using hX_upper

lemma container_elements_cm
    {T : SplitTotallyTower.{0}} (data : DistanceGrowthData T) (j : ℕ)
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
    (hcomplex :
      NumberField.InfinitePlace.nrComplexPlaces K = Module.finrank ℚ (T.fields j))
    (hroot : rootDiscriminant K ≤ data.ρ)
    (U : Finset K)
    (hU_allEmb : ∀ u ∈ U, ∀ σ : K →+* ℂ, ‖σ u‖ = 1)
    (hU_scaled : ∀ u ∈ U, ScaledRingIntegers K data.q u) :
    ∃ Y X : Finset K,
      data.CX ^ Module.finrank ℚ (T.fields j) ≤ (Y.card : ℝ) ∧
      ((X.card : ℝ) ≤ data.A ^ Module.finrank ℚ (T.fields j)) ∧
      (∀ x ∈ Y, x ∈ X) ∧
      (∀ x ∈ Y, ∀ u ∈ U, x + u ∈ X) := by
  rcases
      container_geometry_cm
        data j hcomplex hroot U hU_allEmb hU_scaled with
      ⟨Y, X, hY_lower, hX_upper, hY_scaled, hX_scaled, hY_subset, hshift⟩
  exact ⟨Y, X, hY_lower, hX_upper, hY_subset, hshift⟩

lemma distance_level_image
    {K : Type*} [Field K] [NumberField K]
    (σ : K →+* ℂ) {x u : K} (hu : ‖σ u‖ = 1) :
    IsUnitDistance (σ x) (σ (x + u)) := by
  rw [IsUnitDistance, dist_eq_norm]
  have hsub : σ x - σ (x + u) = -σ u := by
    simp [map_add, sub_eq_add_neg, add_comm]
  rw [hsub, norm_neg]
  exact hu

lemma project_container_plane
    {T : SplitTotallyTower.{0}} (data : DistanceGrowthData T) (j : ℕ)
    {K : Type*} [Field K] [NumberField K]
    (σ : K →+* ℂ)
    (U Y X : Finset K)
    (hU_lower : data.CU ^ Module.finrank ℚ (T.fields j) ≤ (U.card : ℝ))
    (hU_unit : ∀ u ∈ U, ‖σ u‖ = 1)
    (hY_lower : data.CX ^ Module.finrank ℚ (T.fields j) ≤ (Y.card : ℝ))
    (hX_upper : ((X.card : ℝ) ≤ data.A ^ Module.finrank ℚ (T.fields j)))
    (hY_subset : ∀ x ∈ Y, x ∈ X)
    (hshift : ∀ x ∈ Y, ∀ u ∈ U, x + u ∈ X) :
    ∃ Uj Yj Pj : Finset Point,
      data.CU ^ Module.finrank ℚ (T.fields j) ≤ (Uj.card : ℝ) ∧
      (∀ u ∈ Uj, IsUnitDistance 0 u) ∧
      data.CX ^ Module.finrank ℚ (T.fields j) ≤ (Yj.card : ℝ) ∧
      ((Pj.card : ℝ) ≤ data.A ^ Module.finrank ℚ (T.fields j)) ∧
      (∀ x ∈ Yj, x ∈ Pj) ∧
      (∀ x ∈ Yj, ∀ u ∈ Uj, x + u ∈ Pj ∧ IsUnitDistance x (x + u)) := by
  let Uj : Finset Point := U.image σ
  let Yj : Finset Point := Y.image σ
  let Pj : Finset Point := X.image σ
  have hσinj : Function.Injective σ := RingHom.injective σ
  have hUj_card : Uj.card = U.card := by
    simp [Uj, Finset.card_image_of_injective, hσinj]
  have hYj_card : Yj.card = Y.card := by
    simp [Yj, Finset.card_image_of_injective, hσinj]
  have hPj_card : Pj.card = X.card := by
    simp [Pj, Finset.card_image_of_injective, hσinj]
  refine ⟨Uj, Yj, Pj, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [hUj_card] using hU_lower
  · intro u hu
    rcases Finset.mem_image.mp hu with ⟨u0, hu0, rfl⟩
    simpa using
      (distance_level_image σ (x := 0) (u := u0) (hU_unit u0 hu0))
  · simpa [hYj_card] using hY_lower
  · simpa [hPj_card] using hX_upper
  · intro x hx
    rcases Finset.mem_image.mp hx with ⟨x0, hx0, rfl⟩
    exact Finset.mem_image.mpr ⟨x0, hY_subset x0 hx0, rfl⟩
  · intro x hx u hu
    rcases Finset.mem_image.mp hx with ⟨x0, hx0, rfl⟩
    rcases Finset.mem_image.mp hu with ⟨u0, hu0, rfl⟩
    have hmem : σ (x0 + u0) ∈ Pj := by
      exact Finset.mem_image.mpr ⟨x0 + u0, hshift x0 hx0 u0 hu0, rfl⟩
    have hdist : IsUnitDistance (σ x0) (σ (x0 + u0)) :=
      distance_level_image σ (x := x0) (u := u0) (hU_unit u0 hu0)
    exact ⟨by simpa [Pj, map_add] using hmem, by simpa [map_add] using hdist⟩

lemma container_sets_tower
    (T : SplitTotallyTower.{0}) (data : DistanceGrowthData T) (j : ℕ) :
    ∃ Uj Yj Pj : Finset Point,
      data.CU ^ Module.finrank ℚ (T.fields j) ≤ (Uj.card : ℝ) ∧
      (∀ u ∈ Uj, IsUnitDistance 0 u) ∧
      data.CX ^ Module.finrank ℚ (T.fields j) ≤ (Yj.card : ℝ) ∧
      ((Pj.card : ℝ) ≤ data.A ^ Module.finrank ℚ (T.fields j)) ∧
      (∀ x ∈ Yj, x ∈ Pj) ∧
      (∀ x ∈ Yj, ∀ u ∈ Uj, x + u ∈ Pj ∧ IsUnitDistance x (x + u)) := by
  rcases distance_cm_tower T j with
      ⟨K, hFieldK, hNumberFieldK, ι, ii, c, hii, hspan, hc_base, hc_ii, hc_embed,
        hsplit_bridge⟩
  letI := hFieldK
  letI := hNumberFieldK
  rcases cm_i_tower T j ι ii hii hspan with
      ⟨hTotallyComplexK, hcomplex⟩
  letI := hTotallyComplexK
  have hroot_two :
      rootDiscriminant K ≤ 2 * rootDiscriminant (T.fields j) :=
    cm_discriminant_tower T j ι ii hii hspan
  have hroot :
      rootDiscriminant K ≤ data.ρ :=
    le_trans hroot_two (data.hρ_cm j)
  rcases distance_complex_embedding K with ⟨σ⟩
  have hS_splitF :
      ∀ p ∈ data.S,
        Nat.Prime p ∧ p % 4 = 1 ∧
          splitsCompletely (T.fields j) p := by
    intro p hp
    rcases T.splitPrimes_spec (data.hS_split p hp) with ⟨hp_prime, hp_mod, hsplitF_all⟩
    exact ⟨hp_prime, hp_mod, hsplitF_all j⟩
  rcases
      distance_elements_cm
        data j ι ii c hii hspan hc_base hc_ii hc_embed hsplit_bridge hS_splitF with
      ⟨U, hU_lower_raw, hU_allEmb, hU_scaled⟩
  have hclass :
      (NumberField.classNumber K : ℝ) ≤ data.H ^ Module.finrank ℚ (T.fields j) :=
    distance_level_bound data j hcomplex hroot
  have hU_lower :
      data.CU ^ Module.finrank ℚ (T.fields j) ≤
        (((2 : ℝ) ^ data.S.card) ^ NumberField.InfinitePlace.nrComplexPlaces K) /
          (NumberField.classNumber K : ℝ) :=
    distance_level_cu data j hcomplex hclass
  have hU_lower' :
      data.CU ^ Module.finrank ℚ (T.fields j) ≤ (U.card : ℝ) :=
    le_trans hU_lower hU_lower_raw
  rcases
      container_elements_cm
        data j hcomplex hroot U hU_allEmb hU_scaled with
      ⟨Y, X, hY_lower, hX_upper, hY_subset, hshift⟩
  have hU_unit_sigma : ∀ u ∈ U, ‖σ u‖ = 1 := by
    intro u hu
    exact hU_allEmb u hu σ
  exact
    project_container_plane data j σ U Y X
      hU_lower' hU_unit_sigma hY_lower hX_upper hY_subset hshift

lemma distance_pairs_sym
    (P : Finset Point) :
    distancePairsCount P =
      ((P.offDiag.filter fun p => dist p.1 p.2 = 1).image (Function.uncurry Sym2.mk)).card := by
  let E : Finset (Point × Point) := P.offDiag.filter fun p => dist p.1 p.2 = 1
  have hfiber
      (a b : Point) (ha : (a, b) ∈ E) :
      {z ∈ E | Function.uncurry Sym2.mk z = Sym2.mk a b} =
        .cons (a, b) {(b, a)} (by
          intro h
          apply (Finset.mem_offDiag.mp (Finset.mem_filter.mp ha).1).2.2
          exact congrArg Prod.fst (Finset.mem_singleton.mp h)) := by
    have hba : (b, a) ∈ E := by
      rcases Finset.mem_filter.mp ha with ⟨hmem, hdist⟩
      rcases Finset.mem_offDiag.mp hmem with ⟨haP, hbP, hab⟩
      refine Finset.mem_filter.mpr ?_
      refine ⟨Finset.mem_offDiag.mpr ⟨hbP, haP, hab.symm⟩, ?_⟩
      simpa [dist_comm] using hdist
    ext z
    rcases z with ⟨x, y⟩
    simp only [Finset.mem_filter, Finset.mem_cons, Finset.mem_singleton]
    constructor
    · intro hz
      rcases hz with ⟨hzE, hzEq⟩
      have hxy : (x = a ∧ y = b) ∨ (x = b ∧ y = a) := by
        simpa [Function.uncurry, Sym2.eq_iff] using hzEq
      rcases hxy with hxy | hxy
      · left
        exact Prod.ext hxy.1 hxy.2
      · right
        exact Prod.ext hxy.1 hxy.2
    · intro hz
      have hz' : (x = a ∧ y = b) ∨ (x = b ∧ y = a) := by
        simpa [Prod.mk.injEq] using hz
      rcases hz' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨ha, rfl⟩
      · exact ⟨hba, by simp [Function.uncurry]⟩
  have htwo :
      2 * (E.image (Function.uncurry Sym2.mk)).card = E.card := by
    have hsum_two :
        2 * (E.image (Function.uncurry Sym2.mk)).card =
          Finset.sum (E.image (Function.uncurry Sym2.mk)) fun _ => 2 := by
      simp [Nat.mul_comm]
    have hsum_fibers :
        Finset.sum (E.image (Function.uncurry Sym2.mk)) (fun z =>
          ({p ∈ E | Function.uncurry Sym2.mk p = z}).card) = E.card := by
      simpa using
        (Finset.card_eq_sum_card_image (f := Function.uncurry Sym2.mk) (s := E)).symm
    calc
      2 * (E.image (Function.uncurry Sym2.mk)).card =
          Finset.sum (E.image (Function.uncurry Sym2.mk)) (fun _ => 2) := hsum_two
      _ = Finset.sum (E.image (Function.uncurry Sym2.mk)) (fun z =>
            ({p ∈ E | Function.uncurry Sym2.mk p = z}).card) := by
              apply Finset.sum_congr rfl
              intro z hz
              rcases Finset.mem_image.mp hz with ⟨p, hpE, hpz⟩
              rcases p with ⟨a, b⟩
              subst hpz
              have hab : a ≠ b := by
                exact (Finset.mem_offDiag.mp (Finset.mem_filter.mp hpE).1).2.2
              have hpair_ne : (a, b) ≠ (b, a) := by
                intro h
                exact hab (congrArg Prod.fst h)
              change 2 = ({p ∈ E | Function.uncurry Sym2.mk p = Sym2.mk a b}).card
              rw [hfiber a b hpE]
              simp [hpair_ne]
      _ = E.card := hsum_fibers
  simpa [distancePairsCount, E] using
    (Nat.div_eq_of_eq_mul_right Nat.zero_lt_two htwo.symm)

lemma distance_pairs_sets
    (Yj Uj Pj : Finset Point)
    (hY_subset : ∀ x ∈ Yj, x ∈ Pj)
    (hshift :
      ∀ x ∈ Yj, ∀ u ∈ Uj, x + u ∈ Pj ∧ IsUnitDistance x (x + u)) :
    (((Yj.card : ℝ) * Uj.card) / 2) ≤ (distancePairsCount Pj : ℝ) := by
  classical
  let D : Finset (Point × Point) := Yj.product Uj
  let g : Point × Point → Sym2 Point := fun xu => Sym2.mk xu.1 (xu.1 + xu.2)
  let E : Finset (Sym2 Point) :=
    (Pj.offDiag.filter fun p => dist p.1 p.2 = 1).image (Function.uncurry Sym2.mk)
  have hfiber_le_two :
      ∀ z ∈ D.image g, ({p ∈ D | g p = z}).card ≤ 2 := by
    intro z hz
    rcases Finset.mem_image.mp hz with ⟨p, hpD, rfl⟩
    rcases p with ⟨x, u⟩
    have hsubset :
        {p ∈ D | g p = g (x, u)} ⊆ ({(x, u), (x + u, -u)} : Finset (Point × Point)) := by
      intro q hq
      rcases q with ⟨x', u'⟩
      rcases Finset.mem_filter.mp hq with ⟨hqD, hEq⟩
      rcases Finset.mem_product.mp hqD with ⟨hx', hu'⟩
      have hEq' : Sym2.mk x' (x' + u') = Sym2.mk x (x + u) := hEq
      have hxy := Sym2.eq_iff.mp hEq'
      rcases hxy with hxy | hxy
      · have hu : u' = u := by
          simpa [hxy.1] using hxy.2
        have hpair : (x', u') = (x, u) := Prod.ext hxy.1 hu
        simp [hpair]
      · have hu : u' = -u := by
          have hsum : (x + u) + u' = x := by
            simpa [hxy.1, add_assoc] using hxy.2
          have hzero : u + u' = 0 := by
            apply add_left_cancel (a := x)
            simpa [add_assoc] using hsum
          have hzero' : u' + u = 0 := by
            simpa [add_comm] using hzero
          exact eq_neg_iff_add_eq_zero.mpr hzero'
        have hpair : (x', u') = (x + u, -u) := Prod.ext hxy.1 hu
        simp [hpair]
    have hpair_card : ({(x, u), (x + u, -u)} : Finset (Point × Point)).card ≤ 2 := by
      by_cases h : (x, u) = (x + u, -u)
      · simp [h]
      · simp [h]
    exact le_trans (Finset.card_le_card hsubset) hpair_card
  have hcard_le :
      D.card ≤ 2 * (D.image g).card := by
    have hsum_fibers :
        D.card = Finset.sum (D.image g) (fun z => ({p ∈ D | g p = z}).card) := by
      simpa using Finset.card_eq_sum_card_image (f := g) (s := D)
    rw [hsum_fibers]
    calc
      Finset.sum (D.image g) (fun z => ({p ∈ D | g p = z}).card)
          ≤ Finset.sum (D.image g) (fun _ => 2) := by
            exact Finset.sum_le_sum fun z hz => hfiber_le_two z hz
      _ = 2 * (D.image g).card := by
        simp [Nat.mul_comm]
  have himage_lower :
      (((Yj.card : ℝ) * Uj.card) / 2) ≤ ((D.image g).card : ℝ) := by
    have hcard_le' : Yj.card * Uj.card ≤ 2 * (D.image g).card := by
      simpa [D, Finset.card_product] using hcard_le
    have hreal : ((Yj.card : ℝ) * Uj.card) ≤ 2 * ((D.image g).card : ℝ) := by
      exact_mod_cast hcard_le'
    nlinarith
  have himage_subset : D.image g ⊆ E := by
    intro z hz
    rcases Finset.mem_image.mp hz with ⟨p, hpD, rfl⟩
    rcases Finset.mem_product.mp hpD with ⟨hxY, huU⟩
    have hxP : p.1 ∈ Pj := hY_subset p.1 hxY
    rcases hshift p.1 hxY p.2 huU with ⟨hxpP, hdist⟩
    refine Finset.mem_image.mpr ?_
    refine ⟨(p.1, p.1 + p.2), ?_, rfl⟩
    refine Finset.mem_filter.mpr ?_
    refine ⟨Finset.mem_offDiag.mpr ⟨hxP, hxpP, ?_⟩, ?_⟩
    · intro hEq
      rw [IsUnitDistance] at hdist
      have hp2_zero : p.2 = 0 := by
        apply add_left_cancel (a := p.1)
        simpa using hEq.symm
      have hzero : dist p.1 (p.1 + p.2) = 0 := by
        simp [hp2_zero]
      linarith
    · simpa [IsUnitDistance] using hdist
  have himage_le :
      ((D.image g).card : ℝ) ≤ (distancePairsCount Pj : ℝ) := by
    have hcard : (D.image g).card ≤ E.card := Finset.card_le_card himage_subset
    calc
      ((D.image g).card : ℝ) ≤ (E.card : ℝ) := by
        exact_mod_cast hcard
      _ = (distancePairsCount Pj : ℝ) := by
        simpa [E] using congrArg (fun n : ℕ => (n : ℝ))
          (distance_pairs_sym Pj).symm
  exact le_trans himage_lower himage_le

lemma distance_level_edge
    {T : SplitTotallyTower.{0}} (data : DistanceGrowthData T) (j : ℕ)
    (Yj Uj : Finset Point)
    (hY_lower : data.CX ^ Module.finrank ℚ (T.fields j) ≤ (Yj.card : ℝ))
    (hU_lower : data.CU ^ Module.finrank ℚ (T.fields j) ≤ (Uj.card : ℝ)) :
    data.B ^ Module.finrank ℚ (T.fields j) / 2 ≤ (((Yj.card : ℝ) * Uj.card) / 2) := by
  let d : ℕ := Module.finrank ℚ (T.fields j)
  have hCU_pos : 0 < data.CU := distance_cu_pos data
  have hCX_pos : 0 < data.CX := by
    linarith [data.hCX_gt]
  have hCU_nonneg : 0 ≤ data.CU := le_of_lt hCU_pos
  have hCX_nonneg : 0 ≤ data.CX := le_of_lt hCX_pos
  have hU_nonneg : 0 ≤ ((Uj.card : ℝ)) := by positivity
  have hCX_pow_nonneg : 0 ≤ data.CX ^ d := by
    exact pow_nonneg hCX_nonneg d
  have hmul :
      data.CU ^ d * data.CX ^ d ≤ ((Uj.card : ℝ) * (Yj.card : ℝ)) := by
    exact mul_le_mul hU_lower hY_lower hCX_pow_nonneg hU_nonneg
  have hBpow :
      data.B ^ d = data.CU ^ d * data.CX ^ d := by
    rw [data.hB_def, mul_pow]
  have hmain : data.B ^ d ≤ ((Yj.card : ℝ) * Uj.card) := by
    calc
      data.B ^ d = data.CU ^ d * data.CX ^ d := hBpow
      _ ≤ ((Uj.card : ℝ) * (Yj.card : ℝ)) := hmul
      _ = ((Yj.card : ℝ) * Uj.card) := by ring
  have hdiv :
      data.B ^ d / 2 ≤ ((Yj.card : ℝ) * Uj.card) / 2 := by
    exact div_le_div_of_nonneg_right hmain (by norm_num)
  simpa [d] using hdiv

lemma level_point_tower
    (T : SplitTotallyTower.{0}) (data : DistanceGrowthData T) (j : ℕ) :
    ∃ Pj : Finset Point,
      data.CX ^ Module.finrank ℚ (T.fields j) ≤ (Pj.card : ℝ) ∧
      (Pj.card : ℝ) ≤ data.A ^ Module.finrank ℚ (T.fields j) ∧
      data.B ^ Module.finrank ℚ (T.fields j) / 2 ≤
        (distancePairsCount Pj : ℝ) := by
  rcases container_sets_tower T data j with
      ⟨Uj, Yj, Pj, hU_lower, hU_unit, hY_lower, hP_upper, hY_subset, hshift⟩
  refine ⟨Pj, ?_, hP_upper, ?_⟩
  · refine le_trans hY_lower ?_
    exact_mod_cast Finset.card_le_card hY_subset
  · have hEdgesFromSets :
        (((Yj.card : ℝ) * Uj.card) / 2) ≤ (distancePairsCount Pj : ℝ) :=
      distance_pairs_sets Yj Uj Pj hY_subset hshift
    have hEdgesFromBounds :
        data.B ^ Module.finrank ℚ (T.fields j) / 2 ≤ (((Yj.card : ℝ) * Uj.card) / 2) :=
      distance_level_edge data j Yj Uj hY_lower hU_lower
    exact le_trans hEdgesFromBounds hEdgesFromSets

lemma point_sets_tower
    (T : SplitTotallyTower.{0}) :
    ∃ data : DistanceGrowthData T,
      ∀ j : ℕ,
        ∃ Pj : Finset Point,
          data.CX ^ Module.finrank ℚ (T.fields j) ≤ (Pj.card : ℝ) ∧
          (Pj.card : ℝ) ≤ data.A ^ Module.finrank ℚ (T.fields j) ∧
          data.B ^ Module.finrank ℚ (T.fields j) / 2 ≤
            (distancePairsCount Pj : ℝ) := by
  rcases distance_scalar_tower T with ⟨data⟩
  refine ⟨data, ?_⟩
  intro j
  exact level_point_tower T data j

lemma distance_point_tower
    (T : SplitTotallyTower.{0}) :
    ∃ CX A B : ℝ,
      Nonempty
        (DistancePointData
          (fun j => Module.finrank ℚ (T.fields j)) CX A B) ∧
      1 < CX ∧
      1 < A ∧
      A < B := by
  rcases point_sets_tower T with ⟨data, hP⟩
  refine ⟨data.CX, data.A, data.B, ?_, data.hCX_gt, data.hA_gt, data.hBA⟩
  classical
  refine ⟨{
    P := fun j => Classical.choose (hP j)
    lower := ?_
    upper := ?_
    edges := ?_
  }⟩
  · intro j
    exact (Classical.choose_spec (hP j)).1
  · intro j
    exact (Classical.choose_spec (hP j)).2.1
  · intro j
    exact (Classical.choose_spec (hP j)).2.2

lemma distance_point_data :
    ∃ T : SplitTotallyTower.{0}, ∃ CX A B : ℝ,
      Nonempty
        (DistancePointData
          (fun j => Module.finrank ℚ (T.fields j)) CX A B) ∧
      1 < CX ∧
      1 < A ∧
      A < B := by
  rcases input_totally_tower with ⟨T⟩
  rcases distance_point_tower T with
      ⟨CX, A, B, pointData, hCX, hA, hBA⟩
  exact ⟨T, CX, A, B, pointData, hCX, hA, hBA⟩

lemma distance_construction_tower
    (T : SplitTotallyTower.{0}) :
    Nonempty (DistanceTowerConstruction T) := by
  rcases distance_point_tower T with
      ⟨CX, A, B, hPointData, hCX, hA, hBA⟩
  rcases hPointData with ⟨pointData⟩
  refine ⟨{
    d := fun j => Module.finrank ℚ (T.fields j)
    CX := CX
    A := A
    B := B
    hd := rfl
    hCX_gt := hCX
    hA_gt := hA
    hBA := hBA
    pointData := pointData
  }⟩

lemma distance_construction_data :
    ∃ T : SplitTotallyTower.{0}, Nonempty (DistanceTowerConstruction T) := by
  rcases input_totally_tower with ⟨T⟩
  rcases distance_construction_tower T with ⟨C⟩
  exact ⟨T, ⟨C⟩⟩

lemma distance_construct_point
    (d : ℕ → ℕ) (CX A B : ℝ)
    (data : DistancePointData d CX A B) :
    ∀ j : ℕ,
      ∃ Pj : Finset Point,
        CX ^ d j ≤ (Pj.card : ℝ) ∧
        (Pj.card : ℝ) ≤ A ^ d j ∧
        B ^ d j / 2 ≤ (distancePairsCount Pj : ℝ) := by
  intro j
  exact ⟨data.P j, data.lower j, data.upper j, data.edges j⟩

lemma distance_point_tendsto
    (d : ℕ → ℕ) (P : ℕ → Finset Point) (CX : ℝ)
    (hCX : 1 < CX) (hd_tendsto : Tendsto d atTop atTop)
    (hP_lower : ∀ j : ℕ, CX ^ d j ≤ ((P j).card : ℝ)) :
    Tendsto (fun j ↦ (P j).card) atTop atTop := by
  have hpow_tendsto : Tendsto (fun j ↦ CX ^ d j) atTop atTop :=
    (tendsto_pow_atTop_atTop_of_one_lt hCX).comp hd_tendsto
  refine Filter.tendsto_atTop.mpr ?_
  intro n
  have hpow_eventually : ∀ᶠ j : ℕ in atTop, (n : ℝ) ≤ CX ^ d j :=
    (Filter.tendsto_atTop.mp hpow_tendsto) n
  filter_upwards [hpow_eventually] with j hj
  have hcard_real : (n : ℝ) ≤ ((P j).card : ℝ) := le_trans hj (hP_lower j)
  exact_mod_cast hcard_real

lemma unit_distance_gamma
    (A B : ℝ) (hA : 1 < A) (hBA : A < B) :
    1 < Real.log B / Real.log A := by
  have hA0 : 0 < A := by linarith
  have hB0 : 0 < B := by linarith
  have hlogA : 0 < Real.log A := Real.log_pos hA
  have hlogAB : Real.log A < Real.log B :=
    Real.strictMonoOn_log hA0 hB0 hBA
  rw [one_lt_div hlogA]
  exact hlogAB

lemma unit_distance_control
    (d : ℕ → ℕ) (P : ℕ → Finset Point) (A B γ : ℝ)
    (hγ_def : γ = Real.log B / Real.log A)
    (hA : 1 < A) (hBA : A < B)
    (hP_upper : ∀ j : ℕ, ((P j).card : ℝ) ≤ A ^ d j) :
    ∀ j : ℕ, Real.rpow ((P j).card : ℝ) γ ≤ B ^ d j := by
  intro j
  have hA0 : 0 < A := by
    linarith
  have hB0 : 0 < B := by
    linarith
  have hA_nonneg : 0 ≤ A := le_of_lt hA0
  have hγ_nonneg : 0 ≤ γ := by
    have hγ_gt : 1 < γ := by
      rw [hγ_def]
      exact unit_distance_gamma A B hA hBA
    linarith
  have hstep : Real.rpow ((P j).card : ℝ) γ ≤ Real.rpow (A ^ d j) γ := by
    apply Real.rpow_le_rpow
    · positivity
    · exact hP_upper j
    · exact hγ_nonneg
  have hlogA : 0 < Real.log A := Real.log_pos hA
  have hbase : A ^ γ = B := by
    rw [hγ_def, Real.rpow_def_of_pos hA0]
    have hlogA_ne : Real.log A ≠ 0 := by
      linarith
    field_simp [hlogA_ne]
    rw [Real.exp_log hB0]
  have hpow_eq : Real.rpow (A ^ d j) γ = B ^ d j := by
    calc
      Real.rpow (A ^ d j) γ = Real.rpow (A ^ (d j : ℝ)) γ := by
        rw [show (A ^ d j : ℝ) = A ^ (d j : ℝ) by
          symm
          exact Real.rpow_natCast A (d j)]
      _ = A ^ ((d j : ℝ) * γ) := by
        symm
        exact Real.rpow_mul hA_nonneg (d j : ℝ) γ
      _ = A ^ (γ * (d j : ℝ)) := by
        rw [mul_comm]
      _ = (A ^ γ) ^ (d j : ℝ) := by
        rw [Real.rpow_mul hA_nonneg γ (d j : ℝ)]
      _ = B ^ d j := by
        rw [hbase, Real.rpow_natCast]
  exact le_trans hstep (le_of_eq hpow_eq)

/--
The main theorem: assuming the black-box tower input, there is a family of
planar point sets of unbounded size determining at least `c N^(1 + ε)` unit
distances.
-/
theorem main_theorem :
    ∃ ε > 0, ∃ c > 0, ∃ P : ℕ → Finset Point,
      Tendsto (fun j ↦ (P j).card) atTop atTop ∧
        ∀ j,
          c * Real.rpow ((P j).card : ℝ) (1 + ε) ≤
            (distancePairsCount (P j) : ℝ) := by
  classical
  rcases distance_construction_data with ⟨T, hC⟩
  rcases hC with ⟨C⟩
  let d : ℕ → ℕ := C.d
  let CX : ℝ := C.CX
  let A : ℝ := C.A
  let B : ℝ := C.B
  let pointData : DistancePointData d CX A B := C.pointData
  have hP :
      ∀ j : ℕ,
        ∃ Pj : Finset Point,
          CX ^ d j ≤ (Pj.card : ℝ) ∧
          (Pj.card : ℝ) ≤ A ^ d j ∧
          B ^ d j / 2 ≤ (distancePairsCount Pj : ℝ) :=
    distance_construct_point d CX A B pointData
  choose P hP_spec using hP
  have hP_lower :
      ∀ j : ℕ, CX ^ d j ≤ ((P j).card : ℝ) := by
    intro j
    exact (hP_spec j).1
  have hP_upper :
      ∀ j : ℕ, ((P j).card : ℝ) ≤ A ^ d j := by
    intro j
    exact (hP_spec j).2.1
  have hP_edges :
      ∀ j : ℕ, B ^ d j / 2 ≤ (distancePairsCount (P j) : ℝ) := by
    intro j
    exact (hP_spec j).2.2
  have hP_tendsto : Tendsto (fun j ↦ (P j).card) atTop atTop := by
    have hd_tendsto : Tendsto d atTop atTop := by
      simpa [d, C.hd] using T.degree_tendsto_top
    exact distance_point_tendsto d P CX C.hCX_gt hd_tendsto hP_lower
  let γ : ℝ := Real.log B / Real.log A
  have hγ : 1 < γ := by
    exact unit_distance_gamma A B C.hA_gt C.hBA
  let ε : ℝ := γ - 1
  have hε : 0 < ε := by
    dsimp [ε]
    linarith
  let c : ℝ := 1 / 2
  have hc : 0 < c := by
    norm_num [c]
  have hPowerControl :
      ∀ j : ℕ, Real.rpow ((P j).card : ℝ) γ ≤ B ^ d j := by
    exact unit_distance_control d P A B γ rfl C.hA_gt C.hBA hP_upper
  refine ⟨ε, hε, c, hc, P, hP_tendsto, ?_⟩
  intro j
  have hEdge :
      c * B ^ d j ≤ (distancePairsCount (P j) : ℝ) := by
    simpa [c, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hP_edges j
  have hPow :
      c * Real.rpow ((P j).card : ℝ) γ ≤ c * B ^ d j := by
    exact mul_le_mul_of_nonneg_left (hPowerControl j) (le_of_lt hc)
  have hExp : 1 + ε = γ := by
    dsimp [ε]
    linarith
  calc
    c * Real.rpow ((P j).card : ℝ) (1 + ε)
        = c * Real.rpow ((P j).card : ℝ) γ := by rw [hExp]
    _ ≤ c * B ^ d j := hPow
    _ ≤ (distancePairsCount (P j) : ℝ) := hEdge

/--
The set of all possible numbers of unit distances for a configuration of `n` points.
-/
def unitDistanceCounts (n : ℕ) : Set ℕ :=
  {m | ∃ points : Finset Point, points.card = n ∧ distancePairsCount points = m}

/--
This lemma confirms that the set of possible unit distance counts is bounded above, which
ensures that taking the supremum (`sSup`) is a well-defined operation.

The bound used here is the easy polynomial estimate `n^2`.
-/
theorem counts_bdd_above (n : ℕ) : BddAbove (unitDistanceCounts n) := by
  refine ⟨n * n, ?_⟩
  rintro m ⟨points, hcard, rfl⟩
  unfold distancePairsCount
  calc
    (Finset.card
          (Finset.filter
            (fun p : Point × Point => dist p.1 p.2 = 1)
            points.offDiag)) / 2
        ≤ Finset.card
            (Finset.filter
              (fun p : Point × Point => dist p.1 p.2 = 1)
              points.offDiag) :=
      Nat.div_le_self _ _
    _ ≤ points.offDiag.card := Finset.card_filter_le _ _
    _ = points.card * points.card - points.card := Finset.offDiag_card points
    _ ≤ points.card * points.card := Nat.sub_le _ _
    _ = n * n := by simp [hcard]

/--
The **maximum number of unit distances** determined by any set of `n` points in the plane.
This function is often denoted by `u(n)` in combinatorics.
-/
def maxUnitDistances (n : ℕ) : ℕ :=
  sSup (unitDistanceCounts n)

/--
Does every set of `n` distinct points in `ℝ²` contain at most
`n^(1 + O(1 / log log n))` many pairs which are distance `1` apart?
-/
theorem not_erdos_90 :
    ¬ ∃ O : ℕ → ℝ,
      O =O[atTop] (fun n => 1 / Real.log (Real.log (n : ℝ))) ∧
        ∀ᶠ n : ℕ in atTop,
          (maxUnitDistances n : ℝ) ≤ Real.rpow (n : ℝ) (1 + O n) := by
  intro h
  rcases h with ⟨O, hO, hUpper⟩
  obtain ⟨ε, hε, c, hc, P, hP, hLower⟩ :=
    main_theorem
  have hLogLog : Tendsto (fun n : ℕ => Real.log (Real.log (n : ℝ))) atTop atTop := by
    exact Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have hBaseZero : Tendsto (fun n : ℕ => 1 / Real.log (Real.log (n : ℝ))) atTop (𝓝 0) := by
    simpa [one_div] using (tendsto_inv_atTop_zero.comp hLogLog)
  have hOZero : Tendsto O atTop (𝓝 0) :=
    hO.trans_tendsto hBaseZero
  have hOSmallNat : ∀ᶠ n : ℕ in atTop, O n < ε / 2 := by
    exact hOZero.eventually_lt tendsto_const_nhds (by nlinarith)
  have hPReal : Tendsto (fun j : ℕ => ((P j).card : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hP
  have hPow : Tendsto (fun j : ℕ => ((P j).card : ℝ) ^ (ε / 2 : ℝ)) atTop atTop := by
    exact (tendsto_rpow_atTop (by nlinarith)).comp hPReal
  have hUpperP : ∀ᶠ j : ℕ in atTop,
      (maxUnitDistances ((P j).card) : ℝ) ≤ (((P j).card : ℝ) ^ (1 + O ((P j).card))) := by
    exact hP.eventually hUpper
  have hOSmallP : ∀ᶠ j : ℕ in atTop, O ((P j).card) < ε / 2 := by
    exact hP.eventually hOSmallNat
  have hCardLarge : ∀ᶠ j : ℕ in atTop, (2 : ℝ) ≤ (P j).card := by
    exact hPReal.eventually_ge_atTop 2
  have hPowLarge : ∀ᶠ j : ℕ in atTop, 1 / c + 1 ≤ ((P j).card : ℝ) ^ (ε / 2 : ℝ) := by
    exact hPow.eventually_ge_atTop (1 / c + 1)
  have hFalse : ∀ᶠ j : ℕ in atTop, False := by
    filter_upwards [hUpperP, hOSmallP, hCardLarge, hPowLarge] with j hUpperj hOj hCardj hPowj
    let N : ℝ := (P j).card
    have hNpos : 0 < N := by
      dsimp [N]
      linarith
    have hNone : 1 ≤ N := by
      dsimp [N]
      linarith
    have hMem : distancePairsCount (P j) ∈ unitDistanceCounts (P j).card := by
      exact ⟨P j, rfl, rfl⟩
    have hSupNat : distancePairsCount (P j) ≤ maxUnitDistances (P j).card := by
      unfold maxUnitDistances
      exact le_csSup (counts_bdd_above _) hMem
    have hSup : (distancePairsCount (P j) : ℝ) ≤ (maxUnitDistances (P j).card : ℝ) := by
      exact_mod_cast hSupNat
    have hMain : c * N ^ (1 + ε) ≤ N ^ (1 + O ((P j).card)) := by
      simpa [N] using le_trans (hLower j) (le_trans hSup hUpperj)
    have hExp : 1 + O ((P j).card) ≤ 1 + ε / 2 := by
      linarith
    have hMain' : c * N ^ (1 + ε) ≤ N ^ (1 + ε / 2) := by
      exact hMain.trans <| Real.rpow_le_rpow_of_exponent_le hNone hExp
    have hcinv : c * (1 / c) = 1 := by
      field_simp [hc.ne']
    have hFactorLe : 1 + c ≤ c * N ^ (ε / 2) := by
      have hmul := mul_le_mul_of_nonneg_left hPowj (le_of_lt hc)
      dsimp [N] at hmul ⊢
      rw [mul_add, hcinv] at hmul
      simpa [mul_assoc, mul_left_comm, mul_comm] using hmul
    have hFactorGt : 1 < c * N ^ (ε / 2) := by
      linarith
    have hStrict : N ^ (1 + ε / 2) < c * N ^ (1 + ε) := by
      have hmul := mul_lt_mul_of_pos_right hFactorGt (Real.rpow_pos_of_pos hNpos (1 + ε / 2))
      have hsplit : N ^ (ε / 2) * N ^ (1 + ε / 2) = N ^ (1 + ε) := by
        have hs : ε / 2 + (1 + ε / 2) = 1 + ε := by ring
        rw [← Real.rpow_add hNpos, hs]
      calc
        N ^ (1 + ε / 2) < c * (N ^ (ε / 2) * N ^ (1 + ε / 2)) := by
          simpa [one_mul, mul_assoc, mul_left_comm, mul_comm] using hmul
        _ = c * N ^ (1 + ε) := by rw [hsplit]
    exact (not_lt_of_ge hMain') hStrict
  rcases Filter.Eventually.exists hFalse with ⟨j, hj⟩
  exact hj

end Submission
