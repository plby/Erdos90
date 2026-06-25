import ChallengeDeps
import Towers.Geometry.Counterexamples.UnitDistance

open LeanEval.Combinatorics

namespace Submission

private noncomputable def complexToPlane : ℂ ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2) :=
  Complex.orthonormalBasisOneI.repr

private lemma map_offDiag (P : Finset ℂ) :
    (P.map complexToPlane.toEquiv.toEmbedding).offDiag =
      P.offDiag.map
        (complexToPlane.toEquiv.toEmbedding.prodMap complexToPlane.toEquiv.toEmbedding) := by
  classical
  ext q
  constructor
  · intro hq
    rcases Finset.mem_offDiag.mp hq with ⟨hq₁, hq₂, hqne⟩
    rcases Finset.mem_map.mp hq₁ with ⟨a, ha, ha_eq⟩
    rcases Finset.mem_map.mp hq₂ with ⟨b, hb, hb_eq⟩
    apply Finset.mem_map.mpr
    refine ⟨(a, b), Finset.mem_offDiag.mpr ⟨ha, hb, ?_⟩, ?_⟩
    · intro hab
      apply hqne
      rw [← ha_eq, ← hb_eq]
      exact congrArg complexToPlane (by simpa using hab)
    · change (complexToPlane a, complexToPlane b) = q
      exact Prod.ext ha_eq hb_eq
  · intro hq
    rcases Finset.mem_map.mp hq with ⟨⟨a, b⟩, hab, hab_eq⟩
    rcases Finset.mem_offDiag.mp hab with ⟨ha, hb, habne⟩
    apply Finset.mem_offDiag.mpr
    have h₁ : complexToPlane a = q.1 := congrArg Prod.fst hab_eq
    have h₂ : complexToPlane b = q.2 := congrArg Prod.snd hab_eq
    refine ⟨Finset.mem_map.mpr ⟨a, ha, h₁⟩, Finset.mem_map.mpr ⟨b, hb, h₂⟩, ?_⟩
    intro hqeq
    apply habne
    exact complexToPlane.injective (h₁.trans (hqeq.trans h₂.symm))

private lemma unitDist_map (P : Finset ℂ) :
    unitDist (P.map complexToPlane.toEquiv.toEmbedding) =
      Towers.distancePairsCount P := by
  classical
  unfold unitDist Towers.distancePairsCount
  rw [map_offDiag, Finset.filter_map, Finset.card_map]
  congr 2
  ext q
  simp [complexToPlane]

open Filter

theorem erdos_conjecture_false :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ N : ℕ, ∃ (n : ℕ) (P : Finset (EuclideanSpace ℝ (Fin 2))),
        N ≤ n ∧ P.card = n ∧ (n : ℝ) ^ (1 + δ) ≤ (unitDist P : ℝ) := by
  classical
  obtain ⟨ε, hε, c, hc, P, hP, hLower⟩ :=
    Towers.main_theorem
  let δ : ℝ := ε / 2
  have hδ : 0 < δ := by
    dsimp [δ]
    positivity
  refine ⟨δ, hδ, ?_⟩
  have hPReal : Tendsto (fun j : ℕ => ((P j).card : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hP
  have hPow : Tendsto (fun j : ℕ => ((P j).card : ℝ) ^ δ) atTop atTop :=
    (tendsto_rpow_atTop hδ).comp hPReal
  intro N
  have hCardN : ∀ᶠ j : ℕ in atTop, N ≤ (P j).card :=
    hP.eventually (eventually_ge_atTop N)
  have hCardPos : ∀ᶠ j : ℕ in atTop, 1 ≤ (P j).card :=
    hP.eventually (eventually_ge_atTop 1)
  have hPowLarge : ∀ᶠ j : ℕ in atTop, 1 / c ≤ ((P j).card : ℝ) ^ δ :=
    hPow.eventually_ge_atTop (1 / c)
  obtain ⟨j, hNj, hjpos, hjpow⟩ :=
    Filter.Eventually.exists (hCardN.and (hCardPos.and hPowLarge))
  let Q : Finset (EuclideanSpace ℝ (Fin 2)) :=
    (P j).map complexToPlane.toEquiv.toEmbedding
  refine ⟨(P j).card, Q, hNj, ?_, ?_⟩
  · simp [Q]
  · have hbase : 0 < ((P j).card : ℝ) := by
      exact_mod_cast (show 0 < (P j).card by omega)
    have hcinv : c * (1 / c) = 1 := by
      field_simp [hc.ne']
    have hfactor : 1 ≤ c * ((P j).card : ℝ) ^ δ := by
      rw [← hcinv]
      exact mul_le_mul_of_nonneg_left hjpow (le_of_lt hc)
    have hsplit :
        ((P j).card : ℝ) ^ δ * ((P j).card : ℝ) ^ (1 + δ) =
          ((P j).card : ℝ) ^ (1 + ε) := by
      rw [← Real.rpow_add hbase]
      congr 1
      dsimp [δ]
      ring
    have hAbsorb :
        ((P j).card : ℝ) ^ (1 + δ) ≤
          c * ((P j).card : ℝ) ^ (1 + ε) := by
      calc
        ((P j).card : ℝ) ^ (1 + δ) =
            1 * ((P j).card : ℝ) ^ (1 + δ) := by rw [one_mul]
        _ ≤ (c * ((P j).card : ℝ) ^ δ) * ((P j).card : ℝ) ^ (1 + δ) :=
          mul_le_mul_of_nonneg_right hfactor (Real.rpow_nonneg hbase.le _)
        _ = c * ((P j).card : ℝ) ^ (1 + ε) := by rw [mul_assoc, hsplit]
    rw [unitDist_map]
    exact hAbsorb.trans (hLower j)

#print axioms erdos_conjecture_false

end Submission
