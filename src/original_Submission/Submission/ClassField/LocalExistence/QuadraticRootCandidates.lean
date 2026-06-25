import Submission.ClassField.LocalExistence.HilbertRootCandidates

/-!
# The quadratic specialization of norm-core divisibility

This file connects the concrete conic/norm API in Section III.4 to the
candidate-root compactness argument in Section III.5.  It isolates exactly
the remaining local quadratic nondegeneracy and norm-core lifting inputs.
-/

namespace Submission.CField.LExist

open Submission.CField.LFTheory
open Submission.CField.HSymbol

noncomputable section

universe u

variable (K : Type u) [NontriviallyNormedField K]
  [IsUltrametricDist K] [ValuativeRel K] [IsNonarchimedeanLocalField K]
  [Valuation.Compatible (NormedField.valuation (K := K))]

omit [IsUltrametricDist K] [ValuativeRel K]
  [IsNonarchimedeanLocalField K]
  [Valuation.Compatible (NormedField.valuation (K := K))] in
/-- A universal quadratic-norm preimage of `a` gives a square norm preimage,
using the concrete conic form of Proposition III.4.1. -/
theorem nth_preimage_lift
    (a : Kˣ) (L : FASubext K)
    (right_nondegenerate : ∀ y : L.1,
      (∀ x, NontrivialQuadraticConic x y) → IsSquare y)
    (hlift : ∃ y : L.1ˣ,
      normOnUnits K L.1 y = a ∧
        ∀ x : L.1, QuadraticValue x (y : L.1)) :
    NthNormPreimage K 2 a L := by
  obtain ⟨y, hyNorm, hyUniversal⟩ := hlift
  have hySquare : IsSquare (y : L.1) :=
    square_forall_nondegenerate
      (right_nondegenerate (y : L.1)) hyUniversal
  obtain ⟨c, hc⟩ := hySquare
  have hc0 : c ≠ 0 := by
    intro hc0
    apply y.ne_zero
    rw [hc, hc0, zero_mul]
  refine ⟨y, hyNorm, ⟨Units.mk0 c hc0, ?_⟩⟩
  apply Units.ext
  change c ^ 2 = (y : L.1)
  rw [pow_two, ← hc]

omit [IsUltrametricDist K] [ValuativeRel K]
  [IsNonarchimedeanLocalField K]
  [Valuation.Compatible (NormedField.valuation (K := K))] in
/-- The concrete quadratic Hilbert input makes the candidate square-root set
`E(L)` nonempty. -/
theorem candidates_nonempty_lift
    (a : Kˣ) (L : FASubext K)
    (right_nondegenerate : ∀ y : L.1,
      (∀ x, NontrivialQuadraticConic x y) → IsSquare y)
    (hlift : ∃ y : L.1ˣ,
      normOnUnits K L.1 y = a ∧
        ∀ x : L.1, QuadraticValue x (y : L.1)) :
    (localRootCandidates K 2 a L).Nonempty := by
  apply candidates_nth_preimage K 2 a L
  exact nth_preimage_lift K a L
    right_nondegenerate hlift

/-- Quadratic nondegeneracy and Step III.5.2 norm-core lifting imply that
every element of the base norm core has a square root in that core. -/
theorem core_square_lifts
    (hNorm : LocalNormCorrespondence K)
    (right_nondegenerate : ∀ (L : FASubext K) (y : L.1),
      (∀ x, NontrivialQuadraticConic x y) → IsSquare y)
    (hlift : ∀ a ∈ localNormCore K,
      ∀ L : FASubext K,
        ∃ y : L.1ˣ, normOnUnits K L.1 y = a ∧
          ∀ x : L.1, QuadraticValue x (y : L.1))
    (a : Kˣ) (ha : a ∈ localNormCore K) :
    ∃ b ∈ localNormCore K, b ^ 2 = a := by
  letI : Nonempty (FASubext K) :=
    ⟨canonicalUnramifiedSubextension K 1⟩
  obtain ⟨b, hb, hpow⟩ := common_directed_nonempty
    (localRootCandidates K 2 a) 2 a
    (local_candidates_directed K hNorm 2 a)
    (fun L ↦ candidates_nonempty_lift
      K a L (right_nondegenerate L) (hlift a ha L))
    (local_root_candidates K 2 (by decide) a)
    (fun _ _ hb ↦ hb.1)
  refine ⟨b, ?_, hpow⟩
  rw [localNormCore, familyCore, Subgroup.mem_iInf]
  intro L
  exact (Set.mem_iInter.mp hb L).2

end

end Submission.CField.LExist
