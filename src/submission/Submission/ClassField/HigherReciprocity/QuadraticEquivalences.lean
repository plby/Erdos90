import Submission.ClassField.QuadraticForms.QuadraticHilbert
import Mathlib.Tactic.LinearCombination

/-!
# Chapter VIII, Example 5.6: quadratic-form and norm equivalences

This file proves the elementary equivalences in Example VIII.5.6 that do
not refer to the Brauer invariant: isotropy of the four-variable quaternion
norm form, a point on the associated conic, and representability by the
quadratic norm form.
-/

namespace Submission.CField.HRecip.QFEquiva

open Submission.CField.HSymbol

variable {K : Type*} [Field K]

/-- The reduced norm form of the quaternion algebra `H(a,b)` represents
zero nontrivially. -/
def NontrivialQuaternionZero (a b : K) : Prop :=
  ∃ x y z t : K,
    (x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0 ∨ t ≠ 0) ∧
      x ^ 2 - a * y ^ 2 - b * z ^ 2 + a * b * t ^ 2 = 0

/-- The four-variable norm form of `H(a,b)` is isotropic exactly when its
three-variable conic has a nontrivial point.  This is the second-to-fourth
condition in Example VIII.5.6, written without any local-field hypotheses
because the argument is purely algebraic. -/
theorem quaternion_norm_conic (a b : K) :
    NontrivialQuaternionZero a b ↔
      NontrivialQuadraticConic a b := by
  constructor
  · rintro ⟨x, y, z, t, hne, heq⟩
    let d : K := z ^ 2 - a * t ^ 2
    have hxy : x ^ 2 - a * y ^ 2 = b * d := by
      dsimp [d]
      linear_combination heq
    by_cases hd : d = 0
    · by_cases hzt : z = 0 ∧ t = 0
      · refine ⟨y, 0, x, ?_, ?_⟩
        · rcases hne with hx | hy | hz | ht
          · exact Or.inr (Or.inr hx)
          · exact Or.inl hy
          · exact (hz hzt.1).elim
          · exact (ht hzt.2).elim
        · have hxy0 : x ^ 2 - a * y ^ 2 = 0 := by simpa [hd] using hxy
          linear_combination hxy0
      · refine ⟨t, 0, z, ?_, ?_⟩
        · rcases not_and_or.mp hzt with hz | ht
          · exact Or.inr (Or.inr hz)
          · exact Or.inl ht
        · have hd' : z ^ 2 - a * t ^ 2 = 0 := by simpa [d] using hd
          linear_combination hd'
    · refine ⟨y * z - x * t, d, x * z - a * y * t, ?_, ?_⟩
      · exact Or.inr (Or.inl hd)
      · calc
          (x * z - a * y * t) ^ 2 =
              a * (y * z - x * t) ^ 2 +
                (x ^ 2 - a * y ^ 2) * d := by ring
          _ = a * (y * z - x * t) ^ 2 + b * d ^ 2 := by rw [hxy]; ring
  · rintro ⟨y, z, x, hne, heq⟩
    refine ⟨x, y, z, 0, ?_, ?_⟩
    · rcases hne with hy | hz | hx
      · exact Or.inr (Or.inl hy)
      · exact Or.inr (Or.inr (Or.inl hz))
      · exact Or.inl hx
    · linear_combination heq

/-- Over a field of residue characteristic different from two, and for
nonzero `a`, the quadratic norm equation is equivalent to the conic
condition even when `a` is a square.  This removes the nonsquare hypothesis
needed by the earlier generic lemma; Example VIII.5.6 has exactly these
hypotheses because `K_v = ℚ_p`, `p` is odd, and `a ∈ K_vˣ`. -/
theorem quadratic_conic_ne
    {a b : K} (ha0 : a ≠ 0) (htwo : (2 : K) ≠ 0) :
    QuadraticValue a b ↔
      NontrivialQuadraticConic a b := by
  by_cases ha : IsSquare a
  · constructor
    · rintro ⟨w, v, rfl⟩
      refine ⟨v, 1, w, Or.inr (Or.inl one_ne_zero), ?_⟩
      ring
    · intro _
      obtain ⟨s, rfl⟩ := ha
      have hs0 : s ≠ 0 := by
        intro hs
        apply ha0
        simp [hs]
      refine ⟨(b + 1) / 2, (1 - b) / (2 * s), ?_⟩
      field_simp [htwo, hs0]
      ring
  · exact nontrivial_conic_solution ha

/-- The three elementary conditions in Example VIII.5.6 are equivalent for
nonzero `a` in odd residue characteristic. -/
theorem sign_quaternion_value
    {a b : K} (ha0 : a ≠ 0) (htwo : (2 : K) ≠ 0) :
    (Submission.CField.QForms.quadraticHilbertSign a b = 1 ↔
      NontrivialQuaternionZero a b) ∧
    (Submission.CField.QForms.quadraticHilbertSign a b = 1 ↔
      QuadraticValue a b) := by
  rw [Submission.CField.QForms.hilbert_sign_one]
  exact ⟨(quaternion_norm_conic a b).symm,
    (quadratic_conic_ne ha0 htwo).symm⟩

end Submission.CField.HRecip.QFEquiva
