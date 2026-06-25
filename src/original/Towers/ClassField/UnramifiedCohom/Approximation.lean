import Mathlib.Topology.Algebra.Group.Basic

/-!
# Milne, Class Field Theory, Proposition III.1.2: successive approximation

This file isolates the algebraic induction in Milne's proof of surjectivity of
the norm on units.  An initial lift modulo the first filtration subgroup and
the ability to correct an error by one further layer produce a norm
approximation modulo every layer.
-/

namespace Towers.CField.UCohom

universe u v

variable {L : Type u} {K : Type v} [CommGroup L] [CommGroup K]

/-- **Proposition III.1.2, successive-approximation core.** Suppose every
element of `K` is a norm modulo `U 1`, and every error in `U (n+1)` can be
corrected by a norm modulo `U (n+2)`. Then every element is a norm modulo
`U (n+1)` for every finite `n`.

For local units, the first hypothesis comes from the residue-field norm and
the second from the residue-field trace through Lemma III.1.3. -/
theorem approximation_through_filtration
    (N : L →* K) (U : ℕ → Subgroup K)
    (h₀ : ∀ u : K, ∃ v : L, u / N v ∈ U 1)
    (hstep : ∀ (n : ℕ) (e : K), e ∈ U (n + 1) →
      ∃ w : L, e / N w ∈ U (n + 2))
    (u : K) (n : ℕ) : ∃ v : L, u / N v ∈ U (n + 1) := by
  induction n with
  | zero => simpa using h₀ u
  | succ n ih =>
      obtain ⟨v, hv⟩ := ih
      obtain ⟨w, hw⟩ := hstep n (u / N v) hv
      refine ⟨v * w, ?_⟩
      simpa [map_mul, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hw

end Towers.CField.UCohom
