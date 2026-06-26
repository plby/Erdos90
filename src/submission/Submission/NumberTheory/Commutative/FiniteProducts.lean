import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Ideal.Prod

/-!
# Milne, Algebraic Number Theory, Proposition 1.1 and Remark 1.2

This file records the classification of ideals and prime ideals in binary and finite products
of rings.
-/

namespace Submission.NumberTheory.Milne

universe u v

variable {A B : Type*} [CommSemiring A] [CommSemiring B]

/-- **Milne, Proposition 1.1.** Every ideal of a binary product is the
product of its two coordinate ideals.  The coordinate ideals are given
explicitly by the images under the two projections. -/
theorem binary_ideal_coordinate (I : Ideal (A × B)) :
    I = Ideal.prod
      (Ideal.map (RingHom.fst A B) I)
      (Ideal.map (RingHom.snd A B) I) :=
  Ideal.ideal_prod_eq I

/-- **Milne, Proposition 1.1.** The prime ideals of `A × B` are exactly
`p × B` for prime `p` in `A`, and `A × q` for prime `q` in `B`. -/
theorem binary_ideal_prime (I : Ideal (A × B)) :
    I.IsPrime ↔
      (∃ p : Ideal A, p.IsPrime ∧ I = Ideal.prod p ⊤) ∨
        ∃ q : Ideal B, q.IsPrime ∧ I = Ideal.prod ⊤ q :=
  Ideal.ideal_prod_prime I

variable {ι : Type u} {R : ι → Type v} [∀ i, CommSemiring (R i)]

/-- Every ideal in a finite product of rings is the product of its coordinate ideals.

This is the first assertion of Milne's Remark 1.2. Mathlib packages the result as an order
isomorphism, `Ideal.piOrderIso`.
-/
theorem ideal_pi [Finite ι] (I : Ideal (∀ i, R i)) :
    ∃ J : ∀ i, Ideal (R i), I = Ideal.pi J := by
  exact ⟨Ideal.piOrderIso I, (Ideal.piOrderIso.symm_apply_apply I).symm⟩

/-- A coordinatewise ideal in a product is prime precisely when one coordinate is prime and
all the other coordinate ideals are the whole ring.

Together with `ideal_pi`, this is the prime-ideal classification in Milne's
Remark 1.2. The equivalence itself does not require finiteness; finiteness is needed only to
know that every ideal of the product is coordinatewise.
-/
theorem ideal_pi_prime (J : ∀ i, Ideal (R i)) :
    (Ideal.pi J).IsPrime ↔
      ∃ j, (J j).IsPrime ∧ ∀ i, i ≠ j → J i = ⊤ := by
  classical
  constructor
  · intro hJ
    have h_exists : ∃ j, J j ≠ ⊤ := by
      by_contra h
      push Not at h
      have htop : Ideal.pi J = ⊤ := by
        ext x
        simp [Ideal.mem_pi, h]
      exact hJ.ne_top htop
    obtain ⟨j, hj⟩ := h_exists
    refine ⟨j, ?_, ?_⟩
    · refine ⟨hj, ?_⟩
      intro a b hab
      have hab' : Pi.single j a * Pi.single j b ∈ Ideal.pi J := by
        rw [← Pi.single_mul]
        exact Ideal.single_mem_pi hab
      rcases hJ.mem_or_mem hab' with ha | hb
      · left
        simpa using (Ideal.mem_pi _ _).mp ha j
      · right
        simpa using (Ideal.mem_pi _ _).mp hb j
    · intro i hij
      apply (Ideal.eq_top_iff_one (J i)).mpr
      have hzero : Pi.single j 1 * Pi.single i 1 ∈ Ideal.pi J := by
        have hmul : Pi.single j 1 * Pi.single i 1 = (0 : ∀ i, R i) := by
          ext k
          by_cases hkj : k = j
          · subst k
            simp [hij]
          · simp [hkj]
        rw [hmul]
        exact (Ideal.pi J).zero_mem
      have hj_not_mem : Pi.single j 1 ∉ Ideal.pi J := by
        intro hmem
        apply hj
        apply (Ideal.eq_top_iff_one (J j)).mpr
        simpa using (Ideal.mem_pi _ _).mp hmem j
      have hi_mem := (hJ.mem_or_mem hzero).resolve_left hj_not_mem
      simpa using (Ideal.mem_pi _ _).mp hi_mem i
  · rintro ⟨j, hj, htop⟩
    refine ⟨?_, ?_⟩
    · intro h
      apply hj.ne_top
      apply (Ideal.eq_top_iff_one (J j)).mpr
      have : (1 : ∀ i, R i) ∈ Ideal.pi J := by rw [h]; simp
      exact (Ideal.mem_pi _ _).mp this j
    · intro a b hab
      have habj : a j * b j ∈ J j := (Ideal.mem_pi _ _).mp hab j
      rcases hj.mem_or_mem habj with ha | hb
      · left
        apply (Ideal.mem_pi _ _).mpr
        intro i
        by_cases hi : i = j
        · subst i
          exact ha
        · rw [htop i hi]
          simp
      · right
        apply (Ideal.mem_pi _ _).mpr
        intro i
        by_cases hi : i = j
        · subst i
          exact hb
        · rw [htop i hi]
          simp

end Submission.NumberTheory.Milne
