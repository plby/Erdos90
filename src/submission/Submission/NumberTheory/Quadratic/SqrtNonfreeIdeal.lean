import Submission.NumberTheory.Quadratic.SqrtFiveIdeals

/-!
# Milne, Algebraic Number Theory, Remark 2.31(c)

The ideal `(2, 1 + sqrt(-5))` lies strictly between `(2)` and `Z[sqrt(-5)]`.  It is not
principal, and in fact it is not free as a module over `Z[sqrt(-5)]`.
-/

namespace Submission.NumberTheory.SNFive

open Ideal

private instance : NoZeroDivisors SNFive where
  eq_zero_or_eq_zero_of_mul_eq_zero {a b} hab := by
    have hnorm : a.norm * b.norm = 0 := by
      rw [← Zsqrtd.norm_mul, hab, Zsqrtd.norm_zero]
    rcases mul_eq_zero.mp hnorm with ha | hb
    · exact Or.inl ((Zsqrtd.norm_eq_zero_iff (by norm_num) a).mp ha)
    · exact Or.inr ((Zsqrtd.norm_eq_zero_iff (by norm_num) b).mp hb)

private instance : IsDomain SNFive := NoZeroDivisors.to_isDomain _

private lemma norm_ne_two (x : SNFive) : x.norm ≠ 2 := by
  intro h
  have him_lower : -1 < x.im := by
    rw [Zsqrtd.norm_def] at h
    nlinarith [sq_nonneg x.re, sq_nonneg (x.im + 1)]
  have him_upper : x.im < 1 := by
    rw [Zsqrtd.norm_def] at h
    nlinarith [sq_nonneg x.re, sq_nonneg (x.im - 1)]
  have him : x.im = 0 := by omega
  rw [Zsqrtd.norm_def, him] at h
  have hsquare : IsSquare (2 : Int) := by
    refine ⟨x.re, ?_⟩
    simpa [pow_two] using h.symm
  norm_num at hsquare

/-- The ideal `(2, 1 + sqrt(-5))` is not principal. -/
theorem prime_not_principal : ¬ primeIdealTwo.IsPrincipal := by
  intro hprincipal
  obtain ⟨x, hx⟩ := hprincipal.principal
  have hxIdeal : primeIdealTwo = Ideal.span {x} := by
    ext y
    change y ∈ (primeIdealTwo : Submodule SNFive SNFive) ↔
      y ∈ Submodule.span SNFive {x}
    rw [hx]
  have hsquare : span ({x ^ 2} : Set SNFive) = span {(2 : SNFive)} := by
    rw [show span ({x ^ 2} : Set SNFive) = span {x} ^ 2 by
      simp [pow_two, Ideal.span_singleton_mul_span_singleton]]
    rw [← hxIdeal, prime_ideal_sq]
  have hassociated : Associated (x ^ 2) (2 : SNFive) :=
    Ideal.span_singleton_eq_span_singleton.mp hsquare
  have hnorm : (x ^ 2).norm = (2 : SNFive).norm :=
    Zsqrtd.norm_eq_of_associated (by norm_num : (-5 : Int) ≤ 0) hassociated
  rw [pow_two, Zsqrtd.norm_mul] at hnorm
  norm_num [Zsqrtd.norm_def] at hnorm
  have hxnorm_nonneg : 0 ≤ x.norm := Zsqrtd.norm_nonneg (by norm_num) x
  have : x.norm = 2 := by
    rw [Zsqrtd.norm_def]
    rw [Zsqrtd.norm_def] at hxnorm_nonneg
    nlinarith
  exact norm_ne_two x this

/-- The ideal `(2, 1 + sqrt(-5))` is not a free module over `Z[sqrt(-5)]`. -/
theorem prime_not_free : ¬ Module.Free SNFive primeIdealTwo := by
  intro hfree
  letI : Module.Free SNFive primeIdealTwo := hfree
  letI : Module.Finite SNFive primeIdealTwo := Module.Finite.of_fg <| by
    rw [prime_span_pair]
    exact Submodule.fg_span (by simp)
  have hne : primeIdealTwo ≠ ⊥ := by
    intro hbot
    have hmem : (2 : SNFive) ∈ primeIdealTwo := by
      rw [prime_span_pair]
      exact Ideal.subset_span (by simp)
    rw [hbot] at hmem
    simp at hmem
  have hfinrank : Module.finrank SNFive primeIdealTwo = 1 := by
    have hcard := Ideal.rank_eq (Module.Basis.singleton (Fin 1) SNFive) hne
      (Module.finBasis SNFive primeIdealTwo)
    simpa using hcard
  let e : SNFive ≃ₗ[SNFive] primeIdealTwo :=
    (Module.nonempty_linearEquiv_of_finrank_eq_one hfinrank).some
  apply prime_not_principal
  refine ⟨(e 1 : SNFive), ?_⟩
  ext y
  constructor
  · intro hy
    rw [Submodule.mem_span_singleton]
    obtain ⟨r, hr⟩ := e.surjective (⟨y, hy⟩ : primeIdealTwo)
    refine ⟨r, ?_⟩
    have her : e r = r • e 1 := by
      simpa using e.map_smul r (1 : SNFive)
    have hcoe := congrArg (fun z : primeIdealTwo => (z : SNFive)) (hr.symm.trans her)
    simpa [mul_comm] using hcoe.symm
  · intro hy
    refine (Submodule.span_le.mpr ?_) hy
    rintro z rfl
    exact (e 1).prop

end Submission.NumberTheory.SNFive
