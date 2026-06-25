import Mathlib.RingTheory.PowerSeries.Substitution

namespace Submission.CField.FGroups

open scoped BigOperators PowerSeries

open PowerSeries

variable {R : Type*} [CommRing R]

private lemma finsum_add_ite {A : ℕ → R} (hA : A.HasFiniteSupport) (a : ℕ) :
    finsum A = A a + finsum (fun d ↦ if d = a then 0 else A d) := by
  let F : ℕ → R := fun d ↦ if d = a then A d else 0
  have hF : F.HasFiniteSupport := by
    rw [Function.HasFiniteSupport]
    refine Set.Finite.subset (Set.finite_singleton a) ?_
    intro d hd
    simp only [Function.mem_support] at hd
    simpa only [Set.mem_singleton_iff] using not_imp_not.mp (fun h ↦ by simp [F, h]) hd
  have hsub : (A - F).HasFiniteSupport := hA.sub hF
  calc
    finsum A = finsum (fun d ↦ F d + (A - F) d) := by
      apply finsum_congr
      intro d
      simp [F]
    _ = finsum F + finsum (A - F) := finsum_add_distrib hF hsub
    _ = A a + finsum (fun d ↦ if d = a then 0 else A d) := by
      congr 1
      · rw [finsum_eq_single F a]
        · simp [F]
        · intro d hd
          simp [F, hd]
      · apply finsum_congr
        intro d
        by_cases hd : d = a <;> simp [F, hd]

private noncomputable def inverseCoeff (f : R⟦X⟧) (u : Rˣ) : ℕ → R :=
  Nat.strongRec fun n previous ↦
    if _hn : n = 0 then 0 else
      (↑u⁻¹ : R) *
        (coeff n (X : R⟦X⟧) -
          finsum fun d ↦
            if d = 1 then 0 else
              coeff d f * coeff n
                ((PowerSeries.mk fun k ↦ if hk : k < n then previous k hk else 0) ^ d))

private lemma inverseCoeff_eq (f : R⟦X⟧) (u : Rˣ) (n : ℕ) :
    inverseCoeff f u n =
      if _hn : n = 0 then 0 else
        (↑u⁻¹ : R) *
          (coeff n (X : R⟦X⟧) -
            finsum fun d ↦
              if d = 1 then 0 else
                coeff d f * coeff n
                  ((PowerSeries.mk fun k ↦ if k < n then inverseCoeff f u k else 0) ^ d)) := by
  rw [inverseCoeff, Nat.strongRec_eq]
  rfl

/-- The recursively constructed candidate for the substitution inverse. -/
noncomputable def compositionalInverse (f : R⟦X⟧) (u : Rˣ) : R⟦X⟧ :=
  PowerSeries.mk (inverseCoeff f u)

@[simp]
theorem coeff_compositionalInverse (f : R⟦X⟧) (u : Rˣ) (n : ℕ) :
    coeff n (compositionalInverse f u) = inverseCoeff f u n := by
  simp [compositionalInverse]

@[simp]
theorem constant_compositional_inverse (f : R⟦X⟧) (u : Rˣ) :
    constantCoeff (compositionalInverse f u) = 0 := by
  rw [← coeff_zero_eq_constantCoeff, coeff_compositionalInverse, inverseCoeff_eq]
  simp

private lemma coeff_mul_zero
    {p q : R⟦X⟧} {n : ℕ} (hp : ∀ k < n, coeff k p = 0)
    (hq : q.constantCoeff = 0) : coeff n (p * q) = 0 := by
  rw [coeff_mul]
  refine Finset.sum_eq_zero fun ij hij ↦ ?_
  have hij' : ij.1 + ij.2 = n := Finset.mem_antidiagonal.mp hij
  by_cases hj : ij.2 = 0
  · simp [hj, coeff_zero_eq_constantCoeff, hq]
  · have hi : ij.1 < n := by omega
    rw [hp ij.1 hi, zero_mul]

private lemma constant_coeff_geom₂_eq_zero {g h : R⟦X⟧}
    (hg : g.constantCoeff = 0) (hh : h.constantCoeff = 0)
    {d : ℕ} (hd : d ≠ 1) :
    constantCoeff (∑ i ∈ Finset.range d, g ^ i * h ^ (d - 1 - i)) = 0 := by
  cases d with
  | zero => simp
  | succ d =>
      have hd0 : d ≠ 0 := by
        intro hd'
        apply hd
        simp [hd']
      rw [map_sum]
      refine Finset.sum_eq_zero fun i hi ↦ ?_
      rw [map_mul, map_pow, map_pow, hg, hh]
      by_cases hi0 : i = 0
      · subst i
        simp [hd0]
      · simp [hi0]

private lemma eq_eq_lt {g h : R⟦X⟧} {n d : ℕ}
    (hg : g.constantCoeff = 0) (hh : h.constantCoeff = 0)
    (hcoeff : ∀ k < n, coeff k g = coeff k h) (hd : d ≠ 1) :
    coeff n (g ^ d) = coeff n (h ^ d) := by
  let s : R⟦X⟧ := ∑ i ∈ Finset.range d, g ^ i * h ^ (d - 1 - i)
  have hs : s.constantCoeff = 0 := constant_coeff_geom₂_eq_zero hg hh hd
  have hp : ∀ k < n, coeff k (g - h) = 0 := by
    intro k hk
    rw [map_sub, hcoeff k hk, sub_self]
  have hz : coeff n ((g - h) * s) = 0 :=
    coeff_mul_zero hp hs
  rw [mul_comm, geom_sum₂_mul] at hz
  exact sub_eq_zero.mp (by simpa only [map_sub] using hz)

/-- The recursive series is a left substitution inverse when `u` represents
the linear coefficient of `f`. -/
theorem subst_compositionalInverse {f : R⟦X⟧} (u : Rˣ)
    (hf : f.constantCoeff = 0) (hu : (↑u : R) = coeff 1 f) :
    f.subst (compositionalInverse f u) = X := by
  apply PowerSeries.ext
  intro n
  by_cases hn : n = 0
  · subst n
    rw [coeff_zero_eq_constantCoeff]
    simpa using
      (constantCoeff_subst_eq_zero (constant_compositional_inverse f u) f hf)
  · let g : R⟦X⟧ := compositionalInverse f u
    let q : R⟦X⟧ := PowerSeries.mk fun k ↦ if k < n then inverseCoeff f u k else 0
    let A : ℕ → R := fun d ↦ coeff d f * coeff n (g ^ d)
    have hg : g.constantCoeff = 0 := constant_compositional_inverse f u
    have hq : q.constantCoeff = 0 := by
      rw [← coeff_zero_eq_constantCoeff]
      rw [show coeff 0 q = (if 0 < n then inverseCoeff f u 0 else 0) by simp [q]]
      rw [if_pos (Nat.pos_of_ne_zero hn), inverseCoeff_eq]
      simp
    have hA : A.HasFiniteSupport := by
      simpa only [A, smul_eq_mul] using
        coeff_subst_finite' (HasSubst.of_constantCoeff_zero' hg) f n
    have hother :
        finsum (fun d ↦ if d = 1 then 0 else A d) =
          finsum (fun d ↦ if d = 1 then 0 else coeff d f * coeff n (q ^ d)) := by
      apply finsum_congr
      intro d
      split_ifs with hd
      · rfl
      · simp only [A]
        rw [eq_eq_lt hg hq]
        · intro k hk
          simp [g, q, compositionalInverse, hk]
        · exact hd
    rw [coeff_subst' (HasSubst.of_constantCoeff_zero' hg)]
    simp only [smul_eq_mul]
    change finsum A = coeff n (X : R⟦X⟧)
    rw [finsum_add_ite hA 1, hother]
    simp only [A, pow_one]
    rw [coeff_compositionalInverse, inverseCoeff_eq, dif_neg hn, ← hu]
    change (↑u : R) *
        ((↑u⁻¹ : R) *
          (coeff n (X : R⟦X⟧) -
            finsum (fun d ↦ if d = 1 then 0 else coeff d f * coeff n (q ^ d)))) +
        finsum (fun d ↦ if d = 1 then 0 else coeff d f * coeff n (q ^ d)) =
      coeff n (X : R⟦X⟧)
    rw [← mul_assoc]
    simp

/-- If the linear coefficient of `f` is a unit, substitution on the right by
series with zero constant coefficient is left-cancellative.  This is the
coefficientwise uniqueness argument in Lemma 2.1(b). -/
theorem subst_injective_coeff {f g h : R⟦X⟧}
    (hf1 : IsUnit (coeff 1 f))
    (hg : g.constantCoeff = 0) (hh : h.constantCoeff = 0)
    (heq : f.subst g = f.subst h) : g = h := by
  apply PowerSeries.ext
  intro n
  induction n using Nat.strongRec with
  | ind n ih =>
      cases n with
      | zero => rw [coeff_zero_eq_constantCoeff, hg, hh]
      | succ n =>
          let A : ℕ → R := fun d ↦ coeff d f * coeff (n + 1) (g ^ d)
          let B : ℕ → R := fun d ↦ coeff d f * coeff (n + 1) (h ^ d)
          have hA : A.HasFiniteSupport := by
            simpa only [A, smul_eq_mul] using
              coeff_subst_finite' (HasSubst.of_constantCoeff_zero' hg) f (n + 1)
          have hB : B.HasFiniteSupport := by
            simpa only [B, smul_eq_mul] using
              coeff_subst_finite' (HasSubst.of_constantCoeff_zero' hh) f (n + 1)
          have hsum : finsum (fun d ↦ A d - B d) = 0 := by
            rw [finsum_sub_distrib hA hB]
            have hc := congrArg (coeff (R := R) (n + 1)) heq
            rw [coeff_subst' (HasSubst.of_constantCoeff_zero' hg),
              coeff_subst' (HasSubst.of_constantCoeff_zero' hh)] at hc
            have hc' : finsum A = finsum B := by
              simpa only [A, B, smul_eq_mul] using hc
            rw [hc', sub_self]
          have hother : ∀ d, d ≠ 1 → A d - B d = 0 := by
            intro d hd
            simp only [A, B]
            rw [eq_eq_lt hg hh (fun k hk ↦ ih k (by omega)) hd,
              sub_self]
          have hone : A 1 - B 1 = 0 := by
            rw [finsum_eq_single (fun d ↦ A d - B d) 1 hother] at hsum
            exact hsum
          simp only [A, B, pow_one] at hone
          apply sub_eq_zero.mp
          apply hf1.mul_left_cancel
          simpa [mul_sub] using hone

/-- The linear coefficient of a composite of power series with zero inner
constant coefficient is the product of the linear coefficients. -/
theorem coeff_one_subst {f g : R⟦X⟧} (hg : g.constantCoeff = 0) :
    coeff 1 (f.subst g) = coeff 1 f * coeff 1 g := by
  rw [coeff_subst' (HasSubst.of_constantCoeff_zero' hg)]
  rw [finsum_eq_single (fun d ↦ coeff d f • coeff 1 (g ^ d)) 1]
  · simp
  · intro d hd
    rw [coeff_one_pow]
    cases d with
    | zero => simp
    | succ d =>
        have hd0 : d ≠ 0 := by
          intro hd'
          apply hd
          simp [hd']
        simp [hg, hd0]

/-- The necessary direction of Lemma 2.1(b): a left substitution inverse
forces the linear coefficient to be a unit. -/
theorem unit_subst_x {f g : R⟦X⟧}
    (hg : g.constantCoeff = 0) (hfg : f.subst g = X) :
    IsUnit (coeff 1 f) := by
  rw [isUnit_iff_exists_inv]
  refine ⟨coeff 1 g, ?_⟩
  rw [← coeff_one_subst hg, hfg, coeff_one_X]

/-- Any left substitution inverse furnished by Lemma 2.1(b) is automa
a right inverse.  This is Milne's associativity-and-cancellation argument. -/
theorem subst_x {f g : R⟦X⟧}
    (hf : f.constantCoeff = 0) (hg : g.constantCoeff = 0)
    (hfg : f.subst g = X) : g.subst f = X := by
  have hf1 : IsUnit (coeff 1 f) := unit_subst_x hg hfg
  have hgf0 : (g.subst f).constantCoeff = 0 :=
    constantCoeff_subst_eq_zero hf g hg
  apply subst_injective_coeff hf1 hgf0 constantCoeff_X
  rw [← subst_comp_subst_apply (HasSubst.of_constantCoeff_zero' hg)
    (HasSubst.of_constantCoeff_zero' hf), hfg]
  rw [subst_X (HasSubst.of_constantCoeff_zero' hf)]
  simp

/-- A left substitution inverse is unique. -/
theorem subst_inverse_unique {f g h : R⟦X⟧}
    (hg : g.constantCoeff = 0) (hh : h.constantCoeff = 0)
    (hfg : f.subst g = X) (hfh : f.subst h = X) : g = h := by
  exact subst_injective_coeff
    (unit_subst_x hg hfg) hg hh (hfg.trans hfh.symm)

/-- Existence of a substitution inverse is equivalent to invertibility of the
linear coefficient.  This is the existence assertion of Lemma 2.1(b). -/
theorem subst_x_coeff {f : R⟦X⟧}
    (hf : f.constantCoeff = 0) :
    (∃ g : R⟦X⟧, g.constantCoeff = 0 ∧ f.subst g = X) ↔
      IsUnit (coeff 1 f) := by
  constructor
  · rintro ⟨g, hg, hfg⟩
    exact unit_subst_x hg hfg
  · rintro ⟨u, hu⟩
    refine ⟨compositionalInverse f u, constant_compositional_inverse f u, ?_⟩
    exact subst_compositionalInverse u hf hu

/-- The existence assertion in Lemma 2.1(b), separated from its consequences.
Once a left inverse exists, it is unique and two-sided by the preceding
theorems. -/
theorem compositionalInverse_spec {f : R⟦X⟧} (hf : f.constantCoeff = 0)
    (hex : ∃ g : R⟦X⟧, g.constantCoeff = 0 ∧ f.subst g = X) :
    ∃! g : R⟦X⟧, g.constantCoeff = 0 ∧ f.subst g = X ∧ g.subst f = X := by
  obtain ⟨g, hg, hfg⟩ := hex
  refine ⟨g, ⟨hg, hfg, subst_x hf hg hfg⟩, ?_⟩
  intro h hh'
  exact (subst_inverse_unique (g := g) (h := h) hg hh'.1 hfg hh'.2.1).symm

/-- Milne, Lemma 2.1(b), in full: a zero-constant power series has a
substitution inverse exactly when its linear coefficient is a unit.  In that
case the inverse is unique and is simultaneously a left and right inverse. -/
theorem unique_sided_compositional {f : R⟦X⟧}
    (hf : f.constantCoeff = 0) :
    (∃! g : R⟦X⟧,
      g.constantCoeff = 0 ∧ f.subst g = X ∧ g.subst f = X) ↔
      IsUnit (coeff 1 f) := by
  constructor
  · rintro ⟨g, hg, _⟩
    exact unit_subst_x hg.1 hg.2.1
  · intro hf1
    apply compositionalInverse_spec hf
    exact (subst_x_coeff hf).2 hf1

end Submission.CField.FGroups
