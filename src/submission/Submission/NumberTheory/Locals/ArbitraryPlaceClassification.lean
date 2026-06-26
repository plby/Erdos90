import Submission.NumberTheory.Locals.ArchimedeanPlaceClassification
import Submission.NumberTheory.Locals.NonarchimedeanClassification


/-!
# Classification of arbitrary absolute values on number fields

This file combines the archimedean and nonarchimedean halves of Milne's
Theorem 7.14.  It also proves uniqueness: equivalent normalized finite
places have the same centered prime, while a finite place cannot be
equivalent to an infinite place.
-/

namespace Submission.NumberTheory.Milne

open IsDedekindDomain NumberField

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

/-- Two normalized finite places are equal exactly when their underlying
absolute values are equivalent. -/
theorem finite_place_equiv (p q : FinitePlace K) :
    p = q ↔ p.1.IsEquiv q.1 := by
  refine ⟨fun hpq => hpq ▸ .rfl, fun hpq => ?_⟩
  apply FinitePlace.maximalIdeal_injective
  apply HeightOneSpectrum.ext
  ext x
  rw [← FinitePlace.norm_lt_one_iff_mem (K := K) p.maximalIdeal x,
    ← FinitePlace.norm_lt_one_iff_mem (K := K) q.maximalIdeal x,
    FinitePlace.norm_embedding_eq, FinitePlace.norm_embedding_eq]
  exact hpq.lt_one_iff

/-- Every normalized finite place is nonarchimedean. -/
theorem place_nonarchimedean (p : FinitePlace K) :
    IsNonarchimedean p.1 := by
  rw [nonarchimedean_nat_cast]
  intro n
  change p (n : K) ≤ 1
  rw [← FinitePlace.norm_embedding_eq p, FinitePlace.norm_embedding]
  exact IsNonarchimedean.apply_natCast_le_one
    (HeightOneSpectrum.isNonarchimedean_adicAbv K p.maximalIdeal)

/-- Every finite place is represented by a nontrivial absolute value. -/
theorem finite_place_nontrivial (p : FinitePlace K) :
    p.1.IsNontrivial := by
  obtain ⟨x, hx, hx0⟩ :=
    Submodule.exists_mem_ne_zero_of_ne_bot p.maximalIdeal.ne_bot
  let xK : K := algebraMap (𝓞 K) K x
  have hxK : xK ≠ 0 := by
    exact (FaithfulSMul.algebraMap_eq_zero_iff (𝓞 K) K).not.2 hx0
  have hlt : p.1 xK < 1 := by
    change p xK < 1
    rw [← FinitePlace.norm_embedding_eq p]
    exact (FinitePlace.norm_lt_one_iff_mem (K := K) p.maximalIdeal x).2 hx
  exact ⟨xK, hxK, ne_of_lt hlt⟩

omit [NumberField K] in
/-- No normalized infinite place is nonarchimedean. -/
theorem infinite_place_nonarchimedean (p : InfinitePlace K) :
    ¬ IsNonarchimedean p.1 := by
  intro hp
  have htwo := (nonarchimedean_nat_cast p.1).1 hp 2
  change p (2 : K) ≤ 1 at htwo
  have hp2 : p (2 : K) = (2 : ℝ) := by
    change p ((2 : ℕ) : K) = ((2 : ℕ) : ℝ)
    exact InfinitePlace.map_natCast p 2
  rw [hp2] at htwo
  norm_num at htwo

omit [NumberField K] in
/-- Being nonarchimedean depends only on the equivalence class of an
absolute value. -/
theorem nonarchimedean_equiv
    {v w : AbsoluteValue K ℝ} (h : v.IsEquiv w) :
    IsNonarchimedean v ↔ IsNonarchimedean w := by
  rw [nonarchimedean_nat_cast,
    nonarchimedean_nat_cast]
  exact forall_congr' fun _ => h.le_one_iff

/-- The normalized absolute value represented by either a finite or an
infinite place. -/
def placeAbsoluteValue : FinitePlace K ⊕ InfinitePlace K → AbsoluteValue K ℝ
  | .inl p => p.1
  | .inr p => p.1

/-- Milne, Theorem 7.14: every nontrivial absolute value on a number field
is equivalent to a unique normalized finite or infinite place. -/
theorem unique_place_equiv
    (w : AbsoluteValue K ℝ) (hw : w.IsNontrivial) :
    ∃! p : FinitePlace K ⊕ InfinitePlace K,
      w.IsEquiv (placeAbsoluteValue p) := by
  have hex : ∃ p : FinitePlace K ⊕ InfinitePlace K,
      w.IsEquiv (placeAbsoluteValue p) := by
    by_cases hna : IsNonarchimedean w
    · obtain ⟨p, hp⟩ :=
        finite_place_nonarchimedean w hw hna
      exact ⟨.inl p, hp⟩
    · obtain ⟨p, hp⟩ :=
        infinite_not_nonarchimedean w hw hna
      exact ⟨.inr p, hp⟩
  obtain ⟨p, hp⟩ := hex
  refine ⟨p, hp, ?_⟩
  intro q hq
  cases p with
  | inl p =>
      cases q with
      | inl q =>
          congr 1
          exact (finite_place_equiv q p).2 (hq.symm.trans hp)
      | inr q =>
          exfalso
          apply infinite_place_nonarchimedean q
          exact (nonarchimedean_equiv (hp.symm.trans hq)).1
            (place_nonarchimedean p)
  | inr p =>
      cases q with
      | inl q =>
          exfalso
          apply infinite_place_nonarchimedean p
          exact (nonarchimedean_equiv (hq.symm.trans hp)).1
            (place_nonarchimedean q)
      | inr q =>
          congr 1
          exact (InfinitePlace.eq_iff_isEquiv (K := K)).2 (hq.symm.trans hp)

end

end Submission.NumberTheory.Milne
