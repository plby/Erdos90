import Towers.ClassField.Shifting.SolvableNegOne
import Towers.ClassField.Shifting.TateZeroTransfer

/-!
# Milne, Class Field Theory, Theorem II.3.10

This file assembles the arbitrary finite-group case in every Tate range
represented by the project: positive cohomology, degrees zero and minus one,
and positive homology (the Tate degrees below minus one).
-/

namespace Towers.CField.Shifting

open CategoryTheory CategoryTheory.Limits Rep

noncomputable section

universe u

/-- For an arbitrary finite group, the kernel of Milne's induced cover again
satisfies the `H¹/H²` hypothesis after every injective restriction. -/
theorem cover_h_12
    {k G : Type u} [CommRing k] [Group G] [Finite G]
    (A : Rep.{u} k G)
    (h12 : ∀ {K : Type u} [Group K] [Finite K] (f : K →* G),
      Function.Injective f →
        IsZero (groupCohomology (Rep.res f A) 1) ∧
        IsZero (groupCohomology (Rep.res f A) 2)) :
    ∀ {K : Type u} [Group K] [Finite K] (f : K →* G),
      Function.Injective f →
        IsZero (groupCohomology
          (Rep.res f (coverSequence A).X₁) 1) ∧
        IsZero (groupCohomology
          (Rep.res f (coverSequence A).X₁) 2) := by
  intro K _ _ f hf
  letI : Fintype K := Fintype.ofFinite K
  have h12K : ∀ {L : Type u} [Group L] [Finite L] (g : L →* K),
      Function.Injective g →
        IsZero (groupCohomology (Rep.res g (Rep.res f A)) 1) ∧
        IsZero (groupCohomology (Rep.res g (Rep.res f A)) 2) := by
    intro L _ _ g hg
    simpa only [Rep.res, MonoidHom.coe_comp, Function.comp_def] using
      h12 (f.comp g) (hf.comp hg)
  have hzero : Subsingleton (tateCohomologyZero (Rep.res f A)) :=
    subsingleton_tate_12 (Rep.res f A) h12K
  exact cover_12_injective A f hf hzero (h12 f hf).1

/-- **Theorem II.3.10, degree-minus-one case.** The subgroup `H¹/H²`
hypothesis implies vanishing of `H_T⁻¹` for an arbitrary finite group. -/
theorem subsingleton_cohomology_12
    {k G : Type u} [CommRing k] [Group G] [Fintype G]
    (A : Rep.{u} k G)
    (h12 : ∀ {K : Type u} [Group K] [Finite K] (f : K →* G),
      Function.Injective f →
        IsZero (groupCohomology (Rep.res f A) 1) ∧
        IsZero (groupCohomology (Rep.res f A) 2)) :
    Subsingleton (tateCohomologyOne A) := by
  have h12' : ∀ {K : Type u} [Group K] [Finite K] (f : K →* G),
      Function.Injective f →
        IsZero (groupCohomology
          (Rep.res f (coverSequence A).X₁) 1) ∧
        IsZero (groupCohomology
          (Rep.res f (coverSequence A).X₁) 2) :=
    cover_h_12 A h12
  have hzero' : Subsingleton
      (tateCohomologyZero (coverSequence A).X₁) :=
    subsingleton_tate_12
      (coverSequence A).X₁ h12'
  letI : Subsingleton
      (tateCohomologyZero (coverSequence A).X₁) := hzero'
  exact (cover_shift_self A).injective.subsingleton

set_option maxHeartbeats 1000000 in
-- Recursive elaboration unfolds a fresh induced cover at each homological degree.
/-- **Theorem II.3.10, Tate degrees below minus one.** Under the subgroup
`H¹/H²` hypothesis, every positive group homology group vanishes for an
arbitrary finite group. -/
theorem homology_h_12
    {k G : Type u} [CommRing k] [Group G] [Finite G]
    (A : Rep.{u} k G)
    (h12 : ∀ {K : Type u} [Group K] [Finite K] (f : K →* G),
      Function.Injective f →
        IsZero (groupCohomology (Rep.res f A) 1) ∧
        IsZero (groupCohomology (Rep.res f A) 2))
    (n : ℕ) (hn : 0 < n) : IsZero (groupHomology A n) := by
  letI : Fintype G := Fintype.ofFinite G
  have h12' : ∀ {K : Type u} [Group K] [Finite K] (f : K →* G),
      Function.Injective f →
        IsZero (groupCohomology
          (Rep.res f (coverSequence A).X₁) 1) ∧
        IsZero (groupCohomology
          (Rep.res f (coverSequence A).X₁) 2) :=
    cover_h_12 A h12
  by_cases hn1 : n = 1
  · subst n
    have hneg' : Subsingleton
        (tateCohomologyOne (coverSequence A).X₁) :=
      subsingleton_cohomology_12
        (coverSequence A).X₁ h12'
    letI : Subsingleton
        (tateCohomologyOne (coverSequence A).X₁) := hneg'
    letI : Subsingleton (groupHomology A 1) :=
      (coverOneShift A).injective.subsingleton
    exact ModuleCat.isZero_of_subsingleton _
  · obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
    have hm : 0 < m := by omega
    have ih := homology_h_12
      (coverSequence A).X₁ h12' m hm
    exact ih.of_iso (coverHomologyShift A m hm)
termination_by n

/-- **Theorem II.3.10.** This packages all four ranges of Tate cohomology
represented in the project, with exactly Milne's hypothesis on literal
subgroups. -/
theorem allDegrees
    {k G : Type u} [CommRing k] [Group G] [Fintype G]
    (A : Rep.{u} k G)
    (h12 : ∀ H : Subgroup G,
      IsZero (groupCohomology (Rep.res H.subtype A) 1) ∧
      IsZero (groupCohomology (Rep.res H.subtype A) 2)) :
    (∀ n : ℕ, 0 < n → IsZero (groupCohomology A n)) ∧
      Subsingleton (tateCohomologyZero A) ∧
      Subsingleton (tateCohomologyOne A) ∧
      (∀ n : ℕ, 0 < n → IsZero (groupHomology A n)) := by
  have h12' : ∀ {K : Type u} [Group K] [Finite K] (f : K →* G),
      Function.Injective f →
        IsZero (groupCohomology (Rep.res f A) 1) ∧
        IsZero (groupCohomology (Rep.res f A) 2) := by
    intro K _ _ f hf
    exact cohomology_12_subgroups A h12 f hf
  exact ⟨fun n hn => cohomology_h_12 A h12' n hn,
    subsingleton_tate_12 A h12',
    subsingleton_cohomology_12 A h12',
    fun n hn => homology_h_12 A h12' n hn⟩

end

end Towers.CField.Shifting
