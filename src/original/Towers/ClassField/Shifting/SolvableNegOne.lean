import Towers.ClassField.Shifting.SolvableTateZero
import Towers.ClassField.Shifting.TateCoverClosure
import Towers.ClassField.Shifting.TateLowerShift

/-!
# Milne, Class Field Theory, Theorem II.3.10: solvable degree minus one

Milne obtains the negative range by repeatedly applying the induced cover.
This file carries out the first recursive step.  The kernel of the cover again
satisfies the degree-one and degree-two hypothesis, so its degree-zero Tate
cohomology vanishes; the exceptional cover shift then gives vanishing in
degree minus one for the original module.
-/

namespace Towers.CField.Shifting

open CategoryTheory CategoryTheory.Limits Rep

noncomputable section

universe u

/-- Over a finite solvable group, the kernel of Milne's induced cover again
satisfies the hypothesis of Theorem II.3.10 after every injective
restriction. -/
theorem cover_12_solvable
    {k G : Type u} [CommRing k] [Group G] [Finite G] [IsSolvable G]
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
  letI : IsSolvable K := solvable_of_solvable_injective hf
  have h12K : ∀ {L : Type u} [Group L] [Finite L] (g : L →* K),
      Function.Injective g →
        IsZero (groupCohomology (Rep.res g (Rep.res f A)) 1) ∧
        IsZero (groupCohomology (Rep.res g (Rep.res f A)) 2) := by
    intro L _ _ g hg
    simpa only [Rep.res, MonoidHom.coe_comp, Function.comp_def] using
      h12 (f.comp g) (hf.comp hg)
  have hzero : Subsingleton (tateCohomologyZero (Rep.res f A)) :=
    subsingleton_tate_solvable (Rep.res f A) h12K
  exact cover_12_injective A f hf hzero (h12 f hf).1

/-- **Theorem II.3.10, degree-minus-one solvable case.** Vanishing of `H¹`
and `H²` after every injective restriction implies vanishing of
`H_T⁻¹(G,A)` for a finite solvable group. -/
theorem subsingleton_cohomology_solvable
    {k G : Type u} [CommRing k] [Group G] [Fintype G] [IsSolvable G]
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
    cover_12_solvable A h12
  have hzero' : Subsingleton
      (tateCohomologyZero (coverSequence A).X₁) :=
    subsingleton_tate_solvable
      (coverSequence A).X₁ h12'
  letI : Subsingleton
      (tateCohomologyZero (coverSequence A).X₁) := hzero'
  exact (cover_shift_self A).injective.subsingleton

set_option maxHeartbeats 1000000 in
-- Recursive elaboration unfolds a fresh induced cover at each homological degree.
/-- **Theorem II.3.10, negative solvable range below minus one.** Under the
degree-one and degree-two hypothesis, every positive group homology group
vanishes.  These are precisely the Tate groups in degrees below `-1`. -/
theorem homology_solvable_12
    {k G : Type u} [CommRing k] [Group G] [Finite G] [IsSolvable G]
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
    cover_12_solvable A h12
  by_cases hn1 : n = 1
  · subst n
    have hneg' : Subsingleton
        (tateCohomologyOne (coverSequence A).X₁) :=
      subsingleton_cohomology_solvable
        (coverSequence A).X₁ h12'
    letI : Subsingleton
        (tateCohomologyOne (coverSequence A).X₁) := hneg'
    letI : Subsingleton (groupHomology A 1) :=
      (coverOneShift A).injective.subsingleton
    exact ModuleCat.isZero_of_subsingleton _
  · obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
    have hm : 0 < m := by omega
    have ih := homology_solvable_12
      (coverSequence A).X₁ h12' m hm
    exact ih.of_iso (coverHomologyShift A m hm)
termination_by n

end

end Towers.CField.Shifting
