import Towers.ClassField.CohomologyOps.AcyclicInflation
import Towers.ClassField.Shifting.SubsingletonLinearEquiv
import Towers.ClassField.Shifting.SolvableGroup
import Towers.ClassField.Shifting.SylowDetection
import Mathlib.GroupTheory.Nilpotent

/-!
# Milne, Class Field Theory, Theorem II.3.10: positive solvable case

This file carries out Milne's induction on the order of a finite solvable
group in every positive cohomological degree.
-/

namespace Towers.CField.Shifting

open CategoryTheory CategoryTheory.Limits Rep

noncomputable section

universe u

set_option maxHeartbeats 2000000 in
-- Recursive elaboration compares cohomology over a subgroup and its cyclic quotient.
/-- **Theorem II.3.10, positive-degree solvable case.** The hypothesis is
written for every injective homomorphism into `G`; this is the subgroup
hypothesis in a form stable under the recursive restriction to a subgroup. -/
theorem zero_cohomology_solvable
    {k G : Type u} [CommRing k] [Group G] [Finite G] [IsSolvable G]
    (A : Rep.{u} k G)
    (h12 : ∀ {K : Type u} [Group K] [Finite K] (f : K →* G),
      Function.Injective f →
        IsZero (groupCohomology (Rep.res f A) 1) ∧
        IsZero (groupCohomology (Rep.res f A) 2))
    (n : ℕ) (hn : 0 < n) : IsZero (groupCohomology A n) := by
  classical
  by_cases hG : Nontrivial G
  · letI : Nontrivial G := hG
    obtain ⟨H, hHtop, hnormal, hcyclic⟩ :=
      proper_normal_cyclic (G := G)
    letI : H.Normal := hnormal
    have h12H : ∀ {K : Type u} [Group K] [Finite K] (f : K →* H),
        Function.Injective f →
          IsZero (groupCohomology
            (Rep.res f (Rep.res H.subtype A)) 1) ∧
          IsZero (groupCohomology
            (Rep.res f (Rep.res H.subtype A)) 2) := by
      intro K _ _ f hf
      simpa only [Rep.res, MonoidHom.coe_comp, Function.comp_def] using
        h12 (H.subtype.comp f) (H.subtype_injective.comp hf)
    have hHacyclic : ∀ q : ℕ, 0 < q →
        IsZero (groupCohomology (Rep.res H.subtype A) q) := by
      intro q hq
      exact zero_cohomology_solvable
        (Rep.res H.subtype A) h12H q hq
    let e1 := COps.inflationIsoAcyclic
      A H hHacyclic 1 Nat.zero_lt_one
    let e2 := COps.inflationIsoAcyclic
      A H hHacyclic 2 (by omega)
    have hG12 := h12 (MonoidHom.id G) (fun _ _ h => h)
    have hQ1 : IsZero
        (groupCohomology (A.quotientToInvariants H) 1) :=
      hG12.1.of_iso e1
    have hQ2 : IsZero
        (groupCohomology (A.quotientToInvariants H) 2) :=
      hG12.2.of_iso e2
    letI : IsCyclic (G ⧸ H) := hcyclic
    letI : CommGroup (G ⧸ H) := IsCyclic.commGroup
    letI : Fintype (G ⧸ H) := Fintype.ofFinite (G ⧸ H)
    obtain ⟨g, hg⟩ := isCyclic_iff_exists_zpowers_eq_top.mp
      (inferInstance : IsCyclic (G ⧸ H))
    have hQ : Subsingleton
        (groupCohomology (A.quotientToInvariants H) n) :=
      subsingleton_cohomology_cyclic
        (A.quotientToInvariants H) g (by
          intro x
          rw [hg]
          trivial)
        (ModuleCat.subsingleton_of_isZero hQ1)
        (ModuleCat.subsingleton_of_isZero hQ2) n hn
    have hQzero : IsZero
        (groupCohomology (A.quotientToInvariants H) n) := by
      letI := hQ
      exact ModuleCat.isZero_of_subsingleton _
    exact hQzero.of_iso
      (COps.inflationIsoAcyclic
        A H hHacyclic n hn).symm
  · letI : Subsingleton G := not_nontrivial_iff_subsingleton.mp hG
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
    exact isZero_groupCohomology_succ_of_subsingleton A m
termination_by Nat.card G
decreasing_by
  exact nat_ne_top H hHtop

/-- **Theorem II.3.10, positive cohomological range.** Vanishing of `H^1`
and `H^2` after every injective restriction implies vanishing in every
positive degree for an arbitrary finite group. -/
theorem cohomology_h_12
    {k G : Type u} [CommRing k] [Group G] [Finite G]
    (A : Rep.{u} k G)
    (h12 : ∀ {K : Type u} [Group K] [Finite K] (f : K →* G),
      Function.Injective f →
        IsZero (groupCohomology (Rep.res f A) 1) ∧
        IsZero (groupCohomology (Rep.res f A) 2))
    (n : ℕ) (hn : 0 < n) : IsZero (groupCohomology A n) := by
  letI : Fintype G := Fintype.ofFinite G
  letI : Subsingleton (groupCohomology A n) :=
    subsingleton_group_sylow A n fun p _ P => by
      letI : Group.IsNilpotent ↥(P : Subgroup G) :=
        @IsPGroup.isNilpotent ↥(P : Subgroup G) _ _ p _ P.isPGroup'
      letI : IsSolvable ↥(P : Subgroup G) := inferInstance
      have h12P : ∀ {K : Type u} [Group K] [Finite K]
          (f : K →* ↥(P : Subgroup G)),
          Function.Injective f →
            IsZero (groupCohomology
              (Rep.res f (Rep.res (P : Subgroup G).subtype A)) 1) ∧
            IsZero (groupCohomology
              (Rep.res f (Rep.res (P : Subgroup G).subtype A)) 2) := by
        intro K _ _ f hf
        simpa only [Rep.res, MonoidHom.coe_comp, Function.comp_def] using
          h12 ((P : Subgroup G).subtype.comp f)
            ((P : Subgroup G).subtype_injective.comp hf)
      exact ModuleCat.subsingleton_of_isZero
        (zero_cohomology_solvable
          (Rep.res (P : Subgroup G).subtype A) h12P n hn)
  exact ModuleCat.isZero_of_subsingleton _

end

end Towers.CField.Shifting
