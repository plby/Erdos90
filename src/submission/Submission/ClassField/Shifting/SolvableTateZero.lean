import Submission.ClassField.Shifting.NormTransitivity
import Submission.ClassField.Shifting.SolvablePositive

/-!
# Milne, Class Field Theory, Theorem II.3.10: solvable degree zero

This file carries out the exceptional-degree step in Milne's induction on a
finite solvable group.  The key input is transitivity of the norm across a
normal subgroup.
-/

namespace Submission.CField.Shifting

open CategoryTheory CategoryTheory.Limits Rep

noncomputable section

universe u

set_option maxHeartbeats 2000000 in
-- Recursive elaboration compares Tate degree zero over a subgroup and quotient.
/-- **Theorem II.3.10, degree-zero solvable case.** Vanishing of `H¹` and
`H²` after every injective restriction implies vanishing of `H_T⁰` for a
finite solvable group. -/
theorem subsingleton_tate_solvable
    {k G : Type u} [CommRing k] [Group G] [Fintype G] [IsSolvable G]
    (A : Rep.{u} k G)
    (h12 : ∀ {K : Type u} [Group K] [Finite K] (f : K →* G),
      Function.Injective f →
        IsZero (groupCohomology (Rep.res f A) 1) ∧
        IsZero (groupCohomology (Rep.res f A) 2)) :
    Subsingleton (tateCohomologyZero A) := by
  classical
  by_cases hG : Nontrivial G
  · letI : Nontrivial G := hG
    obtain ⟨H, hHtop, hnormal, hcyclic⟩ :=
      proper_normal_cyclic (G := G)
    letI : H.Normal := hnormal
    letI : Fintype H := Fintype.ofFinite H
    letI : Fintype (G ⧸ H) := Fintype.ofFinite (G ⧸ H)
    have h12H : ∀ {K : Type u} [Group K] [Finite K] (f : K →* H),
        Function.Injective f →
          IsZero (groupCohomology
            (Rep.res f (Rep.res H.subtype A)) 1) ∧
          IsZero (groupCohomology
            (Rep.res f (Rep.res H.subtype A)) 2) := by
      intro K _ _ f hf
      simpa only [Rep.res, MonoidHom.coe_comp, Function.comp_def] using
        h12 (H.subtype.comp f) (H.subtype_injective.comp hf)
    have hH0 : Subsingleton
        (tateCohomologyZero (Rep.res H.subtype A)) :=
      subsingleton_tate_solvable
        (Rep.res H.subtype A) h12H
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
    obtain ⟨g, hg⟩ := isCyclic_iff_exists_zpowers_eq_top.mp
      (inferInstance : IsCyclic (G ⧸ H))
    have hQ0 : Subsingleton
        (tateCohomologyZero (A.quotientToInvariants H)) :=
      (tate_subsingleton_cyclic
        (A.quotientToInvariants H) g (by
          intro x
          rw [hg]
          trivial)
        (ModuleCat.subsingleton_of_isZero hQ1)
        (ModuleCat.subsingleton_of_isZero hQ2)).2.1
    exact subsingleton_cohomology_normal A H hH0 hQ0
  · letI : Subsingleton G := not_nontrivial_iff_subsingleton.mp hG
    letI : IsCyclic G := inferInstance
    letI : CommGroup G := IsCyclic.commGroup
    obtain ⟨g, hg⟩ := isCyclic_iff_exists_zpowers_eq_top.mp
      (inferInstance : IsCyclic G)
    have hG12 := h12 (MonoidHom.id G) (fun _ _ h => h)
    exact (tate_subsingleton_cyclic A g (by
      intro x
      rw [hg]
      trivial)
      (ModuleCat.subsingleton_of_isZero hG12.1)
      (ModuleCat.subsingleton_of_isZero hG12.2)).2.1
termination_by Nat.card G
decreasing_by
  exact nat_ne_top H hHtop

end

end Submission.CField.Shifting
