import Mathlib.GroupTheory.Sylow
import Towers.ClassField.CohomologyOps.RestrictionZero
import Towers.ClassField.Shifting.SolvableTateZero

/-!
# Milne, Class Field Theory, Theorem II.3.10: Tate degree-zero transfer

This file extends the Sylow-detection step to Tate degree zero.  The essential
calculation is that corestricting the norm for a subgroup gives the norm for
the whole group.
-/

namespace Towers.CField.Shifting

open CategoryTheory CategoryTheory.Limits Rep
open scoped BigOperators

noncomputable section

universe u

variable {k G : Type u} [CommRing k] [Group G] [Fintype G]

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex
attribute [local instance] Fintype.ofFinite

/-- Corestriction carries the norm for a subgroup to the norm for the whole
group. -/
theorem corestriction_norm_restrict
    (A : Rep.{u} k G) (H : Subgroup G) (S : H.LeftTransversal) (x : A) :
    COps.corestrictionZero A H S
        ⟨(Rep.res H.subtype A).ρ.norm x,
          fun h => (Rep.res H.subtype A).ρ.self_norm_apply h x⟩ =
      ⟨A.ρ.norm x, fun g => A.ρ.self_norm_apply g x⟩ := by
  apply Subtype.ext
  simp only [COps.corestrictionZero,
    COps.transversalNorm, Representation.norm,
    LinearMap.sum_apply]
  calc
    ∑ q : G ⧸ H, A.ρ (S.2.leftQuotientEquiv q : G)
        (∑ h : H, A.ρ h x) =
        ∑ q : G ⧸ H, ∑ h : H,
          A.ρ ((S.2.leftQuotientEquiv q : G) * h) x := by
      apply Fintype.sum_congr
      intro q
      simp [map_sum, ← Module.End.mul_apply, ← map_mul]
    _ = ∑ s : {s : G // s ∈ S.1}, ∑ h : H,
        A.ρ ((s : G) * h) x :=
      S.2.leftQuotientEquiv.sum_comp
        (fun s : {s : G // s ∈ S.1} =>
          ∑ h : H, A.ρ ((s : G) * h) x)
    _ = ∑ p : ({s : G // s ∈ S.1} × H),
        A.ρ ((p.1 : G) * p.2) x := by
      rw [Fintype.sum_prod_type]
    _ = ∑ g : G,
        A.ρ (((S.2.equiv g).1 : G) * (S.2.equiv g).2) x :=
      (S.2.equiv.sum_comp
        (fun p : ({s : G // s ∈ S.1} × H) =>
          A.ρ ((p.1 : G) * p.2) x)).symm
    _ = ∑ g : G, A.ρ g x := by
      apply Fintype.sum_congr
      intro g
      rw [S.2.equiv_fst_mul_equiv_snd]

/-- Vanishing of Tate degree zero on every Sylow subgroup detects vanishing
on the ambient finite group. -/
theorem subsingleton_cohomology_sylow
    (A : Rep.{u} k G)
    (hSylow : ∀ (p : ℕ) [Fact p.Prime] (P : Sylow p G),
      Subsingleton
        (tateCohomologyZero (Rep.res (P : Subgroup G).subtype A))) :
    Subsingleton (tateCohomologyZero A) := by
  constructor
  intro a b
  by_contra hab
  have hsub : a - b ≠ 0 := sub_ne_zero.mpr hab
  have horder : addOrderOf (a - b) ≠ 1 := by simpa using hsub
  obtain ⟨p, hp, hpOrder⟩ := Nat.exists_prime_and_dvd horder
  letI : Fact p.Prime := ⟨hp⟩
  let P : Sylow p G := Classical.choice Sylow.nonempty
  letI : Subsingleton
      (tateCohomologyZero (Rep.res (P : Subgroup G).subtype A)) :=
    hSylow p P
  obtain ⟨x, hx⟩ := Submodule.Quotient.mk_surjective
    (LinearMap.range (normCoinvariantsInvariants A)) (a - b)
  have hnormP : Function.Surjective
      (normCoinvariantsInvariants
        (Rep.res (P : Subgroup G).subtype A)) :=
    (coinvariants_invariants_surjective _).2 inferInstance
  obtain ⟨c, hc⟩ := hnormP
    (COps.restrictionZero A (P : Subgroup G) x)
  obtain ⟨y, rfl⟩ := Representation.Coinvariants.mk_surjective
    (Rep.res (P : Subgroup G).subtype A).ρ c
  let S : (P : Subgroup G).LeftTransversal := default
  have hindexNorm : (P : Subgroup G).index • x =
      normCoinvariantsInvariants A
        (Representation.Coinvariants.mk A.ρ y) := by
    rw [coinvariants_invariants_mk] at hc
    rw [coinvariants_invariants_mk]
    calc
      (P : Subgroup G).index • x =
          COps.corestrictionZero A (P : Subgroup G) S
            (COps.restrictionZero A (P : Subgroup G) x) :=
        (COps.corestriction_zero_restriction
          A (P : Subgroup G) S x).symm
      _ = COps.corestrictionZero A (P : Subgroup G) S
          ⟨(Rep.res (P : Subgroup G).subtype A).ρ.norm y,
            fun h => (Rep.res (P : Subgroup G).subtype A).ρ.self_norm_apply h y⟩ :=
        congrArg (COps.corestrictionZero A (P : Subgroup G) S)
          hc.symm
      _ = ⟨A.ρ.norm y, fun g => A.ρ.self_norm_apply g y⟩ :=
        corestriction_norm_restrict A (P : Subgroup G) S y
  have hindex : (P : Subgroup G).index • (a - b) = 0 := by
    rw [← hx]
    apply (Submodule.Quotient.mk_eq_zero _).2
    exact ⟨Representation.Coinvariants.mk A.ρ y, hindexNorm.symm⟩
  have hOrderIndex : addOrderOf (a - b) ∣ (P : Subgroup G).index :=
    addOrderOf_dvd_iff_nsmul_eq_zero.mpr hindex
  exact P.not_dvd_index (hpOrder.trans hOrderIndex)

/-- **Theorem II.3.10, degree-zero case.** The subgroup `H¹/H²`
hypothesis implies vanishing of Tate degree zero for an arbitrary finite
group. -/
theorem subsingleton_tate_12
    {k G : Type u} [CommRing k] [Group G] [Fintype G]
    (A : Rep.{u} k G)
    (h12 : ∀ {K : Type u} [Group K] [Finite K] (f : K →* G),
      Function.Injective f →
        IsZero (groupCohomology (Rep.res f A) 1) ∧
        IsZero (groupCohomology (Rep.res f A) 2)) :
    Subsingleton (tateCohomologyZero A) := by
  apply subsingleton_cohomology_sylow A
  intro p _ P
  letI : Group.IsNilpotent ↑(P : Subgroup G) :=
    @IsPGroup.isNilpotent ↑(P : Subgroup G) _ _ p _ P.isPGroup'
  letI : IsSolvable ↑(P : Subgroup G) := inferInstance
  have h12P : ∀ {K : Type u} [Group K] [Finite K]
      (f : K →* ↑(P : Subgroup G)), Function.Injective f →
        IsZero (groupCohomology
          (Rep.res f (Rep.res (P : Subgroup G).subtype A)) 1) ∧
        IsZero (groupCohomology
          (Rep.res f (Rep.res (P : Subgroup G).subtype A)) 2) := by
    intro K _ _ f hf
    simpa only [Rep.res, MonoidHom.coe_comp, Function.comp_def] using
      h12 ((P : Subgroup G).subtype.comp f)
        ((P : Subgroup G).subtype_injective.comp hf)
  exact subsingleton_tate_solvable
    (Rep.res (P : Subgroup G).subtype A) h12P

end

end Towers.CField.Shifting
