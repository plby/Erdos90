import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Submission.ClassField.LocalBrauer.CanonicalNormData

/-!
# Principal-unit approximation in an unramified extension

This file supplies generator-free ideal-theoretic lemmas for Milne's
successive unit-norm approximation.  In particular, formal unramifiedness
identifies maximal ideals, while faithful flatness makes all of their powers
contract exactly.
-/

namespace Submission.CField.LBrauer

noncomputable section

open IsLocalRing
open scoped BigOperators

universe u v w

/-- Every power of the maximal ideal contracts exactly through a finite
torsion-free formally unramified extension of local DVRs. -/
theorem maximal_comap_formally
    {A : Type u} {B : Type v}
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CommRing B] [IsDomain B] [IsLocalRing B]
    [Algebra A B] [Module.Finite A B] [Module.IsTorsionFree A B]
    [IsLocalHom (algebraMap A B)] [Algebra.FormallyUnramified A B]
    (m : ℕ) :
    ((maximalIdeal B) ^ m).comap (algebraMap A B) =
      (maximalIdeal A) ^ m := by
  letI : Module.Free A B := Module.free_of_finite_type_torsion_free'
  letI : Module.FaithfullyFlat A B := inferInstance
  rw [← Algebra.FormallyUnramified.map_maximalIdeal (R := A) (S := B),
    ← Ideal.map_pow]
  exact Ideal.comap_map_eq_self_of_faithfullyFlat ((maximalIdeal A) ^ m)

/-- Trace surjectivity supplies a one-step norm correction on positive
principal-unit layers.  This formulation is independent of a choice of
uniformizer or coordinates on the successive quotients. -/
theorem principal_formally_unramified
    {A B : Type u} {G : Type w}
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [Algebra A B] [Module.Finite A B] [Module.IsTorsionFree A B]
    [IsLocalHom (algebraMap A B)] [Algebra.FormallyUnramified A B]
    [Group G] [Fintype G] [MulSemiringAction G B]
    [IsGaloisGroup G A B] [Finite (ResidueField B)]
    (N : Bˣ →* Aˣ)
    (hNprod : ∀ v : Bˣ,
      algebraMap A B (N v : A) = ∏ g : G, g • (v : B))
    (m : ℕ) (hm : 0 < m) (u : Aˣ)
    (hu : (u : A) - 1 ∈ (maximalIdeal A) ^ m) :
    ∃ v : Bˣ,
      (v : B) - 1 ∈ (maximalIdeal B) ^ m ∧
        ((u / N v : Aˣ) : A) - 1 ∈ (maximalIdeal A) ^ (m + 1) := by
  letI : (maximalIdeal B).LiesOver (maximalIdeal A) :=
    (Ideal.liesOver_iff _ _).mpr
      (maximalIdeal_comap (algebraMap A B)).symm
  letI : Algebra.IsUnramifiedAt A (maximalIdeal B) := by
    change Algebra.FormallyUnramified A
      (Localization.AtPrime (maximalIdeal B))
    infer_instance
  obtain ⟨tbar, htbar⟩ :=
    UCohom.field_trace_surjective
      (ResidueField A) (ResidueField B) (1 : ResidueField A)
  obtain ⟨t, ht⟩ := residue_surjective tbar
  let s : B := ∑ g : G, g • t
  have hs_fixed (h : G) : h • s = s := by
    change (MulSemiringAction.toRingAut G B h) (∑ g : G, g • t) =
      ∑ g : G, g • t
    rw [map_sum]
    exact Fintype.sum_bijective (h * ·) (Group.mulLeft_bijective h)
      (fun g ↦ (MulSemiringAction.toRingAut G B h) (g • t))
      (fun g ↦ g • t) (fun g ↦ by
        change h • (g • t) = (h * g) • t
        exact smul_smul h g t)
  obtain ⟨c, hc⟩ :=
    Algebra.IsInvariant.isInvariant (A := A) (B := B) (G := G) s hs_fixed
  have hcres : residue A c = 1 := by
    have htrace := residue_sum_unramified
      (A := A) (B := B) (G := G)
      (IsDiscreteValuationRing.not_a_field A)
      (IsDiscreteValuationRing.not_a_field B) c t
      (by
        rw [hc]
        apply Finset.sum_congr
        · ext g
          simp only [Finset.mem_univ]
        · intro g _hg
          rfl)
    rw [ht, htbar] at htrace
    exact htrace
  have hc_one : c - 1 ∈ maximalIdeal A := by
    rw [← residue_eq_zero_iff, map_sub, map_one, hcres, sub_self]
  let d : A := (u : A) - 1
  have hd : d ∈ (maximalIdeal A) ^ m := hu
  let b : B := algebraMap A B d * t
  have hdmap : algebraMap A B d ∈ (maximalIdeal B) ^ m := by
    rw [← Algebra.FormallyUnramified.map_maximalIdeal (R := A) (S := B),
      ← Ideal.map_pow]
    exact Ideal.mem_map_of_mem (algebraMap A B) hd
  have hb : b ∈ (maximalIdeal B) ^ m :=
    ((maximalIdeal B) ^ m).mul_mem_right t hdmap
  have hsum : algebraMap A B (d * c) = ∑ g : G, g • b := by
    rw [map_mul, hc]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro g _
    change algebraMap A B d * (g • t) =
      (MulSemiringAction.toRingAut G B g) (algebraMap A B d * t)
    symm
    rw [map_mul]
    congr 1
    change g • algebraMap A B d = algebraMap A B d
    exact smul_algebraMap g d
  have hdc : d * c - d ∈ (maximalIdeal A) ^ (m + 1) := by
    rw [show d * c - d = d * (c - 1) by ring, pow_succ]
    exact Ideal.mul_mem_mul hd hc_one
  have hdcmap : algebraMap A B (d * c - d) ∈
      (maximalIdeal B) ^ (m + 1) := by
    rw [← Algebra.FormallyUnramified.map_maximalIdeal (R := A) (S := B),
      ← Ideal.map_pow]
    exact Ideal.mem_map_of_mem (algebraMap A B) hdc
  have hprod : (∏ g : G, g • (1 + b)) -
      (1 + algebraMap A B (d * c)) ∈
        (maximalIdeal B) ^ (m + 1) := by
    rw [hsum]
    exact galois_mod_succ m hm hb
  have hbmax : b ∈ maximalIdeal B :=
    Ideal.pow_le_self hm.ne' hb
  have hvunit : IsUnit (1 + b) := by
    have hneg : -b ∈ nonunits B := by
      rw [← IsLocalRing.mem_maximalIdeal]
      exact (maximalIdeal B).neg_mem hbmax
    simpa only [sub_neg_eq_add] using
      IsLocalRing.isUnit_one_sub_self_of_mem_nonunits (-b) hneg
  let v : Bˣ := hvunit.unit
  have hv : (v : B) = 1 + b := hvunit.unit_spec
  refine ⟨v, ?_, ?_⟩
  · rw [hv, add_sub_cancel_left]
    exact hb
  · have hnorm_sub : algebraMap A B ((N v : A) - (u : A)) ∈
        (maximalIdeal B) ^ (m + 1) := by
      rw [map_sub, hNprod, hv]
      have hidentity :
          (∏ g : G, g • (1 + b)) - algebraMap A B (u : A) =
            ((∏ g : G, g • (1 + b)) -
                (1 + algebraMap A B (d * c))) +
              algebraMap A B (d * c - d) := by
        simp only [map_sub]
        simp [d]
        ring
      rw [hidentity]
      exact ((maximalIdeal B) ^ (m + 1)).add_mem hprod hdcmap
    have hnorm_sub_base : (N v : A) - (u : A) ∈
        (maximalIdeal A) ^ (m + 1) :=
      ideal_pow_comap (algebraMap A B)
        (maximalIdeal A) (maximalIdeal B) (m + 1)
        (maximal_comap_formally (m + 1))
        ((N v : A) - (u : A)) hnorm_sub
    have hu_sub_norm : (u : A) - (N v : A) ∈
        (maximalIdeal A) ^ (m + 1) := by
      simpa only [neg_sub] using
        ((maximalIdeal A) ^ (m + 1)).neg_mem hnorm_sub_base
    have hquotient : ((u / N v : Aˣ) : A) - 1 =
        ((u : A) - (N v : A)) * (((N v)⁻¹ : Aˣ) : A) := by
      rw [div_eq_mul_inv, Units.val_mul]
      simp [sub_mul]
    rw [hquotient]
    exact ((maximalIdeal A) ^ (m + 1)).mul_mem_right _ hu_sub_norm

end

end Submission.CField.LBrauer
