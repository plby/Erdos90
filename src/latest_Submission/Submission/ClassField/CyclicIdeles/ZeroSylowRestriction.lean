import Mathlib.Data.Nat.PrimeFin
import Mathlib.GroupTheory.Torsion
import Submission.ClassField.CohomologyOps.RestrictionZero
import Submission.ClassField.Shifting.TateZeroTransfer

/-!
# Sylow restriction in Tate degree zero

This file packages the degree-zero restriction map
`Aᴳ / N_G A → Aᴴ / N_H A`, proves the usual restriction--corestriction
injectivity on a Sylow primary component, and derives finiteness from all
Sylow restrictions.
-/

namespace Submission.CField.CIdeles

open CategoryTheory Representation
open Submission.CField.COps
open Submission.CField.Shifting
open scoped BigOperators

noncomputable section

universe u

variable {k G : Type u} [CommRing k] [Group G] [Fintype G]

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex
attribute [local instance] Fintype.ofFinite

private noncomputable def invariantsMulLinear
    {G₁ G₂ : Type u} [Group G₁] [Group G₂]
    (e : G₁ ≃* G₂) (A : Rep.{u} k G₂) :
    A.ρ.invariants ≃ₗ[k] (Rep.res e.toMonoidHom A).ρ.invariants where
  toFun x := ⟨x.1, fun g ↦ x.2 (e g)⟩
  invFun x := ⟨x.1, fun h ↦ by simpa using x.2 (e.symm h)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem res_mul_norm
    {G₁ G₂ : Type u} [Group G₁] [Group G₂]
    [Fintype G₁] [Fintype G₂]
    (e : G₁ ≃* G₂) (A : Rep.{u} k G₂) (x : A) :
    (Rep.res e.toMonoidHom A).ρ.norm x = A.ρ.norm x := by
  rw [Representation.norm, Representation.norm,
    LinearMap.sum_apply, LinearMap.sum_apply]
  exact e.sum_comp (fun h : G₂ ↦ A.ρ h x)

private theorem norm_range_equiv
    {G₁ G₂ : Type u} [Group G₁] [Group G₂]
    [Fintype G₁] [Fintype G₂]
    (e : G₁ ≃* G₂) (A : Rep.{u} k G₂) :
    (LinearMap.range (normCoinvariantsInvariants A)).map
        (invariantsMulLinear e A).toLinearMap =
      LinearMap.range
        (normCoinvariantsInvariants (Rep.res e.toMonoidHom A)) := by
  ext x
  constructor
  · rintro ⟨_, ⟨c, rfl⟩, rfl⟩
    obtain ⟨y, rfl⟩ := Coinvariants.mk_surjective A.ρ c
    refine ⟨Coinvariants.mk (Rep.res e.toMonoidHom A).ρ y, ?_⟩
    rw [coinvariants_invariants_mk,
      coinvariants_invariants_mk]
    apply Subtype.ext
    change (Rep.res e.toMonoidHom A).ρ.norm y = A.ρ.norm y
    exact res_mul_norm e A y
  · rintro ⟨c, rfl⟩
    obtain ⟨y, rfl⟩ := Coinvariants.mk_surjective
      (Rep.res e.toMonoidHom A).ρ c
    refine ⟨normCoinvariantsInvariants A (Coinvariants.mk A.ρ y),
      ⟨Coinvariants.mk A.ρ y, rfl⟩, ?_⟩
    rw [coinvariants_invariants_mk,
      coinvariants_invariants_mk]
    apply Subtype.ext
    change A.ρ.norm y = (Rep.res e.toMonoidHom A).ρ.norm y
    exact (res_mul_norm e A y).symm

/-- Tate degree zero is invariant under relabelling the finite acting group
by an equivalence. -/
noncomputable def tateCohomologyAdd
    {G₁ G₂ : Type u} [Group G₁] [Group G₂]
    [Fintype G₁] [Fintype G₂]
    (e : G₁ ≃* G₂) (A : Rep.{u} k G₂) :
    tateCohomologyZero A ≃+
      tateCohomologyZero (Rep.res e.toMonoidHom A) :=
  (Submodule.Quotient.equiv
    (LinearMap.range (normCoinvariantsInvariants A))
    (LinearMap.range
      (normCoinvariantsInvariants (Rep.res e.toMonoidHom A)))
    (invariantsMulLinear e A)
    (norm_range_equiv e A)).toAddEquiv

private theorem restriction_zero_norm
    (A : Rep.{u} k G) (H : Subgroup G)
    (c : A.ρ.Coinvariants) :
    restrictionZero A H (normCoinvariantsInvariants A c) ∈
      LinearMap.range
        (normCoinvariantsInvariants (Rep.res H.subtype A)) := by
  obtain ⟨y, rfl⟩ := Coinvariants.mk_surjective A.ρ c
  let T : H.RightTransversal := default
  let z : A := ∑ t : {t : G // t ∈ T.1}, A.ρ (t : G) y
  refine ⟨Coinvariants.mk (Rep.res H.subtype A).ρ z, ?_⟩
  rw [coinvariants_invariants_mk]
  apply Subtype.ext
  change (Rep.res H.subtype A).ρ.norm z =
    (normCoinvariantsInvariants A (Coinvariants.mk A.ρ y)).1
  rw [coinvariants_invariants_mk]
  change (Rep.res H.subtype A).ρ.norm z = A.ρ.norm y
  rw [Representation.norm, LinearMap.sum_apply,
    Representation.norm, LinearMap.sum_apply]
  simp only [z, map_sum]
  calc
    (∑ h : H, ∑ t : {t : G // t ∈ T.1},
        A.ρ (h : G) (A.ρ (t : G) y)) =
        ∑ h : H, ∑ t : {t : G // t ∈ T.1},
          A.ρ ((h : G) * (t : G)) y := by
      apply Fintype.sum_congr
      intro h
      apply Fintype.sum_congr
      intro t
      rw [← Module.End.mul_apply, ← map_mul]
    _ = ∑ q : H × {t : G // t ∈ T.1},
        A.ρ ((q.1 : G) * (q.2 : G)) y := by
      rw [Fintype.sum_prod_type]
    _ = ∑ g : G,
        A.ρ (((T.2.equiv g).1 : G) * ((T.2.equiv g).2 : G)) y :=
      (T.2.equiv.sum_comp
        (fun q : H × {t : G // t ∈ T.1} ↦
          A.ρ ((q.1 : G) * (q.2 : G)) y)).symm
    _ = ∑ g : G, A.ρ g y := by
      apply Fintype.sum_congr
      intro g
      rw [T.2.equiv_fst_mul_equiv_snd]

/-- Restriction in Tate degree zero. -/
noncomputable def tateRestrictionZero
    (A : Rep.{u} k G) (H : Subgroup G) :
    tateCohomologyZero A →ₗ[k]
      tateCohomologyZero (Rep.res H.subtype A) :=
  Submodule.mapQ
    (LinearMap.range (normCoinvariantsInvariants A))
    (LinearMap.range
      (normCoinvariantsInvariants (Rep.res H.subtype A)))
    (restrictionZero A H)
    (by
      rintro x ⟨c, rfl⟩
      exact restriction_zero_norm A H c)

@[simp]
theorem tate_restriction_mk
    (A : Rep.{u} k G) (H : Subgroup G) (x : A.ρ.invariants) :
    tateRestrictionZero A H
        (Submodule.Quotient.mk
          (p := LinearMap.range (normCoinvariantsInvariants A)) x) =
      Submodule.Quotient.mk
        (p := LinearMap.range
          (normCoinvariantsInvariants (Rep.res H.subtype A)))
        (restrictionZero A H x) :=
  rfl

private theorem index_nsmul_restriction
    (A : Rep.{u} k G) (H : Subgroup G)
    (a : tateCohomologyZero A)
    (ha : tateRestrictionZero A H a = 0) :
    H.index • a = 0 := by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective
    (LinearMap.range (normCoinvariantsInvariants A)) a
  rw [tate_restriction_mk] at ha
  have hmem : restrictionZero A H x ∈
      LinearMap.range
        (normCoinvariantsInvariants (Rep.res H.subtype A)) :=
    (Submodule.Quotient.mk_eq_zero _).mp ha
  obtain ⟨c, hc⟩ := hmem
  obtain ⟨y, rfl⟩ := Coinvariants.mk_surjective
    (Rep.res H.subtype A).ρ c
  rw [coinvariants_invariants_mk] at hc
  let S : H.LeftTransversal := default
  apply (Submodule.Quotient.mk_eq_zero _).2
  refine ⟨Coinvariants.mk A.ρ y, ?_⟩
  rw [coinvariants_invariants_mk]
  change ⟨A.ρ.norm y, _⟩ = H.index • x
  calc
    ⟨A.ρ.norm y, fun g ↦ A.ρ.self_norm_apply g y⟩ =
        corestrictionZero A H S
          ⟨(Rep.res H.subtype A).ρ.norm y,
            fun h ↦ (Rep.res H.subtype A).ρ.self_norm_apply h y⟩ :=
      by
        apply Subtype.ext
        exact congrArg Subtype.val
          (corestriction_norm_restrict A H S y).symm
    _ = corestrictionZero A H S (restrictionZero A H x) := by rw [hc]
    _ = H.index • x := corestriction_zero_restriction A H S x

/-- Restriction to a Sylow `p`-subgroup is injective on the `p`-primary
component of Tate degree zero. -/
theorem inj_primary_component
    (A : Rep.{u} k G) (p : ℕ) [Fact p.Prime] (P : Sylow p G) :
    Set.InjOn (tateRestrictionZero A (P : Subgroup G))
      (AddCommGroup.primaryComponent (tateCohomologyZero A) p) := by
  intro x hx y hy hxy
  suffices x - y = 0 by exact sub_eq_zero.mp this
  let z : tateCohomologyZero A := x - y
  have hzprimary : z ∈
      AddCommGroup.primaryComponent (tateCohomologyZero A) p :=
    (AddCommGroup.primaryComponent (tateCohomologyZero A) p).sub_mem hx hy
  have hres : tateRestrictionZero A (P : Subgroup G) z = 0 := by
    simp [z, hxy]
  have hindex : (P : Subgroup G).index • z = 0 :=
    index_nsmul_restriction A P z hres
  have horderIndex : addOrderOf z ∣ (P : Subgroup G).index :=
    addOrderOf_dvd_iff_nsmul_eq_zero.mpr hindex
  obtain ⟨e, he⟩ := hzprimary
  by_cases hz : z = 0
  · exact hz
  have horderPow : addOrderOf z ∣ p ^ e :=
    addOrderOf_dvd_iff_nsmul_eq_zero.mpr he
  obtain ⟨k, _hk, horder⟩ :=
    (Nat.dvd_prime_pow (Fact.out : Nat.Prime p)).mp horderPow
  have hkzero : k ≠ 0 := by
    intro hk
    apply hz
    apply AddMonoid.addOrderOf_eq_one_iff.mp
    simp [horder, hk]
  have hpOrder : p ∣ addOrderOf z := by
    rw [horder]
    exact dvd_pow (dvd_refl p) hkzero
  exact (P.not_dvd_index (hpOrder.trans horderIndex)).elim

/-- Tate degree zero is annihilated by the order of the acting group. -/
theorem nsmul_tate_cohomology
    (A : Rep.{u} k G) (a : tateCohomologyZero A) :
    Nat.card G • a = 0 := by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective
    (LinearMap.range (normCoinvariantsInvariants A)) a
  apply (Submodule.Quotient.mk_eq_zero _).2
  refine ⟨Coinvariants.mk A.ρ x.1, ?_⟩
  rw [coinvariants_invariants_mk]
  apply Subtype.ext
  change A.ρ.norm x.1 = Nat.card G • x.1
  rw [Representation.norm, LinearMap.sum_apply]
  calc
    (∑ g : G, A.ρ g x.1) = ∑ _g : G, x.1 := by
      apply Fintype.sum_congr
      intro g
      exact x.2 g
    _ = Nat.card G • x.1 := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_eq_nat_card]

/-- Finiteness of Tate degree zero is detected on all Sylow restrictions. -/
theorem tate_cohomology_sylow
    (A : Rep.{u} k G)
    (hfinite : ∀ (p : ℕ) [Fact p.Prime] (P : Sylow p G),
      Finite (tateCohomologyZero
        (Rep.res (P : Subgroup G).subtype A))) :
    Finite (tateCohomologyZero A) := by
  let I := {p : ℕ // p ∈ (Nat.card G).primeFactors}
  let primeFact (i : I) : Fact i.1.Prime :=
    ⟨Nat.prime_of_mem_primeFactors i.2⟩
  let P (i : I) : Sylow i.1 G := by
    letI : Fact i.1.Prime := primeFact i
    exact Classical.choice Sylow.nonempty
  let T (i : I) := tateCohomologyZero
    (Rep.res ((P i : Sylow i.1 G) : Subgroup G).subtype A)
  letI (i : I) : Finite (T i) := by
    dsimp only [T]
    letI : Fact i.1.Prime := primeFact i
    exact hfinite i.1 (P i)
  let f : tateCohomologyZero A → ∀ i : I, T i :=
    fun x i ↦ tateRestrictionZero A (P i : Subgroup G) x
  have hf : Function.Injective f := by
    intro x y hxy
    suffices x - y = 0 by exact sub_eq_zero.mp this
    let z : tateCohomologyZero A := x - y
    have horderCard : addOrderOf z ∣ Nat.card G :=
      addOrderOf_dvd_iff_nsmul_eq_zero.mpr
        (nsmul_tate_cohomology A z)
    by_contra hz
    have horder : addOrderOf z ≠ 1 := by simpa [z] using hz
    obtain ⟨p, hp, hpOrder⟩ := Nat.exists_prime_and_dvd horder
    have hpCard : p ∣ Nat.card G := hpOrder.trans horderCard
    have hpMem : p ∈ (Nat.card G).primeFactors :=
      hp.mem_primeFactors hpCard Nat.card_pos.ne'
    let i : I := ⟨p, hpMem⟩
    letI : Fact p.Prime := ⟨hp⟩
    let Q : Sylow p G := P i
    have hres : tateRestrictionZero A (Q : Subgroup G) z = 0 := by
      have hi := congrFun hxy i
      change tateRestrictionZero A (Q : Subgroup G) x =
        tateRestrictionZero A (Q : Subgroup G) y at hi
      simp [z, hi]
    have hindex : (Q : Subgroup G).index • z = 0 :=
      index_nsmul_restriction A Q z hres
    have horderIndex : addOrderOf z ∣ (Q : Subgroup G).index :=
      addOrderOf_dvd_iff_nsmul_eq_zero.mpr hindex
    exact Q.not_dvd_index (hpOrder.trans horderIndex)
  exact Finite.of_injective f hf

/-- The order of the ambient `p`-primary component divides the order of the
Tate degree-zero group after restriction to a Sylow `p`-subgroup. -/
theorem ord_proj_restriction
    (A : Rep.{u} k G) (p : ℕ) [Fact p.Prime] (P : Sylow p G)
    [Finite (tateCohomologyZero A)]
    [Finite (tateCohomologyZero
      (Rep.res (P : Subgroup G).subtype A))] :
    ordProj[p] (Nat.card (tateCohomologyZero A)) ∣
      Nat.card (tateCohomologyZero
        (Rep.res (P : Subgroup G).subtype A)) := by
  let T := tateCohomologyZero
    (Rep.res (P : Subgroup G).subtype A)
  let M := Multiplicative (tateCohomologyZero A)
  let Q : Sylow p M := Classical.choice Sylow.nonempty
  let f : Q →* Multiplicative T :=
    (tateRestrictionZero A (P : Subgroup G)).toAddMonoidHom.toMultiplicative.comp
      (Q : Subgroup M).subtype
  have hQprimary (x : Q) :
      Multiplicative.toAdd (x : M) ∈
        AddCommGroup.primaryComponent (tateCohomologyZero A) p := by
    obtain ⟨m, hm⟩ := (IsPGroup.iff_orderOf.mp Q.isPGroup') x
    refine ⟨m, ?_⟩
    apply Multiplicative.ofAdd.injective
    simp only [ofAdd_nsmul, ofAdd_toAdd, ofAdd_zero]
    have hm' : orderOf (x : M) = p ^ m := by
      simpa only [orderOf_submonoid] using hm
    rw [← hm']
    exact pow_orderOf_eq_one (x : M)
  have hf : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    change Multiplicative.toAdd (x : M) = Multiplicative.toAdd (y : M)
    apply inj_primary_component A p P
      (hQprimary x) (hQprimary y)
    exact hxy
  have hQrange : Nat.card Q = Nat.card f.range :=
    Nat.card_congr (Equiv.ofInjective f hf)
  have hQdvd : Nat.card Q ∣ Nat.card T := by
    rw [hQrange]
    exact f.range.card_subgroup_dvd_card
  rw [Q.card_eq_multiplicity] at hQdvd
  simpa only [M, T] using hQdvd

end

end Submission.CField.CIdeles
