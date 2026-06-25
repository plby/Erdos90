import Submission.ClassField.HasseNorm.PositiveDirectSum
import Submission.ClassField.Shifting.AssemblingTensorShift
import Mathlib.GroupTheory.Coset.Card

/-!
# Tate degree zero for the idèle direct-sum decomposition

This file proves the exceptional degree-zero clause of Proposition VII.2.5.
It constructs functorial maps on invariants modulo norms, proves the
degree-zero form of Shapiro directly for coinduced modules, and then repeats
the finite-support direct-limit argument from the positive degrees.
-/

namespace Submission.CField.HNorm

open CategoryTheory CategoryTheory.Limits Representation
open IsDedekindDomain NumberField
open Submission.NumberTheory.Milne
open Submission.CField.COps
open Submission.CField.Shifting
open Submission.CField.Ideles
open Submission.CField.ICohomo

noncomputable section

-- The arithmetic representations below have several inherited additive
-- structures; allow instance search to resolve the intended quotient one.

universe u

/-! ## Functoriality and Shapiro in Tate degree zero -/

variable {k G : Type u} [CommRing k] [Group G] [Fintype G]

/-- A morphism of representations induces a map on invariants modulo
norms. -/
noncomputable def tateCohomology
    {A B : Rep.{u} k G} (f : A ⟶ B) :
    tateCohomologyZero A →ₗ[k] tateCohomologyZero B := by
  let fInv := ((Rep.invariantsFunctor k G).map f).hom
  let normA : A.ρ.Coinvariants →ₗ[k] A.ρ.invariants :=
    Shifting.normCoinvariantsInvariants A
  let normB : B.ρ.Coinvariants →ₗ[k] B.ρ.invariants :=
    Shifting.normCoinvariantsInvariants B
  refine normA.range.liftQ (normB.range.mkQ.comp fInv) ?_
  intro z hz
  rcases hz with ⟨c, rfl⟩
  obtain ⟨x, rfl⟩ := Coinvariants.mk_surjective A.ρ c
  rw [LinearMap.mem_ker]
  change normB.range.mkQ
    (fInv (Shifting.normCoinvariantsInvariants A (Coinvariants.mk A.ρ x))) = 0
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  refine ⟨Coinvariants.mk B.ρ (f x), ?_⟩
  rw [coinvariants_invariants_mk, coinvariants_invariants_mk]
  apply Subtype.ext
  dsimp only [fInv]
  change B.ρ.norm (f x) = f (A.ρ.norm x)
  exact congrArg (fun q : A ⟶ B ↦ q.hom x) (Rep.norm_comm f)

@[simp]
theorem tate_cohomology_mk
    {A B : Rep.{u} k G} (f : A ⟶ B) (z : A.ρ.invariants) :
    tateCohomology f (Submodule.Quotient.mk z) =
      Submodule.Quotient.mk (((Rep.invariantsFunctor k G).map f).hom z) := by
  unfold tateCohomology
  rw [Submodule.liftQ_apply]
  rfl

/-- Membership in the norm range can be witnessed before passage to
coinvariants. -/
theorem tate_range_raw
    (A : Rep.{u} k G) (z : A.ρ.invariants) :
    z ∈ LinearMap.range (Shifting.normCoinvariantsInvariants A) ↔
      ∃ x : A,
        ⟨A.ρ.norm x, fun g ↦ A.ρ.self_norm_apply g x⟩ = z := by
  constructor
  · rintro ⟨c, rfl⟩
    obtain ⟨x, rfl⟩ := Coinvariants.mk_surjective A.ρ c
    exact ⟨x, rfl⟩
  · rintro ⟨x, rfl⟩
    exact ⟨Coinvariants.mk A.ρ x, rfl⟩

/-- Evaluation at one identifies invariants of a coinduced representation
with invariants of the subgroup representation. -/
noncomputable def coinducedInvariantsLinear
    (H : Subgroup G) (A : Rep.{u} k H) :
    (Rep.coind H.subtype A).ρ.invariants ≃ₗ[k] A.ρ.invariants where
  toFun x := ⟨x.1.1 1, fun h ↦ by
    have hx := congrArg (fun f ↦ f.1 1) (x.2 (h : G))
    calc
      A.ρ h (x.1.1 1) = x.1.1 h := by
        simpa using (x.1.2 h 1).symm
      _ = x.1.1 1 := by simpa [Representation.coind] using hx⟩
  invFun m := ⟨⟨fun _ ↦ m.1, fun h g ↦ by simpa using (m.2 h).symm⟩,
    fun g ↦ by apply Subtype.ext; funext t; rfl⟩
  left_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    funext g
    have hx := congrArg (fun f ↦ f.1 1) (x.2 g)
    simpa [Representation.coind] using hx.symm
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

/-- One fiber of the right-coset quotient is a copy of the subgroup. -/
noncomputable def rightCosetFiber (H : Subgroup G)
    (q : Quotient (QuotientGroup.rightRel H)) :
    {g : G // Quotient.mk'' g = q} ≃ H where
  toFun z := ⟨z.1 * q.out⁻¹, by
    have hzq : Quotient.mk'' z.1 = Quotient.mk'' q.out :=
      z.2.trans (Quotient.out_eq' q).symm
    have hrel := Quotient.exact' hzq
    have hm : q.out * z.1⁻¹ ∈ H :=
      QuotientGroup.rightRel_apply.mp hrel
    simpa only [mul_inv_rev, inv_inv] using H.inv_mem hm⟩
  invFun h := ⟨h.1 * q.out, by
    calc
      Quotient.mk'' (h.1 * q.out) = Quotient.mk'' q.out := by
        apply Quotient.sound'
        apply QuotientGroup.rightRel_apply.mpr
        simp [H.inv_mem h.2]
      _ = q := Quotient.out_eq' q⟩
  left_inv z := by
    apply Subtype.ext
    simp
  right_inv h := by
    apply Subtype.ext
    simp

/-- Evaluation at one sends a global norm in a coinduced module to a local
subgroup norm. -/
theorem coinduced_invariants_norm
    (H : Subgroup G) [Fintype H] (A : Rep.{u} k H)
    (x : Rep.coind H.subtype A) :
    coinducedInvariantsLinear H A
        ⟨(Rep.coind H.subtype A).ρ.norm x,
          fun g ↦ (Rep.coind H.subtype A).ρ.self_norm_apply g x⟩ ∈
      LinearMap.range (Shifting.normCoinvariantsInvariants A) := by
  classical
  apply (tate_range_raw A _).2
  let Q := Quotient (QuotientGroup.rightRel H)
  let a : A := ∑ q : Q, x.1 q.out
  refine ⟨a, Subtype.ext ?_⟩
  change A.ρ.norm a = ((Rep.coind H.subtype A).ρ.norm x).1 1
  rw [show ((Rep.coind H.subtype A).ρ.norm x).1 1 =
      ∑ g : G, x.1 g by
    rw [Representation.norm, LinearMap.sum_apply, Submodule.coe_sum,
      Finset.sum_apply]
    apply Finset.sum_congr rfl
    intro g _
    exact induced_action_apply H A g x 1 |>.trans (by rw [one_mul])]
  simp only [Representation.norm, LinearMap.sum_apply]
  change (∑ h : H, A.ρ h a) = ∑ g : G, x.1 g
  rw [show (∑ h : H, A.ρ h a) =
      ∑ q : Q, ∑ h : H, A.ρ h (x.1 q.out) by
    simp only [a, map_sum]
    rw [Finset.sum_comm]]
  rw [← Fintype.sum_fiberwise
    (fun g : G ↦ (Quotient.mk'' g : Quotient (QuotientGroup.rightRel H)))
    (fun g : G ↦ x.1 g)]
  apply Fintype.sum_congr
  intro q
  calc
    (∑ h : H, A.ρ h (x.1 q.out)) =
        ∑ h : H, x.1 (h.1 * q.out) := by
      apply Finset.sum_congr rfl
      intro h _
      exact (x.2 h q.out).symm
    _ = ∑ z : {g : G // Quotient.mk'' g = q}, x.1 z.1 := by
      exact (rightCosetFiber H q).symm.sum_comp
        (fun z : {g : G // Quotient.mk'' g = q} ↦ x.1 z.1)

/-- Every local subgroup norm is obtained by evaluating a global norm in
the coinduced module. -/
theorem coinduced_invariants_symm
    (H : Subgroup G) [Fintype H] (A : Rep.{u} k H)
    (z : A.ρ.invariants)
    (hz : z ∈ LinearMap.range (Shifting.normCoinvariantsInvariants A)) :
    (coinducedInvariantsLinear H A).symm z ∈
      LinearMap.range
        (Shifting.normCoinvariantsInvariants (Rep.coind H.subtype A)) := by
  obtain ⟨a, ha⟩ := (tate_range_raw A z).1 hz
  classical
  let f : G → A := fun g ↦ if hg : g ∈ H then A.ρ ⟨g, hg⟩ a else 0
  have hf (h : H) (g : G) : f (h.1 * g) = A.ρ h (f g) := by
    by_cases hg : g ∈ H
    · have hhg : h.1 * g ∈ H := H.mul_mem h.2 hg
      simp only [f, dif_pos hg, dif_pos hhg]
      rw [← Module.End.mul_apply, ← map_mul]
      rfl
    · have hhg : h.1 * g ∉ H := by
        intro hmem
        apply hg
        simpa [← mul_assoc] using H.mul_mem (H.inv_mem h.2) hmem
      simp [f, hg, hhg]
  let y : Rep.coind H.subtype A := ⟨f, hf⟩
  apply (tate_range_raw (Rep.coind H.subtype A) _).2
  refine ⟨y, ?_⟩
  apply (coinducedInvariantsLinear H A).injective
  rw [(coinducedInvariantsLinear H A).apply_symm_apply]
  apply Subtype.ext
  change ((Rep.coind H.subtype A).ρ.norm y).1 1 = z.1
  rw [show ((Rep.coind H.subtype A).ρ.norm y).1 1 =
      ∑ g : G, f g by
    rw [Representation.norm, LinearMap.sum_apply, Submodule.coe_sum,
      Finset.sum_apply]
    apply Finset.sum_congr rfl
    intro g _
    exact induced_action_apply H A g y 1 |>.trans (by rw [one_mul])]
  rw [← ha]
  change (∑ g : G, f g) = A.ρ.norm a
  rw [Representation.norm, LinearMap.sum_apply]
  simp only [f]
  calc
    (∑ g : G, if hg : g ∈ H then A.ρ ⟨g, hg⟩ a else 0) =
        ∑ g ∈ Finset.univ.filter (· ∈ H),
          if hg : g ∈ H then A.ρ ⟨g, hg⟩ a else 0 := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro g _
      by_cases hg : g ∈ H <;> simp [hg]
    _ = ∑ h : H, A.ρ h a := by
      rw [Finset.sum_subtype (p := fun g : G ↦ g ∈ H)
        (F := inferInstanceAs (Fintype H))]
      · apply Finset.sum_congr rfl
        intro h _
        simp
      · intro g
        simp

/-- Degree-zero Tate Shapiro for a coinduced representation. -/
noncomputable def tateCohomologyCoinduced
    (H : Subgroup G) [Fintype H] (A : Rep.{u} k H) :
    tateCohomologyZero (Rep.coind H.subtype A) ≃+
      tateCohomologyZero A := by
  have hrange :
      (LinearMap.range
        (Shifting.normCoinvariantsInvariants (Rep.coind H.subtype A))).map
          (coinducedInvariantsLinear H A).toLinearMap =
        LinearMap.range (Shifting.normCoinvariantsInvariants A) := by
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨y, hy⟩ := (tate_range_raw
        (Rep.coind H.subtype A) x).1 hx
      subst x
      exact coinduced_invariants_norm H A y
    · intro hz
      refine ⟨(coinducedInvariantsLinear H A).symm z, ?_, ?_⟩
      · exact coinduced_invariants_symm H A z hz
      · exact (coinducedInvariantsLinear H A).apply_symm_apply z
  exact (Submodule.Quotient.equiv
    (LinearMap.range
      (Shifting.normCoinvariantsInvariants (Rep.coind H.subtype A)))
    (LinearMap.range (Shifting.normCoinvariantsInvariants A))
    (coinducedInvariantsLinear H A) hrange).toAddEquiv

/-! ## Tate degree zero and arbitrary products -/

variable {ι : Type u}

local instance tateProductRepModule
    (X : Rep.{u, u, u} k G) : Module k X := X.hV2

/-- Coordinate projection on Tate degree zero for a categorical product of
representations. -/
noncomputable def tateProductPi (A : ι → Rep.{u} k G) :
    tateCohomologyZero (∏ᶜ A) →+
      (∀ i, tateCohomologyZero (A i)) where
  toFun q i := tateCohomology (Pi.π A i) q
  map_zero' := by
    funext i
    exact map_zero _
  map_add' x y := by
    funext i
    exact map_add _ x y

theorem tate_pi_surjective
    (A : ι → Rep.{u} k G) :
    Function.Surjective (tateProductPi A) := by
  classical
  letI : PreservesLimit (Discrete.functor A)
      (forget (Rep k G)) := by
    change PreservesLimit (Discrete.functor A)
      (forget₂ (Rep k G) (ModuleCat k) ⋙ forget (ModuleCat k))
    infer_instance
  intro q
  have hrepresentative (i : ι) :
      ∃ z : (A i).ρ.invariants, Submodule.Quotient.mk z = q i :=
    tate_projection_surjective (A i) (q i)
  choose z hz using hrepresentative
  let x : ↑(∏ᶜ A) := (Concrete.productEquiv A).symm (fun i ↦ (z i).1)
  have hx (g : G) : (∏ᶜ A).ρ g x = x := by
    apply (Concrete.productEquiv A).injective
    funext i
    rw [Concrete.productEquiv_apply_apply,
      Concrete.productEquiv_apply_apply]
    change (Pi.π A i).hom ((∏ᶜ A).ρ g x) = (Pi.π A i).hom x
    rw [Rep.hom_comm_apply]
    rw [show (Pi.π A i).hom x = (z i).1 by
      exact Concrete.productEquiv_symm_apply_π A (fun i ↦ (z i).1) i]
    exact (z i).2 g
  refine ⟨Submodule.Quotient.mk ⟨x, hx⟩, ?_⟩
  funext i
  change tateCohomology (Pi.π A i)
    (Submodule.Quotient.mk ⟨x, hx⟩) = q i
  rw [tate_cohomology_mk, ← hz i]
  congr 1
  apply Subtype.ext
  exact Concrete.productEquiv_symm_apply_π A (fun i ↦ (z i).1) i

theorem tate_pi_injective
    (A : ι → Rep.{u} k G) :
    Function.Injective (tateProductPi A) := by
  classical
  letI : PreservesLimit (Discrete.functor A)
      (forget (Rep k G)) := by
    change PreservesLimit (Discrete.functor A)
      (forget₂ (Rep k G) (ModuleCat k) ⋙ forget (ModuleCat k))
    infer_instance
  have hkernel (q : tateCohomologyZero (∏ᶜ A))
      (hq : tateProductPi A q = 0) : q = 0 := by
    obtain ⟨z, rfl⟩ :=
      tate_projection_surjective (∏ᶜ A) q
    have hcoord (i : ι) :
        (((Rep.invariantsFunctor k G).map (Pi.π A i)).hom z) ∈
          LinearMap.range (Shifting.normCoinvariantsInvariants (A i)) := by
      have hi : (Submodule.Quotient.mk
          (((Rep.invariantsFunctor k G).map (Pi.π A i)).hom z) :
            tateCohomologyZero (A i)) = 0 := by
        have hi₀ := congrFun hq i
        change tateCohomology (Pi.π A i)
          (tateCohomologyProjection (∏ᶜ A) z) = 0 at hi₀
        unfold tateCohomologyProjection at hi₀
        rw [Submodule.mkQ_apply, tate_cohomology_mk] at hi₀
        exact hi₀
      exact (Submodule.Quotient.mk_eq_zero
        (LinearMap.range (Shifting.normCoinvariantsInvariants (A i)))).1 hi
    have hraw (i : ι) : ∃ y : A i,
        ⟨(A i).ρ.norm y, fun g ↦ (A i).ρ.self_norm_apply g y⟩ =
          ((Rep.invariantsFunctor k G).map (Pi.π A i)).hom z :=
      (tate_range_raw (A i) _).1 (hcoord i)
    choose y hy using hraw
    let yProduct : ↑(∏ᶜ A) :=
      (Concrete.productEquiv A).symm (fun i ↦ y i)
    unfold tateCohomologyProjection
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    apply (tate_range_raw (∏ᶜ A) z).2
    refine ⟨yProduct, Subtype.ext ?_⟩
    apply (Concrete.productEquiv A).injective
    funext i
    rw [Concrete.productEquiv_apply_apply,
      Concrete.productEquiv_apply_apply]
    change (Pi.π A i).hom ((∏ᶜ A).ρ.norm yProduct) =
      (Pi.π A i).hom z.1
    rw [show (Pi.π A i).hom ((∏ᶜ A).ρ.norm yProduct) =
        (A i).ρ.norm ((Pi.π A i).hom yProduct) by
      exact congrArg (fun f : (∏ᶜ A) ⟶ A i ↦ f.hom yProduct)
        (Rep.norm_comm (Pi.π A i)) |>.symm]
    rw [show (Pi.π A i).hom yProduct = y i by
      exact Concrete.productEquiv_symm_apply_π A (fun i ↦ y i) i]
    exact congrArg Subtype.val (hy i)
  intro q q' hqq'
  apply sub_eq_zero.mp
  apply hkernel
  rw [map_sub, hqq', sub_self]

/-- Tate degree zero commutes with arbitrary categorical products. -/
noncomputable def tateCohomologyPi
    (A : ι → Rep.{u} k G) :
    tateCohomologyZero (∏ᶜ A) ≃+
      (∀ i, tateCohomologyZero (A i)) :=
  AddEquiv.ofBijective (tateProductPi A)
    ⟨tate_pi_injective A,
      tate_pi_surjective A⟩

/-- Functoriality of the degree-zero Tate map under composition. -/
theorem tate_cohomology_comp
    {A B C : Rep.{u} k G} (f : A ⟶ B) (g : B ⟶ C)
    (q : tateCohomologyZero A) :
    tateCohomology (f ≫ g) q =
      tateCohomology g (tateCohomology f q) := by
  obtain ⟨z, rfl⟩ := tate_projection_surjective A q
  unfold tateCohomologyProjection
  rw [Submodule.mkQ_apply]
  rw [tate_cohomology_mk (f := f ≫ g)]
  rw [tate_cohomology_mk (f := f)]
  let w : B.ρ.invariants :=
    ((Rep.invariantsFunctor k G).map f).hom z
  change Submodule.Quotient.mk
      (((Rep.invariantsFunctor k G).map (f ≫ g)).hom z) =
    tateCohomology g (Submodule.Quotient.mk w)
  rw [tate_cohomology_mk]
  rfl

/-- The degree-zero Tate map of an identity morphism is the identity. -/
theorem tate_cohomology_id
    (A : Rep.{u} k G) (q : tateCohomologyZero A) :
    tateCohomology (𝟙 A) q = q := by
  obtain ⟨z, rfl⟩ := tate_projection_surjective A q
  unfold tateCohomologyProjection
  rw [Submodule.mkQ_apply]
  rw [tate_cohomology_mk]
  rfl

/-- The two projections identify Tate degree zero of a categorical binary
product with the product of the two Tate groups. -/
noncomputable def tateBinaryProd
    (A B : Rep.{u} k G) :
    tateCohomologyZero (A ⨯ B) →+
      tateCohomologyZero A × tateCohomologyZero B where
  toFun q :=
    (tateCohomology (Limits.prod.fst : A ⨯ B ⟶ A) q,
      tateCohomology (Limits.prod.snd : A ⨯ B ⟶ B) q)
  map_zero' := by simp
  map_add' _ _ := by simp

theorem tate_binary_surjective
    (A B : Rep.{u} k G) :
    Function.Surjective (tateBinaryProd A B) := by
  classical
  letI : PreservesLimit (pair A B) (forget (Rep k G)) := by
    change PreservesLimit (pair A B)
      (forget₂ (Rep k G) (ModuleCat k) ⋙ forget (ModuleCat k))
    infer_instance
  rintro ⟨qA, qB⟩
  obtain ⟨zA, rfl⟩ := tate_projection_surjective A qA
  obtain ⟨zB, rfl⟩ := tate_projection_surjective B qB
  let x : ↑(A ⨯ B) := (Concrete.prodEquiv A B).symm (zA.1, zB.1)
  have hx (g : G) : (A ⨯ B).ρ g x = x := by
    apply (Concrete.prodEquiv A B).injective
    apply Prod.ext
    · rw [Concrete.prodEquiv_apply_fst, Concrete.prodEquiv_apply_fst]
      change (Limits.prod.fst : A ⨯ B ⟶ A).hom ((A ⨯ B).ρ g x) =
        (Limits.prod.fst : A ⨯ B ⟶ A).hom x
      rw [Rep.hom_comm_apply]
      rw [show (Limits.prod.fst : A ⨯ B ⟶ A).hom x = zA.1 by
        exact Concrete.prodEquiv_symm_apply_fst A B (zA.1, zB.1)]
      exact zA.2 g
    · rw [Concrete.prodEquiv_apply_snd, Concrete.prodEquiv_apply_snd]
      change (Limits.prod.snd : A ⨯ B ⟶ B).hom ((A ⨯ B).ρ g x) =
        (Limits.prod.snd : A ⨯ B ⟶ B).hom x
      rw [Rep.hom_comm_apply]
      rw [show (Limits.prod.snd : A ⨯ B ⟶ B).hom x = zB.1 by
        exact Concrete.prodEquiv_symm_apply_snd A B (zA.1, zB.1)]
      exact zB.2 g
  refine ⟨Submodule.Quotient.mk ⟨x, hx⟩, ?_⟩
  apply Prod.ext
  · change tateCohomology (Limits.prod.fst : A ⨯ B ⟶ A)
      (Submodule.Quotient.mk ⟨x, hx⟩) = Submodule.Quotient.mk zA
    rw [tate_cohomology_mk]
    congr 1
    apply Subtype.ext
    exact Concrete.prodEquiv_symm_apply_fst A B (zA.1, zB.1)
  · change tateCohomology (Limits.prod.snd : A ⨯ B ⟶ B)
      (Submodule.Quotient.mk ⟨x, hx⟩) = Submodule.Quotient.mk zB
    rw [tate_cohomology_mk]
    congr 1
    apply Subtype.ext
    exact Concrete.prodEquiv_symm_apply_snd A B (zA.1, zB.1)

theorem tate_binary_injective
    (A B : Rep.{u} k G) :
    Function.Injective (tateBinaryProd A B) := by
  classical
  letI : PreservesLimit (pair A B) (forget (Rep k G)) := by
    change PreservesLimit (pair A B)
      (forget₂ (Rep k G) (ModuleCat k) ⋙ forget (ModuleCat k))
    infer_instance
  have hkernel (q : tateCohomologyZero (A ⨯ B))
      (hq : tateBinaryProd A B q = 0) : q = 0 := by
    obtain ⟨z, rfl⟩ := tate_projection_surjective (A ⨯ B) q
    have hcoordA :
        (((Rep.invariantsFunctor k G).map
          (Limits.prod.fst : A ⨯ B ⟶ A)).hom z) ∈
          LinearMap.range (Shifting.normCoinvariantsInvariants A) := by
      apply (Submodule.Quotient.mk_eq_zero
        (LinearMap.range (Shifting.normCoinvariantsInvariants A))).1
      have h := congrArg Prod.fst hq
      change tateCohomology (Limits.prod.fst : A ⨯ B ⟶ A)
        (tateCohomologyProjection (A ⨯ B) z) = 0 at h
      unfold tateCohomologyProjection at h
      rw [Submodule.mkQ_apply, tate_cohomology_mk] at h
      exact h
    have hcoordB :
        (((Rep.invariantsFunctor k G).map
          (Limits.prod.snd : A ⨯ B ⟶ B)).hom z) ∈
          LinearMap.range (Shifting.normCoinvariantsInvariants B) := by
      apply (Submodule.Quotient.mk_eq_zero
        (LinearMap.range (Shifting.normCoinvariantsInvariants B))).1
      have h := congrArg Prod.snd hq
      change tateCohomology (Limits.prod.snd : A ⨯ B ⟶ B)
        (tateCohomologyProjection (A ⨯ B) z) = 0 at h
      unfold tateCohomologyProjection at h
      rw [Submodule.mkQ_apply, tate_cohomology_mk] at h
      exact h
    obtain ⟨yA, hyA⟩ :=
      (tate_range_raw A _).1 hcoordA
    obtain ⟨yB, hyB⟩ :=
      (tate_range_raw B _).1 hcoordB
    let y : ↑(A ⨯ B) := (Concrete.prodEquiv A B).symm (yA, yB)
    unfold tateCohomologyProjection
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    apply (tate_range_raw (A ⨯ B) z).2
    refine ⟨y, Subtype.ext ?_⟩
    apply (Concrete.prodEquiv A B).injective
    apply Prod.ext
    · rw [Concrete.prodEquiv_apply_fst, Concrete.prodEquiv_apply_fst]
      change (Limits.prod.fst : A ⨯ B ⟶ A).hom ((A ⨯ B).ρ.norm y) =
        (Limits.prod.fst : A ⨯ B ⟶ A).hom z.1
      rw [show (Limits.prod.fst : A ⨯ B ⟶ A).hom ((A ⨯ B).ρ.norm y) =
          A.ρ.norm ((Limits.prod.fst : A ⨯ B ⟶ A).hom y) by
        exact (congrArg (fun f : A ⨯ B ⟶ A ↦ f.hom y)
          (Rep.norm_comm (Limits.prod.fst : A ⨯ B ⟶ A))).symm]
      rw [show (Limits.prod.fst : A ⨯ B ⟶ A).hom y = yA by
        exact Concrete.prodEquiv_symm_apply_fst A B (yA, yB)]
      exact congrArg Subtype.val hyA
    · rw [Concrete.prodEquiv_apply_snd, Concrete.prodEquiv_apply_snd]
      change (Limits.prod.snd : A ⨯ B ⟶ B).hom ((A ⨯ B).ρ.norm y) =
        (Limits.prod.snd : A ⨯ B ⟶ B).hom z.1
      rw [show (Limits.prod.snd : A ⨯ B ⟶ B).hom ((A ⨯ B).ρ.norm y) =
          B.ρ.norm ((Limits.prod.snd : A ⨯ B ⟶ B).hom y) by
        exact (congrArg (fun f : A ⨯ B ⟶ B ↦ f.hom y)
          (Rep.norm_comm (Limits.prod.snd : A ⨯ B ⟶ B))).symm]
      rw [show (Limits.prod.snd : A ⨯ B ⟶ B).hom y = yB by
        exact Concrete.prodEquiv_symm_apply_snd A B (yA, yB)]
      exact congrArg Subtype.val hyB
  intro q q' hqq'
  apply sub_eq_zero.mp
  apply hkernel
  rw [map_sub, hqq', sub_self]

noncomputable def tateCohomologyBinary
    (A B : Rep.{u} k G) :
    tateCohomologyZero (A ⨯ B) ≃+
      tateCohomologyZero A × tateCohomologyZero B :=
  AddEquiv.ofBijective (tateBinaryProd A B)
    ⟨tate_binary_injective A B,
      tate_binary_surjective A B⟩

theorem tate_cohomology_iso
    {A B : Rep.{u} k G} (e : A ≅ B) (q : tateCohomologyZero A) :
    tateAddIso e q =
      tateCohomology e.hom q := by
  obtain ⟨z, rfl⟩ := tate_projection_surjective A q
  unfold tateCohomologyProjection
  rw [Submodule.mkQ_apply]
  change tateZeroIso e (Submodule.Quotient.mk z) = _
  rw [tate_iso_mk,
    tate_cohomology_mk]

/-! ## Arithmetic finite-stage Tate groups -/

-- Quotient cohomology over the concrete idèle representations has deeply
-- nested inherited structures; arithmetic declarations need more reduction
-- time than the generic default permits.

variable {K L : Type u} [Field K] [NumberField K]
  [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

local instance tateDirectSumGalFintype : Fintype Gal(L/K) :=
  Fintype.ofFinite Gal(L/K)

local instance (priority := 2000) tateDirectSumRepModule
    (X : Rep.{u, u, u} (ULift.{u} ℤ) Gal(L/K)) :
    Module (ULift.{u} ℤ) X := X.hV2

/-- Choose the algebraic quotient-group structure on Tate degree zero.  This
avoids instance search wandering through the unrelated normed structures on
the concrete completion modules. -/
local instance (priority := 5000) tateDirectSumTateZeroAddCommGroup
    (A : Rep.{u, u, u} (ULift.{u} ℤ) Gal(L/K)) :
    AddCommGroup (tateCohomologyZero A) :=
  Module.addCommMonoidToAddCommGroup (ULift.{u} ℤ)

local instance tateDirectSumFinitePrimeStabilizerFintype
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (Q : FinitePrimesAbove (K := K) (L := L) P) :
    Fintype (primeAboveStabilizer (K := K) (L := L) P Q) :=
  Fintype.ofFinite _

local instance (priority := 2000) tateDirectSumFiniteStageProductAddCommGroup
    (S : Finset (NumberFieldPlace K)) :
    AddCommGroup (tateCohomologyZero
      (resizedStageRepresentation
        (K := K) (L := L) S)) := inferInstance

local instance (priority := 2000) tateDirectSumFiniteStageOrbitAddCommGroup
    (S : Finset (NumberFieldPlace K))
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    AddCommGroup (tateCohomologyZero
      (stageOrbitRepresentation
        (K := K) (L := L) S P)) := inferInstance

local instance (priority := 2000) tateDirectSumIdelesStageAddCommGroup
    (S : Finset (NumberFieldPlace K)) :
    AddCommGroup (tateCohomologyZero
      (resizedPlacesRepresentation
        (K := K) (L := L) S)) := inferInstance

local instance (priority := 2000) tateDirectSumInfiniteIdelesAddCommGroup :
    AddCommGroup (tateCohomologyZero
      (resizedInfiniteRepresentation K L)) := inferInstance

local instance (priority := 2000) tateDirectSumPlaceCompletionAddCommGroup
    (v : NumberFieldPlace K) :
    AddCommGroup (tateCohomologyZero
      (resizedPlaceRepresentation
        (K := K) (L := L) v)) := inferInstance

local instance (priority := 2000) tateDirectSumFinitePrimesLocalUnitsAddCommGroup
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    AddCommGroup (tateCohomologyZero
      (resizedPrimesRepresentation
        (K := K) (L := L) P)) := inferInstance

local instance (priority := 2000) tateDirectSumFinitePrimeLocalUnitsAddCommGroup
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (Q : FinitePrimesAbove (K := K) (L := L) P) :
    AddCommGroup (tateCohomologyZero
      (resizedUnitsRepresentation
        (K := K) (L := L) P Q)) := inferInstance

local instance (priority := 2000) tateDirectSumFiniteCompletionOrbitAddCommGroup
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    AddCommGroup (tateCohomologyZero
      (resizedAboveRepresentation
        (K := K) (L := L) P)) := inferInstance

local instance (priority := 2000) tateDirectSumConcreteIdeleAddCommGroup :
    AddCommGroup (tateCohomologyZero
      (resizedConcreteRepresentation K L)) := inferInstance

local instance tateDirectSumNumberFieldPlaceDecidableEq :
    DecidableEq (NumberFieldPlace K) := Classical.decEq _

local instance tateDirectSumFinitePrimeDecidableEq :
    DecidableEq (HeightOneSpectrum (NumberField.RingOfIntegers K)) :=
  Classical.decEq _

/-- Tate degree zero of the finite-prime pointwise product, coordinatewise. -/
noncomputable def stageTatePi
    (S : Finset (NumberFieldPlace K)) :
    tateCohomologyZero
        (resizedStageRepresentation
          (K := K) (L := L) S) ≃+
      (∀ P : HeightOneSpectrum (NumberField.RingOfIntegers K),
        tateCohomologyZero
          (stageOrbitRepresentation
            (K := K) (L := L) S P)) :=
  (tateAddIso
    (stageIsoCategorical
      (K := K) (L := L) S)).trans
    (tateCohomologyPi
      (fun P : HeightOneSpectrum (NumberField.RingOfIntegers K) ↦
        stageOrbitRepresentation
          (K := K) (L := L) S P))

theorem resized_stage_pi
    (S : Finset (NumberFieldPlace K))
    (q : tateCohomologyZero
      (resizedStageRepresentation
        (K := K) (L := L) S))
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    stageTatePi
        (K := K) (L := L) S q P =
      tateCohomology
        (resizedStageEvaluation
          (K := K) (L := L) S P) q := by
  let A := fun P : HeightOneSpectrum (NumberField.RingOfIntegers K) ↦
    stageOrbitRepresentation (K := K) (L := L) S P
  let e := stageIsoCategorical
    (K := K) (L := L) S
  change tateCohomology (Pi.π A P)
      (tateAddIso e q) = _
  rw [tate_cohomology_iso,
    ← tate_cohomology_comp]
  have hprojection : e.hom ≫ Pi.π A P =
      resizedStageEvaluation
        (K := K) (L := L) S P := by
    rw [← cancel_epi e.inv]
    simp only [Iso.inv_hom_id_assoc]
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro x
    rfl
  rw [hprojection]

/-- Tate degree zero of the infinite idèle factor, indexed by the finitely
many infinite places of the base field. -/
noncomputable def resizedIdelesDirect :
    tateCohomologyZero (resizedInfiniteRepresentation K L) ≃+
      DirectSum (InfinitePlace K) (fun v ↦ tateCohomologyZero
        (resizedPlaceRepresentation
          (K := K) (L := L) (.inr v))) := by
  let A := fun v : InfinitePlace K ↦
    resizedPlaceRepresentation (K := K) (L := L) (.inr v)
  exact ((tateAddIso
    ((resizedIsoProducts
      (K := K) (L := L)).trans
        (productsIsoCategorical
          (K := K) (L := L)))).trans
      (tateCohomologyPi A)).trans
    (DirectSum.addEquivProd
      (fun v : InfinitePlace K ↦ tateCohomologyZero (A v))).symm

set_option maxHeartbeats 1000000 in
-- Splitting the finite stage constructs and composes several large categorical
-- product equivalences, which needs a larger deterministic reduction budget.
/-- A complete finite idèle stage splits into its infinite and finite-prime
Tate-zero factors. -/
noncomputable def resizedIdelesInfinite
    (S : Finset (NumberFieldPlace K)) :
    tateCohomologyZero
        (resizedPlacesRepresentation (K := K) (L := L) S) ≃+
      tateCohomologyZero (resizedInfiniteRepresentation K L) ×
        tateCohomologyZero
          (resizedStageRepresentation
            (K := K) (L := L) S) := by
  let A := resizedInfiniteRepresentation K L
  let B := resizedStageRepresentation (K := K) (L := L) S
  let e : resizedPlacesRepresentation
      (K := K) (L := L) S ≅ A ⨯ B :=
    (resizedRepresentationIso
      (K := K) (L := L) S).trans
      (resizedIsoCategorical
        (K := K) (L := L) S)
  exact (tateAddIso e).trans
    (tateCohomologyBinary A B)

/-! ## The cofinal finite-prime stages -/

theorem units_subsingleton_unramified
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (Q : FinitePrimesAbove (K := K) (L := L) P)
    (hQ : Algebra.IsUnramifiedAt
      (NumberField.RingOfIntegers K) Q.1.asIdeal) :
    Subsingleton (tateCohomologyZero
      (resizedUnitsRepresentation
        (K := K) (L := L) P Q)) := by
  let H := primeAboveStabilizer (K := K) (L := L) P Q
  let A := resizedUnitsRepresentation
    (K := K) (L := L) P Q
  letI : Fintype H := Fintype.ofFinite H
  letI : IsCyclic H :=
    above_stabilizer_unramified
      (K := K) (L := L) P Q hQ
  letI : CommGroup H := IsCyclic.commGroup
  let g := Classical.choose (IsCyclic.exists_generator (α := H))
  let hg := Classical.choose_spec (IsCyclic.exists_generator (α := H))
  letI : Subsingleton (groupCohomology A 2) :=
    cohomology_subsingleton_unramified
      (K := K) (L := L) P Q hQ 2 (by omega)
  exact (tateCohomologyTwo A g hg).injective.subsingleton

theorem resized_subsingleton_unramified
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (Q : FinitePrimesAbove (K := K) (L := L) P)
    (hQ : Algebra.IsUnramifiedAt
      (NumberField.RingOfIntegers K) Q.1.asIdeal) :
    Subsingleton (tateCohomologyZero
      (resizedPrimesRepresentation
        (K := K) (L := L) P)) := by
  let H := primeAboveStabilizer (K := K) (L := L) P Q
  let A := resizedUnitsRepresentation
    (K := K) (L := L) P Q
  letI : Fintype H := Fintype.ofFinite H
  letI : Subsingleton (tateCohomologyZero A) :=
    units_subsingleton_unramified
      (K := K) (L := L) P Q hQ
  let e := (tateAddIso
    (aboveInducedIso
      (K := K) (L := L) P Q)).trans
      (tateCohomologyCoinduced H A)
  exact e.injective.subsingleton

theorem stage_subsingleton_outside
    (S : Finset (NumberFieldPlace K))
    (hunramified :
      ∀ (P : HeightOneSpectrum (NumberField.RingOfIntegers K)),
        (Sum.inl P : NumberFieldPlace K) ∉ S →
          ∀ Q : UpperPrimeFactors (K := K) (L := L) P,
            Algebra.IsUnramifiedAt (NumberField.RingOfIntegers K)
              (upperPrime (K := K) (L := L) P Q).asIdeal)
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hP : (Sum.inl P : NumberFieldPlace K) ∉ S) :
    Subsingleton (tateCohomologyZero
      (stageOrbitRepresentation
        (K := K) (L := L) S P)) := by
  letI : Fact (FinitePlace.mk P).val.IsNontrivial :=
    ⟨absolute_value_nontrivial P⟩
  letI : IsUltrametricDist (FinitePlace.mk P).val.Completion :=
    placeUltrametricDist P
  let w : CompletionPlacesAbove (L := L) (FinitePlace.mk P).val :=
    Classical.choice (absolute_value_extension
      (K := K) (L := L) (FinitePlace.mk P).val)
  let Q₀ : UpperPrimeFactors (K := K) (L := L) P :=
    placeUpperFactor (K := K) (L := L) P w
  let Q : FinitePrimesAbove (K := K) (L := L) P :=
    upperPrimesAbove (K := K) (L := L) P Q₀
  have hQ : Algebra.IsUnramifiedAt
      (NumberField.RingOfIntegers K) Q.1.asIdeal := by
    simpa only [Q, upper_primes_above] using
      hunramified P hP Q₀
  letI : Subsingleton (tateCohomologyZero
      (resizedPrimesRepresentation
        (K := K) (L := L) P)) :=
    resized_subsingleton_unramified
      (K := K) (L := L) P Q hQ
  exact (tateAddIso
    (resizedStageIso
      (K := K) (L := L) S P hP)).injective.subsingleton

structure OrbitTateZero
    (K L : Type u) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K)) where
  down : tateCohomologyZero
    (resizedAboveRepresentation
      (K := K) (L := L) P)

abbrev ExceptionalTateZero
    (K L : Type u) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (S : Finset (NumberFieldPlace K)) :=
  ∀ P : {P : HeightOneSpectrum (NumberField.RingOfIntegers K) //
      (Sum.inl P : NumberFieldPlace K) ∈ S},
    OrbitTateZero K L P.1

noncomputable def orbitTateEquiv
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    OrbitTateZero K L P ≃
      tateCohomologyZero
      (resizedAboveRepresentation
        (K := K) (L := L) P) where
  toFun := OrbitTateZero.down
  invFun := OrbitTateZero.mk
  left_inv _ := rfl
  right_inv _ := rfl

local instance (priority := 3000) finiteCompletionOrbitTateZeroAddCommGroup
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    AddCommGroup (OrbitTateZero K L P) :=
  (orbitTateEquiv (K := K) (L := L) P).addCommGroup

noncomputable def completionOrbitTate
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    OrbitTateZero K L P ≃+
      tateCohomologyZero
        (resizedAboveRepresentation
          (K := K) (L := L) P) :=
  { toEquiv := orbitTateEquiv
      (K := K) (L := L) P
    map_add' := fun _ _ ↦ rfl }

theorem cofinal_tate_subsingleton
    (T : Finset (NumberFieldPlace K))
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hP : (Sum.inl P : NumberFieldPlace K) ∉
      cofinalIdeleStage K L T) :
    Subsingleton (tateCohomologyZero
      (stageOrbitRepresentation
        (K := K) (L := L) (cofinalIdeleStage K L T) P)) := by
  apply stage_subsingleton_outside
    (K := K) (L := L) (cofinalIdeleStage K L T)
  · intro P' hP' Q
    exact unramified_stage_spec (K := K) (L := L) P'
      (fun h ↦ hP' (Finset.mem_union_left _ h)) Q
  · exact hP

/-- Transport in Tate degree zero from an exceptional stage orbit to the
unrestricted completion orbit.  Naming this component equivalence keeps the
dependent product construction below from repeatedly unfolding the rather
large arithmetic representation isomorphism. -/
noncomputable def stageTateFull
    (S : Finset (NumberFieldPlace K))
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hP : (Sum.inl P : NumberFieldPlace K) ∈ S) :
    tateCohomologyZero
        (stageOrbitRepresentation
          (K := K) (L := L) S P) ≃+
      OrbitTateZero K L P :=
  (tateAddIso
    (stageIsoFull
      (K := K) (L := L) S P hP)).trans
    (completionOrbitTate
      (K := K) (L := L) P).symm

/-- The inverse exceptional-orbit transport, kept opaque for the dependent
function equivalence below. -/
noncomputable def stageFullSymm
    (S : Finset (NumberFieldPlace K))
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hP : (Sum.inl P : NumberFieldPlace K) ∈ S) :
    OrbitTateZero K L P ≃+
      tateCohomologyZero
        (stageOrbitRepresentation
          (K := K) (L := L) S P) :=
  (stageTateFull
    (K := K) (L := L) S P hP).symm

@[simp]
theorem stage_full_symm
    (S : Finset (NumberFieldPlace K))
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hP : (Sum.inl P : NumberFieldPlace K) ∈ S)
    (q : tateCohomologyZero
      (stageOrbitRepresentation
        (K := K) (L := L) S P)) :
    stageFullSymm
        (K := K) (L := L) S P hP
        (stageTateFull
          (K := K) (L := L) S P hP q) = q := by
  unfold stageFullSymm
  exact AddEquiv.symm_apply_apply _ q

@[simp]
theorem stage_tate_symm
    (S : Finset (NumberFieldPlace K))
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hP : (Sum.inl P : NumberFieldPlace K) ∈ S)
    (q : OrbitTateZero K L P) :
    stageTateFull
        (K := K) (L := L) S P hP
        (stageFullSymm
          (K := K) (L := L) S P hP q) = q := by
  unfold stageFullSymm
  exact AddEquiv.apply_symm_apply _ q

noncomputable def piTateExceptional
    (S : Finset (NumberFieldPlace K))
    (x : ∀ P : HeightOneSpectrum (NumberField.RingOfIntegers K),
      tateCohomologyZero
        (stageOrbitRepresentation
          (K := K) (L := L) S P)) :
    ExceptionalTateZero K L S := fun P ↦
  stageTateFull
    (K := K) (L := L) S P.1 P.2 (x P.1)

@[simp]
theorem stage_tate_exceptional
    (S : Finset (NumberFieldPlace K))
    (x : ∀ P : HeightOneSpectrum (NumberField.RingOfIntegers K),
      tateCohomologyZero
        (stageOrbitRepresentation
          (K := K) (L := L) S P))
    (P : {P : HeightOneSpectrum (NumberField.RingOfIntegers K) //
      (Sum.inl P : NumberFieldPlace K) ∈ S}) :
    piTateExceptional
        (K := K) (L := L) S x P =
      stageTateFull
        (K := K) (L := L) S P.1 P.2 (x P.1) := rfl

noncomputable def exceptionalStagePi
    (S : Finset (NumberFieldPlace K))
    (x : ExceptionalTateZero K L S)
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    tateCohomologyZero
      (stageOrbitRepresentation
        (K := K) (L := L) S P) :=
  if hP : (Sum.inl P : NumberFieldPlace K) ∈ S then
    stageFullSymm
      (K := K) (L := L) S P hP (x ⟨P, hP⟩)
  else 0

@[simp]
theorem exceptional_tate_pi
    (S : Finset (NumberFieldPlace K))
    (x : ExceptionalTateZero K L S)
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hP : (Sum.inl P : NumberFieldPlace K) ∈ S) :
    exceptionalStagePi
        (K := K) (L := L) S x P =
      stageFullSymm
        (K := K) (L := L) S P hP (x ⟨P, hP⟩) := by
  unfold exceptionalStagePi
  simp only [dif_pos hP]

@[simp]
theorem exceptional_stage_pi
    (S : Finset (NumberFieldPlace K))
    (x : ExceptionalTateZero K L S)
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hP : (Sum.inl P : NumberFieldPlace K) ∉ S) :
    exceptionalStagePi
        (K := K) (L := L) S x P = 0 := by
  unfold exceptionalStagePi
  simp only [dif_neg hP]

set_option maxHeartbeats 1000000 in
-- The inverse law combines proof-dependent coordinates with large arithmetic
-- representation types, so elaboration needs a larger deterministic budget.
noncomputable def stageTateExceptional
    (S : Finset (NumberFieldPlace K))
    (houtside : ∀ P : HeightOneSpectrum
        (NumberField.RingOfIntegers K),
      (Sum.inl P : NumberFieldPlace K) ∉ S →
        Subsingleton (tateCohomologyZero
          (stageOrbitRepresentation
            (K := K) (L := L) S P))) :
    (∀ P : HeightOneSpectrum (NumberField.RingOfIntegers K),
      tateCohomologyZero
        (stageOrbitRepresentation
          (K := K) (L := L) S P)) ≃+
      ExceptionalTateZero K L S where
  toFun := piTateExceptional
    (K := K) (L := L) S
  invFun := exceptionalStagePi
    (K := K) (L := L) S
  left_inv x := by
    funext P
    by_cases hP : (Sum.inl P : NumberFieldPlace K) ∈ S
    · rw [exceptional_tate_pi
        (K := K) (L := L) S _ P hP,
        stage_tate_exceptional,
        stage_full_symm]
    · letI := houtside P hP
      exact Subsingleton.elim _ _
  right_inv x := by
    funext P
    rw [stage_tate_exceptional,
      exceptional_tate_pi
        (K := K) (L := L) S _ P.1 P.2,
      stage_tate_symm]
  map_add' x y := by
    funext P
    change stageTateFull
        (K := K) (L := L) S P.1 P.2 ((x + y) P.1) =
      stageTateFull
          (K := K) (L := L) S P.1 P.2 (x P.1) +
        stageTateFull
          (K := K) (L := L) S P.1 P.2 (y P.1)
    rw [Pi.add_apply]
    exact (stageTateFull
      (K := K) (L := L) S P.1 P.2).map_add (x P.1) (y P.1)

@[simp]
theorem stage_pi_exceptional
    (S : Finset (NumberFieldPlace K))
    (houtside : ∀ P : HeightOneSpectrum
        (NumberField.RingOfIntegers K),
      (Sum.inl P : NumberFieldPlace K) ∉ S →
        Subsingleton (tateCohomologyZero
          (stageOrbitRepresentation
            (K := K) (L := L) S P)))
    (x : ∀ P : HeightOneSpectrum (NumberField.RingOfIntegers K),
      tateCohomologyZero
        (stageOrbitRepresentation
          (K := K) (L := L) S P))
    (P : {P : HeightOneSpectrum (NumberField.RingOfIntegers K) //
      (Sum.inl P : NumberFieldPlace K) ∈ S}) :
    stageTateExceptional
        (K := K) (L := L) S houtside x P =
      stageTateFull
        (K := K) (L := L) S P.1 P.2 (x P.1) := by
  change piTateExceptional
      (K := K) (L := L) S x P = _
  exact stage_tate_exceptional
    (K := K) (L := L) S x P

noncomputable def cofinalTateExceptional
    (T : Finset (NumberFieldPlace K)) :
    tateCohomologyZero
        (resizedStageRepresentation
          (K := K) (L := L) (cofinalIdeleStage K L T)) ≃+
      ExceptionalTateZero
        K L (cofinalIdeleStage K L T) :=
  (stageTatePi
    (K := K) (L := L) (cofinalIdeleStage K L T)).trans
      (stageTateExceptional
        (K := K) (L := L) (cofinalIdeleStage K L T)
        (fun P hP ↦ cofinal_tate_subsingleton
          (K := K) (L := L) T P hP))

noncomputable def cofinalExceptionalFun
    (T : Finset (NumberFieldPlace K))
    (q : tateCohomologyZero
      (resizedStageRepresentation
        (K := K) (L := L) (cofinalIdeleStage K L T))) :
    ExceptionalTateZero K L (cofinalIdeleStage K L T) :=
  piTateExceptional
    (K := K) (L := L) (cofinalIdeleStage K L T)
    (stageTatePi
      (K := K) (L := L) (cofinalIdeleStage K L T) q)

noncomputable def cofinalExceptionalHom
    (T : Finset (NumberFieldPlace K)) :
    tateCohomologyZero
        (resizedStageRepresentation
          (K := K) (L := L) (cofinalIdeleStage K L T)) →+
      ExceptionalTateZero K L (cofinalIdeleStage K L T) where
  toFun := cofinalExceptionalFun
    (K := K) (L := L) T
  map_zero' :=
    (cofinalTateExceptional
      (K := K) (L := L) T).map_zero
  map_add' :=
    (cofinalTateExceptional
      (K := K) (L := L) T).map_add

@[simp]
theorem cofinal_tate_exceptional
    (T : Finset (NumberFieldPlace K))
    (q : tateCohomologyZero
      (resizedStageRepresentation
        (K := K) (L := L) (cofinalIdeleStage K L T)))
    (P : {P : HeightOneSpectrum (NumberField.RingOfIntegers K) //
      (Sum.inl P : NumberFieldPlace K) ∈ cofinalIdeleStage K L T}) :
    cofinalTateExceptional
        (K := K) (L := L) T q P =
      cofinalExceptionalFun
        (K := K) (L := L) T q P := by
  unfold cofinalTateExceptional
  unfold cofinalExceptionalFun
  change piTateExceptional
      (K := K) (L := L) (cofinalIdeleStage K L T)
      (stageTatePi
        (K := K) (L := L) (cofinalIdeleStage K L T) q) P = _
  exact stage_tate_exceptional
    (K := K) (L := L) _ _ P

noncomputable def exceptionalTateFamily
    (S : Finset (NumberFieldPlace K)) :
    ExceptionalTateZero K L S →+
      (∀ P : {P : HeightOneSpectrum (NumberField.RingOfIntegers K) //
          P ∈ exceptionalBasePrimes (K := K) S},
        OrbitTateZero K L P.1) :=
  AddMonoidHom.mk'
    (fun x P ↦ x ⟨P.1,
      (exceptional_base_primes (K := K) S P.1).mp P.2⟩)
    (fun _ _ ↦ by funext P; simp only [Pi.add_apply])

theorem exceptional_tate_injective
    (S : Finset (NumberFieldPlace K)) :
    Function.Injective
      (exceptionalTateFamily
        (K := K) (L := L) S) := by
  intro x y hxy
  funext P
  have h := congrFun hxy ⟨P.1,
    (exceptional_base_primes (K := K) S P.1).mpr P.2⟩
  exact h

noncomputable def exceptionalDirectFun
    (S : Finset (NumberFieldPlace K)) :
    ExceptionalTateZero K L S →
      DirectSum (HeightOneSpectrum (NumberField.RingOfIntegers K))
        (OrbitTateZero K L) := fun x ↦
  DFinsupp.mk (exceptionalBasePrimes (K := K) S)
    (exceptionalTateFamily
      (K := K) (L := L) S x)

noncomputable def exceptionalDirectSum
    (S : Finset (NumberFieldPlace K)) :
    ExceptionalTateZero K L S →+
      DirectSum (HeightOneSpectrum (NumberField.RingOfIntegers K))
        (OrbitTateZero K L) where
  toFun := exceptionalDirectFun
    (K := K) (L := L) S
  map_zero' := by
    unfold exceptionalDirectFun
    apply DFinsupp.ext
    intro P
    simp
  map_add' x y := by
    unfold exceptionalDirectFun
    apply DFinsupp.ext
    intro P
    by_cases hP : P ∈ exceptionalBasePrimes (K := K) S <;>
      simp [DFinsupp.mk_apply, hP]

@[simp]
theorem resized_direct_sum
    (S : Finset (NumberFieldPlace K))
    (x : ExceptionalTateZero K L S)
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hP : (Sum.inl P : NumberFieldPlace K) ∈ S) :
    exceptionalDirectSum
      (K := K) (L := L) S x P = x ⟨P, hP⟩ := by
  change DFinsupp.mk (exceptionalBasePrimes (K := K) S)
      (exceptionalTateFamily
        (K := K) (L := L) S x) P = x ⟨P, hP⟩
  rw [DFinsupp.mk_of_mem
    ((exceptional_base_primes (K := K) S P).mpr hP)]
  rfl

@[simp]
theorem exceptional_direct_not
    (S : Finset (NumberFieldPlace K))
    (x : ExceptionalTateZero K L S)
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hP : (Sum.inl P : NumberFieldPlace K) ∉ S) :
    exceptionalDirectSum
      (K := K) (L := L) S x P = 0 := by
  change DFinsupp.mk (exceptionalBasePrimes (K := K) S)
      (exceptionalTateFamily
        (K := K) (L := L) S x) P = 0
  rw [DFinsupp.mk_apply]
  simp only [dif_neg (fun h ↦
    hP ((exceptional_base_primes (K := K) S P).mp h))]

@[simp]
theorem resized_exceptional_fun
    (S : Finset (NumberFieldPlace K))
    (x : ExceptionalTateZero K L S)
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hP : (Sum.inl P : NumberFieldPlace K) ∈ S) :
    exceptionalDirectFun
      (K := K) (L := L) S x P = x ⟨P, hP⟩ :=
  resized_direct_sum
    (K := K) (L := L) S x P hP

@[simp]
theorem exceptional_direct_fun
    (S : Finset (NumberFieldPlace K))
    (x : ExceptionalTateZero K L S)
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hP : (Sum.inl P : NumberFieldPlace K) ∉ S) :
    exceptionalDirectFun
      (K := K) (L := L) S x P = 0 :=
  exceptional_direct_not
    (K := K) (L := L) S x P hP

theorem resized_exceptional_injective
    (S : Finset (NumberFieldPlace K)) :
    Function.Injective
      (exceptionalDirectSum
        (K := K) (L := L) S) := by
  intro x y hxy
  funext P
  have h := congrArg
    (fun z : DirectSum (HeightOneSpectrum (NumberField.RingOfIntegers K))
      (OrbitTateZero K L) ↦ z P.1) hxy
  change DFinsupp.mk (exceptionalBasePrimes (K := K) S)
      (exceptionalTateFamily
        (K := K) (L := L) S x) P.1 =
    DFinsupp.mk (exceptionalBasePrimes (K := K) S)
      (exceptionalTateFamily
        (K := K) (L := L) S y) P.1 at h
  rw [DFinsupp.mk_of_mem
      ((exceptional_base_primes (K := K) S P.1).mpr P.2),
    DFinsupp.mk_of_mem
      ((exceptional_base_primes (K := K) S P.1).mpr P.2)] at h
  exact h

theorem exceptional_tate_preimage
    (y : DirectSum (HeightOneSpectrum (NumberField.RingOfIntegers K))
      (OrbitTateZero K L)) :
    ∃ (S : Finset (NumberFieldPlace K))
      (x : ExceptionalTateZero K L S),
      exceptionalDirectSum
        (K := K) (L := L) S x = y := by
  classical
  let S : Finset (NumberFieldPlace K) :=
    y.support.image (fun P ↦ (Sum.inl P : NumberFieldPlace K))
  have hmem (P : HeightOneSpectrum (NumberField.RingOfIntegers K)) :
      (Sum.inl P : NumberFieldPlace K) ∈ S ↔ P ∈ y.support := by
    simp only [S, Finset.mem_image]
    constructor
    · rintro ⟨Q, hQ, hQP⟩
      exact Sum.inl_injective hQP |>.symm ▸ hQ
    · exact fun hP ↦ ⟨P, hP, rfl⟩
  let x : ExceptionalTateZero K L S := fun P ↦ y P.1
  refine ⟨S, x, ?_⟩
  apply DirectSum.ext
  intro P
  by_cases hP : P ∈ y.support
  · rw [resized_direct_sum
      (K := K) (L := L) S x P ((hmem P).mpr hP)]
  · rw [exceptional_direct_not
      (K := K) (L := L) S x P (fun h ↦ hP ((hmem P).mp h))]
    exact (DFinsupp.notMem_support_iff.mp hP).symm

noncomputable def resizedExceptionalFun
    {S T : Finset (NumberFieldPlace K)} (_hST : S ⊆ T) :
    ExceptionalTateZero K L S →
      ExceptionalTateZero K L T := fun x P ↦
  if hP : (Sum.inl P.1 : NumberFieldPlace K) ∈ S then
    x ⟨P.1, hP⟩ else 0

noncomputable def resizedExceptionalTate
    {S T : Finset (NumberFieldPlace K)} (hST : S ⊆ T) :
    ExceptionalTateZero K L S →+
      ExceptionalTateZero K L T :=
  AddMonoidHom.mk'
    (resizedExceptionalFun
      (K := K) (L := L) hST)
    (fun x y ↦ by
      funext P
      unfold resizedExceptionalFun
      by_cases hP : (Sum.inl P.1 : NumberFieldPlace K) ∈ S <;>
        simp [hP])

@[simp]
theorem exceptional_transition_fun
    {S T : Finset (NumberFieldPlace K)} (hST : S ⊆ T)
    (x : ExceptionalTateZero K L S) :
    resizedExceptionalTate
        (K := K) (L := L) hST x =
      resizedExceptionalFun
        (K := K) (L := L) hST x := rfl

@[simp]
theorem exceptional_tate_transition
    {S T : Finset (NumberFieldPlace K)} (hST : S ⊆ T)
    (x : ExceptionalTateZero K L S)
    (P : {P : HeightOneSpectrum (NumberField.RingOfIntegers K) //
      (Sum.inl P : NumberFieldPlace K) ∈ T})
    (hP : (Sum.inl P.1 : NumberFieldPlace K) ∈ S) :
    resizedExceptionalTate
      (K := K) (L := L) hST x P = x ⟨P.1, hP⟩ := by
  change resizedExceptionalFun
      (K := K) (L := L) hST x P = _
  unfold resizedExceptionalFun
  simp only [dif_pos hP]

@[simp]
theorem resized_exceptional_tate
    {S T : Finset (NumberFieldPlace K)} (hST : S ⊆ T)
    (x : ExceptionalTateZero K L S)
    (P : {P : HeightOneSpectrum (NumberField.RingOfIntegers K) //
      (Sum.inl P : NumberFieldPlace K) ∈ T})
    (hP : (Sum.inl P.1 : NumberFieldPlace K) ∉ S) :
    resizedExceptionalTate
      (K := K) (L := L) hST x P = 0 := by
  change resizedExceptionalFun
      (K := K) (L := L) hST x P = _
  unfold resizedExceptionalFun
  simp only [dif_neg hP]

theorem resized_direct_transition
    {S T : Finset (NumberFieldPlace K)} (hST : S ⊆ T)
    (x : ExceptionalTateZero K L S) :
    exceptionalDirectSum
        (K := K) (L := L) T
        (resizedExceptionalTate
          (K := K) (L := L) hST x) =
      exceptionalDirectSum
        (K := K) (L := L) S x := by
  apply DirectSum.ext
  intro P
  by_cases hPS : (Sum.inl P : NumberFieldPlace K) ∈ S
  · have hPT := hST hPS
    rw [resized_direct_sum
      (K := K) (L := L) T _ P hPT,
      exceptional_tate_transition
        (K := K) (L := L) hST _ ⟨P, hPT⟩ hPS,
      resized_direct_sum
        (K := K) (L := L) S x P hPS]
  · rw [exceptional_direct_not
      (K := K) (L := L) S x P hPS]
    by_cases hPT : (Sum.inl P : NumberFieldPlace K) ∈ T
    · rw [resized_direct_sum
        (K := K) (L := L) T _ P hPT,
        resized_exceptional_tate
          (K := K) (L := L) hST _ ⟨P, hPT⟩ hPS]
    · rw [exceptional_direct_not
        (K := K) (L := L) T _ P hPT]

/-! ## Tate degree zero as the finite-stage direct limit -/

noncomputable def resizedPlacesTransition
    {S T : Finset (NumberFieldPlace K)} (hST : S ⊆ T) :
    tateCohomologyZero
        (resizedPlacesRepresentation (K := K) (L := L) S) →ₗ[ULift.{u} ℤ]
      tateCohomologyZero
        (resizedPlacesRepresentation (K := K) (L := L) T) :=
  tateCohomology
    (resizedIdeles (K := K) (L := L) hST)

noncomputable def resizedIdelesInclusion
    (S : Finset (NumberFieldPlace K)) :
    tateCohomologyZero
        (resizedPlacesRepresentation (K := K) (L := L) S) →ₗ[ULift.{u} ℤ]
      tateCohomologyZero (resizedConcreteRepresentation K L) :=
  tateCohomology
    (resizedInclusion (K := K) (L := L) S)

theorem ideles_places_preimage
    (q : tateCohomologyZero (resizedConcreteRepresentation K L)) :
    ∃ (S : Finset (NumberFieldPlace K))
      (qS : tateCohomologyZero
        (resizedPlacesRepresentation (K := K) (L := L) S)),
      resizedIdelesInclusion
        (K := K) (L := L) S qS = q := by
  classical
  obtain ⟨z, rfl⟩ := tate_projection_surjective
    (resizedConcreteRepresentation K L) q
  let g₀ : Fin 0 → Gal(L/K) := fun i ↦ Fin.elim0 i
  obtain ⟨S, hzS⟩ := ideles_idele_cochain
    (K := K) (L := L) 0 (fun _ ↦ z.1)
  let xS : resizedPlacesRepresentation (K := K) (L := L) S :=
    resizedIdeleCochain S 0 (fun _ ↦ z.1) hzS g₀
  have hxS (g : Gal(L/K)) :
      (resizedPlacesRepresentation
        (K := K) (L := L) S).ρ g xS = xS := by
    apply resized_inclusion_injective (K := K) (L := L) S
    let inc := resizedInclusion (K := K) (L := L) S
    calc
      inc.hom ((resizedPlacesRepresentation
          (K := K) (L := L) S).ρ g xS) =
          (resizedConcreteRepresentation K L).ρ g (inc.hom xS) :=
        Rep.hom_comm_apply inc g xS
      _ = (resizedConcreteRepresentation K L).ρ g z.1 := by rfl
      _ = z.1 := z.2 g
      _ = inc.hom xS := by rfl
  refine ⟨S, Submodule.Quotient.mk ⟨xS, hxS⟩, ?_⟩
  unfold resizedIdelesInclusion
  change tateCohomology
      (resizedInclusion (K := K) (L := L) S)
      (Submodule.Quotient.mk ⟨xS, hxS⟩) =
    tateCohomologyProjection (resizedConcreteRepresentation K L) z
  rw [tate_cohomology_mk]
  unfold tateCohomologyProjection
  rw [Submodule.mkQ_apply]
  congr 1

set_option maxHeartbeats 2000000 in
-- Extracting a common finite support for a norm witness unfolds the full
-- resized idèle representation and its quotient maps.
theorem ideles_places_tate
    (S : Finset (NumberFieldPlace K))
    (qS : tateCohomologyZero
      (resizedPlacesRepresentation (K := K) (L := L) S))
    (hq : resizedIdelesInclusion
      (K := K) (L := L) S qS = 0) :
    ∃ (T : Finset (NumberFieldPlace K)) (hST : S ⊆ T),
      resizedPlacesTransition
        (K := K) (L := L) hST qS = 0 := by
  classical
  let AS := resizedPlacesRepresentation (K := K) (L := L) S
  let A := resizedConcreteRepresentation K L
  let incS := resizedInclusion (K := K) (L := L) S
  obtain ⟨zS, rfl⟩ := tate_projection_surjective AS qS
  have hnorm : (((Rep.invariantsFunctor (ULift.{u} ℤ) Gal(L/K)).map incS).hom zS) ∈
      LinearMap.range (Shifting.normCoinvariantsInvariants A) := by
    apply (Submodule.Quotient.mk_eq_zero
      (LinearMap.range (Shifting.normCoinvariantsInvariants A))).1
    unfold resizedIdelesInclusion at hq
    unfold tateCohomologyProjection at hq
    rw [Submodule.mkQ_apply] at hq
    change tateCohomology incS (Submodule.Quotient.mk zS) = 0 at hq
    rw [tate_cohomology_mk] at hq
    exact hq
  obtain ⟨y, hy⟩ :=
    (tate_range_raw A _).1 hnorm
  let g₀ : Fin 0 → Gal(L/K) := fun i ↦ Fin.elim0 i
  obtain ⟨T₀, hyT₀⟩ := ideles_idele_cochain
    (K := K) (L := L) 0 (fun _ ↦ y)
  let T := S ∪ T₀
  have hST : S ⊆ T := Finset.subset_union_left
  have hT₀T : T₀ ⊆ T := Finset.subset_union_right
  have hyT : ∀ g, ((fun _ ↦ y) g).toMul ∈
      idelesAtPlaces (K := K) (L := L) T := fun g ↦
    ideles_places_mono (K := K) (L := L) hT₀T (hyT₀ g)
  let AT := resizedPlacesRepresentation (K := K) (L := L) T
  let incT := resizedInclusion (K := K) (L := L) T
  let trans := resizedIdeles (K := K) (L := L) hST
  let yT : AT := resizedIdeleCochain T 0 (fun _ ↦ y) hyT g₀
  let zT : AT.ρ.invariants :=
    ((Rep.invariantsFunctor (ULift.{u} ℤ) Gal(L/K)).map trans).hom zS
  have hnormT : ⟨AT.ρ.norm yT,
      fun g ↦ AT.ρ.self_norm_apply g yT⟩ = zT := by
    apply Subtype.ext
    apply resized_inclusion_injective (K := K) (L := L) T
    calc
      incT.hom (AT.ρ.norm yT) = A.ρ.norm (incT.hom yT) := by
        exact (congrArg (fun f : AT ⟶ A ↦ f.hom yT)
          (Rep.norm_comm incT)).symm
      _ = A.ρ.norm y := by rfl
      _ = (((Rep.invariantsFunctor (ULift.{u} ℤ) Gal(L/K)).map incS).hom zS).1 :=
        congrArg Subtype.val hy
      _ = incT.hom zT.1 := by rfl
  refine ⟨T, hST, ?_⟩
  unfold resizedPlacesTransition
  unfold tateCohomologyProjection
  rw [Submodule.mkQ_apply]
  change tateCohomology trans (Submodule.Quotient.mk zS) = 0
  rw [tate_cohomology_mk]
  apply (Submodule.Quotient.mk_eq_zero
    (LinearMap.range (Shifting.normCoinvariantsInvariants AT))).2
  exact (tate_range_raw AT zT).2 ⟨yT, hnormT⟩

theorem resized_ideles_self
    (S : Finset (NumberFieldPlace K))
    (q : tateCohomologyZero
      (resizedPlacesRepresentation (K := K) (L := L) S)) :
    resizedPlacesTransition (K := K) (L := L)
      (show S ⊆ S from fun _ h ↦ h) q = q := by
  have htransition :
      resizedIdeles (K := K) (L := L)
          (show S ⊆ S from fun _ h ↦ h) =
        𝟙 (resizedPlacesRepresentation
          (K := K) (L := L) S) := by
    ext x
    rfl
  unfold resizedPlacesTransition
  rw [htransition]
  exact tate_cohomology_id _ q

theorem resized_ideles_comp
    {S T U : Finset (NumberFieldPlace K)}
    (hST : S ⊆ T) (hTU : T ⊆ U)
    (q : tateCohomologyZero
      (resizedPlacesRepresentation (K := K) (L := L) S)) :
    resizedPlacesTransition (K := K) (L := L) hTU
        (resizedPlacesTransition
          (K := K) (L := L) hST q) =
      resizedPlacesTransition (K := K) (L := L)
        (hST.trans hTU) q := by
  have htransition :
      resizedIdeles (K := K) (L := L) hST ≫
          resizedIdeles (K := K) (L := L) hTU =
        resizedIdeles (K := K) (L := L)
          (hST.trans hTU) := by
    ext x
    rfl
  unfold resizedPlacesTransition
  rw [← htransition]
  exact (tate_cohomology_comp _ _ q).symm

noncomputable instance resizedDirectedSystem :
    DirectedSystem
      (fun S : Finset (NumberFieldPlace K) ↦ tateCohomologyZero
        (resizedPlacesRepresentation (K := K) (L := L) S))
      (fun {_ _} h ↦ resizedPlacesTransition
        (K := K) (L := L) h) where
  map_self := resized_ideles_self
    (K := K) (L := L)
  map_map := by
    intro k j i hij hjk x
    exact resized_ideles_comp
      (K := K) (L := L) hij hjk x

abbrev ResizedIdelesLimit
    (K L : Type u) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] :=
  DirectLimit
    (fun S : Finset (NumberFieldPlace K) ↦ tateCohomologyZero
      (resizedPlacesRepresentation (K := K) (L := L) S))
    (fun _ _ h ↦ resizedPlacesTransition
      (K := K) (L := L) h)

theorem resized_places_inclusion
    {S T : Finset (NumberFieldPlace K)} (hST : S ⊆ T)
    (q : tateCohomologyZero
      (resizedPlacesRepresentation (K := K) (L := L) S)) :
    resizedIdelesInclusion (K := K) (L := L) T
        (resizedPlacesTransition
          (K := K) (L := L) hST q) =
      resizedIdelesInclusion (K := K) (L := L) S q := by
  have hinclusion :
      resizedIdeles (K := K) (L := L) hST ≫
          resizedInclusion (K := K) (L := L) T =
        resizedInclusion (K := K) (L := L) S := by
    ext y
    rfl
  unfold resizedIdelesInclusion
  unfold resizedPlacesTransition
  rw [← hinclusion]
  exact (tate_cohomology_comp _ _ q).symm

set_option maxHeartbeats 1000000 in
-- The direct-limit lift compares proof-dependent transition maps between
-- large resized representation quotients.
noncomputable def resizedIdelesConcrete :
    ResizedIdelesLimit K L →+
      tateCohomologyZero (resizedConcreteRepresentation K L) where
  toFun := DirectLimit.lift
    (ι := Finset (NumberFieldPlace K))
    (F := fun S : Finset (NumberFieldPlace K) ↦ tateCohomologyZero
      (resizedPlacesRepresentation (K := K) (L := L) S))
    (fun _ _ h ↦ resizedPlacesTransition
      (K := K) (L := L) h)
    (fun S q ↦ resizedIdelesInclusion
      (K := K) (L := L) S q)
    (fun S T h q ↦
      (resized_places_inclusion
        (K := K) (L := L) h q).symm)
  map_zero' := by
    rw [DirectLimit.zero_def (∅ : Finset (NumberFieldPlace K)),
      DirectLimit.lift_def]
    exact map_zero _
  map_add' q q' := by
    induction q, q' using DirectLimit.induction₂ with
    | _ S x y =>
      rw [DirectLimit.add_def, DirectLimit.lift_def,
        DirectLimit.lift_def, DirectLimit.lift_def]
      exact map_add _ x y

theorem ideles_limit_surjective :
    Function.Surjective
      (resizedIdelesConcrete
        (K := K) (L := L)) := by
  intro q
  obtain ⟨S, qS, hqS⟩ :=
    ideles_places_preimage (K := K) (L := L) q
  refine ⟨(⟦⟨S, qS⟩⟧ : ResizedIdelesLimit K L), ?_⟩
  change resizedIdelesInclusion
    (K := K) (L := L) S qS = q
  exact hqS

theorem resized_places_limit :
    Function.Injective
      (resizedIdelesConcrete
        (K := K) (L := L)) := by
  intro q q' hqq'
  apply sub_eq_zero.mp
  have hzero : resizedIdelesConcrete
      (K := K) (L := L) (q - q') = 0 := by
    rw [map_sub, hqq', sub_self]
  let F : Finset (NumberFieldPlace K) → Type u :=
    fun S ↦ tateCohomologyZero
      (resizedPlacesRepresentation (K := K) (L := L) S)
  let f := fun (S T : Finset (NumberFieldPlace K)) (h : S ⊆ T) ↦
    resizedPlacesTransition (K := K) (L := L) h
  obtain ⟨S, qS, hq⟩ := DirectLimit.exists_eq_mk f (q - q')
  rw [hq] at hzero ⊢
  have hstage : resizedIdelesInclusion
      (K := K) (L := L) S qS = 0 := by
    exact hzero
  obtain ⟨T, hST, hT⟩ :=
    ideles_places_tate
      (K := K) (L := L) S qS hstage
  change f S T hST qS = 0 at hT
  calc
    (⟦⟨S, qS⟩⟧ : DirectLimit F f) =
        ⟦⟨T, f S T hST qS⟩⟧ :=
      DirectLimit.eq_of_le (f := f) ⟨S, qS⟩ T hST
    _ = ⟦⟨T, 0⟩⟧ := congrArg
      (fun z ↦ (⟦⟨T, z⟩⟧ : DirectLimit F f)) hT
    _ = 0 := (DirectLimit.zero_def T).symm

noncomputable def resizedIdelesTate :
    ResizedIdelesLimit K L ≃+
      tateCohomologyZero (resizedConcreteRepresentation K L) :=
  AddEquiv.ofBijective
    (resizedIdelesConcrete (K := K) (L := L))
    ⟨resized_places_limit
      (K := K) (L := L),
     ideles_limit_surjective
      (K := K) (L := L)⟩

/-! ## Naturality of the stage decomposition -/

theorem resized_places_fst
    (S : Finset (NumberFieldPlace K))
    (q : tateCohomologyZero
      (resizedPlacesRepresentation (K := K) (L := L) S)) :
    (resizedIdelesInfinite
      (K := K) (L := L) S q).1 =
      tateCohomology
        ((resizedRepresentationIso
          (K := K) (L := L) S).hom ≫
            resizedPlacesInfinite
              (K := K) (L := L) S) q := by
  let A := resizedInfiniteRepresentation K L
  let B := resizedStageRepresentation (K := K) (L := L) S
  let e : resizedPlacesRepresentation
      (K := K) (L := L) S ≅ A ⨯ B :=
    (resizedRepresentationIso
      (K := K) (L := L) S).trans
      (resizedIsoCategorical
        (K := K) (L := L) S)
  change tateCohomology (Limits.prod.fst : A ⨯ B ⟶ A)
      (tateAddIso e q) = _
  rw [tate_cohomology_iso,
    ← tate_cohomology_comp]
  have hproj : e.hom ≫ (Limits.prod.fst : A ⨯ B ⟶ A) =
      (resizedRepresentationIso
        (K := K) (L := L) S).hom ≫
          resizedPlacesInfinite
            (K := K) (L := L) S := by
    rw [show e.hom =
      (resizedRepresentationIso
        (K := K) (L := L) S).hom ≫
        (resizedIsoCategorical
          (K := K) (L := L) S).hom from rfl,
    Category.assoc,
    iso_categorical_fst]
  rw [hproj]

theorem resized_places_snd
    (S : Finset (NumberFieldPlace K))
    (q : tateCohomologyZero
      (resizedPlacesRepresentation (K := K) (L := L) S)) :
    (resizedIdelesInfinite
      (K := K) (L := L) S q).2 =
      tateCohomology
        ((resizedRepresentationIso
          (K := K) (L := L) S).hom ≫
            resizedIdelesFinite
              (K := K) (L := L) S) q := by
  let A := resizedInfiniteRepresentation K L
  let B := resizedStageRepresentation (K := K) (L := L) S
  let e : resizedPlacesRepresentation
      (K := K) (L := L) S ≅ A ⨯ B :=
    (resizedRepresentationIso
      (K := K) (L := L) S).trans
      (resizedIsoCategorical
        (K := K) (L := L) S)
  change tateCohomology (Limits.prod.snd : A ⨯ B ⟶ B)
      (tateAddIso e q) = _
  rw [tate_cohomology_iso,
    ← tate_cohomology_comp]
  have hproj : e.hom ≫ (Limits.prod.snd : A ⨯ B ⟶ B) =
      (resizedRepresentationIso
        (K := K) (L := L) S).hom ≫
          resizedIdelesFinite
            (K := K) (L := L) S := by
    rw [show e.hom =
      (resizedRepresentationIso
        (K := K) (L := L) S).hom ≫
        (resizedIsoCategorical
          (K := K) (L := L) S).hom from rfl,
    Category.assoc,
    iso_categorical_snd]
  rw [hproj]

noncomputable def resizedStageTransition
    {S T : Finset (NumberFieldPlace K)} (hST : S ⊆ T) :
    tateCohomologyZero
        (resizedStageRepresentation
          (K := K) (L := L) S) →ₗ[ULift.{u} ℤ]
      tateCohomologyZero
        (resizedStageRepresentation
          (K := K) (L := L) T) :=
  tateCohomology
    (ideleStageTransition
      (K := K) (L := L) hST)

theorem stage_pi_transition
    {S T : Finset (NumberFieldPlace K)} (hST : S ⊆ T)
    (q : tateCohomologyZero
      (resizedStageRepresentation
        (K := K) (L := L) S))
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    stageTatePi
        (K := K) (L := L) T
        (resizedStageTransition
          (K := K) (L := L) hST q) P =
      tateCohomology
        (stageOrbitTransition
          (K := K) (L := L) hST P)
        (stageTatePi
          (K := K) (L := L) S q P) := by
  rw [resized_stage_pi,
    resized_stage_pi]
  unfold resizedStageTransition
  calc
    tateCohomology
        (resizedStageEvaluation
          (K := K) (L := L) T P)
        (tateCohomology
          (ideleStageTransition
            (K := K) (L := L) hST) q) =
      tateCohomology
        (ideleStageTransition
            (K := K) (L := L) hST ≫
          resizedStageEvaluation
            (K := K) (L := L) T P) q :=
      (tate_cohomology_comp _ _ q).symm
    _ = tateCohomology
        (resizedStageEvaluation
            (K := K) (L := L) S P ≫
          stageOrbitTransition
            (K := K) (L := L) hST P) q := by
      rw [resized_stage_evaluation]
    _ = _ := tate_cohomology_comp _ _ q

theorem resized_places_transition
    {S T : Finset (NumberFieldPlace K)} (hST : S ⊆ T)
    (q : tateCohomologyZero
      (resizedPlacesRepresentation (K := K) (L := L) S)) :
    resizedIdelesInfinite
        (K := K) (L := L) T
        (resizedPlacesTransition
          (K := K) (L := L) hST q) =
      ((resizedIdelesInfinite
          (K := K) (L := L) S q).1,
       resizedStageTransition
          (K := K) (L := L) hST
          (resizedIdelesInfinite
            (K := K) (L := L) S q).2) := by
  apply Prod.ext
  · rw [resized_places_fst,
      resized_places_fst]
    let pS := (resizedRepresentationIso
      (K := K) (L := L) S).hom ≫
        resizedPlacesInfinite (K := K) (L := L) S
    let pT := (resizedRepresentationIso
      (K := K) (L := L) T).hom ≫
        resizedPlacesInfinite (K := K) (L := L) T
    have hsquare : resizedIdeles
        (K := K) (L := L) hST ≫ pT = pS := by
      apply Rep.hom_ext
      apply Representation.IntertwiningMap.ext
      apply LinearMap.ext
      intro x
      rfl
    unfold resizedPlacesTransition
    change tateCohomology pT
      (tateCohomology
        (resizedIdeles (K := K) (L := L) hST) q) =
      tateCohomology pS q
    calc
      _ = tateCohomology
          (resizedIdeles (K := K) (L := L) hST ≫ pT) q :=
        (tate_cohomology_comp _ _ q).symm
      _ = tateCohomology pS q := by rw [hsquare]
  · rw [resized_places_snd,
      resized_places_snd]
    let pS := (resizedRepresentationIso
      (K := K) (L := L) S).hom ≫
        resizedIdelesFinite (K := K) (L := L) S
    let pT := (resizedRepresentationIso
      (K := K) (L := L) T).hom ≫
        resizedIdelesFinite (K := K) (L := L) T
    let f := ideleStageTransition
      (K := K) (L := L) hST
    have hsquare : resizedIdeles
        (K := K) (L := L) hST ≫ pT = pS ≫ f := by
      apply Rep.hom_ext
      apply Representation.IntertwiningMap.ext
      apply LinearMap.ext
      intro x
      apply Additive.toMul.injective
      funext P
      apply Subtype.ext
      rfl
    unfold resizedPlacesTransition
    unfold resizedStageTransition
    change tateCohomology pT
      (tateCohomology
        (resizedIdeles (K := K) (L := L) hST) q) =
      tateCohomology f (tateCohomology pS q)
    calc
      _ = tateCohomology
          (resizedIdeles (K := K) (L := L) hST ≫ pT) q :=
        (tate_cohomology_comp _ _ q).symm
      _ = tateCohomology (pS ≫ f) q := by rw [hsquare]
      _ = _ := tate_cohomology_comp _ _ q

theorem stage_full_transition
    {S T : Finset (NumberFieldPlace K)} (hST : S ⊆ T)
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hPS : (Sum.inl P : NumberFieldPlace K) ∈ S)
    (q : tateCohomologyZero
      (stageOrbitRepresentation
        (K := K) (L := L) S P)) :
    stageTateFull
        (K := K) (L := L) T P (hST hPS)
        (tateCohomology
          (stageOrbitTransition
            (K := K) (L := L) hST P) q) =
      stageTateFull
        (K := K) (L := L) S P hPS q := by
  let trans := stageOrbitTransition
    (K := K) (L := L) hST P
  let eT := stageIsoFull
    (K := K) (L := L) T P (hST hPS)
  let eS := stageIsoFull
    (K := K) (L := L) S P hPS
  change (completionOrbitTate
      (K := K) (L := L) P).symm
        (tateAddIso eT (tateCohomology trans q)) =
    (completionOrbitTate
      (K := K) (L := L) P).symm (tateAddIso eS q)
  apply (completionOrbitTate
    (K := K) (L := L) P).injective
  simp only [AddEquiv.apply_symm_apply]
  rw [tate_cohomology_iso, tate_cohomology_iso]
  have hsquare : trans ≫ eT.hom = eS.hom := by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro x
    apply Additive.toMul.injective
    rfl
  calc
    tateCohomology eT.hom (tateCohomology trans q) =
        tateCohomology (trans ≫ eT.hom) q :=
      (tate_cohomology_comp _ _ q).symm
    _ = tateCohomology eS.hom q := by rw [hsquare]

theorem cofinal_stage_transition
    {T U : Finset (NumberFieldPlace K)} (hTU : T ⊆ U)
    (q : tateCohomologyZero
      (resizedStageRepresentation
        (K := K) (L := L) (cofinalIdeleStage K L T)))
    (P : {P : HeightOneSpectrum (NumberField.RingOfIntegers K) //
      (Sum.inl P : NumberFieldPlace K) ∈ cofinalIdeleStage K L U}) :
    cofinalExceptionalFun
        (K := K) (L := L) U
        (resizedStageTransition
          (K := K) (L := L)
          (cofinal_stage_mono (K := K) (L := L) hTU) q) P =
      if hPT : (Sum.inl P.1 : NumberFieldPlace K) ∈
          cofinalIdeleStage K L T then
        cofinalExceptionalFun
          (K := K) (L := L) T q ⟨P.1, hPT⟩
      else 0 := by
  let hStage := cofinal_stage_mono (K := K) (L := L) hTU
  by_cases hPT : (Sum.inl P.1 : NumberFieldPlace K) ∈
      cofinalIdeleStage K L T
  · simp only [dif_pos hPT]
    unfold cofinalExceptionalFun
    rw [stage_tate_exceptional,
      stage_pi_transition
        (K := K) (L := L) hStage q P.1,
      stage_tate_exceptional]
    simpa only using
      (stage_full_transition
        (K := K) (L := L) hStage P.1 hPT
        (stageTatePi
          (K := K) (L := L) (cofinalIdeleStage K L T) q P.1))
  · simp only [dif_neg hPT]
    unfold cofinalExceptionalFun
    rw [stage_tate_exceptional,
      stage_pi_transition
        (K := K) (L := L) hStage q P.1]
    letI := cofinal_tate_subsingleton
      (K := K) (L := L) T P.1 hPT
    have hzero : stageTatePi
        (K := K) (L := L) (cofinalIdeleStage K L T) q P.1 = 0 :=
      Subsingleton.elim _ _
    let trans := stageOrbitTransition
      (K := K) (L := L) hStage P.1
    calc
      stageTateFull
          (K := K) (L := L) (cofinalIdeleStage K L U) P.1 P.2
          (tateCohomology trans
            (stageTatePi
              (K := K) (L := L) (cofinalIdeleStage K L T) q P.1)) =
        stageTateFull
          (K := K) (L := L) (cofinalIdeleStage K L U) P.1 P.2
          (tateCohomology trans 0) := by rw [hzero]
      _ = stageTateFull
          (K := K) (L := L) (cofinalIdeleStage K L U) P.1 P.2 0 := by
        rw [(tateCohomology trans).map_zero]
      _ = 0 := (stageTateFull
        (K := K) (L := L) (cofinalIdeleStage K L U) P.1 P.2).map_zero

theorem cofinal_stage_direct
    {T U : Finset (NumberFieldPlace K)} (hTU : T ⊆ U)
    (q : tateCohomologyZero
      (resizedStageRepresentation
        (K := K) (L := L) (cofinalIdeleStage K L T)))
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    exceptionalDirectFun
        (K := K) (L := L) (cofinalIdeleStage K L U)
        (cofinalExceptionalFun
          (K := K) (L := L) U
          (resizedStageTransition
            (K := K) (L := L)
            (cofinal_stage_mono (K := K) (L := L) hTU) q)) P =
      exceptionalDirectFun
        (K := K) (L := L) (cofinalIdeleStage K L T)
        (cofinalExceptionalFun
          (K := K) (L := L) T q) P := by
  let hStage := cofinal_stage_mono (K := K) (L := L) hTU
  by_cases hPT : (Sum.inl P : NumberFieldPlace K) ∈
      cofinalIdeleStage K L T
  · have hPU := hStage hPT
    rw [resized_exceptional_fun
        (K := K) (L := L) (cofinalIdeleStage K L U) _ P hPU,
      resized_exceptional_fun
        (K := K) (L := L) (cofinalIdeleStage K L T) _ P hPT,
      cofinal_stage_transition
        (K := K) (L := L) hTU q ⟨P, hPU⟩]
    simp only [dif_pos hPT]
  · rw [exceptional_direct_fun
        (K := K) (L := L) (cofinalIdeleStage K L T) _ P hPT]
    by_cases hPU : (Sum.inl P : NumberFieldPlace K) ∈
        cofinalIdeleStage K L U
    · rw [resized_exceptional_fun
          (K := K) (L := L) (cofinalIdeleStage K L U) _ P hPU,
        cofinal_stage_transition
          (K := K) (L := L) hTU q ⟨P, hPU⟩]
      simp only [dif_neg hPT]
    · rw [exceptional_direct_fun
        (K := K) (L := L) (cofinalIdeleStage K L U) _ P hPU]

/-! ## Passing the stage calculation to the direct limit -/

abbrev ResizedTateSplit
    (K L : Type u) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] :=
  DirectSum (InfinitePlace K) (fun v ↦ tateCohomologyZero
      (resizedPlaceRepresentation
        (K := K) (L := L) (.inr v))) ×
    DirectSum (HeightOneSpectrum (NumberField.RingOfIntegers K))
      (OrbitTateZero K L)

noncomputable def cofinalPlacesSplit
    (T : Finset (NumberFieldPlace K)) :
    tateCohomologyZero
        (resizedPlacesRepresentation
          (K := K) (L := L) (cofinalIdeleStage K L T)) →+
      ResizedTateSplit K L := by
  let split := resizedIdelesInfinite
    (K := K) (L := L) (cofinalIdeleStage K L T)
  let infinite :=
    (resizedIdelesDirect
      (K := K) (L := L)).toAddMonoidHom
  let finite := (exceptionalDirectSum
      (K := K) (L := L) (cofinalIdeleStage K L T)).comp
    (cofinalExceptionalHom
      (K := K) (L := L) T)
  exact (infinite.prodMap finite).comp split.toAddMonoidHom

@[simp]
theorem cofinal_ideles_fst
    (T : Finset (NumberFieldPlace K))
    (q : tateCohomologyZero
      (resizedPlacesRepresentation
        (K := K) (L := L) (cofinalIdeleStage K L T))) :
    (cofinalPlacesSplit
      (K := K) (L := L) T q).1 =
      resizedIdelesDirect
        (K := K) (L := L)
        (resizedIdelesInfinite
          (K := K) (L := L) (cofinalIdeleStage K L T) q).1 := rfl

@[simp]
theorem cofinal_ideles_snd
    (T : Finset (NumberFieldPlace K))
    (q : tateCohomologyZero
      (resizedPlacesRepresentation
        (K := K) (L := L) (cofinalIdeleStage K L T))) :
    (cofinalPlacesSplit
      (K := K) (L := L) T q).2 =
      exceptionalDirectFun
        (K := K) (L := L) (cofinalIdeleStage K L T)
        (cofinalExceptionalFun
          (K := K) (L := L) T
          (resizedIdelesInfinite
            (K := K) (L := L) (cofinalIdeleStage K L T) q).2) := rfl

theorem cofinal_ideles_injective
    (T : Finset (NumberFieldPlace K)) :
    Function.Injective
      (cofinalPlacesSplit
        (K := K) (L := L) T) := by
  intro q q' hqq'
  apply (resizedIdelesInfinite
    (K := K) (L := L) (cofinalIdeleStage K L T)).injective
  apply Prod.ext
  · apply (resizedIdelesDirect
      (K := K) (L := L)).injective
    exact congrArg Prod.fst hqq'
  · have hfun := resized_exceptional_injective
      (K := K) (L := L) (cofinalIdeleStage K L T)
      (congrArg Prod.snd hqq')
    apply (cofinalTateExceptional
      (K := K) (L := L) T).injective
    funext P
    rw [cofinal_tate_exceptional,
      cofinal_tate_exceptional]
    exact congrFun hfun P

theorem cofinal_split_transition
    {T U : Finset (NumberFieldPlace K)} (hTU : T ⊆ U)
    (q : tateCohomologyZero
      (resizedPlacesRepresentation
        (K := K) (L := L) (cofinalIdeleStage K L T))) :
    cofinalPlacesSplit
        (K := K) (L := L) U
        (resizedPlacesTransition
          (K := K) (L := L)
          (cofinal_stage_mono (K := K) (L := L) hTU) q) =
      cofinalPlacesSplit
        (K := K) (L := L) T q := by
  let hStage := cofinal_stage_mono (K := K) (L := L) hTU
  have hsplit :=
    resized_places_transition
      (K := K) (L := L) hStage q
  change
    (resizedIdelesDirect
        (K := K) (L := L)
        (resizedIdelesInfinite
          (K := K) (L := L) (cofinalIdeleStage K L U)
          (resizedPlacesTransition
            (K := K) (L := L) hStage q)).1,
      exceptionalDirectFun
        (K := K) (L := L) (cofinalIdeleStage K L U)
        (cofinalExceptionalFun
          (K := K) (L := L) U
          (resizedIdelesInfinite
            (K := K) (L := L) (cofinalIdeleStage K L U)
            (resizedPlacesTransition
              (K := K) (L := L) hStage q)).2)) = _
  rw [hsplit]
  apply Prod.ext
  · rfl
  · let qFin :=
      (resizedIdelesInfinite
        (K := K) (L := L) (cofinalIdeleStage K L T) q).2
    apply DirectSum.ext
    intro P
    exact cofinal_stage_direct
      (K := K) (L := L) hTU qFin P

noncomputable def idelesSplitStage
    (S : Finset (NumberFieldPlace K)) :
    tateCohomologyZero
        (resizedPlacesRepresentation (K := K) (L := L) S) →+
      ResizedTateSplit K L :=
  (cofinalPlacesSplit
    (K := K) (L := L) S).comp
      (resizedPlacesTransition
        (K := K) (L := L)
        (show S ⊆ cofinalIdeleStage K L S from
          Finset.subset_union_right)).toAddMonoidHom

theorem ideles_places_stage
    {S T : Finset (NumberFieldPlace K)} (hST : S ⊆ T)
    (q : tateCohomologyZero
      (resizedPlacesRepresentation (K := K) (L := L) S)) :
    idelesSplitStage
        (K := K) (L := L) T
        (resizedPlacesTransition
          (K := K) (L := L) hST q) =
      idelesSplitStage
        (K := K) (L := L) S q := by
  let hS : S ⊆ cofinalIdeleStage K L S := Finset.subset_union_right
  let hT : T ⊆ cofinalIdeleStage K L T := Finset.subset_union_right
  let hC : cofinalIdeleStage K L S ⊆
      cofinalIdeleStage K L T :=
    cofinal_stage_mono (K := K) (L := L) hST
  have hpromote :
      resizedPlacesTransition
          (K := K) (L := L) hT
          (resizedPlacesTransition
            (K := K) (L := L) hST q) =
        resizedPlacesTransition
          (K := K) (L := L) hC
          (resizedPlacesTransition
            (K := K) (L := L) hS q) := by
    rw [resized_ideles_comp,
      resized_ideles_comp]
  change cofinalPlacesSplit
      (K := K) (L := L) T
      (resizedPlacesTransition
        (K := K) (L := L) hT
        (resizedPlacesTransition
          (K := K) (L := L) hST q)) = _
  rw [hpromote]
  exact cofinal_split_transition
    (K := K) (L := L) hST _

noncomputable def resizedIdelesFun :
    ResizedIdelesLimit K L →
      ResizedTateSplit K L :=
  DirectLimit.lift
    (ι := Finset (NumberFieldPlace K))
    (F := fun S : Finset (NumberFieldPlace K) ↦
      tateCohomologyZero
        (resizedPlacesRepresentation (K := K) (L := L) S))
    (fun _ _ h ↦ resizedPlacesTransition
      (K := K) (L := L) h)
    (fun S q ↦ idelesSplitStage
      (K := K) (L := L) S q)
    (fun _ _ h q ↦
      (ideles_places_stage
        (K := K) (L := L) h q).symm)

noncomputable def resizedPlacesSplit :
    ResizedIdelesLimit K L →+
      ResizedTateSplit K L where
  toFun := resizedIdelesFun
    (K := K) (L := L)
  map_zero' := by
    change resizedIdelesFun
      (K := K) (L := L) 0 = 0
    unfold resizedIdelesFun
    rw [DirectLimit.zero_def (∅ : Finset (NumberFieldPlace K)),
      DirectLimit.lift_def]
    exact map_zero _
  map_add' q q' := by
    change resizedIdelesFun
        (K := K) (L := L) (q + q') =
      resizedIdelesFun
          (K := K) (L := L) q +
        resizedIdelesFun
          (K := K) (L := L) q'
    unfold resizedIdelesFun
    induction q, q' using DirectLimit.induction₂ with
    | _ S x y =>
      rw [DirectLimit.add_def, DirectLimit.lift_def,
        DirectLimit.lift_def, DirectLimit.lift_def]
      exact map_add _ x y

@[simp]
theorem resized_limit_mk
    (S : Finset (NumberFieldPlace K))
    (q : tateCohomologyZero
      (resizedPlacesRepresentation (K := K) (L := L) S)) :
    resizedPlacesSplit
        (K := K) (L := L) (⟦⟨S, q⟩⟧) =
      idelesSplitStage (K := K) (L := L) S q := by
  unfold resizedPlacesSplit
  unfold resizedIdelesFun
  rfl

theorem resized_split_injective :
    Function.Injective
      (resizedPlacesSplit
        (K := K) (L := L)) := by
  intro q q' hqq'
  apply sub_eq_zero.mp
  have hzero : resizedPlacesSplit
      (K := K) (L := L) (q - q') = 0 := by
    rw [map_sub, hqq', sub_self]
  let F : Finset (NumberFieldPlace K) → Type u := fun S ↦
    tateCohomologyZero
      (resizedPlacesRepresentation (K := K) (L := L) S)
  let f := fun (S T : Finset (NumberFieldPlace K)) (h : S ⊆ T) ↦
    resizedPlacesTransition (K := K) (L := L) h
  obtain ⟨S, qS, hq⟩ := DirectLimit.exists_eq_mk f (q - q')
  rw [hq] at hzero ⊢
  let hS : S ⊆ cofinalIdeleStage K L S := Finset.subset_union_right
  have hstage : cofinalPlacesSplit
      (K := K) (L := L) S
      (f S (cofinalIdeleStage K L S) hS qS) = 0 := hzero
  have hqSzero : f S (cofinalIdeleStage K L S) hS qS = 0 :=
    cofinal_ideles_injective
      (K := K) (L := L) S (hstage.trans (map_zero _).symm)
  calc
    (⟦⟨S, qS⟩⟧ : DirectLimit F f) =
        ⟦⟨cofinalIdeleStage K L S,
          f S (cofinalIdeleStage K L S) hS qS⟩⟧ :=
      DirectLimit.eq_of_le (f := f) ⟨S, qS⟩
        (cofinalIdeleStage K L S) hS
    _ = ⟦⟨cofinalIdeleStage K L S, 0⟩⟧ :=
      congrArg (fun z ↦ (⟦⟨cofinalIdeleStage K L S, z⟩⟧ :
        DirectLimit F f)) hqSzero
    _ = 0 := (DirectLimit.zero_def _).symm

set_option maxHeartbeats 4000000 in
-- Constructing a preimage coordinates both infinite and finite direct-limit
-- factors and elaborates their dependent transition proofs.
theorem resized_ideles_preimage
    (y : ResizedTateSplit K L) :
    ∃ q : ResizedIdelesLimit K L,
      resizedPlacesSplit
        (K := K) (L := L) q = y := by
  obtain ⟨S, xS, hxS⟩ :=
    exceptional_tate_preimage
      (K := K) (L := L) y.2
  let C := cofinalIdeleStage K L S
  let hS : S ⊆ C := Finset.subset_union_right
  let xC : ExceptionalTateZero K L C :=
    resizedExceptionalTate
      (K := K) (L := L) hS xS
  let qInf :=
    (resizedIdelesDirect
      (K := K) (L := L)).symm y.1
  let qFin :=
    (cofinalTateExceptional
      (K := K) (L := L) S).symm xC
  let qC := (resizedIdelesInfinite
    (K := K) (L := L) C).symm (qInf, qFin)
  refine ⟨(⟦⟨C, qC⟩⟧ : ResizedIdelesLimit K L), ?_⟩
  rw [resized_limit_mk]
  rw [show idelesSplitStage
      (K := K) (L := L) C qC =
        cofinalPlacesSplit
          (K := K) (L := L) S qC by
    exact cofinal_split_transition
      (K := K) (L := L) hS qC]
  apply Prod.ext
  · rw [cofinal_ideles_fst]
    rw [show resizedIdelesInfinite
        (K := K) (L := L) C qC = (qInf, qFin) from
      AddEquiv.apply_symm_apply _ _]
    exact AddEquiv.apply_symm_apply _ _
  · rw [cofinal_ideles_snd]
    rw [show resizedIdelesInfinite
        (K := K) (L := L) C qC = (qInf, qFin) from
      AddEquiv.apply_symm_apply _ _]
    have hqFin : cofinalExceptionalFun
        (K := K) (L := L) S qFin = xC := by
      funext P
      rw [← cofinal_tate_exceptional]
      exact congrFun (AddEquiv.apply_symm_apply
        (cofinalTateExceptional
          (K := K) (L := L) S) xC) P
    rw [hqFin]
    change exceptionalDirectSum
        (K := K) (L := L) C xC = y.2
    rw [resized_direct_transition
      (K := K) (L := L) hS xS]
    exact hxS

noncomputable def resizedLimitSplit :
    ResizedIdelesLimit K L ≃+
      ResizedTateSplit K L :=
  AddEquiv.ofBijective
    (resizedPlacesSplit (K := K) (L := L))
    ⟨resized_split_injective
      (K := K) (L := L),
     fun y ↦ resized_ideles_preimage
      (K := K) (L := L) y⟩

/-! ## Recombining finite and infinite places -/

/-- A direct sum indexed by a sum type splits into the product of the two
component direct sums. -/
noncomputable def directSumAdd
    {I J : Type u} (C : I ⊕ J → Type u)
    [∀ s, AddCommGroup (C s)] :
    DirectSum (I ⊕ J) C ≃+
      DirectSum I (fun i ↦ C (.inl i)) ×
        DirectSum J (fun j ↦ C (.inr j)) := by
  let e := Equiv.sumEquivSigmaBool I J
  let δ : (b : Bool) → (bif b then J else I) → Type u :=
    fun b x ↦ C (e.symm ⟨b, x⟩)
  let e₁ : DirectSum (I ⊕ J) C ≃+
      DirectSum (Σ b, bif b then J else I)
        (fun s ↦ C (e.symm s)) := DirectSum.equivCongrLeft e
  let e₂ : DirectSum (Σ b, bif b then J else I)
      (fun s ↦ C (e.symm s)) ≃+
      DirectSum Bool (fun b ↦ DirectSum (bif b then J else I) (δ b)) :=
    DirectSum.sigmaCurryEquiv (δ := δ)
  let D := fun b : Bool ↦ DirectSum (bif b then J else I) (δ b)
  let e₃ : DirectSum Bool D ≃+ (∀ b, D b) := DirectSum.addEquivProd D
  let e₄ : (∀ b : Bool, D b) ≃+ D false × D true :=
    { toFun := fun f ↦ (f false, f true)
      invFun := fun p b ↦ match b with
        | false => p.1
        | true => p.2
      left_inv := fun f ↦ by funext b; cases b <;> rfl
      right_inv := fun p ↦ rfl
      map_add' := fun _ _ ↦ rfl }
  exact ((e₁.trans e₂).trans e₃).trans e₄

noncomputable def resizedTatePlace
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    OrbitTateZero K L P ≃+
      tateCohomologyZero
        (resizedPlaceRepresentation
          (K := K) (L := L) (.inl P)) := by
  exact completionOrbitTate (K := K) (L := L) P |>.trans
    (tateAddIso
      (resizedIsoOrbit
        (K := K) (L := L) P)).symm

noncomputable def resizedTateDirect :
    DirectSum (HeightOneSpectrum (NumberField.RingOfIntegers K))
        (OrbitTateZero K L) ≃+
      DirectSum (HeightOneSpectrum (NumberField.RingOfIntegers K))
        (fun P ↦ tateCohomologyZero
          (resizedPlaceRepresentation
            (K := K) (L := L) (.inl P))) :=
  DirectSum.congrAddEquiv fun P ↦
    resizedTatePlace
      (K := K) (L := L) P

/-- Tate degree zero of the restricted idèles is the direct sum of the
Tate-zero groups of all completion orbits. -/
noncomputable def resizedTateDecomposition :
    tateCohomologyZero (resizedConcreteRepresentation K L) ≃+
      DirectSum (NumberFieldPlace K)
        (fun v ↦ tateCohomologyZero
          (resizedPlaceRepresentation
            (K := K) (L := L) v)) :=
  (resizedIdelesTate
    (K := K) (L := L)).symm |>.trans
    ((resizedLimitSplit
      (K := K) (L := L)).trans <|
      (AddEquiv.prodCongr
        (AddEquiv.refl _)
        (resizedTateDirect
          (K := K) (L := L))).trans <|
        AddEquiv.prodComm |>.trans
          (directSumAdd
            (fun v : NumberFieldPlace K ↦ tateCohomologyZero
              (resizedPlaceRepresentation
                (K := K) (L := L) v))).symm)

/-! ## Placewise Tate Shapiro and Proposition VII.2.5 -/

local instance tateDirectSumCompletionPlaceStabilizerFintype
    (completion : HasseCompletionData K L) (v : NumberFieldPlace K) :
    Fintype (CompletionPlaceStabilizer
      (hasseAbsoluteValue v)
      (hasseChosenPlace completion v)) :=
  Fintype.ofFinite _

local instance (priority := 2000)
    tateDirectSumChosenCompletionAddCommGroup
    (completion : HasseCompletionData K L) (v : NumberFieldPlace K) :
    AddCommGroup (tateCohomologyZero
      (chosenUnitsRepresentation
        (K := K) (L := L) completion v)) := inferInstance

noncomputable def resizedTateStabilizer
    (completion : HasseCompletionData K L)
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    tateCohomologyZero
        (resizedPlaceRepresentation
          (K := K) (L := L) (.inl P)) ≃+
      tateCohomologyZero
        (chosenUnitsRepresentation
          (K := K) (L := L) completion (.inl P)) := by
  letI : MulAction.IsPretransitive Gal(L/K)
      (CompletionPlacesAbove (L := L) (FinitePlace.mk P).val) :=
    completion_above_pretransitive P
  let H := CompletionPlaceStabilizer
    (hasseAbsoluteValue (K := K) (.inl P))
    (hasseChosenPlace completion (.inl P))
  let A := chosenUnitsRepresentation
    (K := K) (L := L) completion (.inl P)
  exact (tateAddIso
    (uliftInducedIso
      (K := K) (L := L) (FinitePlace.mk P).val
      (hasseChosenPlace completion (.inl P)))).trans
    (tateCohomologyCoinduced H A)

noncomputable def resizedInfiniteStabilizer
    (completion : HasseCompletionData K L) (v : InfinitePlace K) :
    tateCohomologyZero
        (resizedPlaceRepresentation
          (K := K) (L := L) (.inr v)) ≃+
      tateCohomologyZero
        (chosenUnitsRepresentation
          (K := K) (L := L) completion (.inr v)) := by
  letI : MulAction.IsPretransitive Gal(L/K)
      (CompletionPlacesAbove (L := L) v.1) :=
    places_above_pretransitive v
  let H := CompletionPlaceStabilizer
    (hasseAbsoluteValue (K := K) (.inr v))
    (hasseChosenPlace completion (.inr v))
  let A := chosenUnitsRepresentation
    (K := K) (L := L) completion (.inr v)
  exact (tateAddIso
    (uliftInducedIso
      (K := K) (L := L) v.1
      (hasseChosenPlace completion (.inr v)))).trans
    (tateCohomologyCoinduced H A)

noncomputable def resizedCompletionStabilizer
    (completion : HasseCompletionData K L)
    (v : NumberFieldPlace K) :
    tateCohomologyZero
        (resizedPlaceRepresentation
          (K := K) (L := L) v) ≃+
      tateCohomologyZero
        (chosenUnitsRepresentation
          (K := K) (L := L) completion v) := by
  cases v with
  | inl P =>
      exact resizedTateStabilizer
        (K := K) (L := L) completion P
  | inr v =>
      exact resizedInfiniteStabilizer
        (K := K) (L := L) completion v

noncomputable def tateDirectStabilizer
    (completion : HasseCompletionData K L) :
    DirectSum (NumberFieldPlace K)
        (fun v ↦ tateCohomologyZero
          (resizedPlaceRepresentation
            (K := K) (L := L) v)) ≃+
      DirectSum (NumberFieldPlace K)
        (fun v ↦ tateCohomologyZero
          (chosenUnitsRepresentation
            (K := K) (L := L) completion v)) :=
  DirectSum.congrAddEquiv fun v ↦
    resizedCompletionStabilizer
      (K := K) (L := L) completion v

/-- **Proposition VII.2.5.**  For the concrete restricted idèle
representation, Tate degree zero and every positive degree decompose as the
direct sum of the corresponding local decomposition-group cohomology. -/
theorem resized_concrete_direct
    (completion : HasseCompletionData K L) :
    IdeleCohomologyDirect
      (resizedConcreteRepresentation K L)
      (fun v ↦ CompletionPlaceStabilizer
        (hasseAbsoluteValue v)
        (hasseChosenPlace completion v))
      (fun v ↦ chosenUnitsRepresentation
        (K := K) (L := L) completion v) := by
  constructor
  · exact ⟨resizedTateDecomposition
      (K := K) (L := L) |>.trans
        (tateDirectStabilizer
          (K := K) (L := L) completion)⟩
  · exact resized_cohomology_direct
      (K := K) (L := L) completion

end

end Submission.CField.HNorm
