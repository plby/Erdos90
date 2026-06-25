import Mathlib.RepresentationTheory.FiniteIndex
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Shapiro
import Mathlib.RepresentationTheory.Homological.GroupHomology.Shapiro
import Towers.ClassField.Shifting.LowTateCohomology

/-!
# Milne, Class Field Theory, Proposition II.3.1

An induced module, in Milne's sense of induction from the trivial subgroup, has
vanishing Tate cohomology in every degree.  Mathlib does not yet package Tate
cohomology uniformly over the integers, so the result is stated in its four
source-order pieces: positive group cohomology, degrees zero and minus one,
and positive group homology (which gives Tate degrees at most minus two).
-/

namespace Towers.CField.Shifting

open CategoryTheory Representation

noncomputable section

universe u

variable {k G : Type u} [CommRing k] [Group G] [Fintype G]

local instance : DecidableRel (QuotientGroup.rightRel (⊥ : Subgroup G)) :=
  Classical.decRel _

private abbrev botRep (A : Rep.{u} k (⊥ : Subgroup G)) : Rep.{u} k G :=
  Rep.ind (⊥ : Subgroup G).subtype A

private def bottomToTrivial (A : Rep.{u} k (⊥ : Subgroup G)) :
    A ⟶ Rep.res (⊥ : Subgroup G).subtype (Rep.trivial k G A) :=
  Rep.ofHom ⟨LinearMap.id, fun s ↦ LinearMap.ext fun x ↦ by
    obtain rfl : s = 1 := Subtype.ext (Subgroup.mem_bot.mp s.property)
    change A.ρ 1 x = x
    simp⟩

/-- Augmentation of a module induced from the trivial subgroup. -/
private def inducedAugmentation (A : Rep.{u} k (⊥ : Subgroup G)) : botRep A →ₗ[k] A :=
  ((Rep.indResHomEquiv (⊥ : Subgroup G).subtype A (Rep.trivial k G A)).symm
    (bottomToTrivial A)).hom.toLinearMap

omit [Fintype G] in
@[simp]
private theorem induced_ind_mk (A : Rep.{u} k (⊥ : Subgroup G))
    (g : G) (a : A) :
    inducedAugmentation A (IndV.mk (⊥ : Subgroup G).subtype A.ρ g a) = a := by
  simp [inducedAugmentation, Rep.indResHomEquiv, bottomToTrivial]

/-- The coinvariants of a module induced from the trivial subgroup are the
original module, via augmentation. -/
private def inducedCoinvariantsEquiv (A : Rep.{u} k (⊥ : Subgroup G)) :
    (botRep A).ρ.Coinvariants ≃ₗ[k] A := by
  let toBase : (botRep A).ρ.Coinvariants →ₗ[k] A :=
    Coinvariants.lift _ (inducedAugmentation A) fun g ↦ by
      let f : botRep A ⟶ Rep.trivial k G A :=
        (Rep.indResHomEquiv (⊥ : Subgroup G).subtype A (Rep.trivial k G A)).symm
          (bottomToTrivial A)
      exact LinearMap.ext fun x ↦ by
        simpa [inducedAugmentation, f] using Rep.hom_comm_apply f g x
  let fromBase : A →ₗ[k] (botRep A).ρ.Coinvariants :=
    Coinvariants.mk _ ∘ₗ IndV.mk (⊥ : Subgroup G).subtype A.ρ 1
  refine LinearEquiv.ofLinear toBase fromBase ?_ ?_
  · ext a
    exact induced_ind_mk A 1 a
  · apply Coinvariants.hom_ext
    apply IndV.hom_ext
    intro g
    ext a
    change Coinvariants.mk _
        (IndV.mk (⊥ : Subgroup G).subtype A.ρ 1
          (inducedAugmentation A (IndV.mk (⊥ : Subgroup G).subtype A.ρ g a))) =
      Coinvariants.mk _ (IndV.mk (⊥ : Subgroup G).subtype A.ρ g a)
    rw [induced_ind_mk]
    rw [← Coinvariants.mk_self_apply (botRep A).ρ g⁻¹
      (IndV.mk (⊥ : Subgroup G).subtype A.ρ 1 a)]
    simp

omit [Fintype G] in
@[simp]
private theorem induced_coinvariants_mk
    (A : Rep.{u} k (⊥ : Subgroup G)) (g : G) (a : A) :
    inducedCoinvariantsEquiv A
        (Coinvariants.mk _ (IndV.mk (⊥ : Subgroup G).subtype A.ρ g a)) = a :=
  induced_ind_mk A g a

/-- Evaluation at one identifies invariant coinduced functions from the
trivial subgroup with their constant value. -/
private def coinducedInvariantsEquiv (A : Rep.{u} k (⊥ : Subgroup G)) :
    (Rep.coind (⊥ : Subgroup G).subtype A).ρ.invariants ≃ₗ[k] A where
  toFun x := x.1.1 1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun a := ⟨⟨fun _ ↦ a, fun s g ↦ by
    obtain rfl : s = 1 := Subtype.ext (Subgroup.mem_bot.mp s.property)
    simp⟩, fun g ↦ by
      apply Subtype.ext
      funext h
      rfl⟩
  left_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    funext g
    have h := congrArg (fun f ↦ f.1 1) (x.2 g)
    simpa using h.symm
  right_inv _ := rfl

/-- An isomorphism of representations restricts to an isomorphism on
invariants. -/
private def invariantsEquivIso {A B : Rep.{u} k G} (e : A ≅ B) :
    A.ρ.invariants ≃ₗ[k] B.ρ.invariants where
  toFun x := ⟨e.hom.hom x.1, fun g ↦ by
    rw [← e.hom.hom.isIntertwining]
    simp [x.2 g]⟩
  map_add' _ _ := by ext; simp
  map_smul' _ _ := by ext; simp
  invFun x := ⟨e.inv.hom x.1, fun g ↦ by
    rw [← e.inv.hom.isIntertwining]
    simp [x.2 g]⟩
  left_inv x := by ext; simp
  right_inv x := by ext; simp

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

/-- The invariants of a module induced from the trivial subgroup are the
original module: pass through finite-index induction-coinduction and evaluate
at one. -/
private def inducedInvariantsEquiv (A : Rep.{u} k (⊥ : Subgroup G)) :
    (botRep A).ρ.invariants ≃ₗ[k] A :=
  (invariantsEquivIso (Rep.indCoindIso A)).trans (coinducedInvariantsEquiv A)

omit [Fintype G] in
private theorem bottom_right_rel (x y : G) :
    (QuotientGroup.rightRel (⊥ : Subgroup G)).r x y ↔ x = y := by
  constructor
  · rintro ⟨s, rfl⟩
    obtain rfl : s = 1 := Subtype.ext (Subgroup.mem_bot.mp s.property)
    simp
  · rintro rfl
    exact ⟨1, by simp⟩

omit [Fintype G] in
@[simp]
private theorem ind_coind_v
    (A : Rep.{u} k (⊥ : Subgroup G)) (g h : G) (a : A) :
    (Rep.indToCoind A (IndV.mk (⊥ : Subgroup G).subtype A.ρ g a)).1 h =
      Rep.indToCoindAux A g a h := by
  simp [Rep.indToCoind]

private theorem induced_invariants_mk
    (A : Rep.{u} k (⊥ : Subgroup G)) (g : G) (a : A) :
    inducedInvariantsEquiv A
        ⟨(botRep A).ρ.norm (IndV.mk (⊥ : Subgroup G).subtype A.ρ g a),
          fun h ↦ (botRep A).ρ.self_norm_apply h _⟩ = a := by
  change ((Rep.indToCoind A) ((botRep A).ρ.norm
    (IndV.mk (⊥ : Subgroup G).subtype A.ρ g a))).1 1 = a
  rw [show (botRep A).ρ.norm
      (IndV.mk (⊥ : Subgroup G).subtype A.ρ g a) =
      ∑ h : G, (botRep A).ρ h
        (IndV.mk (⊥ : Subgroup G).subtype A.ρ g a) by
          simp [Representation.norm], map_sum]
  rw [Submodule.coe_sum, Finset.sum_apply]
  simp only [Representation.ind_mk]
  rw [Finset.sum_eq_single g]
  · rw [ind_coind_v]
    simp
  · intro h _ hne
    rw [ind_coind_v, Rep.indToCoindAux_of_not_rel]
    rw [bottom_right_rel]
    intro hr
    apply hne
    have := congrArg (fun x : G ↦ x * h) hr
    simpa using this
  · simp

/-- Under the canonical identifications of the coinvariants and invariants
with the base module, the norm of an induced module is the identity. -/
private theorem induced_invariants_comp
    (A : Rep.{u} k (⊥ : Subgroup G)) :
    (inducedInvariantsEquiv A).toLinearMap.comp
        (normCoinvariantsInvariants (botRep A)) =
      (inducedCoinvariantsEquiv A).toLinearMap := by
  apply Coinvariants.hom_ext
  apply IndV.hom_ext
  intro g
  ext a
  simp only [LinearMap.comp_apply]
  rw [coinvariants_invariants_mk]
  exact (induced_invariants_mk A g a).trans
    (induced_coinvariants_mk A g a).symm

/-- **Proposition II.3.1, degree zero.** Degree-zero Tate cohomology of a
module induced from the trivial subgroup vanishes. -/
theorem subsingleton_tate_induced
    (A : Rep.{u} k (⊥ : Subgroup G)) :
    Subsingleton (tateCohomologyZero (botRep A)) := by
  change Subsingleton
    ((botRep A).ρ.invariants ⧸ LinearMap.range (normCoinvariantsInvariants (botRep A)))
  rw [Submodule.Quotient.subsingleton_iff]
  apply Submodule.eq_top_iff'.2
  intro y
  let x := (inducedCoinvariantsEquiv A).symm (inducedInvariantsEquiv A y)
  refine ⟨x, ?_⟩
  apply (inducedInvariantsEquiv A).injective
  simpa [x] using LinearMap.congr_fun (induced_invariants_comp A) x

/-- **Proposition II.3.1, degree minus one.** Degree-minus-one Tate
cohomology of a module induced from the trivial subgroup vanishes. -/
theorem subsingleton_cohomology_induced
    (A : Rep.{u} k (⊥ : Subgroup G)) :
    Subsingleton (tateCohomologyOne (botRep A)) := by
  constructor
  rintro ⟨x, hx⟩ ⟨y, hy⟩
  apply Subtype.ext
  apply (inducedCoinvariantsEquiv A).injective
  change inducedCoinvariantsEquiv A x = inducedCoinvariantsEquiv A y
  have zx : inducedCoinvariantsEquiv A x = 0 := by
    calc
      inducedCoinvariantsEquiv A x =
          inducedInvariantsEquiv A (normCoinvariantsInvariants (botRep A) x) :=
        (LinearMap.congr_fun (induced_invariants_comp A) x).symm
      _ = 0 := by rw [LinearMap.mem_ker.mp hx]; simp
  have zy : inducedCoinvariantsEquiv A y = 0 := by
    calc
      inducedCoinvariantsEquiv A y =
          inducedInvariantsEquiv A (normCoinvariantsInvariants (botRep A) y) :=
        (LinearMap.congr_fun (induced_invariants_comp A) y).symm
      _ = 0 := by rw [LinearMap.mem_ker.mp hy]; simp
  rw [zx, zy]

set_option linter.unusedFintypeInType false in
/-- **Proposition II.3.1, positive degrees.** Positive group cohomology of
a module induced from the trivial subgroup vanishes. -/
theorem cohomology_induced_succ
    (A : Rep.{u} k (⊥ : Subgroup G)) (n : ℕ) :
    Limits.IsZero (groupCohomology (botRep A) (n + 1)) := by
  let e : botRep A ≅ Rep.coind (⊥ : Subgroup G).subtype A := Rep.indCoindIso A
  have hA : Limits.IsZero (groupCohomology A (n + 1)) :=
    isZero_groupCohomology_succ_of_subsingleton A n
  have hc : Limits.IsZero
      (groupCohomology (Rep.coind (⊥ : Subgroup G).subtype A) (n + 1)) :=
    Limits.IsZero.of_iso hA (groupCohomology.coindIso A (n + 1))
  exact Limits.IsZero.of_iso hc
    ((groupCohomology.functor k G (n + 1)).mapIso e)

set_option linter.unusedFintypeInType false in
/-- Positive-degree formulation of Proposition II.3.1. -/
theorem zero_cohomology_induced
    (A : Rep.{u} k (⊥ : Subgroup G)) (n : ℕ) (hn : 0 < n) :
    Limits.IsZero (groupCohomology (botRep A) n) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  exact cohomology_induced_succ A m

omit [Fintype G] in
/-- **Proposition II.3.1, degrees at most minus two.** Positive group
homology of a module induced from the trivial subgroup vanishes. -/
theorem homology_induced_succ
    (A : Rep.{u} k (⊥ : Subgroup G)) (n : ℕ) :
    Limits.IsZero (groupHomology (botRep A) (n + 1)) := by
  letI := Classical.decEq G
  have hA : Limits.IsZero (groupHomology A (n + 1)) :=
    isZero_groupHomology_succ_of_subsingleton A n
  exact Limits.IsZero.of_iso hA (groupHomology.indIso (⊥ : Subgroup G) A (n + 1))

omit [Fintype G] in
/-- Positive-homological-degree formulation of Proposition II.3.1, i.e.
the Tate-cohomological range of degrees at most minus two. -/
theorem zero_homology_induced
    (A : Rep.{u} k (⊥ : Subgroup G)) (n : ℕ) (hn : 0 < n) :
    Limits.IsZero (groupHomology (botRep A) n) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  exact homology_induced_succ A m

end

end Towers.CField.Shifting
