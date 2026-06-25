import Towers.Group.Edmonton.SubgroupCommutators

/-!
# The Edmonton Notes on Nilpotent Groups: commutators of generated subgroups

This file formalizes Hall's Lemma 2.4.
-/

namespace Towers
namespace Edmonton

open Group
open scoped commutatorElement

universe u

variable {G : Type u} [Group G]

/-- The set Hall writes as `S^X`: all right conjugates of elements of `S`
by elements of `X`. -/
def hallConjugatesBy (S : Set G) (X : Subgroup G) : Set G :=
  {z | ∃ s ∈ S, ∃ x ∈ X, hallConjugate s x = z}

/-- The subgroup Hall writes as `⟨S^X⟩`. -/
def relativeNormalClosure (S : Set G) (X : Subgroup G) : Subgroup G :=
  Subgroup.closure (hallConjugatesBy S X)

/-- Every element of `S` belongs to `⟨S^X⟩`. -/
lemma subset_relative_closure (S : Set G) (X : Subgroup G) :
    S ⊆ relativeNormalClosure S X := by
  intro s hs
  apply Subgroup.subset_closure
  exact ⟨s, hs, 1, X.one_mem, by simp [hallConjugate]⟩

/-- Conjugation by an element of `X` preserves the generating conjugates
used in `⟨S^X⟩`. -/
lemma conjugate_hall_conjugates
    {S : Set G} {X : Subgroup G} {g z : G}
    (hg : g ∈ X) (hz : z ∈ hallConjugatesBy S X) :
    g * z * g⁻¹ ∈ hallConjugatesBy S X := by
  obtain ⟨s, hs, x, hx, rfl⟩ := hz
  refine ⟨s, hs, x * g⁻¹, X.mul_mem hx (X.inv_mem hg), ?_⟩
  simp [hallConjugate, mul_assoc]

/-- Conjugation by an element of `X` preserves `⟨S^X⟩`. -/
lemma conjugate_relative_closure
    {S : Set G} {X : Subgroup G} {g z : G}
    (hg : g ∈ X) (hz : z ∈ relativeNormalClosure S X) :
    g * z * g⁻¹ ∈ relativeNormalClosure S X := by
  rw [relativeNormalClosure] at hz ⊢
  refine Subgroup.closure_induction ?_ ?_ ?_ ?_ hz
  · exact fun z hz ↦ Subgroup.subset_closure (conjugate_hall_conjugates hg hz)
  · simp
  · intro a b _ _ ha hb
    rw [← conj_mul]
    exact (Subgroup.closure (hallConjugatesBy S X)).mul_mem ha hb
  · intro a _ ha
    rw [← conj_inv]
    exact (Subgroup.closure (hallConjugatesBy S X)).inv_mem ha

/-- The subgroup `X` normalizes `⟨S^X⟩`. -/
lemma normalizer_relative_closure (S : Set G) (X : Subgroup G) :
    X ≤ Subgroup.normalizer (relativeNormalClosure S X : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro z
  constructor
  · exact conjugate_relative_closure hg
  · intro hz
    have hback :=
      conjugate_relative_closure (X.inv_mem hg) hz
    simpa [mul_assoc] using hback

/-- `⟨S^X⟩` is the smallest subgroup containing `S` and normalized by
`X`. -/
lemma relative_normal_closure
    {S : Set G} {X N : Subgroup G} (hS : S ⊆ N)
    (hX : X ≤ Subgroup.normalizer (N : Set G)) :
    relativeNormalClosure S X ≤ N := by
  rw [relativeNormalClosure, Subgroup.closure_le]
  rintro _ ⟨s, hs, x, hx, rfl⟩
  exact (Subgroup.mem_normalizer_iff''.mp (hX hx) s).mp (hS hs)

/-- The basic commutators formed from the generating sets `A` and `B`. -/
def basicHallCommutators (A B : Set G) : Set G :=
  {c | ∃ a ∈ A, ∃ b ∈ B, hallCommutator a b = c}

/-- Commuting a member of `⟨A⟩` with a generator from `B` lands in
`⟨C^⟨A⟩⟩`, where `C` is the set of basic commutators. -/
lemma closure_relative_normal
    (A B : Set G) {x b : G} (hx : x ∈ Subgroup.closure A) (hb : b ∈ B) :
    hallCommutator x b ∈
      relativeNormalClosure (basicHallCommutators A B) (Subgroup.closure A) := by
  let N :=
    relativeNormalClosure (basicHallCommutators A B) (Subgroup.closure A)
  have hnorm :
      Subgroup.closure A ≤ Subgroup.normalizer (N : Set G) :=
    normalizer_relative_closure _ _
  induction hx using Subgroup.closure_induction with
  | mem a ha =>
      exact subset_relative_closure _ _
        ⟨a, ha, b, hb, rfl⟩
  | one =>
      simp [hallCommutator]
  | mul x y hx hy ihx ihy =>
      rw [commutator_mul_left]
      exact N.mul_mem
        ((Subgroup.mem_normalizer_iff''.mp (hnorm hy) _).mp ihx) ihy
  | inv x hx ih =>
      have hconj :
          hallConjugate (hallCommutator x b) x⁻¹ ∈ N :=
        (Subgroup.mem_normalizer_iff''.mp
          (hnorm ((Subgroup.closure A).inv_mem hx)) _).mp ih
      simpa [hallCommutator, hallConjugate, mul_assoc] using N.inv_mem hconj

/-- All Hall commutators between `⟨A⟩` and `⟨B⟩` lie in the iterated
relative normal closure from Lemma 2.4. -/
lemma closures_iterated_closure
    (A B : Set G) {x y : G}
    (hx : x ∈ Subgroup.closure A) (hy : y ∈ Subgroup.closure B) :
    hallCommutator x y ∈
      relativeNormalClosure
        (relativeNormalClosure
          (basicHallCommutators A B) (Subgroup.closure A) : Set G)
        (Subgroup.closure B) := by
  let N :=
    relativeNormalClosure (basicHallCommutators A B) (Subgroup.closure A)
  let H := relativeNormalClosure (N : Set G) (Subgroup.closure B)
  have hNleH : N ≤ H :=
    subset_relative_closure (N : Set G) (Subgroup.closure B)
  have hnorm :
      Subgroup.closure B ≤ Subgroup.normalizer (H : Set G) :=
    normalizer_relative_closure _ _
  induction hy using Subgroup.closure_induction with
  | mem b hb =>
      exact hNleH
        (closure_relative_normal A B hx hb)
  | one =>
      simp [hallCommutator]
  | mul y z hy hz ihy ihz =>
      rw [commutator_mul_right]
      exact H.mul_mem ihz
        ((Subgroup.mem_normalizer_iff''.mp (hnorm hz) _).mp ihy)
  | inv y hy ih =>
      have hconj :
          hallConjugate (hallCommutator x y) y⁻¹ ∈ H :=
        (Subgroup.mem_normalizer_iff''.mp
          (hnorm ((Subgroup.closure B).inv_mem hy)) _).mp ih
      simpa [hallCommutator, hallConjugate, mul_assoc] using H.inv_mem hconj

/-- The iterated relative normal closure of the basic commutators is
contained in the full subgroup commutator. -/
lemma iterated_relative_commutator (A B : Set G) :
    relativeNormalClosure
        (relativeNormalClosure
          (basicHallCommutators A B) (Subgroup.closure A) : Set G)
        (Subgroup.closure B) ≤
      ⁅Subgroup.closure A, Subgroup.closure B⁆ := by
  let X := Subgroup.closure A
  let Y := Subgroup.closure B
  let C := (⁅X, Y⁆ : Subgroup G)
  have hC_le : C ≤ X ⊔ Y :=
    Subgroup.commutator_mono le_sup_left le_sup_right
      |>.trans (X ⊔ Y).commutator_le_self
  letI : (C.subgroupOf (X ⊔ Y)).Normal := commutator_sup X Y
  have hnormalizer :
      X ⊔ Y ≤ Subgroup.normalizer (C : Set G) :=
    Subgroup.le_normalizer_of_normal_subgroupOf hC_le
  have hbasic : basicHallCommutators A B ⊆ C := by
    rintro _ ⟨a, ha, b, hb, rfl⟩
    exact hall_commutator
      (Subgroup.subset_closure ha) (Subgroup.subset_closure hb)
  have hinner :
      relativeNormalClosure (basicHallCommutators A B) X ≤ C :=
    relative_normal_closure hbasic (le_sup_left.trans hnormalizer)
  exact relative_normal_closure hinner (le_sup_right.trans hnormalizer)

/-- **Hall, Lemma 2.4.** If `X = ⟨A⟩`, `Y = ⟨B⟩`, and `C` is the set of
basic commutators `[a,b]`, then `[X,Y] = ⟨⟨C^X⟩^Y⟩`. -/
theorem commutator_closures_iterated (A B : Set G) :
    ⁅Subgroup.closure A, Subgroup.closure B⁆ =
      relativeNormalClosure
        (relativeNormalClosure
          (basicHallCommutators A B) (Subgroup.closure A) : Set G)
        (Subgroup.closure B) := by
  apply le_antisymm
  · rw [Subgroup.commutator_le]
    intro x hx y hy
    rw [commutator_element_inv]
    exact closures_iterated_closure A B
      ((Subgroup.closure A).inv_mem hx) ((Subgroup.closure B).inv_mem hy)
  · exact iterated_relative_commutator A B

end Edmonton
end Towers
