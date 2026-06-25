import Towers.Group.Petresco.CommutatorProducts

/-!
# Petresco's 1954 paper: commutator bounds

This file formalizes Propositions 5.6 and 5.7. The proofs use closure
induction, the same algebraic content as Petresco's collection argument.
-/

namespace Towers
namespace Edmonton
namespace P1954

open scoped commutatorElement

universe u

variable {G : Type u} [Group G]

/-- A normalized target containing `[X,H]` and `[Y,H]` also contains
`[X ⊔ Y,H]`. -/
lemma commutator_sup_normalized
    {X Y H N : Subgroup G}
    (hXH : X ≤ H) (hYH : Y ≤ H)
    (hN : H ≤ Subgroup.normalizer (N : Set G))
    (hX : ⁅X, H⁆ ≤ N) (hY : ⁅Y, H⁆ ≤ N) :
    ⁅X ⊔ Y, H⁆ ≤ N := by
  have hclosureH :
      Subgroup.closure ((X : Set G) ∪ (Y : Set G)) ≤ H := by
    rw [← Subgroup.sup_eq_closure]
    exact sup_le hXH hYH
  rw [Subgroup.commutator_le]
  intro x hx y hy
  rw [Subgroup.sup_eq_closure] at hx
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
      rcases hx with hx | hx
      · exact hX (Subgroup.commutator_mem_commutator hx hy)
      · exact hY (Subgroup.commutator_mem_commutator hx hy)
  | one =>
      simp
  | mul x z hx hz ihx ihz =>
      have hconj :
          hallConjugate (hallCommutator z⁻¹ y⁻¹) x⁻¹ ∈ N := by
        have hraw : x * ⁅z, y⁆ * x⁻¹ ∈ N :=
          (Subgroup.mem_normalizer_iff.mp (hN (hclosureH hx)) _).mp ihz
        simpa [hallConjugate, commutator_element_inv] using hraw
      have ihx' : hallCommutator x⁻¹ y⁻¹ ∈ N := by
        rw [← commutator_element_inv]
        exact ihx
      rw [commutator_element_inv, mul_inv_rev,
        commutator_mul_left]
      exact N.mul_mem hconj ihx'
  | inv x hx ih =>
      have hconj :
          x⁻¹ * (⁅x, y⁆)⁻¹ * x ∈ N := by
        simpa using
          (Subgroup.mem_normalizer_iff.mp
            (hN (H.inv_mem (hclosureH hx))) _).mp (N.inv_mem ih)
      simpa [commutatorElement_def, mul_assoc] using hconj

/-- **Petresco 5.6.** If `A* ≤ A`, then
`[A*, A ⊔ B] ≤ [A*,A][A,B]`. -/
theorem sup_internal_mixed
    {Astar A B : Subgroup G} (hAstar : Astar ≤ A) :
    ⁅Astar, A ⊔ B⁆ ≤ ⁅Astar, A⁆ ⊔ ⁅A, B⁆ := by
  let N : Subgroup G := ⁅Astar, A⁆ ⊔ ⁅A, B⁆
  have hclosureH :
      Subgroup.closure ((A : Set G) ∪ (B : Set G)) ≤ A ⊔ B := by
    rw [← Subgroup.sup_eq_closure]
  have hfirstA : ⁅Astar, A⁆ ≤ A :=
    (Subgroup.commutator_mono hAstar le_rfl).trans A.commutator_le_self
  have hA_normalizes : A ≤ Subgroup.normalizer (N : Set G) := by
    exact le_normalizer_sup
      (normalizer_commutator_right Astar A)
      (normalizer_commutator_left A B)
  have hB_normalizes : B ≤ Subgroup.normalizer (N : Set G) := by
    simpa [N] using normalizes_sup_commutator hfirstA
  have hnormalizes :
      A ⊔ B ≤ Subgroup.normalizer (N : Set G) :=
    sup_le hA_normalizes hB_normalizes
  rw [Subgroup.commutator_le]
  intro x hx y hy
  rw [Subgroup.sup_eq_closure] at hy
  induction hy using Subgroup.closure_induction with
  | mem y hy =>
      rcases hy with hy | hy
      · exact Subgroup.mem_sup_left
          (Subgroup.commutator_mem_commutator hx hy)
      · exact Subgroup.mem_sup_right
          (Subgroup.commutator_mem_commutator (hAstar hx) hy)
  | one =>
      simp
  | mul y z hy hz ihy ihz =>
      have hconj :
          hallConjugate (hallCommutator x⁻¹ z⁻¹) y⁻¹ ∈ N := by
        have hraw : y * ⁅x, z⁆ * y⁻¹ ∈ N :=
          (Subgroup.mem_normalizer_iff.mp
            (hnormalizes (hclosureH hy)) _).mp ihz
        simpa [hallConjugate, commutator_element_inv] using hraw
      have ihy' : hallCommutator x⁻¹ y⁻¹ ∈ N := by
        rw [← commutator_element_inv]
        exact ihy
      rw [commutator_element_inv, mul_inv_rev,
        commutator_mul_right]
      exact N.mul_mem ihy' hconj
  | inv y hy ih =>
      have hconj :
          y⁻¹ * (⁅x, y⁆)⁻¹ * y ∈ N := by
        simpa using
          (Subgroup.mem_normalizer_iff.mp
            (hnormalizes ((A ⊔ B).inv_mem (hclosureH hy))) _).mp
              (N.inv_mem ih)
      simpa [commutatorElement_def, mul_assoc] using hconj

set_option maxHeartbeats 2000000 in
-- The nested closure inductions and normalizer bounds need a larger elaboration budget.
/-- **Petresco 5.7.** If `A*` is normal in `A` and `B*` is normal in `B`,
then the commutator of `A*[A,B]B*` with `A ⊔ B` is bounded by
`[A*,A][A,B][B*,B]`. -/
theorem commutator_mixed_product
    {Astar A Bstar B : Subgroup G}
    (hAstar : Astar ≤ A) (hBstar : Bstar ≤ B)
    [(Astar.subgroupOf A).Normal] [(Bstar.subgroupOf B).Normal] :
    ⁅(Astar ⊔ ⁅A, B⁆) ⊔ Bstar, A ⊔ B⁆ ≤
      (⁅Astar, A⁆ ⊔ ⁅A, B⁆) ⊔ ⁅Bstar, B⁆ := by
  let H : Subgroup G := A ⊔ B
  let N : Subgroup G := (⁅Astar, A⁆ ⊔ ⁅A, B⁆) ⊔ ⁅Bstar, B⁆
  have hAA : ⁅Astar, A⁆ ≤ A :=
    (Subgroup.commutator_mono hAstar le_rfl).trans A.commutator_le_self
  have hBB : ⁅Bstar, B⁆ ≤ B :=
    (Subgroup.commutator_mono hBstar le_rfl).trans B.commutator_le_self
  letI : (⁅Astar, A⁆.subgroupOf A).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hAA]
    exact normalizer_commutator_right Astar A
  letI : (⁅Bstar, B⁆.subgroupOf B).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hBB]
    exact normalizer_commutator_right Bstar B
  have hNH : N ≤ H := by
    exact sup_le
      (sup_le (hAA.trans le_sup_left)
        ((Subgroup.commutator_mono le_sup_left le_sup_right).trans
          H.commutator_le_self))
      (hBB.trans le_sup_right)
  letI : (N.subgroupOf H).Normal := by
    simpa [N, H] using
      (sup_commutator_normal (Astar := ⁅Astar, A⁆) (Bstar := ⁅Bstar, B⁆)
        hAA hBB)
  have hnormalizes : H ≤ Subgroup.normalizer (N : Set G) :=
    Subgroup.le_normalizer_of_normal_subgroupOf hNH
  have hAstarH : Astar ≤ H := hAstar.trans le_sup_left
  have hcommH : ⁅A, B⁆ ≤ H :=
    (Subgroup.commutator_mono le_sup_left le_sup_right).trans
      H.commutator_le_self
  have hBstarH : Bstar ≤ H := hBstar.trans le_sup_right
  have hAstar_bound : ⁅Astar, H⁆ ≤ N := by
    change ⁅Astar, A ⊔ B⁆ ≤ N
    exact (sup_internal_mixed (B := B) hAstar).trans le_sup_left
  have hcomm_bound : ⁅⁅A, B⁆, H⁆ ≤ N := by
    have hleft : ⁅⁅A, B⁆, H⁆ ≤ ⁅A, B⁆ := by
      letI : (⁅A, B⁆.subgroupOf H).Normal := by
        simpa [H] using commutator_sup A B
      exact commutator_left_subgroup hcommH
    have htarget : ⁅A, B⁆ ≤ N := le_sup_right.trans le_sup_left
    exact hleft.trans htarget
  have hBstar_bound : ⁅Bstar, H⁆ ≤ N := by
    have htarget : ⁅Bstar, B⁆ ⊔ ⁅B, A⁆ ≤ N := by
      apply sup_le
      · exact le_sup_right
      · rw [Subgroup.commutator_comm B A]
        exact le_sup_right.trans le_sup_left
    change ⁅Bstar, A ⊔ B⁆ ≤ N
    rw [sup_comm A B]
    exact (sup_internal_mixed (Astar := Bstar) (A := B) (B := A) hBstar).trans
      htarget
  have hleft :
      ⁅Astar ⊔ ⁅A, B⁆, H⁆ ≤ N :=
    commutator_sup_normalized
      (X := Astar) (Y := ⁅A, B⁆) (H := H) (N := N)
      hAstarH hcommH hnormalizes hAstar_bound hcomm_bound
  exact commutator_sup_normalized
    (X := Astar ⊔ ⁅A, B⁆) (Y := Bstar) (H := H) (N := N)
    (sup_le hAstarH hcommH) hBstarH hnormalizes hleft hBstar_bound

end P1954
end Edmonton
end Towers
