import Towers.Group.Petresco.NormalClosures

/-!
# Petresco's 1954 paper: products involving a subgroup commutator

This file formalizes Propositions 5.1--5.5 of Petresco's
*Sur les commutateurs* in subgroup and pointwise-product form.
-/

namespace Towers
namespace Edmonton
namespace P1954

open scoped commutatorElement Pointwise

universe u

variable {G : Type u} [Group G]

/-- If a subgroup normalizes each of two subgroups, it normalizes their
supremum. -/
lemma le_normalizer_sup
    {X H K : Subgroup G}
    (hH : X ≤ Subgroup.normalizer (H : Set G))
    (hK : X ≤ Subgroup.normalizer (K : Set G)) :
    X ≤ Subgroup.normalizer ((H ⊔ K : Subgroup G) : Set G) :=
  (le_inf hH hK).trans
    (Subgroup.normalizer_inf_normalizer_le_normalizer_sup H K)

/-- Elementwise form of Petresco 5.3. Conjugation by `B` preserves
`A* [A,B]` whenever `A* ≤ A`. -/
lemma conjugate_commutator_product
    {Astar A B : Subgroup G} (hAstar : Astar ≤ A)
    {g x : G} (hg : g ∈ B) (hx : x ∈ Astar ⊔ ⁅A, B⁆) :
    g * x * g⁻¹ ∈ Astar ⊔ ⁅A, B⁆ := by
  rw [Subgroup.sup_eq_closure] at hx ⊢
  refine Subgroup.closure_induction ?_ ?_ ?_ ?_ hx
  · rintro x (hx | hx)
    · have hc : ⁅g, x⁆ ∈ ⁅A, B⁆ := by
        rw [Subgroup.commutator_comm A B]
        exact Subgroup.commutator_mem_commutator hg (hAstar hx)
      have hprod :
          ⁅g, x⁆ * x ∈
            Subgroup.closure
              ((Astar : Set G) ∪ ((⁅A, B⁆ : Subgroup G) : Set G)) :=
        (Subgroup.closure
          ((Astar : Set G) ∪ ((⁅A, B⁆ : Subgroup G) : Set G))).mul_mem
          (Subgroup.subset_closure (Set.mem_union_right _ hc))
          (Subgroup.subset_closure (Set.mem_union_left _ hx))
      simpa [commutatorElement_def, mul_assoc] using hprod
    · exact Subgroup.subset_closure
        (Set.mem_union_right _
          (conjugate_commutator_right hg hx))
  · simp
  · intro a b _ _ ha hb
    rw [← conj_mul]
    exact
      (Subgroup.closure
        ((Astar : Set G) ∪ ((⁅A, B⁆ : Subgroup G) : Set G))).mul_mem ha hb
  · intro a _ ha
    rw [← conj_inv]
    exact
      (Subgroup.closure
        ((Astar : Set G) ∪ ((⁅A, B⁆ : Subgroup G) : Set G))).inv_mem ha

/-- **Petresco 5.3.** If `A* ≤ A`, then `B` normalizes `A*[A,B]`. -/
theorem normalizes_sup_commutator
    {Astar A B : Subgroup G} (hAstar : Astar ≤ A) :
    B ≤ Subgroup.normalizer (Astar ⊔ ⁅A, B⁆ : Subgroup G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · exact conjugate_commutator_product hAstar hg
  · intro hx
    have hback :=
      conjugate_commutator_product hAstar (B.inv_mem hg) hx
    simpa [mul_assoc] using hback

/-- **Petresco 5.1, literal product form.** The subgroup represented by
`A*[A,B]B*` has carrier equal to the corresponding threefold pointwise
product. -/
theorem coe_sup_set
    {Astar A Bstar B : Subgroup G}
    (hAstar : Astar ≤ A) (hBstar : Bstar ≤ B) :
    ((((Astar ⊔ ⁅A, B⁆) ⊔ Bstar : Subgroup G) : Set G)) =
      (Astar : Set G) * (⁅A, B⁆ : Subgroup G) * (Bstar : Set G) := by
  rw [Subgroup.coe_mul_of_right_le_normalizer_left
    (Astar ⊔ ⁅A, B⁆) Bstar
    (hBstar.trans (normalizes_sup_commutator hAstar))]
  rw [Subgroup.coe_mul_of_left_le_normalizer_right
    Astar ⁅A, B⁆
    (hAstar.trans (normalizer_commutator_left A B))]

/-- **Petresco 5.2.** If `A*` is normal in `A` and `B*` is normal in `B`,
then `A*[A,B]B*` is normal in `A ⊔ B`. -/
theorem sup_commutator_normal
    {Astar A Bstar B : Subgroup G}
    (hAstar : Astar ≤ A) (hBstar : Bstar ≤ B)
    [(Astar.subgroupOf A).Normal] [(Bstar.subgroupOf B).Normal] :
    ((((Astar ⊔ ⁅A, B⁆) ⊔ Bstar).subgroupOf (A ⊔ B))).Normal := by
  let E : Subgroup G := (Astar ⊔ ⁅A, B⁆) ⊔ Bstar
  have hcomm : ⁅A, B⁆ ≤ A ⊔ B :=
    (Subgroup.commutator_mono le_sup_left le_sup_right).trans
      (A ⊔ B).commutator_le_self
  have hEH : E ≤ A ⊔ B := by
    exact sup_le (sup_le (hAstar.trans le_sup_left) hcomm)
      (hBstar.trans le_sup_right)
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer hEH]
  have hA_astar : A ≤ Subgroup.normalizer Astar :=
    Subgroup.le_normalizer_of_normal_subgroupOf hAstar
  have hA_right :
      A ≤ Subgroup.normalizer ((⁅A, B⁆ ⊔ Bstar : Subgroup G) : Set G) := by
    simpa [Subgroup.commutator_comm A B, sup_comm] using
      (normalizes_sup_commutator hBstar)
  have hA_E : A ≤ Subgroup.normalizer E := by
    have h :=
      le_normalizer_sup hA_astar hA_right
    simpa [E, sup_assoc] using h
  have hB_left :
      B ≤ Subgroup.normalizer ((Astar ⊔ ⁅A, B⁆ : Subgroup G) : Set G) :=
    normalizes_sup_commutator hAstar
  have hB_bstar : B ≤ Subgroup.normalizer Bstar :=
    Subgroup.le_normalizer_of_normal_subgroupOf hBstar
  have hB_E : B ≤ Subgroup.normalizer E :=
    le_normalizer_sup hB_left hB_bstar
  exact sup_le hA_E hB_E

/-- **Petresco 5.4.** If `A* ≤ A`, then `A*[A,G]` is normal in `G`. -/
theorem sup_commutator_top
    {Astar A : Subgroup G} (hAstar : Astar ≤ A) :
    (Astar ⊔ ⁅A, (⊤ : Subgroup G)⁆ : Subgroup G).Normal := by
  apply Subgroup.normalizer_eq_top_iff.mp
  exact top_unique (normalizes_sup_commutator hAstar)

/-- **Petresco 5.5.** Every subgroup between `[A,G]` and a normal subgroup
`A` is itself normal. -/
theorem normal_of_le
    {Astar A : Subgroup G} (_hA : A.Normal)
    (hcomm : ⁅A, (⊤ : Subgroup G)⁆ ≤ Astar) (hAstar : Astar ≤ A) :
    Astar.Normal := by
  have hnormal := sup_commutator_top hAstar
  rwa [sup_eq_left.mpr hcomm] at hnormal

end P1954
end Edmonton
end Towers
