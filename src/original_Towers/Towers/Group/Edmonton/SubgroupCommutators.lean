import Towers.Group.Edmonton.CommutatorIdentities

/-!
# The Edmonton Notes on Nilpotent Groups: subgroup commutators

This file formalizes Hall's Lemmas 2.2 and 2.3.
-/

namespace Towers
namespace Edmonton

open Group
open scoped commutatorElement Pointwise

universe u

variable {G : Type u} [Group G]

/-- Hall's subgroup `X̄ = X [X,Y]`. -/
def commutatorExtensionLeft (X Y : Subgroup G) : Subgroup G :=
  X ⊔ ⁅X, Y⁆

/-- Hall's subgroup `Ȳ = Y [X,Y]`. -/
def commutatorExtensionRight (X Y : Subgroup G) : Subgroup G :=
  Y ⊔ ⁅X, Y⁆

/-- An element of the right input conjugates the left input into
`X ⊔ [X,Y]`. -/
lemma conjugate_extension_right
    {X Y : Subgroup G} {g h : G} (hg : g ∈ Y)
    (hh : h ∈ commutatorExtensionLeft X Y) :
    g * h * g⁻¹ ∈ commutatorExtensionLeft X Y := by
  rw [commutatorExtensionLeft, Subgroup.sup_eq_closure] at hh ⊢
  refine Subgroup.closure_induction ?_ ?_ ?_ ?_ hh
  · rintro x (hx | hx)
    · have hc : ⁅g, x⁆ ∈ ⁅X, Y⁆ := by
        rw [Subgroup.commutator_comm X Y]
        exact Subgroup.commutator_mem_commutator hg hx
      have hprod :
          ⁅g, x⁆ * x ∈
            Subgroup.closure ((X : Set G) ∪ ((⁅X, Y⁆ : Subgroup G) : Set G)) :=
        (Subgroup.closure
          ((X : Set G) ∪ ((⁅X, Y⁆ : Subgroup G) : Set G))).mul_mem
          (Subgroup.subset_closure (Set.mem_union_right _ hc))
          (Subgroup.subset_closure (Set.mem_union_left _ hx))
      simpa [commutatorElement_def, mul_assoc] using hprod
    · exact
        Subgroup.subset_closure
          (Set.mem_union_right _
            (conjugate_commutator_right hg hx))
  · simp
  · intro a b _ _ ha hb
    rw [← conj_mul]
    exact
      (Subgroup.closure
        ((X : Set G) ∪ ((⁅X, Y⁆ : Subgroup G) : Set G))).mul_mem ha hb
  · intro a _ ha
    rw [← conj_inv]
    exact
      (Subgroup.closure
        ((X : Set G) ∪ ((⁅X, Y⁆ : Subgroup G) : Set G))).inv_mem ha

/-- The right input normalizes `X ⊔ [X,Y]`. -/
lemma normalizer_extension_right (X Y : Subgroup G) :
    Y ≤ Subgroup.normalizer (commutatorExtensionLeft X Y : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · exact conjugate_extension_right hg
  · intro hconj
    have hback :=
      conjugate_extension_right (Y.inv_mem hg) hconj
    simpa [mul_assoc] using hback

/-- `X ⊔ [X,Y]` is normal in `X ⊔ Y`. -/
theorem commutator_normal_sup (X Y : Subgroup G) :
    ((commutatorExtensionLeft X Y).subgroupOf (X ⊔ Y)).Normal := by
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer]
  · exact sup_le
      ((le_sup_left.trans Subgroup.le_normalizer))
      (normalizer_extension_right X Y)
  · exact sup_le le_sup_left
      (Subgroup.commutator_mono le_sup_left le_sup_right
        |>.trans (X ⊔ Y).commutator_le_self)

/-- `Y ⊔ [X,Y]` is normal in `X ⊔ Y`. -/
theorem commutator_extension_sup (X Y : Subgroup G) :
    ((commutatorExtensionRight X Y).subgroupOf (X ⊔ Y)).Normal := by
  have h := commutator_normal_sup Y X
  rw [sup_comm Y X] at h
  simpa [commutatorExtensionRight, commutatorExtensionLeft,
    Subgroup.commutator_comm Y X] using h

/-- Hall's enlarged subgroups still generate `X ⊔ Y`. -/
theorem commutator_extensions_sup (X Y : Subgroup G) :
    commutatorExtensionLeft X Y ⊔ commutatorExtensionRight X Y = X ⊔ Y := by
  apply le_antisymm
  · exact sup_le
      (sup_le le_sup_left
        (Subgroup.commutator_mono le_sup_left le_sup_right
          |>.trans (X ⊔ Y).commutator_le_self))
      (sup_le le_sup_right
        (Subgroup.commutator_mono le_sup_left le_sup_right
          |>.trans (X ⊔ Y).commutator_le_self))
  · exact sup_le
      (le_sup_left.trans le_sup_left)
      (le_sup_left.trans le_sup_right)

/-- Hall's literal product formula
`X ⊔ Y = (X ⊔ [X,Y]) (Y ⊔ [X,Y])`. -/
theorem commutator_extensions_mul (X Y : Subgroup G) :
    ((X ⊔ Y : Subgroup G) : Set G) =
      (commutatorExtensionLeft X Y : Set G) *
        (commutatorExtensionRight X Y : Set G) := by
  have hleft_le :
      commutatorExtensionLeft X Y ≤ X ⊔ Y :=
    sup_le le_sup_left
      (Subgroup.commutator_mono le_sup_left le_sup_right
        |>.trans (X ⊔ Y).commutator_le_self)
  have hright_le :
      commutatorExtensionRight X Y ≤ X ⊔ Y :=
    sup_le le_sup_right
      (Subgroup.commutator_mono le_sup_left le_sup_right
        |>.trans (X ⊔ Y).commutator_le_self)
  letI : ((commutatorExtensionRight X Y).subgroupOf (X ⊔ Y)).Normal :=
    commutator_extension_sup X Y
  have hnormalizer :
      commutatorExtensionLeft X Y ≤
        Subgroup.normalizer (commutatorExtensionRight X Y : Set G) :=
    hleft_le.trans (Subgroup.le_normalizer_of_normal_subgroupOf hright_le)
  rw [← commutator_extensions_sup X Y,
    Subgroup.coe_mul_of_left_le_normalizer_right _ _ hnormalizer]

/-- **Hall, Lemma 2.2.** The commutator and the two enlarged input
subgroups are normal in `X ⊔ Y`, and the enlarged subgroups generate it. -/
theorem commutator_extensions_generate (X Y : Subgroup G) :
    (⁅X, Y⁆.subgroupOf (X ⊔ Y)).Normal ∧
      ((commutatorExtensionLeft X Y).subgroupOf (X ⊔ Y)).Normal ∧
      ((commutatorExtensionRight X Y).subgroupOf (X ⊔ Y)).Normal ∧
      commutatorExtensionLeft X Y ⊔ commutatorExtensionRight X Y = X ⊔ Y ∧
      ((X ⊔ Y : Subgroup G) : Set G) =
        (commutatorExtensionLeft X Y : Set G) *
          (commutatorExtensionRight X Y : Set G) :=
  ⟨commutator_sup X Y, commutator_normal_sup X Y,
    commutator_extension_sup X Y, commutator_extensions_sup X Y,
    commutator_extensions_mul X Y⟩

/-- The subgroup commutator distributes over a supremum of normal subgroups
in its left input. -/
theorem commutator_sup_left
    (H K L : Subgroup G) [H.Normal] [K.Normal] [L.Normal] :
    ⁅H ⊔ K, L⁆ = ⁅H, L⁆ ⊔ ⁅K, L⁆ := by
  apply le_antisymm
  · rw [Subgroup.commutator_le]
    intro x hx z hz
    obtain ⟨h, hh, k, hk, rfl⟩ :=
      Subgroup.mem_sup_of_normal_right.mp hx
    have hk_comm : ⁅k, z⁆ ∈ ⁅K, L⁆ :=
      Subgroup.commutator_mem_commutator hk hz
    have h_comm : ⁅h, z⁆ ∈ ⁅H, L⁆ :=
      Subgroup.commutator_mem_commutator hh hz
    have hconj : h * ⁅k, z⁆ * h⁻¹ ∈ ⁅K, L⁆ :=
      (inferInstance : (⁅K, L⁆ : Subgroup G).Normal).conj_mem _ hk_comm _
    have hprod :
        (h * ⁅k, z⁆ * h⁻¹) * ⁅h, z⁆ ∈ ⁅H, L⁆ ⊔ ⁅K, L⁆ :=
      (⁅H, L⁆ ⊔ ⁅K, L⁆).mul_mem
        (Subgroup.mem_sup_right hconj) (Subgroup.mem_sup_left h_comm)
    simpa [commutatorElement_def, mul_assoc] using hprod
  · exact sup_le
      (Subgroup.commutator_mono le_sup_left le_rfl)
      (Subgroup.commutator_mono le_sup_right le_rfl)

/-- Pointwise-product form of the commutator distribution identity. -/
theorem commutator_sup_mul
    (H K L : Subgroup G) [H.Normal] [K.Normal] [L.Normal] :
    ((⁅H ⊔ K, L⁆ : Subgroup G) : Set G) =
      ((⁅H, L⁆ : Subgroup G) : Set G) * ((⁅K, L⁆ : Subgroup G) : Set G) := by
  rw [commutator_sup_left H K L, Subgroup.mul_normal]

/-- **Hall, Lemma 2.3.** If `H`, `K`, and `L` are normal in `G`, then
`[H,K]` is normal and `[H K,L] = [H,L] [K,L]`. -/
theorem normal_commutator_sup
    (H K L : Subgroup G) [H.Normal] [K.Normal] [L.Normal] :
    (⁅H, K⁆ : Subgroup G).Normal ∧
      ⁅H ⊔ K, L⁆ = ⁅H, L⁆ ⊔ ⁅K, L⁆ ∧
      ((⁅H ⊔ K, L⁆ : Subgroup G) : Set G) =
        ((⁅H, L⁆ : Subgroup G) : Set G) * ((⁅K, L⁆ : Subgroup G) : Set G) :=
  ⟨inferInstance, commutator_sup_left H K L,
    commutator_sup_mul H K L⟩

end Edmonton
end Towers
