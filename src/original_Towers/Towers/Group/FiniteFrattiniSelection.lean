import Mathlib

/-!
# Elementary finite Frattini selection helpers

This file isolates finite-group and additive-span facts used by arithmetic
pro-`p` presentation scaffolds.  These lemmas do not depend on the Zassenhaus
theorem umbrella.
-/

namespace Towers
namespace FFSelect

universe u

/-- A convenient explicit maximality predicate for proper subgroups. -/
def MaximalSubgroup {G : Type u} [Group G] (M : Subgroup G) : Prop :=
  M ≠ ⊤ ∧ ∀ K : Subgroup G, M < K → K = ⊤

lemma subgroup_nat_card
    {G : Type u} [Group G] [Finite G]
    {H K : Subgroup G} (h : H < K) :
    Nat.card H < Nat.card K := by
  classical
  letI : Fintype H := Fintype.ofFinite H
  letI : Fintype K := Fintype.ofFinite K
  let f : H → K := fun x => ⟨x.1, h.1 x.2⟩
  have hf_inj : Function.Injective f := by
    intro a b hab
    exact
      Subtype.ext
        (show (a : G) = b from congrArg (fun x : K => (x : G)) hab)
  have hnotle : ¬ K ≤ H := not_le_of_gt h
  have hex : ∃ g : G, g ∈ K ∧ g ∉ H := by
    by_contra hnone
    apply hnotle
    intro g hgK
    by_contra hgH
    exact hnone ⟨g, hgK, hgH⟩
  rcases hex with ⟨g, hgK, hgH⟩
  have hf_not_surj : ¬ Function.Surjective f := by
    intro hsurj
    rcases hsurj ⟨g, hgK⟩ with ⟨y, hy⟩
    apply hgH
    have hyval : (y : G) = g := by
      simpa [f] using congrArg Subtype.val hy
    simpa [hyval] using y.2
  have hcard : Fintype.card H < Fintype.card K :=
    Fintype.card_lt_of_injective_not_surjective f hf_inj hf_not_surj
  simpa [Nat.card_eq_fintype_card] using hcard

lemma maximal_subgroup
    {G : Type u} [Group G] [Finite G]
    {H : Subgroup G} (hH : H ≠ ⊤) :
    ∃ M : Subgroup G, H ≤ M ∧ MaximalSubgroup M := by
  classical
  letI : Fintype (Subgroup G) := Fintype.ofFinite (Subgroup G)
  let A : Finset (Subgroup G) :=
    Finset.univ.filter (fun K => H ≤ K ∧ K ≠ ⊤)
  have hHmem : H ∈ A := by
    simp [A, hH]
  let B : Finset ℕ := A.image (fun K : Subgroup G => Nat.card K)
  have hBnon : B.Nonempty := by
    refine ⟨Nat.card H, ?_⟩
    exact Finset.mem_image.mpr ⟨H, hHmem, rfl⟩
  let m : ℕ := B.max' hBnon
  have hmB : m ∈ B := Finset.max'_mem B hBnon
  rcases Finset.mem_image.mp hmB with ⟨M, hMA, hMcard⟩
  have hMAprop : H ≤ M ∧ M ≠ ⊤ := by
    simpa [A] using hMA
  refine ⟨M, hMAprop.1, ?_⟩
  constructor
  · exact hMAprop.2
  · intro K hMK
    by_contra hKtop
    have hKmem : K ∈ A := by
      simp [A, hKtop, le_trans hMAprop.1 hMK.le]
    have hKcard_le : Nat.card K ≤ Nat.card M := by
      have hKB : Nat.card K ∈ B :=
        Finset.mem_image.mpr ⟨K, hKmem, rfl⟩
      have hle : Nat.card K ≤ m := Finset.le_max' B (Nat.card K) hKB
      simpa [hMcard] using hle
    have hcard_lt : Nat.card M < Nat.card K :=
      subgroup_nat_card hMK
    exact (not_lt_of_ge hKcard_le) hcard_lt

lemma finite_pgroup_normalizer
    {p : ℕ} {G : Type u} [Group G] [Finite G]
    [Fact (Nat.Prime p)] (hPG : IsPGroup p G)
    {H : Subgroup G} (hH : H ≠ ⊤) :
    H < Subgroup.normalizer (H : Set G) := by
  classical
  have hHlt : H < ⊤ := lt_of_le_of_ne le_top hH
  haveI : Group.IsNilpotent G := hPG.isNilpotent
  exact Group.normalizerCondition_of_isNilpotent H hHlt

lemma maximal_normal_pgroup
    {p : ℕ} {G : Type u} [Group G] [Finite G]
    [Fact (Nat.Prime p)] (hPG : IsPGroup p G)
    {M : Subgroup G} (hM : MaximalSubgroup M) :
    M.Normal := by
  classical
  have hlt : M < Subgroup.normalizer (M : Set G) :=
    finite_pgroup_normalizer (p := p) hPG (H := M) hM.1
  have htop : Subgroup.normalizer (M : Set G) = ⊤ :=
    hM.2 (Subgroup.normalizer (M : Set G)) hlt
  exact Subgroup.normalizer_eq_top_iff.mp htop

lemma mul_span_closure
    {p : ℕ} {A : Type u} [CommGroup A]
    [Module (ZMod p) (Additive A)]
    (S : Set A) {a : A} (ha : a ∈ Subgroup.closure S) :
    Additive.ofMul a ∈
      Submodule.span (ZMod p) (Additive.ofMul '' S) := by
  let W : Submodule (ZMod p) (Additive A) :=
    Submodule.span (ZMod p) (Additive.ofMul '' S)
  let H : Subgroup A :=
    { carrier := {a : A | Additive.ofMul a ∈ W}
      one_mem' := by
        change Additive.ofMul (1 : A) ∈ W
        simp
      mul_mem' := by
        intro x y hx hy
        change Additive.ofMul (x * y) ∈ W
        simpa using W.add_mem hx hy
      inv_mem' := by
        intro x hx
        change Additive.ofMul x⁻¹ ∈ W
        simpa using W.neg_mem hx }
  have hle : Subgroup.closure S ≤ H := by
    refine (Subgroup.closure_le H).2 ?_
    intro x hx
    change Additive.ofMul x ∈ W
    exact Submodule.subset_span ⟨x, hx, rfl⟩
  change a ∈ H
  exact hle ha

lemma span_top_closure
    {p : ℕ} {A : Type u} [CommGroup A]
    [Module (ZMod p) (Additive A)]
    {S : Set A} (hS : Subgroup.closure S = ⊤) :
    Submodule.span (ZMod p) (Additive.ofMul '' S) = ⊤ := by
  apply le_antisymm
  · exact le_top
  · intro x _hx
    induction x using Additive.rec with
    | ofMul a =>
        exact mul_span_closure (p := p) (S := S) (a := a) (by
          simp [hS])

end FFSelect
end Towers
