import Mathlib.Algebra.BigOperators.Group.List.Lemmas
import Mathlib.Algebra.Exact
import Mathlib.Data.List.OfFn
import Mathlib.GroupTheory.Index

/-!
# Milne, Class Field Theory, Lemma II.3.7

An exact sequence of finite groups has trivial alternating product of its
orders.  We use units of `ℚ` for the alternating product, so that division is
honest rather than truncated natural-number division.
-/

namespace Towers.CField.Shifting

open Function

noncomputable section

/-- The nonzero rational number given by the order of a finite group. -/
def groupCardUnit (G : Type*) [Group G] [Finite G] : ℚˣ :=
  Units.mk0 (Nat.card G : ℚ) (by exact_mod_cast (Nat.card_pos : 0 < Nat.card G).ne')

@[simp]
theorem group_card_val (G : Type*) [Group G] [Finite G] :
    (groupCardUnit G : ℚ) = Nat.card G :=
  rfl

/-- The cardinality identity attached to an exact pair of maps. -/
private theorem card_eq_range
    {G₀ G₁ G₂ : Type*} [Group G₀] [Group G₁] [Group G₂]
    [Finite G₀] [Finite G₁] [Finite G₂]
    (f : G₀ →* G₁) (g : G₁ →* G₂) (h : MulExact f g) :
    Nat.card G₁ = Nat.card f.range * Nat.card g.range := by
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup g.ker,
    Nat.card_congr (QuotientGroup.quotientKerEquivRange g).toEquiv,
    ← MonoidHom.mulExact_iff.mp h]
  exact Nat.mul_comm _ _

private theorem card_range_injective
    {G H : Type*} [Group G] [Group H] [Finite G] [Finite H]
    (f : G →* H) (hf : Injective f) : Nat.card f.range = Nat.card G := by
  exact Nat.card_congr
    (Equiv.ofBijective f.rangeRestrict
      ⟨MonoidHom.rangeRestrict_injective_iff.mpr hf, f.rangeRestrict_surjective⟩).symm

private theorem card_range_surjective
    {G H : Type*} [Group G] [Group H] [Finite G] [Finite H]
    (f : G →* H) (hf : Surjective f) : Nat.card f.range = Nat.card H := by
  rw [MonoidHom.range_eq_top.mpr hf]
  exact Nat.card_congr (Equiv.Set.univ H)

/-- The short-exact-sequence case of Lemma II.3.7. -/
theorem mul_short_exact
    {G₀ G₁ G₂ : Type*} [Group G₀] [Group G₁] [Group G₂]
    [Finite G₀] [Finite G₁] [Finite G₂]
    (f : G₀ →* G₁) (g : G₁ →* G₂)
    (hinj : Injective f) (hexact : MulExact f g) (hsurj : Surjective g) :
    Nat.card G₁ = Nat.card G₀ * Nat.card G₂ := by
  rw [card_eq_range f g hexact]
  congr 1
  · exact card_range_injective f hinj
  · exact card_range_surjective g hsurj

/-- Alternating adjacent products telescope. -/
private theorem alternatingProd_adjacent (c : ℕ → ℚˣ) (n : ℕ) :
    (List.ofFn fun i : Fin (n + 1) => c i * c (i + 1)).alternatingProd =
      c 0 * c (n + 1) ^ ((-1 : ℤ) ^ n) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [List.ofFn_succ']
      simp only [Fin.val_castSucc, Fin.val_last, List.concat_eq_append,
        List.alternatingProd_append, List.length_ofFn,
        List.alternatingProd_singleton, ih]
      simp only [pow_succ, mul_zpow]
      simp [zpow_neg, mul_assoc]

/-- A finite exact chain `A₀ → A₁ → ... → Aᵣ`, including exactness at both
ends.  The maps beyond `d (r - 1)` are ignored. -/
structure FEChain (r : ℕ) where
  obj : ℕ → Type*
  [group_obj : ∀ i, Group (obj i)]
  [finite_obj : ∀ i, Finite (obj i)]
  map : ∀ i, obj i →* obj (i + 1)
  positive : 0 < r
  injective_zero : Injective (map 0)
  exact : ∀ i, i + 1 < r → MulExact (map i) (map (i + 1))
  surjective_last : Surjective (map (r - 1))

attribute [instance] FEChain.group_obj FEChain.finite_obj

namespace FEChain

/-- The list of the orders of the groups in the chain, regarded as nonzero
rational numbers. -/
def cardinalityUnits {r : ℕ} (S : FEChain r) : List ℚˣ :=
  List.ofFn fun i : Fin (r + 1) => groupCardUnit (S.obj i)

/-- The auxiliary image orders in Milne's decomposition into short exact
sequences, with a trivial group inserted at each end. -/
private def imageCardUnit {r : ℕ} (S : FEChain r) (i : ℕ) : ℚˣ :=
  match i with
  | 0 => 1
  | i + 1 => if i < r then groupCardUnit (S.map i).range else 1

private theorem card_unit_adjacent {r : ℕ} (S : FEChain r)
    (i : ℕ) (hi : i ≤ r) :
    groupCardUnit (S.obj i) = S.imageCardUnit i * S.imageCardUnit (i + 1) := by
  cases i with
  | zero =>
      simp only [imageCardUnit, one_mul, if_pos S.positive]
      apply Units.ext
      simp only [group_card_val]
      exact_mod_cast (card_range_injective (S.map 0) S.injective_zero).symm
  | succ i =>
      by_cases hir : i + 1 = r
      · subst r
        simp only [imageCardUnit, Nat.lt_add_one_iff, le_refl, if_true,
          lt_self_iff_false, if_false, mul_one]
        apply Units.ext
        simp only [group_card_val]
        exact_mod_cast
          (card_range_surjective (S.map i) (by simpa using S.surjective_last)).symm
      · have hil : i + 1 < r := lt_of_le_of_ne hi hir
        have hi_map : i < r := lt_trans (Nat.lt_succ_self i) hil
        simp only [imageCardUnit, if_pos hi_map, if_pos hil]
        apply Units.ext
        simp only [group_card_val, Units.val_mul]
        exact_mod_cast card_eq_range (S.map i) (S.map (i + 1))
          (S.exact i hil)

/-- **Lemma II.3.7.** The alternating product of the orders in a finite exact
sequence is one. -/
theorem altern_cardi_units {r : ℕ} (S : FEChain r) :
    S.cardinalityUnits.alternatingProd = 1 := by
  rw [cardinalityUnits]
  have hlist :
      (List.ofFn fun i : Fin (r + 1) => groupCardUnit (S.obj i)) =
        List.ofFn fun i : Fin (r + 1) =>
          S.imageCardUnit i * S.imageCardUnit (i + 1) := by
    apply congrArg List.ofFn
    funext i
    exact S.card_unit_adjacent i (by omega)
  rw [hlist, alternatingProd_adjacent]
  simp [imageCardUnit]

/-- The source's displayed fraction, obtained by coercing the alternating
product to `ℚ`. -/
theorem altern_cardi_ratio {r : ℕ} (S : FEChain r) :
    ((S.cardinalityUnits.alternatingProd : ℚ) = 1) := by
  rw [S.altern_cardi_units]
  rfl

end FEChain

end

end Towers.CField.Shifting
