import Towers.ClassField.Shifting.FiniteCardUnit

/-!
# The exact hexagon behind Herbrand-quotient multiplicativity

The six consecutive terms in the relevant long exact sequence form a cyclic
exact hexagon.  Applying Lemma II.3.7 to its image factorizations gives the
cardinality identity used in the proof of Herbrand multiplicativity.
-/

namespace Towers.CField.Shifting

open Function

noncomputable section

/-- An exact pair of maps between finite groups expresses the order of the
middle group as the product of the two image orders. -/
private theorem unit_range_mul
    {G₀ G₁ G₂ : Type*} [Group G₀] [Group G₁] [Group G₂]
    [Finite G₀] [Finite G₁] [Finite G₂]
    (f : G₀ →* G₁) (g : G₁ →* G₂) (h : MulExact f g) :
    groupCardUnit G₁ =
      groupCardUnit f.range * groupCardUnit g.range := by
  have hfactor : MulExact f.range.subtype g.rangeRestrict := by
    intro x
    constructor
    · intro hx
      have hx' : g x = 1 := congrArg Subtype.val hx
      obtain ⟨y, hy⟩ := (h x).mp hx'
      exact ⟨⟨x, ⟨y, hy⟩⟩, rfl⟩
    · rintro ⟨y, rfl⟩
      apply Subtype.ext
      exact (h y).mpr y.property
  have hcard := mul_short_exact
    f.range.subtype g.rangeRestrict Subtype.val_injective hfactor
      g.rangeRestrict_surjective
  apply Units.ext
  simp only [group_card_val, Units.val_mul]
  exact_mod_cast hcard

/-- The cardinality identity for a cyclic exact sequence of six finite groups.
No commutativity assumption on the groups is needed. -/
theorem unit_exact_hexagon
    {A₀ A₁ A₂ B₀ B₁ B₂ : Type*}
    [Group A₀] [Group A₁] [Group A₂]
    [Group B₀] [Group B₁] [Group B₂]
    [Finite A₀] [Finite A₁] [Finite A₂]
    [Finite B₀] [Finite B₁] [Finite B₂]
    (f₀ : A₀ →* A₁) (f₁ : A₁ →* A₂) (f₂ : A₂ →* B₀)
    (g₀ : B₀ →* B₁) (g₁ : B₁ →* B₂) (g₂ : B₂ →* A₀)
    (hA₁ : MulExact f₀ f₁) (hA₂ : MulExact f₁ f₂)
    (hB₀ : MulExact f₂ g₀) (hB₁ : MulExact g₀ g₁)
    (hB₂ : MulExact g₁ g₂) (hA₀ : MulExact g₂ f₀) :
    groupCardUnit A₁ * groupCardUnit B₀ * groupCardUnit B₂ =
      groupCardUnit A₀ * groupCardUnit A₂ * groupCardUnit B₁ := by
  rw [unit_range_mul f₀ f₁ hA₁,
    unit_range_mul f₁ f₂ hA₂,
    unit_range_mul f₂ g₀ hB₀,
    unit_range_mul g₀ g₁ hB₁,
    unit_range_mul g₁ g₂ hB₂,
    unit_range_mul g₂ f₀ hA₀]
  ac_rfl

/-! ## Additive form -/

/-- The nonzero rational number given by the order of a finite additive
group. -/
def addCardUnit (G : Type*) [AddGroup G] [Finite G] : ℚˣ :=
  Units.mk0 (Nat.card G : ℚ) (by exact_mod_cast (Nat.card_pos : 0 < Nat.card G).ne')

@[simp]
theorem card_unit_val (G : Type*) [AddGroup G] [Finite G] :
    (addCardUnit G : ℚ) = Nat.card G :=
  rfl

/-- Additive exact pairs satisfy the same image-order factorization. -/
theorem card_range_mul
    {G₀ G₁ G₂ : Type*} [AddGroup G₀] [AddGroup G₁] [AddGroup G₂]
    [Finite G₀] [Finite G₁] [Finite G₂]
    (f : G₀ →+ G₁) (g : G₁ →+ G₂) (h : Exact f g) :
    addCardUnit G₁ =
      addCardUnit f.range * addCardUnit g.range := by
  have hcard : Nat.card G₁ = Nat.card f.range * Nat.card g.range := by
    rw [AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup g.ker,
      Nat.card_congr (QuotientAddGroup.quotientKerEquivRange g).toEquiv,
      ← AddMonoidHom.exact_iff.mp h]
    exact Nat.mul_comm _ _
  apply Units.ext
  simp only [card_unit_val, Units.val_mul]
  exact_mod_cast hcard

/-- The order identity for a short exact sequence of finite additive groups. -/
theorem card_short_exact
    {G₀ G₁ G₂ : Type*} [AddGroup G₀] [AddGroup G₁] [AddGroup G₂]
    [Finite G₀] [Finite G₁] [Finite G₂]
    (f : G₀ →+ G₁) (g : G₁ →+ G₂)
    (hinj : Injective f) (hexact : Exact f g) (hsurj : Surjective g) :
    addCardUnit G₁ =
      addCardUnit G₀ * addCardUnit G₂ := by
  rw [card_range_mul f g hexact]
  congr 1
  · apply Units.ext
    simp only [card_unit_val]
    exact_mod_cast Nat.card_congr
      (Equiv.ofBijective f.rangeRestrict
        ⟨AddMonoidHom.rangeRestrict_injective_iff.mpr hinj,
          f.rangeRestrict_surjective⟩).symm
  · apply Units.ext
    simp only [card_unit_val]
    rw [AddMonoidHom.range_eq_top.mpr hsurj]
    exact_mod_cast Nat.card_congr (Equiv.Set.univ G₂)

/-- The additive cardinality identity for a cyclic exact sequence of six
finite additive groups.  The additive groups need not be commutative. -/
theorem card_exact_hexagon
    {A₀ A₁ A₂ B₀ B₁ B₂ : Type*}
    [AddGroup A₀] [AddGroup A₁] [AddGroup A₂]
    [AddGroup B₀] [AddGroup B₁] [AddGroup B₂]
    [Finite A₀] [Finite A₁] [Finite A₂]
    [Finite B₀] [Finite B₁] [Finite B₂]
    (f₀ : A₀ →+ A₁) (f₁ : A₁ →+ A₂) (f₂ : A₂ →+ B₀)
    (g₀ : B₀ →+ B₁) (g₁ : B₁ →+ B₂) (g₂ : B₂ →+ A₀)
    (hA₁ : Exact f₀ f₁) (hA₂ : Exact f₁ f₂)
    (hB₀ : Exact f₂ g₀) (hB₁ : Exact g₀ g₁)
    (hB₂ : Exact g₁ g₂) (hA₀ : Exact g₂ f₀) :
    addCardUnit A₁ * addCardUnit B₀ * addCardUnit B₂ =
      addCardUnit A₀ * addCardUnit A₂ *
        addCardUnit B₁ := by
  rw [card_range_mul f₀ f₁ hA₁,
    card_range_mul f₁ f₂ hA₂,
    card_range_mul f₂ g₀ hB₀,
    card_range_mul g₀ g₁ hB₁,
    card_range_mul g₁ g₂ hB₂,
    card_range_mul g₂ f₀ hA₀]
  ac_rfl

end

end Towers.CField.Shifting
