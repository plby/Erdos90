import Towers.Algebra.Magnus.MagnusInverse
import Towers.Group.LowerCentralStrong


/-!
# The Magnus homomorphism and its degree filtration

This file constructs the Magnus homomorphism
`FreeGroup X → (R⟪X⟫)ˣ`, sending `x` to `1 + x`, and proves the standard
easy half of the Magnus--Witt filtration statement: the `i`th lower
central term has Magnus expansion of order at least `i`.
-/

namespace EChapma
namespace MSeries

open scoped commutatorElement

variable {R X : Type*} [Ring R]

/-- Left multiplication preserves a lower bound on vanishing order. -/
theorem vanishes_below_right
    {g : MSeries R X} {n : ℕ} (hg : VanishesBelow g n)
    (f : MSeries R X) :
    VanishesBelow (f * g) n := by
  intro w hw
  induction w using FreeMonoid.inductionOn' generalizing f with
  | one =>
      have hg1 : g 1 = 0 := hg 1 hw
      simp [hg1]
  | mul_of x w ih =>
      rw [apply_of_mul]
      have hgw : g (FreeMonoid.of x * w) = 0 :=
        hg _ hw
      rw [hgw, MulZeroClass.mul_zero, zero_add]
      apply ih (shift x f)
      simp only [FreeMonoid.length_mul, FreeMonoid.length_of] at hw
      omega

/-- Right multiplication preserves a lower bound on vanishing order. -/
theorem vanishes_below_left
    {f : MSeries R X} {n : ℕ} (hf : VanishesBelow f n)
    (g : MSeries R X) :
    VanishesBelow (f * g) n := by
  induction n generalizing f with
  | zero => exact vanishesBelow_zero _
  | succ n ih =>
      intro w
      refine FreeMonoid.casesOn
        (C := fun w => w.length < n + 1 → (f * g) w = 0) w ?_ ?_
      · intro _
        have hf1 : f 1 = 0 := hf 1 (by simp)
        simp [hf1]
      · intro x v hw
        rw [apply_of_mul, hf 1 (by simp), MulZeroClass.zero_mul, zero_add]
        exact ih (f := shift x f) (shift_vanishesBelow hf x) v (by
          rw [FreeMonoid.length_mul, FreeMonoid.length_of] at hw
          omega)

/-- Multiplication adds vanishing orders. -/
theorem vanishes_below_add
    {f g : MSeries R X} {m n : ℕ}
    (hf : VanishesBelow f m) (hg : VanishesBelow g n) :
    VanishesBelow (f * g) (m + n) := by
  induction m generalizing f with
  | zero =>
      simpa using vanishes_below_right hg f
  | succ m ih =>
      intro w
      refine FreeMonoid.casesOn
        (C := fun w => w.length < m + 1 + n → (f * g) w = 0) w ?_ ?_
      · intro _
        have hf1 : f 1 = 0 := hf 1 (by simp)
        simp [hf1]
      · intro x v hw
        rw [apply_of_mul, hf 1 (by simp), MulZeroClass.zero_mul, zero_add]
        exact ih (f := shift x f) (shift_vanishesBelow hf x) v (by
          rw [FreeMonoid.length_mul, FreeMonoid.length_of] at hw
          omega)

/-- Series of order at least `n`, as an additive subgroup. -/
def orderLeastSubgroup (n : ℕ) :
    AddSubgroup (MSeries R X) where
  carrier := {f | VanishesBelow f n}
  zero_mem' := by simp [VanishesBelow]
  add_mem' {f g} hf hg := by
    intro w hw
    simp [hf w hw, hg w hw]
  neg_mem' {f} hf := by
    intro w hw
    simp [hf w hw]

@[simp]
theorem order_least_subgroup
    {f : MSeries R X} {n : ℕ} :
    f ∈ orderLeastSubgroup (R := R) (X := X) n ↔
      VanishesBelow f n :=
  Iff.rfl

/-- Series of order at least `n`, as a two-sided ideal. -/
def orderLeastIdeal (n : ℕ) : Ideal (MSeries R X) where
  carrier := {f | VanishesBelow f n}
  zero_mem' := by simp [VanishesBelow]
  add_mem' {f g} hf hg := by
    intro w hw
    simp [hf w hw, hg w hw]
  smul_mem' a f hf :=
    vanishes_below_right hf a

instance order_least_sided (n : ℕ) :
    (orderLeastIdeal (R := R) (X := X) n).IsTwoSided where
  mul_mem_of_left {_f} g hf :=
    vanishes_below_left hf g

@[simp]
theorem order_least_ideal
    {f : MSeries R X} {n : ℕ} :
    f ∈ orderLeastIdeal (R := R) (X := X) n ↔
      VanishesBelow f n :=
  Iff.rfl

theorem order_least_antitone :
    Antitone (orderLeastIdeal (R := R) (X := X)) := by
  intro m n hmn f hf w hw
  exact hf w (hw.trans_le hmn)

/-- The degree-one series represented by a generator. -/
noncomputable def variableSeries (x : X) : MSeries R X := by
  exact ⟨fun w =>
    @ite R (w = FreeMonoid.of x) (Classical.propDecidable _) 1 0⟩

theorem variable_series_ideal (x : X) :
    variableSeries (R := R) x ∈
      augmentationIdeal (R := R) (X := X) := by
  classical
  change variableSeries (R := R) x 1 = 0
  simp [variableSeries]

theorem variable_vanishes_below (x : X) :
    VanishesBelow (variableSeries (R := R) x) 1 := by
  intro w hw
  have hw1 : w = 1 := FreeMonoid.length_eq_zero.mp (by omega)
  subst w
  exact variable_series_ideal x

/-- The Magnus image of one free generator, bundled in `1 + d`. -/
noncomputable def magnusGenerator (x : X) :
    plusIdealSubgroup
      (augmentationIdeal (R := R) (X := X)) :=
  ⟨oneAddUnit (variableSeries (R := R) x)
      (variable_series_ideal x),
    by
      change (1 + variableSeries (R := R) x :
        MSeries R X) - 1 ∈
          augmentationIdeal (R := R) (X := X)
      simpa using variable_series_ideal x⟩

/-- The Magnus homomorphism `x ↦ 1+x`, with codomain bundled as the
subgroup of units congruent to one modulo the augmentation ideal. -/
noncomputable def magnusHom :
    FreeGroup X →*
      plusIdealSubgroup
        (augmentationIdeal (R := R) (X := X)) :=
  FreeGroup.lift (magnusGenerator (R := R))

/-- The underlying unit-valued Magnus homomorphism. -/
noncomputable def magnusUnitHom :
    FreeGroup X →* (MSeries R X)ˣ :=
  (plusIdealSubgroup
    (augmentationIdeal (R := R) (X := X))).subtype.comp
      (magnusHom (R := R) (X := X))

/-- The underlying formal series of the Magnus image. -/
noncomputable def magnusSeries (g : FreeGroup X) : MSeries R X :=
  (magnusUnitHom (R := R) (X := X) g :
    MSeries R X)

/-- The nonconstant part `μ(g)-1` of a Magnus expansion. -/
noncomputable def magnusDifference (g : FreeGroup X) : MSeries R X :=
  magnusSeries (R := R) g - 1

@[simp]
theorem magnusSeries_one :
    magnusSeries (R := R) (X := X) 1 = 1 := by
  simp [magnusSeries, magnusUnitHom]

@[simp]
theorem magnusSeries_mul (g h : FreeGroup X) :
    magnusSeries (R := R) (g * h) =
      magnusSeries (R := R) g * magnusSeries (R := R) h := by
  simp [magnusSeries, magnusUnitHom]

@[simp]
theorem magnusSeries_inv (g : FreeGroup X) :
    magnusSeries (R := R) g⁻¹ =
      ((((magnusUnitHom (R := R) (X := X) g)⁻¹ :
        (MSeries R X)ˣ)) : MSeries R X) := by
  simp [magnusSeries, magnusUnitHom]

@[simp]
theorem magnusSeries_of (x : X) :
    magnusSeries (R := R) (FreeGroup.of x) =
      1 + variableSeries (R := R) x := by
  change
    ((((magnusHom (R := R) (X := X) (FreeGroup.of x)).1 :
        (MSeries R X)ˣ)) : MSeries R X) =
        1 + variableSeries (R := R) x
  rw [magnusHom, FreeGroup.lift_apply_of]
  rfl

@[simp]
theorem magnusDifference_of (x : X) :
    magnusDifference (R := R) (FreeGroup.of x) =
      variableSeries (R := R) x := by
  simp [magnusDifference]

theorem magnus_difference_ideal (g : FreeGroup X) :
    magnusDifference (R := R) g ∈
      augmentationIdeal (R := R) (X := X) := by
  exact
    (magnusHom (R := R) (X := X) g).property

theorem magnus_vanishes_below (g : FreeGroup X) :
    VanishesBelow (magnusDifference (R := R) g) 1 := by
  intro w hw
  have hw1 : w = 1 := FreeMonoid.length_eq_zero.mp (by omega)
  subst w
  exact magnus_difference_ideal g

private theorem units_vanishes_below
    {u v : (MSeries R X)ˣ} {m n : ℕ}
    (hu : VanishesBelow ((u : MSeries R X) - 1) m)
    (hv : VanishesBelow ((v : MSeries R X) - 1) n) :
    VanishesBelow
      ((((⁅u, v⁆ : (MSeries R X)ˣ) :
          MSeries R X)) - 1) (m + n) := by
  let U : MSeries R X := (u : MSeries R X) - 1
  let V : MSeries R X := (v : MSeries R X) - 1
  let uInv : MSeries R X := ((u⁻¹ : (MSeries R X)ˣ) :
    MSeries R X)
  let vInv : MSeries R X := ((v⁻¹ : (MSeries R X)ˣ) :
    MSeries R X)
  have hUV : VanishesBelow (U * V) (m + n) :=
    vanishes_below_add hu hv
  have hVU : VanishesBelow (V * U) (m + n) := by
    simpa [Nat.add_comm] using vanishes_below_add hv hu
  have hsub : VanishesBelow (U * V - V * U) (m + n) := by
    intro w hw
    simp [hUV w hw, hVU w hw]
  have hright :
      VanishesBelow
        (((U * V - V * U) * uInv) * vInv) (m + n) :=
    vanishes_below_left
      (vanishes_below_left hsub
        uInv)
      vInv
  rw [show
      (((⁅u, v⁆ : (MSeries R X)ˣ) :
          MSeries R X)) - 1 =
        ((U * V - V * U) * uInv) * vInv by
    dsimp [U, V, uInv, vInv]
    rw [commutatorElement_def]
    simp only [Units.val_mul]
    have huu :
        (u : MSeries R X) *
            (((u⁻¹ : (MSeries R X)ˣ) :
              MSeries R X)) = 1 :=
      u.val_inv
    have hvv :
        (v : MSeries R X) *
            (((v⁻¹ : (MSeries R X)ˣ) :
              MSeries R X)) = 1 :=
      v.val_inv
    have hcancel :
        ((v : MSeries R X) * (u : MSeries R X) *
            (((u⁻¹ : (MSeries R X)ˣ) :
              MSeries R X)) *
          (((v⁻¹ : (MSeries R X)ˣ) :
            MSeries R X))) = 1 := by
      calc
        (v : MSeries R X) * (u : MSeries R X) *
              (((u⁻¹ : (MSeries R X)ˣ) :
                MSeries R X)) *
            (((v⁻¹ : (MSeries R X)ˣ) :
              MSeries R X)) =
            (v : MSeries R X) *
              ((u : MSeries R X) *
                (((u⁻¹ : (MSeries R X)ˣ) :
                  MSeries R X))) *
              (((v⁻¹ : (MSeries R X)ˣ) :
                MSeries R X)) := by
                  simp
        _ = (v : MSeries R X) * 1 *
              (((v⁻¹ : (MSeries R X)ˣ) :
                MSeries R X)) := by rw [huu]
        _ = 1 := by simp
    calc
      (u : MSeries R X) * (v : MSeries R X) *
              (((u⁻¹ : (MSeries R X)ˣ) :
                MSeries R X)) *
            (((v⁻¹ : (MSeries R X)ˣ) :
              MSeries R X)) - 1 =
          (u : MSeries R X) * (v : MSeries R X) *
                (((u⁻¹ : (MSeries R X)ˣ) :
                  MSeries R X)) *
              (((v⁻¹ : (MSeries R X)ˣ) :
                MSeries R X)) -
            ((v : MSeries R X) * (u : MSeries R X) *
                (((u⁻¹ : (MSeries R X)ˣ) :
                  MSeries R X)) *
              (((v⁻¹ : (MSeries R X)ˣ) :
                MSeries R X))) := by rw [hcancel]
      _ = (((u : MSeries R X) - 1) *
              ((v : MSeries R X) - 1) -
            ((v : MSeries R X) - 1) *
              ((u : MSeries R X) - 1)) *
            (((u⁻¹ : (MSeries R X)ˣ) :
              MSeries R X)) *
          (((v⁻¹ : (MSeries R X)ˣ) :
            MSeries R X)) := by noncomm_ring]
  exact hright

/-- Commutators add Magnus vanishing orders. -/
theorem magnus_difference_vanishes
    {g h : FreeGroup X} {m n : ℕ}
    (hg : VanishesBelow (magnusDifference (R := R) g) m)
    (hh : VanishesBelow (magnusDifference (R := R) h) n) :
    VanishesBelow
      (magnusDifference (R := R) ⁅g, h⁆) (m + n) := by
  simpa [magnusDifference, magnusSeries, magnusUnitHom,
    map_commutatorElement] using
    units_vanishes_below
      (u := magnusUnitHom (R := R) (X := X) g)
      (v := magnusUnitHom (R := R) (X := X) h) hg hh

/-- The subgroup of free-group elements whose Magnus difference has
order at least `n`. -/
noncomputable def magnusOrderSubgroup (n : ℕ) :
    Subgroup (FreeGroup X) where
  carrier := {g | VanishesBelow (magnusDifference (R := R) g) n}
  one_mem' := by simp [magnusDifference, VanishesBelow]
  mul_mem' {g h} hg hh := by
    have hidentity :
        magnusDifference (R := R) (g * h) =
          magnusDifference (R := R) g +
            magnusSeries (R := R) g *
              magnusDifference (R := R) h := by
      simp only [magnusDifference, magnusSeries_mul]
      noncomm_ring
    change VanishesBelow (magnusDifference (R := R) (g * h)) n
    rw [hidentity]
    intro w hw
    simp [hg w hw,
      vanishes_below_right hh
        (magnusSeries (R := R) g) w hw]
  inv_mem' {g} hg := by
    have hidentity :
        magnusDifference (R := R) g⁻¹ =
          -(magnusSeries (R := R) g⁻¹) *
            magnusDifference (R := R) g := by
      simp only [magnusDifference, magnusSeries_inv]
      let uInv : MSeries R X :=
        ((((magnusUnitHom (R := R) (X := X) g)⁻¹ :
          (MSeries R X)ˣ)) : MSeries R X)
      have hunit :
          uInv *
              magnusSeries (R := R) g = 1 :=
        (magnusUnitHom (R := R) (X := X) g).inv_val
      change
        uInv - 1 =
          -uInv * (magnusSeries (R := R) g - 1)
      calc
        uInv - 1 =
            uInv -
              uInv *
                magnusSeries (R := R) g := by rw [hunit]
        _ = -uInv *
              (magnusSeries (R := R) g - 1) := by
                noncomm_ring
    change VanishesBelow (magnusDifference (R := R) g⁻¹) n
    rw [hidentity]
    exact vanishes_below_right hg _

@[simp]
theorem magnus_order_subgroup
    {g : FreeGroup X} {n : ℕ} :
    g ∈ magnusOrderSubgroup (R := R) (X := X) n ↔
      VanishesBelow (magnusDifference (R := R) g) n :=
  Iff.rfl

theorem magnus_order_one :
    magnusOrderSubgroup (R := R) (X := X) 1 = ⊤ := by
  apply top_unique
  intro g _
  exact magnus_vanishes_below g

/-- The Magnus-order filtration is a descending central series. -/
theorem magnus_descending_series :
    Subgroup.IsDescendingCentralSeries
      (fun n => magnusOrderSubgroup (R := R) (X := X) (n + 1)) := by
  constructor
  · exact magnus_order_one
  · intro g n hg h
    simpa [Nat.add_assoc] using
      magnus_difference_vanishes hg
        (magnus_vanishes_below h)

/-- The easy Magnus--Witt inclusion:
`γ_(n+1)(F) ⊆ μ⁻¹(1+d^(n+1))`. -/
theorem lower_magnus_subgroup (n : ℕ) :
    Subgroup.lowerCentralSeries (FreeGroup X) n ≤
      magnusOrderSubgroup (R := R) (X := X) (n + 1) :=
  Subgroup.descending_central_series_ge_lower
    (fun i => magnusOrderSubgroup (R := R) (X := X) (i + 1))
    magnus_descending_series n

end MSeries
end EChapma
