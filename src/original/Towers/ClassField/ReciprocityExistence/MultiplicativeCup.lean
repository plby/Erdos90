import Mathlib.Algebra.Module.CharacterModule
import Towers.ClassField.CrossedProducts.CohomologyClass

/-!
# The multiplicative cup cocycle in Lemma VII.8.5

For a character `chi : G -> Q/Z`, choose its canonical rational lift in
`[0,1)`.  Its integral coboundary is the normalized cocycle

`n(g,h) = lift(chi h) - lift(chi (gh)) + lift(chi g)`.

If `x` is a `G`-invariant coefficient, Milne's cup class is represented
literally by `(g,h) |-> x ^ n(g,h)`.  This multiplicative presentation is
universe-polymorphic, unlike the current categorical cup-product API.
-/

namespace Towers.CField.RExist

open Towers.CField.CProduca

noncomputable section

universe u v

variable {G : Type u} [Group G]

/-- The canonical representative in `[0,1)` of the value of a rational
character. -/
noncomputable def rationalCharacterLift
    (chi : Additive G →+ AddCircle (1 : ℚ)) (g : G) : ℚ :=
  (AddCircle.equivIco (1 : ℚ) 0 (chi (Additive.ofMul g))).1

theorem rational_character_ico
    (chi : Additive G →+ AddCircle (1 : ℚ)) (g : G) :
    rationalCharacterLift chi g ∈ Set.Ico (0 : ℚ) 1 := by
  simpa only [zero_add, rationalCharacterLift] using
    (AddCircle.equivIco (1 : ℚ) 0
      (chi (Additive.ofMul g))).2

@[simp]
theorem rational_character_coe
    (chi : Additive G →+ AddCircle (1 : ℚ)) (g : G) :
    ((rationalCharacterLift chi g : ℚ) : AddCircle (1 : ℚ)) =
      chi (Additive.ofMul g) := by
  exact (AddCircle.equivIco (1 : ℚ) 0).symm_apply_apply
    (chi (Additive.ofMul g))

@[simp]
theorem rational_character_lift
    (chi : Additive G →+ AddCircle (1 : ℚ)) :
    rationalCharacterLift chi 1 = 0 := by
  have hzero : (0 : ℚ) ∈ Set.Ico (0 : ℚ) (0 + 1) := by norm_num
  change (AddCircle.equivIco (1 : ℚ) 0
    (chi (Additive.ofMul (1 : G)))).1 = 0
  rw [show Additive.ofMul (1 : G) = 0 by rfl, map_zero]
  exact congrArg Subtype.val
    (AddCircle.equivIco_coe_eq hzero)

private theorem rational_coboundary_integer
    (chi : Additive G →+ AddCircle (1 : ℚ)) (g h : G) :
    ∃ z : ℤ, (z : ℚ) =
      rationalCharacterLift chi h - rationalCharacterLift chi (g * h) +
        rationalCharacterLift chi g := by
  let q := rationalCharacterLift chi h -
    rationalCharacterLift chi (g * h) + rationalCharacterLift chi g
  have hq : (q : AddCircle (1 : ℚ)) = 0 := by
    change ((rationalCharacterLift chi h -
        rationalCharacterLift chi (g * h) +
          rationalCharacterLift chi g : ℚ) : AddCircle (1 : ℚ)) = 0
    rw [AddCircle.coe_add, AddCircle.coe_sub,
      rational_character_coe, rational_character_coe,
      rational_character_coe]
    change chi (Additive.ofMul h) - chi (Additive.ofMul (g * h)) +
      chi (Additive.ofMul g) = 0
    rw [show Additive.ofMul (g * h) =
      Additive.ofMul g + Additive.ofMul h by rfl, map_add]
    abel
  obtain ⟨z, hz⟩ := (AddCircle.coe_eq_zero_iff (1 : ℚ)).1 hq
  refine ⟨z, ?_⟩
  simpa [q] using hz

/-- The integral two-coboundary of the canonical rational lift of `chi`. -/
noncomputable def rationalBoundaryExponent
    (chi : Additive G →+ AddCircle (1 : ℚ)) (g h : G) : ℤ :=
  Classical.choose (rational_coboundary_integer chi g h)

theorem rational_boundary_spec
    (chi : Additive G →+ AddCircle (1 : ℚ)) (g h : G) :
    (rationalBoundaryExponent chi g h : ℚ) =
      rationalCharacterLift chi h - rationalCharacterLift chi (g * h) +
        rationalCharacterLift chi g :=
  Classical.choose_spec (rational_coboundary_integer chi g h)

@[simp]
theorem rational_boundary_left
    (chi : Additive G →+ AddCircle (1 : ℚ)) (g : G) :
    rationalBoundaryExponent chi 1 g = 0 := by
  have hq : ((rationalBoundaryExponent chi 1 g : ℤ) : ℚ) = 0 := by
    rw [rational_boundary_spec]
    simp
  exact_mod_cast hq

@[simp]
theorem rational_character_boundary
    (chi : Additive G →+ AddCircle (1 : ℚ)) (g : G) :
    rationalBoundaryExponent chi g 1 = 0 := by
  have hq : ((rationalBoundaryExponent chi g 1 : ℤ) : ℚ) = 0 := by
    rw [rational_boundary_spec]
    simp
  exact_mod_cast hq

/-- The exponent is an additive two-cocycle. -/
theorem rational_boundary_cocycle
    (chi : Additive G →+ AddCircle (1 : ℚ)) (g h j : G) :
    rationalBoundaryExponent chi (g * h) j +
        rationalBoundaryExponent chi g h =
      rationalBoundaryExponent chi h j +
        rationalBoundaryExponent chi g (h * j) := by
  have hq :
      ((rationalBoundaryExponent chi (g * h) j +
          rationalBoundaryExponent chi g h : ℤ) : ℚ) =
        ((rationalBoundaryExponent chi h j +
          rationalBoundaryExponent chi g (h * j) : ℤ) : ℚ) := by
    simp only [Int.cast_add, rational_boundary_spec]
    rw [mul_assoc]
    ring
  exact_mod_cast hq

variable {M : Type v} [CommGroup M] [MulDistribMulAction G M]

/-- Milne's literal cocycle `(g,h) |-> x ^ n(g,h)` for an invariant
coefficient `x`. -/
noncomputable def invariantCupCocycle
    (x : M) (hx : ∀ g : G, g • x = x)
    (chi : Additive G →+ AddCircle (1 : ℚ)) :
    NMCocycl₂ (G := G) (M := M) where
  toFun p := x ^ rationalBoundaryExponent chi p.1 p.2
  isMulCocycle₂ g h j := by
    rw [show g • x ^ rationalBoundaryExponent chi h j =
        x ^ rationalBoundaryExponent chi h j by
      rw [smul_zpow', hx]]
    rw [← zpow_add, ← zpow_add,
      rational_boundary_cocycle]
  map_one_fst g := by simp
  map_one_snd g := by simp

/-- The multiplicative `H²` class of Milne's literal cup cocycle. -/
noncomputable def invariantCharacterCup
    (x : M) (hx : ∀ g : G, g • x = x)
    (chi : Additive G →+ AddCircle (1 : ℚ)) : MHTwo G M :=
  MHTwo.mk (invariantCupCocycle x hx chi)

theorem invariant_cup_cocycle
    (x y : M) (hx : ∀ g : G, g • x = x)
    (hy : ∀ g : G, g • y = y)
    (chi : Additive G →+ AddCircle (1 : ℚ)) :
    invariantCupCocycle (x * y)
        (fun g => by rw [smul_mul', hx g, hy g]) chi =
      invariantCupCocycle x hx chi *
        invariantCupCocycle y hy chi := by
  apply NMCocycl₂.ext
  rintro ⟨g, h⟩
  change (x * y) ^ rationalBoundaryExponent chi g h =
    x ^ rationalBoundaryExponent chi g h *
      y ^ rationalBoundaryExponent chi g h
  exact mul_zpow x y _

@[simp]
theorem invariant_cup_mul
    (x y : M) (hx : ∀ g : G, g • x = x)
    (hy : ∀ g : G, g • y = y)
    (chi : Additive G →+ AddCircle (1 : ℚ)) :
    invariantCharacterCup (x * y)
        (fun g => by rw [smul_mul', hx g, hy g]) chi =
      invariantCharacterCup x hx chi *
        invariantCharacterCup y hy chi := by
  rw [invariantCharacterCup, invariantCharacterCup,
    invariantCharacterCup, invariant_cup_cocycle,
    MHTwo.mk_mul]

@[simp]
theorem invariant_cup_class
    (chi : Additive G →+ AddCircle (1 : ℚ)) :
    invariantCharacterCup (1 : M) (fun g => smul_one g) chi = 1 := by
  change MHTwo.mk
      (invariantCupCocycle (1 : M) (fun g => smul_one g) chi) =
    MHTwo.mk 1
  congr 1
  apply NMCocycl₂.ext
  rintro ⟨g, h⟩
  simp [invariantCupCocycle]

end

end Towers.CField.RExist
