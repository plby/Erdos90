import Submission.ClassField.ReciprocityExistence.MultiplicativeCup

/-!
# Additivity of the multiplicative character cup

The canonical lift of a sum of rational characters need not be the sum of
their canonical lifts.  Their difference is integer-valued, however, and
its coboundary shows that the corresponding multiplicative cup cocycles are
cohomologous.  Thus the cup class is additive in the character variable.
-/

namespace Submission.CField.RExist

open Submission.CField.CProduca

noncomputable section

universe u v

variable {G : Type u} [CommGroup G]

private theorem rational_character_integer
    (χ ψ : CharacterModule (Additive G)) (g : G) :
    ∃ z : ℤ, (z : ℚ) =
      rationalCharacterLift (χ + ψ) g -
        rationalCharacterLift χ g - rationalCharacterLift ψ g := by
  let q := rationalCharacterLift (χ + ψ) g -
    rationalCharacterLift χ g - rationalCharacterLift ψ g
  have hq : (q : AddCircle (1 : ℚ)) = 0 := by
    change ((rationalCharacterLift (χ + ψ) g -
      rationalCharacterLift χ g - rationalCharacterLift ψ g : ℚ) :
        AddCircle (1 : ℚ)) = 0
    rw [AddCircle.coe_sub, AddCircle.coe_sub,
      rational_character_coe, rational_character_coe,
      rational_character_coe]
    change (χ + ψ) (Additive.ofMul g) - χ (Additive.ofMul g) -
      ψ (Additive.ofMul g) = 0
    change (χ (Additive.ofMul g) + ψ (Additive.ofMul g)) -
      χ (Additive.ofMul g) - ψ (Additive.ofMul g) = 0
    abel
  obtain ⟨z, hz⟩ := (AddCircle.coe_eq_zero_iff (1 : ℚ)).1 hq
  refine ⟨z, ?_⟩
  simpa [q] using hz

/-- The integer by which the canonical lift of `χ + ψ` differs from the
sum of the two canonical lifts. -/
private noncomputable def rationalCharacterCorrection
    (χ ψ : CharacterModule (Additive G)) (g : G) : ℤ :=
  Classical.choose (rational_character_integer χ ψ g)

private theorem rational_character_spec
    (χ ψ : CharacterModule (Additive G)) (g : G) :
    (rationalCharacterCorrection χ ψ g : ℚ) =
      rationalCharacterLift (χ + ψ) g -
        rationalCharacterLift χ g - rationalCharacterLift ψ g :=
  Classical.choose_spec (rational_character_integer χ ψ g)

private theorem rational_boundary_add
    (χ ψ : CharacterModule (Additive G)) (g h : G) :
    rationalBoundaryExponent (χ + ψ) g h =
      rationalBoundaryExponent χ g h +
        rationalBoundaryExponent ψ g h +
          rationalCharacterCorrection χ ψ h -
          rationalCharacterCorrection χ ψ (g * h) +
          rationalCharacterCorrection χ ψ g := by
  have hq :
      ((rationalBoundaryExponent (χ + ψ) g h : ℤ) : ℚ) =
        ((rationalBoundaryExponent χ g h +
          rationalBoundaryExponent ψ g h +
          rationalCharacterCorrection χ ψ h -
          rationalCharacterCorrection χ ψ (g * h) +
          rationalCharacterCorrection χ ψ g : ℤ) : ℚ) := by
    simp only [Int.cast_add, Int.cast_sub,
      rational_boundary_spec,
      rational_character_spec]
    ring
  exact_mod_cast hq

/-- The literal multiplicative cup class is additive in its rational
character argument. -/
@[simp]
theorem invariant_cup_add
    {M : Type v} [CommGroup M] [MulDistribMulAction G M]
    (x : M) (hx : ∀ g : G, g • x = x)
    (χ ψ : CharacterModule (Additive G)) :
    invariantCharacterCup x hx (χ + ψ) =
      invariantCharacterCup x hx χ *
        invariantCharacterCup x hx ψ := by
  rw [invariantCharacterCup, invariantCharacterCup,
    invariantCharacterCup, ← MHTwo.mk_mul]
  apply (MHTwo.mk_eq_iff _ _).2
  refine ⟨fun g ↦ x ^ rationalCharacterCorrection χ ψ g, ?_⟩
  intro g h
  change
    g • x ^ rationalCharacterCorrection χ ψ h /
          x ^ rationalCharacterCorrection χ ψ (g * h) *
        x ^ rationalCharacterCorrection χ ψ g =
      x ^ rationalBoundaryExponent (χ + ψ) g h /
        (x ^ rationalBoundaryExponent χ g h *
          x ^ rationalBoundaryExponent ψ g h)
  rw [smul_zpow', hx]
  rw [rational_boundary_add]
  simp only [div_eq_mul_inv, ← zpow_neg, ← zpow_add]
  congr 1
  omega

/-- The zero rational character gives the neutral cup class. -/
@[simp]
theorem invariant_character_cup
    {M : Type v} [CommGroup M] [MulDistribMulAction G M]
    (x : M) (hx : ∀ g : G, g • x = x) :
    invariantCharacterCup x hx
        (0 : CharacterModule (Additive G)) = 1 := by
  let c := invariantCharacterCup x hx
      (0 : CharacterModule (Additive G))
  have h : c = c * c := by
    simpa [c] using invariant_cup_add x hx
      (0 : CharacterModule (Additive G)) 0
  apply mul_left_cancel (a := c)
  simpa using h.symm

end

end Submission.CField.RExist
