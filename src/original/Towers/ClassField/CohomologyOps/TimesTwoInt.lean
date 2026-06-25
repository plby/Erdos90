import Mathlib.LinearAlgebra.FreeModule.ModN

/-!
# Milne, Class Field Theory, Remark II.1.26

Inverse limits of abelian groups need not be exact.  We give the standard
equalizer counterexample.  Consider the pointwise-surjective morphism of
parallel pairs

`(ℤ ⇉ ℤ, 0, 2) ⟶ (ZMod 2 ⇉ ZMod 2, 0, 0)`

whose two components are reduction modulo two.  The source equalizer is zero,
whereas the target equalizer is all of `ZMod 2`, so the induced map on inverse
limits is not surjective.
-/

namespace Towers.CField.COps

noncomputable section

/-- Multiplication by two, viewed as a `ℤ`-linear endomorphism of `ℤ`. -/
def timesTwoInt : ℤ →ₗ[ℤ] ℤ :=
  2 • LinearMap.id

/-- Reduction modulo two as a `ℤ`-linear map. -/
def reduceModTwo : ℤ →ₗ[ℤ] ZMod 2 :=
  (Int.castAddHom (ZMod 2)).toIntLinearMap

/-- The equalizer of the source parallel pair `0, 2 : ℤ ⇉ ℤ`. -/
abbrev sourceEqualizer : Type :=
  LinearMap.ker timesTwoInt

/-- The equalizer of the target parallel pair `0, 0 : ZMod 2 ⇉ ZMod 2`. -/
abbrev targetEqualizer : Type :=
  LinearMap.ker (0 : ZMod 2 →ₗ[ℤ] ZMod 2)

/-- Both squares in the morphism of parallel pairs commute; the nontrivial
one says that reduction modulo two kills twice every integer. -/
theorem reduce_mod_times (x : ℤ) :
    reduceModTwo (timesTwoInt x) = 0 := by
  change ((2 * x : ℤ) : ZMod 2) = 0
  rw [Int.cast_mul]
  have htwo : ((2 : ℤ) : ZMod 2) = 0 :=
    ZMod.intCast_eq_zero_iff_even.mpr (by norm_num)
  rw [htwo, zero_mul]

/-- The map on equalizers induced by reduction modulo two. -/
def equalizerReduction : sourceEqualizer →ₗ[ℤ] targetEqualizer where
  toFun x := ⟨reduceModTwo x.1, by simp⟩
  map_add' _ _ := by ext; simp
  map_smul' c x := by
    apply Subtype.ext
    exact reduceModTwo.map_smul c x.1

/-- Each component of the morphism of parallel pairs is surjective. -/
theorem reduce_mod_surjective : Function.Surjective reduceModTwo := by
  intro x
  obtain ⟨x, rfl⟩ := ZMod.intCast_surjective x
  exact ⟨x, rfl⟩

/-- The equalizer of `0, 2 : ℤ ⇉ ℤ` is trivial. -/
theorem source_equalizer_zero (x : sourceEqualizer) : x = 0 := by
  apply Subtype.ext
  have hx := x.2
  change 2 * x.1 = 0 at hx
  exact (mul_eq_zero.mp hx).resolve_left (by norm_num)

/-- **Remark II.1.26.** The inverse-limit map induced by a pointwise
surjective morphism of diagrams of abelian groups need not be surjective.
Consequently inverse limits are not exact in general. -/
theorem equalizer_not_surjective :
    ¬Function.Surjective equalizerReduction := by
  intro h
  let one : targetEqualizer := ⟨1, by simp⟩
  obtain ⟨x, hx⟩ := h one
  rw [source_equalizer_zero x] at hx
  have : (0 : ZMod 2) = 1 := congrArg Subtype.val hx
  exact zero_ne_one this

end

end Towers.CField.COps
