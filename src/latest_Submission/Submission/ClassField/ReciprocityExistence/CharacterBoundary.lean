import Submission.ClassField.ReciprocityExistence.CyclicCharacter
import Submission.ClassField.LocalReciprocity.CharacterBoundary
import Submission.ClassField.LocalBrauer.CyclicCarryCocycle

/-!
# The cyclic character boundary as a carry class

This file begins the cochain-level comparison required in the converse of
Lemma VII.8.5.  It first exposes `delta chi` as the literal connecting map
for `0 -> Z -> Q -> Q/Z -> 0`, then specializes the normalized cyclic
character to `Multiplicative (ZMod n)`.
-/

namespace Submission.CField.RExist

open CategoryTheory Rep
open Submission.CField.Shifting
open Submission.CField.LRecip
open Submission.CField.LBrauer

noncomputable section

variable (G : Type) [Group G] [Fintype G]

/-- The definition of `characterBoundary` is exactly the connecting map on
the degree-one cocycle represented by the character. -/
theorem character_boundary_connecting
    (chi : RationalCharacter G) :
    characterBoundary G chi =
      groupCohomology.δ (sequence_short_exact G)
        1 2 rfl
        (groupCohomology.H1π (Rep.trivial ℤ G rationalModIntegers)
          ((groupCohomology.cocycles₁IsoOfIsTrivial
            (Rep.trivial ℤ G rationalModIntegers)).inv
              (characterRationalIntegers G chi))) := by
  rfl

section Cyclic

variable (n : ℕ) [NeZero n]

private theorem zmodMultiplicative_generator
    (z : Multiplicative (ZMod n)) :
    z ∈ Subgroup.zpowers (Multiplicative.ofAdd (1 : ZMod n)) := by
  refine ⟨(z.toAdd.val : ℤ), ?_⟩
  change (Multiplicative.ofAdd (1 : ZMod n)) ^ (z.toAdd.val : ℤ) = z
  rw [zpow_natCast]
  apply Multiplicative.toAdd.injective
  simp

/-- Forgetting the two notation wrappers recovers the additive group of
`ZMod n`. -/
def additiveMultiplicativeZ :
    Additive (Multiplicative (ZMod n)) ≃+ ZMod n where
  toFun z := z.toMul.toAdd
  invFun z := Additive.ofMul (Multiplicative.ofAdd z)
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

/-- The injective character on the standard cyclic group, normalized at
the standard generator. -/
noncomputable def standardCyclicCharacter :
    RationalCharacter (Multiplicative (ZMod n)) :=
  (zmodRationalCharacter n).comp
    (additiveMultiplicativeZ n).toAddMonoidHom

theorem standard_character_injective :
    Function.Injective (standardCyclicCharacter n) :=
  (zmod_character_injective n).comp
    (additiveMultiplicativeZ n).injective

@[simp]
theorem standard_cyclic_character
    (z : Additive (Multiplicative (ZMod n))) :
    standardCyclicCharacter n z =
      (((z.toMul.toAdd.val : ℕ) / n : ℚ) : AddCircle (1 : ℚ)) := by
  rw [standardCyclicCharacter, AddMonoidHom.comp_apply,
    additiveMultiplicativeZ]
  exact zmod_rational_character n z.toMul.toAdd

/-- The integral two-cocycle recording addition with carry in `ZMod n`. -/
def standardCarryCocycle :
    groupCohomology.cocycles₂
      (Rep.trivial ℤ (Multiplicative (ZMod n)) ℤ) :=
  ⟨fun p ↦ (CCarry.carry p.1.toAdd p.2.toAdd : ℤ), by
    rw [groupCohomology.mem_cocycles₂_iff]
    intro g h j
    change ((CCarry.carry (g.toAdd + h.toAdd) j.toAdd +
          CCarry.carry g.toAdd h.toAdd : ℕ) : ℤ) =
      ((CCarry.carry h.toAdd j.toAdd +
          CCarry.carry g.toAdd (h.toAdd + j.toAdd) : ℕ) : ℤ)
    exact_mod_cast CCarry.carry_cocycle g.toAdd h.toAdd j.toAdd⟩

/-- The preferred rational lift of the standard cyclic character. -/
def standardCyclicLift
    (g : Multiplicative (ZMod n)) : ℚ :=
  (g.toAdd.val : ℚ) / n

private theorem standard_cyclic_rational
    (g : Multiplicative (ZMod n)) :
    (rationalIntegers (Multiplicative (ZMod n))).hom
        (standardCyclicLift n g) =
      characterRationalIntegers (Multiplicative (ZMod n))
        (standardCyclicCharacter n) (Additive.ofMul g) := by
  apply rationalIntegersInvariant.injective
  change rationalIntegersInvariant
      (Submodule.Quotient.mk ((g.toAdd.val : ℚ) / n)) =
    rationalIntegersInvariant
      (rationalIntegersInvariant.symm
        (standardCyclicCharacter n (Additive.ofMul g)))
  rw [rational_integers_mk,
    AddEquiv.apply_symm_apply]
  exact (standard_cyclic_character n (Additive.ofMul g)).symm

private theorem standard_lift_coboundary
    (g h : Multiplicative (ZMod n)) :
    (integerToRational (Multiplicative (ZMod n))).hom
        ((standardCarryCocycle n :
          Multiplicative (ZMod n) × Multiplicative (ZMod n) → ℤ) (g, h)) =
      groupCohomology.d₁₂ (Rep.trivial ℤ (Multiplicative (ZMod n)) ℚ)
        (standardCyclicLift n) (g, h) := by
  change ((CCarry.carry g.toAdd h.toAdd : ℕ) : ℚ) =
    (h.toAdd.val : ℚ) / n - ((g.toAdd + h.toAdd).val : ℚ) / n +
      (g.toAdd.val : ℚ) / n
  have hcarry := CCarry.val_add_carry g.toAdd h.toAdd
  have hn : (n : ℚ) ≠ 0 := by exact_mod_cast NeZero.ne n
  have hcarryQ :
      ((g.toAdd + h.toAdd).val : ℚ) +
          (n : ℚ) * (CCarry.carry g.toAdd h.toAdd : ℚ) =
        (g.toAdd.val : ℚ) + (h.toAdd.val : ℚ) := by
    exact_mod_cast hcarry
  field_simp
  linarith

/-- The boundary of the normalized injective cyclic character is represented
by the integral carry cocycle. -/
theorem character_boundary_rational :
    characterBoundary (Multiplicative (ZMod n))
        (standardCyclicCharacter n) =
      groupCohomology.H2π
        (Rep.trivial ℤ (Multiplicative (ZMod n)) ℤ)
        (standardCarryCocycle n) := by
  rw [character_boundary_connecting]
  let G := Multiplicative (ZMod n)
  let X := integerRationalSequence G
  letI : X.X₃.IsTrivial := by
    dsimp [X, integerRationalSequence]
    infer_instance
  let z : groupCohomology.cocycles₁ X.X₃ :=
    (groupCohomology.cocycles₁IsoOfIsTrivial X.X₃).inv
      (characterRationalIntegers G
        (standardCyclicCharacter n))
  let y : G → X.X₂ := standardCyclicLift n
  let x : G × G → X.X₁ := fun p ↦
    (standardCarryCocycle n : G × G → ℤ) p
  have hy : X.g.hom ∘ y = z := by
    funext g
    dsimp [X, y, z]
    change (rationalIntegers G).hom
        (standardCyclicLift n g) =
      characterRationalIntegers G
        (standardCyclicCharacter n) (Additive.ofMul g)
    exact standard_cyclic_rational n g
  have hx : X.f.hom ∘ x = groupCohomology.d₁₂ X.X₂ y := by
    funext p
    exact standard_lift_coboundary n p.1 p.2
  have hdelta := groupCohomology.δ₁_apply
    (sequence_short_exact G) z y hy x hx
  simpa [G, X, z, y, x] using hdelta

end Cyclic

end

end Submission.CField.RExist
