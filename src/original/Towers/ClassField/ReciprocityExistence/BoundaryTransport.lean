import Towers.ClassField.ReciprocityExistence.CharacterBoundary

/-!
# Transporting the cyclic character boundary

A chosen equivalence `Multiplicative (ZMod n) ≃* G` transports the normalized
cyclic character to `G`.  Its boundary is represented by the same carry
cocycle, with both arguments pulled back through the equivalence.
-/

namespace Towers.CField.RExist

open CategoryTheory Rep
open Towers.CField.Shifting
open Towers.CField.LRecip
open Towers.CField.LBrauer

noncomputable section

variable (n : ℕ) [NeZero n]
variable (G : Type) [Group G] [Fintype G]

/-- The normalized standard cyclic character transported to an isomorphic
group. -/
noncomputable def transportedStandardCharacter
    (e : Multiplicative (ZMod n) ≃* G) : RationalCharacter G :=
  (standardCyclicCharacter n).comp e.symm.toMonoidHom.toAdditive

omit [Fintype G] in
theorem transported_standard_injective
    (e : Multiplicative (ZMod n) ≃* G) :
    Function.Injective (transportedStandardCharacter n G e) :=
  (standard_character_injective n).comp e.symm.injective

/-- The carry cocycle transported from the standard cyclic model. -/
def transportedStandardCocycle
    (e : Multiplicative (ZMod n) ≃* G) :
    groupCohomology.cocycles₂ (Rep.trivial ℤ G ℤ) :=
  ⟨fun p ↦ (CCarry.carry (e.symm p.1).toAdd
      (e.symm p.2).toAdd : ℤ), by
    rw [groupCohomology.mem_cocycles₂_iff]
    intro g h j
    dsimp only
    simp only [map_mul, Representation.trivial_apply]
    change ((CCarry.carry
          ((e.symm g).toAdd + (e.symm h).toAdd) (e.symm j).toAdd +
        CCarry.carry (e.symm g).toAdd (e.symm h).toAdd : ℕ) : ℤ) =
      ((CCarry.carry (e.symm h).toAdd (e.symm j).toAdd +
        CCarry.carry (e.symm g).toAdd
          ((e.symm h).toAdd + (e.symm j).toAdd) : ℕ) : ℤ)
    exact_mod_cast CCarry.carry_cocycle
      (e.symm g).toAdd (e.symm h).toAdd (e.symm j).toAdd⟩

/-- The preferred rational lift of the transported cyclic character. -/
def transportedStandardLift
    (e : Multiplicative (ZMod n) ≃* G) (g : G) : ℚ :=
  ((e.symm g).toAdd.val : ℚ) / n

omit [Fintype G] in
private theorem transported_standard_cyclic
    (e : Multiplicative (ZMod n) ≃* G) (g : G) :
    (rationalIntegers G).hom
        (transportedStandardLift n G e g) =
      characterRationalIntegers G
        (transportedStandardCharacter n G e)
        (Additive.ofMul g) := by
  apply rationalIntegersInvariant.injective
  change rationalIntegersInvariant
      (Submodule.Quotient.mk (((e.symm g).toAdd.val : ℚ) / n)) =
    rationalIntegersInvariant
      (rationalIntegersInvariant.symm
        (standardCyclicCharacter n
          (Additive.ofMul (e.symm g))))
  rw [rational_integers_mk,
    AddEquiv.apply_symm_apply]
  exact (standard_cyclic_character n
    (Additive.ofMul (e.symm g))).symm

omit [Fintype G] in
private theorem transported_standard_coboundary
    (e : Multiplicative (ZMod n) ≃* G) (g h : G) :
    (integerToRational G).hom
        ((transportedStandardCocycle n G e : G × G → ℤ)
          (g, h)) =
      groupCohomology.d₁₂ (Rep.trivial ℤ G ℚ)
        (transportedStandardLift n G e) (g, h) := by
  dsimp only [transportedStandardCocycle,
    transportedStandardLift]
  change ((CCarry.carry (e.symm g).toAdd
        (e.symm h).toAdd : ℕ) : ℚ) =
    ((e.symm h).toAdd.val : ℚ) / n -
      ((e.symm (g * h)).toAdd.val : ℚ) / n +
      ((e.symm g).toAdd.val : ℚ) / n
  rw [map_mul]
  change ((CCarry.carry (e.symm g).toAdd
        (e.symm h).toAdd : ℕ) : ℚ) =
    ((e.symm h).toAdd.val : ℚ) / n -
      (((e.symm g).toAdd + (e.symm h).toAdd).val : ℚ) / n +
      ((e.symm g).toAdd.val : ℚ) / n
  have hcarry := CCarry.val_add_carry
    (e.symm g).toAdd (e.symm h).toAdd
  have hn : (n : ℚ) ≠ 0 := by exact_mod_cast NeZero.ne n
  have hcarryQ :
      ((((e.symm g).toAdd + (e.symm h).toAdd).val : ℚ) +
          (n : ℚ) *
            (CCarry.carry (e.symm g).toAdd
              (e.symm h).toAdd : ℚ)) =
        ((e.symm g).toAdd.val : ℚ) + ((e.symm h).toAdd.val : ℚ) := by
    exact_mod_cast hcarry
  field_simp
  linarith

/-- The boundary of the transported injective character is the transported
integral carry class. -/
theorem character_boundary_transported
    (e : Multiplicative (ZMod n) ≃* G) :
    characterBoundary G
        (transportedStandardCharacter n G e) =
      groupCohomology.H2π (Rep.trivial ℤ G ℤ)
        (transportedStandardCocycle n G e) := by
  rw [character_boundary_connecting]
  let X := integerRationalSequence G
  letI : X.X₃.IsTrivial := by
    dsimp [X, integerRationalSequence]
    infer_instance
  let z : groupCohomology.cocycles₁ X.X₃ :=
    (groupCohomology.cocycles₁IsoOfIsTrivial X.X₃).inv
      (characterRationalIntegers G
        (transportedStandardCharacter n G e))
  let y : G → X.X₂ := transportedStandardLift n G e
  let x : G × G → X.X₁ := fun p ↦
    (transportedStandardCocycle n G e : G × G → ℤ) p
  have hy : X.g.hom ∘ y = z := by
    funext g
    dsimp [X, y, z]
    change (rationalIntegers G).hom
        (transportedStandardLift n G e g) =
      characterRationalIntegers G
        (transportedStandardCharacter n G e)
          (Additive.ofMul g)
    exact transported_standard_cyclic n G e g
  have hx : X.f.hom ∘ x = groupCohomology.d₁₂ X.X₂ y := by
    funext p
    exact transported_standard_coboundary
      n G e p.1 p.2
  have hdelta := groupCohomology.δ₁_apply
    (sequence_short_exact G) z y hy x hx
  simpa [X, z, y, x] using hdelta

end

end Towers.CField.RExist
