import Mathlib.GroupTheory.FiniteAbelian.Duality
import Mathlib.Algebra.Module.CharacterModule
import Submission.ClassField.LocalBrauer.LocalInvariantTorsion

/-!
# Finite rational-character double duality

For a finite abelian group `G`, evaluation identifies `G` with its double
dual of `ℚ/ℤ`-valued characters.  This is the universe-polymorphic duality
input needed to characterize the local Artin symbol directly by Proposition
III.3.6.
-/

namespace Submission.CField.LRecip

open Submission.CField.LBrauer

noncomputable section

/-- The `n`-torsion of `ℚ/ℤ`, written multiplicatively, is exactly the
subgroup of `n`th roots of unity. -/
noncomputable def torsionRootsUnity
    (n : ℕ) :
    Multiplicative (localInvariantTorsion n) ≃*
      rootsOfUnity n (Multiplicative LocalInvariant) where
  toFun x := ⟨toUnits (Multiplicative.ofAdd
      ((x.toAdd : localInvariantTorsion n) : LocalInvariant)), by
    rw [mem_rootsOfUnity]
    apply Units.ext
    change n • ((x.toAdd : localInvariantTorsion n) : LocalInvariant) = 0
    exact x.toAdd.property⟩
  invFun x := Multiplicative.ofAdd ⟨x.1.1.toAdd, by
    change x.1.1 ^ n = 1
    have hx := x.property
    change x.1 ^ n = 1 at hx
    exact congrArg Units.val hx⟩
  left_inv _ := rfl
  right_inv _ := by
    apply Subtype.ext
    exact toUnits_val_apply _
  map_mul' _ _ := by
    apply Subtype.ext
    apply Units.ext
    rfl

/-- `Multiplicative (ℚ/ℤ)` has enough `n`th roots of unity for every
positive `n`. -/
noncomputable instance enoughRootsUnity
    (n : ℕ) [NeZero n] :
    HasEnoughRootsOfUnity (Multiplicative LocalInvariant) n := by
  let e : rootsOfUnity n (Multiplicative LocalInvariant) ≃*
      Multiplicative (ZMod n) :=
    (torsionRootsUnity n).symm.trans
      (torsionZMod n).symm.toMultiplicative
  refine
    { prim := ?_
      cyc := (e.isCyclic).mpr inferInstance }
  let ζ : Multiplicative LocalInvariant :=
    Multiplicative.ofAdd (((1 : ℚ) / (n : ℚ) : LocalInvariant))
  refine ⟨ζ, (IsPrimitiveRoot.iff_orderOf).2 ?_⟩
  change addOrderOf (((1 : ℚ) / (n : ℚ) : LocalInvariant)) = n
  simpa only [one_mul] using
    (AddCircle.addOrderOf_period_div (p := (1 : ℚ)) (NeZero.pos n))

universe u

/-- Rational characters, written multiplicatively, are the usual unit-valued
characters used by finite-abelian duality. -/
noncomputable def rationalCharacterHom
    (G : Type u) [CommGroup G] :
    Multiplicative (CharacterModule (Additive G)) ≃*
      (G →* (Multiplicative LocalInvariant)ˣ) :=
  (MonoidHom.toAdditiveLeftMulEquiv
      (M := G) (N := LocalInvariant)).symm.trans
    (toUnits.monoidHomCongrRight (M := G))

/-- Evaluation identifies a finite abelian group with the double dual of its
`ℚ/ℤ`-valued characters. -/
noncomputable def characterDoubleDual
    (G : Type u) [CommGroup G] [Finite G] :
    Multiplicative
        (CharacterModule (CharacterModule (Additive G))) ≃* G := by
  let e := rationalCharacterHom G
  exact
    (rationalCharacterHom
        (Multiplicative (CharacterModule (Additive G)))).trans
      (e.monoidHomCongrLeft.trans
        (CommGroup.monoidHomMonoidHomEquiv G
          (Multiplicative LocalInvariant)))

/-- Additive form of rational-character double duality. -/
noncomputable def rationalDoubleDual
    (G : Type u) [CommGroup G] [Finite G] :
    CharacterModule (CharacterModule (Additive G)) ≃+ Additive G :=
  (characterDoubleDual G).toAdditive

@[simp]
theorem rational_double_dual
    (G : Type u) [CommGroup G] [Finite G]
    (η : CharacterModule (CharacterModule (Additive G)))
    (χ : CharacterModule (Additive G)) :
    χ (rationalDoubleDual G η) = η χ := by
  let e := rationalCharacterHom G
  let E :=
    (rationalCharacterHom
        (Multiplicative (CharacterModule (Additive G)))).trans
      e.monoidHomCongrLeft
  have h := CommGroup.apply_monoidHomMonoidHomEquiv
    (G := G) (M := Multiplicative LocalInvariant)
    (e (Multiplicative.ofAdd χ))
    (E (Multiplicative.ofAdd η))
  have h' := congrArg
    (fun z : (Multiplicative LocalInvariant)ˣ ↦ z.1.toAdd) h
  change
    (e (Multiplicative.ofAdd χ)
        (CommGroup.monoidHomMonoidHomEquiv G
          (Multiplicative LocalInvariant)
          (E (Multiplicative.ofAdd η)))).1.toAdd =
      (E (Multiplicative.ofAdd η)
        (e (Multiplicative.ofAdd χ))).1.toAdd
  exact h'

end

end Submission.CField.LRecip
