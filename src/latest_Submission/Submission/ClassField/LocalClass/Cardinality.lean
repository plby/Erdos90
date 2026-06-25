import Submission.ClassField.Shifting.HerbrandExactHexagon

/-!
# Milne, Class Field Theory, Lemma III.2.6: cardinality estimate

The induction in Lemma III.2.6 uses the elementary consequence of an exact
sequence `0 → A → B → C`: for finite groups, `|B| ≤ |A| |C|`.
This file proves that step independently of the unavailable local invariant
and higher inflation-restriction sequence.
-/

namespace Submission.CField.LClass

open Shifting

universe u v w

/-- The finite-cardinality inequality used in the induction of Lemma
III.2.6. The final map need not be surjective. -/
theorem nat_middle_exact
    {A : Type u} {B : Type v} {C : Type w}
    [AddGroup A] [AddGroup B] [AddGroup C]
    [Finite A] [Finite B] [Finite C]
    (f : A →+ B) (g : B →+ C) (hf : Function.Injective f)
    (hfg : Function.Exact f g) :
    Nat.card B ≤ Nat.card A * Nat.card C := by
  have hcardQ := congrArg (fun q : ℚˣ ↦ (q : ℚ))
    (card_range_mul f g hfg)
  have hcard : Nat.card B = Nat.card f.range * Nat.card g.range := by
    have hcardQ' : (Nat.card B : ℚ) =
        (Nat.card f.range : ℚ) * Nat.card g.range := by
      simpa only [card_unit_val, Units.val_mul, Nat.cast_mul] using hcardQ
    exact_mod_cast hcardQ'
  have hfcard : Nat.card f.range = Nat.card A := by
    symm
    exact Nat.card_congr (Equiv.ofInjective f hf)
  have hgcard : Nat.card g.range ≤ Nat.card C :=
    Nat.card_le_card_of_injective Subtype.val Subtype.val_injective
  calc
    Nat.card B = Nat.card A * Nat.card g.range := by rw [hcard, hfcard]
    _ ≤ Nat.card A * Nat.card C := Nat.mul_le_mul_left _ hgcard

end Submission.CField.LClass
