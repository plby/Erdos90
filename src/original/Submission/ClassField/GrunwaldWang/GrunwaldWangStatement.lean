import Mathlib.Analysis.Complex.Circle
import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.Topology.Algebra.ContinuousMonoidHom
import Submission.ClassField.Ideles.GlobalPlace
import Submission.ClassField.Ideles.Ideles

/-!
# The Grunwald--Wang theorem

This file states Theorem VIII.2.4 using continuous circle-valued characters.
The unconditional extension assertion is kept separate from the assertion
that the global character can be chosen with the least possible order; the
Wang exception applies only to the latter.
-/

namespace Submission.CField.GWang

open IsDedekindDomain NumberField
open Submission.CField.Ideles

noncomputable section

universe u

variable (K : Type u) [Field K] [NumberField K]

/-- The finite and infinite primes of a number field. -/
abbrev Place := NumberFieldPlace K

/-- The multiplicative group of the completion at a place. -/
def LocalMultiplicativeGroup (v : Place K) : Type u :=
  (placeCompletion K v)ˣ

instance (v : Place K) : CommGroup (LocalMultiplicativeGroup K v) := by
  simp only [LocalMultiplicativeGroup]
  infer_instance

instance (v : Place K) : TopologicalSpace (LocalMultiplicativeGroup K v) := by
  simp only [LocalMultiplicativeGroup]
  infer_instance

/-- A character means a continuous circle-valued multiplicative character. -/
abbrev LocalCharacter (v : Place K) :=
  LocalMultiplicativeGroup K v →ₜ* Circle

/-- The finite-order local characters occurring in the Grunwald--Wang
theorem.  The finite-order condition makes `orderOf` a positive integer, as
required for the least-common-multiple and Wang-exception clauses. -/
abbrev OrderLocalCharacter (v : Place K) :=
  { chi : LocalCharacter K v // IsOfFinOrder chi }

/-- A finite-order local character has positive order. -/
theorem order_character_pos
    {v : Place K} (chi : OrderLocalCharacter K v) :
    0 < orderOf chi.1 :=
  chi.2.orderOf_pos

/-- A continuous character of the idele class group. -/
abbrev IdeleClassCharacter :=
  IdeleClassGroup (NumberField.RingOfIntegers K) K →ₜ* Circle

/-- A global idele-class character restricts to a specified local character
through the canonical one-place idele embedding. -/
def CharacterRestrictsTo
    (chi : IdeleClassCharacter K) :
    ∀ v : Place K, LocalCharacter K v → Prop
  | .inl v, chi_v =>
      ∀ x : (v.adicCompletion K)ˣ,
        chi (QuotientGroup.mk'
          (principalIdeles (NumberField.RingOfIntegers K) K)
          (finitePlaceEmbedding (NumberField.RingOfIntegers K) K v x)) = chi_v x
  | .inr v, chi_v =>
      ∀ x : v.Completionˣ,
        chi (QuotientGroup.mk'
          (principalIdeles (NumberField.RingOfIntegers K) K)
          (infinitePlaceEmbedding (NumberField.RingOfIntegers K) K v x)) = chi_v x

/-- The possible Wang obstruction at the order `n`: some `2^t` divides
`n`, while adjoining the `2^t`-th roots of unity gives a noncyclic extension
of `K`. -/
def HasWangException (n : ℕ) : Prop :=
  ∃ t : ℕ, 2 ^ t ∣ n ∧
    ¬IsCyclic Gal(CyclotomicField (2 ^ t) K/K)

/-- **Theorem VIII.2.4 (Grunwald--Wang), statement.**

Every finite family of continuous local characters extends to an idele-class
character.  For a family of finite-order characters, if the Wang obstruction
is absent, the extension can be chosen to have order equal to the least common
multiple of the local orders. -/
def GrunwaldWangTheorem : Prop :=
  (∀ (S : Finset (Place K))
      (chi_v : ∀ v : S, LocalCharacter K v.1),
    ∃ chi : IdeleClassCharacter K,
      ∀ v : S, CharacterRestrictsTo K chi v.1 (chi_v v)) ∧
  ∀ (S : Finset (Place K))
    (chi_v : ∀ v : S, OrderLocalCharacter K v.1),
    let n := Finset.univ.lcm (fun v : S => orderOf (chi_v v).1)
    ¬HasWangException K n →
      ∃ chi : IdeleClassCharacter K,
        orderOf chi = n ∧
          ∀ v : S, CharacterRestrictsTo K chi v.1 (chi_v v).1

end

end Submission.CField.GWang
