import Submission.ClassField.GrunwaldWang.CharacterOrders
import Submission.ClassField.GrunwaldWang.GrunwaldWangStatement

/-!
# Chapter VIII, Section 2, Theorem 2.4

The Grunwald--Wang theorem has two logically distinct parts.  Weak
approximation/global duality extends an arbitrary finite family of local
characters.  A second argument changes the global character, without changing
those restrictions, to have the least possible order; only that second step
has the Wang two-primary exception.
-/

namespace Submission.CField.GWang

open Submission.CField.Ideles

noncomputable section
universe u

/-- The unconditional character-extension part of Grunwald--Wang. -/
def CharacterExtensionBridge : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K]
    (S : Finset (Place K))
    (chi_v : ∀ v : S, LocalCharacter K v.1),
    ∃ chi : IdeleClassCharacter K,
      ∀ v : S, CharacterRestrictsTo K chi v.1 (chi_v v)

/-- The order-correction step.  Starting with any extension of the prescribed
finite-order local characters, absence of the Wang exception permits another
extension of exactly the lcm of the local orders. -/
def OrderCorrectionBridge : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K]
    (S : Finset (Place K))
    (chi_v : ∀ v : S, OrderLocalCharacter K v.1),
    let n := Finset.univ.lcm (fun v : S => orderOf (chi_v v).1)
    ¬HasWangException K n →
    ∀ chi₀ : IdeleClassCharacter K,
      (∀ v : S, CharacterRestrictsTo K chi₀ v.1 (chi_v v).1) →
      ∃ chi : IdeleClassCharacter K,
        orderOf chi = n ∧
          ∀ v : S, CharacterRestrictsTo K chi v.1 (chi_v v).1

/-- **Theorem VIII.2.4 (Grunwald--Wang).** -/
theorem grunwald_wang_correction
    (hextend : CharacterExtensionBridge.{u})
    (horder : OrderCorrectionBridge.{u}) :
    ∀ (K : Type u) [Field K] [NumberField K],
      GrunwaldWangTheorem K := by
  intro K _ _
  constructor
  · exact hextend K
  · intro S chi_v
    dsimp only
    intro hnoException
    obtain ⟨chi₀, hchi₀⟩ := hextend K S (fun v => (chi_v v).1)
    exact horder K S chi_v hnoException chi₀ hchi₀

end

end Submission.CField.GWang
