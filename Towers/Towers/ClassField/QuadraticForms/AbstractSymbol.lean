import Towers.ClassField.QuadraticForms.HilbertInvariants

/-! # Chapter VIII, Section 6, Lemma 6.5 -/

namespace Towers.CField.QForms

variable (G μ : Type*) [CommGroup G] [CommGroup μ]

/-- The additional nondegeneracy datum in Lemma 6.5(b).  In the intended
application `G = Kˣ/Kˣ²`, so `a ≠ 1` says that `a` is a nonsquare, and
`negativeValue` is `-1`. -/
structure NHSym extends AHSym G μ where
  negativeValue : μ
  negative_ne_one : negativeValue ≠ 1
  detects_nonsquare : ∀ a : G, a ≠ 1 → ∃ b : G, symbol a b = negativeValue

namespace NHSym

variable {G μ}
variable (h : NHSym G μ)

/-- The four literal clauses of Lemma VIII.6.5. -/
def NondegenerateAbstractSymbol : Prop :=
  (∀ a b c : G,
      h.symbol (a * b) c = h.symbol a c * h.symbol b c) ∧
  (∀ a b c : G,
      h.symbol a (b * c) = h.symbol a b * h.symbol a c) ∧
  (∀ a b c d : G,
      h.symbol (a * c ^ 2) (b * d ^ 2) = h.symbol a b) ∧
  (∀ a : G, a ≠ 1 → ∃ b : G, h.symbol a b = h.negativeValue) ∧
  (∀ a b : G,
      h.symbol b a = (h.symbol a b)⁻¹ ∧
      (h.symbol a b)⁻¹ = h.symbol a b) ∧
  (∀ a : G,
      h.symbol a (h.negOne * a) = 1 ∧ h.symbol 1 a = 1)

/-- **Lemma VIII.6.5.** All four properties follow from bimultiplicativity,
quadratic symmetry, the norm/nondegeneracy clause, and `(a,-a)=1`. -/
theorem nondegenerateAbstractSymbol : h.NondegenerateAbstractSymbol := by
  let h₀ : AHSym G μ := h.toAHSym
  refine ⟨h₀.map_mul_left, h₀.map_mul_right, h₀.mul_sq,
    h.detects_nonsquare, h₀.symmetric_inv, ?_⟩
  intro a
  exact ⟨h.self_neg a, h₀.map_one_left a⟩

end NHSym

end Towers.CField.QForms
