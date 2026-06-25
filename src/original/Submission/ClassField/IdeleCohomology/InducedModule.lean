import Mathlib.RepresentationTheory.Coinduced

/-!
# Chapter VII, Section 2: Milne's induced module

Milne writes `Ind_H^G(A)` for the functions `f : G → A` satisfying
`f(hg) = h f(g)`, with `G` acting by right translation.  This is precisely
Mathlib's function-valued coinduced representation.  The following formulas
record the conventions used in Proposition 2.2 and Lemma 2.1.
-/

namespace Submission.CField.ICohomo

open Representation

noncomputable section

universe u v

variable {k : Type u} {G : Type v} [CommRing k] [Group G]

/-- Milne's function-valued induced module, in Mathlib's terminology. -/
abbrev milneInducedModule (H : Subgroup G) (A : Rep k H) : Rep k G :=
  Rep.coind H.subtype A

/-- **Proposition VII.2.2, covariance condition.** Membership in the
function-valued induced module is exactly Milne's equation
`f(rho * sigma) = rho (f sigma)`. -/
theorem mem_induced
    (H : Subgroup G) (A : Rep k H) (f : G → A) :
    f ∈ A.ρ.coindV H.subtype ↔
      ∀ (rho : H) (sigma : G),
        f (rho.1 * sigma) = A.ρ rho (f sigma) :=
  Iff.rfl

/-- **Lemma VII.2.1 / Proposition VII.2.2, action formula.** The ambient
group acts on the induced function by right translation. -/
theorem induced_action_apply
    (H : Subgroup G) (A : Rep k H)
    (tau : G) (f : milneInducedModule H A) (sigma : G) :
    (((milneInducedModule H A).ρ tau) f).1 sigma = f.1 (sigma * tau) :=
  rfl

end

end Submission.CField.ICohomo
