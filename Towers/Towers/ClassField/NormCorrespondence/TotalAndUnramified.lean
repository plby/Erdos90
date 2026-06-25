import Towers.NumberTheory.Locals.TotallyRamifiedEisenstein

/-!
# Class Field Theory, Chapter I, paragraph 1.12: total versus unramified

Paragraph 1.12 uses the fact that a nontrivial totally ramified extension
cannot contain a nontrivial unramified part.  The theorem below records its
basic ideal-theoretic numerical form: if an extension is totally ramified at
`p` and a prime above `p` is unramified, then the extension has rank one.
-/

namespace Towers.CField.NCorr

open Algebra
open Towers.NumberTheory.Milne

variable (A B : Type*) [CommRing A] [IsDedekindDomain A]
  [CommRing B] [IsDedekindDomain B] [Algebra A B]
  [EssFiniteType A B] [Module.IsTorsionFree A B]

/-- A totally ramified extension which is also unramified at a prime above
the same nonzero prime has rank one. -/
theorem totally_ramified_unramified
    {p : Ideal A} [p.IsPrime] (hp : p ≠ ⊥)
    {P : Ideal B} [P.IsPrime] [P.LiesOver p]
    [Algebra.IsUnramifiedAt A P]
    (htr : TotallyRamified A B p) :
    Module.finrank A B = 1 := by
  rcases htr with ⟨Q, hQprime, hQover, _hpow, hram, hunique⟩
  have hQP : Q = P := (hunique P inferInstance inferInstance).symm
  subst Q
  have hP0 : P ≠ ⊥ :=
    Ideal.ne_bot_of_liesOver_of_ne_bot hp P
  have hramOne : Ideal.ramificationIdx p P = 1 := by
    have h := Ideal.ramificationIdx_eq_one_of_isUnramifiedAt
      (R := A) (p := P) hP0
    simpa [Ideal.LiesOver.over (P := P) (p := p)] using h
  exact hram.symm.trans hramOne

end Towers.CField.NCorr
