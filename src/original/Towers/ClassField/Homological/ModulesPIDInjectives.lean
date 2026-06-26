import Mathlib.Algebra.Category.ModuleCat.EnoughInjectives
import Mathlib.RingTheory.PrincipalIdealDomain

/-!
# Chapter II, Appendix, Proposition A.4

The category of modules over a principal ideal domain has enough injectives.

Mathlib proves the stronger statement for modules over an arbitrary ring.  Its
proof embeds abelian groups into injectives and transports the construction
along the restriction/coextension-of-scalars adjunction.
-/

open CategoryTheory

universe u v

namespace Towers.CField.Homological

/-- Proposition A.4.  Every module over a principal ideal domain embeds in an
injective module. -/
theorem modules_pid_injectives (R : Type u) [CommRing R] [IsDomain R]
    [IsPrincipalIdealRing R] : EnoughInjectives (ModuleCat.{max v u} R) :=
  ModuleCat.enoughInjectives R

end Towers.CField.Homological
