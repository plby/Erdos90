import Mathlib.GroupTheory.Abelianization.Defs
import Mathlib.GroupTheory.Transfer

/-!
# Chapter V, Section 3, Proposition 3.18: transfer

Mathlib constructs the transfer homomorphism intrinsically from a subgroup
of finite index, proving in its construction that the result is independent
of a choice of transversal.  Composing with the quotient to the
abelianization of the subgroup and using the universal property of
abelianization gives Milne's Verlag map.

Theorem 3.19, asserting that this map is trivial when the subgroup is the
commutator subgroup of a finite group, is the deep principal ideal theorem
of Furtwaengler.  It is not presently a theorem in Mathlib's transfer API.
-/

namespace Towers.CField.ARecip

noncomputable section

variable {G : Type*} [Group G] (H : Subgroup G) [H.FiniteIndex]

/-- Proposition 3.18 before passage to the source abelianization: transfer
from `G` to the abelianization of a finite-index subgroup `H`. -/
noncomputable def transferToAbelianization : G →* Abelianization H :=
  MonoidHom.transfer (Abelianization.of : H →* Abelianization H)

/-- Proposition 3.18: the Verlag (transfer) homomorphism
`G^ab -> H^ab`. -/
noncomputable def verlagerung : Abelianization G →* Abelianization H :=
  Abelianization.lift (transferToAbelianization H)

/-- The Verlag applied to the class of `g` is the ordinary transfer of
`g` to `H^ab`. -/
@[simp]
theorem verlagerung_apply_of (g : G) :
    verlagerung H (Abelianization.of g) = transferToAbelianization H g :=
  Abelianization.lift_apply_of _ g

end

end Towers.CField.ARecip
