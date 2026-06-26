import Mathlib.GroupTheory.Abelianization.Defs
import Mathlib.GroupTheory.Transfer

/-!
# Appendix, Exercise A-6: transfer

Mathlib's `MonoidHom.transfer` implements the transversal construction in
parts (a)--(b), proves that it is independent of the transversal, and bundles
the result as a homomorphism.  Applying it to the canonical map from `H` to
its abelianization gives Milne's transfer, and the universal property of the
abelianization gives the displayed map `G/G^c -> H/H^c`.

Parts (c)--(d) compare this map with restriction on group homology through
augmentation ideals.  The current homological representation API does not
yet connect that comparison with `MonoidHom.transfer`.
-/

namespace Towers.CField.TCohomo.Verlag

variable {G : Type*} [Group G] (H : Subgroup G)

/-- **Exercise A-6(a).** In the orientation used by Milne, two representatives
of the same right coset give a correction term lying in `H`. -/
theorem correction_same_coset {sx sxg g : G}
    (hcoset : QuotientGroup.rightRel H sxg (sx * g)) :
    sx * g * sxg⁻¹ ∈ H :=
  QuotientGroup.rightRel_apply.mp hcoset

/-- The transfer from `G` to the abelianization of a finite-index subgroup
`H`. -/
noncomputable def transferToAbelianization [H.FiniteIndex] :
    G →* Abelianization H :=
  MonoidHom.transfer (Abelianization.of : H →* Abelianization H)

/-- **Exercise A-6(b).** The Verlag induced on abelianizations. -/
noncomputable def verlagerung [H.FiniteIndex] :
    Abelianization G →* Abelianization H :=
  Abelianization.lift (transferToAbelianization H)

/-- The induced map agrees with transfer on representatives. -/
@[simp]
theorem verlagerung_of [H.FiniteIndex] (g : G) :
    verlagerung H (Abelianization.of g) = transferToAbelianization H g :=
  rfl

end Towers.CField.TCohomo.Verlag
