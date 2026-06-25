import Submission.ClassField.LocalReciprocity.ArtinCompatibility

/-!
# Tower naturality for finite local Artin maps

This file isolates the exact degree-minus-two Tate naturality square needed
for functoriality of the finite local Artin maps.  The square is stated for
the *forward* fundamental-class equivalences (the inverses of the Artin
maps), as in Milne III.3.3.  Its commutativity implies both commutativity of
the inverse Artin maps and the norm-kernel equality needed by finite-level
descent.

The construction is independent of how the forward equivalences are
obtained.  In the application below they are precisely the inverses of the
equivalences constructed from `abstractArtinMap` and `TateTwoShift` in
`FiniteLocalArtinMap`.
-/

namespace Submission.CField.LRecip

noncomputable section

open scoped IsMulCommutative

open Submission.CField.LFTheory

section QuotientMap

variable {A : Type*} [CommGroup A]

/-- The canonical map between group quotients induced by an inclusion of
normal subgroups. -/
def quotientMapLE (N M : Subgroup A) (hNM : N ≤ M) :
    A ⧸ N →* A ⧸ M :=
  QuotientGroup.map N M (MonoidHom.id A) hNM

@[simp]
theorem quotient_mk (N M : Subgroup A) (hNM : N ≤ M) (x : A) :
    quotientMapLE N M hNM (QuotientGroup.mk' N x) =
      QuotientGroup.mk' M x :=
  rfl

end QuotientMap

section AbstractNaturality

variable {A G Q : Type*} [CommGroup A] [CommGroup G] [CommGroup Q]

/-- Naturality of forward quotient equivalences implies naturality of their
inverse Artin homomorphisms.  This is the formal inverse-square argument in
Milne III.3.3. -/
theorem natural_forward
    (N M : Subgroup A) (hNM : N ≤ M)
    (upper : A ⧸ N ≃* G) (lower : A ⧸ M ≃* Q)
    (restriction : G →* Q)
    (hforward : ∀ g : G,
      quotientMapLE N M hNM (upper.symm g) =
        lower.symm (restriction g))
    (x : A) :
    restriction (upper (QuotientGroup.mk' N x)) =
      lower (QuotientGroup.mk' M x) := by
  apply lower.symm.injective
  rw [lower.symm_apply_apply]
  rw [← hforward]
  rw [upper.symm_apply_apply]
  exact quotient_mk N M hNM x

/-- Homomorphism form of `natural_forward`. -/
theorem inverse_natural_forward
    (N M : Subgroup A) (hNM : N ≤ M)
    (upper : A ⧸ N ≃* G) (lower : A ⧸ M ≃* Q)
    (restriction : G →* Q)
    (hforward : ∀ g : G,
      quotientMapLE N M hNM (upper.symm g) =
        lower.symm (restriction g)) :
    restriction.comp
        (upper.toMonoidHom.comp (QuotientGroup.mk' N)) =
      lower.toMonoidHom.comp (QuotientGroup.mk' M) := by
  ext x
  exact natural_forward N M hNM upper lower
    restriction hforward x

/-- If the lower inverse equivalence has kernel `M`, forward Tate
naturality identifies the kernel of the restricted upper Artin map with
`M`. -/
theorem restricted_forward_natural
    (N M : Subgroup A) (hNM : N ≤ M)
    (upper : A ⧸ N ≃* G) (lower : A ⧸ M ≃* Q)
    (restriction : G →* Q)
    (hforward : ∀ g : G,
      quotientMapLE N M hNM (upper.symm g) =
        lower.symm (restriction g)) :
    (restriction.comp
      (upper.toMonoidHom.comp (QuotientGroup.mk' N))).ker = M := by
  rw [inverse_natural_forward N M hNM upper lower
    restriction hforward]
  ext x
  simp

end AbstractNaturality

section FiniteLocal

variable (K L M : Type)
  [Field K] [Field L] [Field M]
  [Algebra K L] [Algebra K M]
  [FiniteDimensional K L] [FiniteDimensional K M]
  [IsGalois K L] [IsGalois K M]
  [IsMulCommutative Gal(L/K)] [IsMulCommutative Gal(M/K)]

/-- The forward degree-minus-two Tate square for two finite local Artin
data sets.  Its horizontal maps are the forward fundamental-class maps,
namely the inverses of the finite Artin equivalences constructed in
`FiniteLocalArtinMap`.

This is the exact missing cohomological naturality assertion: proving it
from formula (33) requires quotient/deflation naturality of the splitting
module realization of `TateTwoShift` (or an identification with cup
product), neither of which is currently present in the repository. -/
def LAData.ForwardTateSquare
    (upper : LAData K M)
    (lower : LAData K L)
    (restriction : Gal(M/K) →* Gal(L/K))
    (hnorm : normSubgroup K M ≤ normSubgroup K L) : Prop :=
  ∀ sigma : Gal(M/K),
    quotientMapLE (normSubgroup K M) (normSubgroup K L) hnorm
        ((upper.normResidueEquiv K M).symm sigma) =
      (lower.normResidueEquiv K L).symm (restriction sigma)

namespace LAData

variable (upper : LAData K M)
variable (lower : LAData K L)
variable (restriction : Gal(M/K) →* Gal(L/K))
variable (hnorm : normSubgroup K M ≤ normSubgroup K L)

/-- Commutativity of the forward Tate square gives the usual tower
compatibility of the concrete finite local Artin homomorphisms. -/
theorem artin_forward_square
    (hforward : upper.ForwardTateSquare K L M lower restriction hnorm) :
    restriction.comp (upper.artinHom K M) = lower.artinHom K L := by
  exact inverse_natural_forward
    (A := Kˣ) (G := Gal(M/K)) (Q := Gal(L/K))
    (normSubgroup K M) (normSubgroup K L) hnorm
    (upper.normResidueEquiv K M) (lower.normResidueEquiv K L)
    restriction hforward

/-- The desired tower kernel equality follows from the forward Tate square.
This is the exact input consumed by `descendedResidueEquiv`. -/
theorem restricted_forward_square
    (hforward : upper.ForwardTateSquare K L M lower restriction hnorm) :
    (restriction.comp (upper.artinHom K M)).ker = normSubgroup K L := by
  rw [artin_forward_square K L M upper lower restriction
    hnorm hforward]
  exact lower.artinHom_ker K L

end LAData

end FiniteLocal

end

end Submission.CField.LRecip
