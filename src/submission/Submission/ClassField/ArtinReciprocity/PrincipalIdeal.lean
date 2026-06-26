import Submission.NumberTheory.ClassGroup.Principalization
import Submission.ClassField.ArtinReciprocity.Statements
import Submission.ClassField.ArtinReciprocity.Verlagerung

/-!
# Chapter V, Section 3, Theorem 3.17: Principal Ideal Theorem

The literal theorem says that every ideal of `K` becomes principal in the
Hilbert class field of `K`.

The repository proves that all ideals principalize simultaneously in some
finite extension (`principalizationprincipalization`), but it explicitly does not
construct Hilbert class fields.  This file therefore:
* defines a Hilbert class field by the source's maximal everywhere-unramified
  finite abelian property;
* states the literal ideal-extension/principality assertion;
* proves that assertion is exactly equivalent to triviality of the induced
  map on ideal class groups; and
* proves the source's transfer reduction: Artin compatibility plus
  Furtwaengler's transfer theorem makes the class-group map trivial.

The only remaining inputs are genuine missing objects/theorems: construction
of the Hilbert class field, the class-group extension/Artin transfer square,
and Theorem V.3.19 asserting transfer to the commutator is trivial.
-/

namespace Submission.CField.ARecip

open IsDedekindDomain NumberField
open RCGroups
open Submission.NumberTheory.Milne
open scoped nonZeroDivisors

noncomputable section

universe u

variable {K : Type u} [Field K] [NumberField K]

/-- A source-faithful Hilbert class field: a finite abelian extension,
unramified at every finite and real infinite prime, containing every other
such finite abelian extension. -/
structure HCField (K : Type u) [Field K] [NumberField K] where
  extension : ANExt K
  unramified : extension.IsUnramifiedOutside (1 : Modulus K)
  maximal : ∀ L : ANExt K,
    L.IsUnramifiedOutside (1 : Modulus K) →
      Nonempty (L.carrier →ₐ[K] extension.carrier)

namespace HCField

variable (H : HCField K)

/-- Extension of an integral ideal from `K` to its Hilbert class field. -/
def extendIdeal (I : Ideal (𝓞 K)) : Ideal (𝓞 H.extension.carrier) :=
  I.map (algebraMap (𝓞 K) (𝓞 H.extension.carrier))

end HCField

/-- The currently missing functorial class-group map induced by extending
ideals to the Hilbert class field, together with its exact value on every
nonzero ideal representative. -/
structure IdealExtensionData (H : HCField K) where
  classMap : ClassGroup (𝓞 K) →* ClassGroup (𝓞 H.extension.carrier)
  map_mk0 : ∀ (I : Ideal (𝓞 K)) (hI : I ≠ ⊥),
    classMap (ClassGroup.mk0
        ⟨I, mem_nonZeroDivisors_iff_ne_zero.mpr hI⟩) =
      ClassGroup.mk0
        ⟨H.extendIdeal I, mem_nonZeroDivisors_iff_ne_zero.mpr
          (Ideal.map_ne_bot_of_ne_bot hI)⟩

/-- If every ideal capitulates, the induced class-group map is trivial. -/
theorem class_principal_theorem
    (H : HCField K) (D : IdealExtensionData H)
    (hprincipal : (∀ I : Ideal (𝓞 K), (H.extendIdeal I).IsPrincipal)) :
    D.classMap = 1 := by
  ext C
  obtain ⟨I, hI⟩ := ClassGroup.mk0_surjective C
  have hI0 : (I : Ideal (𝓞 K)) ≠ ⊥ :=
    mem_nonZeroDivisors_iff_ne_zero.mp I.property
  rw [← hI, D.map_mk0 I hI0]
  exact (ClassGroup.mk0_eq_one_iff
    (mem_nonZeroDivisors_iff_ne_zero.mpr
        (Ideal.map_ne_bot_of_ne_bot hI0))).mpr
    (hprincipal I)

/-- Conversely, triviality of the class-group extension map says exactly
that every extended nonzero ideal is principal; the zero ideal is principal
separately. -/
theorem principal_theorem_class
    (H : HCField K) (D : IdealExtensionData H)
    (htrivial : D.classMap = 1) :
    (∀ I : Ideal (𝓞 K), (H.extendIdeal I).IsPrincipal) := by
  intro I
  by_cases hI : I = ⊥
  · subst I
    simpa [HCField.extendIdeal] using
      (bot_isPrincipal : (⊥ : Ideal (𝓞 H.extension.carrier)).IsPrincipal)
  · apply (ClassGroup.mk0_eq_one_iff
      (mem_nonZeroDivisors_iff_ne_zero.mpr
        (Ideal.map_ne_bot_of_ne_bot hI))).mp
    have hmap : D.classMap
        (ClassGroup.mk0
          ⟨I, mem_nonZeroDivisors_iff_ne_zero.mpr hI⟩) = 1 := by
      rw [htrivial]
      rfl
    simpa only [HCField.extendIdeal] using
      (D.map_mk0 I hI).symm.trans hmap

/-- Thus the literal theorem is equivalent to triviality of the
capitulation map, once the missing class-group extension API is supplied. -/
theorem principal_ideal_theorem
    (H : HCField K) (D : IdealExtensionData H) :
    (∀ I : Ideal (𝓞 K), (H.extendIdeal I).IsPrincipal
    ) ↔ D.classMap = 1 :=
  ⟨class_principal_theorem H D,
    principal_theorem_class H D⟩

/-- The group-theoretic statement isolated by Milne as Theorem V.3.19.  The
tracked file constructs `verlagerung`, but Mathlib does not prove this
triviality theorem. -/
def FurtwaenglerTransferStatement (G : Type u) [Group G] [Finite G] : Prop :=
  verlagerung (commutator G) = 1

/-- Exact Artin/transfer square used in the source's reduction.  The group
`G` models the Galois group of the Hilbert class field of the Hilbert class
field over `K`; its commutator models the subgroup over the first Hilbert
class field. -/
structure CapitulationTransferBridge
    (H : HCField K) (D : IdealExtensionData H) where
  G : Type u
  [group : Group G]
  [finite : Finite G]
  baseArtin : ClassGroup (𝓞 K) ≃* Abelianization G
  upperArtin :
    ClassGroup (𝓞 H.extension.carrier) ≃* Abelianization (commutator G)
  square : upperArtin.toMonoidHom.comp D.classMap =
    (verlagerung (commutator G)).comp baseArtin.toMonoidHom

attribute [instance]
  CapitulationTransferBridge.group CapitulationTransferBridge.finite

/-- The Artin/transfer square and Furtwaengler's theorem force the
capitulation map to be trivial. -/
theorem class_one_transfer
    (H : HCField K) (D : IdealExtensionData H)
    (B : CapitulationTransferBridge H D)
    (hfurt : FurtwaenglerTransferStatement B.G) :
    D.classMap = 1 := by
  ext C
  apply B.upperArtin.injective
  have hC := DFunLike.congr_fun B.square C
  rw [hfurt] at hC
  simpa using hC

/-- The sharp source reduction of Theorem V.3.17.  Once the Hilbert class
field, the ideal-class extension/Artin square, and Furtwaengler's theorem are
available, the literal ideal-principality conclusion follows. -/
theorem principal_theorem_transfer
    (H : HCField K) (D : IdealExtensionData H)
    (B : CapitulationTransferBridge H D)
    (hfurt : FurtwaenglerTransferStatement B.G) :
    (
      ∀ I : Ideal (𝓞 K), (H.extendIdeal I).IsPrincipal) :=
  principal_theorem_class H D
    (class_one_transfer H D B hfurt)

/-- Uniform form of the source reduction: transfer data and Furtwaengler's
theorem for every Hilbert class field model imply the simultaneous literal
statement of Theorem V.3.17. -/
theorem of_transfer_reduction
    (htransfer : ∀ H : HCField K,
      ∃ (D : IdealExtensionData H)
        (B : CapitulationTransferBridge H D),
          FurtwaenglerTransferStatement B.G) :
    ∀ H : HCField K, (
      ∀ I : Ideal (𝓞 K), (H.extendIdeal I).IsPrincipal
    )
  := by
  intro H
  obtain ⟨D, B, hfurt⟩ := htransfer H
  exact principal_theorem_transfer H D B hfurt

/-- What is already unconditional in the repository: all ideals of `K`
become principal simultaneously in some finite extension.  The missing
assertion in Theorem V.3.17 is that this extension can be chosen to be the
Hilbert class field. -/
theorem finite_principalizing_extension
    (K : Type u) [Field K] [NumberField K] :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra K L) (_ : NumberField L),
      ∀ I : Ideal (𝓞 K),
        (I.map (algebraMap (𝓞 K) (𝓞 L))).IsPrincipal :=
  principalizationprincipalization K

end

end Submission.CField.ARecip
