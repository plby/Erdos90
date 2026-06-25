import Submission.ClassField.GlobalClass.MaximalAbelianSubextension

/-!
# Norm transitivity in the norm limitation theorem

The easy inclusion in Theorem VIII.4.8 uses norm transitivity for an
arbitrary finite tower.  The concrete finite-idèle transitivity theorem
currently available in Chapter VII is stated only for Galois towers.  This
file isolates the unrestricted statement, proves that it descends to idèle
classes, and completes the containment argument without imposing a Galois
hypothesis absent from Milne's theorem.
-/

namespace Submission.CField.GClass

open NumberField
open Submission.CField.Ideles

noncomputable section

universe u

/-- Transitivity of the concrete idèle norm in an arbitrary finite tower,
in the exact generality used by norm limitation. -/
def TransitivityIdeleBridge : Prop :=
  ∀ (K E L : Type u) [Field K] [Field E] [Field L]
    [NumberField K] [NumberField E] [NumberField L]
    [Algebra K E] [Algebra E L] [Algebra K L]
    [IsScalarTower K E L]
    [FiniteDimensional K E] [FiniteDimensional E L],
    ideleNorm (K := K) (L := L) =
      (ideleNorm (K := K) (L := E)).comp
        (ideleNorm (K := E) (L := L))

/-- Arbitrary-tower idèle norm transitivity descends through principal
idèles to the canonical norm on idèle class groups. -/
theorem canonical_idele_trans
    {K E L : Type u} [Field K] [Field E] [Field L]
    [NumberField K] [NumberField E] [NumberField L]
    [Algebra K E] [Algebra E L] [Algebra K L]
    [IsScalarTower K E L]
    [FiniteDimensional K E] [FiniteDimensional E L]
    (htrans : ideleNorm (K := K) (L := L) =
      (ideleNorm (K := K) (L := E)).comp
        (ideleNorm (K := E) (L := L))) :
    canonicalIdeleNorm (K := K) (L := L) =
      (canonicalIdeleNorm (K := K) (L := E)).comp
        (canonicalIdeleNorm (K := E) (L := L)) := by
  apply MonoidHom.ext
  intro c
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective
    (principalIdeles (RingOfIntegers L) L) c
  simp only [canonical_idele_mk]
  rw [htrans]
  rfl

/-- Norm transitivity proves the containment half of Theorem VIII.4.8 for
every finite extension, with no Galois hypothesis on the ambient field. -/
theorem containment_bridge_transitivity
    (htrans : TransitivityIdeleBridge.{u}) :
    NormContainmentBridge.{u} := by
  intro K E _ _ _ _ _ _ M
  have hclass := canonical_idele_trans
    (htrans K M E)
  rw [hclass]
  rintro _ ⟨c, rfl⟩
  exact ⟨canonicalIdeleNorm (K := M) (L := E) c, rfl⟩

/-- After norm transitivity is supplied, the full theorem retains only the
corestriction/index comparison from Milne's proof. -/
theorem transitivity_index
    (htrans : TransitivityIdeleBridge.{u})
    (hindex : IndexBridge.{u}) :
    MaximalSubextensionEquality.{u} :=
  containment_index
    (containment_bridge_transitivity htrans) hindex

end

end Submission.CField.GClass
