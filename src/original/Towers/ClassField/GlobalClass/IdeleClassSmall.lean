import Mathlib.Logic.Small.Basic
import Towers.ClassField.Reciprocity.UniverseArtinNormalization
import Towers.ClassField.CyclicIdeles.FiniteGalois

/-!
# A Type-0 model for the idèle-class representation

Although a number field may be placed in an arbitrary universe, its idèle
group and the idèle-class representation used in Chapter VIII have Type-0
models.  This lets the universe-polymorphic statement of Tate's theorem be
reduced to its already formalized Type-0 version without changing the
arithmetic representation.
-/

namespace Towers.CField.GClass

open CategoryTheory CategoryTheory.Limits
open IsDedekindDomain NumberField Representation
open Towers.CField.Ideles
open Towers.CField.Recip
open Towers.CField.NIndex
open Towers.CField.CIdeles

noncomputable section

universe u

private theorem ideal_generating_finset
    (R : Type u) [CommRing R] [IsNoetherianRing R] (I : Ideal R) :
    ∃ s : Finset R, Ideal.span (s : Set R) = I := by
  obtain ⟨s, hs, hspan⟩ := Submodule.fg_def.mp I.fg_of_isNoetherianRing
  exact ⟨hs.toFinset, by simpa using hspan⟩

private noncomputable def idealGeneratingFinset
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    (I : Ideal R) : Finset R :=
  Classical.choose (ideal_generating_finset R I)

private theorem generating_finset_span
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    (I : Ideal R) :
    Ideal.span (idealGeneratingFinset R I : Set R) = I :=
  Classical.choose_spec (ideal_generating_finset R I)

private theorem ideal_countable
    (R : Type u) [CommRing R] [IsNoetherianRing R] [Countable R] :
    Countable (Ideal R) := by
  exact (show Function.Injective (idealGeneratingFinset R) by
    intro I J h
    rw [← generating_finset_span R I,
      ← generating_finset_span R J, h]).countable

private theorem numberField_countable
    (F : Type u) [Field F] [NumberField F] : Countable F :=
  (Module.finBasis ℚ F).repr.injective.countable

private theorem ring_integers_countable
    (F : Type u) [Field F] [NumberField F] :
    Countable (NumberField.RingOfIntegers F) := by
  letI : Countable F := numberField_countable F
  exact Subtype.coe_injective.countable

/-- The finite idèles of an arbitrary-universe number field have a Type-0
model. -/
theorem finiteIdelesSmall
    (F : Type u) [Field F] [NumberField F] :
    Small.{0} (FiniteIdeles (NumberField.RingOfIntegers F) F) := by
  letI : Countable (NumberField.RingOfIntegers F) :=
    ring_integers_countable F
  letI : Countable (Ideal (NumberField.RingOfIntegers F)) :=
    ideal_countable (NumberField.RingOfIntegers F)
  letI : Countable
      (HeightOneSpectrum (NumberField.RingOfIntegers F)) := by
    exact (show Function.Injective
        (fun P : HeightOneSpectrum (NumberField.RingOfIntegers F) ↦
          P.asIdeal) by
      intro P Q h
      exact HeightOneSpectrum.ext_iff.mpr h).countable
  letI : Small.{0}
      (HeightOneSpectrum (NumberField.RingOfIntegers F)) := inferInstance
  letI (P : HeightOneSpectrum (NumberField.RingOfIntegers F)) :
      Small.{0} (P.adicCompletion F) := by
    let v := (FinitePlace.mk P).val
    letI : Small.{0} v.Completion := absoluteSmallZero F v
    exact small_map (placeCompletionAdic P).symm.toEquiv
  letI (P : HeightOneSpectrum (NumberField.RingOfIntegers F)) :
      Small.{0} (P.adicCompletion F)ˣ :=
    small_of_injective Units.val_injective
  apply small_of_injective
    (f := fun x : FiniteIdeles (NumberField.RingOfIntegers F) F ↦ x.1)
  intro x y h
  exact Subtype.ext h

/-- The infinite adèle ring of an arbitrary-universe number field has a
Type-0 model. -/
theorem infiniteAdeleSmall
    (F : Type u) [Field F] [NumberField F] :
    Small.{0} (InfiniteAdeleRing F) := by
  letI : Small.{0} (InfinitePlace F) := inferInstance
  letI (v : InfinitePlace F) : Small.{0} v.1.Completion :=
    absoluteSmallZero F v.1
  change Small.{0} ((v : InfinitePlace F) → v.1.Completion)
  exact inferInstance

/-- The full idèle group of an arbitrary-universe number field has a Type-0
model. -/
theorem idelesSmallZero
    (F : Type u) [Field F] [NumberField F] :
    Small.{0} (IdeleGroup (NumberField.RingOfIntegers F) F) := by
  letI : Small.{0} (FiniteIdeles (NumberField.RingOfIntegers F) F) :=
    finiteIdelesSmall F
  letI : Small.{0} (InfiniteAdeleRing F) := infiniteAdeleSmall F
  letI : Small.{0} (InfiniteAdeleRing F)ˣ :=
    small_of_injective Units.val_injective
  change Small.{0} ((InfiniteAdeleRing F)ˣ ×
    FiniteIdeles (NumberField.RingOfIntegers F) F)
  exact inferInstance

/-- The carrier of the actual idèle-class cohomology representation used in
Theorems VIII.4.7 and VIII.4.8 has a Type-0 model. -/
theorem cohomologyRepresentationSmall
    (K L : Type u) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] :
    Small.{0} (ideleCohomologyRepresentation K L) := by
  letI : Small.{0} (IdeleGroup (NumberField.RingOfIntegers L) L) :=
    idelesSmallZero L
  change Small.{0}
    (classCokernelRepresentation (K := K) (L := L))
  let f := cokernel.π
    (ICohomo.concreteActionData
      (K := K) (L := L)).principalIdeleHom
  have hsource : Small.{0}
      (ICohomo.concreteActionData
        (K := K) (L := L)).representation := by
    change Small.{0}
      (Additive (IdeleGroup (NumberField.RingOfIntegers L) L))
    exact small_of_injective Additive.toMul.injective
  letI : Small.{0}
      (ICohomo.concreteActionData
        (K := K) (L := L)).representation := hsource
  have hf : Function.Surjective f :=
    (Rep.epi_iff_surjective f).1 (inferInstance : Epi f)
  exact @small_of_surjective.{0, u, u} _ _ inferInstance _ hf

end

end Towers.CField.GClass
