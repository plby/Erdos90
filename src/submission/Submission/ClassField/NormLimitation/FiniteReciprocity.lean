import Submission.ClassField.Reciprocity.IdelicReciprocityLaw
import Submission.ClassField.NormLimitation.SubgroupQuotientMap

/-!
# The reciprocity input to Lemma VII.9.1

The Artin map used in Lemma 9.1 is not additional data.  Once the global
Artin map and Theorem V.5.3 are available, it is the quotient map

`C_K → C_K / Nm(C_L) ≃ Gal(L/K)`.

This file constructs that map and proves both assertions required by
`FiniteArtinData`: it is onto and its kernel is exactly the idèle
class norm group.
-/

namespace Submission.CField.NLimita

open NumberField
open Submission.CField.LFTheory
open Submission.CField.Ideles
open Submission.CField.Recip

noncomputable section

universe u

variable {K : Type u} [Field K] [NumberField K]

noncomputable local instance finiteReciprocityFiniteLayerNumberField
    (L : FASubext K) : NumberField L.1 :=
  NumberField.of_module_finite K L.1

/-- The idèle-class Artin map supplied by finite reciprocity. -/
noncomputable def ideleClassArtin
    (L : FASubext K)
    (phi : IdeleGroup (RingOfIntegers K) K →*
      AbsoluteAbelianGalois K)
    (hL : FiniteReciprocityLaw (RingOfIntegers K) K Gal(L.1/K)
      ((localAbelianRestriction L).comp phi)
      (ideleNormSubgroup (K := K) (L := L.1))) :
    IdeleClassGroup (RingOfIntegers K) K →* Gal(L.1/K) :=
  (ideleClassReciprocity L phi hL).toMonoidHom.comp
    (QuotientGroup.mk' (ideleClassSubgroup L))

/-- The idèle-class Artin map is surjective. -/
theorem idele_artin_surjective
    (L : FASubext K)
    (phi : IdeleGroup (RingOfIntegers K) K →*
      AbsoluteAbelianGalois K)
    (hL : FiniteReciprocityLaw (RingOfIntegers K) K Gal(L.1/K)
      ((localAbelianRestriction L).comp phi)
      (ideleNormSubgroup (K := K) (L := L.1))) :
    Function.Surjective (ideleClassArtin L phi hL) := by
  intro sigma
  obtain ⟨q, rfl⟩ := (ideleClassReciprocity L phi hL).surjective sigma
  obtain ⟨c, rfl⟩ := QuotientGroup.mk'_surjective
    (ideleClassSubgroup L) q
  exact ⟨c, rfl⟩

/-- The kernel of the idèle-class Artin map is the idèle class norm
group, exactly as in Theorem V.5.3. -/
theorem idele_artin_ker
    (L : FASubext K)
    (phi : IdeleGroup (RingOfIntegers K) K →*
      AbsoluteAbelianGalois K)
    (hL : FiniteReciprocityLaw (RingOfIntegers K) K Gal(L.1/K)
      ((localAbelianRestriction L).comp phi)
      (ideleNormSubgroup (K := K) (L := L.1))) :
    (ideleClassArtin L phi hL).ker =
      ideleClassSubgroup L := by
  ext c
  change ideleClassReciprocity L phi hL
      (QuotientGroup.mk' (ideleClassSubgroup L) c) = 1 ↔
    c ∈ ideleClassSubgroup L
  constructor
  · intro h
    apply (QuotientGroup.eq_one_iff c).1
    exact (MulEquiv.map_eq_one_iff
      (ideleClassReciprocity L phi hL)).1 h
  · intro hc
    apply (MulEquiv.map_eq_one_iff
      (ideleClassReciprocity L phi hL)).2
    exact (QuotientGroup.eq_one_iff c).2 hc

/-- The finite Artin package used in Lemma VII.9.1 follows directly from
the global Artin map and the reciprocity law. -/
theorem artin_data_reciprocity
    (phi : IdeleGroup (RingOfIntegers K) K →*
      AbsoluteAbelianGalois K)
    (hphi : ContinuousGlobalArtin phi)
    (hrec : IdeleReciprocityLaw (K := K))
    (L : FASubext K) :
    Nonempty (FiniteArtinData K L) := by
  let hL := (hrec phi hphi).2 L
  exact ⟨{
    artin := ideleClassArtin L phi hL
    surjective := idele_artin_surjective L phi hL
    ker_norm_group := idele_artin_ker L phi hL }⟩

/-- Universe-polymorphic form: Theorems V.5.2 and V.5.3 discharge the
finite-reciprocity bridge in Lemma VII.9.1 for every number field. -/
theorem reciprocity_bridge_global
    (hArtin : ∀ (K : Type u) [Field K] [NumberField K],
      GlobalArtinProposition (K := K))
    (hrec : ∀ (K : Type u) [Field K] [NumberField K],
      IdeleReciprocityLaw (K := K)) :
    FiniteReciprocityBridge.{u} := by
  intro K _ _ L
  obtain ⟨phi, hphi, _⟩ := hArtin K
  exact artin_data_reciprocity phi hphi (hrec K) L

end

end Submission.CField.NLimita
