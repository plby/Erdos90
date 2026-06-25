import Towers.ClassField.Reciprocity.ArtinMapStatements

/-!
# Chapter V, Section 5, Summary 5.10

This file packages the summary exactly in the idèle model used in this
development.  The finite-layer bottom maps are the quotient isomorphisms of
Theorem 5.3, and their commutativity says that they are induced by restriction
of the single absolute global Artin map.

Finite-layer reciprocity proves surjectivity after every finite restriction.
Passing from this to surjectivity onto the inverse-limit absolute abelian
Galois group is the remaining compactness/closed-image input; it is named
separately below rather than hidden in an unrelated hypothesis.
-/

namespace Towers.CField.Recip

open NumberField
open Towers.CField.LFTheory
open Towers.CField.Ideles

noncomputable section

universe u

variable {K : Type u} [Field K] [NumberField K]

local notation "𝓞K" => NumberField.RingOfIntegers K

noncomputable local instance summaryFiniteAbelianSubextensionNumberField
    (L : FASubext K) : NumberField L.1 :=
  NumberField.of_module_finite K L.1

/-- The complete data asserted in Summary V.5.10. -/
structure AbsoluteReciprocityData where
  /-- The global reciprocity (Artin) map. -/
  artin : IdeleGroup 𝓞K K →* AbsoluteAbelianGalois K
  continuous_artin : Continuous artin
  surjective_artin : Function.Surjective artin
  local_compatibility : GlobalArtin artin
  principal_mem_kernel :
    TrivialPrincipalIdeles 𝓞K K
      (AbsoluteAbelianGalois K) artin
  /-- The lower horizontal isomorphism in the diagram, at every finite
  abelian layer. -/
  finiteLayerEquiv : ∀ L : FASubext K,
    IdeleGroup 𝓞K K ⧸
        (principalIdeles 𝓞K K ⊔
          ideleNormSubgroup (K := K) (L := L.1)) ≃*
      Gal(L.1/K)
  /-- The displayed square commutes: the lower isomorphism is induced by
  restriction of the absolute Artin map. -/
  finite_equiv_mk : ∀ (L : FASubext K)
      (a : IdeleGroup 𝓞K K),
    finiteLayerEquiv L
        (QuotientGroup.mk'
          (principalIdeles 𝓞K K ⊔
            ideleNormSubgroup (K := K) (L := L.1)) a) =
      localAbelianRestriction L (artin a)

/-- The precise inverse-limit step not contained in finite-layer
reciprocity: the continuous global Artin map characterized by all local maps
is onto the absolute abelian Galois group. -/
def AbsoluteArtinSurjectivity : Prop :=
  ∀ phi : IdeleGroup 𝓞K K →* AbsoluteAbelianGalois K,
    ContinuousGlobalArtin phi →
    (∀ L : FASubext K,
      Function.Surjective ((localAbelianRestriction L).comp phi)) →
    Function.Surjective phi

/-- Proposition 5.2, Theorem 5.3, and the exact inverse-limit surjectivity
step imply every clause of Summary 5.10. -/
theorem reciprocity_layers_surjectivity
    (hArtin : GlobalArtinProposition (K := K))
    (hReciprocity : IdeleReciprocityLaw (K := K))
    (hSurjective : AbsoluteArtinSurjectivity (K := K)) :
    Nonempty (AbsoluteReciprocityData (K := K))
  := by
  obtain ⟨phi, hphi, _⟩ :=
    global_proposition_reciprocity hArtin hReciprocity
  let hfinite : ∀ L : FASubext K,
      FiniteReciprocityLaw 𝓞K K Gal(L.1/K)
        ((localAbelianRestriction L).comp phi)
        (ideleNormSubgroup (K := K) (L := L.1)) := hphi.2.2
  have honto : Function.Surjective phi :=
    hSurjective phi hphi.1 (fun L ↦ (hfinite L).1)
  let e : ∀ L : FASubext K,
      IdeleGroup 𝓞K K ⧸
          (principalIdeles 𝓞K K ⊔
            ideleNormSubgroup (K := K) (L := L.1)) ≃*
        Gal(L.1/K) :=
    fun L ↦ finiteReciprocityEquiv 𝓞K K Gal(L.1/K)
      ((localAbelianRestriction L).comp phi)
      (ideleNormSubgroup (K := K) (L := L.1)) (hfinite L)
  refine ⟨{
    artin := phi
    continuous_artin := hphi.1.1
    surjective_artin := honto
    local_compatibility := hphi.1.2
    principal_mem_kernel := hphi.2.1
    finiteLayerEquiv := e
    finite_equiv_mk := ?_ }⟩
  intro L a
  exact finite_reciprocity_mk 𝓞K K Gal(L.1/K)
    ((localAbelianRestriction L).comp phi)
    (ideleNormSubgroup (K := K) (L := L.1)) (hfinite L) a

end

end Towers.CField.Recip
