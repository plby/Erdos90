import Submission.NumberTheory.Completions.AdicLocalRing
import Submission.NumberTheory.Galois.DecompositionGroup
import Submission.NumberTheory.Galois.FrobeniusElement
import Submission.ClassField.NormCorrespondence.LocalStatement
import Submission.ClassField.Ideles.FinitePlaceCompletion
import Submission.ClassField.Ideles.IdeleClassNorm
import Submission.ClassField.Reciprocity.Reciprocity
import Submission.ClassField.Reciprocity.UniversePlaceArtin
import Submission.ClassField.IdeleCohomology.CompletionProductAction


/-!
# Chapter V, Section 5: statements of the main idelic theorems

This file states the local-to-global Artin-map proposition, the idelic
reciprocity law, and the idelic existence theorem.  The local compatibility
predicate at a finite place is defined by an actual Chapter I local reciprocity
map on the completed base, transported through the canonical identification
of the local Galois group with the global decomposition group.
-/

namespace Submission.CField.Recip

open Ideal IsDedekindDomain NumberField
open Submission.NumberTheory.Milne
open Submission.CField.LFTheory
open Submission.CField.Ideles
open Submission.CField.ICohomo
open scoped IsMulCommutative

noncomputable section

universe u

variable {K : Type u} [Field K] [NumberField K]

noncomputable local instance finiteAbelianSubextensionNumberField
    (L : FASubext K) : NumberField L.1 :=
  NumberField.of_module_finite K L.1

/-- Arithmetic Frobenius in a finite abelian subextension at an unramified
upper prime. -/
noncomputable def subextensionArithmeticFrobenius
    (L : FASubext K)
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (Q : UpperPrimeFactors (K := K) (L := L.1) P)
    [Algebra.IsUnramifiedAt (NumberField.RingOfIntegers K)
      (upperPrime (K := K) (L := L.1) P Q).asIdeal] :
    Gal(L.1/K) := by
  let q := upperPrime (K := K) (L := L.1) P Q
  letI : q.asIdeal.LiesOver P.asIdeal := by
    refine ⟨?_⟩
    exact (congrArg HeightOneSpectrum.asIdeal
      (upperPrime_under (K := K) (L := L.1) P Q)).symm
  letI : MulSemiringAction Gal(L.1/K) (NumberField.RingOfIntegers L.1) :=
    IsIntegralClosure.MulSemiringAction
      (NumberField.RingOfIntegers K) K L.1
      (NumberField.RingOfIntegers L.1)
  letI : IsGaloisGroup Gal(L.1/K) (NumberField.RingOfIntegers K)
      (NumberField.RingOfIntegers L.1) :=
    IsGaloisGroup.of_isFractionRing Gal(L.1/K)
      (NumberField.RingOfIntegers K) (NumberField.RingOfIntegers L.1) K L.1
  exact arithFrobAt (NumberField.RingOfIntegers K) Gal(L.1/K) q.asIdeal

set_option maxHeartbeats 800000 in
-- The nested completion and automorphism transports require a larger elaboration budget.
/-- A finite-place map is the finite norm-residue map for the completed layer.

The absolute value `w` lies literally over the base absolute value, as required
by the completion and decomposition-group APIs, while its equivalence with the
normalized finite place says that it represents the specified upper prime `Q`.
The norm-residue equivalence of the completed extension is transported to the
global decomposition group through
`decompositionCompletionExtension`.

This finite-layer predicate deliberately does not demand an already assembled
absolute local reciprocity map.  Requiring that stronger object here made the
finite product construction circular: Proposition V.5.2 only uses the finite
norm-residue maps. -/
def LayerLocalArtin
    (L : FASubext K)
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (Q : UpperPrimeFactors (K := K) (L := L.1) P)
    (phi : (P.adicCompletion K)ˣ →* Gal(L.1/K)) : Prop := by
  let v := (FinitePlace.mk P).val
  let q := upperPrime (K := K) (L := L.1) P Q
  exact ∃ (w : AbsoluteValue L.1 ℝ)
      (hwv : AbsoluteValue.LiesOver w v),
    w.IsEquiv (FinitePlace.mk q).val ∧
      letI : Fact v.IsNontrivial :=
        ⟨absolute_value_nontrivial P⟩
      letI : NontriviallyNormedField v.Completion :=
        placeNontriviallyNormed P
      letI : IsUltrametricDist v.Completion :=
        placeUltrametricDist P
      letI : ValuativeRel v.Completion :=
        placeValuativeRel P
      letI : IsNonarchimedeanLocalField v.Completion :=
        placeNonarchimedeanField P
      letI : Fact (AbsoluteValue.LiesOver w v) := ⟨hwv⟩
      letI : Algebra v.Completion w.Completion :=
        (completionLies v w hwv).toAlgebra
      ∃ e : (v.Completionˣ ⧸ normSubgroup v.Completion w.Completion) ≃*
          Gal(w.Completion/v.Completion),
        (∀ x : (P.adicCompletion K)ˣ,
          phi x =
            ((decompositionCompletionExtension v w).symm
              (e (QuotientGroup.mk' (normSubgroup v.Completion w.Completion)
                (Units.map
                  (placeCompletionAdic P).symm.toRingHom
                  x))) : Gal(L.1/K))) ∧
        ∀ q : CompletionPlacesAbove (L := L.1) v,
          phi = adicArtinUniverse K L.1 P q

/-- An infinite-place map is the local Artin map at the layer `L/K` when it
induces the norm-residue isomorphism onto the archimedean decomposition
group.  This includes the real-complex sign map and the trivial cases. -/
def InfiniteLayerArtin
    (L : FASubext K)
    (v : InfinitePlace K)
    (w : InfinitePlacesAbove (K := K) (L := L.1) v)
    (phi : v.1.Completionˣ →* Gal(L.1/K)) : Prop :=
  ∃ e : (v.1.Completionˣ ⧸
        (infiniteCompletionNorm (K := K) (L := L.1) v w).range) ≃*
      absoluteValueDecomposition v.1 w.1.1,
    ∀ x : v.1.Completionˣ,
      phi x = (e (QuotientGroup.mk'
        (infiniteCompletionNorm (K := K) (L := L.1) v w).range x) : Gal(L.1/K))

/-- The local compatibility squares characterizing the global Artin map.
At every place the local maps are the corresponding finite norm-residue
isomorphisms. -/
def GlobalArtin
    (phi : IdeleGroup (NumberField.RingOfIntegers K) K →*
      AbsoluteAbelianGalois K) : Prop :=
  (∀ (L : FASubext K)
      (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
      (Q : UpperPrimeFactors (K := K) (L := L.1) P),
    ∃ phi_v : (P.adicCompletion K)ˣ →* Gal(L.1/K),
      LayerLocalArtin L P Q phi_v ∧
      ∀ x : (P.adicCompletion K)ˣ,
        localAbelianRestriction L
            (phi (finitePlaceEmbedding (NumberField.RingOfIntegers K) K P x)) =
          phi_v x) ∧
  ∀ (L : FASubext K) (v : InfinitePlace K)
      (w : InfinitePlacesAbove (K := K) (L := L.1) v),
    ∃ phi_v : v.1.Completionˣ →* Gal(L.1/K),
      InfiniteLayerArtin L v w phi_v ∧
      ∀ x : v.1.Completionˣ,
        localAbelianRestriction L
            (phi (infinitePlaceEmbedding
              (NumberField.RingOfIntegers K) K v x)) = phi_v x

/-- A global Artin map is continuous and has all the required finite-level
local compatibility squares. -/
def ContinuousGlobalArtin
    (phi : IdeleGroup (NumberField.RingOfIntegers K) K →*
      AbsoluteAbelianGalois K) : Prop :=
  Continuous phi ∧ GlobalArtin phi

/-- **Proposition V.5.2, statement.** There is a unique continuous global
Artin homomorphism whose restriction to every finite abelian layer commutes
with every local Artin map. -/
def GlobalArtinProposition : Prop :=
  ∃! phi : IdeleGroup (NumberField.RingOfIntegers K) K →*
      AbsoluteAbelianGalois K,
    ContinuousGlobalArtin phi

/-- The image of the idele norm in the idele class group. -/
def ideleClassSubgroup (L : FASubext K) :
    Subgroup (IdeleClassGroup (NumberField.RingOfIntegers K) K) :=
  (ideleNormSubgroup (K := K) (L := L.1)).map
    (QuotientGroup.mk' (principalIdeles (NumberField.RingOfIntegers K) K))

/-- The subgroup used in the idelic existence theorem is the range of the
canonical norm on idele class groups. -/
theorem idele_class_range
    (L : FASubext K) :
    ideleClassSubgroup L =
      (canonicalIdeleNorm (K := K) (L := L.1)).range :=
  (canonical_idele_range (K := K) (L := L.1)).symm

/-- **Theorem V.5.3 (Recip Law), statement.** The global Artin map is
trivial on principal ideles, and at every finite abelian layer it is
surjective with kernel equal to the product of the principal ideles and the
idele norm subgroup.  Equivalently it induces the book's displayed quotient
isomorphism. -/
def IdeleReciprocityLaw : Prop :=
  ∀ phi : IdeleGroup (NumberField.RingOfIntegers K) K →*
      AbsoluteAbelianGalois K,
    ContinuousGlobalArtin phi →
      TrivialPrincipalIdeles (NumberField.RingOfIntegers K) K
          (AbsoluteAbelianGalois K) phi ∧
      ∀ L : FASubext K,
        FiniteReciprocityLaw (NumberField.RingOfIntegers K) K Gal(L.1/K)
          ((localAbelianRestriction L).comp phi)
          (ideleNormSubgroup (K := K) (L := L.1))

/-- **Theorem V.5.5 (Existence Theorem), statement.** Open finite-index
subgroups of the idele class group are precisely the norm groups of unique
finite abelian subextensions of the fixed separable closure. -/
def IdeleExistenceTheorem : Prop :=
  ∀ N : Subgroup (IdeleClassGroup (NumberField.RingOfIntegers K) K),
    IsOpen (N : Set (IdeleClassGroup (NumberField.RingOfIntegers K) K)) →
    N.FiniteIndex →
      ∃! L : FASubext K,
        ideleClassSubgroup L = N

/-- **V.5.2 and V.5.3 together.**  Existence and uniqueness of the continuous
global Artin map, together with the reciprocity law, produce a unique map
which is trivial on principal ideles and satisfies the finite-layer
surjectivity and kernel formula. -/
theorem global_proposition_reciprocity
    (hArtin : GlobalArtinProposition (K := K))
    (hReciprocity : IdeleReciprocityLaw (K := K)) :
    ∃! phi : IdeleGroup (NumberField.RingOfIntegers K) K →*
        AbsoluteAbelianGalois K,
      ContinuousGlobalArtin phi ∧
        TrivialPrincipalIdeles (NumberField.RingOfIntegers K) K
          (AbsoluteAbelianGalois K) phi ∧
        ∀ L : FASubext K,
          FiniteReciprocityLaw (NumberField.RingOfIntegers K) K Gal(L.1/K)
            ((localAbelianRestriction L).comp phi)
            (ideleNormSubgroup (K := K) (L := L.1)) := by
  rcases hArtin with ⟨phi, hphi, hunique⟩
  refine ⟨phi, ⟨hphi, hReciprocity phi hphi⟩, ?_⟩
  intro psi hpsi
  exact hunique psi hpsi.1

end

end Submission.CField.Recip
