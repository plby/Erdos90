import Submission.ClassField.LocalReciprocity.DualityConclusion
import Submission.ClassField.LocalReciprocity.Functoriality
import Submission.ClassField.LocalReciprocity.AlgEquiv
import Submission.ClassField.LocalBrauer.ConcreteInflationMorita
import Submission.ClassField.ReciprocityExistence.CupRestriction
import Submission.ClassField.ReciprocityExistence.CupComparison
import Submission.ClassField.NormCorrespondence.InverseLimit
import Submission.ClassField.NormCorrespondence.Main

open scoped IsMulCommutative

/-!
# Milne, Class Field Theory, III.3.3

For nested finite Galois extensions `L / E / K`, restriction from
`Gal(L/K)` to `Gal(E/K)` carries the finite local Artin symbol for `L/K` to
the finite local Artin symbol for `E/K`.  We prove the square by the corrected
argument indicated in Milne's footnote: Proposition III.3.6 identifies Artin
symbols by all rational characters, concrete inflation identifies the two cup
classes, and rational characters separate the finite abelian Galois group.

The final section assembles these compatible finite maps into the inverse
limit defining the abelianized absolute Galois group.
-/

namespace Submission.CField.LRecip

noncomputable section

open CategoryTheory Opposite
open Submission.CField.LFTheory
open Submission.CField.BGroups
open Submission.CField.CProduca
open Submission.CField.LBrauer
open Submission.CField.RExist

universe u

section CupInflation

variable (K Omega : Type u) [Field K] [Field Omega] [Algebra K Omega]
variable {F E : FiniteGaloisIntermediateField K Omega}
variable [IsMulCommutative Gal(F/K)]

attribute [local instance] Units.mulDistribMulActionRight

set_option maxHeartbeats 3000000 in
-- Inflating the explicit cup cocycle and comparing its crossed products
-- requires substantial dependent algebra normalization.
set_option synthInstance.maxHeartbeats 500000 in
omit [IsMulCommutative Gal(F/K)] in
/-- The literal multiplicative character cups at two nested finite Galois
levels define the same Brauer class after inflating the character along
Galois restriction. -/
theorem global_multiplicative_brauer
    (hFE : F ≤ E) (a : Kˣ) (chi : RationalCharacter Gal(F/K)) :
    ((CProduc.hRelativeBrauer K F
        (multiplicativeCupClass K F a chi) :
          relativeBrauerGroup K F) : BrauerGroup K) =
      ((CProduc.hRelativeBrauer K E
        (multiplicativeCupClass K E a
          (chi.comp (galoisRestrictionHom K hFE).toAdditive)) :
            relativeBrauerGroup K E) : BrauerGroup K) := by
  letI : Fact (F ≤ E) := ⟨hFE⟩
  let cF : NMCocycl₂ (G := Gal(F/K)) (M := Fˣ) :=
    invariantCupCocycle
      (Units.map (algebraMap K F).toMonoidHom a)
      (multiplicative_base_fixed K F a) chi
  let cE : NMCocycl₂ (G := Gal(E/K)) (M := Eˣ) :=
    invariantCupCocycle
      (Units.map (algebraMap K E).toMonoidHom a)
      (multiplicative_base_fixed K E a)
      (chi.comp (galoisRestrictionHom K hFE).toAdditive)
  have hcocycle : concreteInflationCocycle K hFE cF = cE := by
    apply NMCocycl₂.ext
    rintro ⟨sigma, tau⟩
    change coefficientUnitsHom K hFE
        ((Units.map (algebraMap K F).toMonoidHom a) ^
          rationalBoundaryExponent chi
            (galoisRestrictionHom K hFE sigma)
            (galoisRestrictionHom K hFE tau)) =
      (Units.map (algebraMap K E).toMonoidHom a) ^
        rationalBoundaryExponent
          (chi.comp (galoisRestrictionHom K hFE).toAdditive)
          sigma tau
    rw [map_zpow, rational_boundary_comp]
    rfl
  change BGroups.brauerClass K
      (CProduc.centralSimpleCSA K F cF) =
    BGroups.brauerClass K
      (CProduc.centralSimpleCSA K E cE)
  rw [← hcocycle]
  exact (BGroups.brauer_class _ _ _).2
    (brauer_equivalent_inflation K cF)

end CupInflation

section LocalTower

variable (K Omega : Type)
  [NontriviallyNormedField K] [IsUltrametricDist K]

local instance globalMultiplicativeCupClassBrauerEqOfLeValuativeRel : ValuativeRel K :=
  ValuativeRel.ofValuation (NormedField.valuation (K := K))

local instance globalMultiplicativeCupClassBrauerEqOfLeValuationCompatible :
    Valuation.Compatible (NormedField.valuation (K := K)) :=
  Valuation.Compatible.ofValuation (NormedField.valuation (K := K))

variable [IsNonarchimedeanLocalField K]
  [Field Omega] [Algebra K Omega]
  {F E : FiniteGaloisIntermediateField K Omega}
  [IsMulCommutative Gal(F/K)]

set_option maxHeartbeats 3000000 in
-- Passing the Brauer-class comparison through the local invariant unfolds
-- both finite-level cohomology equivalences.
set_option synthInstance.maxHeartbeats 500000 in
omit [IsMulCommutative Gal(F/K)] in
/-- The cup invariant is unchanged when a character from a smaller finite
Galois level is inflated along restriction from a larger level. -/
theorem character_cup_restriction
    (hFE : F ≤ E) (a : Kˣ) (chi : RationalCharacter Gal(F/K)) :
    characterCupInvariant K E a
        (chi.comp (galoisRestrictionHom K hFE).toAdditive) =
      characterCupInvariant K F a chi := by
  rw [character_cup_multiplicative,
    character_cup_multiplicative]
  exact congrArg
    (fun x : BrauerGroup K =>
      (carryBrauerInvariant K x).toAdd)
    (global_multiplicative_brauer K Omega hFE a chi).symm

set_option maxHeartbeats 5000000 in
-- The restriction identity combines the character formula with the full
-- finite-level cup-inflation comparison.
set_option synthInstance.maxHeartbeats 500000 in
/-- **Milne III.3.3.** For nested finite abelian Galois levels, Galois
restriction carries the upper finite local Artin homomorphism to the lower
one. -/
theorem abelian_artin_restriction
    [IsMulCommutative Gal(E/K)]
    (hFE : F ≤ E) :
    (galoisRestrictionHom K hFE).comp
        (abelianArtinHom K E) =
      abelianArtinHom K F := by
  apply MonoidHom.ext
  intro a
  apply forall_rational_character
  intro chi
  calc
    chi (Additive.ofMul
        (galoisRestrictionHom K hFE
          (abelianArtinHom K E a))) =
        characterCupInvariant K E a
          (chi.comp (galoisRestrictionHom K hFE).toAdditive) :=
      (comp K E
        (galoisRestrictionHom K hFE) a chi).symm
    _ = characterCupInvariant K F a chi :=
      character_cup_restriction
        K Omega hFE a chi
    _ = chi (Additive.ofMul (abelianArtinHom K F a)) :=
      (transportedCupBoundary K F a chi).symm

set_option maxHeartbeats 5000000 in
-- Factoring ambient restriction through abelianization elaborates several
-- nested Galois and cohomology transports.
set_option synthInstance.maxHeartbeats 500000 in
/-- **Milne III.3.3, abelianized ambient form.**  The ambient extension need
not be abelian.  Restriction to an abelian Galois intermediate field factors
through the ambient abelianization and carries the unconditional Artin map
to the normalized Artin map of that intermediate field. -/
theorem artin_abelianized_restriction
    (hFE : F ≤ E) :
    (Abelianization.lift (galoisRestrictionHom K hFE)).comp
        (localArtinHom K E) =
      abelianArtinHom K F := by
  apply MonoidHom.ext
  intro a
  apply forall_rational_character
  intro chi
  let r : Gal(E/K) →* Gal(F/K) := galoisRestrictionHom K hFE
  let rAb : Abelianization Gal(E/K) →* Gal(F/K) :=
    Abelianization.lift r
  let chiAb : RationalCharacter (Abelianization Gal(E/K)) :=
    chi.comp rAb.toAdditive
  calc
    chi (Additive.ofMul
        (Abelianization.lift (galoisRestrictionHom K hFE)
          (localArtinHom K E a))) =
        chiAb (Additive.ofMul (localArtinHom K E a)) := rfl
    _ = characterCupInvariant K E a
          (chiAb.comp Abelianization.of.toAdditive) :=
      abelianization K E a chiAb
    _ = characterCupInvariant K E a
          (chi.comp r.toAdditive) := by
      rfl
    _ = characterCupInvariant K F a chi :=
      character_cup_restriction
        K Omega hFE a chi
    _ = chi (Additive.ofMul (abelianArtinHom K F a)) :=
      (transportedCupBoundary K F a chi).symm

end LocalTower

section Assembly

variable (K : Type)
  [NontriviallyNormedField K] [IsUltrametricDist K]

local instance assemblyValuativeRel : ValuativeRel K :=
  ValuativeRel.ofValuation (NormedField.valuation (K := K))

local instance assemblyValuationCompatible :
    Valuation.Compatible (NormedField.valuation (K := K)) :=
  Valuation.Compatible.ofValuation (NormedField.valuation (K := K))

variable [IsNonarchimedeanLocalField K]

set_option maxHeartbeats 5000000 in
-- Building the compatible family over every finite Galois level requires a
-- large dependent inverse-system term.
set_option synthInstance.maxHeartbeats 500000 in
/-- The compatible finite-level Artin system supplied by III.3.3 on all
finite Galois levels of the maximal abelian extension. -/
noncomputable def compatibleReciprocityFamily :
    CARecip K where
  hom E := abelianArtinHom K E
  compatible := by
    intro E F f x
    let hFE : F.unop ≤ E.unop := CategoryTheory.leOfHom f.unop
    have hf : f = (CategoryTheory.homOfLE hFE).op := Subsingleton.elim _ _
    rw [hf]
    change galoisRestrictionHom K hFE
        (abelianArtinHom K E.unop x) =
      abelianArtinHom K F.unop x
    exact DFunLike.congr_fun
      (abelian_artin_restriction K
        (maximalAbelianIntermediate K) hFE) x
  equiv E := abelianLocalArtin K E
  equiv_mk _ _ := rfl

/-- The local Artin homomorphism assembled from the compatible finite-level
system of III.3.3. -/
noncomputable def assembledArtinHom :
    Kˣ →* AbsoluteAbelianGalois K :=
  CAArtin.assemble K
    (compatibleReciprocityFamily K).toCAArtin

/-- Every finite projection of the assembled map is the canonical finite
local Artin homomorphism. -/
theorem abelian_restriction_assembled
    (E : FiniteGaloisIntermediateField K
      (maximalAbelianIntermediate K)) (x : Kˣ) :
    localAbelianRestriction (maximalAbelianSubextension K E)
        (assembledArtinHom K x) =
      (maximalAbelianLevel K E).autCongr
        (abelianArtinHom K E x) := by
  exact CAArtin.abelian_restriction_assemble
    K
    (compatibleReciprocityFamily K).toCAArtin
    E x

/-- Every finite projection of the inverse-limit assembly is literally the
cohomologically normalized finite Artin homomorphism, including finite
abelian subextensions not already presented as levels of the chosen
maximal-abelian model. -/
theorem restriction_assembled_all
    (L : FASubext K) (x : Kˣ) :
    localAbelianRestriction L (assembledArtinHom K x) =
      abelianArtinHom K L.1 x := by
  obtain ⟨E, hE⟩ := maximal_abelian_subextension K L
  subst L
  rw [abelian_restriction_assembled]
  exact DFunLike.congr_fun
    (abelian_artin_alg K E
      (maximalAbelianSubextension K E).1
      (maximalAbelianLevel K E)) x

/-- The inverse-limit assembly induces the canonical norm-residue
equivalence at every finite abelian level. -/
theorem induces_reciprocity_assembled
    (E : FiniteGaloisIntermediateField K
      (maximalAbelianIntermediate K)) :
    InducesLocalReciprocity K (assembledArtinHom K)
      (maximalAbelianSubextension K E) :=
  CARecip.induce_recip_assem
    K (compatibleReciprocityFamily K) E

/-- The assembled local Artin homomorphism induces the canonical
norm-residue equivalence on every finite abelian subextension of the fixed
separable closure. -/
theorem induces_assembled_all
    (L : FASubext K) :
    InducesLocalReciprocity K (assembledArtinHom K) L :=
  CARecip.induces_assemble_all
    K (compatibleReciprocityFamily K) L

/-- **Corollary I.1.2, instantiated by III.3.3.**  The compatible finite
Artin maps and their inverse-limit assembly give the bijective,
order-reversing local norm correspondence, including the compositum,
intersection, and supergroup formulas. -/
theorem correspondence_assembled_artin :
    LocalNormCorrespondence K :=
  local_correspondence_reciprocity
    (assembledArtinHom K)
    (induces_assembled_all K)

end Assembly

end

end Submission.CField.LRecip
