import Submission.ClassField.LocalReciprocity.Functoriality
import Submission.ClassField.LocalReciprocity.DualityConclusion
import Submission.ClassField.CrossedProducts.CoefficientTransport
import Submission.ClassField.ReciprocityExistence.CupComparison
import Submission.ClassField.ReciprocityExistence.CupRestriction

open scoped IsMulCommutative

/-!
# Naturality of the finite local Artin map under field equivalence

The finite Artin homomorphism is unchanged when the chosen model of the
finite Galois extension is replaced by an algebra-equivalent one.  This is
the transport needed when a completion is realized as its field range in a
normal closure.
-/

namespace Submission.CField.LRecip

open Submission.CField.BGroups
open Submission.CField.CProduca
open Submission.CField.LBrauer
open Submission.CField.RExist

noncomputable section

variable (K L E : Type)
  [NontriviallyNormedField K] [IsUltrametricDist K]

local instance algEquivValuativeRel : ValuativeRel K :=
  ValuativeRel.ofValuation (NormedField.valuation (K := K))

local instance algEquivValuationCompatible :
    Valuation.Compatible (NormedField.valuation (K := K)) :=
  Valuation.Compatible.ofValuation (NormedField.valuation (K := K))

variable [IsNonarchimedeanLocalField K]
  [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
  [Field E] [Algebra K E] [FiniteDimensional K E] [IsGalois K E]

attribute [local instance] Units.mulDistribMulActionRight

set_option maxHeartbeats 3000000 in
-- The two crossed-product representatives are compared after transporting
-- both their Galois indices and their coefficient units.
/-- The character cup invariant is natural under a `K`-algebra equivalence
of finite Galois extensions. -/
theorem character_cup_alg
    (e : L ≃ₐ[K] E) (a : Kˣ) (chi : RationalCharacter Gal(E/K)) :
    characterCupInvariant K L a
        (chi.comp e.autCongr.toAdditive.toAddMonoidHom) =
      characterCupInvariant K E a chi := by
  let cL : NMCocycl₂ (G := Gal(L/K)) (M := Lˣ) :=
    invariantCupCocycle
      (Units.map (algebraMap K L).toMonoidHom a)
      (multiplicative_base_fixed K L a)
      (chi.comp e.autCongr.toAdditive.toAddMonoidHom)
  let cE : NMCocycl₂ (G := Gal(E/K)) (M := Eˣ) :=
    invariantCupCocycle
      (Units.map (algebraMap K E).toMonoidHom a)
      (multiplicative_base_fixed K E a) chi
  have hc : transportedGaloisCocycle e.toRingEquiv.toRingHom e.autCongr
      (fun sigma x => by simp [AlgEquiv.autCongr_apply]) cL = cE := by
    apply NMCocycl₂.ext
    rintro ⟨sigma, tau⟩
    obtain ⟨sigma, rfl⟩ := e.autCongr.surjective sigma
    obtain ⟨tau, rfl⟩ := e.autCongr.surjective tau
    rw [transported_galois_cocycle]
    dsimp only [cL, cE, invariantCupCocycle]
    rw [map_zpow]
    have hexp : rationalBoundaryExponent
        (chi.comp e.autCongr.toAdditive.toAddMonoidHom) sigma tau =
      rationalBoundaryExponent chi (e.autCongr sigma)
        (e.autCongr tau) := by
      simpa only using rational_boundary_comp
        e.autCongr.toMonoidHom chi sigma tau
    rw [hexp]
    congr 1
    apply Units.ext
    exact e.commutes (a : K)
  have hbrauer := brauer_transported_cocycle K L E e cL
  rw [hc] at hbrauer
  rw [character_cup_multiplicative,
    character_cup_multiplicative]
  exact congrArg
    (fun x : BrauerGroup K => (carryBrauerInvariant K x).toAdd)
    hbrauer

set_option maxHeartbeats 3000000 in
-- Character separation turns the transported cup-class identity into an
-- equality of the two normalized Artin homomorphisms.
/-- The normalized finite local Artin homomorphism commutes with transport
of the finite Galois extension through a base-field algebra equivalence. -/
theorem abelian_artin_alg
    [IsMulCommutative Gal(L/K)] [IsMulCommutative Gal(E/K)]
    (e : L ≃ₐ[K] E) :
    e.autCongr.toMonoidHom.comp (abelianArtinHom K L) =
      abelianArtinHom K E := by
  apply MonoidHom.ext
  intro a
  apply forall_rational_character
  intro chi
  calc
    chi (Additive.ofMul
        (e.autCongr (abelianArtinHom K L a))) =
        characterCupInvariant K L a
          (chi.comp e.autCongr.toAdditive.toAddMonoidHom) :=
      (comp K L e.autCongr.toMonoidHom a chi).symm
    _ = characterCupInvariant K E a chi :=
      character_cup_alg K L E e a chi
    _ = chi (Additive.ofMul (abelianArtinHom K E a)) :=
      (transportedCupBoundary K E a chi).symm

set_option maxHeartbeats 3000000 in
-- The same character-separation argument is applied after passing both
-- possibly noncommutative Galois groups to their abelianizations.
/-- The unconditional abelianization-valued local Artin homomorphism is
natural under a base-field algebra equivalence. -/
theorem artin_hom_alg
    (e : L ≃ₐ[K] E) :
    e.autCongr.abelianizationCongr.toMonoidHom.comp
        (localArtinHom K L) =
      localArtinHom K E := by
  apply MonoidHom.ext
  intro a
  apply forall_rational_character
  intro chi
  let eAb : Abelianization Gal(L/K) ≃* Abelianization Gal(E/K) :=
    e.autCongr.abelianizationCongr
  let chiE : RationalCharacter Gal(E/K) :=
    chi.comp Abelianization.of.toAdditive
  calc
    chi (Additive.ofMul
        (eAb (localArtinHom K L a))) =
        (chi.comp eAb.toAdditive.toAddMonoidHom)
          (Additive.ofMul (localArtinHom K L a)) := rfl
    _ =
        characterCupInvariant K L a
          ((chi.comp eAb.toAdditive.toAddMonoidHom).comp
            Abelianization.of.toAdditive) :=
      abelianization K L a
        (chi.comp eAb.toAdditive.toAddMonoidHom)
    _ = characterCupInvariant K L a
          (chiE.comp e.autCongr.toAdditive.toAddMonoidHom) := by
      rfl
    _ = characterCupInvariant K E a chiE :=
      character_cup_alg K L E e a chiE
    _ = chi (Additive.ofMul (localArtinHom K E a)) :=
      (abelianization K E a chi).symm

end

end Submission.CField.LRecip
