import Submission.ClassField.LocalReciprocity.UniversePolymorphicArtin
import Submission.ClassField.CrossedProducts.CoefficientTransport
import Submission.ClassField.ReciprocityExistence.CupRestriction

/-!
# Universe-polymorphic naturality of the finite local Artin map

The original algebra-equivalence comparison for Proposition III.3.6 is
specialized to `Type 0`.  The ambient cup-pairing construction is available
in every universe, and the crossed-product coefficient transport already
lives in one arbitrary common universe.  This file combines them to obtain
the naturality theorem needed by universe-polymorphic completion models.
-/

namespace Submission.CField.LRecip

open Submission.CField.BGroups
open Submission.CField.CProduca
open Submission.CField.LBrauer
open Submission.CField.RExist
open scoped IsMulCommutative

noncomputable section

universe u

variable (K L E : Type u)
  [NontriviallyNormedField K] [IsUltrametricDist K]
  [ValuativeRel K]
  [Valuation.Compatible (NormedField.valuation (K := K))]
  [IsNonarchimedeanLocalField K]
  [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
  [Field E] [Algebra K E] [FiniteDimensional K E] [IsGalois K E]

attribute [local instance] Units.mulDistribMulActionRight

set_option maxHeartbeats 3000000 in
-- Transporting the crossed-product cocycle and its Brauer class elaborates together.
/-- The ambient character-cup invariant is natural under a `K`-algebra
equivalence of finite Galois extensions. -/
theorem ambient_character_cup
    [IsMulCommutative Gal(L/K)] [IsMulCommutative Gal(E/K)]
    (e : L ≃ₐ[K] E) (a : Kˣ)
    (chi : CharacterModule (Additive Gal(E/K))) :
    ambientCupInvariant K L a
        (chi.comp e.autCongr.toAdditive) =
      ambientCupInvariant K E a chi := by
  let cL : NMCocycl₂ (G := Gal(L/K)) (M := Lˣ) :=
    invariantCupCocycle
      (Units.map (algebraMap K L).toMonoidHom a)
      (multiplicative_base_fixed K L a)
      (chi.comp e.autCongr.toAdditive)
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
        (chi.comp e.autCongr.toAdditive) sigma tau =
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
  change (carryBrauerInvariant K
      (CProduc.brauerClass K L cL)).toAdd =
    (carryBrauerInvariant K
      (CProduc.brauerClass K E cE)).toAdd
  exact congrArg
    (fun x : BrauerGroup K => (carryBrauerInvariant K x).toAdd)
    hbrauer

set_option maxHeartbeats 3000000 in
-- Character separation expands both ambient Artin constructions.
/-- The universe-polymorphic finite local Artin homomorphism commutes with
transport of the extension through a base-field algebra equivalence. -/
theorem abelian_universe_alg
    [IsMulCommutative Gal(L/K)] [IsMulCommutative Gal(E/K)]
    (e : L ≃ₐ[K] E) :
    e.autCongr.toMonoidHom.comp
        (abelianArtinUniverse K L) =
      abelianArtinUniverse K E := by
  apply MonoidHom.ext
  intro a
  apply forall_rational_character
  intro chi
  calc
    chi (Additive.ofMul
        (e.autCongr (abelianArtinUniverse K L a))) =
        characterCupUniverse K L a
          (chi.comp e.autCongr.toAdditive) :=
      (abelian_universe_comp K L e.autCongr.toMonoidHom a chi).symm
    _ = characterCupUniverse K E a chi :=
      ambient_character_cup K L E e a chi
    _ = chi (Additive.ofMul
        (abelianArtinUniverse K E a)) :=
      (abelian_universe_character K E a chi).symm

end

end Submission.CField.LRecip
