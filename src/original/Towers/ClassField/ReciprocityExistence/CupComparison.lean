import Towers.ClassField.LocalReciprocity.CupPairing
import Towers.ClassField.CohomologyOps.Naturality
import Towers.ClassField.ReciprocityExistence.MultiplicativeCup
import Towers.ClassField.ReciprocityExistence.FieldCup

namespace Towers.CField.RExist
open CategoryTheory Rep
open scoped MonoidalCategory
open Towers.CField.Shifting
open Towers.CField.COps.CPBuild
open Towers.CField.LRecip
open Towers.CField.LClass
open Towers.CField.CProduca
open Towers.CField.LBrauer
open Towers.CField.BGroups
noncomputable section

variable {G : Type} [Group G] [Fintype G]

noncomputable def boundaryExponentCocycle
    (chi : RationalCharacter G) :
    groupCohomology.cocycles₂ (Rep.trivial ℤ G ℤ) := by
  refine ⟨fun p => rationalBoundaryExponent chi p.1 p.2, ?_⟩
  rw [groupCohomology.mem_cocycles₂_iff]
  intro g h j
  simpa using rational_boundary_cocycle chi g h j

theorem character_boundary_cocycle
    (chi : RationalCharacter G) :
    characterBoundary G chi =
      groupCohomology.H2π (Rep.trivial ℤ G ℤ)
        (boundaryExponentCocycle chi) := by
  rw [characterBoundary]
  change groupCohomology.δ
      (sequence_short_exact G) 1 2 rfl
      (groupCohomology.H1π (Rep.trivial ℤ G rationalModIntegers)
        ((groupCohomology.cocycles₁IsoOfIsTrivial
          (Rep.trivial ℤ G rationalModIntegers)).inv
            (characterRationalIntegers G chi))) = _
  let c := (groupCohomology.cocycles₁IsoOfIsTrivial
    (Rep.trivial ℤ G rationalModIntegers)).inv
      (characterRationalIntegers G chi)
  let y : G → ℚ := fun g => rationalCharacterLift chi g
  let x : G × G → ℤ :=
    fun p => rationalBoundaryExponent chi p.1 p.2
  have hy :
      (integerRationalSequence G).g.hom ∘ y = c := by
    funext g
    change (Submodule.Quotient.mk (rationalCharacterLift chi g) :
        rationalModIntegers) =
      characterRationalIntegers G chi (Additive.ofMul g)
    apply rationalIntegersInvariant.injective
    rw [rational_integers_mk]
    change (rationalCharacterLift chi g : AddCircle (1 : ℚ)) =
      rationalIntegersInvariant
        (rationalIntegersInvariant.symm
          (chi (Additive.ofMul g)))
    rw [AddEquiv.apply_symm_apply]
    exact rational_character_coe chi g
  have hx :
      (integerRationalSequence G).f.hom ∘ x =
        groupCohomology.d₁₂
          (integerRationalSequence G).X₂ y := by
    funext p
    change ((rationalBoundaryExponent chi p.1 p.2 : ℤ) : ℚ) =
      rationalCharacterLift chi p.2 -
        rationalCharacterLift chi (p.1 * p.2) +
          rationalCharacterLift chi p.1
    exact rational_boundary_spec chi p.1 p.2
  simpa [c, x, boundaryExponentCocycle] using
    groupCohomology.δ₁_apply
      (sequence_short_exact G) c y hy x hx

variable (K L : Type)
  [NontriviallyNormedField K] [IsUltrametricDist K]

local instance scratchBoundaryValuativeRel : ValuativeRel K :=
  ValuativeRel.ofValuation (NormedField.valuation (K := K))

local instance scratchBoundaryCompatible :
    Valuation.Compatible (NormedField.valuation (K := K)) :=
  Valuation.Compatible.ofValuation (NormedField.valuation (K := K))

variable [IsNonarchimedeanLocalField K]
  [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]

attribute [local instance] Units.mulDistribMulActionRight

theorem unitor_tensor_int
    {J : Type} [Group J]
    (M : Rep ℤ J) (m : M) (z : ℤ) :
    (ρ_ M).hom
        (tensorElement M (𝟙_ (Rep ℤ J)) m z) = z • m := by
  simp only [tensor_V, tensorUnit_V, tensor_ρ, tensorUnit_ρ,
    hom_hom_rightUnitor, Representation.Equiv.coe_toIntertwiningMap]
  exact int_smul_eq_zsmul M.hV2 z m

set_option maxHeartbeats 2000000 in
-- Comparing the categorical cup product with the explicit multiplicative
-- cocycle requires normalizing a large bar-resolution expression.
omit [IsUltrametricDist K] [IsNonarchimedeanLocalField K] [IsGalois K L] in
theorem character_boundary_multiplicative
    (a : Kˣ) (chi : RationalCharacter Gal(L/K)) :
    cupCharacterBoundary K L a chi =
      multiplicative2Additive
        (multiplicativeCupClass K L a chi) := by
  let M := Rep.ofMulDistribMulAction Gal(L/K) Lˣ
  let Z : Rep ℤ Gal(L/K) := 𝟙_ (Rep ℤ Gal(L/K))
  let baseC : groupCohomology.cocycles M 0 :=
    (groupCohomology.cocyclesIso₀ M).inv (baseUnitInvariant K L a)
  let boundC := boundaryExponentCocycle chi
  let boundGeneral : groupCohomology.cocycles Z 2 :=
    (groupCohomology.isoCocycles₂ Z).inv boundC
  rw [cupCharacterBoundary]
  rw [character_boundary_cocycle]
  change groupCohomology.map (MonoidHom.id Gal(L/K))
      (ρ_ M).hom 2
      (cupCohomology M Z 0 2
        (groupCohomology.π M 0 baseC)
        (groupCohomology.π Z 2 boundGeneral)) = _
  rw [cupCohomology_π]
  rw [multiplicativeCupClass, invariantCharacterCup]
  rw [multiplicative_2_mk]
  rw [NMCocycl₂.toAdditiveH2]
  change groupCohomology.map (MonoidHom.id Gal(L/K))
      (ρ_ M).hom 2
      (groupCohomology.π (M ⊗ Z) 2
        (cupCocycle M Z 0 2 baseC boundGeneral)) = _
  have hmap := groupCohomology.π_map_apply
    (MonoidHom.id Gal(L/K)) (ρ_ M).hom 2
      (cupCocycle M Z 0 2 baseC boundGeneral)
  have hmap' :
      groupCohomology.map (MonoidHom.id Gal(L/K)) (ρ_ M).hom 2
          (groupCohomology.π (M ⊗ Z) 2
            (cupCocycle M Z 0 2 baseC boundGeneral)) =
        groupCohomology.π M 2
          (groupCohomology.cocyclesMap (MonoidHom.id Gal(L/K))
            (ρ_ M).hom 2 (cupCocycle M Z 0 2 baseC boundGeneral)) := by
    simpa only [Z] using hmap
  rw [hmap']
  change groupCohomology.π M 2
      (groupCohomology.cocyclesMap (MonoidHom.id Gal(L/K))
        (ρ_ M).hom 2 (cupCocycle M Z 0 2 baseC boundGeneral)) =
    groupCohomology.π M 2
      ((groupCohomology.isoCocycles₂ M).inv
        (groupCohomology.cocyclesOfIsMulCocycle₂
          (invariantCupCocycle
            (Units.map (algebraMap K L).toMonoidHom a)
            (multiplicative_base_fixed K L a) chi).isMulCocycle₂))
  apply congrArg (groupCohomology.π M 2)
  apply (ModuleCat.mono_iff_injective
    (groupCohomology.iCocycles M 2)).1 inferInstance
  rw [i_cocycles_id]
  dsimp only [Z]
  funext p
  have hcup := congrFun (i_cup_cocycle
    M (𝟙_ (Rep ℤ Gal(L/K))) 0 2 baseC boundGeneral) p
  change (ρ_ M).hom
      (groupCohomology.iCocycles
        (M ⊗ 𝟙_ (Rep ℤ Gal(L/K))) 2
        (cupCocycle M (𝟙_ (Rep ℤ Gal(L/K)))
          0 2 baseC boundGeneral) p) = _
  rw [hcup]
  have hout := congrFun
    (groupCohomology.isoCocycles₂_inv_comp_iCocycles_apply M
      (groupCohomology.cocyclesOfIsMulCocycle₂
        (invariantCupCocycle
          (Units.map (algebraMap K L).toMonoidHom a)
          (multiplicative_base_fixed K L a) chi).isMulCocycle₂)) p
  have hbase := congrFun
    (groupCohomology.cocyclesIso₀_inv_comp_iCocycles_apply M
      (baseUnitInvariant K L a)) (fun i => p (Fin.castAdd 2 i))
  have hbound := congrFun
    (groupCohomology.isoCocycles₂_inv_comp_iCocycles_apply
      (𝟙_ (Rep ℤ Gal(L/K))) boundC) (fun j => p (Fin.natAdd 0 j))
  have hbase' :
      groupCohomology.iCocycles M 0 baseC
          (fun i => p (Fin.castAdd 2 i)) =
        Additive.ofMul (Units.map (algebraMap K L).toMonoidHom a) :=
    hbase.trans (by rfl)
  have hbound' :
      groupCohomology.iCocycles (𝟙_ (Rep ℤ Gal(L/K))) 2 boundGeneral
          (fun j => p (Fin.natAdd 0 j)) =
        rationalBoundaryExponent chi (p 0) (p 1) :=
    hbound.trans (by rfl)
  calc
    _ = (ρ_ M).hom
          (tensorElement M (𝟙_ (Rep ℤ Gal(L/K)))
            (Additive.ofMul (Units.map (algebraMap K L).toMonoidHom a))
            (rationalBoundaryExponent chi (p 0) (p 1))) := by
      simp only [cochainCup]
      apply congrArg ((ρ_ M).hom)
      apply congrArg₂ (tensorElement M (𝟙_ (Rep ℤ Gal(L/K))))
      · exact hbase'
      · simpa only [initialProduct_zero, Representation.trivial_apply]
          using hbound'
    _ = _ := by
      rw [unitor_tensor_int]
      symm
      exact hout.trans (by rfl)

theorem character_cup_multiplicative
    (a : Kˣ) (chi : RationalCharacter Gal(L/K)) :
    characterCupInvariant K L a chi =
      (carryBrauerInvariant K
        (((CProduc.hRelativeBrauer K L
          (multiplicativeCupClass K L a chi) :
            relativeBrauerGroup K L) : BrauerGroup K))).toAdd := by
  unfold characterCupInvariant invariantH2
  rw [character_boundary_multiplicative]
  have hcomparison :
      (multiplicativeHCohomology
        (G := Gal(L/K)) (M := Lˣ)).symm
          (Multiplicative.ofAdd (multiplicative2Additive
            (multiplicativeCupClass K L a chi))) =
        multiplicativeCupClass K L a chi := by
    change (multiplicativeHCohomology
      (G := Gal(L/K)) (M := Lˣ)).symm
        ((multiplicativeHCohomology
          (G := Gal(L/K)) (M := Lˣ))
            (multiplicativeCupClass K L a chi)) = _
    exact (multiplicativeHCohomology
      (G := Gal(L/K)) (M := Lˣ)).symm_apply_apply _
  rw [hcomparison, invariant_torsion_coe]

end
end Towers.CField.RExist
