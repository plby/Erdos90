import Submission.ClassField.ReciprocityExistence.BoundaryTransport
import Submission.ClassField.CohomologyOps.Naturality

/-!
# Transported cyclic cup product as a carry class

For an arbitrary cyclic model `Multiplicative (ZMod n) ≃* G`, cup product
with the transported character boundary is represented by the transported
carry cocycle.
-/

namespace Submission.CField.RExist

open CategoryTheory MonoidalCategory Rep
open scoped MonoidalCategory
open Submission.CField.COps.CPBuild
open Submission.CField.LRecip
open Submission.CField.LBrauer

noncomputable section

variable (n : ℕ) [NeZero n]
variable (G : Type) [Group G] [Fintype G]
variable (M : Type) [CommGroup M] [MulDistribMulAction G M]

private abbrev cyclicCoefficientRep := Rep.ofMulDistribMulAction G M

/-- A coefficient fixed by `G`, as a degree-zero class. -/
noncomputable def transportedCyclic0
    (pi : (cyclicCoefficientRep G M).ρ.invariants) :
    groupCohomology (cyclicCoefficientRep G M) 0 :=
  groupCohomology.π _ 0
    ((groupCohomology.cocyclesIso₀ (cyclicCoefficientRep G M)).inv pi)

/-- The carry cocycle, with group arguments read in the chosen standard
cyclic coordinates. -/
def transportedCarryCocycle
    (e : Multiplicative (ZMod n) ≃* G)
    (pi : (cyclicCoefficientRep G M).ρ.invariants) :
    groupCohomology.cocycles₂ (cyclicCoefficientRep G M) :=
  ⟨fun p ↦ (CCarry.carry (e.symm p.1).toAdd
      (e.symm p.2).toAdd : ℤ) • pi.1, by
    rw [groupCohomology.mem_cocycles₂_iff]
    intro g h j
    rw [show (cyclicCoefficientRep G M).ρ g
        ((CCarry.carry (e.symm h).toAdd
          (e.symm j).toAdd : ℤ) • pi.1) =
        (CCarry.carry (e.symm h).toAdd
          (e.symm j).toAdd : ℤ) • pi.1 by
      rw [map_zsmul, pi.2 g]]
    simp only [← add_zsmul]
    congr 1
    rw [e.symm.map_mul g h, e.symm.map_mul h j]
    simp only [toAdd_mul]
    exact_mod_cast CCarry.carry_cocycle
      (e.symm g).toAdd (e.symm h).toAdd (e.symm j).toAdd⟩

/-- Cup an invariant coefficient with the boundary of the transported
normalized cyclic character. -/
noncomputable def transportedCyclicBoundary
    (e : Multiplicative (ZMod n) ≃* G)
    (pi : (cyclicCoefficientRep G M).ρ.invariants) :
    groupCohomology.H2 (cyclicCoefficientRep G M) :=
  groupCohomology.map (MonoidHom.id G)
    (ρ_ (cyclicCoefficientRep G M)).hom 2
    (cupCohomology (cyclicCoefficientRep G M)
      (Rep.trivial ℤ G ℤ) 0 2
      (transportedCyclic0 G M pi)
      (characterBoundary G
        (transportedStandardCharacter n G e)))

/-- The transported literal cup-product cocycle is the transported carry
cocycle. -/
theorem transported_cup_carry
    (e : Multiplicative (ZMod n) ≃* G)
    (pi : (cyclicCoefficientRep G M).ρ.invariants) :
    transportedCyclicBoundary n G M e pi =
      groupCohomology.H2π (cyclicCoefficientRep G M)
        (transportedCarryCocycle n G M e pi) := by
  rw [transportedCyclicBoundary,
    character_boundary_transported]
  rw [transportedCyclic0]
  change groupCohomology.map (MonoidHom.id G)
      (ρ_ (cyclicCoefficientRep G M)).hom 2
      (cupCohomology (cyclicCoefficientRep G M)
        (Rep.trivial ℤ G ℤ) 0 2
        (groupCohomology.π (cyclicCoefficientRep G M) 0
          ((groupCohomology.cocyclesIso₀
            (cyclicCoefficientRep G M)).inv pi))
        (groupCohomology.π (Rep.trivial ℤ G ℤ) 2
          ((groupCohomology.isoCocycles₂
            (Rep.trivial ℤ G ℤ)).inv
              (transportedStandardCocycle n G e)))) =
      groupCohomology.π (cyclicCoefficientRep G M) 2
        ((groupCohomology.isoCocycles₂
          (cyclicCoefficientRep G M)).inv
            (transportedCarryCocycle n G M e pi))
  rw [cupCohomology_π]
  let c := cupCocycle (cyclicCoefficientRep G M)
    (Rep.trivial ℤ G ℤ) 0 2
      ((groupCohomology.cocyclesIso₀
        (cyclicCoefficientRep G M)).inv pi)
      ((groupCohomology.isoCocycles₂
        (Rep.trivial ℤ G ℤ)).inv
          (transportedStandardCocycle n G e))
  have hmap := congrArg (fun q ↦ q c)
    (groupCohomology.π_map (MonoidHom.id G)
      (ρ_ (cyclicCoefficientRep G M)).hom 2)
  simp only [ConcreteCategory.comp_apply] at hmap
  calc
    _ = groupCohomology.π (cyclicCoefficientRep G M) 2
        (groupCohomology.cocyclesMap (MonoidHom.id G)
          (ρ_ (cyclicCoefficientRep G M)).hom 2 c) := by
      exact hmap
    _ = _ := by
      apply congrArg (groupCohomology.π (cyclicCoefficientRep G M) 2)
      apply (ModuleCat.mono_iff_injective
        (groupCohomology.iCocycles (cyclicCoefficientRep G M) 2)).1
          inferInstance
      rw [i_cocycles_id]
      dsimp [c]
      funext p
      have hcup := congrFun (i_cup_cocycle
        (cyclicCoefficientRep G M) (Rep.trivial ℤ G ℤ) 0 2
        ((groupCohomology.cocyclesIso₀
          (cyclicCoefficientRep G M)).inv pi)
        ((groupCohomology.isoCocycles₂ (Rep.trivial ℤ G ℤ)).inv
          (transportedStandardCocycle n G e))) p
      change (ρ_ (cyclicCoefficientRep G M)).hom
          (groupCohomology.iCocycles
            ((cyclicCoefficientRep G M) ⊗ Rep.trivial ℤ G ℤ) (0 + 2)
            (cupCocycle (cyclicCoefficientRep G M)
              (Rep.trivial ℤ G ℤ) 0 2
              ((groupCohomology.cocyclesIso₀
                (cyclicCoefficientRep G M)).inv pi)
              ((groupCohomology.isoCocycles₂
                (Rep.trivial ℤ G ℤ)).inv
                  (transportedStandardCocycle n G e))) p) = _
      rw [hcup]
      have hout := congrFun
        (groupCohomology.isoCocycles₂_inv_comp_iCocycles_apply
          (cyclicCoefficientRep G M)
          (transportedCarryCocycle n G M e pi)) p
      have hpi := congrFun
        (groupCohomology.cocyclesIso₀_inv_comp_iCocycles_apply
          (cyclicCoefficientRep G M) pi) (fun i ↦ p (Fin.castAdd 2 i))
      have hcarry := congrFun
        (groupCohomology.isoCocycles₂_inv_comp_iCocycles_apply
          (Rep.trivial ℤ G ℤ)
          (transportedStandardCocycle n G e))
            (fun j ↦ p (Fin.natAdd 0 j))
      have hpi' :
          groupCohomology.iCocycles (cyclicCoefficientRep G M) 0
              ((groupCohomology.cocyclesIso₀
                (cyclicCoefficientRep G M)).inv pi)
              (fun i ↦ p (Fin.castAdd 2 i)) = pi.1 :=
        hpi.trans (by rfl)
      have hcarry' :
          groupCohomology.iCocycles (Rep.trivial ℤ G ℤ) 2
              ((groupCohomology.isoCocycles₂
                (Rep.trivial ℤ G ℤ)).inv
                  (transportedStandardCocycle n G e))
              (fun j ↦ p (Fin.natAdd 0 j)) =
            (CCarry.carry (e.symm (p 0)).toAdd
              (e.symm (p 1)).toAdd : ℤ) :=
        hcarry.trans (by rfl)
      calc
        _ = (ρ_ (cyclicCoefficientRep G M)).hom
              (tensorElement (cyclicCoefficientRep G M)
                (Rep.trivial ℤ G ℤ) pi.1
                (CCarry.carry (e.symm (p 0)).toAdd
                  (e.symm (p 1)).toAdd : ℤ)) := by
          simp only [cochainCup]
          apply congrArg ((ρ_ (cyclicCoefficientRep G M)).hom)
          apply congrArg₂ (tensorElement (cyclicCoefficientRep G M)
            (Rep.trivial ℤ G ℤ))
          · exact hpi'
          · simpa only [initialProduct_zero, Representation.trivial_apply]
              using hcarry'
        _ = (transportedCarryCocycle n G M e pi :
              G × G → M) (p 0, p 1) := by
          change (CCarry.carry (e.symm (p 0)).toAdd
              (e.symm (p 1)).toAdd : ℤ) • pi.1 =
            (CCarry.carry (e.symm (p 0)).toAdd
              (e.symm (p 1)).toAdd : ℤ) • pi.1
          rfl
        _ = (ConcreteCategory.hom
              ((groupCohomology.shortComplexH2
                (cyclicCoefficientRep G M)).moduleCatLeftHomologyData.i ≫
                (groupCohomology.cochainsIso₂
                  (cyclicCoefficientRep G M)).inv))
              (transportedCarryCocycle n G M e pi) p := by
          rfl
        _ = _ := hout.symm

end

end Submission.CField.RExist
