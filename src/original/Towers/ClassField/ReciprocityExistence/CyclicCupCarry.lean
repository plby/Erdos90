import Towers.ClassField.ReciprocityExistence.CharacterBoundary
import Towers.ClassField.CohomologyOps.Naturality

/-!
# Cup product with the cyclic character boundary

For the standard cyclic group, cup product with the boundary of the
normalized injective character is represented by the ordinary carry
cocycle.  This is the cochain calculation behind the cyclic direction of
Lemma VII.8.5.
-/

namespace Towers.CField.RExist

open CategoryTheory MonoidalCategory Rep
open scoped MonoidalCategory
open Towers.CField.COps.CPBuild
open Towers.CField.LRecip
open Towers.CField.LBrauer

noncomputable section

variable (n : ℕ) [NeZero n]
variable (M : Type) [CommGroup M]
  [MulDistribMulAction (Multiplicative (ZMod n)) M]

private abbrev cyclicCoefficientRep :=
  Rep.ofMulDistribMulAction (Multiplicative (ZMod n)) M

/-- An invariant coefficient as a degree-zero cohomology class. -/
noncomputable def cyclicInvariant0
    (pi : (cyclicCoefficientRep n M).ρ.invariants) :
    groupCohomology (cyclicCoefficientRep n M) 0 :=
  groupCohomology.π _ 0
    ((groupCohomology.cocyclesIso₀ (cyclicCoefficientRep n M)).inv pi)

/-- The additive carry cocycle with invariant parameter `pi`. -/
def cyclicCarryCocycle
    (pi : (cyclicCoefficientRep n M).ρ.invariants) :
    groupCohomology.cocycles₂ (cyclicCoefficientRep n M) :=
  ⟨fun p ↦ (CCarry.carry p.1.toAdd p.2.toAdd : ℤ) • pi.1, by
    rw [groupCohomology.mem_cocycles₂_iff]
    intro g h j
    rw [show (cyclicCoefficientRep n M).ρ g
        ((CCarry.carry h.toAdd j.toAdd : ℤ) • pi.1) =
        (CCarry.carry h.toAdd j.toAdd : ℤ) • pi.1 by
      rw [map_zsmul, pi.2 g]]
    simp only [← add_zsmul]
    congr 1
    exact_mod_cast CCarry.carry_cocycle g.toAdd h.toAdd j.toAdd⟩

/-- Cup an invariant coefficient with the boundary of the normalized
standard cyclic character. -/
noncomputable def standardCupBoundary
    (pi : (cyclicCoefficientRep n M).ρ.invariants) :
    groupCohomology.H2 (cyclicCoefficientRep n M) :=
  groupCohomology.map (MonoidHom.id (Multiplicative (ZMod n)))
    (ρ_ (cyclicCoefficientRep n M)).hom 2
    (cupCohomology (cyclicCoefficientRep n M)
      (Rep.trivial ℤ (Multiplicative (ZMod n)) ℤ) 0 2
      (cyclicInvariant0 n M pi)
      (characterBoundary (Multiplicative (ZMod n))
        (standardCyclicCharacter n)))

/-- The literal cup-product cocycle is the cyclic carry cocycle. -/
theorem standard_boundary_carry
    (pi : (cyclicCoefficientRep n M).ρ.invariants) :
    standardCupBoundary n M pi =
      groupCohomology.H2π (cyclicCoefficientRep n M)
        (cyclicCarryCocycle n M pi) := by
  rw [standardCupBoundary,
    character_boundary_rational]
  rw [cyclicInvariant0]
  change groupCohomology.map
      (MonoidHom.id (Multiplicative (ZMod n)))
      (ρ_ (cyclicCoefficientRep n M)).hom 2
      (cupCohomology (cyclicCoefficientRep n M)
        (Rep.trivial ℤ (Multiplicative (ZMod n)) ℤ) 0 2
        (groupCohomology.π (cyclicCoefficientRep n M) 0
          ((groupCohomology.cocyclesIso₀
            (cyclicCoefficientRep n M)).inv pi))
        (groupCohomology.π
          (Rep.trivial ℤ (Multiplicative (ZMod n)) ℤ) 2
          ((groupCohomology.isoCocycles₂
            (Rep.trivial ℤ (Multiplicative (ZMod n)) ℤ)).inv
              (standardCarryCocycle n)))) =
      groupCohomology.π (cyclicCoefficientRep n M) 2
        ((groupCohomology.isoCocycles₂ (cyclicCoefficientRep n M)).inv
          (cyclicCarryCocycle n M pi))
  rw [cupCohomology_π]
  let c := cupCocycle (cyclicCoefficientRep n M)
    (Rep.trivial ℤ (Multiplicative (ZMod n)) ℤ) 0 2
      ((groupCohomology.cocyclesIso₀
        (cyclicCoefficientRep n M)).inv pi)
      ((groupCohomology.isoCocycles₂
        (Rep.trivial ℤ (Multiplicative (ZMod n)) ℤ)).inv
          (standardCarryCocycle n))
  have hmap := congrArg (fun q ↦ q c)
    (groupCohomology.π_map
      (MonoidHom.id (Multiplicative (ZMod n)))
      (ρ_ (cyclicCoefficientRep n M)).hom 2)
  simp only [ConcreteCategory.comp_apply] at hmap
  calc
    _ = groupCohomology.π (cyclicCoefficientRep n M) 2
        (groupCohomology.cocyclesMap
          (MonoidHom.id (Multiplicative (ZMod n)))
          (ρ_ (cyclicCoefficientRep n M)).hom 2 c) := by
      exact hmap
    _ = _ := by
      apply congrArg (groupCohomology.π (cyclicCoefficientRep n M) 2)
      apply (ModuleCat.mono_iff_injective
        (groupCohomology.iCocycles (cyclicCoefficientRep n M) 2)).1
          inferInstance
      rw [i_cocycles_id]
      dsimp [c]
      funext p
      have hcup := congrFun (i_cup_cocycle
        (cyclicCoefficientRep n M)
        (Rep.trivial ℤ (Multiplicative (ZMod n)) ℤ) 0 2
        ((groupCohomology.cocyclesIso₀
          (cyclicCoefficientRep n M)).inv pi)
        ((groupCohomology.isoCocycles₂
          (Rep.trivial ℤ (Multiplicative (ZMod n)) ℤ)).inv
            (standardCarryCocycle n))) p
      change (ρ_ (cyclicCoefficientRep n M)).hom
          (groupCohomology.iCocycles
            ((cyclicCoefficientRep n M) ⊗
              Rep.trivial ℤ (Multiplicative (ZMod n)) ℤ) (0 + 2)
            (cupCocycle (cyclicCoefficientRep n M)
              (Rep.trivial ℤ (Multiplicative (ZMod n)) ℤ) 0 2
              ((groupCohomology.cocyclesIso₀
                (cyclicCoefficientRep n M)).inv pi)
              ((groupCohomology.isoCocycles₂
                (Rep.trivial ℤ (Multiplicative (ZMod n)) ℤ)).inv
                  (standardCarryCocycle n))) p) = _
      rw [hcup]
      have hout := congrFun
        (groupCohomology.isoCocycles₂_inv_comp_iCocycles_apply
          (cyclicCoefficientRep n M) (cyclicCarryCocycle n M pi)) p
      have hpi := congrFun
        (groupCohomology.cocyclesIso₀_inv_comp_iCocycles_apply
          (cyclicCoefficientRep n M) pi) (fun i ↦ p (Fin.castAdd 2 i))
      have hcarry := congrFun
        (groupCohomology.isoCocycles₂_inv_comp_iCocycles_apply
          (Rep.trivial ℤ (Multiplicative (ZMod n)) ℤ)
          (standardCarryCocycle n)) (fun j ↦ p (Fin.natAdd 0 j))
      have hpi' :
          groupCohomology.iCocycles (cyclicCoefficientRep n M) 0
              ((groupCohomology.cocyclesIso₀
                (cyclicCoefficientRep n M)).inv pi)
              (fun i ↦ p (Fin.castAdd 2 i)) = pi.1 :=
        hpi.trans (by rfl)
      have hcarry' :
          groupCohomology.iCocycles
              (Rep.trivial ℤ (Multiplicative (ZMod n)) ℤ) 2
              ((groupCohomology.isoCocycles₂
                (Rep.trivial ℤ (Multiplicative (ZMod n)) ℤ)).inv
                  (standardCarryCocycle n))
              (fun j ↦ p (Fin.natAdd 0 j)) =
            (CCarry.carry (p 0).toAdd (p 1).toAdd : ℤ) :=
        hcarry.trans (by rfl)
      calc
        _ = (ρ_ (cyclicCoefficientRep n M)).hom
              (tensorElement (cyclicCoefficientRep n M)
                (Rep.trivial ℤ (Multiplicative (ZMod n)) ℤ) pi.1
                (CCarry.carry (p 0).toAdd (p 1).toAdd : ℤ)) := by
          simp only [cochainCup]
          apply congrArg ((ρ_ (cyclicCoefficientRep n M)).hom)
          apply congrArg₂ (tensorElement (cyclicCoefficientRep n M)
            (Rep.trivial ℤ (Multiplicative (ZMod n)) ℤ))
          · exact hpi'
          · simpa only [initialProduct_zero, Representation.trivial_apply]
              using hcarry'
        _ = (cyclicCarryCocycle n M pi :
              Multiplicative (ZMod n) × Multiplicative (ZMod n) → M)
              (p 0, p 1) := by
          change (CCarry.carry (p 0).toAdd (p 1).toAdd : ℤ) • pi.1 =
            (CCarry.carry (p 0).toAdd (p 1).toAdd : ℤ) • pi.1
          rfl
        _ = (ConcreteCategory.hom
              ((groupCohomology.shortComplexH2
                (cyclicCoefficientRep n M)).moduleCatLeftHomologyData.i ≫
                (groupCohomology.cochainsIso₂
                  (cyclicCoefficientRep n M)).inv))
              (cyclicCarryCocycle n M pi) p := by
          rfl
        _ = _ := hout.symm

end

end Towers.CField.RExist
