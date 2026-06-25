import Towers.ClassField.CrossedProducts.BrauerRestriction
import Towers.ClassField.LocalBrauer.CyclicCarryRestriction
import Towers.ClassField.LocalBrauer.ConcreteInflationComparison

/-!
# Restriction of Galois carry cocycles

This file transports the elementary cyclic subgroup calculation to the
Galois-cohomology coordinates used in the local invariant construction.
-/

namespace Towers.CField.LBrauer

noncomputable section

universe u

open CProduca

attribute [local instance] Units.mulDistribMulActionRight

variable (K L E : Type u) [Field K] [Field L] [Field E]
  [Algebra K L] [Algebra K E] [Algebra L E] [IsScalarTower K L E]

/-- In compatible cyclic coordinates, Galois restriction carries the
ambient carry class to the carry class of the subgroup. -/
theorem restriction_carry_cocycle
    {m f : ℕ} [NeZero m] [NeZero f]
    (eK : Multiplicative (ZMod (m * f)) ≃* Gal(E/K))
    (eL : Multiplicative (ZMod m) ≃* Gal(E/L))
    (hcompat : ∀ z,
      galoisTowerInclusion K L E (eL z) =
        eK (CCarry.subgroupHom m f z))
    (a : Kˣ) :
    galoisHRestriction K L E
        (MHTwo.mk (galoisCarryCocycle K eK a)) =
      MHTwo.mk
        (galoisCarryCocycle L eL (Units.map (algebraMap K L) a)) := by
  letI : MulDistribMulAction (Multiplicative (ZMod (m * f))) Eˣ :=
    GroupH2.pulledAction eK
  letI : MulDistribMulAction (Multiplicative (ZMod m)) Eˣ :=
    GroupH2.pulledAction eL
  rw [galois_restriction_mk]
  apply congrArg MHTwo.mk
  apply NMCocycl₂.ext
  rintro ⟨g, h⟩
  rw [NMCocycl₂.restrict_apply]
  have hg : eK.symm (galoisTowerInclusion K L E g) =
      CCarry.subgroupHom m f (eL.symm g) := by
    apply eK.injective
    rw [eK.apply_symm_apply, ← hcompat, eL.apply_symm_apply]
  have hh : eK.symm (galoisTowerInclusion K L E h) =
      CCarry.subgroupHom m f (eL.symm h) := by
    apply eK.injective
    rw [eK.apply_symm_apply, ← hcompat, eL.apply_symm_apply]
  dsimp only [galoisCarryCocycle]
  rw [MHTrans.cocycleMap_apply,
    MHTrans.cocycleMap_apply]
  change (Units.map (algebraMap K E).toMonoidHom a) ^
      CCarry.carry
        (eK.symm (galoisTowerInclusion K L E g)).toAdd
        (eK.symm (galoisTowerInclusion K L E h)).toAdd =
    (Units.map (algebraMap L E).toMonoidHom
      (Units.map (algebraMap K L).toMonoidHom a)) ^
      CCarry.carry (eL.symm g).toAdd (eL.symm h).toAdd
  rw [hg, hh, CCarry.subgroup_hom_add,
    CCarry.subgroup_hom_add, CCarry.carry_add_hom]
  congr 1
  ext
  exact IsScalarTower.algebraMap_apply K L E a

/-- Equivalently, scalar extension of the relative Brauer class represented
by the ambient carry cocycle is represented by the subgroup carry cocycle. -/
theorem brauer_carry_cocycle
    [FiniteDimensional K E] [IsGalois K E]
    [FiniteDimensional L E] [IsGalois L E]
    {m f : ℕ} [NeZero m] [NeZero f]
    (eK : Multiplicative (ZMod (m * f)) ≃* Gal(E/K))
    (eL : Multiplicative (ZMod m) ≃* Gal(E/L))
    (hcompat : ∀ z,
      galoisTowerInclusion K L E (eL z) =
        eK (CCarry.subgroupHom m f z))
    (a : Kˣ) :
    brauerHRestriction K L E
        (MHTwo.mk (galoisCarryCocycle K eK a)) =
      MHTwo.mk
        (galoisCarryCocycle L eL (Units.map (algebraMap K L) a)) := by
  rw [← GaloisRestrictionCompatibility]
  exact restriction_carry_cocycle K L E eK eL hcompat a

/-- The same calculation stated directly in relative Brauer groups. -/
theorem brauer_change_carry
    [FiniteDimensional K E] [IsGalois K E]
    [FiniteDimensional L E] [IsGalois L E]
    {m f : ℕ} [NeZero m] [NeZero f]
    (eK : Multiplicative (ZMod (m * f)) ≃* Gal(E/K))
    (eL : Multiplicative (ZMod m) ≃* Gal(E/L))
    (hcompat : ∀ z,
      galoisTowerInclusion K L E (eL z) =
        eK (CCarry.subgroupHom m f z))
    (a : Kˣ) :
    relativeBrauerChange K L E
        (CProduc.relativeBrauerClass K E
          (galoisCarryCocycle K eK a)) =
      CProduc.relativeBrauerClass L E
        (galoisCarryCocycle L eL (Units.map (algebraMap K L) a)) := by
  change relativeBrauerChange K L E
      (CProduc.hRelativeBrauer K E
        (MHTwo.mk (galoisCarryCocycle K eK a))) =
    CProduc.hRelativeBrauer L E
      (MHTwo.mk
        (galoisCarryCocycle L eL (Units.map (algebraMap K L) a)))
  rw [← h_brauer_restriction,
    brauer_carry_cocycle K L E eK eL hcompat a]

end

end Towers.CField.LBrauer
