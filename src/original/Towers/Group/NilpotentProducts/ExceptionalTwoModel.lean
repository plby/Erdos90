import Towers.Group.NilpotentProducts.CyclicProducts
import Towers.Group.NilpotentProducts.ExceptionalTwoNilpotency
import Towers.Group.NilpotentProducts.GeneralModel

/-!
# The equation-(29) model of Struik's Theorem 4
-/

namespace Struik
namespace P1960

open Towers

/-- The integral equation-(29) generator in position `i`. -/
def exceptionalTwoModel {t : ℕ} (i : Fin t) :
    ELCoordi t :=
  generalExceptionalResidues (generalGenerator i)

/-- An arbitrary integral multiple of one equation-(29) generator
coordinate. -/
def generatorMultiple {t : ℕ} (i : Fin t) (n : ℤ) :
    ELCoordi t :=
  generalExceptionalResidues
    (generalGeneratorMultiple i n)

@[simp] theorem exceptional_residues_generator
    {t : ℕ} (i : Fin t) :
    toGeneralResidues (exceptionalTwoModel i) =
      generalGenerator i :=
  exceptional_general_residues _

@[simp] theorem exceptional_residues_multiple
    {t : ℕ} (i : Fin t) (n : ℤ) :
    toGeneralResidues (generatorMultiple i n) =
      generalGeneratorMultiple i n :=
  exceptional_general_residues _

theorem generator_pow {t : ℕ} (i : Fin t) (n : ℕ) :
    exceptionalTwoModel i ^ n = generatorMultiple i n := by
  apply (mulGeneralResidues t).injective
  rw [map_pow]
  change
    toGeneralResidues (exceptionalTwoModel i) ^ n =
      toGeneralResidues (generatorMultiple i n)
  rw [exceptional_residues_generator,
    generalGenerator_pow,
    exceptional_residues_multiple]

/-- The canonical generators of the equation-(29) residue group. -/
noncomputable def exceptionalModelGenerator
    {t : ℕ} (r : Fin t → ℕ)
    (hpos : ∀ i, 0 < r i) (hmono : Monotone r)
    (i : Fin t) : ExceptionalResiduesResidue r hpos hmono :=
  (exceptionalTwoModel i : ExceptionalResiduesResidue r hpos hmono)

private theorem generator_pow_rel
    {t : ℕ} (r : Fin t → ℕ) (i : Fin t) :
    ERMod r
      (exceptionalTwoModel i ^ singleModulus r i)
      (ELCoordi.zero t) := by
  rw [generator_pow]
  refine ⟨?_, fun _ => .refl _, fun _ => .refl _, fun _ => .refl _,
    fun _ => .refl _, fun _ => .refl _⟩
  intro j
  by_cases hji : j = i
  · subst j
    simp [generatorMultiple,
      generalExceptionalResidues,
      generalGeneratorMultiple,
      ELCoordi.zero, Int.ModEq]
  · simp [generatorMultiple,
      generalExceptionalResidues,
      generalGeneratorMultiple,
      ELCoordi.zero, hji]

theorem exceptional_model_residue
    {t : ℕ} (r : Fin t → ℕ)
    (hpos : ∀ i, 0 < r i) (hmono : Monotone r)
    (i : Fin t) :
    exceptionalModelGenerator r hpos hmono i ^
      singleModulus r i = 1 := by
  apply (exceptionalResiduesCon r hpos hmono).eq.mpr
  exact generator_pow_rel r i

/-- The free product of the cyclic groups of orders `2 ^ rᵢ` maps
canonically to the equation-(29) residue group. -/
noncomputable def cyclicExceptionalResidues
    {t : ℕ} (r : Fin t → ℕ)
    (hpos : ∀ i, 0 < r i) (hmono : Monotone r) :
    CyclicFreeProduct (singleModulus r) →*
      ExceptionalResiduesResidue r hpos hmono := by
  apply PresentedGroup.toGroup
  · intro rel hrel
    obtain ⟨i, rfl⟩ := hrel
    simpa using
      exceptional_model_residue r hpos hmono i

/-- The canonical equation-(29) map factors through the fourth
nilpotent product. -/
noncomputable def
    nilpotentExceptionalResidues
    {t : ℕ} (r : Fin t → ℕ)
    (hpos : ∀ i, 0 < r i) (hmono : Monotone r) :
    NilpotentCyclicProduct (singleModulus r) 4 →*
      ExceptionalResiduesResidue r hpos hmono := by
  let f := cyclicExceptionalResidues r hpos hmono
  apply QuotientGroup.lift
    (Subgroup.lowerCentralSeries
      (CyclicFreeProduct (singleModulus r)) 3) f
  intro x hx
  apply MonoidHom.mem_ker.mp
  have hxmap :
      f x ∈ Subgroup.lowerCentralSeries
        (ExceptionalResiduesResidue r hpos hmono) 3 :=
    Subgroup.lowerCentralSeries.map f 3 (Subgroup.mem_map_of_mem f hx)
  simpa [lower_exceptional_bot
    r hpos hmono] using hxmap

end P1960
end Struik
