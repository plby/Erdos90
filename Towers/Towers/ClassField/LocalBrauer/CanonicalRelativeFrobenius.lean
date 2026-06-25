import Towers.ClassField.LocalBrauer.RelativeFrobeniusGenerator
import Towers.ClassField.LocalBrauer.CanonicalFrobeniusInflation
import Towers.ClassField.CrossedProducts.GaloisRestriction
import Towers.ClassField.LocalBrauer.CyclicCarryRestriction

/-!
# Frobenius coordinates on a relative canonical unramified level

For `U_f ⊆ U_{m f}`, the relative arithmetic Frobenius is the `f`-th
power of arithmetic Frobenius over the original base.  It supplies the
cyclic coordinate compatible both with the ambient coordinate over the base
and with the canonical degree-`m` level over `U_f`.
-/

namespace Towers.CField.LBrauer

noncomputable section

universe u

open CProduca

variable (K : Type u)
  [NontriviallyNormedField K] [IsUltrametricDist K] [ValuativeRel K]
  [IsNonarchimedeanLocalField K]
  [Valuation.Compatible (NormedField.valuation (K := K))]

private abbrev relativeLowerLevel (f : ℕ) :=
  canonicalUnramifiedLevel K f

private abbrev relativeUpperLevel (m f : ℕ) :=
  canonicalUnramifiedLevel K (m * f)

set_option maxHeartbeats 3000000 in
-- Comparing relative and ambient Frobenius coordinates unfolds both canonical levels.
set_option synthInstance.maxHeartbeats 300000 in
-- The comparison synthesizes the transported relative Galois structures.
/-- The relative Frobenius coordinate is the subgroup coordinate inside the
ambient degree-`m f` Frobenius coordinate. -/
theorem frobenius_z_compatible
    (m f : ℕ) [NeZero m] [NeZero f]
    (z : Multiplicative (ZMod m)) :
    galoisTowerInclusion K (relativeLowerLevel K f)
        (relativeUpperLevel K m f)
        (frobeniusZMod K m f z) =
      levelZMod K (m * f)
        (CCarry.subgroupHom m f z) := by
  apply CCarry.subgroup_compatible_generator
    (incl := galoisTowerInclusion K (relativeLowerLevel K f)
      (relativeUpperLevel K m f))
    (eG := levelZMod K (m * f))
    (eH := frobeniusZMod K m f)
  change galoisTowerInclusion K (relativeLowerLevel K f)
      (relativeUpperLevel K m f)
      (frobeniusZMod K m f
        (Multiplicative.ofAdd (1 : ZMod m))) =
    levelZMod K (m * f)
      (CCarry.subgroupHom m f
        (Multiplicative.ofAdd (1 : ZMod m)))
  rw [relative_frobenius_z]
  have hincl :
      galoisTowerInclusion K (relativeLowerLevel K f)
          (relativeUpperLevel K m f)
          (relativeArithmeticFrobenius K m f) =
        (canonicalArithmeticFrobenius K (m * f)) ^ f := by
    apply AlgEquiv.ext
    intro x
    rfl
  rw [hincl]
  have hsub : CCarry.subgroupHom m f
      (Multiplicative.ofAdd (1 : ZMod m)) =
      (Multiplicative.ofAdd (1 : ZMod (m * f))) ^ f := by
    apply Multiplicative.toAdd.injective
    change CCarry.subgroupAddHom m f (1 : ZMod m) =
      ((Multiplicative.ofAdd (1 : ZMod (m * f))) ^ f).toAdd
    calc
      CCarry.subgroupAddHom m f (1 : ZMod m) =
          ((1 * f : ℕ) : ZMod (m * f)) :=
        by simpa using CCarry.subgroup_nat_cast m f 1
      _ = ((Multiplicative.ofAdd (1 : ZMod (m * f))) ^ f).toAdd := by
        simp
  rw [hsub, map_pow, level_frobenius_z]

end

end Towers.CField.LBrauer
