import Towers.ClassField.LocalBrauer.RelativeFrobeniusTransport

/-!
# The relative canonical unramified Frobenius coordinate
-/

namespace Towers.CField.LBrauer

noncomputable section

universe u

variable (K : Type u)
  [NontriviallyNormedField K] [IsUltrametricDist K] [ValuativeRel K]
  [IsNonarchimedeanLocalField K]
  [Valuation.Compatible (NormedField.valuation (K := K))]

private abbrev relativeLowerLevel (f : ℕ) :=
  canonicalUnramifiedLevel K f

private abbrev relativeUpperLevel (m f : ℕ) :=
  canonicalUnramifiedLevel K (m * f)

set_option maxHeartbeats 4000000 in
-- Constructing the relative equivalence unfolds both canonical tower levels.
set_option synthInstance.maxHeartbeats 500000 in
/-- The chosen identification of the relative level `U_{m f}/U_f` with the
canonical degree-`m` unramified extension of `U_f`. -/
noncomputable def canonicalUnramifiedRelative
    (m f : ℕ) [NeZero m] [NeZero f] :
    relativeUpperLevel K m f ≃ₐ[relativeLowerLevel K f]
      canonicalUnramifiedLevel (relativeLowerLevel K f) m :=
  Classical.choice
    (nonempty_level_relative K m f)

set_option maxHeartbeats 7000000 in
-- The coordinate transports the canonical Frobenius coordinate across a nested level.
set_option synthInstance.maxHeartbeats 500000 in
/-- The Frobenius-normalized cyclic coordinate on `Gal(U_{m f}/U_f)`. -/
noncomputable def frobeniusZMod
    (m f : ℕ) [NeZero m] [NeZero f] :
    Multiplicative (ZMod m) ≃*
      Gal(relativeUpperLevel K m f/relativeLowerLevel K f) := by
  let F := relativeLowerLevel K f
  exact (levelZMod F m).trans
    (canonicalUnramifiedRelative K m f).autCongr.symm

end

end Towers.CField.LBrauer
