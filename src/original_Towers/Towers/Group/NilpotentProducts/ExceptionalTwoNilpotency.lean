import Towers.Group.NilpotentProducts.GeneralNilpotency
import Towers.Group.NilpotentProducts.ExceptionalTwoEquivalence
import Towers.Group.NilpotentProducts.ExceptionalTwoResidues

/-!
# Nilpotency of the equation-(29) coordinate groups
-/

namespace Struik
namespace P1960

open Towers
open Towers.Edmonton

/-- The integral equation-(29) group has nilpotency class at most three. -/
theorem series_exceptional_bot (t : ℕ) :
    Subgroup.lowerCentralSeries (ELCoordi t) 3 = ⊥ := by
  let e := (mulGeneralResidues t).symm
  rw [← central_series_surjective
      e.toMonoidHom e.surjective 3,
    series_general_bot t,
    Subgroup.map_bot]

/-- The residue coordinate group in Theorem 4 has nilpotency class at
most three. -/
theorem lower_exceptional_bot
    {t : ℕ} (r : Fin t → ℕ)
    (hpos : ∀ i, 0 < r i) (hmono : Monotone r) :
    Subgroup.lowerCentralSeries (ExceptionalResiduesResidue r hpos hmono) 3 = ⊥ := by
  let q := (exceptionalResiduesCon r hpos hmono).mk'
  rw [← central_series_surjective q
      (exceptionalResiduesCon r hpos hmono).mk'_surjective 3,
    series_exceptional_bot t,
    Subgroup.map_bot]

end P1960
end Struik
