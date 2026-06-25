import Submission.Group.Edmonton.CentralSeries
import Submission.Group.Presentation

/-!
# Nilpotent products of cyclic groups

This file defines the groups studied in Struik (1960).  An order value of
zero contributes the tautological relator `x⁰=1`, so it represents an
infinite cyclic factor.
-/

namespace Struik
namespace P1960

open Submission

universe u

variable {ι : Type u}

/-- The generator-order relators for a free product of cyclic groups. -/
def cyclicOrderRelators (order : ι → ℕ) : Set (FreeGroup ι) :=
  Set.range fun i => FreeGroup.of i ^ order i

/-- The free product of cyclic groups with the specified orders.  The value
`0` denotes an infinite cyclic factor. -/
abbrev CyclicFreeProduct (order : ι → ℕ) :=
  PresentedGroup (cyclicOrderRelators order)

/-- The canonical generator of a cyclic factor. -/
def cyclicGenerator (order : ι → ℕ) (i : ι) :
    CyclicFreeProduct order :=
  PresentedGroup.of i

/-- Each canonical generator satisfies its defining order relation. -/
theorem cyclic_generator_order
    (order : ι → ℕ) (i : ι) :
    cyclicGenerator order i ^ order i = 1 := by
  change
    (PresentedGroup.mk (cyclicOrderRelators order) (FreeGroup.of i)) ^
        order i =
      1
  rw [← map_pow]
  exact PresentedGroup.one_of_mem (Set.mem_range_self i)

/-- Struik's `F/Fₙ`: the free product of the cyclic factors, truncated by
the `n`th one-based lower-central term. -/
abbrev NilpotentCyclicProduct (order : ι → ℕ) (n : ℕ) :=
  CyclicFreeProduct order ⧸
    Subgroup.lowerCentralSeries (CyclicFreeProduct order) (n - 1)

/-- The image of a cyclic factor generator in `F/Fₙ`. -/
def nilpotentCyclicGenerator
    (order : ι → ℕ) (n : ℕ) (i : ι) :
    NilpotentCyclicProduct order n :=
  QuotientGroup.mk' (Subgroup.lowerCentralSeries (CyclicFreeProduct order) (n - 1))
    (cyclicGenerator order i)

/-- The defining order relation survives in every nilpotent product. -/
theorem nilpotent_cyclic_generator
    (order : ι → ℕ) (n : ℕ) (i : ι) :
    nilpotentCyclicGenerator order n i ^ order i = 1 := by
  change
    (QuotientGroup.mk'
      (Subgroup.lowerCentralSeries (CyclicFreeProduct order) (n - 1))
      (cyclicGenerator order i)) ^ order i =
      1
  rw [← map_pow, cyclic_generator_order]
  rfl

/-- The defining lower-central term of `F/Fₙ` is trivial. -/
theorem nilpotent_cyclic_bot
    (order : ι → ℕ) (n : ℕ) :
    Subgroup.lowerCentralSeries (NilpotentCyclicProduct order n) (n - 1) = ⊥ := by
  rw [Submission.Edmonton.lower_series_quotient,
    Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']

/-- In particular, Struik's `F/F₄` has trivial fourth one-based
lower-central term. -/
theorem nilpotent_four_bot
    (order : ι → ℕ) :
    Subgroup.lowerCentralSeries (NilpotentCyclicProduct order 4) 3 = ⊥ := by
  simpa using nilpotent_cyclic_bot order 4

end P1960
end Struik
