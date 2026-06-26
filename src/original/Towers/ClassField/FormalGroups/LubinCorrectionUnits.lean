import Towers.ClassField.FormalGroups.LubinTateIntertwiner
import Mathlib.RingTheory.LocalRing.Basic
import Mathlib.RingTheory.Ideal.Span

/-!
# Class Field Theory, Chapter I, Lemma 2.11: correction units

Milne's homogeneous correction divides by `(pi^r - 1) * pi`.  The first
factor is a unit because a positive power of the uniformizer is a nonunit in
the local coefficient ring.  Thus divisibility by the whole denominator is
equivalent to divisibility by `pi`.
-/

namespace Towers.CField.FGroups

variable {R : Type*} [CommRing R] [IsLocalRing R]

omit [IsLocalRing R] in
/-- A positive power of a nonunit remains a nonunit. -/
theorem not_unit_pow {pi : R} (hpi : ¬ IsUnit pi)
    {r : ℕ} (hr : r ≠ 0) : ¬ IsUnit (pi ^ r) := by
  simpa only [isUnit_pow_iff hr] using hpi

/-- In a local ring, `1 - pi^r` is a unit for every positive `r` when `pi`
is a nonunit. -/
theorem unit_sub_not {pi : R} (hpi : ¬ IsUnit pi)
    {r : ℕ} (hr : r ≠ 0) : IsUnit (1 - pi ^ r) := by
  apply IsLocalRing.isUnit_one_sub_self_of_mem_nonunits
  rw [mem_nonunits_iff]
  exact not_unit_pow hpi hr

/-- The sign-reversed correction factor `pi^r - 1` is also a unit. -/
theorem pow_sub_not {pi : R} (hpi : ¬ IsUnit pi)
    {r : ℕ} (hr : r ≠ 0) : IsUnit (pi ^ r - 1) := by
  have h := (unit_sub_not hpi hr).neg
  simpa only [neg_sub] using h

/-- Multiplying the uniformizer by Milne's unit correction factor does not
change its principal ideal. -/
theorem span_correction_uniformizer {pi : R} (hpi : ¬ IsUnit pi)
    {r : ℕ} (hr : r ≠ 0) :
    Ideal.span ({(pi ^ r - 1) * pi} : Set R) = Ideal.span {pi} := by
  exact Ideal.span_singleton_mul_left_unit
    (pow_sub_not hpi hr) pi

omit [IsLocalRing R] in
/-- The denominator appearing in the degree-`r+1` correction factors as a
unit times `pi`. -/
theorem succ_sub_factor (pi : R) (r : ℕ) :
    pi ^ (r + 1) - pi = (pi ^ r - 1) * pi := by
  rw [pow_succ]
  ring

/-- Over a local domain, the scalar multiplying the degree-`r+1`
homogeneous correction is nonzero for positive `r`. -/
theorem sub_self_ne [IsDomain R]
    {pi : R} (hpi0 : pi ≠ 0) (hpi : ¬ IsUnit pi)
    {r : ℕ} (hr : r ≠ 0) :
    pi ^ (r + 1) - pi ≠ 0 := by
  rw [succ_sub_factor]
  exact mul_ne_zero
    (IsUnit.ne_zero (pow_sub_not hpi hr)) hpi0

end Towers.CField.FGroups
