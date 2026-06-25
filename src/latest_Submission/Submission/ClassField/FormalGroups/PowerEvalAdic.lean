import Mathlib.RingTheory.PowerSeries.Evaluation
import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology

/-!
# Class Field Theory, Chapter I, Remark 2.2

In a complete adic ring, a power series can be evaluated at every element of
the defining ideal.  Its terms converge to zero, the coefficient-weighted
series sums to the library's power-series evaluation, and if the constant
coefficient lies in the ideal then so does the value.  Taking the ideal to be
the maximal ideal of a complete discrete valuation ring gives Milne's remark.
-/

namespace Submission.CField.FGroups

open Filter

variable {R : Type*} [CommRing R] [UniformSpace R] [IsUniformAddGroup R]
  [IsTopologicalRing R] [T2Space R] [CompleteSpace R]

omit [IsUniformAddGroup R] [IsTopologicalRing R] [T2Space R]
  [CompleteSpace R] in
/-- Every element of an ideal defining the topology is topologically
nilpotent, hence is a valid power-series evaluation point. -/
theorem power_series_adic {I : Ideal R} (hI : IsAdic I)
    {c : R} (hc : c ∈ I) : PowerSeries.HasEval c := by
  rw [PowerSeries.hasEval_def, IsTopologicallyNilpotent]
  refine hI.hasBasis_nhds_zero.tendsto_right_iff.mpr ?_
  intro m _
  filter_upwards [eventually_ge_atTop m] with n hn
  exact Ideal.pow_le_pow_right hn (Ideal.pow_mem_pow hc n)

omit [IsUniformAddGroup R] [IsTopologicalRing R] [T2Space R]
  [CompleteSpace R] in
/-- The terms `a_n c^n` in Remark 2.2 tend to zero. -/
theorem coeff_tendsto_adic
    {I : Ideal R} (hI : IsAdic I) (f : PowerSeries R)
    {c : R} (hc : c ∈ I) :
    Tendsto (fun n : Nat => PowerSeries.coeff n f * c ^ n)
      atTop (nhds 0) := by
  letI : IsLinearTopology R R :=
    IsLinearTopology.mk_of_hasBasis R hI.hasBasis_nhds_zero
  exact IsLinearTopology.tendsto_mul_zero_of_right _ _
    (power_series_adic hI hc)

/-- The coefficient-weighted series converges to power-series evaluation at
an element of the defining ideal. -/
theorem series_sum_adic
    {I : Ideal R} (hI : IsAdic I) (f : PowerSeries R)
    {c : R} (hc : c ∈ I) :
    HasSum (fun n : Nat => PowerSeries.coeff n f * c ^ n)
      (PowerSeries.eval₂ (RingHom.id R) c f) := by
  letI : IsLinearTopology R R :=
    IsLinearTopology.mk_of_hasBasis R hI.hasBasis_nhds_zero
  simpa using PowerSeries.hasSum_eval₂ continuous_id
    (power_series_adic hI hc) f

/-- If the constant coefficient belongs to the defining ideal, then the
value of the power series at an element of that ideal also belongs to it. -/
theorem constant_coeff_adic
    {I : Ideal R} (hI : IsAdic I) (f : PowerSeries R)
    {c : R} (hc : c ∈ I) (hconstant : PowerSeries.constantCoeff f ∈ I) :
    PowerSeries.eval₂ (RingHom.id R) c f ∈ I := by
  letI : IsLinearTopology R R :=
    IsLinearTopology.mk_of_hasBasis R hI.hasBasis_nhds_zero
  rw [PowerSeries.eval₂_eq_tsum continuous_id
    (power_series_adic hI hc)]
  apply tsum_mem
  · have hOpen : IsOpen (I : Set R) := by
      simpa using (isAdic_iff.mp hI).1 1
    exact I.toAddSubgroup.isClosed_of_isOpen hOpen
  · intro n
    cases n with
    | zero => simpa using hconstant
    | succ n =>
        apply I.mul_mem_left
        rw [pow_succ]
        exact I.mul_mem_left _ hc

end Submission.CField.FGroups
