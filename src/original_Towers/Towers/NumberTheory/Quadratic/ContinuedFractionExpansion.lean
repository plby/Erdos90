import Mathlib.Algebra.ContinuedFractions.Computation.ApproximationCorollaries
import Mathlib.Algebra.ContinuedFractions.Computation.TerminatesIffRat
import Mathlib.Algebra.Ring.Periodic
import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Topology.MetricSpace.Pseudo.Real
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

/-!
# Milne, Algebraic Number Theory, continued-fraction expansions

The canonical regular continued fraction of a real number converges to that number, and the
expansion is infinite precisely for irrational inputs.  The algebraic direction of the later
characterization of quadratic irrationals by periodic expansions is proved in
`PeriodicContinuedFractions`.
-/

namespace Towers.NumberTheory.Milne

open Filter GenContFract Polynomial
open scoped Topology

/-- A sequence is eventually periodic if some tail has a positive period. -/
def EventuallyPeriodic {A : Type*} (f : ℕ → A) : Prop :=
  ∃ N p : ℕ, 0 < p ∧ Function.Periodic (fun n ↦ f (N + n)) p

theorem eventuallyPeriodic_iff {A : Type*} (f : ℕ → A) :
    EventuallyPeriodic f ↔
      ∃ N p : ℕ, 0 < p ∧ ∀ n : ℕ, f (N + (n + p)) = f (N + n) := by
  simp only [EventuallyPeriodic, Function.Periodic]

/-- The canonical continued fraction of `x` is eventually periodic when its sequence of
partial denominators is eventually periodic. -/
def ContinuedEventuallyPeriodic (x : ℝ) : Prop :=
  EventuallyPeriodic (fun n ↦ (GenContFract.of x).partDens.get? n)

/-- A real quadratic irrational is an algebraic real number of degree exactly two over `ℚ`. -/
def IQIrrati (x : ℝ) : Prop :=
  IsIntegral ℚ x ∧ (minpoly ℚ x).natDegree = 2

/-- The square root of a nonsquare natural number is a quadratic irrational. -/
theorem quadratic_irrational_cast {d : ℕ} (hd : ¬ IsSquare d) :
    IQIrrati (Real.sqrt d) := by
  let p : ℚ[X] := Polynomial.X ^ 2 - Polynomial.C (d : ℚ)
  have hpmonic : p.Monic := by
    dsimp [p]
    monicity
    norm_num
  have hpdeg : p.natDegree = 2 := by
    dsimp [p]
    compute_degree
    norm_num
  have hproot : Polynomial.aeval (Real.sqrt d) p = 0 := by
    dsimp [p]
    simp only [map_sub, map_pow, Polynomial.aeval_X, map_natCast]
    rw [Real.sq_sqrt (Nat.cast_nonneg d)]
    norm_num
  have hint : IsIntegral ℚ (Real.sqrt d) := ⟨p, hpmonic, hproot⟩
  refine ⟨hint, le_antisymm ?_ ?_⟩
  · have hdiv : minpoly ℚ (Real.sqrt d) ∣ p := minpoly.dvd ℚ _ hproot
    have hle := Polynomial.natDegree_le_of_dvd hdiv hpmonic.ne_zero
    simpa [hpdeg] using hle
  · rw [minpoly.two_le_natDegree_iff hint]
    simpa [Irrational] using (irrational_sqrt_natCast_iff.mpr hd)

/-- The convergents of the canonical continued fraction of a real number converge to it. -/
theorem real_continued_converges (x : ℝ) :
    Tendsto (GenContFract.of x).convs atTop (𝓝 x) :=
  GenContFract.of_convergence x

/-- An irrational real number has a nonterminating canonical continued fraction. -/
theorem irrational_continued_terminates (x : ℝ)
    (hx : ¬ ∃ q : ℚ, x = (q : ℝ)) :
    ¬(GenContFract.of x).Terminates := by
  exact fun h ↦ hx ((GenContFract.terminates_iff_rat x).mp h)

/-- A real number has an infinite canonical continued fraction exactly when it is irrational. -/
theorem continued_terminates_irrational (x : ℝ) :
    ¬(GenContFract.of x).Terminates ↔ ¬ ∃ q : ℚ, x = (q : ℝ) :=
  not_congr (GenContFract.terminates_iff_rat x)

/-- The canonical continued fraction of the square root of a nonsquare natural number does not
terminate. -/
theorem sqrt_continued_terminates {d : ℕ} (hd : ¬ IsSquare d) :
    ¬(GenContFract.of (Real.sqrt d)).Terminates := by
  apply irrational_continued_terminates
  intro hrat
  exact (irrational_sqrt_natCast_iff.mpr hd) ⟨hrat.choose, hrat.choose_spec.symm⟩

end Towers.NumberTheory.Milne
