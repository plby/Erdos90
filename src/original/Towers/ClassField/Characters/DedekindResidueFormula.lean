import Mathlib.NumberTheory.NumberField.DedekindZeta

/-!
# Chapter V, Section 2, Theorem 2.4(a)

Mathlib proves the Dirichlet class-number formula in exactly the asymptotic
form used here: `(s - 1) * zeta_K(s)` tends to the explicit positive residue
as real `s` tends to `1` from above.

The general ray-class `L`-function and its nonvanishing in Theorem 2.4(b),
and consequently the prime-ideal density theorem 2.5, are not presently
available as packaged Mathlib APIs.
-/

namespace Towers.CField.Charac

open Filter NumberField NumberField.InfinitePlace NumberField.Units Topology

variable (K : Type*) [Field K] [NumberField K]

/-- The explicit residue in the analytic class-number formula. -/
theorem dedekind_zeta_formula :
    dedekindZeta_residue K =
      (2 ^ nrRealPlaces K * (2 * Real.pi) ^ nrComplexPlaces K *
          regulator K * classNumber K) /
        (torsionOrder K * Real.sqrt |discr K|) :=
  dedekindZeta_residue_def K

/-- Theorem 2.4(a): the Dedekind zeta function has the class-number-formula
residue at `1`. -/
theorem dedekindZeta_asymptotic :
    Tendsto (fun s : ℝ ↦ (s - 1) * dedekindZeta K s)
      (𝓝[>] 1) (𝓝 (dedekindZeta_residue K)) :=
  tendsto_sub_one_mul_dedekindZeta_nhdsGT K

/-- The residue in Theorem 2.4(a) is positive. -/
theorem dedekind_zeta_pos :
    0 < dedekindZeta_residue K :=
  dedekindZeta_residue_pos K

end Towers.CField.Charac
