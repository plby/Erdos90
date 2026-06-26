import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.NumberTheory.MulChar.Lemmas

/-!
# Chapter V, Section 2: Dirichlet characters and Euler products

Mathlib's `DirichletCharacter R m` is a multiplicative character of
`ZMod m`, extended by zero away from the units.  Thus it directly implements
the convention used in the text.
-/

namespace Towers.CField.Charac

open Filter Nat Topology
open scoped LSeries.notation

noncomputable section

/-- A value of a Dirichlet character on a unit modulo `m` is a root of
unity. -/
theorem dirichlet_roots_unity {m : ℕ} [NeZero m]
    (chi : DirichletCharacter ℂ m) (a : (ZMod m)ˣ) :
    MulChar.equivToUnitHom chi a ∈
      rootsOfUnity (Fintype.card (ZMod m)ˣ) ℂ :=
  chi.apply_mem_rootsOfUnity a

/-- The principal Dirichlet character is the unit element in the character
group. -/
abbrev principalCharacter (m : ℕ) : DirichletCharacter ℂ m := 1

/-- For `Re(s) > 1`, the analytically continued `L`-function agrees with its
defining Dirichlet series. -/
theorem l_function_dirichlet {m : ℕ} [NeZero m]
    (chi : DirichletCharacter ℂ m)
    {s : ℂ} (hs : 1 < s.re) :
    DirichletCharacter.LFunction chi s = LSeries (chi ·) s :=
  chi.LFunction_eq_LSeries hs

/-- The Euler product for a Dirichlet `L`-series, valid in its half-plane of
absolute convergence. -/
theorem dirichlet_l_euler {m : ℕ}
    (chi : DirichletCharacter ℂ m) {s : ℂ} (hs : 1 < s.re) :
    Tendsto
      (fun n : ℕ ↦ ∏ p ∈ primesBelow n,
        (1 - chi p * (p : ℂ) ^ (-s))⁻¹)
      atTop (𝓝 (L ↗chi s)) :=
  chi.LSeries_eulerProduct hs

/-- The Euler product for the Riemann zeta function. -/
theorem riemann_zeta_euler {s : ℂ} (hs : 1 < s.re) :
    Tendsto
      (fun n : ℕ ↦ ∏ p ∈ primesBelow n,
        (1 - (p : ℂ) ^ (-s))⁻¹)
      atTop (𝓝 (riemannZeta s)) :=
  riemannZeta_eulerProduct hs

end

end Towers.CField.Charac
