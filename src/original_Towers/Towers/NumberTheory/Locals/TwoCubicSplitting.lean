import Towers.NumberTheory.Locals.NewtonRootLifting
import Mathlib.Algebra.GCDMonoid.IntegrallyClosed
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Polynomial.Eval.Irreducible
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.Tactic.FinCases

/-!
# A cubic that splits completely over the 2-adic field

Milne, *Algebraic Number Theory*, Example 7.45 considers

`X^3 + X^2 + 2X - 8`.

The polynomial is irreducible over `ℚ`, but it has three roots over `ℚ_[2]`
of additive valuations `0`, `1`, and `2`.  We construct the roots directly by
Hensel lifting.  Besides the original polynomial, the substitutions `X = 2Y`
and `X = 4Z` lead to the integral equations

`2Y^3 + Y^2 + Y - 2 = 0` and `8Z^3 + 2Z^2 + Z - 1 = 0`.

Each of the three equations has a Hensel lift near `1`; multiplying the latter
two lifts by `2` and `4` gives roots in the required valuation strata.
-/

namespace Towers.NumberTheory.Milne

open Polynomial

noncomputable section

local instance twoPrimeFact_45 : Fact (Nat.Prime 2) := ⟨by decide⟩
local instance threePrimeFact_45 : Fact (Nat.Prime 3) := ⟨by decide⟩

/-- The cubic in Milne, Example 7.45. -/
def adicCubicSplitting (R : Type*) [Ring R] : R[X] :=
  X ^ 3 + X ^ 2 + 2 * X - 8

theorem cubic_splitting_monic (R : Type*) [Ring R] :
    (adicCubicSplitting R).Monic := by
  rw [show adicCubicSplitting R = X ^ 3 + (X ^ 2 + 2 * X - 8) by
    simp only [adicCubicSplitting]
    abel]
  apply monic_X_pow_add
  compute_degree
  all_goals norm_num

private theorem cubic_splitting_irreducible :
    Irreducible
      ((adicCubicSplitting ℤ).map (Int.castRingHom (ZMod 3))) := by
  let f : (ZMod 3)[X] := X ^ 3 + X ^ 2 + 2 * X - 8
  have hf : (adicCubicSplitting ℤ).map (Int.castRingHom (ZMod 3)) = f := by
    simp [adicCubicSplitting, f]
  rw [hf]
  apply irreducible_of_degree_le_three_of_not_isRoot
  · have hdegree : f.natDegree = 3 := by
      dsimp [f]
      compute_degree
      all_goals norm_num
    simp [hdegree]
  · intro x
    fin_cases x <;> norm_num [f, IsRoot.def] <;> decide

/-- The cubic in Example 7.45 is irreducible over `ℚ`. -/
theorem adic_splitting_irreducible :
    Irreducible (adicCubicSplitting ℚ) := by
  have hZ : Irreducible (adicCubicSplitting ℤ) := by
    apply Monic.irreducible_of_irreducible_map
      (Int.castRingHom (ZMod 3)) (adicCubicSplitting ℤ)
    · exact cubic_splitting_monic ℤ
    · exact cubic_splitting_irreducible
  have hmap :
      Irreducible ((adicCubicSplitting ℤ).map (algebraMap ℤ ℚ)) :=
    ((cubic_splitting_monic ℤ).irreducible_iff_irreducible_map_fraction_map
      (K := ℚ)).1 hZ
  simpa [adicCubicSplitting] using hmap

private def ScaledByTwo : ℤ[X] :=
  2 * X ^ 3 + X ^ 2 + X - 2

private def ScaledByFour : ℤ[X] :=
  8 * X ^ 3 + 2 * X ^ 2 + X - 1

private theorem padic_int_valuation
    {a : ℤ_[2]} (ha : ‖a‖ = 1) : a.valuation = 0 := by
  have hau : IsUnit a := PadicInt.isUnit_iff.mpr ha
  obtain ⟨b, hb⟩ := isUnit_iff_dvd_one.mp hau
  have hb0 : b ≠ 0 := by
    intro hbzero
    subst b
    simp at hb
  have hval := PadicInt.valuation_mul hau.ne_zero hb0
  rw [← hb, PadicInt.valuation_one] at hval
  omega

private theorem hensel_roots :
    ∃ u v w : ℤ_[2],
      (adicCubicSplitting ℤ).aeval u = 0 ∧
        ScaledByTwo.aeval v = 0 ∧
          ScaledByFour.aeval w = 0 ∧
            ‖u‖ = 1 ∧ ‖v‖ = 1 ∧ ‖w‖ = 1 := by
  let F : ℤ[X] := adicCubicSplitting ℤ
  let G : ℤ[X] := ScaledByTwo
  let H : ℤ[X] := ScaledByFour
  have hF1 : F.aeval (1 : ℤ_[2]) = (-4 : ℤ_[2]) := by
    norm_num [F, adicCubicSplitting, aeval_def]
  have hFd1 : F.derivative.aeval (1 : ℤ_[2]) = (7 : ℤ_[2]) := by
    norm_num [F, adicCubicSplitting, aeval_def]
  have hG1 : G.aeval (1 : ℤ_[2]) = (2 : ℤ_[2]) := by
    norm_num [G, ScaledByTwo, aeval_def]
  have hGd1 : G.derivative.aeval (1 : ℤ_[2]) = (9 : ℤ_[2]) := by
    norm_num [G, ScaledByTwo, aeval_def]
  have hH1 : H.aeval (1 : ℤ_[2]) = (10 : ℤ_[2]) := by
    norm_num [H, ScaledByFour, aeval_def]
  have hHd1 : H.derivative.aeval (1 : ℤ_[2]) = (29 : ℤ_[2]) := by
    norm_num [H, ScaledByFour, aeval_def]
  have hnormSeven : ‖(7 : ℤ_[2])‖ = 1 :=
    PadicInt.norm_natCast_eq_one_iff.mpr (by decide)
  have hnormNine : ‖(9 : ℤ_[2])‖ = 1 :=
    PadicInt.norm_natCast_eq_one_iff.mpr (by decide)
  have hnormTwentyNine : ‖(29 : ℤ_[2])‖ = 1 :=
    PadicInt.norm_natCast_eq_one_iff.mpr (by decide)
  have hnewtonF :
      ‖F.aeval (1 : ℤ_[2])‖ < ‖F.derivative.aeval (1 : ℤ_[2])‖ ^ 2 := by
    rw [hF1, hFd1, hnormSeven, one_pow]
    exact PadicInt.norm_intCast_lt_one_iff.mpr (by norm_num)
  have hnewtonG :
      ‖G.aeval (1 : ℤ_[2])‖ < ‖G.derivative.aeval (1 : ℤ_[2])‖ ^ 2 := by
    rw [hG1, hGd1, hnormNine, one_pow]
    exact PadicInt.norm_natCast_lt_one_iff.mpr (by decide)
  have hnewtonH :
      ‖H.aeval (1 : ℤ_[2])‖ < ‖H.derivative.aeval (1 : ℤ_[2])‖ ^ 2 := by
    rw [hH1, hHd1, hnormTwentyNine, one_pow]
    exact PadicInt.norm_natCast_lt_one_iff.mpr (by decide)
  obtain ⟨u, hu, hu1, -, -⟩ := padic_newton_root F 1 hnewtonF
  obtain ⟨v, hv, hv1, -, -⟩ := padic_newton_root G 1 hnewtonG
  obtain ⟨w, hw, hw1, -, -⟩ := padic_newton_root H 1 hnewtonH
  have unitNorm {a : ℤ_[2]} (ha : ‖a - 1‖ < 1) : ‖a‖ = 1 := by
    have h : ‖a + -(1 : ℤ_[2])‖ < ‖-(1 : ℤ_[2])‖ := by
      simpa [sub_eq_add_neg] using ha
    simpa using PadicInt.norm_eq_of_norm_add_lt_right h
  have hu1' : ‖u - 1‖ < 1 := by simpa [hFd1, hnormSeven] using hu1
  have hv1' : ‖v - 1‖ < 1 := by simpa [hGd1, hnormNine] using hv1
  have hw1' : ‖w - 1‖ < 1 := by simpa [hHd1, hnormTwentyNine] using hw1
  exact ⟨u, v, w, by simpa [F] using hu, by simpa [G] using hv,
    by simpa [H] using hw, unitNorm hu1', unitNorm hv1', unitNorm hw1'⟩

/-- Example 7.45: the cubic has three `2`-adic integral roots of additive
valuations `0`, `1`, and `2`. -/
theorem roots_valuations_two :
    ∃ α0 α1 α2 : ℤ_[2],
      (adicCubicSplitting ℤ).aeval α0 = 0 ∧
        (adicCubicSplitting ℤ).aeval α1 = 0 ∧
          (adicCubicSplitting ℤ).aeval α2 = 0 ∧
            α0.valuation = 0 ∧ α1.valuation = 1 ∧ α2.valuation = 2 := by
  obtain ⟨u, v, w, hu, hv, hw, hunorm, hvnorm, hwnorm⟩ := hensel_roots
  let α0 : ℤ_[2] := u
  let α1 : ℤ_[2] := 2 * v
  let α2 : ℤ_[2] := 4 * w
  have hvEq : 2 * v ^ 3 + v ^ 2 + v - 2 = 0 := by
    simpa [ScaledByTwo, aeval_def] using hv
  have hwEq : 8 * w ^ 3 + 2 * w ^ 2 + w - 1 = 0 := by
    simpa [ScaledByFour, aeval_def] using hw
  have hα1 : (adicCubicSplitting ℤ).aeval α1 = 0 := by
    simp [α1, adicCubicSplitting, aeval_def]
    linear_combination 4 * hvEq
  have hα2 : (adicCubicSplitting ℤ).aeval α2 = 0 := by
    simp [α2, adicCubicSplitting, aeval_def]
    linear_combination 8 * hwEq
  have huval : u.valuation = 0 :=
    padic_int_valuation hunorm
  have hvval : v.valuation = 0 :=
    padic_int_valuation hvnorm
  have hwval : w.valuation = 0 :=
    padic_int_valuation hwnorm
  have htwoVal : ((2 : ℤ_[2])).valuation = 1 := PadicInt.valuation_p
  have hfourVal : ((4 : ℤ_[2])).valuation = 2 := by
    rw [show (4 : ℤ_[2]) = 2 * 2 by norm_num,
      PadicInt.valuation_mul (by norm_num) (by norm_num), htwoVal]
  have hα1val : α1.valuation = 1 := by
    change (2 * v : ℤ_[2]).valuation = 1
    rw [PadicInt.valuation_mul (by norm_num)
      (PadicInt.isUnit_iff.mpr hvnorm).ne_zero, htwoVal, hvval]
  have hα2val : α2.valuation = 2 := by
    change (4 * w : ℤ_[2]).valuation = 2
    rw [PadicInt.valuation_mul (by norm_num)
      (PadicInt.isUnit_iff.mpr hwnorm).ne_zero, hfourVal, hwval]
  exact ⟨α0, α1, α2, by simpa [α0] using hu, hα1, hα2,
    by simpa [α0] using huval, hα1val, hα2val⟩

/-- The field-valued form of Example 7.45: there are three roots in `ℚ_[2]`
whose additive valuations are exactly `0`, `1`, and `2`. -/
theorem adic_roots_valuations :
    ∃ α0 α1 α2 : ℚ_[2],
      (adicCubicSplitting ℚ_[2]).IsRoot α0 ∧
        (adicCubicSplitting ℚ_[2]).IsRoot α1 ∧
          (adicCubicSplitting ℚ_[2]).IsRoot α2 ∧
            α0.valuation = 0 ∧ α1.valuation = 1 ∧ α2.valuation = 2 := by
  obtain ⟨α0, α1, α2, hα0, hα1, hα2, hα0val, hα1val, hα2val⟩ :=
    roots_valuations_two
  refine ⟨(α0 : ℚ_[2]), (α1 : ℚ_[2]), (α2 : ℚ_[2]), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [IsRoot.def]
    have h := congrArg (fun x : ℤ_[2] ↦ (x : ℚ_[2])) hα0
    simpa [adicCubicSplitting, aeval_def] using h
  · rw [IsRoot.def]
    have h := congrArg (fun x : ℤ_[2] ↦ (x : ℚ_[2])) hα1
    simpa [adicCubicSplitting, aeval_def] using h
  · rw [IsRoot.def]
    have h := congrArg (fun x : ℤ_[2] ↦ (x : ℚ_[2])) hα2
    simpa [adicCubicSplitting, aeval_def] using h
  · exact_mod_cast hα0val
  · exact_mod_cast hα1val
  · exact_mod_cast hα2val

/-- The cubic of Example 7.45 splits completely over the `2`-adic integers. -/
theorem splitting_splits_int :
    ((adicCubicSplitting ℤ).map (algebraMap ℤ ℤ_[2])).Splits := by
  classical
  obtain ⟨α0, α1, α2, hα0, hα1, hα2, hα0val, hα1val, hα2val⟩ :=
    roots_valuations_two
  let P : ℤ_[2][X] := (adicCubicSplitting ℤ).map (algebraMap ℤ ℤ_[2])
  have hPdegree : P.natDegree = 3 := by
    apply natDegree_eq_of_degree_eq_some
    simpa [P, adicCubicSplitting] using
      (degree_cubic (R := ℤ_[2]) (a := 1) (b := 1) (c := 2) (d := -8) one_ne_zero)
  have hPne : P ≠ 0 := by
    intro h
    have := congrArg (fun q : ℤ_[2][X] ↦ q.coeff 3) h
    norm_num [P, adicCubicSplitting, coeff_sub, coeff_add, coeff_mul, coeff_X] at this
  have hroot (a : ℤ_[2]) (ha : (adicCubicSplitting ℤ).aeval a = 0) :
      P.IsRoot a := by
    simpa [P, IsRoot.def, aeval_def, eval_map] using ha
  have hα0mem : α0 ∈ P.roots := (mem_roots hPne).2 (hroot α0 hα0)
  have hα1mem : α1 ∈ P.roots := (mem_roots hPne).2 (hroot α1 hα1)
  have hα2mem : α2 ∈ P.roots := (mem_roots hPne).2 (hroot α2 hα2)
  have hα01 : α0 ≠ α1 := by
    intro h
    subst α1
    omega
  have hα02 : α0 ≠ α2 := by
    intro h
    subst α2
    omega
  have hα12 : α1 ≠ α2 := by
    intro h
    subst α2
    omega
  have hsubset : ({α0, α1, α2} : Finset ℤ_[2]) ⊆ P.roots.toFinset := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    simp only [Multiset.mem_toFinset]
    rcases hx with rfl | rfl | rfl
    · exact hα0mem
    · exact hα1mem
    · exact hα2mem
  change P.Splits
  apply splits_iff_card_roots.mpr
  rw [hPdegree]
  apply le_antisymm
  · simpa [hPdegree] using P.card_roots'
  · calc
      3 = ({α0, α1, α2} : Finset ℤ_[2]).card := by simp [hα01, hα02, hα12]
      _ ≤ P.roots.toFinset.card := Finset.card_le_card hsubset
      _ ≤ P.roots.card := Multiset.toFinset_card_le _

/-- The cubic of Example 7.45 splits completely over `ℚ_[2]`. -/
theorem cubic_splitting_splits :
    ((adicCubicSplitting ℚ).map (algebraMap ℚ ℚ_[2])).Splits := by
  have h := splitting_splits_int
  simpa [adicCubicSplitting, Polynomial.map_map, ← IsScalarTower.algebraMap_eq] using
    h.map (algebraMap ℤ_[2] ℚ_[2])

end

end Towers.NumberTheory.Milne
