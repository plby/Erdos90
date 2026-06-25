import Mathlib.NumberTheory.NumberField.DedekindZeta
import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Towers.ClassField.Characters.DedekindResidueFormula

/-!
# Chapter VI, Section 2: ideal-class asymptotics and residues

Mathlib proves the lattice-counting asymptotic for every ordinary ideal
class, which is the modulus-one case underlying Proposition 2.8.  The sharper
ray-class estimate

`|S(x, k) - g_m x| ≤ C x^(1 - 1/d)`

and a ray-class partial-zeta function with its meromorphic continuation are
not yet packaged.  Consequently Corollaries 2.9 and 2.11 are represented by
their strongest existing ordinary-class and rational-Dirichlet analogues.
Corollary 2.12 is available exactly at the level of its residue formula and
real asymptotic at `1`.
-/

namespace Towers.CField.EProduc

open Filter Ideal NumberField NumberField.InfinitePlace NumberField.Units Topology
  nonZeroDivisors

noncomputable section

variable (K : Type*) [Field K] [NumberField K]

/-- The leading constant for integral ideals in one ordinary ideal class.
This is the modulus-one specialization of `g_m` in Proposition 2.8. -/
def ordinaryCountingConstant : ℝ :=
  (2 ^ nrRealPlaces K * (2 * Real.pi) ^ nrComplexPlaces K * regulator K) /
    (torsionOrder K * Real.sqrt |discr K|)

/-- Proposition 2.8, ordinary ideal-class specialization: the number of
integral ideals in a fixed class and of norm at most `x`, divided by `x`,
tends to the class-independent leading constant. -/
theorem ordinary_counting_asymptotic
    (C : ClassGroup (𝓞 K)) :
    Tendsto
      (fun x : ℝ ↦
        (Nat.card {I : (Ideal (𝓞 K))⁰ //
          absNorm (I : Ideal (𝓞 K)) ≤ x ∧ ClassGroup.mk0 I = C} : ℝ) / x)
      atTop (𝓝 (ordinaryCountingConstant K)) := by
  simpa [ordinaryCountingConstant] using
    Ideal.tendsto_norm_le_and_mk_eq_div_atTop K C

/-- The total ideal-counting asymptotic obtained by summing Proposition 2.8
over the ordinary class group. -/
theorem total_counting_asymptotic :
    Tendsto
      (fun x : ℝ ↦
        (Nat.card {I : Ideal (𝓞 K) // absNorm I ≤ x} : ℝ) / x)
      atTop (𝓝 (dedekindZeta_residue K)) := by
  simpa [dedekindZeta_residue, ordinaryCountingConstant] using
    Ideal.tendsto_norm_le_div_atTop K

/-- Lemma 2.10: the sum of a nontrivial complex character of a finite
abelian group is zero.  The codomain is `ℂˣ`, matching the text's
`ℂ×`. -/
theorem character_sum_zero {A : Type*}
    [CommGroup A] [Fintype A]
    (chi : A →* ℂˣ) (hchi : chi ≠ 1) :
    ∑ a, (chi a : ℂ) = 0 := by
  obtain ⟨b, hb⟩ : ∃ b, chi b ≠ 1 := by
    by_contra h
    apply hchi
    ext a
    simpa using not_exists.mp h a
  have hb' : (chi b : ℂ) ≠ 1 := by
    intro h
    apply hb
    ext
    exact h
  let S : ℂ := ∑ a, (chi a : ℂ)
  have hperm : ∑ a, (chi (a * b) : ℂ) = S := by
    simpa [S] using Equiv.sum_comp (Equiv.mulRight b) (fun a ↦ (chi a : ℂ))
  have hmul : S * (chi b : ℂ) = S := by
    calc
      S * (chi b : ℂ) = ∑ a, (chi a : ℂ) * (chi b : ℂ) := by
        simp only [S, Finset.sum_mul]
      _ = ∑ a, (chi (a * b) : ℂ) := by simp
      _ = S := hperm
  have hz : S * ((chi b : ℂ) - 1) = 0 := by
    calc
      S * ((chi b : ℂ) - 1) = S * (chi b : ℂ) - S := by ring
      _ = 0 := by rw [hmul, sub_self]
  exact (mul_eq_zero.mp hz).resolve_right (sub_ne_zero.mpr hb')

/-- Corollary 2.11, rational Dirichlet-character specialization: the
continued `L`-function of a nonprincipal character is differentiable on all
of `ℂ`. -/
theorem dirichlet_l_differentiable
    {N : ℕ} [NeZero N] {chi : DirichletCharacter ℂ N}
    (hchi : chi ≠ 1) :
    Differentiable ℂ (DirichletCharacter.LFunction chi) :=
  DirichletCharacter.differentiable_LFunction hchi

/-- Corollary 2.12: the explicit residue in the Dedekind class-number
formula. -/
theorem partial_zeta_dedekind :
    dedekindZeta_residue K =
      (2 ^ nrRealPlaces K * (2 * Real.pi) ^ nrComplexPlaces K *
          regulator K * classNumber K) /
        (torsionOrder K * Real.sqrt |discr K|) :=
  dedekindZeta_residue_def K

/-- Corollary 2.12, asymptotic formulation of the residue at `1`. -/
theorem dedekind_zeta_asymptotic :
    Tendsto (fun s : ℝ ↦ (s - 1) * dedekindZeta K s)
      (𝓝[>] 1) (𝓝 (dedekindZeta_residue K)) :=
  tendsto_sub_one_mul_dedekindZeta_nhdsGT K

/-- The residue in Corollary 2.12 is positive. -/
theorem partial_zeta_pos :
    0 < dedekindZeta_residue K :=
  dedekindZeta_residue_pos K

end

end Towers.CField.EProduc
