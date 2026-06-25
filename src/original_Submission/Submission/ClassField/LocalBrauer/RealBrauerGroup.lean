import Mathlib.Analysis.Complex.Polynomial.Basic
import Submission.ClassField.BrauerGroups.BrauerTrivialClass
import Submission.ClassField.BrauerGroups.CentralSimpleClosed
import Submission.ClassField.CrossedProducts.Cohomology
import Submission.ClassField.LocalBrauer.RealH2

/-!
# Chapter IV, Section 4: the Brauer group of the real numbers

Milne computes the real Brauer group from the two cohomology classes for
`Complex/Real`.  The nontrivial crossed product is Hamilton's quaternion
algebra.  Uniqueness of the division-algebra representative of a Brauer class
then shows that every central simple real algebra is a matrix algebra over
either `Real` or the Hamilton quaternions.
-/

namespace Submission.CField.LBrauer

noncomputable section

open BGroups
open CProduca
open scoped Quaternion

/-- Every real Brauer class is split by `Complex`. -/
theorem real_complex_top :
    relativeBrauerGroup ℝ ℂ = ⊤ := by
  apply le_antisymm le_top
  intro x _
  rw [relative_brauer_group]
  letI : Subsingleton (BrauerGroup.{0, 0} ℂ) :=
    brauer_subsingleton_closed ℂ
  exact Subsingleton.elim _ _

/-- Crossed products identify real multiplicative `H²` with the full real
Brauer group. -/
noncomputable def realHBrauer :
    MHTwo (Gal(ℂ/ℝ)) ℂˣ ≃* BrauerGroup.{0, 0} ℝ :=
  (CProduc.hRelativeBrauer ℝ ℂ).trans
    ((MulEquiv.subgroupCongr real_complex_top).trans
      Subgroup.topEquiv)

/-- The Brauer group of the real numbers is cyclic of order two. -/
noncomputable def realBrauerEquiv :
    BrauerGroup.{0, 0} ℝ ≃* Multiplicative (ZMod 2) :=
  realHBrauer.symm.trans realH2

/-- Milne's factor set determines the Brauer class of Hamilton's
quaternions. -/
theorem real_brauer_set :
    realHBrauer (MHTwo.mk realFactorSet) =
      brauerClass ℝ hamiltonCSA := by
  change ((CProduc.hRelativeBrauer ℝ ℂ
      (MHTwo.mk realFactorSet) :
        relativeBrauerGroup ℝ ℂ) : BrauerGroup ℝ) = _
  rw [CProduc.h_relative_brauer,
    CProduc.h_brauer_mk]
  change brauerClass ℝ (CProduc.centralSimpleCSA ℝ ℂ realFactorSet) =
    brauerClass ℝ hamiltonCSA
  rw [brauer_class]
  exact brauer_equivalent_alg ℝ _ _
    RCProduc.algEquivHamilton

/-- Hamilton's quaternion algebra is the nonzero element of the real Brauer
group. -/
@[simp]
theorem real_group_hamilton :
    realBrauerEquiv (brauerClass ℝ hamiltonCSA) =
      Multiplicative.ofAdd (1 : ZMod 2) := by
  rw [← real_brauer_set]
  simp [realBrauerEquiv]

/-- Hamilton's quaternion algebra does not represent the trivial real Brauer
class. -/
theorem hamilton_brauer_ne :
    brauerClass ℝ hamiltonCSA ≠ (1 : BrauerGroup ℝ) := by
  intro h
  have := congrArg realBrauerEquiv h
  simp at this

/-- Every real Brauer class is either the trivial class or Hamilton's
quaternion class. -/
theorem real_brauer_hamilton (x : BrauerGroup.{0, 0} ℝ) :
    x = 1 ∨ x = brauerClass ℝ hamiltonCSA := by
  let y := realHBrauer.symm x
  rcases real_or_set y with hy | hy
  · left
    calc
      x = realHBrauer y :=
        (realHBrauer.apply_symm_apply x).symm
      _ = 1 := by rw [hy]; exact map_one realHBrauer
  · right
    calc
      x = realHBrauer y :=
        (realHBrauer.apply_symm_apply x).symm
      _ = brauerClass ℝ hamiltonCSA := by
        rw [hy]
        exact real_brauer_set

/-- Every finite-dimensional central simple real algebra is a matrix algebra
over either `Real` or Hamilton's quaternions. -/
theorem simple_matrix_hamilton
    (A : Type) [Ring A] [Algebra ℝ A] [IsSimpleRing A]
    [Algebra.IsCentral ℝ A] [Module.Finite ℝ A] :
    (∃ n : ℕ, n ≠ 0 ∧
      Nonempty (A ≃ₐ[ℝ] Matrix (Fin n) (Fin n) ℝ)) ∨
    (∃ n : ℕ, n ≠ 0 ∧
      Nonempty (A ≃ₐ[ℝ] Matrix (Fin n) (Fin n) ℍ[ℝ])) := by
  obtain ⟨n, hn, D, hDdiv, hDalg, hDcentral, hDfin, ⟨eA⟩⟩ :=
    matrix_division_algebra ℝ A
  letI : NeZero n := hn
  letI : DivisionRing D := hDdiv
  letI : Algebra ℝ D := hDalg
  letI : Algebra.IsCentral ℝ D := hDcentral
  letI : Module.Finite ℝ D := hDfin
  have hAD : IsBrauerEquivalent
      (centralSimpleCSA ℝ A) (centralDivisionCSA ℝ D) := by
    refine ⟨1, n, one_ne_zero, NeZero.ne n, ?_⟩
    exact ⟨(matrixFinAlg ℝ A).trans eA⟩
  rcases real_brauer_hamilton
      (brauerClass ℝ (centralSimpleCSA ℝ A)) with hA | hA
  · left
    have hAbase : IsBrauerEquivalent
        (centralSimpleCSA ℝ A) (baseFieldCSA ℝ) := by
      rw [← brauer_class]
      exact hA
    have hDbase : IsBrauerEquivalent
        (centralDivisionCSA ℝ D) (centralDivisionCSA ℝ ℝ) := by
      simpa only [centralDivisionCSA, baseFieldCSA] using
        hAD.symm.trans hAbase
    obtain ⟨eD⟩ :=
      (division_brauer_equivalent ℝ D ℝ).1 hDbase
    exact ⟨n, NeZero.ne n, ⟨eA.trans eD.mapMatrix⟩⟩
  · right
    have hAH : IsBrauerEquivalent
        (centralSimpleCSA ℝ A) hamiltonCSA := by
      rw [← brauer_class]
      exact hA
    have hDH : IsBrauerEquivalent
        (centralDivisionCSA ℝ D) (centralDivisionCSA ℝ ℍ[ℝ]) := by
      simpa only [centralDivisionCSA, hamiltonCSA, centralSimpleCSA] using
        hAD.symm.trans hAH
    obtain ⟨eD⟩ :=
      (division_brauer_equivalent ℝ D ℍ[ℝ]).1 hDH
    exact ⟨n, NeZero.ne n, ⟨eA.trans eD.mapMatrix⟩⟩

end

end Submission.CField.LBrauer
