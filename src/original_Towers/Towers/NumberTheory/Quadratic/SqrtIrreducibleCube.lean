import Mathlib
import Towers.NumberTheory.Quadratic.SqrtNegFive

/-!
# Milne, Algebraic Number Theory, two-hour examination, Question 4

An irreducible algebraic integer need not be prime, so divisibility of a cube does not in
general imply divisibility of its base.  The familiar ring `Z[sqrt(-5)]` already supplies a
counterexample.  If the ideal class group is trivial, however, the ring of integers is a
principal ideal ring; irreducibles are then prime and the implication follows.
-/

namespace Towers.NumberTheory.Milne

open scoped NumberField nonZeroDivisors

namespace EFour

open Towers.NumberTheory.SNFive

/-- In `Z[sqrt(-5)]`, the irreducible element `2` divides `(1 + sqrt(-5))^3`. -/
theorem sqrt_five_cube :
    (2 : SNFive) ∣ (⟨1, 1⟩ : SNFive) ^ 3 := by
  refine ⟨(⟨-7, -1⟩ : SNFive), ?_⟩
  ext <;> norm_num [pow_succ]

/-- But `2` does not divide `1 + sqrt(-5)`. -/
theorem dvd_sqrt_five :
    ¬(2 : SNFive) ∣ (⟨1, 1⟩ : SNFive) := by
  rintro ⟨c, hc⟩
  have hre := congrArg Zsqrtd.re hc
  norm_num at hre
  omega

/-- Examination 4, negative part: irreducibility alone does not let divisibility descend
from a cube to its base. -/
theorem irredu_cube_count :
    Irreducible (2 : SNFive) ∧
      (2 : SNFive) ∣ (⟨1, 1⟩ : SNFive) ^ 3 ∧
      ¬(2 : SNFive) ∣ (⟨1, 1⟩ : SNFive) :=
  ⟨irreducible_two, sqrt_five_cube,
    dvd_sqrt_five⟩

/-- A Dedekind domain with trivial ideal class group is a principal ideal ring. -/
theorem principal_ring_subsingleton
    (R : Type*) [CommRing R] [IsDomain R] [IsDedekindDomain R]
    [Subsingleton (ClassGroup R)] :
    IsPrincipalIdealRing R := by
  constructor
  intro I
  by_cases hI : I = ⊥
  · rw [hI]
    exact bot_isPrincipal
  · apply (ClassGroup.mk0_eq_one_iff
      (mem_nonZeroDivisors_iff_ne_zero.mpr hI)).mp
    exact Subsingleton.elim _ 1

/-- Examination 4, positive part: triviality of the ideal class group is a sufficient
condition for an irreducible algebraic integer dividing a cube to divide its base. -/
theorem irredu_cube_subsi
    {K : Type*} [Field K] [NumberField K]
    [Subsingleton (ClassGroup (𝓞 K))]
    {alpha pi : 𝓞 K} (hpi : Irreducible pi) (hdiv : pi ∣ alpha ^ 3) :
    pi ∣ alpha := by
  letI : IsPrincipalIdealRing (𝓞 K) :=
    principal_ring_subsingleton (𝓞 K)
  exact (UniqueFactorizationMonoid.irreducible_iff_prime.mp hpi).dvd_of_dvd_pow hdiv

end EFour

end Towers.NumberTheory.Milne
