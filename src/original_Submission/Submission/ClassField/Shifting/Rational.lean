import Submission.ClassField.Shifting.NormExactSequence

/-!
# Class Field Theory, Chapter II, Lemma 3.3(a): rational low Tate groups

For the trivial action on `ℚ`, the norm from coinvariants to invariants is
multiplication by the nonzero integer `|G|`, hence is bijective.  This proves
the degree `0` and degree `-1` cases of Milne's rational Tate-cohomology
vanishing without any uniform integer-indexed Tate-cohomology interface.
-/

namespace Submission.CField.Shifting

open Representation

noncomputable section

variable (G : Type) [Group G] [Fintype G]

private theorem coinvariants_trivial_rat :
    Function.Injective
      (normCoinvariantsInvariants (Rep.trivial ℤ G ℚ)) := by
  intro x y hxy
  induction x using Coinvariants.induction_on with
  | _ x =>
      induction y using Coinvariants.induction_on with
      | _ y =>
          have h := congrArg Subtype.val hxy
          change (Rep.trivial ℤ G ℚ).ρ.norm x =
            (Rep.trivial ℤ G ℚ).ρ.norm y at h
          have h : Fintype.card G • x = Fintype.card G • y := by
            simpa [Representation.norm] using h
          have hcard : (Fintype.card G : ℚ) ≠ 0 := by
            exact_mod_cast Fintype.card_ne_zero
          have hxy' : x = y := by
            apply (mul_left_cancel₀ hcard)
            simpa [nsmul_eq_mul] using h
          exact congrArg (Coinvariants.mk (Rep.trivial ℤ G ℚ).ρ) hxy'

private theorem coinvariants_invariants_rat :
    Function.Surjective
      (normCoinvariantsInvariants (Rep.trivial ℤ G ℚ)) := by
  intro y
  have hcard : (Fintype.card G : ℚ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  let x : ℚ := y.1 / Fintype.card G
  refine ⟨Coinvariants.mk (Rep.trivial ℤ G ℚ).ρ x, ?_⟩
  apply Subtype.ext
  change (Rep.trivial ℤ G ℚ).ρ.norm x = y.1
  calc
    (Rep.trivial ℤ G ℚ).ρ.norm x = Fintype.card G • x := by
      simp [Representation.norm]
    _ = y.1 := by
      simp only [nsmul_eq_mul]
      dsimp [x]
      field_simp

/-- **Lemma II.3.3(a), degree `-1`.** The degree-minus-one Tate group with
trivial rational coefficients is zero. -/
theorem subsingleton_trivial_rat :
    Subsingleton (tateCohomologyOne (Rep.trivial ℤ G ℚ)) := by
  constructor
  intro x y
  apply Subtype.ext
  apply coinvariants_trivial_rat G
  rw [LinearMap.mem_ker.mp x.property, LinearMap.mem_ker.mp y.property]

/-- **Lemma II.3.3(a), degree `0`.** The degree-zero Tate group with trivial
rational coefficients is zero. -/
theorem subsingleton_cohomology_rat :
    Subsingleton (tateCohomologyZero (Rep.trivial ℤ G ℚ)) := by
  apply Submodule.Quotient.subsingleton_iff.mpr
  exact LinearMap.range_eq_top.mpr
    (coinvariants_invariants_rat G)

end

end Submission.CField.Shifting
