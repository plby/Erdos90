import Submission.ClassField.FormalGroups.LubinTateExamples
import Mathlib.NumberTheory.Cyclotomic.Gal

/-!
# Class Field Theory, Chapter I, Example 3.8

This file records the elementary algebra behind the cyclotomic realization of
the Lubin--Tate tower for `ℚ_p`.  For Milne's polynomial
`f(X) = (1 + X)^p - 1`, translating a root of unity by `-1` turns iteration of
`f` into ordinary powering.  It also does not change the generated field.
-/

namespace Submission.CField.LTate

open Polynomial
open scoped IntermediateField

noncomputable section

/-- Evaluation of the cyclotomic Lubin--Tate polynomial is ordinary powering
after translating the argument by one. -/
theorem lubin_tate_polynomial
    {R : Type*} [CommRing R] (p : ℕ) (x : R) :
    eval x
        ((FGroups.cyclotomicLubinTate p).map
          (Int.castRingHom R)) =
      (1 + x) ^ p - 1 := by
  simp [FGroups.cyclotomicLubinTate]

/-- Example 3.8: at `ζ - 1`, the cyclotomic Lubin--Tate polynomial has value
`ζ^p - 1`. -/
theorem lubin_tate_sub
    {R : Type*} [CommRing R] (p : ℕ) (ζ : R) :
    eval (ζ - 1)
        ((FGroups.cyclotomicLubinTate p).map
          (Int.castRingHom R)) =
      ζ ^ p - 1 := by
  rw [lubin_tate_polynomial]
  congr 2
  ring

/-- The `n`-fold compositional iterate at `ζ - 1` is `ζ^(p^n) - 1`,
the explicit polynomial identity used in Example 3.8. -/
theorem iterate_lubin_tate
    {R : Type*} [CommRing R] (p n : ℕ) (ζ : R) :
    eval (ζ - 1)
        ((((FGroups.cyclotomicLubinTate p).map
          (Int.castRingHom R)).comp)^[n] X) =
      ζ ^ (p ^ n) - 1 := by
  let f := (FGroups.cyclotomicLubinTate p).map
    (Int.castRingHom R)
  change eval (ζ - 1) (f.comp^[n] X) = ζ ^ (p ^ n) - 1
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply', Polynomial.eval_comp, ih]
      rw [show eval (ζ ^ (p ^ n) - 1) f =
          (ζ ^ (p ^ n)) ^ p - 1 by
        simpa only [f] using
          lubin_tate_sub p (ζ ^ (p ^ n))]
      rw [← pow_mul, pow_succ]

/-- Thus `ζ - 1` is a level-`n` Lubin--Tate root exactly when `ζ` is a
`p^n`-th root of unity. -/
theorem iterate_cyclotomic_lubin
    {R : Type*} [CommRing R] (p n : ℕ) (ζ : R) :
    eval (ζ - 1)
        ((((FGroups.cyclotomicLubinTate p).map
          (Int.castRingHom R)).comp)^[n] X) = 0 ↔
      ζ ^ (p ^ n) = 1 := by
  rw [iterate_lubin_tate]
  exact sub_eq_zero

/-- Compatible `p`-power roots of unity give compatible roots in Milne's
Lubin--Tate tower after subtracting one. -/
theorem cyclotomic_lubin_tate
    {R : Type*} [CommRing R] (p : ℕ) {ζ ξ : R} (hζ : ζ ^ p = ξ) :
    eval (ζ - 1)
        ((FGroups.cyclotomicLubinTate p).map
          (Int.castRingHom R)) =
      ξ - 1 := by
  rw [lubin_tate_sub, hζ]

/-- A `p^n`-th root of unity becomes a zero of the `p^n` multiplicative
endomorphism after subtracting one. -/
theorem multiplicative_endomorphism_sub
    {R : Type*} [CommRing R] {p n : ℕ} {ζ : R} (hζ : ζ ^ (p ^ n) = 1) :
    FGroups.multiplicativePowerEndomorphism (p ^ n) (ζ - 1) = 0 := by
  simp only [FGroups.multiplicativePowerEndomorphism]
  have htranslate : 1 + (ζ - 1) = ζ := by ring
  rw [htranslate, hζ, sub_self]

/-- Translating a field generator by one does not change the generated
intermediate field.  In Example 3.8 this identifies `K(ζ_{p^n} - 1)` with
`K(ζ_{p^n})`. -/
theorem adjoin_sub_one
    {K L : Type*} [Field K] [Field L] [Algebra K L] (ζ : L) :
    K⟮ζ - 1⟯ = K⟮ζ⟯ := by
  apply le_antisymm
  · rw [IntermediateField.adjoin_simple_le_iff]
    exact sub_mem (IntermediateField.mem_adjoin_simple_self K ζ) (one_mem _)
  · rw [IntermediateField.adjoin_simple_le_iff]
    have hζsub : ζ - 1 ∈ K⟮ζ - 1⟯ :=
      IntermediateField.mem_adjoin_simple_self K (ζ - 1)
    convert add_mem hζsub (one_mem _) using 1
    ring

/-- The standard cyclotomic Galois isomorphism acts on the translated
Lubin--Tate generator exactly as expected: the unit `t` sends `ζ - 1` to
`ζ ^ t - 1`.  This is the "standard one" assertion at the end of
Example 3.8. -/
theorem cyclotomic_aut_symm
    {n : ℕ} [NeZero n] {K L : Type*}
    [Field K] [Field L] [Algebra K L]
    [IsCyclotomicExtension {n} K L]
    (h : Irreducible (cyclotomic n K)) (t : (ZMod n)ˣ) :
    (IsCyclotomicExtension.autEquivPow L h).symm t
        (IsCyclotomicExtension.zeta n K L - 1) =
      IsCyclotomicExtension.zeta n K L ^ t.val.val - 1 := by
  rw [map_sub, map_one]
  have hspec := (IsCyclotomicExtension.zeta_spec n K L).autToPow_spec K
    ((IsCyclotomicExtension.autEquivPow L h).symm t)
  have ht := (IsCyclotomicExtension.autEquivPow L h).apply_symm_apply t
  rw [IsCyclotomicExtension.autEquivPow_apply] at ht
  rw [← hspec]
  congr 2
  exact congrArg (fun x : (ZMod n)ˣ ↦ x.val.val) ht

end

end Submission.CField.LTate
