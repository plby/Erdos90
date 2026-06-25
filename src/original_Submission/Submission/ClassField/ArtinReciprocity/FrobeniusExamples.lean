import Submission.NumberTheory.Galois.CyclotomicQuadraticFrobenius
import Submission.ClassField.LubinTate.CyclotomicResidueDegree
import Mathlib.NumberTheory.NumberField.Cyclotomic.Galois

/-!
# Chapter V, Examples 3.1 and 3.2

The global Artin homomorphism on fractional ideals has not yet been packaged
in the project.  The Frobenius computations which determine the two Artin
maps are available, however.  This file records them in the class-field-theory
namespace: quadratic Frobenius acts through the Legendre symbol, and
cyclotomic Frobenius corresponds to the residue class of the rational prime.
-/

namespace Submission.CField.ARecip

open NumberField
open Submission.NumberTheory.Milne

noncomputable section

/-- Example 3.1 on residue fields: Frobenius on a square root acts by the
Legendre-symbol sign. -/
theorem frobenius_apply_sqrt
    (p : ℕ) [Fact p.Prime] (hp : p ≠ 2)
    (L : Type*) [Field L] [Finite L] [Algebra (ZMod p) L]
    [Algebra.IsAlgebraic (ZMod p) L]
    (m : ℤ) (alpha : L)
    (halpha : alpha ^ 2 = algebraMap (ZMod p) L (m : ZMod p)) :
    FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod p) L alpha =
      algebraMap (ZMod p) L (legendreSym p m : ZMod p) * alpha := by
  have hchar : ringChar (ZMod p) ≠ 2 := by
    exact (ZMod.ringChar_zmod_n p).substr hp
  simpa only [legendreSym] using
    quadratic_frobenius_apply (ZMod p) L hchar (m : ZMod p) alpha halpha

/-- Example 3.1, fixed-point form: away from the ramified primes, Frobenius
fixes the square root exactly when the Legendre symbol is `1`. -/
theorem frobenius_fixed_iff
    (p : ℕ) [Fact p.Prime] (hp : p ≠ 2)
    (L : Type*) [Field L] [Finite L] [Algebra (ZMod p) L]
    [Algebra.IsAlgebraic (ZMod p) L]
    (m : ℤ) (hm : (m : ZMod p) ≠ 0) (alpha : L)
    (halpha : alpha ^ 2 = algebraMap (ZMod p) L (m : ZMod p))
    (halpha0 : alpha ≠ 0) :
    FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod p) L alpha = alpha ↔
      legendreSym p m = 1 := by
  have hchar : ringChar (ZMod p) ≠ 2 := by
    exact (ZMod.ringChar_zmod_n p).substr hp
  exact
    (quadratic_frobenius_square
      (ZMod p) L hchar (m : ZMod p) hm alpha halpha halpha0).trans
      (legendreSym.eq_one_iff (p := p) hm).symm

/-- Example 3.2, algebraic part: under the standard cyclotomic Galois
equivalence, the automorphism represented by `a` sends the chosen primitive
root to its `a`th power. -/
theorem automorphism_apply_zeta
    (n : ℕ) [NeZero n]
    (K : Type*) [Field K] [NumberField K]
    [IsCyclotomicExtension {n} ℚ K]
    (a : (ZMod n)ˣ) :
    (IsCyclotomicExtension.Rat.galEquivZMod n K).symm a
        (IsCyclotomicExtension.zeta n ℚ K) =
      IsCyclotomicExtension.zeta n ℚ K ^ a.val.val := by
  exact
    Submission.CField.LTate.cyclotomic_aut_zeta
      (K := ℚ) (L := K) (Polynomial.cyclotomic.irreducible_rat (NeZero.pos n)) a

/-- Example 3.2 at a rational prime: the arithmetic Frobenius action on a
primitive `n`th root is the `p`th-power action. -/
theorem frobenius_primitive_root
    (p n : ℕ) [Fact p.Prime] [NeZero n]
    (L : Type*) [Field L] [Finite L] [Algebra (ZMod p) L]
    [Algebra.IsAlgebraic (ZMod p) L]
    (hp : ¬p ∣ n) (ζ : L) (hζ : IsPrimitiveRoot ζ n) :
    FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod p) L ζ = ζ ^ p :=
  (cyclotomic_frobenius_apply p n L hp ζ hζ).1

/-- Example 3.2 in the global Galois group: if `P` lies over the rational
prime `p` and `p` is prime to `n`, then arithmetic Frobenius at `P`
corresponds to the unit class `[p]` modulo `n`. -/
theorem gal_z_frobenius
    (n p : ℕ) [NeZero n] [Fact p.Prime]
    (K : Type*) [Field K] [NumberField K]
    [IsCyclotomicExtension {n} ℚ K] [IsGalois ℚ K]
    (P : Ideal (NumberField.RingOfIntegers K)) [P.IsMaximal]
    [P.LiesOver (Ideal.span {(p : ℤ)})]
    (hnp : p.Coprime n) :
    IsCyclotomicExtension.Rat.galEquivZMod n K
        (arithFrobAt ℤ Gal(K/ℚ) P) =
      ZMod.unitOfCoprime p hnp := by
  let ζ : NumberField.RingOfIntegers K :=
    (IsCyclotomicExtension.zeta_spec n ℚ K).toInteger
  have hζ : IsPrimitiveRoot ζ n :=
    (IsCyclotomicExtension.zeta_spec n ℚ K).toInteger_isPrimitiveRoot
  have hnP : (n : NumberField.RingOfIntegers K) ∉ P := by
    intro hnP
    have hnspan : (n : ℤ) ∈ Ideal.span {(p : ℤ)} :=
      (Ideal.mem_of_liesOver (P := P) (p := Ideal.span {(p : ℤ)}) (n : ℤ)).2
        (by simpa using hnP)
    have hpdivInt : (p : ℤ) ∣ n := by
      simpa only [Ideal.mem_span_singleton] using hnspan
    have hpdiv : p ∣ n := by exact_mod_cast hpdivInt
    exact ((Fact.out : Nat.Prime p).coprime_iff_not_dvd.mp hnp) hpdiv
  have hcard : Nat.card (ℤ ⧸ P.under ℤ) = p := by
    rw [← Ideal.LiesOver.over (P := P) (p := Ideal.span {(p : ℤ)})]
    exact Int.card_ideal_quot p
  have hfrob : arithFrobAt ℤ Gal(K/ℚ) P • ζ = ζ ^ p := by
    simpa only [hcard] using
      arith_frob_root
        (R := ℤ) (G := Gal(K/ℚ)) P ζ hζ hnP
  have hgal :=
    IsCyclotomicExtension.Rat.galEquivZMod_smul_of_pow_eq n K
      (arithFrobAt ℤ Gal(K/ℚ) P) hζ.pow_eq_one
  have hpow :
      ζ ^ (IsCyclotomicExtension.Rat.galEquivZMod n K
        (arithFrobAt ℤ Gal(K/ℚ) P)).val.val = ζ ^ p := by
    rw [← hgal, hfrob]
  have hmod :
      (IsCyclotomicExtension.Rat.galEquivZMod n K
          (arithFrobAt ℤ Gal(K/ℚ) P)).val.val ≡ p [MOD n] := by
    simpa only [hζ.eq_orderOf] using
      (hζ.isOfFinOrder (NeZero.ne n)).pow_eq_pow_iff_modEq.mp hpow
  apply Units.ext
  change
    (IsCyclotomicExtension.Rat.galEquivZMod n K
        (arithFrobAt ℤ Gal(K/ℚ) P)).val = (p : ZMod n)
  simpa using
    (ZMod.natCast_eq_natCast_iff'
      (IsCyclotomicExtension.Rat.galEquivZMod n K
        (arithFrobAt ℤ Gal(K/ℚ) P)).val.val p n).2 hmod

end

end Submission.CField.ARecip
