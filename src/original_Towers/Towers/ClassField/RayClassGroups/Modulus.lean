import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
import Mathlib.RingTheory.DedekindDomain.Factorization

/-!
# Chapter V, Section 1: moduli

A modulus of a number field has a finitely supported nonnegative exponent at
each finite prime and a choice of real infinite primes, each occurring with
exponent one.  Complex infinite primes do not occur.  This file packages that
definition directly using Mathlib's height-one spectrum and infinite places.
-/

namespace Towers.CField.RCGroups

open IsDedekindDomain NumberField

noncomputable section

variable (K : Type*) [Field K]

/-- A real infinite prime of a number field. -/
abbrev RealInfinitePlace :=
  {w : InfinitePlace K // InfinitePlace.IsReal w}

/-- Definition V.1.3: a modulus of a number field. -/
structure Modulus where
  /-- Exponents of the finite prime ideals. -/
  finite : HeightOneSpectrum (𝓞 K) →₀ ℕ
  /-- The real infinite primes occurring in the modulus. -/
  infinite : Finset (RealInfinitePlace K)

namespace Modulus

/-- The trivial modulus. -/
protected def one : Modulus K where
  finite := 0
  infinite := ∅

instance : One (Modulus K) := ⟨Modulus.one K⟩

/-- Divisibility of moduli is componentwise on finite exponents and inclusion
on the real infinite part. -/
def Divides (m n : Modulus K) : Prop :=
  (∀ p, m.finite p ≤ n.finite p) ∧ m.infinite ⊆ n.infinite

instance : LE (Modulus K) := ⟨Divides K⟩

@[simp]
theorem le_def {m n : Modulus K} :
    m ≤ n ↔ (∀ p, m.finite p ≤ n.finite p) ∧ m.infinite ⊆ n.infinite :=
  Iff.rfl

instance : PartialOrder (Modulus K) where
  le := (· ≤ ·)
  le_refl m := ⟨fun _ => le_rfl, Finset.Subset.rfl⟩
  le_trans m n r hmn hnr :=
    ⟨fun p => (hmn.1 p).trans (hnr.1 p), hmn.2.trans hnr.2⟩
  le_antisymm m n hmn hnm := by
    cases m with
    | mk mf mi =>
      cases n with
      | mk nf ni =>
        congr
        · exact Finsupp.ext fun p => le_antisymm (hmn.1 p) (hnm.1 p)
        · exact Finset.Subset.antisymm hmn.2 hnm.2

@[simp]
theorem one_finite : (1 : Modulus K).finite = 0 := rfl

@[simp]
theorem one_infinite : (1 : Modulus K).infinite = ∅ := rfl

@[simp]
theorem one_le (m : Modulus K) : (1 : Modulus K) ≤ m := by
  constructor
  · intro p
    simp
  · simp

/-- The finite primes dividing a modulus. -/
def finiteSupport (m : Modulus K) : Finset (HeightOneSpectrum (𝓞 K)) :=
  m.finite.support

@[simp]
theorem finite_support_iff (m : Modulus K)
    (p : HeightOneSpectrum (𝓞 K)) :
    p ∈ m.finiteSupport ↔ m.finite p ≠ 0 := by
  simp [finiteSupport]

/-- The integral ideal represented by the finite part of a modulus. -/
def finiteIdeal (m : Modulus K) : Ideal (𝓞 K) :=
  m.finite.prod fun p e => p.asIdeal ^ e

@[simp]
theorem one_finiteIdeal : (1 : Modulus K).finiteIdeal = 1 := by
  simp [finiteIdeal]

/-- Positivity at every real prime occurring in the modulus. -/
def PositiveInfinity (m : Modulus K) (x : K) : Prop :=
  ∀ w ∈ m.infinite,
    0 < InfinitePlace.embedding_of_isReal w.property x

@[simp]
theorem one_positive_infinity (x : K) :
    PositiveInfinity (K := K) (1 : Modulus K) x := by
  simp [PositiveInfinity]

end Modulus

end

end Towers.CField.RCGroups
