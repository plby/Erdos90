import Mathlib.NumberTheory.Padics.HeightOneSpectrum
import Mathlib.Topology.Algebra.Group.Units
import Submission.ClassField.Ideles.Ideles

/-!
# Chapter V, Section 5, Example 5.9: the local factors over `Q`

Mathlib contains the local identifications used in Milne's description of the
rational ideles: height-one primes of `Z` are ordinary rational primes, their
completions are the fields `Q_p`, and the unique infinite completion is `R`.
This file packages those equivalences, including their induced equivalences
on unit groups.

The full topological isomorphism in Lemma 5.9 additionally normalizes an
arbitrary restricted-product element by a single nonzero rational number.
That requires a theorem assembling the finitely many nonzero local valuations
of an idele into one rational number, together with compatibility of that
normalization with the restricted-product topology.  This global assembly is
not currently packaged, so no axiom for the full isomorphism is introduced.
-/

noncomputable section

namespace Submission.CField.Recip

open IsDedekindDomain NumberField
open Submission.CField.Ideles

local instance (p : Nat.Primes) : Fact p.1.Prime := ⟨p.2⟩

/-- The finite places of `Q`, represented as height-one primes of `Z`, are in
canonical bijection with the ordinary prime natural numbers. -/
def rationalPlacesEquiv : HeightOneSpectrum ℤ ≃ Nat.Primes :=
  Rat.HeightOneSpectrum.primesEquiv

/-- The completion at the finite place corresponding to `p` is continuously
isomorphic, as a `Q`-algebra, to the field of `p`-adic numbers. -/
def rationalFiniteCompletion (p : Nat.Primes) :
    ((rationalPlacesEquiv.symm p).adicCompletion ℚ) ≃A[ℚ] ℚ_[p] :=
  (Padic.adicCompletionEquiv ℤ p).symm

/-- The preceding local-field equivalence induces an equivalence of
multiplicative groups. -/
def rationalCompletionUnits (p : Nat.Primes) :
    ((rationalPlacesEquiv.symm p).adicCompletion ℚ)ˣ ≃* ℚ_[p]ˣ :=
  Units.mapEquiv (rationalFiniteCompletion p).toMulEquiv

/-- The unique infinite completion of `Q` is the real field. -/
def rationalInfiniteCompletion :
    Rat.infinitePlace.Completion ≃+* ℝ :=
  InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace

/-- The real-completion equivalence induces an equivalence of multiplicative
groups. -/
def rationalInfiniteUnits :
    Rat.infinitePlace.Completionˣ ≃* ℝˣ :=
  Units.mapEquiv rationalInfiniteCompletion.toMulEquiv

/-- In particular, the ideles of `Q` in the Section 4 model have one infinite
factor and finite factors indexed by the ordinary prime numbers. -/
abbrev RationalIdeles := IdeleGroup ℤ ℚ

end Submission.CField.Recip
