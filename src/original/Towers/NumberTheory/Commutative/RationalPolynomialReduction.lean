import Towers.NumberTheory.Commutative.RationalIntegralModel
import Towers.NumberTheory.Commutative.ScaleRootsFactorization
import Towers.NumberTheory.Galois.DedekindDegreePartition

/-!
# Reduction of a rational polynomial through an integral model

Suppose a monic integral polynomial `g` is obtained from a rational polynomial
by scaling all roots by a nonzero integer `d`.  Away from the primes dividing
`d`, the image of `d` in the residue field is a unit.  Scaling the roots of
the reduction of `g` by its inverse recovers the unscaled reduction and does
not change the multiset of irreducible-factor degrees.
-/

namespace Towers.NumberTheory.Milne

open IsDedekindDomain Polynomial UniqueFactorizationMonoid

noncomputable section

/-- The reduction associated to a root-scaled integral model, with the root
scaling undone in the residue field. -/
noncomputable def rationalModelReduction
    (d : nonZeroDivisors ℤ) (g : ℤ[X]) (v : HeightOneSpectrum ℤ) :
    (ℤ ⧸ v.asIdeal)[X] := by
  letI : v.asIdeal.IsMaximal := v.isMaximal
  letI : Field (ℤ ⧸ v.asIdeal) := Ideal.Quotient.field v.asIdeal
  exact (g.map (Ideal.Quotient.mk v.asIdeal)).scaleRoots
    ((Ideal.Quotient.mk v.asIdeal d : ℤ ⧸ v.asIdeal)⁻¹)

/-- The irreducible-factor degrees of the unscaled model reduction. -/
noncomputable def rationalModelDegrees
    (d : nonZeroDivisors ℤ) (g : ℤ[X]) (v : HeightOneSpectrum ℤ) :
    Multiset ℕ := by
  letI : v.asIdeal.IsMaximal := v.isMaximal
  letI : Field (ℤ ⧸ v.asIdeal) := Ideal.Quotient.field v.asIdeal
  classical
  exact (normalizedFactors (rationalModelReduction d g v)).map natDegree

/-- Away from the primes dividing the scaling denominator, undoing the root
scaling does not alter the degrees of the irreducible factors of the reduced
integral model. -/
theorem rational_model_degrees
    (d : nonZeroDivisors ℤ) (g : ℤ[X]) (hg : g.Monic)
    (v : HeightOneSpectrum ℤ) (hd : (d : ℤ) ∉ v.asIdeal) :
    rationalModelDegrees d g v =
      reductionFactorDegrees g v.asIdeal := by
  letI : v.asIdeal.IsMaximal := v.isMaximal
  letI : Field (ℤ ⧸ v.asIdeal) := Ideal.Quotient.field v.asIdeal
  classical
  let red : (ℤ ⧸ v.asIdeal)[X] := g.map (Ideal.Quotient.mk v.asIdeal)
  let dbar : ℤ ⧸ v.asIdeal := Ideal.Quotient.mk v.asIdeal d
  have hred : red ≠ 0 := (hg.map _).ne_zero
  have hdbar : dbar ≠ 0 := by
    change Ideal.Quotient.mk v.asIdeal (d : ℤ) ≠ 0
    intro hzero
    exact hd (Ideal.Quotient.eq_zero_iff_mem.mp hzero)
  have hinv : IsUnit dbar⁻¹ := isUnit_iff_ne_zero.mpr (inv_ne_zero hdbar)
  change (normalizedFactors (red.scaleRoots dbar⁻¹)).map natDegree =
    (normalizedFactors red).map natDegree
  exact degrees_scale_roots red hred hinv

end

end Towers.NumberTheory.Milne
