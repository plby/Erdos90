import Submission.Algebra.Magnus.MagnusHomogeneous
import Submission.Algebra.Magnus.UnitriangularMagnus
import Mathlib.RingTheory.Ideal.Maps

/-!
# Evaluation of truncated Magnus series

This file defines the finite-word-polynomial map into the quotient of the
Magnus ring by all terms of degree at least `n`.  Individual Magnus images
will be represented in this quotient by finite polynomials, without any
finiteness hypothesis on the alphabet.
-/

noncomputable section

namespace EChapma
namespace MSeries

open Submission
open Submission.TBluepr

variable {R X : Type*} [CommRing R]

/-- Finite word polynomials embedded coefficientwise in the Magnus ring. -/
def seriesRingHom
    [DecidableEq X] :
    MonoidAlgebra R (FreeMonoid X) →+* MSeries R X :=
  (GAWt.groupAlgebraMagnus
      (R := R) (X := X)).comp
    (freeAssociativeRealization R X).toRingHom

@[simp]
theorem series_ring_hom
    [DecidableEq X]
    (p : MonoidAlgebra R (FreeMonoid X)) :
    seriesRingHom (R := R) (X := X) p =
      wordPolynomialSeries p :=
  magnus_associative_realization p

/-- The Magnus ring truncated below degree `n`. -/
abbrev TruncatedMagnusRing
    (R X : Type*) [CommRing R] (n : ℕ) :=
  MSeries R X ⧸
    orderLeastIdeal (R := R) (X := X) n

/-- The finite-polynomial map into the degree-`< n` Magnus quotient. -/
def magnusRingHom
    [DecidableEq X]
    (n : ℕ) :
    MonoidAlgebra R (FreeMonoid X) →+*
      TruncatedMagnusRing R X n :=
  (Ideal.Quotient.mk
      (orderLeastIdeal (R := R) (X := X) n)).comp
    (seriesRingHom (R := R) (X := X))

end MSeries
end EChapma
