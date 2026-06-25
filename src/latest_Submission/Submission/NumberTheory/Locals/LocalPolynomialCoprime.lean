import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.Polynomial.Resultant.Basic


/-!
# Coprime polynomial lifts over a local ring

This is the monic-monic form of Milne's Lemma 7.34 used in Hensel
factorization: coprimality after reduction to the residue field implies strict
coprimality over the local ring.
-/

namespace Submission.NumberTheory.Milne

open Polynomial

section

variable {A : Type*} [CommRing A] [IsLocalRing A]

/-- Milne, Lemma 7.34 in the form needed for Theorem 7.33. -/
theorem coprime_monic_residue
    {f g : A[X]} (hf : f.Monic) (hg : g.Monic)
    (hcoprime : IsCoprime
      (f.map (IsLocalRing.residue A)) (g.map (IsLocalRing.residue A))) :
    IsCoprime f g := by
  rw [← isUnit_resultant_iff_isCoprime hf]
  rw [← IsLocalRing.notMem_maximalIdeal]
  intro hmem
  have hzero : IsLocalRing.residue A (resultant f g) = 0 := by
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hmem
  have hmap :
      resultant (f.map (IsLocalRing.residue A))
          (g.map (IsLocalRing.residue A)) =
        IsLocalRing.residue A (resultant f g) := by
    simp [hf.natDegree_map, hg.natDegree_map]
  have hunit : IsUnit
      (resultant (f.map (IsLocalRing.residue A))
        (g.map (IsLocalRing.residue A))) :=
    (isUnit_resultant_iff_isCoprime (hf.map _)).2 hcoprime
  exact (isUnit_iff_ne_zero.mp hunit) (hmap.trans hzero)

end

end Submission.NumberTheory.Milne
