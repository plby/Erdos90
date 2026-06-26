import Towers.ClassField.LocalBrauer.RelativeFrobeniusCore

/-!
# Norm preservation for transported relative arithmetic Frobenius

This module contains the transported automorphism and the spectral-norm
comparison for the algebra equivalence between the two canonical relative
extensions.
-/

namespace Towers.CField.LBrauer

noncomputable section

universe u

open ValuativeRel

variable (K : Type u)
  [NontriviallyNormedField K] [IsUltrametricDist K] [ValuativeRel K]
  [IsNonarchimedeanLocalField K]
  [Valuation.Compatible (NormedField.valuation (K := K))]

private abbrev F (n : ℕ) := canonicalRelativeLevel K n
private abbrev E (m n : ℕ) := canonicalUpperLevel K m n
private abbrev C (m n : ℕ) [NeZero m] [NeZero n] :=
  relativeTargetLevel K m n

set_option maxHeartbeats 1000000 in
-- Conjugating between canonical levels compares two nested closure algebras.
set_option synthInstance.maxHeartbeats 500000 in
noncomputable def transportedArithmeticFrobenius
    (m n : ℕ) [NeZero m] [NeZero n]
    (e : E K m n ≃ₐ[F K n] C K m n) : Gal(C K m n/F K n) :=
  e.autCongr (relativeArithmeticFrobenius K m n)

set_option maxHeartbeats 1000000 in
-- Cache the application rule before downstream proofs unfold the nested conjugation.
set_option synthInstance.maxHeartbeats 500000 in
theorem transported_relative_frobenius
    (m n : ℕ) [NeZero m] [NeZero n]
    (e : E K m n ≃ₐ[F K n] C K m n) (y : C K m n) :
    transportedArithmeticFrobenius (K := K) m n e y =
      e (relativeArithmeticFrobenius K m n (e.symm y)) :=
  rfl

set_option maxHeartbeats 1000000 in
-- Both norms are the spectral norm over the common relative lower level.
set_option synthInstance.maxHeartbeats 500000 in
theorem canonical_relative_alg
    (m n : ℕ) [NeZero m] [NeZero n]
    (e : E K m n ≃ₐ[F K n] C K m n) (x : E K m n) :
    ‖e x‖ = ‖x‖ := by
  rw [NormedAlgebra.norm_eq_spectralNorm (F K n),
    NormedAlgebra.norm_eq_spectralNorm (F K n)]
  simp only [spectralNorm, minpoly.algEquiv_eq]

end

end Towers.CField.LBrauer
