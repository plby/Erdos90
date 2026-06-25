import Towers.NumberTheory.Completions.LocalDegreeBound
import Towers.NumberTheory.Completions.LocalTowerBound

/-!
# Uniform different bounds for factors of a completed product

The product decomposition bounds the degree of each completed field factor
by the global degree.  The unconditional Henselian-DVR estimate therefore
gives one exponent, depending only on that global degree and the completed
base, for the different in every factor.
-/

namespace Towers.NumberTheory.Milne

open scoped TensorProduct

noncomputable section

universe u

variable {K L C F ι : Type u}
  [Field K] [Field L] [Algebra K L]
  [Field F] [Algebra K F]
  [CommRing C] [IsDomain C] [IsDiscreteValuationRing C] [CharZero C]
  [HenselianLocalRing C]
  [Algebra C F] [IsFractionRing C F]
  [Finite ι]

variable (B E : ι → Type u)
  [∀ i, CommRing (B i)] [∀ i, IsDomain (B i)]
  [∀ i, IsDiscreteValuationRing (B i)] [∀ i, CharZero (B i)]
  [∀ i, HenselianLocalRing (B i)]
  [∀ i, Field (E i)]
  [∀ i, Algebra C (B i)] [∀ i, FaithfulSMul C (B i)]
  [∀ i, Module.Finite C (B i)] [∀ i, Module.IsTorsionFree C (B i)]
  [∀ i, Algebra.IsAlgebraic C (B i)]
  [∀ i, Algebra (B i) (E i)] [∀ i, IsFractionRing (B i) (E i)]
  [∀ i, Algebra F (E i)] [∀ i, Algebra C (E i)]
  [∀ i, IsScalarTower C (B i) (E i)]
  [∀ i, IsScalarTower C F (E i)]
  [∀ i, FiniteDimensional F (E i)]
  [∀ i, FiniteDimensional (IsLocalRing.ResidueField C)
    (IsLocalRing.ResidueField (B i))]
  [∀ i, Algebra.IsSeparable (IsLocalRing.ResidueField C)
    (IsLocalRing.ResidueField (B i))]

/-- The different in any factor of a completed product is bounded by the
standard exponent formed from the global degree. -/
theorem different_maximal_pi
    (e : F ⊗[K] L ≃ₐ[F] (∀ i, E i)) (N : ℕ)
    (hdegree : Module.finrank K L ≤ N) (i : ι) :
    differentIdeal C (B i) ∣
      IsLocalRing.maximalIdeal (B i) ^
        (N * (dvrCastValuation C N.factorial + 1)) := by
  have hfield : Module.finrank F (E i) ≤ N :=
    (finrank_tensor_pi E e i).trans hdegree
  have hring : Module.finrank C (B i) ≤ N :=
    finrank_fraction_fields N hfield
  exact
    different_henselian_dvr
      C (B i) N hring

end

end Towers.NumberTheory.Milne
