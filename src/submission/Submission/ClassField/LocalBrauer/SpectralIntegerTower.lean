import Submission.NumberTheory.Locals.UnramifiedExtensions
import Submission.ClassField.LocalBrauer.SpectralIntegerClosure

/-!
# Spectral integer rings in a field tower

The spectral norm is unchanged when an element is viewed higher in a field
tower.  Consequently the field embedding restricts to the corresponding
spectral integer rings and their scalar tower.
-/

namespace Submission.CField.LBrauer

noncomputable section

universe u

open scoped NormedField Valued

variable (K F E : Type u)
  [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [NormedField F] [NormedField E]
  [IsUltrametricDist F] [IsUltrametricDist E]
  [NormedAlgebra K F] [NormedAlgebra K E]
  [Algebra F E]
  [Algebra.IsAlgebraic K F] [Algebra.IsAlgebraic K E]
  [IsScalarTower K F E]

private abbrev spectralInteger (L : Type u) [NormedField L]
    [IsUltrametricDist L] :=
  Valuation.integer (NormedField.valuation (K := L))

include K
set_option maxHeartbeats 2000000 in
-- Unfolding both spectral normed-algebra structures is expensive.
omit [IsUltrametricDist F] [IsUltrametricDist E] in
/-- The field embedding in a tower preserves the two spectral norms induced
by the common complete base field. -/
theorem algebra_spectral_tower (x : F) :
    ‖algebraMap F E x‖ = ‖x‖ := by
  rw [NormedAlgebra.norm_eq_spectralNorm K,
    ← spectralNorm.eq_of_tower (K := K) (L := E) x,
    ← NormedAlgebra.norm_eq_spectralNorm K]

set_option maxHeartbeats 2000000 in
-- Elaborating the restricted algebra map unfolds both spectral norms.
/-- The inclusion of a field in a larger field restricts to their spectral
integer rings when both norms are the spectral norm over the same complete
base field. -/
def spectralIntegerTower :
    spectralInteger F →+* spectralInteger E :=
  (algebraMap F E).restrict (spectralInteger F) (spectralInteger E) <| by
    intro x hx
    rw [Valuation.mem_integer_iff, NormedField.valuation_apply] at hx ⊢
    rw [← NNReal.coe_le_coe] at hx ⊢
    change ‖algebraMap F E x‖ ≤ 1
    change ‖x‖ ≤ 1 at hx
    rwa [algebra_spectral_tower (K := K) (F := F) (E := E)]

@[simp]
theorem spectral_tower_coe
    (x : spectralInteger F) :
    ((spectralIntegerTower (K := K) (F := F) (E := E) x :
        spectralInteger E) : E) =
      algebraMap F E x :=
  rfl

/-- The inclusion of spectral integer rings is continuous for their subtype
norm topologies. -/
theorem continuous_spectral_tower :
    Continuous
      (spectralIntegerTower (K := K) (F := F) (E := E)) := by
  have hisometry : Isometry (algebraMap F E) :=
    AddMonoidHomClass.isometry_of_norm (algebraMap F E)
      (algebra_spectral_tower (K := K) (F := F) (E := E))
  exact Continuous.subtype_mk
    (hisometry.continuous.comp continuous_subtype_val) _

/-- The spectral integer inclusion carries the source maximal ideal into the
target maximal ideal. -/
theorem spectral_tower_maximal
    (x : spectralInteger F)
    (hx : x ∈ IsLocalRing.maximalIdeal (spectralInteger F)) :
    spectralIntegerTower (K := K) (F := F) (E := E) x ∈
      IsLocalRing.maximalIdeal (spectralInteger E) := by
  change x ∈ IsLocalRing.maximalIdeal
    (Valuation.integer (NormedField.valuation (K := F))) at hx
  change spectralIntegerTower (K := K) (F := F) (E := E) x ∈
    IsLocalRing.maximalIdeal
      (Valuation.integer (NormedField.valuation (K := E)))
  have hx' : (NormedField.valuation (K := F)) (x : F) < 1 :=
    (NormedField.valuation (K := F)).mem_maximalIdeal_iff.mp hx
  apply (NormedField.valuation (K := E)).mem_maximalIdeal_iff.mpr
  rw [NormedField.valuation_apply] at hx' ⊢
  rw [← NNReal.coe_lt_coe] at hx' ⊢
  change ‖algebraMap F E (x : F)‖ < 1
  change ‖(x : F)‖ < 1 at hx'
  rwa [algebra_spectral_tower (K := K) (F := F) (E := E)]

/-- If the restricted tower map commutes with a chosen coefficient-ring
action, it is an algebra homomorphism over that coefficient ring. -/
def spectralTowerCommutes
    {R : Type*} [CommSemiring R]
    [Algebra R (spectralInteger F)] [Algebra R (spectralInteger E)]
    (hcomm :
      (spectralIntegerTower (K := K) (F := F) (E := E)).comp
          (algebraMap R (spectralInteger F)) =
        algebraMap R (spectralInteger E)) :
    spectralInteger F →ₐ[R] spectralInteger E :=
  { spectralIntegerTower (K := K) (F := F) (E := E) with
    commutes' := by
      intro x
      exact DFunLike.congr_fun hcomm x }

/-- The algebra structure on the larger spectral integer ring induced by the
field tower. -/
@[implicit_reducible]
def spectralTowerAlgebra :
    Algebra (spectralInteger F) (spectralInteger E) :=
  (spectralIntegerTower (K := K) (F := F) (E := E)).toAlgebra

/-- The inclusion of spectral integer rings is compatible with their
inclusions in the top field. -/
@[implicit_reducible]
def spectralTowerScalar :
    letI : Algebra (spectralInteger F) (spectralInteger E) :=
      spectralTowerAlgebra (K := K) (F := F) (E := E)
    IsScalarTower (spectralInteger F) (spectralInteger E) E :=
  letI : Algebra (spectralInteger F) (spectralInteger E) :=
    spectralTowerAlgebra (K := K) (F := F) (E := E)
  IsScalarTower.of_algebraMap_eq' rfl

end

end Submission.CField.LBrauer
