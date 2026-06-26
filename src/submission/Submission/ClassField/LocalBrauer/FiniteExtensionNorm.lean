import Mathlib.Topology.Algebra.Monoid
import Submission.ClassField.LocalBrauer.FiniteExtensionOrder


/-!
# Norms on the integer rings of finite local extensions

For a finite Galois extension equipped with its canonical spectral topology,
the field norm preserves valuation integers.  Indeed, the norm is the product
of the Galois conjugates and every conjugate is an isometry for the spectral
norm.  This gives the concrete continuous homomorphism on integer-unit groups
used in the unramified norm argument.
-/

namespace Submission.CField.LBrauer

noncomputable section

universe u v

open ValuativeRel

namespace FLExt

variable (K : Type u) (L : Type v)
  [NontriviallyNormedField K] [IsUltrametricDist K]
  [ValuativeRel K] [IsNonarchimedeanLocalField K]
  [Valuation.Compatible (NormedField.valuation (K := K))]
  [Field L] [Algebra K L] [Module.Finite K L] [IsGalois K L]

omit [Valuation.Compatible (NormedField.valuation (K := K))]
  [IsGalois K L] in
/-- Every `K`-automorphism of a finite extension is an isometry for the
canonical spectral norm. -/
theorem isometry_algEquiv
    (σ : Gal(L/K)) :
    letI : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.of_finite K L
    letI : NontriviallyNormedField L := nontriviallyNormedField K L
    Isometry σ := by
  letI : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.of_finite K L
  letI : NontriviallyNormedField L := nontriviallyNormedField K L
  apply Isometry.of_dist_eq
  intro x y
  rw [dist_eq_norm, dist_eq_norm, ← map_sub]
  exact spectralNorm_eq_of_equiv σ (x - y) |>.symm

omit [Valuation.Compatible (NormedField.valuation (K := K))] in
/-- The field norm is continuous for the canonical spectral topology. -/
theorem continuous_fieldNorm :
    letI : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.of_finite K L
    letI : NontriviallyNormedField L := nontriviallyNormedField K L
    letI : NormedAlgebra K L := spectralNorm.normedAlgebra K L
    Continuous (Algebra.norm K : L → K) := by
  letI : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.of_finite K L
  letI : NontriviallyNormedField L := nontriviallyNormedField K L
  letI : NormedAlgebra K L := spectralNorm.normedAlgebra K L
  have hproduct : Continuous fun x : L ↦ ∏ σ : Gal(L/K), σ x :=
    continuous_finsetProd Finset.univ fun σ _ ↦
      (isometry_algEquiv K L σ).continuous
  have hcomposite : Continuous
      ((algebraMap K L) ∘ (Algebra.norm K : L → K)) := by
    apply hproduct.congr
    intro x
    exact (Algebra.norm_eq_prod_automorphisms K x).symm
  exact (algebraMap_isometry (𝕜 := K) (𝕜' := L)).comp_continuous_iff.mp
    hcomposite

private theorem field_norm_integers :
    letI : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.of_finite K L
    letI : NontriviallyNormedField L := nontriviallyNormedField K L
    letI : NormedAlgebra K L := spectralNorm.normedAlgebra K L
    letI : IsUltrametricDist L := IsUltrametricDist.of_normedAlgebra K
    letI : ValuativeRel L := valuativeRel K L
    ∀ x : 𝒪[L], Algebra.norm K (x : L) ∈ 𝒪[K] := by
  letI : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.of_finite K L
  letI : NontriviallyNormedField L := nontriviallyNormedField K L
  letI : NormedAlgebra K L := spectralNorm.normedAlgebra K L
  letI : IsUltrametricDist L := IsUltrametricDist.of_normedAlgebra K
  letI : ValuativeRel L := valuativeRel K L
  letI : Valuation.Compatible (NormedField.valuation (K := L)) :=
    Valuation.Compatible.ofValuation (NormedField.valuation (K := L))
  intro x
  rw [Valuation.mem_integer_iff]
  conv_rhs => rw [← map_one (ValuativeRel.valuation K)]
  rw [← Valuation.vle_iff_le (ValuativeRel.valuation K),
    Valuation.vle_iff_le (NormedField.valuation (K := K))]
  simp only [NormedField.valuation_apply, nnnorm_one]
  have hx : ‖(x : L)‖₊ ≤ 1 := by
    have hx' : (ValuativeRel.valuation L) (x : L) ≤ 1 := x.property
    conv_rhs at hx' => rw [← map_one (ValuativeRel.valuation L)]
    rw [← Valuation.vle_iff_le (ValuativeRel.valuation L),
      Valuation.vle_iff_le (NormedField.valuation (K := L))] at hx'
    simpa only [NormedField.valuation_apply, nnnorm_one] using hx'
  calc
    ‖Algebra.norm K (x : L)‖₊ =
        ‖algebraMap K L (Algebra.norm K (x : L))‖₊ := by
      apply NNReal.eq
      simp
    _ = ‖∏ σ : Gal(L/K), σ (x : L)‖₊ := by
      rw [Algebra.norm_eq_prod_automorphisms]
    _ = ∏ σ : Gal(L/K), ‖σ (x : L)‖₊ := by simp
    _ = ∏ _σ : Gal(L/K), ‖(x : L)‖₊ := by
      apply Finset.prod_congr rfl
      intro σ _
      apply NNReal.eq
      exact spectralNorm_eq_of_equiv σ (x : L) |>.symm
    _ ≤ 1 := Finset.prod_le_one (fun _ _ ↦ zero_le) fun _ _ ↦ hx

/-- The field norm restricted to the canonical valuation integer rings. -/
def integerNorm :
    letI : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.of_finite K L
    letI : NontriviallyNormedField L := nontriviallyNormedField K L
    letI : NormedAlgebra K L := spectralNorm.normedAlgebra K L
    letI : IsUltrametricDist L := IsUltrametricDist.of_normedAlgebra K
    letI : ValuativeRel L := valuativeRel K L
    𝒪[L] →* 𝒪[K] := by
  letI : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.of_finite K L
  letI : NontriviallyNormedField L := nontriviallyNormedField K L
  letI : NormedAlgebra K L := spectralNorm.normedAlgebra K L
  letI : IsUltrametricDist L := IsUltrametricDist.of_normedAlgebra K
  letI : ValuativeRel L := valuativeRel K L
  exact
    { toFun := fun x ↦ ⟨Algebra.norm K (x : L), field_norm_integers K L x⟩
      map_one' := by ext; simp
      map_mul' := by intro x y; ext; simp }

@[simp]
theorem integerNorm_coe :
    letI : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.of_finite K L
    letI : NontriviallyNormedField L := nontriviallyNormedField K L
    letI : NormedAlgebra K L := spectralNorm.normedAlgebra K L
    letI : IsUltrametricDist L := IsUltrametricDist.of_normedAlgebra K
    letI : ValuativeRel L := valuativeRel K L
    ∀ x : 𝒪[L],
      (((integerNorm K L x : 𝒪[K]) : K)) = Algebra.norm K (x : L) := by
  letI : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.of_finite K L
  letI : NontriviallyNormedField L := nontriviallyNormedField K L
  letI : NormedAlgebra K L := spectralNorm.normedAlgebra K L
  letI : IsUltrametricDist L := IsUltrametricDist.of_normedAlgebra K
  letI : ValuativeRel L := valuativeRel K L
  intro x
  rfl

/-- The restricted norm on valuation integers is continuous. -/
theorem continuous_integerNorm :
    letI : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.of_finite K L
    letI : NontriviallyNormedField L := nontriviallyNormedField K L
    letI : NormedAlgebra K L := spectralNorm.normedAlgebra K L
    letI : IsUltrametricDist L := IsUltrametricDist.of_normedAlgebra K
    letI : ValuativeRel L := valuativeRel K L
    Continuous (integerNorm K L) := by
  letI : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.of_finite K L
  letI : NontriviallyNormedField L := nontriviallyNormedField K L
  letI : NormedAlgebra K L := spectralNorm.normedAlgebra K L
  letI : IsUltrametricDist L := IsUltrametricDist.of_normedAlgebra K
  letI : ValuativeRel L := valuativeRel K L
  exact ((continuous_fieldNorm K L).comp continuous_subtype_val).subtype_mk _

/-- The concrete norm homomorphism on integer-unit groups. -/
def integerUnitNorm :
    letI : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.of_finite K L
    letI : NontriviallyNormedField L := nontriviallyNormedField K L
    letI : NormedAlgebra K L := spectralNorm.normedAlgebra K L
    letI : IsUltrametricDist L := IsUltrametricDist.of_normedAlgebra K
    letI : ValuativeRel L := valuativeRel K L
    𝒪[L]ˣ →* 𝒪[K]ˣ :=
  Units.map (integerNorm K L)

/-- The integer-unit norm is continuous. -/
theorem continuous_integer_norm :
    letI : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.of_finite K L
    letI : NontriviallyNormedField L := nontriviallyNormedField K L
    letI : NormedAlgebra K L := spectralNorm.normedAlgebra K L
    letI : IsUltrametricDist L := IsUltrametricDist.of_normedAlgebra K
    letI : ValuativeRel L := valuativeRel K L
    Continuous (integerUnitNorm K L) := by
  letI : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.of_finite K L
  letI : NontriviallyNormedField L := nontriviallyNormedField K L
  letI : NormedAlgebra K L := spectralNorm.normedAlgebra K L
  letI : IsUltrametricDist L := IsUltrametricDist.of_normedAlgebra K
  letI : ValuativeRel L := valuativeRel K L
  exact (continuous_integerNorm K L).units_map

/-- Coercing the integer-unit norm to the base field recovers the field
norm. -/
@[simp]
theorem integer_norm_coe :
    letI : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.of_finite K L
    letI : NontriviallyNormedField L := nontriviallyNormedField K L
    letI : NormedAlgebra K L := spectralNorm.normedAlgebra K L
    letI : IsUltrametricDist L := IsUltrametricDist.of_normedAlgebra K
    letI : ValuativeRel L := valuativeRel K L
    ∀ v : 𝒪[L]ˣ,
      ((((integerUnitNorm K L v : 𝒪[K]ˣ) : 𝒪[K]) : K)) =
        Algebra.norm K (((v : 𝒪[L]) : L)) := by
  letI : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.of_finite K L
  letI : NontriviallyNormedField L := nontriviallyNormedField K L
  letI : NormedAlgebra K L := spectralNorm.normedAlgebra K L
  letI : IsUltrametricDist L := IsUltrametricDist.of_normedAlgebra K
  letI : ValuativeRel L := valuativeRel K L
  intro v
  rfl

end FLExt

end

end Submission.CField.LBrauer
