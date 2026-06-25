import Mathlib.Algebra.Module.Lattice
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Towers.ClassField.LocalBrauer.DivisionAlgebraIntegrality
import Towers.ClassField.LocalBrauer.DivisionResidueExtension

/-!
# Chapter IV, Section 4: the integer lattice of a division algebra

The closed unit ball `O_D` in a finite-dimensional division algebra is a
lattice over the integer ring `O_K` of the centre.  Consequently it is a
finite free `O_K`-module, of the same rank as `D` has over `K`.
-/

namespace Towers.CField.LBrauer

noncomputable section

open ValuativeRel

universe u

variable (K D : Type u) [NontriviallyNormedField K] [IsUltrametricDist K]
  [ValuativeRel K] [IsNonarchimedeanLocalField K] [DivisionRing D]
  [Valuation.Compatible (NormedField.valuation (K := K))]
  [Algebra K D] [Module.Finite K D]

/-- The scalar action of `O_K` on `D`, through the centre map. -/
@[implicit_reducible]
def baseIntegerDivision : Algebra 𝒪[K] D :=
  ((algebraMap K D).comp (valuation K).integer.subtype).toAlgebra'
    fun r x ↦ Algebra.commutes (r : K) x

local instance : Algebra 𝒪[K] D := baseIntegerDivision K D

local instance : IsScalarTower 𝒪[K] K D :=
  IsScalarTower.of_algebraMap_eq' rfl

local instance : Module.IsTorsionFree 𝒪[K] D :=
  Module.IsTorsionFree.comap Subtype.val
    (fun _ hr ↦ by simpa [isRegular_iff_ne_zero] using hr.ne_zero)
    (fun r x ↦ by
      rw [Algebra.smul_def, Algebra.smul_def]
      rfl)

local instance : IsFractionRing 𝒪[K] K :=
  (Valuation.integer.integers (valuation K)).isFractionRing

/-- The scalar action of `O_K` on `O_D`. -/
@[implicit_reducible]
def divisionIntegerAlgebra : Algebra 𝒪[K] (divisionIntegerSubring K D) :=
  (baseDivision K D).toAlgebra'
    fun r x ↦ by
      apply Subtype.ext
      exact Algebra.commutes (r : K) (x : D)

local instance : Algebra 𝒪[K] (divisionIntegerSubring K D) :=
  divisionIntegerAlgebra K D

/-- The integer ring `O_D`, regarded as an `O_K`-submodule of `D`. -/
def divisionIntegerSubmodule : Submodule 𝒪[K] D where
  carrier := divisionIntegerSubring K D
  zero_mem' := (divisionIntegerSubring K D).zero_mem
  add_mem' := (divisionIntegerSubring K D).add_mem
  smul_mem' := by
    intro r x hx
    change divisionAbsoluteValue K D (algebraMap K D (r : K) * x) ≤ 1
    rw [map_mul, division_absolute_value]
    have hr := (baseDivision K D r).property
    change divisionAbsoluteValue K D (algebraMap K D (r : K)) ≤ 1 at hr
    rw [division_absolute_value] at hr
    have hrnonneg : 0 ≤ ‖(r : K)‖ := norm_nonneg _
    have hxnonneg := (divisionAbsoluteValue K D |>.nonneg x)
    have hxle : divisionAbsoluteValue K D x ≤ 1 := hx
    nlinarith

@[simp]
theorem division_integer_submodule (x : D) :
    x ∈ divisionIntegerSubmodule K D ↔
      x ∈ divisionIntegerSubring K D :=
  Iff.rfl

/-- The subtype defined by the integer subring is linearly equivalent to the
subtype defined by the integer submodule. -/
def divisionIntegerLinear :
    divisionIntegerSubring K D ≃ₗ[𝒪[K]] divisionIntegerSubmodule K D where
  toFun x := ⟨x, x.property⟩
  invFun x := ⟨x, x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[implicit_reducible]
private def divisionAlgebraNorm : Norm D :=
  ⟨divisionAbsoluteValue K D⟩

private def divisionSpaceCore :
    @NormedSpace.Core K D _ _ _ (divisionAlgebraNorm K D) := by
  letI : Norm D := divisionAlgebraNorm K D
  refine
    { norm_nonneg := fun x ↦ (divisionAbsoluteValue K D).nonneg x
      norm_smul := fun c x ↦ by
        change divisionAbsoluteValue K D (c • x) =
          ‖c‖ * divisionAbsoluteValue K D x
        rw [Algebra.smul_def, map_mul,
          division_absolute_value]
      norm_triangle := fun x y ↦ (divisionAbsoluteValue K D).add_le x y
      norm_eq_zero_iff := fun x ↦ by
        change divisionAbsoluteValue K D x = 0 ↔ x = 0
        exact (divisionAbsoluteValue K D).eq_zero }

omit [IsNonarchimedeanLocalField K] in
private theorem base_integer_one {x : K} (hx : ‖x‖ ≤ 1) :
    x ∈ (valuation K).integer := by
  have hxnorm : NormedField.valuation x ≤ 1 := by
    change ‖x‖₊ ≤ 1
    exact_mod_cast hx
  exact (ValuativeRel.isEquiv (NormedField.valuation (K := K))
    (valuation K)).le_one_iff_le_one.mp hxnorm

/-- The integer submodule is finitely generated over `O_K`. -/
theorem division_submodule_fg :
    (divisionIntegerSubmodule K D).FG := by
  letI : Norm D := divisionAlgebraNorm K D
  let core := divisionSpaceCore K D
  letI : NormedAddCommGroup D := NormedAddCommGroup.ofCore core
  letI : NormedSpace K D := NormedSpace.ofCore core
  let ι := Module.Free.ChooseBasisIndex K D
  let b : Module.Basis ι K D := Module.Free.chooseBasis K D
  letI : Fintype ι := Fintype.ofFinite ι
  let e : D →L[K] (ι → K) := b.equivFunL.toContinuousLinearMap
  obtain ⟨c, hc⟩ := NormedField.exists_lt_norm K ‖e‖
  have hcpos : 0 < ‖c‖ := (lt_of_le_of_lt (norm_nonneg e) hc)
  have hc0 : c ≠ 0 := norm_pos_iff.mp hcpos
  let coord : divisionIntegerSubmodule K D → ι → K :=
    fun x i ↦ c⁻¹ * b.equivFun (x : D) i
  have hcoord_mem (x : divisionIntegerSubmodule K D) (i : ι) :
      coord x i ∈ (valuation K).integer := by
    apply base_integer_one K
    rw [show coord x i = c⁻¹ * b.equivFun (x : D) i from rfl,
      norm_mul, norm_inv]
    have hcoord : ‖b.equivFun (x : D) i‖ ≤ ‖c‖ := by
      calc
        ‖b.equivFun (x : D) i‖ ≤ ‖e (x : D)‖ := by
          exact norm_le_pi_norm _ i
        _ ≤ ‖e‖ * ‖(x : D)‖ := e.le_opNorm _
        _ ≤ ‖e‖ := by
          exact mul_le_of_le_one_right (norm_nonneg e) x.property
        _ ≤ ‖c‖ := hc.le
    rw [inv_mul_eq_div]
    exact (div_le_one hcpos).mpr hcoord
  let f : divisionIntegerSubmodule K D →ₗ[𝒪[K]] (ι → 𝒪[K]) :=
    { toFun := fun x i ↦ ⟨coord x i, hcoord_mem x i⟩
      map_add' := by
        intro x y
        ext i
        simp [coord, mul_add]
      map_smul' := by
        intro r x
        funext i
        apply Subtype.ext
        change coord (r • x) i = (r : K) * coord x i
        simp only [coord, Submodule.coe_smul, Algebra.smul_def]
        rw [show algebraMap 𝒪[K] D r = algebraMap K D (r : K) by rfl]
        rw [← Algebra.smul_def, map_smul]
        simp only [Pi.smul_apply, smul_eq_mul]
        ring }
  have hf : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    apply b.equivFun.injective
    funext i
    have hi := congrArg (fun z : ι → 𝒪[K] ↦ ((z i : 𝒪[K]) : K)) hxy
    change coord x i = coord y i at hi
    change c⁻¹ * b.equivFun (x : D) i =
      c⁻¹ * b.equivFun (y : D) i at hi
    exact mul_left_cancel₀ (inv_ne_zero hc0) hi
  have hfinite : Module.Finite 𝒪[K] (divisionIntegerSubmodule K D) :=
    Module.Finite.of_injective f hf
  rw [← Module.Finite.iff_fg]
  exact hfinite

/-- The integer submodule spans the division algebra over `K`. -/
theorem division_submodule_top :
    Submodule.span K (divisionIntegerSubmodule K D : Set D) = ⊤ := by
  letI : Norm D := divisionAlgebraNorm K D
  let core := divisionSpaceCore K D
  letI : NormedAddCommGroup D := NormedAddCommGroup.ofCore core
  letI : NormedSpace K D := NormedSpace.ofCore core
  rw [eq_top_iff]
  intro x
  obtain ⟨c, hcpos, hc⟩ :=
    NormedField.exists_norm_lt (K) (show 0 < 1 / (‖x‖ + 1) by positivity)
  have hc0 : c ≠ 0 := norm_pos_iff.mp hcpos
  let y : D := c • x
  have hy : y ∈ divisionIntegerSubmodule K D := by
    change divisionAbsoluteValue K D y ≤ 1
    change ‖y‖ ≤ 1
    rw [show y = c • x from rfl, norm_smul]
    have hxnonneg : 0 ≤ ‖x‖ := norm_nonneg x
    have hdenom : 0 < ‖x‖ + 1 := by positivity
    apply le_of_lt
    calc
      ‖c‖ * ‖x‖ ≤ (1 / (‖x‖ + 1)) * ‖x‖ :=
        mul_le_mul_of_nonneg_right hc.le hxnonneg
      _ < 1 := by
        rw [div_mul_eq_mul_div]
        exact (div_lt_one hdenom).mpr (by linarith)
  have hyspan : y ∈ Submodule.span K (divisionIntegerSubmodule K D : Set D) :=
    Submodule.subset_span hy
  have := (Submodule.span K (divisionIntegerSubmodule K D : Set D)).smul_mem c⁻¹ hyspan
  simpa [y, hc0] using this

/-- `O_D` is an `O_K`-lattice in `D`. -/
theorem division_submodule_lattice :
    Submodule.IsLattice K (divisionIntegerSubmodule K D) :=
  ⟨division_submodule_fg K D,
    division_submodule_top K D⟩

/-- The integer ring of a local division algebra is finite over the integer
ring of its centre. -/
theorem division_integer_module :
    Module.Finite 𝒪[K] (divisionIntegerSubring K D) := by
  letI : Submodule.IsLattice K (divisionIntegerSubmodule K D) :=
    division_submodule_lattice K D
  exact Module.Finite.equiv (divisionIntegerLinear K D).symm

/-- The integer ring of a local division algebra is free over the DVR of its
centre. -/
theorem division_integer_free :
    Module.Free 𝒪[K] (divisionIntegerSubring K D) := by
  letI : Submodule.IsLattice K (divisionIntegerSubmodule K D) :=
    division_submodule_lattice K D
  letI : Module.Finite 𝒪[K] (divisionIntegerSubmodule K D) := inferInstance
  letI : Module.Free 𝒪[K] (divisionIntegerSubmodule K D) :=
    Module.free_of_finite_type_torsion_free'
  exact Module.Free.of_equiv (divisionIntegerLinear K D).symm

/-- The `O_K`-rank of `O_D` equals the `K`-dimension of `D`. -/
theorem division_integer_finrank :
    letI : Module.Finite 𝒪[K] (divisionIntegerSubring K D) :=
      division_integer_module K D
    letI : Module.Free 𝒪[K] (divisionIntegerSubring K D) :=
      division_integer_free K D
    Module.finrank 𝒪[K] (divisionIntegerSubring K D) =
      Module.finrank K D := by
  letI : Submodule.IsLattice K (divisionIntegerSubmodule K D) :=
    division_submodule_lattice K D
  letI : Module.Finite 𝒪[K] (divisionIntegerSubring K D) :=
    division_integer_module K D
  letI : Module.Free 𝒪[K] (divisionIntegerSubring K D) :=
    division_integer_free K D
  letI : Module.Finite 𝒪[K] (divisionIntegerSubmodule K D) := inferInstance
  letI : Module.Free 𝒪[K] (divisionIntegerSubmodule K D) :=
    Module.free_of_finite_type_torsion_free'
  calc
    Module.finrank 𝒪[K] (divisionIntegerSubring K D) =
        Module.finrank 𝒪[K] (divisionIntegerSubmodule K D) :=
      LinearEquiv.finrank_eq (divisionIntegerLinear K D)
    _ = Module.finrank K D := Module.finrank_eq_of_rank_eq
      ((Submodule.IsLattice.rank' K (divisionIntegerSubmodule K D)).trans
        (Module.finrank_eq_rank K D).symm)

end

end Towers.CField.LBrauer
