import Submission.ClassField.LocalBrauer.DivisionResidueField

/-!
# Chapter IV, Section 4: the residue extension of a local division algebra

The centre embeds the integer ring of the local field into the integer ring
of the division algebra.  Reduction modulo the strict-valuation ideals gives
the natural embedding of the base residue field into the residue field of the
division algebra.  This file packages that embedding, its algebra structure,
and Milne's residue degree.
-/

namespace Submission.CField.LBrauer

noncomputable section

open ValuativeRel

universe u

variable (K D : Type u) [NontriviallyNormedField K] [IsUltrametricDist K]
  [ValuativeRel K] [IsNonarchimedeanLocalField K] [DivisionRing D]
  [Valuation.Compatible (NormedField.valuation (K := K))]
  [Algebra K D] [Module.Finite K D]

/-- The centre map sends local-field integers to division-algebra integers. -/
def baseDivision : 𝒪[K] →+* divisionIntegerSubring K D where
  toFun x := ⟨algebraMap K D (x : K), by
    rw [division_subring,
      division_absolute_value]
    have hxval : valuation K (x : K) ≤ 1 := x.property
    have hxnorm : NormedField.valuation (x : K) ≤ 1 :=
      (ValuativeRel.isEquiv (NormedField.valuation (K := K))
        (valuation K)).le_one_iff_le_one.mpr hxval
    exact_mod_cast hxnorm⟩
  map_one' := by ext; simp
  map_mul' x y := by ext; simp
  map_zero' := by ext; simp
  map_add' x y := by ext; simp

@[simp]
theorem coe_integer_division (x : 𝒪[K]) :
    ((baseDivision K D x : divisionIntegerSubring K D) : D) =
      algebraMap K D (x : K) :=
  rfl

/-- Reduction of central integers in the residue ring of the division
algebra. -/
def baseDivisionResidue : 𝒪[K] →+* divisionResidueRing K D :=
  (divisionMaximalIdeal K D).ringCon.mk'.comp
    (baseDivision K D)

@[simp]
theorem base_division_residue (x : 𝒪[K]) :
    baseDivisionResidue K D x =
      (divisionMaximalIdeal K D).ringCon.mk'
        (baseDivision K D x) :=
  rfl

/-- A central integer in the maximal ideal of `𝒪[K]` reduces to zero in
the division residue ring. -/
theorem base_integer_division
    (x : 𝒪[K]) (hx : x ∈ IsLocalRing.maximalIdeal 𝒪[K]) :
    baseDivisionResidue K D x = 0 := by
  apply (RingCon.eq (c := (divisionMaximalIdeal K D).ringCon)).mpr
  rw [← (divisionMaximalIdeal K D).mem_iff]
  rw [division_maximal]
  rw [coe_integer_division,
    division_absolute_value]
  have hxnot : ¬ IsUnit x := by
    simpa only [IsLocalRing.mem_maximalIdeal] using hx
  have hxval : valuation K (x : K) < 1 :=
    (Valuation.Integer.not_isUnit_iff_valuation_lt_one
      (v := valuation K)).mp hxnot
  have hxnorm : NormedField.valuation (x : K) < 1 :=
    (ValuativeRel.isEquiv (NormedField.valuation (K := K))
      (valuation K)).lt_one_iff_lt_one.mpr hxval
  exact_mod_cast hxnorm

/-- Reduction of central integers is a local homomorphism. -/
private theorem base_division_hom :
    letI : Field (divisionResidueRing K D) := divisionResidueField K D
    IsLocalHom (baseDivisionResidue K D) := by
  letI : Field (divisionResidueRing K D) := divisionResidueField K D
  refine ⟨fun x hxunit ↦ ?_⟩
  by_contra hx
  have hxmem : x ∈ IsLocalRing.maximalIdeal 𝒪[K] := by
    simpa only [IsLocalRing.mem_maximalIdeal] using hx
  have hzero := base_integer_division K D x hxmem
  rw [hzero] at hxunit
  exact not_isUnit_zero hxunit

/-- The natural map from the residue field of `K` into the residue field of
`D`. -/
def baseResidueDivision : 𝓀[K] →+* divisionResidueRing K D := by
  letI : Field (divisionResidueRing K D) := divisionResidueField K D
  letI : IsLocalHom (baseDivisionResidue K D) :=
    base_division_hom K D
  exact IsLocalRing.ResidueField.lift (baseDivisionResidue K D)

@[simp]
theorem base_residue_division (x : 𝒪[K]) :
    baseResidueDivision K D (IsLocalRing.residue 𝒪[K] x) =
      baseDivisionResidue K D x :=
  rfl

/-- The map of residue fields induced by the centre is injective. -/
theorem base_division_injective :
    Function.Injective (baseResidueDivision K D) := by
  letI : Field (divisionResidueRing K D) := divisionResidueField K D
  exact RingHom.injective (baseResidueDivision K D)

/-- The canonical algebra structure of the division residue field over the
base residue field. -/
@[implicit_reducible]
def divisionResidueAlgebra : Algebra 𝓀[K] (divisionResidueRing K D) := by
  letI : Field (divisionResidueRing K D) := divisionResidueField K D
  exact (baseResidueDivision K D).toAlgebra

/-- The residue-field extension of a local division algebra is
finite-dimensional. -/
theorem division_residue_module :
    letI : Field (divisionResidueRing K D) := divisionResidueField K D
    letI : Algebra 𝓀[K] (divisionResidueRing K D) :=
      divisionResidueAlgebra K D
    Module.Finite 𝓀[K] (divisionResidueRing K D) := by
  letI : Field (divisionResidueRing K D) := divisionResidueField K D
  letI : Algebra 𝓀[K] (divisionResidueRing K D) :=
    divisionResidueAlgebra K D
  letI : Finite (divisionResidueRing K D) := division_residue_ring K D
  exact Module.Finite.of_finite

/-- Milne's residue degree `f = [\bar D : k]`. -/
noncomputable def residueDegree : ℕ := by
  letI : Field (divisionResidueRing K D) := divisionResidueField K D
  letI : Algebra 𝓀[K] (divisionResidueRing K D) :=
    divisionResidueAlgebra K D
  exact Module.finrank 𝓀[K] (divisionResidueRing K D)

theorem residue_degree_finrank :
    residueDegree K D =
      letI : Field (divisionResidueRing K D) := divisionResidueField K D
      letI : Algebra 𝓀[K] (divisionResidueRing K D) :=
        divisionResidueAlgebra K D
      Module.finrank 𝓀[K] (divisionResidueRing K D) :=
  rfl

end

end Submission.CField.LBrauer
