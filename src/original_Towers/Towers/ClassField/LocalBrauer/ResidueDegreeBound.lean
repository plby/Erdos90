import Mathlib.FieldTheory.PrimitiveElement
import Towers.ClassField.LocalBrauer.DivisionAlgebraIntegrality
import Towers.ClassField.LocalBrauer.LocalDivisionAlgebra
import Towers.ClassField.LocalBrauer.DivisionResidueExtension

/-!
# Chapter IV, Section 4: the residue-degree bound

Milne proves that the residue degree of a central division algebra of degree
`n` is at most `n`.  Choose a primitive element of the finite residue field,
lift it to an integer `alpha`, and reduce an integral minimal polynomial of
`alpha`.  The minimal polynomial of the residue class divides that reduction,
while `K[alpha]` has degree at most `n`.
-/

namespace Towers.CField.LBrauer

noncomputable section

open Polynomial
open scoped Valued

universe u

variable (K D : Type u) [NontriviallyNormedField K] [IsUltrametricDist K]
  [ValuativeRel K] [IsNonarchimedeanLocalField K] [DivisionRing D]
  [Valuation.Compatible (NormedField.valuation (K := K))]
  [Algebra K D] [Algebra.IsCentral K D] [Module.Finite K D]

set_option maxHeartbeats 1000000 in
-- Several field and scalar-tower structures coexist on the generated subfield.
omit [Algebra.IsCentral K D] in
/-- A primitive element of the division residue field can be lifted to an
integer `alpha` whose generated commutative subfield has degree at least the
residue degree. -/
theorem residue_generator_lift :
    ∃ alpha : divisionIntegerSubring K D,
      let E := Algebra.adjoin K ({(alpha : D)} : Set D)
      (∀ x y : E, x * y = y * x) ∧
        residueDegree K D ≤ Module.finrank K E := by
  let d := divisionResidueRing K D
  letI : Field d := divisionResidueField K D
  letI : Algebra 𝓀[K] d := divisionResidueAlgebra K D
  letI : Module.Finite 𝓀[K] d := division_residue_module K D
  letI : Finite d := division_residue_ring K D
  letI : Finite 𝓀[K] := local_field_residue K
  letI : Algebra.IsSeparable 𝓀[K] d := by infer_instance
  obtain ⟨a, ha⟩ := Field.exists_primitive_element 𝓀[K] d
  obtain ⟨alpha, halpha⟩ :=
    (divisionMaximalIdeal K D).ringCon.mk'_surjective a
  let E : Subalgebra K D := Algebra.adjoin K ({(alpha : D)} : Set D)
  have hset : ∀ x ∈ ({(alpha : D)} : Set D),
      ∀ y ∈ ({(alpha : D)} : Set D), x * y = y * x := by
    intro x hx y hy
    simp only [Set.mem_singleton_iff] at hx hy
    subst x
    subst y
    rfl
  have hcomm : ∀ x y : E, x * y = y * x :=
    by
      letI : IsMulCommutative E := Algebra.isMulCommutative_adjoin K hset
      exact mul_comm'
  letI : CommRing E := { (inferInstance : Ring E) with mul_comm := hcomm }
  letI : Module.Finite K E :=
    Module.Finite.of_injective E.val.toLinearMap Subtype.val_injective
  letI : IsDomain E :=
    Function.Injective.isDomain E.val.toRingHom Subtype.val_injective
  letI : Field E := fieldOfFiniteDimensional K E
  let e : E :=
    ⟨(alpha : D), Algebra.subset_adjoin (Set.mem_singleton (alpha : D))⟩
  let ON := baseIntegerRing K
  let OR := (ValuativeRel.valuation K).integer
  let normIntegerToRelInteger : ON →+* OR := {
    toFun x := ⟨x, by
      have hx : NormedField.valuation (x : K) ≤ 1 := x.property
      exact (ValuativeRel.isEquiv (NormedField.valuation (K := K))
        (ValuativeRel.valuation K)).le_one_iff_le_one.mp hx⟩
    map_one' := by ext; rfl
    map_mul' _ _ := by ext; rfl
    map_zero' := by ext; rfl
    map_add' _ _ := by ext; rfl }
  let f : ON →+* E := (algebraMap K E).comp ON.subtype
  letI : Algebra ON E := f.toAlgebra
  letI : IsScalarTower ON K E :=
    IsScalarTower.of_algebraMap_eq' (by rfl)
  have halphaIntD : (integerDivision K D).IsIntegralElem (alpha : D) :=
    (division_subring_elem K D (alpha : D)).mp alpha.property
  have heInt : IsIntegral ON e := by
    apply RingHom.IsIntegralElem.of_map
      (f := f) (g := E.val.toRingHom) Subtype.val_injective
    simpa [ON, f, e, integerDivision] using halphaIntD
  let p : ON[X] := minpoly ON e
  have hpmonic : p.Monic := minpoly.monic heInt
  have hpRootE : eval₂ f e p = 0 := minpoly.aeval ON e
  have hpRootD : eval₂ (integerDivision K D) (alpha : D) p = 0 := by
    have h := congrArg E.val.toRingHom hpRootE
    rw [map_zero, hom_eval₂] at h
    change eval₂ (E.val.toRingHom.comp f) (alpha : D) p = 0 at h
    have hmaps : E.val.toRingHom.comp f = integerDivision K D := by
      ext c
      rfl
    simpa [hmaps] using h
  let pR : OR[X] := p.map normIntegerToRelInteger
  have hpRmonic : pR.Monic := hpmonic.map _
  have hpRootOD :
      eval₂ (baseDivision K D) alpha pR = 0 := by
    apply Subtype.ext
    change (divisionIntegerSubring K D).subtype
      (eval₂ (baseDivision K D) alpha pR) =
        (divisionIntegerSubring K D).subtype 0
    rw [hom_eval₂]
    change eval₂
      ((divisionIntegerSubring K D).subtype.comp
        (baseDivision K D)) (alpha : D) pR = 0
    change eval₂ _ _ (p.map normIntegerToRelInteger) = 0
    rw [eval₂_map]
    simpa [ON, OR, integerDivision, baseDivision,
      normIntegerToRelInteger] using hpRootD
  let rho : OR →+* 𝓀[K] := IsLocalRing.residue OR
  let pbar : 𝓀[K][X] := pR.map rho
  have hpbarRoot : aeval a pbar = 0 := by
    have hmap := congrArg
      (divisionMaximalIdeal K D).ringCon.mk' hpRootOD
    rw [map_zero, hom_eval₂] at hmap
    change eval₂ (baseDivisionResidue K D) _ pR = 0 at hmap
    have halpha' :
        (divisionMaximalIdeal K D).ringCon.mk' alpha = a := halpha
    rw [halpha'] at hmap
    change eval₂ (algebraMap 𝓀[K] d) a pbar = 0
    rw [eval₂_map]
    simpa [d, OR, rho, pbar, baseDivisionResidue,
      divisionResidueAlgebra] using hmap
  have hminDvd : minpoly 𝓀[K] a ∣ pbar := minpoly.dvd 𝓀[K] a hpbarRoot
  have hpbarMonic : pbar.Monic := hpRmonic.map _
  have hdegreeResidue :
      residueDegree K D = (minpoly 𝓀[K] a).natDegree := by
    rw [residue_degree_finrank]
    exact (Field.primitive_element_iff_minpoly_natDegree_eq 𝓀[K] a).mp ha |>.symm
  have hdegreePR : pR.natDegree = p.natDegree := by
    dsimp [pR]
    exact hpmonic.natDegree_map _
  have hdegreePbar : pbar.natDegree = p.natDegree :=
    (hpRmonic.natDegree_map _).trans hdegreePR
  have hminMap :
      minpoly K e = p.map (algebraMap ON K) :=
    minpoly.isIntegrallyClosed_eq_field_fractions' K heInt
  have hdegreeP : p.natDegree = (minpoly K e).natDegree := by
    rw [hminMap, hpmonic.natDegree_map]
  have hdegree : residueDegree K D ≤ Module.finrank K E := by
    calc
      residueDegree K D = (minpoly 𝓀[K] a).natDegree := hdegreeResidue
      _ ≤ pbar.natDegree := natDegree_le_of_dvd hminDvd hpbarMonic.ne_zero
      _ = p.natDegree := hdegreePbar
      _ = (minpoly K e).natDegree := hdegreeP
      _ ≤ Module.finrank K E := minpoly.natDegree_le e
  exact ⟨alpha, hcomm, hdegree⟩

/-- Milne's bound `f ≤ n` for the residue degree of a central division
algebra of dimension `n²`. -/
theorem degree_sqrt_finrank :
    residueDegree K D ≤ Nat.sqrt (Module.finrank K D) := by
  obtain ⟨alpha, hcomm, hdegree⟩ := residue_generator_lift K D
  exact hdegree.trans <|
    commutative_subalgebra_finrank K D
      (Algebra.adjoin K ({(alpha : D)} : Set D)) hcomm

end

end Towers.CField.LBrauer
