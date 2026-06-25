import Towers.NumberTheory.Locals.UnramifiedResidueLift
import Towers.ClassField.LocalBrauer.ResidueGeneratorSubfield
import Towers.ClassField.LocalBrauer.UnramifiedAdjoin

/-!
# Chapter IV, Section 4: the unramified maximal splitting subfield

When the residue degree of a central division algebra is its degree, a lift
of a primitive residue element generates a maximal commutative subfield.  By
retaining the integral minimal polynomial used in the lift, equality in the
degree bound shows that its reduction is irreducible and separable.  The
integer algebra it generates is therefore formally unramified, and hence
unramified at its maximal ideal in Mathlib's intrinsic sense.
-/

namespace Towers.CField.LBrauer

noncomputable section

open CProduca
open Polynomial
open scoped Valued

universe u

variable (K D : Type u) [NontriviallyNormedField K] [IsUltrametricDist K]
  [ValuativeRel K] [IsNonarchimedeanLocalField K] [DivisionRing D]
  [Valuation.Compatible (NormedField.valuation (K := K))]
  [Algebra K D] [Algebra.IsCentral K D] [Module.Finite K D]

set_option maxHeartbeats 1000000 in
-- Constructing all structures on the lifted residue subfield is expensive.
set_option synthInstance.maxHeartbeats 200000 in
-- Finding formal unramifiedness unfolds the localized integer tower.
/-- If the residue degree is the degree of `D`, there is a lifted primitive
residue element whose generated field is maximal and splitting, while its
integer algebra is unramified over `O_K`. -/
theorem maximal_splitting_subfield
    (hresidue : residueDegree K D = Nat.sqrt (Module.finrank K D)) :
    ∃ alpha : divisionIntegerSubring K D,
      let E := Algebra.adjoin K ({(alpha : D)} : Set D)
      ∃ hcomm : ∀ x y : E, x * y = y * x,
        Module.finrank K E = Nat.sqrt (Module.finrank K D) ∧
          IsMaximalCommutative E ∧
          (letI : IsSimpleRing E :=
            commutative_subalgebra_simple K D E hcomm
           SplitSubalgebra K D E hcomm) ∧
          letI : CommRing E := { (inferInstance : Ring E) with mul_comm := hcomm }
          letI : Module.Finite K E :=
            Module.Finite.of_injective E.val.toLinearMap Subtype.val_injective
          letI : IsDomain E :=
            Function.Injective.isDomain E.val.toRingHom Subtype.val_injective
          letI : Field E := fieldOfFiniteDimensional K E
          let OR := (ValuativeRel.valuation K).integer
          let g : OR →+* E := (algebraMap K E).comp OR.subtype
          letI : Algebra OR E := g.toAlgebra
          let e : E :=
            ⟨(alpha : D), Algebra.subset_adjoin
              (Set.mem_singleton (alpha : D))⟩
          let U := Algebra.adjoin OR ({e} : Set E)
          IsIntegral OR e ∧
            Algebra.FormallyUnramified OR U ∧
            ∃ hlocal : IsLocalRing U,
              letI := hlocal
              ∃ hdvr : IsDiscreteValuationRing U,
                letI := hdvr
                Algebra.IsUnramifiedAt OR (IsLocalRing.maximalIdeal U) := by
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
  letI : IsScalarTower ON K E := IsScalarTower.of_algebraMap_eq' (by rfl)
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
  have hpRootOD : eval₂ (baseDivision K D) alpha pR = 0 := by
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
    have hmap := congrArg (divisionMaximalIdeal K D).ringCon.mk' hpRootOD
    rw [map_zero, hom_eval₂] at hmap
    change eval₂ (baseDivisionResidue K D) _ pR = 0 at hmap
    have halpha' : (divisionMaximalIdeal K D).ringCon.mk' alpha = a := halpha
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
  have hminMap : minpoly K e = p.map (algebraMap ON K) :=
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
  have hmain := residue_maximal_split K D alpha hcomm
    hdegree hresidue
  obtain ⟨hfinrank, hmaximal, hsplit⟩ := hmain
  have hminDegree : (minpoly 𝓀[K] a).natDegree = Module.finrank K E := by
    rw [← hdegreeResidue, hresidue, ← hfinrank]
  have hpbarDegreeLe : pbar.natDegree ≤ Module.finrank K E := by
    rw [hdegreePbar, hdegreeP]
    exact minpoly.natDegree_le e
  have hpbarDegree : pbar.natDegree = (minpoly 𝓀[K] a).natDegree :=
    Nat.le_antisymm (hpbarDegreeLe.trans_eq hminDegree.symm)
      (natDegree_le_of_dvd hminDvd hpbarMonic.ne_zero)
  have hpbarEq : pbar = minpoly 𝓀[K] a :=
    Polynomial.eq_of_monic_of_dvd_of_natDegree_le
      (minpoly.monic (Algebra.IsIntegral.isIntegral a)) hpbarMonic hminDvd
      hpbarDegree.le
  have hpbarIrred : Irreducible pbar := by
    rw [hpbarEq]
    exact minpoly.irreducible (Algebra.IsIntegral.isIntegral a)
  have hpbarSep : pbar.Separable := by
    rw [hpbarEq]
    exact Algebra.IsSeparable.isSeparable 𝓀[K] a
  let g : OR →+* E := (algebraMap K E).comp OR.subtype
  letI : Algebra OR E := g.toAlgebra
  letI : Module.IsTorsionFree OR E :=
    Module.IsTorsionFree.comap Subtype.val
      (fun _ hr ↦ by simpa [isRegular_iff_ne_zero] using hr.ne_zero)
      (fun r x ↦ by
        rw [Algebra.smul_def, Algebra.smul_def]
        rfl)
  have hpRootER : eval₂ g e pR = 0 := by
    change eval₂ g e (p.map normIntegerToRelInteger) = 0
    rw [eval₂_map]
    have hcomp : g.comp normIntegerToRelInteger = f := by
      ext c
      rfl
    simpa [hcomp] using hpRootE
  have heIntR : IsIntegral OR e := ⟨pR, hpRmonic, by
    simpa [aeval_def] using hpRootER⟩
  have hpRirred : Irreducible pR :=
    Polynomial.Monic.irreducible_of_irreducible_map rho pR hpRmonic <| by
      simpa [pbar] using hpbarIrred
  have hpRDvd : minpoly OR e ∣ pR :=
    minpoly.isIntegrallyClosed_dvd heIntR (by simpa [aeval_def] using hpRootER)
  have hminpolyR : minpoly OR e = pR :=
    Polynomial.eq_of_monic_of_associated (minpoly.monic heIntR) hpRmonic
      ((minpoly.irreducible heIntR).associated_of_dvd hpRirred hpRDvd)
  let U := Algebra.adjoin OR ({e} : Set E)
  let hlocal : IsLocalRing U :=
    adjoin_irreducible_minpoly
      OR E pR e hpRmonic hpbarIrred heIntR hminpolyR
  letI : IsLocalRing U := hlocal
  letI : Algebra.FormallyUnramified OR U :=
    formally_separable_minpoly
      OR E pR e hpRmonic hpbarIrred hpbarSep heIntR hminpolyR
  letI : Module.Finite OR U :=
    Algebra.finite_adjoin_simple_of_isIntegral heIntR
  letI : Algebra.IsIntegral OR U := Algebra.IsIntegral.of_finite OR U
  letI : IsDedekindDomain U := isDedekindDomain.of_formallyUnramified OR U
  let hdvr : IsDiscreteValuationRing U := by
    have hORU : Function.Injective (algebraMap OR U) := by
      intro x y hxy
      apply Subtype.ext
      apply (algebraMap K E).injective
      have hxy' := congrArg (fun z : U ↦ (z : E)) hxy
      exact hxy'
    have hnfield : ¬ IsField U := by
      intro hU
      exact IsDiscreteValuationRing.not_isField OR
        (isField_of_isIntegral_of_isField hORU hU)
    have hdedekind : IsDedekindDomain U := inferInstance
    exact ((IsDiscreteValuationRing.TFAE U hnfield).out 2 0).mp hdedekind
  letI : IsDiscreteValuationRing U := hdvr
  refine ⟨alpha, hcomm, hfinrank, hmaximal, hsplit, heIntR, ?_, hlocal,
    hdvr, ?_⟩
  · infer_instance
  · change Algebra.FormallyUnramified OR
      (Localization.AtPrime (IsLocalRing.maximalIdeal U))
    infer_instance

end

end Towers.CField.LBrauer
