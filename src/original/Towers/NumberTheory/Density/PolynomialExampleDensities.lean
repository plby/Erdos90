import Towers.NumberTheory.Density.PolynomialFactorization
import Towers.NumberTheory.Density.CubicChebotarevDensities
import Towers.NumberTheory.Density.QuarticSmallGroup
import Towers.NumberTheory.Density.DihedralQuarticChebotarev

/-!
# Literal polynomial-factorization densities in degrees three and four

This file upgrades the abstract cycle-count tables in ANT, Examples 8.36 and
8.37, to statements about the literal degrees of the irreducible factors of a
polynomial after reduction.  The statements are conditional only on the
corresponding concrete model of the Galois action and on Chebotarev.
-/

namespace Towers.NumberTheory.Milne

open DihedralGroup Equiv IsDedekindDomain NumberField Polynomial

noncomputable section

/-! ## Concrete cubic actions -/

/-- The trivial group acting on three roots. -/
def cubicTrivialAction : PUnit →* Equiv.Perm (Fin 3) where
  toFun _ := 1
  map_one' := rfl
  map_mul' _ _ := rfl

/-- The natural permutation action of the cubic transposition subgroup. -/
def cubicCAction : cubicC2 →* Equiv.Perm (Fin 3) := cubicC2.subtype

/-- The alternating group on three roots. -/
abbrev CubicAlternatingGroup := alternatingGroup (Fin 3)

/-- The natural action of `A₃` on three roots. -/
def cubicAlternatingAction : CubicAlternatingGroup →* Equiv.Perm (Fin 3) :=
  (alternatingGroup (Fin 3)).subtype

/-- The natural action of `S₃` on three roots. -/
def cubicSymmetricAction : Equiv.Perm (Fin 3) →* Equiv.Perm (Fin 3) :=
  MonoidHom.id _

/-! The counts below are the rows of the cubic table, expressed using full
partitions, so fixed points appear as parts of size one. -/

theorem cubic_trivial_count :
    Nat.card {g : PUnit //
      ((cubicTrivialAction g).partition).parts = {1, 1, 1}} = 1 := by
  rw [Nat.card_eq_fintype_card]
  decide

theorem c_split_count :
    Nat.card {g : cubicC2 //
      ((cubicCAction g).partition).parts = {1, 1, 1}} = 1 := by
  have hparts (g : cubicC2) :
      ((cubicCAction g).partition).parts = {1, 1, 1} ↔ g = 1 := by
    change (((g : Equiv.Perm (Fin 3)).partition).parts = {1, 1, 1}) ↔ g = 1
    constructor
    · intro h
      by_contra hg
      have hcycle := c_cycle_type g hg
      have hsupport : (g : Equiv.Perm (Fin 3)).support.card = 2 := by
        rw [← Equiv.Perm.sum_cycleType, hcycle]
        simp
      rw [Equiv.Perm.parts_partition, hcycle, hsupport] at h
      exact (by decide : ({2, 1} : Multiset ℕ) ≠ {1, 1, 1}) h
    · rintro rfl
      decide
  let e : {g : cubicC2 //
      ((cubicCAction g).partition).parts = {1, 1, 1}} ≃ PUnit.{1} :=
    { toFun := fun _ => PUnit.unit
      invFun := fun _ => ⟨(1 : cubicC2), (hparts 1).2 rfl⟩
      left_inv := fun g => Subtype.ext ((hparts g.1).1 g.2).symm
      right_inv := fun _ => rfl }
  rw [Nat.card_congr e]
  simp

theorem cubic_c_count :
    Nat.card {g : cubicC2 //
      ((cubicCAction g).partition).parts = {1, 2}} = 1 := by
  have hparts (g : cubicC2) :
      ((cubicCAction g).partition).parts = {1, 2} ↔ g ≠ 1 := by
    change (((g : Equiv.Perm (Fin 3)).partition).parts = {1, 2}) ↔ g ≠ 1
    constructor
    · intro h hg
      subst g
      have hne :
          (((1 : Equiv.Perm (Fin 3)).partition).parts : Multiset ℕ) ≠ {1, 2} := by
        decide
      exact hne h
    · intro hg
      have hcycle := c_cycle_type g hg
      have hsupport : (g : Equiv.Perm (Fin 3)).support.card = 2 := by
        rw [← Equiv.Perm.sum_cycleType, hcycle]
        simp
      rw [Equiv.Perm.parts_partition, hcycle, hsupport]
      decide
  let e : {g : cubicC2 //
      ((cubicCAction g).partition).parts = {1, 2}} ≃ PUnit.{1} :=
    { toFun := fun _ => PUnit.unit
      invFun := fun _ =>
        ⟨cubicCSwap, (hparts cubicCSwap).2 cubic_c_swap⟩
      left_inv := fun g => by
        apply Subtype.ext
        obtain ⟨tau, htau, hunique⟩ :=
          (Nat.card_eq_two_iff' (1 : cubicC2)).mp cubic_c_card
        exact ((hunique g.1 ((hparts g.1).1 g.2)).trans
          (hunique cubicCSwap cubic_c_swap).symm).symm
      right_inv := fun _ => rfl }
  rw [Nat.card_congr e]
  simp

theorem cubic_alternating_count :
    Nat.card {g : CubicAlternatingGroup //
      ((cubicAlternatingAction g).partition).parts = {1, 1, 1}} = 1 := by
  rw [Nat.card_eq_fintype_card]
  decide

theorem alternating_irreducible_count :
    Nat.card {g : CubicAlternatingGroup //
      ((cubicAlternatingAction g).partition).parts = {3}} = 2 := by
  rw [Nat.card_eq_fintype_card]
  decide

theorem symmetric_split_count :
    Nat.card {g : Equiv.Perm (Fin 3) //
      ((cubicSymmetricAction g).partition).parts = {1, 1, 1}} = 1 := by
  rw [Nat.card_eq_fintype_card]
  decide

theorem cubic_symmetric_count :
    Nat.card {g : Equiv.Perm (Fin 3) //
      ((cubicSymmetricAction g).partition).parts = {1, 2}} = 3 := by
  rw [Nat.card_eq_fintype_card]
  decide

theorem symmetric_irreducible_count :
    Nat.card {g : Equiv.Perm (Fin 3) //
      ((cubicSymmetricAction g).partition).parts = {3}} = 2 := by
  rw [Nat.card_eq_fintype_card]
  decide

/-! ## Concrete quartic counts -/

theorem quartic_split_count :
    Nat.card {g : QuarticOrderGroup //
      ((quarticOrderAction g).partition).parts = {1, 1, 1, 1}} = 1 := by
  rw [Nat.card_eq_fintype_card]
  decide

theorem quartic_quadratics_count :
    Nat.card {g : QuarticOrderGroup //
      ((quarticOrderAction g).partition).parts = {2, 2}} = 1 := by
  rw [Nat.card_eq_fintype_card]
  decide

theorem quartic_klein_action :
    Nat.card {g : QuarticKleinGroup //
      ((quarticKleinAction g).partition).parts = {1, 1, 1, 1}} = 1 := by
  rw [Nat.card_eq_fintype_card]
  decide

theorem klein_quadratics_count :
    Nat.card {g : QuarticKleinGroup //
      ((quarticKleinAction g).partition).parts = {2, 2}} = 3 := by
  rw [Nat.card_eq_fintype_card]
  decide

theorem quartic_klein_split :
    Nat.card {g : QuarticKleinGroup //
      ((quarticKleinQuadratic g).partition).parts =
        {1, 1, 1, 1}} = 1 := by
  rw [Nat.card_eq_fintype_card]
  decide

theorem quartic_klein_count :
    Nat.card {g : QuarticKleinGroup //
      ((quarticKleinQuadratic g).partition).parts =
        {1, 1, 2}} = 2 := by
  rw [Nat.card_eq_fintype_card]
  decide

theorem quartic_klein_quadratics :
    Nat.card {g : QuarticKleinGroup //
      ((quarticKleinQuadratic g).partition).parts = {2, 2}} = 1 := by
  rw [Nat.card_eq_fintype_card]
  decide

theorem quartic_action_count :
    Nat.card {g : QuarticCyclicGroup //
      ((quarticCyclicAction g).partition).parts = {1, 1, 1, 1}} = 1 := by
  rw [Nat.card_eq_fintype_card]
  decide

theorem quartic_action_quadratics :
    Nat.card {g : QuarticCyclicGroup //
      ((quarticCyclicAction g).partition).parts = {2, 2}} = 1 := by
  rw [Nat.card_eq_fintype_card]
  decide

theorem quartic_irreducible_count :
    Nat.card {g : QuarticCyclicGroup //
      ((quarticCyclicAction g).partition).parts = {4}} = 2 := by
  rw [Nat.card_eq_fintype_card]
  decide

theorem square_dihedral_action :
    Nat.card {g : DihedralGroup 4 //
      ((squareDihedralAction g).partition).parts = {1, 1, 1, 1}} = 1 := by
  rw [Nat.card_eq_fintype_card]
  decide

theorem square_dihedral_count :
    Nat.card {g : DihedralGroup 4 //
      ((squareDihedralAction g).partition).parts = {1, 1, 2}} = 2 := by
  rw [Nat.card_eq_fintype_card]
  decide

theorem square_dihedral_quadratics :
    Nat.card {g : DihedralGroup 4 //
      ((squareDihedralAction g).partition).parts = {2, 2}} = 3 := by
  rw [Nat.card_eq_fintype_card]
  decide

theorem square_dihedral_irreducible :
    Nat.card {g : DihedralGroup 4 //
      ((squareDihedralAction g).partition).parts = {4}} = 2 := by
  rw [Nat.card_eq_fintype_card]
  decide

theorem quartic_alternating_action :
    Nat.card {g : QuarticAlternatingGroup //
      ((quarticAlternatingAction g).partition).parts = {1, 1, 1, 1}} = 1 := by
  rw [Nat.card_eq_fintype_card]
  decide

theorem quartic_alternating_quadratics :
    Nat.card {g : QuarticAlternatingGroup //
      ((quarticAlternatingAction g).partition).parts = {2, 2}} = 3 := by
  rw [Nat.card_eq_fintype_card]
  decide

theorem quartic_alternating_count :
    Nat.card {g : QuarticAlternatingGroup //
      ((quarticAlternatingAction g).partition).parts = {1, 3}} = 8 := by
  rw [Nat.card_eq_fintype_card]
  decide

theorem quartic_symmetric_split :
    Nat.card {g : Equiv.Perm (Fin 4) //
      ((g : Equiv.Perm (Fin 4)).partition).parts = {1, 1, 1, 1}} = 1 := by
  rw [Nat.card_eq_fintype_card]
  decide

theorem quartic_symmetric_count :
    Nat.card {g : Equiv.Perm (Fin 4) //
      ((g : Equiv.Perm (Fin 4)).partition).parts = {1, 1, 2}} = 6 := by
  rw [Nat.card_eq_fintype_card]
  decide

theorem quartic_symmetric_quadratics :
    Nat.card {g : Equiv.Perm (Fin 4) //
      ((g : Equiv.Perm (Fin 4)).partition).parts = {2, 2}} = 3 := by
  rw [Nat.card_eq_fintype_card]
  decide

theorem quartic_symmetric_action :
    Nat.card {g : Equiv.Perm (Fin 4) //
      ((g : Equiv.Perm (Fin 4)).partition).parts = {1, 3}} = 8 := by
  rw [Nat.card_eq_fintype_card]
  decide

theorem quartic_symmetric_irreducible :
    Nat.card {g : Equiv.Perm (Fin 4) //
      ((g : Equiv.Perm (Fin 4)).partition).parts = {4}} = 6 := by
  rw [Nat.card_eq_fintype_card]
  decide

/-! ## Literal rows of Examples 8.36 and 8.37 -/

variable (K L : Type*) [Field K] [Field L]
  [NumberField K] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

noncomputable local instance literalDensityIntegralClosureDecidableEq :
    DecidableEq (RingOfIntegers L) := Classical.decEq _

variable (f : (RingOfIntegers K)[X]) (hf : f.Monic)
  (hdegree : 0 < f.natDegree)
  (hdisc : f.discr ≠ 0)
  (hsplits :
    (f.map (algebraMap (RingOfIntegers K) (RingOfIntegers L))).Splits)

include hf hdegree hdisc hsplits

/-- The literal trivial-group row of Example 8.36. -/
theorem trivial_density_row
    (e : Gal(L/K) ≃* PUnit)
    (hparts : ∀ sigma,
      ((integralRootAction K L f sigma).partition).parts =
        ((cubicTrivialAction (e sigma)).partition).parts)
    (hcheb : ChebotarevDensityTheorem K L) :
    PNDensit K
      (primesReductionDegrees K f {1, 1, 1}) 1 := by
  have h := degrees_density_equivalent
    K L f hf hdegree hdisc hsplits cubicTrivialAction e hparts
    {1, 1, 1} 1 1 cubic_trivial_count (by simp) hcheb
  simpa using h

/-- The literal `C₂` row of Example 8.36. -/
theorem c_density_row
    (e : Gal(L/K) ≃* cubicC2)
    (hparts : ∀ sigma,
      ((integralRootAction K L f sigma).partition).parts =
        ((cubicCAction (e sigma)).partition).parts)
    (hcheb : ChebotarevDensityTheorem K L) :
    PNDensit K
        (primesReductionDegrees K f {1, 1, 1}) (1 / 2) ∧
      PNDensit K
        (primesReductionDegrees K f {1, 2}) (1 / 2) := by
  constructor
  · have h := degrees_density_equivalent
      K L f hf hdegree hdisc hsplits cubicCAction e hparts
      {1, 1, 1} 1 2 c_split_count cubic_c_card hcheb
    convert h using 1 ; norm_num
  · have h := degrees_density_equivalent
      K L f hf hdegree hdisc hsplits cubicCAction e hparts
      {1, 2} 1 2 cubic_c_count cubic_c_card hcheb
    convert h using 1 ; norm_num

/-- The literal `A₃` row of Example 8.36. -/
theorem alternating_density_row
    (e : Gal(L/K) ≃* CubicAlternatingGroup)
    (hparts : ∀ sigma,
      ((integralRootAction K L f sigma).partition).parts =
        ((cubicAlternatingAction (e sigma)).partition).parts)
    (hcheb : ChebotarevDensityTheorem K L) :
    PNDensit K
        (primesReductionDegrees K f {1, 1, 1}) (1 / 3) ∧
      PNDensit K
        (primesReductionDegrees K f {3}) (2 / 3) := by
  have hcard : Nat.card CubicAlternatingGroup = 3 := by
    rw [nat_card_alternatingGroup]
    norm_num
  constructor
  · have h := degrees_density_equivalent
      K L f hf hdegree hdisc hsplits cubicAlternatingAction e hparts
      {1, 1, 1} 1 3 cubic_alternating_count hcard hcheb
    convert h using 1 ; norm_num
  · have h := degrees_density_equivalent
      K L f hf hdegree hdisc hsplits cubicAlternatingAction e hparts
      {3} 2 3 alternating_irreducible_count hcard hcheb
    convert h using 1

/-- The literal `S₃` row of Example 8.36. -/
theorem symmetric_density_row
    (e : Gal(L/K) ≃* Equiv.Perm (Fin 3))
    (hparts : ∀ sigma,
      ((integralRootAction K L f sigma).partition).parts =
        ((cubicSymmetricAction (e sigma)).partition).parts)
    (hcheb : ChebotarevDensityTheorem K L) :
    PNDensit K
        (primesReductionDegrees K f {1, 1, 1}) (1 / 6) ∧
      PNDensit K
        (primesReductionDegrees K f {1, 2}) (1 / 2) ∧
      PNDensit K
        (primesReductionDegrees K f {3}) (1 / 3) := by
  constructor
  · have h := degrees_density_equivalent
      K L f hf hdegree hdisc hsplits cubicSymmetricAction e hparts
      {1, 1, 1} 1 6 symmetric_split_count s3_card hcheb
    convert h using 1 ; norm_num
  · constructor
    · have h := degrees_density_equivalent
        K L f hf hdegree hdisc hsplits cubicSymmetricAction e hparts
        {1, 2} 3 6 cubic_symmetric_count s3_card hcheb
      convert h using 1 ; norm_num
    · have h := degrees_density_equivalent
        K L f hf hdegree hdisc hsplits cubicSymmetricAction e hparts
        {3} 2 6 symmetric_irreducible_count s3_card hcheb
      convert h using 1 ; norm_num

/-- The literal quartic `C₂` row of Example 8.37(a). -/
theorem quartic_density_row
    (e : Gal(L/K) ≃* QuarticOrderGroup)
    (hparts : ∀ sigma,
      ((integralRootAction K L f sigma).partition).parts =
        ((quarticOrderAction (e sigma)).partition).parts)
    (hcheb : ChebotarevDensityTheorem K L) :
    PNDensit K
        (primesReductionDegrees K f {1, 1, 1, 1}) (1 / 2) ∧
      PNDensit K
        (primesReductionDegrees K f {2, 2}) (1 / 2) := by
  constructor
  · have h := degrees_density_equivalent
      K L f hf hdegree hdisc hsplits quarticOrderAction e hparts
      {1, 1, 1, 1} 1 2 quartic_split_count
      quartic_nat_card hcheb
    convert h using 1 ; norm_num
  · have h := degrees_density_equivalent
      K L f hf hdegree hdisc hsplits quarticOrderAction e hparts
      {2, 2} 1 2 quartic_quadratics_count
      quartic_nat_card hcheb
    convert h using 1 ; norm_num

/-- The literal `V₄` row of Example 8.37(a). -/
theorem klein_density_row
    (e : Gal(L/K) ≃* QuarticKleinGroup)
    (hparts : ∀ sigma,
      ((integralRootAction K L f sigma).partition).parts =
        ((quarticKleinAction (e sigma)).partition).parts)
    (hcheb : ChebotarevDensityTheorem K L) :
    PNDensit K
        (primesReductionDegrees K f {1, 1, 1, 1}) (1 / 4) ∧
      PNDensit K
        (primesReductionDegrees K f {2, 2}) (3 / 4) := by
  constructor
  · have h := degrees_density_equivalent
      K L f hf hdegree hdisc hsplits quarticKleinAction e hparts
      {1, 1, 1, 1} 1 4 quartic_klein_action
      quartic_klein_card hcheb
    convert h using 1 ; norm_num
  · have h := degrees_density_equivalent
      K L f hf hdegree hdisc hsplits quarticKleinAction e hparts
      {2, 2} 3 4 klein_quadratics_count
      quartic_klein_card hcheb
    convert h using 1

/-- The literal density row for the faithful `V₄` action on two quadratic
orbits omitted by the printed classification in Example 8.37. -/
theorem quartic_klein_row
    (e : Gal(L/K) ≃* QuarticKleinGroup)
    (hparts : ∀ sigma,
      ((integralRootAction K L f sigma).partition).parts =
        ((quarticKleinQuadratic (e sigma)).partition).parts)
    (hcheb : ChebotarevDensityTheorem K L) :
    PNDensit K
        (primesReductionDegrees K f {1, 1, 1, 1}) (1 / 4) ∧
      PNDensit K
        (primesReductionDegrees K f {1, 1, 2}) (1 / 2) ∧
      PNDensit K
        (primesReductionDegrees K f {2, 2}) (1 / 4) := by
  constructor
  · have h := degrees_density_equivalent
      K L f hf hdegree hdisc hsplits quarticKleinQuadratic e hparts
      {1, 1, 1, 1} 1 4 quartic_klein_split
      quartic_klein_card hcheb
    convert h using 1 ; norm_num
  · constructor
    · have h := degrees_density_equivalent
        K L f hf hdegree hdisc hsplits quarticKleinQuadratic e hparts
        {1, 1, 2} 2 4 quartic_klein_count
        quartic_klein_card hcheb
      convert h using 1 ; norm_num
    · have h := degrees_density_equivalent
        K L f hf hdegree hdisc hsplits quarticKleinQuadratic e hparts
        {2, 2} 1 4 quartic_klein_quadratics
        quartic_klein_card hcheb
      convert h using 1 ; norm_num

/-- The literal `A₄` row of Example 8.37(a). -/
theorem quartic_alternating_row
    (e : Gal(L/K) ≃* QuarticAlternatingGroup)
    (hparts : ∀ sigma,
      ((integralRootAction K L f sigma).partition).parts =
        ((quarticAlternatingAction (e sigma)).partition).parts)
    (hcheb : ChebotarevDensityTheorem K L) :
    PNDensit K
        (primesReductionDegrees K f {1, 1, 1, 1}) (1 / 12) ∧
      PNDensit K
        (primesReductionDegrees K f {2, 2}) (1 / 4) ∧
      PNDensit K
        (primesReductionDegrees K f {1, 3}) (2 / 3) := by
  constructor
  · have h := degrees_density_equivalent
      K L f hf hdegree hdisc hsplits quarticAlternatingAction e hparts
      {1, 1, 1, 1} 1 12 quartic_alternating_action
      quartic_alternating_card hcheb
    convert h using 1 ; norm_num
  · constructor
    · have h := degrees_density_equivalent
        K L f hf hdegree hdisc hsplits quarticAlternatingAction e hparts
        {2, 2} 3 12 quartic_alternating_quadratics
        quartic_alternating_card hcheb
      convert h using 1 ; norm_num
    · have h := degrees_density_equivalent
        K L f hf hdegree hdisc hsplits quarticAlternatingAction e hparts
        {1, 3} 8 12 quartic_alternating_count
        quartic_alternating_card hcheb
      convert h using 1 ; norm_num

/-- The literal `C₄` row of Example 8.37(b). -/
theorem quartic_factorization_row
    (e : Gal(L/K) ≃* QuarticCyclicGroup)
    (hparts : ∀ sigma,
      ((integralRootAction K L f sigma).partition).parts =
        ((quarticCyclicAction (e sigma)).partition).parts)
    (hcheb : ChebotarevDensityTheorem K L) :
    PNDensit K
        (primesReductionDegrees K f {1, 1, 1, 1}) (1 / 4) ∧
      PNDensit K
        (primesReductionDegrees K f {2, 2}) (1 / 4) ∧
      PNDensit K
        (primesReductionDegrees K f {4}) (1 / 2) := by
  constructor
  · have h := degrees_density_equivalent
      K L f hf hdegree hdisc hsplits quarticCyclicAction e hparts
      {1, 1, 1, 1} 1 4 quartic_action_count
      quartic_cyclic_card hcheb
    convert h using 1 ; norm_num
  · constructor
    · have h := degrees_density_equivalent
        K L f hf hdegree hdisc hsplits quarticCyclicAction e hparts
        {2, 2} 1 4 quartic_action_quadratics
        quartic_cyclic_card hcheb
      convert h using 1 ; norm_num
    · have h := degrees_density_equivalent
        K L f hf hdegree hdisc hsplits quarticCyclicAction e hparts
        {4} 2 4 quartic_irreducible_count
        quartic_cyclic_card hcheb
      convert h using 1 ; norm_num

/-- The literal `D₈` row singled out in Example 8.37. -/
theorem dihedral_quartic_row
    (e : Gal(L/K) ≃* DihedralGroup 4)
    (hparts : ∀ sigma,
      ((integralRootAction K L f sigma).partition).parts =
        ((squareDihedralAction (e sigma)).partition).parts)
    (hcheb : ChebotarevDensityTheorem K L) :
    PNDensit K
        (primesReductionDegrees K f {1, 1, 1, 1}) (1 / 8) ∧
      PNDensit K
        (primesReductionDegrees K f {1, 1, 2}) (1 / 4) ∧
      PNDensit K
        (primesReductionDegrees K f {2, 2}) (3 / 8) ∧
      PNDensit K
        (primesReductionDegrees K f {4}) (1 / 4) := by
  have hcard : Nat.card (DihedralGroup 4) = 8 := by
    simpa using DihedralGroup.nat_card (n := 4)
  constructor
  · have h := degrees_density_equivalent
      K L f hf hdegree hdisc hsplits squareDihedralAction e hparts
      {1, 1, 1, 1} 1 8 square_dihedral_action hcard hcheb
    convert h using 1 ; norm_num
  · constructor
    · have h := degrees_density_equivalent
        K L f hf hdegree hdisc hsplits squareDihedralAction e hparts
        {1, 1, 2} 2 8 square_dihedral_count hcard hcheb
      convert h using 1 ; norm_num
    · constructor
      · have h := degrees_density_equivalent
          K L f hf hdegree hdisc hsplits squareDihedralAction e hparts
          {2, 2} 3 8 square_dihedral_quadratics hcard hcheb
        convert h using 1
      · have h := degrees_density_equivalent
          K L f hf hdegree hdisc hsplits squareDihedralAction e hparts
          {4} 2 8 square_dihedral_irreducible hcard hcheb
        convert h using 1 ; norm_num

/-- The literal `S₄` row of Example 8.37(b). -/
theorem quartic_symmetric_row
    (e : Gal(L/K) ≃* Equiv.Perm (Fin 4))
    (hparts : ∀ sigma,
      ((integralRootAction K L f sigma).partition).parts =
        ((e sigma).partition).parts)
    (hcheb : ChebotarevDensityTheorem K L) :
    PNDensit K
        (primesReductionDegrees K f {1, 1, 1, 1}) (1 / 24) ∧
      PNDensit K
        (primesReductionDegrees K f {1, 1, 2}) (1 / 4) ∧
      PNDensit K
        (primesReductionDegrees K f {2, 2}) (1 / 8) ∧
      PNDensit K
        (primesReductionDegrees K f {1, 3}) (1 / 3) ∧
      PNDensit K
        (primesReductionDegrees K f {4}) (1 / 4) := by
  let rho : Equiv.Perm (Fin 4) →* Equiv.Perm (Fin 4) := MonoidHom.id _
  have hparts' : ∀ sigma,
      ((integralRootAction K L f sigma).partition).parts =
        ((rho (e sigma)).partition).parts := hparts
  constructor
  · have h := degrees_density_equivalent
      K L f hf hdegree hdisc hsplits rho e hparts'
      {1, 1, 1, 1} 1 24 quartic_symmetric_split s4_card hcheb
    convert h using 1 ; norm_num
  · constructor
    · have h := degrees_density_equivalent
        K L f hf hdegree hdisc hsplits rho e hparts'
        {1, 1, 2} 6 24 quartic_symmetric_count s4_card hcheb
      convert h using 1 ; norm_num
    · constructor
      · have h := degrees_density_equivalent
          K L f hf hdegree hdisc hsplits rho e hparts'
          {2, 2} 3 24 quartic_symmetric_quadratics s4_card hcheb
        convert h using 1 ; norm_num
      · constructor
        · have h := degrees_density_equivalent
            K L f hf hdegree hdisc hsplits rho e hparts'
            {1, 3} 8 24 quartic_symmetric_action s4_card hcheb
          convert h using 1 ; norm_num
        · have h := degrees_density_equivalent
            K L f hf hdegree hdisc hsplits rho e hparts'
            {4} 6 24 quartic_symmetric_irreducible s4_card hcheb
          convert h using 1 ; norm_num

end

end Towers.NumberTheory.Milne
