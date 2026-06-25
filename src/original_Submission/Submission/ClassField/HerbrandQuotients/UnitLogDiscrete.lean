import Submission.ClassField.HerbrandQuotients.ProductHyperplane
import Mathlib.Topology.Instances.ZMultiples

/-!
# Discreteness of the logarithmic `T`-unit lattice

This is the lattice assertion in the proof of the `T`-unit theorem used by
Milne in Proposition VII.3.1.  Finite coordinates take values in discrete
cyclic logarithmic value groups.  Once they vanish, the element is an
ordinary unit, and discreteness of Dirichlet's ordinary unit lattice
isolates the remaining infinite coordinates.
-/

namespace Submission.CField.HQuotie

open IsDedekindDomain NumberField Representation
open Submission.NumberTheory.Milne
open Submission.CField.Ideles
open Submission.CField.ICohomo
open Submission.CField.NIndex
open scoped BigOperators NNReal

noncomputable section

universe u

variable {K L : Type u} [Field K] [Field L] [NumberField K] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]

/-- A finite coordinate of the raw logarithmic embedding, rescaled to the
globally normalized logarithm. -/
noncomputable def normalizedLogCoordinate
    (S : Finset (NumberFieldPlace K))
    (Q : primesAbovePlaces (K := K) (L := L) S) :
    upperLogLattice (K := K) (L := L) S → ℝ := fun y =>
  placeLogScale (K := K) (L := L) S Q *
    y.1 (upperPlacePrime (K := K) (L := L) S Q)

noncomputable def normalizedLogValue
    (Q : FinitePrime L) : AddSubgroup ℝ :=
  AddSubgroup.zmultiples (Real.log (Ideal.absNorm Q.asIdeal : ℝ))

set_option maxHeartbeats 1000000 in
-- Elaborating the dependent finite-place coercions needs a larger local budget.
theorem normalized_log_zmultiples
    (S : Finset (NumberFieldPlace K))
    (Q : primesAbovePlaces (K := K) (L := L) S)
    (x : Additive (unitsAtPlaces (K := K) (L := L) S)) :
    placeLogScale (K := K) (L := L) S Q *
        upperUnitLog (K := K) (L := L) S x
          (upperPlacePrime (K := K) (L := L) S Q) ∈
      normalizedLogValue Q.1 := by
  rw [log_scale_upper]
  unfold normalizedLogValue
  exact place_log_zmultiples (L := L) Q
    ((Additive.toMul x : unitsAtPlaces (K := K) (L := L) S) : Lˣ)

set_option maxHeartbeats 1000000 in
-- Elaborating the dependent upper-place coordinate needs a larger local budget.
theorem log_coordinate_zmultiples
    (S : Finset (NumberFieldPlace K))
    (Q : primesAbovePlaces (K := K) (L := L) S)
    (y : upperLogLattice (K := K) (L := L) S) :
    normalizedLogCoordinate (K := K) (L := L) S Q y ∈
      normalizedLogValue Q.1 := by
  obtain ⟨x, hx⟩ := y.2
  unfold normalizedLogCoordinate
  rw [show y.1 (upperPlacePrime (K := K) (L := L) S Q) =
      upperUnitLog (K := K) (L := L) S x
        (upperPlacePrime (K := K) (L := L) S Q) from
    congrFun hx.symm _]
  exact normalized_log_zmultiples
    (K := K) (L := L) S Q x

/-- A normalized finite log coordinate, valued in its discrete cyclic
group. -/
noncomputable def logZMultiples
    (S : Finset (NumberFieldPlace K))
    (Q : primesAbovePlaces (K := K) (L := L) S) :
    upperLogLattice (K := K) (L := L) S →
      normalizedLogValue Q.1 := fun y =>
  ⟨normalizedLogCoordinate (K := K) (L := L) S Q y,
    log_coordinate_zmultiples
      (K := K) (L := L) S Q y⟩

theorem log_z_multiples
    (S : Finset (NumberFieldPlace K))
    (Q : primesAbovePlaces (K := K) (L := L) S) :
    Continuous (logZMultiples
      (K := K) (L := L) S Q) := by
  apply Continuous.codRestrict
  unfold normalizedLogCoordinate
  exact continuous_const.mul
    ((continuous_apply
      (upperPlacePrime (K := K) (L := L) S Q)).comp
        continuous_subtype_val)

/-- Vanishing of any one normalized finite logarithmic coordinate is an
open condition on the logarithmic image. -/
theorem open_normalized_log
    (S : Finset (NumberFieldPlace K))
    (Q : primesAbovePlaces (K := K) (L := L) S) :
    IsOpen {y : upperLogLattice (K := K) (L := L) S |
      logZMultiples (K := K) (L := L) S Q y = 0} := by
  exact (isOpen_discrete ({0} : Set (AddSubgroup.zmultiples
      (Real.log (Ideal.absNorm Q.1.asIdeal : ℝ))))).preimage
    (log_z_multiples
      (K := K) (L := L) S Q)

/-- The simultaneous vanishing locus of all finite normalized logarithms. -/
def normalizedLogSet
    (S : Finset (NumberFieldPlace K)) :
    Set (upperLogLattice (K := K) (L := L) S) :=
  {y | ∀ Q, logZMultiples
    (K := K) (L := L) S Q y = 0}

theorem normalized_log_set
    (S : Finset (NumberFieldPlace K)) :
    IsOpen (normalizedLogSet (K := K) (L := L) S) := by
  rw [show normalizedLogSet (K := K) (L := L) S =
      ⋂ Q, {y | logZMultiples
        (K := K) (L := L) S Q y = 0} by
    ext y
    simp [normalizedLogSet]]
  exact isOpen_iInter_of_finite fun Q =>
    open_normalized_log (K := K) (L := L) S Q

/-- Reindex the infinite coordinates of the upper-place function space to
Dirichlet's logarithmic space, including the real/complex multiplicity. -/
noncomputable def upperLogLinear
    (S : Finset (NumberFieldPlace K))
    (hSinf : ∀ v : InfinitePlace K,
      (Sum.inr v : NumberFieldPlace K) ∈ S) :
    (upperPlacesAt (K := K) (L := L) S → ℝ) →ₗ[ℝ]
      NumberField.Units.dirichletUnitTheorem.logSpace L where
  toFun f w := (w.1.mult : ℝ) *
    f (infiniteUpperPlace (K := K) (L := L) S hSinf w.1)
  map_add' f g := by
    funext w
    simp only [Pi.add_apply]
    ring
  map_smul' r f := by
    funext w
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

theorem continuous_log_linear
    (S : Finset (NumberFieldPlace K))
    (hSinf : ∀ v : InfinitePlace K,
      (Sum.inr v : NumberFieldPlace K) ∈ S) :
    Continuous (upperLogLinear
      (K := K) (L := L) S hSinf) :=
  (upperLogLinear
    (K := K) (L := L) S hSinf).continuous_of_finiteDimensional

private theorem ring_integers_valuations
    (x : Lˣ) (hx : ∀ Q : FinitePrime L, Q.valuation L (x : L) = 1) :
    ∃ u : (NumberField.RingOfIntegers L)ˣ, (u : L) = (x : L) := by
  have hxmem : (x : L) ∈
      (algebraMap (NumberField.RingOfIntegers L) L).range :=
    IsDedekindDomain.HeightOneSpectrum.mem_integers_of_valuation_le_one
      L (x : L) fun Q => by rw [hx Q]
  have hxinv : ∀ Q : FinitePrime L,
      Q.valuation L ((x : L)⁻¹) = 1 := by
    intro Q
    rw [map_inv₀, hx Q, inv_one]
  have hxmemInv : (x : L)⁻¹ ∈
      (algebraMap (NumberField.RingOfIntegers L) L).range :=
    IsDedekindDomain.HeightOneSpectrum.mem_integers_of_valuation_le_one
      L ((x : L)⁻¹) fun Q => by rw [hxinv Q]
  obtain ⟨a, ha⟩ := hxmem
  obtain ⟨b, hb⟩ := hxmemInv
  let u : (NumberField.RingOfIntegers L)ˣ :=
    { val := a
      inv := b
      val_inv := by
        apply NumberField.RingOfIntegers.coe_injective
        rw [map_mul, ha, hb]
        exact mul_inv_cancel₀ x.ne_zero
      inv_val := by
        apply NumberField.RingOfIntegers.coe_injective
        rw [map_mul, ha, hb]
        exact inv_mul_cancel₀ x.ne_zero }
  exact ⟨u, ha⟩

private theorem place_valuation_value
    (Q : FinitePrime L) {x : L} (hx : (FinitePlace.mk Q).1 x = 1) :
    Q.valuation L x = 1 := by
  have hnorm : ‖FinitePlace.embedding Q x‖ = 1 := by
    simpa only [FinitePlace.mk_apply] using hx
  rw [FinitePlace.norm_embedding'] at hnorm
  have h' :
      WithZeroMulInt.toNNReal (HeightOneSpectrum.absNorm_ne_zero Q)
          (Q.valuation L x) = 1 := by
    exact_mod_cast hnorm
  exact (WithZeroMulInt.toNNReal_eq_one_iff
    (Q.valuation L x)
    (HeightOneSpectrum.absNorm_ne_zero Q)
    (ne_of_gt (HeightOneSpectrum.one_lt_absNorm_nnreal Q))).mp h'

private theorem valuations_log_set
    (S : Finset (NumberFieldPlace K))
    (y : upperLogLattice (K := K) (L := L) S)
    (hy : y ∈ normalizedLogSet (K := K) (L := L) S)
    (x : Additive (unitsAtPlaces (K := K) (L := L) S))
    (hx : upperUnitLog (K := K) (L := L) S x = y.1) :
    ∀ Q : FinitePrime L,
      Q.valuation L ((((Additive.toMul x :
        unitsAtPlaces (K := K) (L := L) S) : Lˣ) : L)) = 1 := by
  intro Q
  by_cases hQT : Q ∈ primesAbovePlaces (K := K) (L := L) S
  · let q : primesAbovePlaces (K := K) (L := L) S := ⟨Q, hQT⟩
    rw [normalizedLogSet] at hy
    have hzero : normalizedLogCoordinate
        (K := K) (L := L) S q y = 0 :=
      congrArg Subtype.val (hy q)
    unfold normalizedLogCoordinate at hzero
    rw [← hx] at hzero
    change placeLogScale (K := K) (L := L) S q *
        Real.log ((upperPlacePrime
          (K := K) (L := L) S q).2.1
            ((((Additive.toMul x : unitsAtPlaces
              (K := K) (L := L) S) : Lˣ) : L))) = 0 at hzero
    have hrawLog : Real.log ((upperPlacePrime
        (K := K) (L := L) S q).2.1
          ((((Additive.toMul x : unitsAtPlaces
            (K := K) (L := L) S) : Lˣ) : L))) = 0 :=
      (mul_eq_zero.mp hzero).resolve_left
        (log_scale_pos (K := K) (L := L) S q).ne'
    have hraw : (upperPlacePrime
        (K := K) (L := L) S q).2.1
          ((((Additive.toMul x : unitsAtPlaces
            (K := K) (L := L) S) : Lˣ) : L)) = 1 :=
      Real.eq_one_of_pos_of_log_eq_zero
        ((upperPlacePrime (K := K) (L := L) S q).2.1.pos
          ((Additive.toMul x : unitsAtPlaces
            (K := K) (L := L) S) : Lˣ).ne_zero) hrawLog
    apply place_valuation_value Q
    rw [← rpow_log_scale
      (K := K) (L := L) S q]
    rw [hraw, Real.one_rpow]
  · exact (Additive.toMul x).property Q hQT

/-- On a logarithmic vector whose finite coordinates vanish, the infinite
coordinate vector belongs to Dirichlet's ordinary unit lattice. -/
noncomputable def logUnitLattice
    (S : Finset (NumberFieldPlace K))
    (hSinf : ∀ v : InfinitePlace K,
      (Sum.inr v : NumberFieldPlace K) ∈ S) :
    normalizedLogSet (K := K) (L := L) S →
      NumberField.Units.unitLattice L := fun z => by
  let y := z.1
  let x := Classical.choose y.2
  have hx := Classical.choose_spec y.2
  have hvals := valuations_log_set
    (K := K) (L := L) S y z.2 x hx
  let u := Classical.choose (ring_integers_valuations
    ((Additive.toMul x : unitsAtPlaces (K := K) (L := L) S) : Lˣ) hvals)
  have hu := Classical.choose_spec (ring_integers_valuations
    ((Additive.toMul x : unitsAtPlaces (K := K) (L := L) S) : Lˣ) hvals)
  refine ⟨upperLogLinear (K := K) (L := L) S hSinf y.1, ?_⟩
  rw [NumberField.Units.unitLattice, Submodule.map_top]
  refine ⟨Additive.ofMul u, ?_⟩
  funext w
  change NumberField.Units.logEmbedding L (Additive.ofMul u) w = _
  rw [NumberField.Units.dirichletUnitTheorem.logEmbedding_component]
  rw [← hx]
  change (w.1.mult : ℝ) * Real.log (w.1 (u : L)) =
    (w.1.mult : ℝ) * Real.log
      (w.1 ((((Additive.toMul x : unitsAtPlaces
        (K := K) (L := L) S) : Lˣ) : L)))
  rw [hu]

@[simp]
theorem log_lattice_val
    (S : Finset (NumberFieldPlace K))
    (hSinf : ∀ v : InfinitePlace K,
      (Sum.inr v : NumberFieldPlace K) ∈ S)
    (z : normalizedLogSet (K := K) (L := L) S) :
    (logUnitLattice (K := K) (L := L) S hSinf z :
        NumberField.Units.dirichletUnitTheorem.logSpace L) =
      upperLogLinear (K := K) (L := L) S hSinf z.1.1 :=
  by
    unfold logUnitLattice
    dsimp only

theorem continuous_log_lattice
    (S : Finset (NumberFieldPlace K))
    (hSinf : ∀ v : InfinitePlace K,
      (Sum.inr v : NumberFieldPlace K) ∈ S) :
    Continuous (logUnitLattice
      (K := K) (L := L) S hSinf) := by
  apply Continuous.codRestrict
  have hsub : Continuous (fun z : normalizedLogSet
      (K := K) (L := L) S => z.1.1) :=
    continuous_subtype_val.comp continuous_subtype_val
  have hcont : Continuous (fun z : normalizedLogSet
      (K := K) (L := L) S => upperLogLinear
        (K := K) (L := L) S hSinf z.1.1) :=
    (continuous_log_linear
      (K := K) (L := L) S hSinf).comp hsub
  simpa only [log_lattice_val] using hcont

theorem log_unit_lattice
    (S : Finset (NumberFieldPlace K))
    (hSinf : ∀ v : InfinitePlace K,
      (Sum.inr v : NumberFieldPlace K) ∈ S)
    (z : normalizedLogSet (K := K) (L := L) S) :
    logUnitLattice (K := K) (L := L) S hSinf z = 0 ↔
      (z.1 : upperLogLattice (K := K) (L := L) S) = 0 := by
  constructor
  · intro hz
    let y := z.1
    obtain ⟨x, hx⟩ := y.2
    have hvals := valuations_log_set
      (K := K) (L := L) S y z.2 x hx
    obtain ⟨u, hu⟩ := ring_integers_valuations
      ((Additive.toMul x : unitsAtPlaces (K := K) (L := L) S) : Lˣ) hvals
    have hinf : upperLogLinear
        (K := K) (L := L) S hSinf y.1 = 0 := by
      simpa using congrArg
        (fun a : NumberField.Units.unitLattice L =>
          (a : NumberField.Units.dirichletUnitTheorem.logSpace L)) hz
    have hlogu : NumberField.Units.logEmbedding L (Additive.ofMul u) = 0 := by
      funext w
      have hw : upperLogLinear
          (K := K) (L := L) S hSinf y.1 w = 0 := by
        simpa only [Pi.zero_apply] using congrFun hinf w
      rw [← hx] at hw
      change (w.1.mult : ℝ) * Real.log
          (w.1 ((((Additive.toMul x : unitsAtPlaces
            (K := K) (L := L) S) : Lˣ) : L))) = 0 at hw
      change (w.1.mult : ℝ) * Real.log (w.1 (u : L)) = 0
      rw [hu]
      exact hw
    have huTorsion : u ∈ NumberField.Units.torsion L :=
      NumberField.Units.dirichletUnitTheorem.logEmbedding_eq_zero_iff.mp hlogu
    have hxTorsion : Additive.toMul x ∈ CommGroup.torsion
        (unitsAtPlaces (K := K) (L := L) S) := by
      rw [NumberField.Units.torsion, CommGroup.mem_torsion,
        isOfFinOrder_iff_pow_eq_one] at huTorsion
      rw [CommGroup.mem_torsion, isOfFinOrder_iff_pow_eq_one]
      obtain ⟨n, hn, hun⟩ := huTorsion
      refine ⟨n, hn, ?_⟩
      apply Subtype.ext
      apply Units.ext
      have hunL := congrArg (fun a : (NumberField.RingOfIntegers L)ˣ =>
        (a : L)) hun
      simpa [hu] using hunL
    have hxzero : upperUnitLog (K := K) (L := L) S x = 0 :=
      (upper_log_torsion
        (K := K) (L := L) S hSinf x).mpr hxTorsion
    have hyzero : y.1 = 0 := hx.symm.trans hxzero
    exact Subtype.ext hyzero
  · intro hz
    apply Subtype.ext
    rw [log_lattice_val]
    rw [hz]
    exact map_zero _

/-- Zero is isolated in the logarithmic image. -/
theorem open_log_lattice
    (S : Finset (NumberFieldPlace K))
    (hSinf : ∀ v : InfinitePlace K,
      (Sum.inr v : NumberFieldPlace K) ∈ S) :
    IsOpen ({0} : Set
      (upperLogLattice (K := K) (L := L) S)) := by
  let U := normalizedLogSet (K := K) (L := L) S
  have hopenU : IsOpen U :=
    normalized_log_set (K := K) (L := L) S
  have hopenPre : IsOpen {z : U |
      logUnitLattice (K := K) (L := L) S hSinf z = 0} :=
    (isOpen_discrete ({0} : Set (NumberField.Units.unitLattice L))).preimage
      (continuous_log_lattice
        (K := K) (L := L) S hSinf)
  have himage : ((↑) : U →
      upperLogLattice (K := K) (L := L) S) ''
        {z : U | logUnitLattice
          (K := K) (L := L) S hSinf z = 0} =
        ({0} : Set (upperLogLattice (K := K) (L := L) S)) := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact (log_unit_lattice
        (K := K) (L := L) S hSinf z).mp hz
    · intro hy
      have hy0 : y = 0 := by simpa using hy
      subst y
      let z : U := ⟨0, by
        change ∀ Q, logZMultiples
          (K := K) (L := L) S Q 0 = 0
        intro Q
        apply Subtype.ext
        simp [logZMultiples,
          normalizedLogCoordinate]⟩
      refine ⟨z, ?_, rfl⟩
      apply (log_unit_lattice
        (K := K) (L := L) S hSinf z).mpr
      rfl
  rw [← himage]
  exact hopenU.isOpenMap_subtype_val _ hopenPre

/-- The logarithmic image `M⁰` is a discrete subgroup of the ambient real
function space.  This is the lattice clause of the `T`-unit theorem. -/
theorem lattice_discrete_topology
    (S : Finset (NumberFieldPlace K))
    (hSinf : ∀ v : InfinitePlace K,
      (Sum.inr v : NumberFieldPlace K) ∈ S) :
    DiscreteTopology
      (upperLogLattice (K := K) (L := L) S) := by
  rw [discreteTopology_iff_isOpen_singleton_zero]
  exact open_log_lattice
    (K := K) (L := L) S hSinf

end

end Submission.CField.HQuotie
