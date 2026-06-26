import Towers.ClassField.CrossedProducts.CohomologyRestriction
import Towers.ClassField.CrossedProducts.BrauerRestriction
import Towers.ClassField.CrossedProducts.RelativeGroupMono
import Towers.ClassField.CrossedProducts.Cohomology
import Towers.ClassField.CrossedProducts.ProductBaseChange
import Towers.ClassField.BrauerGroups.BaseChangeTower
import Towers.ClassField.LocalBrauer.ConcreteInflationMorita
import Towers.ClassField.GrunwaldWang.CyclicDivision
import Towers.ClassField.GlobalClass.BrauerSequenceStatements
import Towers.NumberTheory.Galois.PlaceCompletionDegree
import Towers.NumberTheory.Completions.UnramifiedCompletion
import Towers.FieldTheory.CentralFactorSet
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Hilbert90


/-!
# Brauer obstruction of a central embedding problem

This file transports the explicit factor-set obstruction of a central group
extension to the relative Brauer group of a finite Galois extension.  The
coefficient map is deliberately explicit: in the cubic application it is the
identification of the central kernel with the cube roots of unity in a
cyclotomic base change.
-/

noncomputable section

namespace Towers
namespace TBluepr

open Towers.CField.BGroups
open Towers.CField.CProduca
open Towers.CField.LBrauer
open Towers.CField.Ideles
open Towers.CField.GClass
open Towers.NumberTheory.Milne
open NumberField
open IsDedekindDomain
open scoped Pointwise TensorProduct

attribute [local instance] Units.mulDistribMulActionRight
attribute [local instance low] Algebra.TensorProduct.rightAlgebra

universe u v w z

local instance centralBrauerRingOfIntegersGaloisAction
    {K L : Type u} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] :
    MulSemiringAction Gal(L/K) (NumberField.RingOfIntegers L) :=
  IsIntegralClosure.MulSemiringAction
    (NumberField.RingOfIntegers K) K L (NumberField.RingOfIntegers L)

local instance centralBrauerRingOfIntegersSMulCommClass
    {K L : Type u} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] :
    SMulCommClass Gal(L/K) (NumberField.RingOfIntegers K)
      (NumberField.RingOfIntegers L) where
  smul_comm sigma a b := by
    apply Subtype.ext
    have hG (x : NumberField.RingOfIntegers L) :
        ((sigma • x : NumberField.RingOfIntegers L) : L) =
          sigma (x : L) :=
      algebraMap.coe_smul' (B := NumberField.RingOfIntegers L)
        (C := L) sigma x
    have hA (x : NumberField.RingOfIntegers L) :
        ((a • x : NumberField.RingOfIntegers L) : L) =
          (a : K) • (x : L) :=
      algebraMap.coe_smul (A := NumberField.RingOfIntegers K)
        (B := NumberField.RingOfIntegers L) (C := L) a x
    calc
      ((sigma • (a • b) : NumberField.RingOfIntegers L) : L) =
          sigma (((a • b : NumberField.RingOfIntegers L) : L)) :=
        hG (a • b)
      _ = sigma ((a : K) • (b : L)) := congrArg sigma (hA b)
      _ = (a : K) • sigma (b : L) := smul_comm sigma (a : K) (b : L)
      _ = (a : K) •
          ((sigma • b : NumberField.RingOfIntegers L) : L) :=
        congrArg (fun y : L => (a : K) • y) (hG b).symm
      _ = ((a • (sigma • b) : NumberField.RingOfIntegers L) : L) :=
        (hA (sigma • b)).symm

/-- The residue field at a nonarchimedean global place is canonically the
residue field of its completed valuation ring. -/
noncomputable def centeredCompletionResidue
    {L : Type u} [Field L] [NumberField L]
    (w : AbsoluteValue L ℝ) (hw : w.IsNontrivial)
    (hwna : IsNonarchimedean w) :
    let Q := nonarchimedeanHeightSpectrum w hw hwna
    letI : IsUltrametricDist w.Completion :=
      absoluteUltrametricDist w hwna
    (NumberField.RingOfIntegers L ⧸ Q.asIdeal) ≃+*
      IsLocalRing.ResidueField (completionIntegerRing w) := by
  let Q := nonarchimedeanHeightSpectrum w hw hwna
  letI : IsUltrametricDist w.Completion :=
    absoluteUltrametricDist w hwna
  let eQuotient : (NumberField.RingOfIntegers L ⧸ Q.asIdeal) ≃+*
      Q.asIdeal.ResidueField :=
    RingEquiv.ofBijective
      (algebraMap (NumberField.RingOfIntegers L ⧸ Q.asIdeal)
        Q.asIdeal.ResidueField)
      Q.asIdeal.bijective_algebraMap_quotient_residueField
  exact (eQuotient.trans
    (placeAdicResidue Q)).trans
      (IsLocalRing.ResidueField.mapEquiv
        (centeredIntegerAdic w hw hwna)).symm

set_option maxHeartbeats 1000000 in
-- Residue-field comparison unfolds the adic-completion equivalences.
set_option synthInstance.maxHeartbeats 100000 in
-- Removing redundant goal reshaping leaves the integral-ideal search contiguous.
@[simp]
theorem centered_residue_mk
    {L : Type u} [Field L] [NumberField L]
    (w : AbsoluteValue L ℝ) (hw : w.IsNontrivial)
    (hwna : IsNonarchimedean w)
    (x : NumberField.RingOfIntegers L) :
    let Q := nonarchimedeanHeightSpectrum w hw hwna
    letI : IsUltrametricDist w.Completion :=
      absoluteUltrametricDist w hwna
    centeredCompletionResidue w hw hwna
        (Ideal.Quotient.mk Q.asIdeal x) =
      IsLocalRing.residue (completionIntegerRing w)
        (integersCenteredInteger w hw hwna x) := by
  dsimp only
  let Q := nonarchimedeanHeightSpectrum w hw hwna
  letI : IsUltrametricDist w.Completion :=
    absoluteUltrametricDist w hwna
  letI : Fact (FinitePlace.mk Q).val.IsNontrivial :=
    ⟨absolute_value_nontrivial Q⟩
  letI : IsUltrametricDist (FinitePlace.mk Q).val.Completion :=
    placeUltrametricDist Q
  have hAdic :
      placeAdicResidue Q
          (algebraMap (NumberField.RingOfIntegers L ⧸ Q.asIdeal)
            Q.asIdeal.ResidueField
            (Ideal.Quotient.mk Q.asIdeal x)) =
        IsLocalRing.residue (Q.adicCompletionIntegers L)
          (algebraMap (NumberField.RingOfIntegers L)
            (Q.adicCompletionIntegers L) x) := by
    let A := Localization.AtPrime Q.asIdeal
    let C := Q.adicCompletionIntegers L
    let f : A →+* C := primeAdicIntegers (K := L) Q
    letI : IsLocalHom f :=
      adic_integers_hom (K := L) Q
    letI : IsTopologicalRing C :=
      Subring.instIsTopologicalRing _
    let hf := adic_integers_range (K := L) Q
    let J := IsLocalRing.maximalIdeal C
    let hJ : IsOpen J := by
      simpa only [pow_one] using
        open_maximal_integers (K := L) Q 1
    have hdense (a : A) :
        denseRangeOpen f hf J hJ
            (Ideal.Quotient.mk (J.comap f) a) =
          Ideal.Quotient.mk J (f a) :=
      range_open_mk f hf J hJ a
    let eAdic : Q.asIdeal.ResidueField ≃+*
        IsLocalRing.ResidueField C :=
      (Ideal.quotEquivOfEq (IsLocalRing.maximalIdeal_comap f).symm).trans
        (denseRangeOpen f hf J hJ)
    have he : placeAdicResidue Q = eAdic := by
      apply RingEquiv.ext
      intro z
      rfl
    rw [he]
    change eAdic
      (algebraMap (NumberField.RingOfIntegers L ⧸ Q.asIdeal)
        Q.asIdeal.ResidueField
        (algebraMap (NumberField.RingOfIntegers L)
          (NumberField.RingOfIntegers L ⧸ Q.asIdeal) x)) = _
    rw [← IsScalarTower.algebraMap_apply
      (NumberField.RingOfIntegers L)
      (NumberField.RingOfIntegers L ⧸ Q.asIdeal)
      Q.asIdeal.ResidueField x]
    rw [show algebraMap (NumberField.RingOfIntegers L)
        Q.asIdeal.ResidueField x =
      Ideal.Quotient.mk (IsLocalRing.maximalIdeal
        (Localization.AtPrime Q.asIdeal))
        (algebraMap (NumberField.RingOfIntegers L)
          (Localization.AtPrime Q.asIdeal) x) from rfl]
    unfold eAdic
    change (denseRangeOpen f hf J hJ)
      ((Ideal.quotEquivOfEq
        (IsLocalRing.maximalIdeal_comap f).symm)
        (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A)
          (algebraMap (NumberField.RingOfIntegers L) A x))) = _
    rw [Ideal.quotEquivOfEq_mk,
      hdense,
      adic_integers_algebra]
    rfl
  rw [show centeredCompletionResidue w hw hwna
      (Ideal.Quotient.mk Q.asIdeal x) =
      (IsLocalRing.ResidueField.mapEquiv
        (centeredIntegerAdic w hw hwna)).symm
        (placeAdicResidue Q
          (algebraMap (NumberField.RingOfIntegers L ⧸ Q.asIdeal)
            Q.asIdeal.ResidueField
            (Ideal.Quotient.mk Q.asIdeal x))) by rfl]
  change (IsLocalRing.ResidueField.mapEquiv
      (centeredIntegerAdic w hw hwna)).symm
      (placeAdicResidue Q
        (algebraMap (NumberField.RingOfIntegers L ⧸ Q.asIdeal)
          Q.asIdeal.ResidueField
          (Ideal.Quotient.mk Q.asIdeal x))) = _
  rw [hAdic]
  rfl

/-- Inertia membership is transported by an equivariant map whose induced
map on residue rings is an equivalence. -/
theorem inertia_quotient_equiv
    {R : Type u} {B : Type v} [CommRing R] [CommRing B]
    {G : Type w} {H : Type z} [Group G] [Group H]
    [MulSemiringAction G R] [MulSemiringAction H B]
    (I : Ideal R) (J : Ideal B) (eG : G ≃* H) (f : R →+* B)
    (hsmul : ∀ sigma x, eG sigma • f x = f (sigma • x))
    (hstable : ∀ (tau : H) (z : B), z ∈ J → tau • z ∈ J)
    (eResidue : (R ⧸ I) ≃+* (B ⧸ J))
    (heResidue : ∀ x, eResidue (Ideal.Quotient.mk I x) =
      Ideal.Quotient.mk J (f x))
    (sigma : G) :
    (sigma ∈ I.inertia G) ↔ (eG sigma ∈ J.inertia H) := by
  constructor
  · intro hsigma y
    obtain ⟨ybar, hybar⟩ := eResidue.surjective
      (Ideal.Quotient.mk J y)
    obtain ⟨x, hx⟩ := Ideal.Quotient.mk_surjective ybar
    subst ybar
    have hyf : y - f x ∈ J := by
      rw [← Ideal.Quotient.eq]
      exact hybar.symm.trans (heResidue x)
    have hsigmaf : eG sigma • f x - f x ∈ J := by
      rw [← Ideal.Quotient.eq]
      rw [hsmul]
      have hxmod : Ideal.Quotient.mk I (sigma • x) =
          Ideal.Quotient.mk I x := by
        rw [Ideal.Quotient.eq]
        exact hsigma x
      calc
        Ideal.Quotient.mk J (f (sigma • x)) =
            eResidue (Ideal.Quotient.mk I (sigma • x)) :=
          (heResidue _).symm
        _ = eResidue (Ideal.Quotient.mk I x) :=
          congrArg eResidue hxmod
        _ = Ideal.Quotient.mk J (f x) := heResidue x
    have hpreserve : eG sigma • (y - f x) ∈ J := by
      exact hstable (eG sigma) (y - f x) hyf
    have hlast : f x - y ∈ J := by
      simpa only [neg_sub] using J.neg_mem hyf
    have hsum := J.add_mem (J.add_mem hpreserve hsigmaf) hlast
    have heq :
        (eG sigma • (y - f x) + (eG sigma • f x - f x)) +
            (f x - y) = eG sigma • y - y := by
      rw [smul_sub]
      ring
    rw [← heq]
    exact hsum
  · intro hsigma x
    change sigma • x - x ∈ I
    rw [← Ideal.Quotient.eq]
    apply eResidue.injective
    rw [heResidue, heResidue]
    rw [Ideal.Quotient.eq]
    rw [← hsmul]
    exact hsigma (f x)

/-- An equivariant residue-ring equivalence transports the defining power
formula for an arithmetic Frobenius. -/
theorem action_arith_frob
    {R : Type u} {S : Type v} {B : Type w}
    [CommRing R] [CommRing S] [CommRing B] [Algebra R S]
    {G : Type z} {H : Type*} [Group G] [Group H]
    [MulSemiringAction G S] [SMulCommClass G R S]
    [MulSemiringAction H B]
    (I : Ideal S) (J : Ideal B) (eG : G ≃* H) (f : S →+* B)
    (hsmul : ∀ sigma x, eG sigma • f x = f (sigma • x))
    (hstable : ∀ (tau : H) (y : B), y ∈ J → tau • y ∈ J)
    (eResidue : (S ⧸ I) ≃+* (B ⧸ J))
    (heResidue : ∀ x, eResidue (Ideal.Quotient.mk I x) =
      Ideal.Quotient.mk J (f x))
    (sigma : G) (hsigma : IsArithFrobAt R sigma I) (y : B) :
    Ideal.Quotient.mk J (eG sigma • y) =
      (Ideal.Quotient.mk J y) ^ Nat.card (R ⧸ I.under R) := by
  obtain ⟨ybar, hybar⟩ := eResidue.surjective (Ideal.Quotient.mk J y)
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective ybar
  have hyf : y - f x ∈ J := by
    rw [← Ideal.Quotient.eq]
    exact hybar.symm.trans (heResidue x)
  have haction : Ideal.Quotient.mk J (eG sigma • y) =
      Ideal.Quotient.mk J (eG sigma • f x) := by
    rw [Ideal.Quotient.eq]
    rw [← smul_sub]
    exact hstable (eG sigma) (y - f x) hyf
  calc
    Ideal.Quotient.mk J (eG sigma • y) =
        Ideal.Quotient.mk J (eG sigma • f x) := haction
    _ = Ideal.Quotient.mk J (f (sigma • x)) := by rw [hsmul]
    _ = eResidue (Ideal.Quotient.mk I (sigma • x)) :=
      (heResidue _).symm
    _ = eResidue
        ((Ideal.Quotient.mk I x) ^ Nat.card (R ⧸ I.under R)) := by
      exact congrArg eResidue (hsigma.mk_apply x)
    _ = (eResidue (Ideal.Quotient.mk I x)) ^
        Nat.card (R ⧸ I.under R) := by rw [map_pow]
    _ = (Ideal.Quotient.mk J y) ^ Nat.card (R ⧸ I.under R) := by
      exact congrArg (fun z => z ^ Nat.card (R ⧸ I.under R)) hybar

set_option maxHeartbeats 4000000 in
-- Elaboration and instance synthesis each need an explicit local budget.
set_option synthInstance.maxHeartbeats 1000000 in
-- Completion and integral-closure instance synthesis has a large telescope.
/-- The decomposition-group equivalence with the Galois group of the
completion identifies global inertia with inertia of the completed valuation
ring. -/
theorem decomposition_completion_inertia
    {K L : Type u} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (v : AbsoluteValue K ℝ) [Fact v.IsNontrivial]
    [IsUltrametricDist v.Completion] (_hvna : IsNonarchimedean v)
    (w : Towers.CField.ICohomo.CompletionPlacesAbove
      (L := L) v)
    [Finite (Towers.CField.ICohomo.CompletionPlacesAbove
      (L := L) v)]
    [Nonempty (Towers.CField.ICohomo.CompletionPlacesAbove
      (L := L) v)]
    [MulAction.IsPretransitive Gal(L/K)
      (Towers.CField.ICohomo.CompletionPlacesAbove
        (L := L) v)] :
    let hw := absolute_extension_nontrivial v w
    let hwna := absolute_extension_nonarchimedean v w
    let Q := nonarchimedeanHeightSpectrum w.1 hw hwna
    letI : Fact w.1.IsNontrivial := ⟨hw⟩
    letI : IsUltrametricDist w.1.Completion :=
      absoluteUltrametricDist w.1 hwna
    letI : Fact (AbsoluteValue.LiesOver w.1 v) := ⟨w.2⟩
    letI : Algebra v.Completion w.1.Completion :=
      (completionLies v w.1 w.2).toAlgebra
    letI : FiniteDimensional v.Completion w.1.Completion :=
      placeCompletionDimensional v w
    letI : IsGalois v.Completion w.1.Completion :=
      placeCompletionGalois v w
    let A := completionIntegerRing v
    let B := completionIntegerRing w.1
    letI : Algebra A v.Completion := A.subtype.toAlgebra
    letI : Algebra A B := completionIntegerLies v w.1 w.2
    letI : Algebra B w.1.Completion := B.subtype.toAlgebra
    letI : Algebra A w.1.Completion :=
      ((completionLies v w.1 w.2).comp A.subtype).toAlgebra
    letI : IsScalarTower A B w.1.Completion :=
      IsScalarTower.of_algebraMap_eq' rfl
    letI : IsScalarTower A v.Completion w.1.Completion :=
      IsScalarTower.of_algebraMap_eq' rfl
    letI : IsFractionRing A v.Completion :=
      (Valuation.integer.integers
        (NormedField.valuation (K := v.Completion))).isFractionRing
    letI : IsIntegralClosure B A w.1.Completion :=
      completion_integer_closure v w.1 w.2
        (Algebra.IsAlgebraic.of_finite v.Completion w.1.Completion)
    letI : MulSemiringAction Gal(w.1.Completion/v.Completion) B :=
      IsIntegralClosure.MulSemiringAction
        A v.Completion w.1.Completion B
    ∀ sigma : absoluteValueDecomposition v w.1,
      (sigma.1 ∈ Q.asIdeal.inertia Gal(L/K)) ↔
        decompositionCompletionExtension v w.1 sigma ∈
          (IsLocalRing.maximalIdeal B).inertia
            Gal(w.1.Completion/v.Completion) := by
  dsimp only
  let hw := absolute_extension_nontrivial v w
  let hwna := absolute_extension_nonarchimedean v w
  let Q := nonarchimedeanHeightSpectrum w.1 hw hwna
  letI : Fact w.1.IsNontrivial := ⟨hw⟩
  letI : IsUltrametricDist w.1.Completion :=
    absoluteUltrametricDist w.1 hwna
  letI : Fact (AbsoluteValue.LiesOver w.1 v) := ⟨w.2⟩
  letI : Algebra v.Completion w.1.Completion :=
    (completionLies v w.1 w.2).toAlgebra
  letI : FiniteDimensional v.Completion w.1.Completion :=
    placeCompletionDimensional v w
  letI : IsGalois v.Completion w.1.Completion :=
    placeCompletionGalois v w
  let A := completionIntegerRing v
  let B := completionIntegerRing w.1
  letI : Algebra A v.Completion := A.subtype.toAlgebra
  letI : Algebra A B := completionIntegerLies v w.1 w.2
  letI : Algebra B w.1.Completion := B.subtype.toAlgebra
  letI : Algebra A w.1.Completion :=
    ((completionLies v w.1 w.2).comp A.subtype).toAlgebra
  letI : IsScalarTower A B w.1.Completion :=
    IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower A v.Completion w.1.Completion :=
    IsScalarTower.of_algebraMap_eq' rfl
  letI : IsFractionRing A v.Completion :=
    (Valuation.integer.integers
      (NormedField.valuation (K := v.Completion))).isFractionRing
  letI : IsIntegralClosure B A w.1.Completion :=
    completion_integer_closure v w.1 w.2
      (Algebra.IsAlgebraic.of_finite v.Completion w.1.Completion)
  letI : MulSemiringAction Gal(w.1.Completion/v.Completion) B :=
    IsIntegralClosure.MulSemiringAction
      A v.Completion w.1.Completion B
  let e := decompositionCompletionExtension v w.1
  let g : NumberField.RingOfIntegers L →+* B :=
    integersCenteredInteger w.1 hw hwna
  have hsmul (sigma : absoluteValueDecomposition v w.1)
      (x : NumberField.RingOfIntegers L) :
      e sigma • g x = g (sigma • x) := by
    apply Subtype.ext
    calc
      ((e sigma • g x : B) : w.1.Completion) =
          e sigma ((g x : B) : w.1.Completion) :=
        algebraMap.coe_smul' (B := B) (C := w.1.Completion)
          (e sigma) (g x)
      _ = e sigma (completionEmbedding w.1 (x : L)) := by
        rw [integers_centered_coe]
      _ = completionEmbedding w.1 ((sigma.1 • x :
          NumberField.RingOfIntegers L) : L) := by
        rw [show e sigma = decompositionCompletionEquiv v w.1 sigma from rfl,
          decomposition_alg_embedding]
        have hglobal :
            ((sigma.1 • x : NumberField.RingOfIntegers L) : L) =
              sigma.1 (x : L) :=
          algebraMap_galRestrict_apply
            (A := NumberField.RingOfIntegers K) (K := K) (L := L)
            (B := NumberField.RingOfIntegers L) sigma.1 x
        exact congrArg (completionEmbedding w.1) hglobal.symm
      _ = ((g (sigma • x) : B) : w.1.Completion) := by
        exact (integers_centered_coe
          w.1 hw hwna (sigma • x)).symm
  have hstable (tau : Gal(w.1.Completion/v.Completion)) (z : B)
      (hz : z ∈ IsLocalRing.maximalIdeal B) :
      tau • z ∈ IsLocalRing.maximalIdeal B := by
    let etau : B ≃+* B := MulSemiringAction.toRingAut _ _ tau
    have hmap : (IsLocalRing.maximalIdeal B).map etau =
        IsLocalRing.maximalIdeal B :=
      IsLocalRing.map_ringEquiv_maximalIdeal etau
    rw [← hmap]
    exact Ideal.mem_map_of_mem etau hz
  intro sigma
  change (sigma ∈ Q.asIdeal.inertia
      (absoluteValueDecomposition v w.1)) ↔ _
  exact inertia_quotient_equiv
    Q.asIdeal (IsLocalRing.maximalIdeal B) e g hsmul hstable
    (centeredCompletionResidue w.1 hw hwna)
    (centered_residue_mk w.1 hw hwna) sigma

set_option maxHeartbeats 4000000 in
-- Elaboration and instance synthesis each need an explicit local budget.
set_option synthInstance.maxHeartbeats 1000000 in
-- Completion and integral-closure instance synthesis has a large telescope.
/-- Under the decomposition-group equivalence, a global arithmetic
Frobenius acts on the residue field of the completed valuation ring by the
global residue-cardinality power. -/
theorem decomposition_arith_frob
    {K L : Type u} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (v : AbsoluteValue K ℝ) [Fact v.IsNontrivial]
    [IsUltrametricDist v.Completion]
    (w : Towers.CField.ICohomo.CompletionPlacesAbove
      (L := L) v)
    [Finite (Towers.CField.ICohomo.CompletionPlacesAbove
      (L := L) v)]
    [Nonempty (Towers.CField.ICohomo.CompletionPlacesAbove
      (L := L) v)]
    [MulAction.IsPretransitive Gal(L/K)
      (Towers.CField.ICohomo.CompletionPlacesAbove
        (L := L) v)] :
    let hw := absolute_extension_nontrivial v w
    let hwna := absolute_extension_nonarchimedean v w
    let Q := nonarchimedeanHeightSpectrum w.1 hw hwna
    letI : Fact w.1.IsNontrivial := ⟨hw⟩
    letI : IsUltrametricDist w.1.Completion :=
      absoluteUltrametricDist w.1 hwna
    letI : Fact (AbsoluteValue.LiesOver w.1 v) := ⟨w.2⟩
    letI : Algebra v.Completion w.1.Completion :=
      (completionLies v w.1 w.2).toAlgebra
    letI : FiniteDimensional v.Completion w.1.Completion :=
      placeCompletionDimensional v w
    letI : IsGalois v.Completion w.1.Completion :=
      placeCompletionGalois v w
    let A := completionIntegerRing v
    let B := completionIntegerRing w.1
    letI : Algebra A v.Completion := A.subtype.toAlgebra
    letI : Algebra A B := completionIntegerLies v w.1 w.2
    letI : Algebra B w.1.Completion := B.subtype.toAlgebra
    letI : Algebra A w.1.Completion :=
      ((completionLies v w.1 w.2).comp A.subtype).toAlgebra
    letI : IsScalarTower A B w.1.Completion :=
      IsScalarTower.of_algebraMap_eq' rfl
    letI : IsScalarTower A v.Completion w.1.Completion :=
      IsScalarTower.of_algebraMap_eq' rfl
    letI : IsFractionRing A v.Completion :=
      (Valuation.integer.integers
        (NormedField.valuation (K := v.Completion))).isFractionRing
    letI : IsIntegralClosure B A w.1.Completion :=
      completion_integer_closure v w.1 w.2
        (Algebra.IsAlgebraic.of_finite v.Completion w.1.Completion)
    letI : MulSemiringAction Gal(w.1.Completion/v.Completion) B :=
      IsIntegralClosure.MulSemiringAction
        A v.Completion w.1.Completion B
    ∀ sigma : absoluteValueDecomposition v w.1,
      IsArithFrobAt (NumberField.RingOfIntegers K) sigma.1 Q.asIdeal →
      ∀ y : B,
        IsLocalRing.residue B
            (decompositionCompletionExtension v w.1 sigma • y) =
          (IsLocalRing.residue B y) ^
            Nat.card (NumberField.RingOfIntegers K ⧸
              Q.asIdeal.under (NumberField.RingOfIntegers K)) := by
  dsimp only
  let hw := absolute_extension_nontrivial v w
  let hwna := absolute_extension_nonarchimedean v w
  let Q := nonarchimedeanHeightSpectrum w.1 hw hwna
  letI : Fact w.1.IsNontrivial := ⟨hw⟩
  letI : IsUltrametricDist w.1.Completion :=
    absoluteUltrametricDist w.1 hwna
  letI : Fact (AbsoluteValue.LiesOver w.1 v) := ⟨w.2⟩
  letI : Algebra v.Completion w.1.Completion :=
    (completionLies v w.1 w.2).toAlgebra
  letI : FiniteDimensional v.Completion w.1.Completion :=
    placeCompletionDimensional v w
  letI : IsGalois v.Completion w.1.Completion :=
    placeCompletionGalois v w
  let A := completionIntegerRing v
  let B := completionIntegerRing w.1
  letI : Algebra A v.Completion := A.subtype.toAlgebra
  letI : Algebra A B := completionIntegerLies v w.1 w.2
  letI : Algebra B w.1.Completion := B.subtype.toAlgebra
  letI : Algebra A w.1.Completion :=
    ((completionLies v w.1 w.2).comp A.subtype).toAlgebra
  letI : IsScalarTower A B w.1.Completion :=
    IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower A v.Completion w.1.Completion :=
    IsScalarTower.of_algebraMap_eq' rfl
  letI : IsFractionRing A v.Completion :=
    (Valuation.integer.integers
      (NormedField.valuation (K := v.Completion))).isFractionRing
  letI : IsIntegralClosure B A w.1.Completion :=
    completion_integer_closure v w.1 w.2
      (Algebra.IsAlgebraic.of_finite v.Completion w.1.Completion)
  letI : MulSemiringAction Gal(w.1.Completion/v.Completion) B :=
    IsIntegralClosure.MulSemiringAction
      A v.Completion w.1.Completion B
  let e := decompositionCompletionExtension v w.1
  let g : NumberField.RingOfIntegers L →+* B :=
    integersCenteredInteger w.1 hw hwna
  have hsmul (sigma : absoluteValueDecomposition v w.1)
      (x : NumberField.RingOfIntegers L) :
      e sigma • g x = g (sigma • x) := by
    apply Subtype.ext
    calc
      ((e sigma • g x : B) : w.1.Completion) =
          e sigma ((g x : B) : w.1.Completion) :=
        algebraMap.coe_smul' (B := B) (C := w.1.Completion)
          (e sigma) (g x)
      _ = e sigma (completionEmbedding w.1 (x : L)) := by
        rw [integers_centered_coe]
      _ = completionEmbedding w.1 ((sigma.1 • x :
          NumberField.RingOfIntegers L) : L) := by
        rw [show e sigma = decompositionCompletionEquiv v w.1 sigma from rfl,
          decomposition_alg_embedding]
        have hglobal :
            ((sigma.1 • x : NumberField.RingOfIntegers L) : L) =
              sigma.1 (x : L) :=
          algebraMap.coe_smul' (B := NumberField.RingOfIntegers L)
            (C := L) sigma.1 x
        exact congrArg (completionEmbedding w.1) hglobal.symm
      _ = ((g (sigma • x) : B) : w.1.Completion) := by
        exact (integers_centered_coe
          w.1 hw hwna (sigma • x)).symm
  have hstable (tau : Gal(w.1.Completion/v.Completion)) (y : B)
      (hy : y ∈ IsLocalRing.maximalIdeal B) :
      tau • y ∈ IsLocalRing.maximalIdeal B := by
    let etau : B ≃+* B := MulSemiringAction.toRingAut _ _ tau
    have hmap : (IsLocalRing.maximalIdeal B).map etau =
        IsLocalRing.maximalIdeal B :=
      IsLocalRing.map_ringEquiv_maximalIdeal etau
    rw [← hmap]
    exact Ideal.mem_map_of_mem etau hy
  intro sigma hsigma y
  change Ideal.Quotient.mk (IsLocalRing.maximalIdeal B) (e sigma • y) = _
  have hsigma' :
      IsArithFrobAt (NumberField.RingOfIntegers K) sigma Q.asIdeal := by
    change IsArithFrobAt (NumberField.RingOfIntegers K) sigma.1 Q.asIdeal
    exact hsigma
  exact action_arith_frob
    (R := NumberField.RingOfIntegers K)
    Q.asIdeal (IsLocalRing.maximalIdeal B) e g hsmul hstable
    (centeredCompletionResidue w.1 hw hwna)
    (centered_residue_mk w.1 hw hwna) sigma hsigma' y

/-- A primitive `n`th root of unity gives the standard multiplicative
character from `ZMod n` into the units of the field. -/
noncomputable def zmodPrimitiveRoot
    {K : Type u} [Field K] {n : ℕ}
    (zeta : K) (hzeta : IsPrimitiveRoot zeta n) (hn : n ≠ 0) :
    Multiplicative (ZMod n) →* Kˣ := by
  let zetaUnit : Kˣ := Units.mk0 zeta (hzeta.ne_zero hn)
  let integerPowers : ℤ →+ Additive Kˣ :=
    { toFun := fun m => m • Additive.ofMul zetaUnit
      map_zero' := zero_zsmul _
      map_add' := fun a b => add_zsmul (Additive.ofMul zetaUnit) a b }
  have hperiod : integerPowers (n : ℤ) = 0 := by
    apply Additive.toMul.injective
    change zetaUnit ^ n = 1
    apply Units.ext
    exact hzeta.pow_eq_one
  exact (MulEquiv.multiplicativeAdditive Kˣ).toMonoidHom.comp
    (AddMonoidHom.toMultiplicative (ZMod.lift n ⟨integerPowers, hperiod⟩))

/-- Embed an abstract cyclic cubic group as the cube roots of unity in an
extension field. -/
noncomputable def cubicGroupUnits
    {C : Type v} [Group C]
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    (e : C ≃* Multiplicative (ZMod 3))
    (zeta : K) (hzeta : IsPrimitiveRoot zeta 3) :
    C →* Lˣ :=
  (Units.map (algebraMap K L)).comp
    ((zmodPrimitiveRoot zeta hzeta (by norm_num)).comp e.toMonoidHom)

/-- The faithful version of the cubic coefficient embedding, built through
the explicit equivalence between `ZMod 3` and the powers of a primitive cube
root.  This presentation exposes injectivity directly. -/
noncomputable def cubicUnitsFaithful
    {C : Type v} [Group C]
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    (e : C ≃* Multiplicative (ZMod 3))
    (zeta : K) (hzeta : IsPrimitiveRoot zeta 3) :
    C →* Lˣ := by
  let zetaUnit : Kˣ := (hzeta.isUnit (by norm_num)).unit
  let hzetaUnit : IsPrimitiveRoot zetaUnit 3 :=
    hzeta.isUnit_unit (by norm_num)
  let eZeta : Multiplicative (ZMod 3) ≃* Subgroup.zpowers zetaUnit :=
    hzetaUnit.zmodEquivZPowers.toMultiplicativeLeft
  exact (Units.map (algebraMap K L)).comp
    ((Subgroup.zpowers zetaUnit).subtype.comp
      (eZeta.toMonoidHom.comp e.toMonoidHom))

theorem cubic_faithful_injective
    {C : Type v} [Group C]
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    (e : C ≃* Multiplicative (ZMod 3))
    (zeta : K) (hzeta : IsPrimitiveRoot zeta 3) :
    Function.Injective
      (cubicUnitsFaithful (K := K) (L := L) e zeta hzeta) := by
  let zetaUnit : Kˣ := (hzeta.isUnit (by norm_num)).unit
  let hzetaUnit : IsPrimitiveRoot zetaUnit 3 :=
    hzeta.isUnit_unit (by norm_num)
  change Function.Injective
    ((Units.map (algebraMap K L).toMonoidHom).comp
      ((Subgroup.zpowers zetaUnit).subtype.comp
        (hzetaUnit.zmodEquivZPowers.toMultiplicativeLeft.toMonoidHom.comp
          e.toMonoidHom)))
  exact (Units.map_injective (algebraMap K L).injective).comp
    (Subtype.val_injective.comp
      (hzetaUnit.zmodEquivZPowers.toMultiplicativeLeft.injective.comp e.injective))

/-- The faithful cubic coefficient embedding is still defined over the base
field, hence fixed by every relative Galois automorphism. -/
theorem cubic_faithful_fixed
    {C : Type v} [Group C]
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    (e : C ≃* Multiplicative (ZMod 3))
    (zeta : K) (hzeta : IsPrimitiveRoot zeta 3)
    (sigma : Gal(L/K)) (c : C) :
    Units.map sigma.toRingEquiv.toMonoidHom
        (cubicUnitsFaithful e zeta hzeta c) =
      cubicUnitsFaithful e zeta hzeta c := by
  apply Units.ext
  simp [cubicUnitsFaithful]

/-- The cubic kernel embedded through the base field is fixed by every
relative Galois automorphism. -/
theorem cubic_units_fixed
    {C : Type v} [Group C]
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    (e : C ≃* Multiplicative (ZMod 3))
    (zeta : K) (hzeta : IsPrimitiveRoot zeta 3)
    (sigma : Gal(L/K)) (c : C) :
    Units.map sigma.toRingEquiv.toMonoidHom (cubicGroupUnits e zeta hzeta c) =
      cubicGroupUnits e zeta hzeta c := by
  apply Units.ext
  simp [cubicGroupUnits]

/-- Restriction gives the expected Galois-group equivalence for a linearly
disjoint compositum inside a common ambient field. -/
noncomputable def galoisCompositumEquiv
    {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω]
    (L K : IntermediateField k Ω)
    [Normal k L] [FiniteDimensional k L]
    [FiniteDimensional K Ω] [IsGalois K Ω]
    (hsup : L ⊔ K = ⊤) (hinf : L ⊓ K = ⊥) :
    Gal(Ω/K) ≃* Gal(L/k) :=
  MulEquiv.ofBijective
    (IntermediateField.restrictRestrictAlgEquivMapHom k L K Ω)
    ⟨IntermediateField.restrictRestrictAlgEquivMapHom_injective L K hsup,
      IntermediateField.restrictRestrictAlgEquivMapHom_surjective L K hinf⟩

/-- Abstract Brauer-theoretic inflation is the usual operation of restricting
the Galois arguments and including the coefficient field. -/
theorem inflation_coefficients_restriction
    (K : Type u) [Field K]
    {F M : FiniteGaloisIntermediateField K (SeparableClosure K)}
    (hFM : F ≤ M)
    (x : MHTwo Gal(F/K) Fˣ) :
    letI : MulDistribMulAction Gal(M/K) Fˣ :=
      (inferInstance : MulDistribMulAction Gal(F/K) Fˣ).compHom Fˣ
        (galoisRestrictionHom K hFM)
    Towers.CField.CProduca.inflationHom K hFM x =
      MHTwo.mapCoefficientsHom
        (coefficientUnitsHom K hFM)
        (fun sigma z => coefficient_units_hom K hFM sigma z)
        (MHTwo.restrictionHom
          (galoisRestrictionHom K hFM)
          (fun _ _ => rfl) x) := by
  letI : MulDistribMulAction Gal(M/K) Fˣ :=
    (inferInstance : MulDistribMulAction Gal(F/K) Fˣ).compHom Fˣ
      (galoisRestrictionHom K hFM)
  induction x using Quotient.inductionOn with
  | _ c =>
      letI : Fact (F ≤ M) := ⟨hFM⟩
      have hinfl :=
        inflation_concrete_cocycle
          (K := K) (E := M) c
      rw [show Fact.out = hFM from Subsingleton.elim _ _] at hinfl
      exact hinfl.trans rfl

set_option synthInstance.maxHeartbeats 100000 in
-- Direct-limit typeclass synthesis unfolds the dependent inflation system.
/-- A finite-level Galois `H²` class with trivial absolute Brauer class
becomes trivial after inflation to a finite Galois overfield. -/
theorem h_inflates_brauer
    (K : Type u) [Field K]
    (L : FiniteGaloisIntermediateField K (SeparableClosure K))
    (x : MHTwo Gal(L/K) Lˣ)
    (hx : Towers.CField.CProduca.finiteHBrauer K L x = 1) :
    ∃ E : FiniteGaloisIntermediateField K (SeparableClosure K),
      ∃ hLE : L ≤ E,
        Towers.CField.CProduca.inflationHom K hLE x = 1 := by
  open Towers.CField.CProduca in
  have habsolute : absoluteMultiplicative2 K L x = 1 := by
    apply absolute_brauer_injective K
    rw [absolute_brauer_multiplicative, hx, map_one]
  let y : Σ F,
      Towers.CField.CProduca.multiplicativeHFamily K F :=
    ⟨L, x⟩
  change (⟦y⟧ :
      Towers.CField.CProduca.absoluteMultiplicativeH K) = 1
    at habsolute
  rcases (DirectLimit.exists_eq_one y).mp habsolute with
    ⟨E, hLE, hE⟩
  exact ⟨E, hLE, hE⟩

/-- The central-extension class, restricted along a Galois-group
identification and mapped into the multiplicative group of the coefficient
field. -/
noncomputable def centralExtensionClass
    {E : Type v} {G : Type w} [Group E] [Group G]
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (q : E →* G) (hq : Function.Surjective q)
    (hcentral : q.ker ≤ Subgroup.center E)
    (galoisEquiv : Gal(L/K) ≃* G)
    (kernelToUnits : q.ker →* Lˣ)
    (hfixed : ∀ sigma : Gal(L/K), ∀ z : q.ker,
      sigma • kernelToUnits z = kernelToUnits z) :
    MHTwo Gal(L/K) Lˣ := by
  letI : CommGroup q.ker :=
    centralExtensionComm q hcentral
  letI : MulDistribMulAction G q.ker :=
    trivialDistribAction G q.ker
  letI : MulDistribMulAction Gal(L/K) q.ker :=
    trivialDistribAction Gal(L/K) q.ker
  let restricted : MHTwo Gal(L/K) q.ker :=
    MHTwo.restrictionHom galoisEquiv.toMonoidHom
      (fun _ _ => rfl)
      (extensionObstructionClass q hq hcentral)
  exact MHTwo.mapCoefficientsHom kernelToUnits
    (fun sigma z => (hfixed sigma z).symm) restricted

set_option synthInstance.maxHeartbeats 200000 in
-- Extra heartbeats are needed for the typeclass search in this proof.
set_option maxHeartbeats 800000 in
/-- A weak solution over a finite Galois overfield kills the inflation of the
coefficient-field-valued obstruction class. -/
theorem central_inflation_lift
    {Q : Type v} {G : Type w} [Group Q] [Group G]
    (K : Type u) [Field K]
    {F M : FiniteGaloisIntermediateField K (SeparableClosure K)}
    (hFM : F ≤ M)
    (q : Q →* G) (hq : Function.Surjective q)
    (hcentral : q.ker ≤ Subgroup.center Q)
    (galoisEquiv : Gal(F/K) ≃* G)
    (kernelToUnits : q.ker →* Fˣ)
    (hfixed : ∀ sigma : Gal(F/K), ∀ z : q.ker,
      Units.map sigma (kernelToUnits z) = kernelToUnits z)
    (lift : Gal(M/K) →* Q)
    (hlift : q.comp lift =
      galoisEquiv.toMonoidHom.comp (galoisRestrictionHom K hFM)) :
    Towers.CField.CProduca.inflationHom K hFM
        (centralExtensionClass q hq hcentral galoisEquiv
          kernelToUnits (fun sigma z => hfixed sigma z)) = 1 := by
  letI : CommGroup q.ker :=
    centralExtensionComm q hcentral
  letI : MulDistribMulAction G q.ker :=
    trivialDistribAction G q.ker
  letI : MulDistribMulAction Gal(F/K) q.ker :=
    trivialDistribAction Gal(F/K) q.ker
  letI : MulDistribMulAction Gal(M/K) q.ker :=
    trivialDistribAction Gal(M/K) q.ker
  letI : MulDistribMulAction Gal(M/K) Fˣ :=
    (inferInstance : MulDistribMulAction Gal(F/K) Fˣ).compHom Fˣ
      (galoisRestrictionHom K hFM)
  let obstruction : MHTwo G q.ker :=
    extensionObstructionClass q hq hcentral
  have hobstruction :
      MHTwo.restrictionHom
          (galoisEquiv.toMonoidHom.comp
            (galoisRestrictionHom K hFM))
          (fun _ _ => rfl) obstruction = 1 := by
    exact obstruction_restrict_lift
      q hq hcentral
      (galoisEquiv.toMonoidHom.comp (galoisRestrictionHom K hFM))
      lift hlift
  rw [inflation_coefficients_restriction]
  change
    MHTwo.mapCoefficientsHom
        (coefficientUnitsHom K hFM)
        _
        (MHTwo.restrictionHom
          (galoisRestrictionHom K hFM) _
          (MHTwo.mapCoefficientsHom kernelToUnits _
            (MHTwo.restrictionHom
              galoisEquiv.toMonoidHom _ obstruction))) = 1
  rw [MHTwo.restriction_hom_coefficients
    (r := galoisRestrictionHom K hFM)
    (hM := fun _ _ => rfl)
    (hN := fun _ _ => rfl)
    (f := kernelToUnits)
    (fG := fun sigma z => (hfixed sigma z).symm)
    (fH := fun sigma z =>
      (hfixed (galoisRestrictionHom K hFM sigma) z).symm)]
  rw [MHTwo.restrictionHom_comp
    (f := galoisEquiv.toMonoidHom)
    (g := galoisRestrictionHom K hFM)
    (hf := fun _ _ => rfl)
    (hg := fun _ _ => rfl)
    (hfg := fun _ _ => rfl)]
  rw [hobstruction]
  simp

set_option synthInstance.maxHeartbeats 200000 in
-- Extra heartbeats are needed for the typeclass search in this proof.
set_option maxHeartbeats 800000 in
/-- A finite Galois weak solution makes the corresponding central-extension
class trivial in the Brauer group of the base field.  This is inflation
compatibility for the finite-level crossed-product class. -/
theorem central_brauer_lift
    {Q : Type v} {G : Type w} [Group Q] [Group G]
    (K : Type u) [Field K]
    {F M : FiniteGaloisIntermediateField K (SeparableClosure K)}
    (hFM : F ≤ M)
    (q : Q →* G) (hq : Function.Surjective q)
    (hcentral : q.ker ≤ Subgroup.center Q)
    (galoisEquiv : Gal(F/K) ≃* G)
    (kernelToUnits : q.ker →* Fˣ)
    (hfixed : ∀ sigma : Gal(F/K), ∀ z : q.ker,
      Units.map sigma (kernelToUnits z) = kernelToUnits z)
    (lift : Gal(M/K) →* Q)
    (hlift : q.comp lift =
      galoisEquiv.toMonoidHom.comp (galoisRestrictionHom K hFM)) :
    Towers.CField.CProduca.finiteHBrauer K F
        (centralExtensionClass q hq hcentral galoisEquiv
          kernelToUnits (fun sigma z => hfixed sigma z)) = 1 := by
  let c := centralExtensionClass q hq hcentral galoisEquiv
    kernelToUnits (fun sigma z => hfixed sigma z)
  rw [← Towers.CField.CProduca.h_2_inflation
    K hFM c]
  rw [central_inflation_lift
    K hFM q hq hcentral galoisEquiv kernelToUnits hfixed lift hlift]
  exact map_one _

/-- The relative Brauer class attached to a central extension after the
central kernel has been embedded equivariantly into the coefficient field. -/
noncomputable def extensionRelativeBrauer
    {E : Type v} {G : Type w} [Group E] [Group G]
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (q : E →* G) (hq : Function.Surjective q)
    (hcentral : q.ker ≤ Subgroup.center E)
    (galoisEquiv : Gal(L/K) ≃* G)
    (kernelToUnits : q.ker →* Lˣ)
    (hfixed : ∀ sigma : Gal(L/K), ∀ z : q.ker,
      sigma • kernelToUnits z = kernelToUnits z) :
    relativeBrauerGroup K L :=
  CProduc.hRelativeBrauer K L
    (centralExtensionClass q hq hcentral galoisEquiv
      kernelToUnits hfixed)

/-- The relative Brauer obstruction vanishes exactly when the corresponding
`Lˣ`-valued Galois cohomology class vanishes. -/
theorem extension_relative_brauer
    {E : Type v} {G : Type w} [Group E] [Group G]
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (q : E →* G) (hq : Function.Surjective q)
    (hcentral : q.ker ≤ Subgroup.center E)
    (galoisEquiv : Gal(L/K) ≃* G)
    (kernelToUnits : q.ker →* Lˣ)
    (hfixed : ∀ sigma : Gal(L/K), ∀ z : q.ker,
      sigma • kernelToUnits z = kernelToUnits z) :
    extensionRelativeBrauer q hq hcentral galoisEquiv
        kernelToUnits hfixed = 1 ↔
      centralExtensionClass q hq hcentral galoisEquiv
        kernelToUnits hfixed = 1 := by
  let e := CProduc.hRelativeBrauer K L
  constructor
  · intro h
    apply e.injective
    change e (centralExtensionClass q hq hcentral galoisEquiv
      kernelToUnits hfixed) = e 1
    exact h.trans (map_one e).symm
  · intro h
    change e (centralExtensionClass q hq hcentral galoisEquiv
      kernelToUnits hfixed) = 1
    exact (congrArg e h).trans (map_one e)

/-- A trivial coefficient-field-valued obstruction supplies the cochain and
Kummer radical used to construct a weak solution.  The cube of the
trivializing cochain is a one-cocycle because the original factor set has
cubic values; Hilbert 90 then writes it as `sigma(a) / a`. -/
theorem central_kummer_data
    {Q : Type v} {G : Type w} [Group Q] [Group G]
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (q : Q →* G) (hq : Function.Surjective q)
    (hcentral : q.ker ≤ Subgroup.center Q)
    (galoisEquiv : Gal(L/K) ≃* G)
    (kernelToUnits : q.ker →* Lˣ)
    (hfixed : ∀ sigma : Gal(L/K), ∀ z : q.ker,
      sigma • kernelToUnits z = kernelToUnits z)
    (hkernel : ∀ z : q.ker, z ^ 3 = 1)
    (hzero : centralExtensionClass q hq hcentral galoisEquiv
      kernelToUnits hfixed = 1) :
    ∃ b : Gal(L/K) → Lˣ,
      (∀ sigma tau : Gal(L/K),
        sigma • b tau / b (sigma * tau) * b sigma =
          kernelToUnits
            ((centralExtensionSet q hq hcentral)
              (galoisEquiv sigma, galoisEquiv tau))) ∧
      ∃ a : Lˣ, ∀ sigma : Gal(L/K),
        sigma • a / a = b sigma ^ 3 := by
  letI : CommGroup q.ker :=
    centralExtensionComm q hcentral
  letI : MulDistribMulAction G q.ker :=
    trivialDistribAction G q.ker
  letI : MulDistribMulAction Gal(L/K) q.ker :=
    trivialDistribAction Gal(L/K) q.ker
  let cG := centralExtensionSet q hq hcentral
  let cR : NMCocycl₂ (G := Gal(L/K)) (M := q.ker) :=
    NMCocycl₂.restrict galoisEquiv.toMonoidHom
      (fun _ _ => rfl) (cG.normalizedMulCocycle (fun _ _ => rfl))
  let cL : NMCocycl₂ (G := Gal(L/K)) (M := Lˣ) :=
    NMCocycl₂.mapCoefficients kernelToUnits
      (fun sigma z => (hfixed sigma z).symm) cR
  have hcLclass : MHTwo.mk cL = 1 := by
    change MHTwo.mk
      (NMCocycl₂.mapCoefficients kernelToUnits
        (fun sigma z => (hfixed sigma z).symm)
        (NMCocycl₂.restrict galoisEquiv.toMonoidHom
          (fun _ _ => rfl)
          ((centralExtensionSet q hq hcentral).normalizedMulCocycle
            (fun _ _ => rfl)))) = 1 at hzero
    exact hzero
  have hcoh : MHTwo.IsCohomologous cL 1 :=
    (MHTwo.mk_eq_iff cL 1).1 (by simpa using hcLclass)
  obtain ⟨b, hb⟩ := hcoh
  have hb' : ∀ sigma tau : Gal(L/K),
      sigma • b tau / b (sigma * tau) * b sigma = cL (sigma, tau) := by
    intro sigma tau
    simpa [MHTwo.IsCohomologous] using hb sigma tau
  have hcubic : ∀ sigma tau : Gal(L/K), cL (sigma, tau) ^ 3 = 1 := by
    intro sigma tau
    change (kernelToUnits (cG (galoisEquiv sigma, galoisEquiv tau))) ^ 3 = 1
    rw [← map_pow, hkernel, map_one]
  have hbCocycle : groupCohomology.IsMulCocycle₁ (fun sigma => b sigma ^ 3) :=
    groupCohomology.isMulCocycle₁_pow_of_coboundary_eq_torsion
      3 cL b hb' hcubic
  obtain ⟨a, ha⟩ :=
    groupCohomology.isMulCoboundary₁_of_isMulCocycle₁_of_aut_to_units
      (fun sigma => b sigma ^ 3) hbCocycle
  refine ⟨b, ?_, a, ha⟩
  intro sigma tau
  simpa [cL, cR, cG] using hb' sigma tau

/-- Restrict a global cocycle to the decomposition group at a finite place
and transport it to the corresponding extension of completions. -/
noncomputable def restrictedGaloisCocycle
    {K L : Type u} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (v : AbsoluteValue K ℝ) [Fact v.IsNontrivial]
    [IsUltrametricDist v.Completion] (hvna : IsNonarchimedean v)
    (w : Towers.CField.ICohomo.CompletionPlacesAbove
      (L := L) v)
    [Finite (Towers.CField.ICohomo.CompletionPlacesAbove
      (L := L) v)]
    [Nonempty (Towers.CField.ICohomo.CompletionPlacesAbove
      (L := L) v)]
    [MulAction.IsPretransitive Gal(L/K)
      (Towers.CField.ICohomo.CompletionPlacesAbove
        (L := L) v)]
    (c : NMCocycl₂ (G := Gal(L/K)) (M := Lˣ)) :
    letI : Algebra v.Completion w.1.Completion :=
      (Towers.NumberTheory.Milne.completionLies
        v w.1 w.2).toAlgebra
    letI : FiniteDimensional v.Completion w.1.Completion :=
      Towers.NumberTheory.Milne.placeCompletionDimensional v w
    letI : IsGalois v.Completion w.1.Completion :=
      Towers.NumberTheory.Milne.placeCompletionGalois v w
    NMCocycl₂
      (G := Gal(w.1.Completion/v.Completion)) (M := w.1.Completionˣ) := by
  let D := Towers.NumberTheory.Milne.completionDecompositionField
    v hvna w
  let H := Towers.NumberTheory.Milne.completionDecompositionGroup
    v hvna w
  letI : NumberField D := NumberField.of_module_finite K D
  letI : IsGaloisGroup H D L :=
    IsGaloisGroup.subgroup Gal(L/K) K L H
  letI : FiniteDimensional D L := IsGaloisGroup.finiteDimensional H D L
  letI : IsGalois D L := IsGaloisGroup.isGalois H D L
  let W := Towers.CField.ICohomo.CompletionPlacesAbove
    (L := L) v
  letI : Finite W :=
    Towers.NumberTheory.Milne.absolute_extensions_separable v
  letI : Nonempty W :=
    Towers.NumberTheory.Milne.absolute_value_extension
      (K := K) (L := L) v
  letI : MulAction.IsPretransitive Gal(L/K) W :=
    Towers.NumberTheory.Milne.above_pretr_nonar
      v hvna
  letI : Algebra v.Completion w.1.Completion :=
    (Towers.NumberTheory.Milne.completionLies
      v w.1 w.2).toAlgebra
  letI : FiniteDimensional v.Completion w.1.Completion :=
    Towers.NumberTheory.Milne.placeCompletionDimensional v w
  letI : IsGalois v.Completion w.1.Completion :=
    Towers.NumberTheory.Milne.placeCompletionGalois v w
  let cD : NMCocycl₂ (G := Gal(L/D)) (M := Lˣ) :=
    NMCocycl₂.restrict (galoisTowerInclusion K D L)
      (fun _ _ => rfl) c
  let g :=
    Towers.NumberTheory.Milne.decompositionGaloisCompletion
      v hvna w
  exact transportedGaloisCocycle
    (Towers.NumberTheory.Milne.completionEmbedding w.1) g
    (fun sigma a =>
      (decomposition_galois_embedding
        v hvna w sigma a).symm)
    cD

/-- The local Galois group at a completion maps to the global quotient through
the decomposition group and the chosen global Galois identification. -/
noncomputable def completionDecomposition
    {G : Type w} [Group G]
    {K L : Type u} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (v : AbsoluteValue K ℝ) [Fact v.IsNontrivial]
    [IsUltrametricDist v.Completion] (hvna : IsNonarchimedean v)
    (w : Towers.CField.ICohomo.CompletionPlacesAbove
      (L := L) v)
    [Finite (Towers.CField.ICohomo.CompletionPlacesAbove
      (L := L) v)]
    [Nonempty (Towers.CField.ICohomo.CompletionPlacesAbove
      (L := L) v)]
    [MulAction.IsPretransitive Gal(L/K)
      (Towers.CField.ICohomo.CompletionPlacesAbove
        (L := L) v)]
    (galoisEquiv : Gal(L/K) ≃* G) :
    letI : Algebra v.Completion w.1.Completion :=
      (Towers.NumberTheory.Milne.completionLies
        v w.1 w.2).toAlgebra
    letI : FiniteDimensional v.Completion w.1.Completion :=
      Towers.NumberTheory.Milne.placeCompletionDimensional v w
    letI : IsGalois v.Completion w.1.Completion :=
      Towers.NumberTheory.Milne.placeCompletionGalois v w
    Gal(w.1.Completion/v.Completion) →* G := by
  let D := Towers.NumberTheory.Milne.completionDecompositionField
    v hvna w
  letI : Algebra v.Completion w.1.Completion :=
    (Towers.NumberTheory.Milne.completionLies
      v w.1 w.2).toAlgebra
  letI : FiniteDimensional v.Completion w.1.Completion :=
    Towers.NumberTheory.Milne.placeCompletionDimensional v w
  letI : IsGalois v.Completion w.1.Completion :=
    Towers.NumberTheory.Milne.placeCompletionGalois v w
  exact galoisEquiv.toMonoidHom.comp
    ((galoisTowerInclusion K D L).comp
      (Towers.NumberTheory.Milne.decompositionGaloisCompletion
        v hvna w).symm.toMonoidHom)

/-- Complete the coefficient embedding of a central kernel at a chosen place. -/
noncomputable def completionKernelUnits
    {C : Type v} [Group C]
    {K L : Type u} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (v : AbsoluteValue K ℝ)
    (w : Towers.CField.ICohomo.CompletionPlacesAbove
      (L := L) v)
    (kernelToUnits : C →* Lˣ) : C →* w.1.Completionˣ :=
  (Units.map
    (Towers.NumberTheory.Milne.completionEmbedding w.1)).comp
      kernelToUnits

set_option synthInstance.maxHeartbeats 200000 in
-- Extra heartbeats are needed for the typeclass search in this proof.
set_option maxHeartbeats 1000000 in
/-- A globally fixed kernel embedding remains fixed after passage to the
completion and transport from the decomposition group. -/
theorem completion_units_fixed
    {C : Type v} [Group C]
    {K L : Type u} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (v : AbsoluteValue K ℝ) [Fact v.IsNontrivial]
    [IsUltrametricDist v.Completion] (hvna : IsNonarchimedean v)
    (w : Towers.CField.ICohomo.CompletionPlacesAbove
      (L := L) v)
    [Finite (Towers.CField.ICohomo.CompletionPlacesAbove
      (L := L) v)]
    [Nonempty (Towers.CField.ICohomo.CompletionPlacesAbove
      (L := L) v)]
    [MulAction.IsPretransitive Gal(L/K)
      (Towers.CField.ICohomo.CompletionPlacesAbove
        (L := L) v)]
    (kernelToUnits : C →* Lˣ)
    (hfixed : ∀ sigma : Gal(L/K), ∀ z : C,
      sigma • kernelToUnits z = kernelToUnits z) :
    letI : Algebra v.Completion w.1.Completion :=
      (Towers.NumberTheory.Milne.completionLies
        v w.1 w.2).toAlgebra
    letI : FiniteDimensional v.Completion w.1.Completion :=
      Towers.NumberTheory.Milne.placeCompletionDimensional v w
    letI : IsGalois v.Completion w.1.Completion :=
      Towers.NumberTheory.Milne.placeCompletionGalois v w
    ∀ sigma : Gal(w.1.Completion/v.Completion), ∀ z : C,
      sigma • completionKernelUnits v w kernelToUnits z =
        completionKernelUnits v w kernelToUnits z := by
  let D := Towers.NumberTheory.Milne.completionDecompositionField
    v hvna w
  letI : Algebra v.Completion w.1.Completion :=
    (Towers.NumberTheory.Milne.completionLies
      v w.1 w.2).toAlgebra
  letI : FiniteDimensional v.Completion w.1.Completion :=
    Towers.NumberTheory.Milne.placeCompletionDimensional v w
  letI : IsGalois v.Completion w.1.Completion :=
    Towers.NumberTheory.Milne.placeCompletionGalois v w
  change ∀ sigma : Gal(w.1.Completion/v.Completion), ∀ z : C,
    sigma • completionKernelUnits v w kernelToUnits z =
      completionKernelUnits v w kernelToUnits z
  intro sigma z
  let g :=
    Towers.NumberTheory.Milne.decompositionGaloisCompletion
      v hvna w
  let tau : Gal(L/D) := g.symm sigma
  apply Units.ext
  change sigma
      (Towers.NumberTheory.Milne.completionEmbedding w.1
        (kernelToUnits z : L)) =
    Towers.NumberTheory.Milne.completionEmbedding w.1
      (kernelToUnits z : L)
  have hz := hfixed (galoisTowerInclusion K D L tau) z
  have hzval : tau (kernelToUnits z : L) = (kernelToUnits z : L) := by
    simpa using congrArg Units.val hz
  calc
    sigma (Towers.NumberTheory.Milne.completionEmbedding w.1
        (kernelToUnits z : L)) =
        g tau (Towers.NumberTheory.Milne.completionEmbedding w.1
          (kernelToUnits z : L)) := by rw [g.apply_symm_apply sigma]
    _ = Towers.NumberTheory.Milne.completionEmbedding w.1
          (tau (kernelToUnits z : L)) :=
      Towers.NumberTheory.Milne.decomposition_galois_embedding
        v hvna w tau (kernelToUnits z : L)
    _ = Towers.NumberTheory.Milne.completionEmbedding w.1
          (kernelToUnits z : L) := by rw [hzval]

set_option synthInstance.maxHeartbeats 1000000 in
-- Extra heartbeats are needed for the typeclass search in this proof.
set_option maxHeartbeats 4000000 in
/-- Completion transport of a central-extension cocycle is exactly the
coefficient image of the central obstruction restricted to the local
decomposition homomorphism. -/
theorem completion_restricted_class
    {Q : Type v} {G : Type w} [Group Q] [Group G]
    {K L : Type u} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (q : Q →* G) (hq : Function.Surjective q)
    (hcentral : q.ker ≤ Subgroup.center Q)
    (galoisEquiv : Gal(L/K) ≃* G)
    (kernelToUnits : q.ker →* Lˣ)
    (hfixed : ∀ sigma : Gal(L/K), ∀ z : q.ker,
      sigma • kernelToUnits z = kernelToUnits z)
    (v : AbsoluteValue K ℝ) [Fact v.IsNontrivial]
    [IsUltrametricDist v.Completion] (hvna : IsNonarchimedean v)
    (w : Towers.CField.ICohomo.CompletionPlacesAbove
      (L := L) v)
    [Finite (Towers.CField.ICohomo.CompletionPlacesAbove
      (L := L) v)]
    [Nonempty (Towers.CField.ICohomo.CompletionPlacesAbove
      (L := L) v)]
    [MulAction.IsPretransitive Gal(L/K)
      (Towers.CField.ICohomo.CompletionPlacesAbove
      (L := L) v)] :
    letI : Algebra v.Completion w.1.Completion :=
      (Towers.NumberTheory.Milne.completionLies
        v w.1 w.2).toAlgebra
    letI : FiniteDimensional v.Completion w.1.Completion :=
      Towers.NumberTheory.Milne.placeCompletionDimensional v w
    letI : IsGalois v.Completion w.1.Completion :=
      Towers.NumberTheory.Milne.placeCompletionGalois v w
    letI : CommGroup q.ker :=
      centralExtensionComm q hcentral
    letI : MulDistribMulAction G q.ker :=
      trivialDistribAction G q.ker
    letI : MulDistribMulAction Gal(L/K) q.ker :=
      trivialDistribAction Gal(L/K) q.ker
    letI : MulDistribMulAction Gal(w.1.Completion/v.Completion) q.ker :=
      trivialDistribAction Gal(w.1.Completion/v.Completion) q.ker
    let cGlobal := NMCocycl₂.mapCoefficients kernelToUnits
      (fun sigma z ↦ (hfixed sigma z).symm)
      (NMCocycl₂.restrict galoisEquiv.toMonoidHom
        (fun _ _ ↦ rfl)
        ((centralExtensionSet q hq hcentral).normalizedMulCocycle
          (fun _ _ ↦ rfl)))
    MHTwo.mk
        (restrictedGaloisCocycle v hvna w cGlobal) =
      MHTwo.mapCoefficientsHom
        (completionKernelUnits v w kernelToUnits)
        (fun sigma z ↦
          (completion_units_fixed
            v hvna w kernelToUnits hfixed sigma z).symm)
        (MHTwo.restrictionHom
          (completionDecomposition v hvna w galoisEquiv)
          (fun _ _ ↦ rfl)
          (extensionObstructionClass q hq hcentral)) := by
  let D := Towers.NumberTheory.Milne.completionDecompositionField
    v hvna w
  letI : Algebra v.Completion w.1.Completion :=
    (Towers.NumberTheory.Milne.completionLies
      v w.1 w.2).toAlgebra
  letI : FiniteDimensional v.Completion w.1.Completion :=
    Towers.NumberTheory.Milne.placeCompletionDimensional v w
  letI : IsGalois v.Completion w.1.Completion :=
    Towers.NumberTheory.Milne.placeCompletionGalois v w
  letI : CommGroup q.ker :=
    centralExtensionComm q hcentral
  letI : MulDistribMulAction G q.ker :=
    trivialDistribAction G q.ker
  letI : MulDistribMulAction Gal(L/K) q.ker :=
    trivialDistribAction Gal(L/K) q.ker
  letI : MulDistribMulAction Gal(w.1.Completion/v.Completion) q.ker :=
    trivialDistribAction Gal(w.1.Completion/v.Completion) q.ker
  let cGlobal := NMCocycl₂.mapCoefficients kernelToUnits
    (fun sigma z ↦ (hfixed sigma z).symm)
    (NMCocycl₂.restrict galoisEquiv.toMonoidHom
      (fun _ _ ↦ rfl)
      ((centralExtensionSet q hq hcentral).normalizedMulCocycle
        (fun _ _ ↦ rfl)))
  change MHTwo.mk
      (restrictedGaloisCocycle v hvna w cGlobal) =
    MHTwo.mapCoefficientsHom
      (completionKernelUnits v w kernelToUnits) _
      (MHTwo.restrictionHom
        (completionDecomposition v hvna w galoisEquiv) _
        (extensionObstructionClass q hq hcentral))
  apply congrArg MHTwo.mk
  apply NMCocycl₂.ext
  rintro ⟨sigma, tau⟩
  simp [restrictedGaloisCocycle,
    completionDecomposition, completionKernelUnits,
    cGlobal, transportedGaloisCocycle,
    ]

set_option synthInstance.maxHeartbeats 1000000 in
-- Extra heartbeats are needed for the typeclass search in this proof.
set_option maxHeartbeats 6000000 in
/-- At an arbitrary nonarchimedean place, localization of a global crossed
product is represented by the cocycle restricted to the decomposition group
and transported to the chosen extension of completions. -/
theorem base_change_crossed
    {K L : Type u} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (v : AbsoluteValue K ℝ) [Fact v.IsNontrivial]
    [IsUltrametricDist v.Completion] (hvna : IsNonarchimedean v)
    (w : Towers.CField.ICohomo.CompletionPlacesAbove
      (L := L) v)
    [Finite (Towers.CField.ICohomo.CompletionPlacesAbove
      (L := L) v)]
    [Nonempty (Towers.CField.ICohomo.CompletionPlacesAbove
      (L := L) v)]
    [MulAction.IsPretransitive Gal(L/K)
      (Towers.CField.ICohomo.CompletionPlacesAbove
        (L := L) v)]
    (c : NMCocycl₂ (G := Gal(L/K)) (M := Lˣ)) :
    letI : Algebra K v.Completion :=
      Towers.NumberTheory.Milne.completionBaseAlgebra v
    letI : Algebra v.Completion w.1.Completion :=
      (Towers.NumberTheory.Milne.completionLies
        v w.1 w.2).toAlgebra
    letI : FiniteDimensional v.Completion w.1.Completion :=
      Towers.NumberTheory.Milne.placeCompletionDimensional v w
    letI : IsGalois v.Completion w.1.Completion :=
      Towers.NumberTheory.Milne.placeCompletionGalois v w
    brauerBaseChange K v.Completion (CProduc.brauerClass K L c) =
      CProduc.brauerClass v.Completion w.1.Completion
        (restrictedGaloisCocycle v hvna w c) := by
  open Towers.NumberTheory.Milne in
    let D := completionDecompositionField v hvna w
    let H := completionDecompositionGroup v hvna w
    letI : NumberField D := NumberField.of_module_finite K D
    letI : IsGaloisGroup H D L :=
      IsGaloisGroup.subgroup Gal(L/K) K L H
    letI : FiniteDimensional D L := IsGaloisGroup.finiteDimensional H D L
    letI : IsGalois D L := IsGaloisGroup.isGalois H D L
    letI : Algebra K v.Completion := completionBaseAlgebra v
    letI : SMul K v.Completion := (completionBaseAlgebra v).toSMul
    letI : Module K v.Completion := Algebra.toModule
    letI : Algebra D v.Completion :=
      (decompositionEmbeddingCompletion v hvna w).toAlgebra
    letI : SMul D v.Completion :=
      (decompositionEmbeddingCompletion v hvna w).toAlgebra.toSMul
    letI : Module D v.Completion := Algebra.toModule
    letI : IsScalarTower K D v.Completion := by
      apply IsScalarTower.of_algebraMap_eq'
      ext x
      exact (decompositionEmbeddingCompletion v hvna w).commutes x |>.symm
    letI : Algebra v.Completion w.1.Completion :=
      (completionLies v w.1 w.2).toAlgebra
    letI : SMul v.Completion w.1.Completion :=
      (completionLies v w.1 w.2).toAlgebra.toSMul
    letI : Module v.Completion w.1.Completion := Algebra.toModule
    letI : Algebra D w.1.Completion :=
      ((completionEmbedding w.1).comp (algebraMap D L)).toAlgebra
    letI : SMul D w.1.Completion :=
      (((completionEmbedding w.1).comp (algebraMap D L)).toAlgebra).toSMul
    letI : Module D w.1.Completion := Algebra.toModule
    letI : IsScalarTower D v.Completion w.1.Completion := by
      apply IsScalarTower.of_algebraMap_eq'
      ext x
      exact (comple_decom_embed
        v hvna w x).symm
    letI : FiniteDimensional v.Completion w.1.Completion :=
      placeCompletionDimensional v w
    letI : IsGalois v.Completion w.1.Completion :=
      placeCompletionGalois v w
    let cD : NMCocycl₂ (G := Gal(L/D)) (M := Lˣ) :=
      NMCocycl₂.restrict (galoisTowerInclusion K D L)
        (fun _ _ => rfl) c
    let i : L →+* w.1.Completion := completionEmbedding w.1
    let g : Gal(L/D) ≃* Gal(w.1.Completion/v.Completion) :=
      decompositionGaloisCompletion v hvna w
    let hi : ∀ sigma : Gal(L/D), ∀ a : L,
        i (sigma a) = g sigma (i a) := fun sigma a =>
      (decomposition_galois_embedding
        v hvna w sigma a).symm
    let hbase : ∀ a : D,
        i (algebraMap D L a) =
          algebraMap v.Completion w.1.Completion
            (algebraMap D v.Completion a) := fun a =>
      (comple_decom_embed v hvna w a).symm
    let coeffEquiv : L ⊗[D] v.Completion ≃ₐ[v.Completion] w.1.Completion :=
      decompositionTensorCompletion v hvna w
    have hcoeff : ∀ (a : L) (b : v.Completion),
        coeffEquiv (a ⊗ₜ[D] b) =
          i a * algebraMap v.Completion w.1.Completion b := by
      intro a b
      exact decomposition_tensor_tmul v hvna w a b
    calc
      brauerBaseChange K v.Completion
          (CProduc.brauerClass K L c) =
          brauerBaseChange D v.Completion
            (brauerBaseChange K D (CProduc.brauerClass K L c)) :=
        (base_change_tower K D v.Completion
          (CProduc.brauerClass K L c)).symm
      _ = brauerBaseChange D v.Completion
          (CProduc.brauerClass D L cD) := by
        apply congrArg (brauerBaseChange D v.Completion)
        exact (restricted_crossed_brauer K D L c).symm
      _ = CProduc.brauerClass v.Completion w.1.Completion
          (transportedGaloisCocycle i g hi cD) :=
        brauer_base_crossed i g hi hbase cD coeffEquiv hcoeff
      _ = CProduc.brauerClass v.Completion w.1.Completion
          (restrictedGaloisCocycle v hvna w c) := rfl

set_option synthInstance.maxHeartbeats 1000000 in
-- Extra heartbeats are needed for the typeclass search in this proof.
set_option maxHeartbeats 6000000 in
/-- Triviality of the completed, decomposition-restricted central obstruction
kills the scalar extension of its global relative Brauer class. -/
theorem brauer_change_obstruction
    {Q : Type v} {G : Type w} [Group Q] [Group G]
    {K L : Type u} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (q : Q →* G) (hq : Function.Surjective q)
    (hcentral : q.ker ≤ Subgroup.center Q)
    (galoisEquiv : Gal(L/K) ≃* G)
    (kernelToUnits : q.ker →* Lˣ)
    (hfixed : ∀ sigma : Gal(L/K), ∀ z : q.ker,
      sigma • kernelToUnits z = kernelToUnits z)
    (v : AbsoluteValue K ℝ) [Fact v.IsNontrivial]
    [IsUltrametricDist v.Completion] (hvna : IsNonarchimedean v)
    (w : Towers.CField.ICohomo.CompletionPlacesAbove
      (L := L) v)
    [Finite (Towers.CField.ICohomo.CompletionPlacesAbove
      (L := L) v)]
    [Nonempty (Towers.CField.ICohomo.CompletionPlacesAbove
      (L := L) v)]
    [MulAction.IsPretransitive Gal(L/K)
      (Towers.CField.ICohomo.CompletionPlacesAbove
        (L := L) v)]
    (hlocal :
      letI : Algebra v.Completion w.1.Completion :=
        (Towers.NumberTheory.Milne.completionLies
          v w.1 w.2).toAlgebra
      letI : FiniteDimensional v.Completion w.1.Completion :=
        Towers.NumberTheory.Milne.placeCompletionDimensional v w
      letI : IsGalois v.Completion w.1.Completion :=
        Towers.NumberTheory.Milne.placeCompletionGalois v w
      letI : CommGroup q.ker :=
        centralExtensionComm q hcentral
      letI : MulDistribMulAction G q.ker :=
        trivialDistribAction G q.ker
      letI : MulDistribMulAction Gal(w.1.Completion/v.Completion) q.ker :=
        trivialDistribAction Gal(w.1.Completion/v.Completion) q.ker
      MHTwo.mapCoefficientsHom
          (completionKernelUnits v w kernelToUnits)
          (fun sigma z ↦
            (completion_units_fixed
              v hvna w kernelToUnits hfixed sigma z).symm)
          (MHTwo.restrictionHom
            (completionDecomposition v hvna w galoisEquiv)
            (fun _ _ ↦ rfl)
            (extensionObstructionClass q hq hcentral)) = 1) :
    letI : Algebra K v.Completion :=
      Towers.NumberTheory.Milne.completionBaseAlgebra v
    brauerBaseChange K v.Completion
        (extensionRelativeBrauer q hq hcentral galoisEquiv
          kernelToUnits hfixed : BrauerGroup K) = 1 := by
  let D := Towers.NumberTheory.Milne.completionDecompositionField
    v hvna w
  letI : Algebra K v.Completion :=
    Towers.NumberTheory.Milne.completionBaseAlgebra v
  letI : Algebra v.Completion w.1.Completion :=
    (Towers.NumberTheory.Milne.completionLies
      v w.1 w.2).toAlgebra
  letI : FiniteDimensional v.Completion w.1.Completion :=
    Towers.NumberTheory.Milne.placeCompletionDimensional v w
  letI : IsGalois v.Completion w.1.Completion :=
    Towers.NumberTheory.Milne.placeCompletionGalois v w
  letI : CommGroup q.ker :=
    centralExtensionComm q hcentral
  letI : MulDistribMulAction G q.ker :=
    trivialDistribAction G q.ker
  letI : MulDistribMulAction Gal(L/K) q.ker :=
    trivialDistribAction Gal(L/K) q.ker
  letI : MulDistribMulAction Gal(w.1.Completion/v.Completion) q.ker :=
    trivialDistribAction Gal(w.1.Completion/v.Completion) q.ker
  let cGlobal := NMCocycl₂.mapCoefficients kernelToUnits
    (fun sigma z ↦ (hfixed sigma z).symm)
    (NMCocycl₂.restrict galoisEquiv.toMonoidHom
      (fun _ _ ↦ rfl)
      ((centralExtensionSet q hq hcentral).normalizedMulCocycle
        (fun _ _ ↦ rfl)))
  let cLocal := restrictedGaloisCocycle v hvna w cGlobal
  have hmk : MHTwo.mk cLocal = 1 := by
    rw [completion_restricted_class
      q hq hcentral galoisEquiv kernelToUnits hfixed v hvna w]
    exact hlocal
  have hrelative : CProduc.relativeBrauerClass
      v.Completion w.1.Completion cLocal = 1 := by
    calc
      CProduc.relativeBrauerClass
          v.Completion w.1.Completion cLocal =
          CProduc.hRelativeBrauer
            v.Completion w.1.Completion (MHTwo.mk cLocal) := rfl
      _ = CProduc.hRelativeBrauer
            v.Completion w.1.Completion 1 := congrArg
              (CProduc.hRelativeBrauer
                v.Completion w.1.Completion) hmk
      _ = 1 := map_one _
  have hbrauer : CProduc.brauerClass
      v.Completion w.1.Completion cLocal = 1 := by
    exact congrArg Subtype.val hrelative
  change brauerBaseChange K v.Completion
      (CProduc.brauerClass K L cGlobal) = 1
  rw [base_change_crossed v hvna w cGlobal]
  exact hbrauer

/-- The factor set obtained by transporting a global Galois cocycle to a
completion whose decomposition group is the whole global Galois group. -/
noncomputable def completionTransportedCocycle
    {K L : Type u} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (v : AbsoluteValue K ℝ) [Fact v.IsNontrivial]
    [IsUltrametricDist v.Completion]
    [Finite (Towers.CField.ICohomo.CompletionPlacesAbove
      (L := L) v)]
    [Nonempty (Towers.CField.ICohomo.CompletionPlacesAbove
      (L := L) v)]
    [MulAction.IsPretransitive Gal(L/K)
      (Towers.CField.ICohomo.CompletionPlacesAbove
        (L := L) v)]
    (w : Towers.CField.ICohomo.CompletionPlacesAbove
      (L := L) v)
    (htop : Towers.NumberTheory.Milne.absoluteValueDecomposition
      v w.1 = ⊤)
    (c : NMCocycl₂ (G := Gal(L/K)) (M := Lˣ)) :
    letI : Algebra v.Completion w.1.Completion :=
      (Towers.NumberTheory.Milne.completionLies
        v w.1 w.2).toAlgebra
    letI : FiniteDimensional v.Completion w.1.Completion :=
      Towers.NumberTheory.Milne.placeCompletionDimensional v w
    letI : IsGalois v.Completion w.1.Completion :=
      Towers.NumberTheory.Milne.placeCompletionGalois v w
    NMCocycl₂
      (G := Gal(w.1.Completion/v.Completion)) (M := w.1.Completionˣ) := by
  letI : Algebra v.Completion w.1.Completion :=
    (Towers.NumberTheory.Milne.completionLies
      v w.1 w.2).toAlgebra
  letI : FiniteDimensional v.Completion w.1.Completion :=
    Towers.NumberTheory.Milne.placeCompletionDimensional v w
  letI : IsGalois v.Completion w.1.Completion :=
    Towers.NumberTheory.Milne.placeCompletionGalois v w
  let g :=
    Towers.NumberTheory.Milne.globalDecompositionTop
      v w htop
  exact transportedGaloisCocycle
    (Towers.NumberTheory.Milne.completionEmbedding w.1) g
    (fun sigma a =>
      (global_decomposition_embedding
          v w htop sigma a).symm)
    c

set_option synthInstance.maxHeartbeats 1000000 in
-- Extra heartbeats are needed for the typeclass search in this proof.
set_option maxHeartbeats 5000000 in
/-- At a place with full decomposition group, localization of a global
crossed product is represented by its completion-transported cocycle. -/
theorem change_crossed_top
    {K L : Type u} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (v : AbsoluteValue K ℝ) [Fact v.IsNontrivial]
    [IsUltrametricDist v.Completion]
    [Finite (Towers.CField.ICohomo.CompletionPlacesAbove
      (L := L) v)]
    [Nonempty (Towers.CField.ICohomo.CompletionPlacesAbove
      (L := L) v)]
    [MulAction.IsPretransitive Gal(L/K)
      (Towers.CField.ICohomo.CompletionPlacesAbove
        (L := L) v)]
    (w : Towers.CField.ICohomo.CompletionPlacesAbove
      (L := L) v)
    (htop : Towers.NumberTheory.Milne.absoluteValueDecomposition
      v w.1 = ⊤)
    (c : NMCocycl₂ (G := Gal(L/K)) (M := Lˣ)) :
    letI : Algebra K v.Completion :=
      Towers.NumberTheory.Milne.completionBaseAlgebra v
    letI : Algebra v.Completion w.1.Completion :=
      (Towers.NumberTheory.Milne.completionLies
        v w.1 w.2).toAlgebra
    letI : FiniteDimensional v.Completion w.1.Completion :=
      Towers.NumberTheory.Milne.placeCompletionDimensional v w
    letI : IsGalois v.Completion w.1.Completion :=
      Towers.NumberTheory.Milne.placeCompletionGalois v w
    brauerBaseChange K v.Completion (CProduc.brauerClass K L c) =
      CProduc.brauerClass v.Completion w.1.Completion
        (completionTransportedCocycle v w htop c) := by
  open Towers.NumberTheory.Milne in
    letI : Algebra K v.Completion := completionBaseAlgebra v
    letI : SMul K v.Completion := (completionBaseAlgebra v).toSMul
    letI : Module K v.Completion := Algebra.toModule
    letI : Algebra v.Completion w.1.Completion :=
      (completionLies v w.1 w.2).toAlgebra
    letI : SMul v.Completion w.1.Completion :=
      ((completionLies v w.1 w.2).toAlgebra).toSMul
    letI : Module v.Completion w.1.Completion := Algebra.toModule
    letI : Algebra K w.1.Completion :=
      ((completionEmbedding w.1).comp (algebraMap K L)).toAlgebra
    letI : SMul K w.1.Completion :=
      (((completionEmbedding w.1).comp (algebraMap K L)).toAlgebra).toSMul
    letI : Module K w.1.Completion := Algebra.toModule
    letI : IsScalarTower K v.Completion w.1.Completion :=
      IsScalarTower.of_algebraMap_eq' (by
        simpa using (completion_lies_comp v w.1 w.2).symm)
    letI : FiniteDimensional v.Completion w.1.Completion :=
      placeCompletionDimensional v w
    letI : IsGalois v.Completion w.1.Completion :=
      placeCompletionGalois v w
    let g := globalDecompositionTop v w htop
    let hi : ∀ sigma : Gal(L/K), ∀ a : L,
        completionEmbedding w.1 (sigma a) =
          g sigma (completionEmbedding w.1 a) :=
      fun sigma a =>
        (global_decomposition_embedding
          v w htop sigma a).symm
    let coeffEquiv :=
      tensorDecompositionTop v w htop
    let hbase : ∀ a : K,
        completionEmbedding w.1 (algebraMap K L a) =
          algebraMap v.Completion w.1.Completion
            (algebraMap K v.Completion a) := by
      intro a
      have hcomp := RingHom.congr_fun
        (completion_lies_comp v w.1 w.2) a
      exact hcomp.symm
    apply brauer_base_crossed
      (completionEmbedding w.1) g hi hbase c coeffEquiv
    intro a b
    change completionTensorPlace v w (a ⊗ₜ[K] b) =
      completionEmbedding w.1 a * completionLies v w.1 w.2 b
    exact tensor_place_tmul v a b w

set_option synthInstance.maxHeartbeats 1000000 in
-- Extra heartbeats are needed for the typeclass search in this proof.
set_option maxHeartbeats 6000000 in
/-- If a Brauer class becomes trivial over the decomposition field of an
extension of a nonarchimedean place, then it is trivial over the base
completion.  The distinguished decomposition-field completion has degree
one, so the decomposition field itself embeds into the base completion. -/
theorem brauer_change_decomposition
    {K L : Type u} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (v : AbsoluteValue K ℝ) [Fact v.IsNontrivial]
    [IsUltrametricDist v.Completion] (hvna : IsNonarchimedean v)
    (w : Towers.CField.ICohomo.CompletionPlacesAbove
      (L := L) v)
    (x : BrauerGroup K)
    (hD :
      let hw :=
        Towers.NumberTheory.Milne.absolute_extension_nontrivial
          v w
      let hwna :=
        Towers.NumberTheory.Milne.absolute_extension_nonarchimedean
          v w
      let P :=
        Towers.NumberTheory.Milne.nonarchimedeanHeightSpectrum
          w.1 hw hwna
      let H := MulAction.stabilizer Gal(L/K) P.asIdeal
      let D := (FixedPoints.intermediateField H : IntermediateField K L)
      brauerBaseChange K D x = 1) :
    letI : Algebra K v.Completion :=
      Towers.NumberTheory.Milne.completionBaseAlgebra v
    brauerBaseChange K v.Completion x = 1 := by
  open Towers.NumberTheory.Milne in
    let hw := absolute_extension_nontrivial v w
    let hwna := absolute_extension_nonarchimedean v w
    let P := nonarchimedeanHeightSpectrum w.1 hw hwna
    let H := MulAction.stabilizer Gal(L/K) P.asIdeal
    let D := (FixedPoints.intermediateField H : IntermediateField K L)
    letI : NontriviallyNormedField v.Completion :=
      absoluteNontriviallyNormed v
    letI : Algebra K v.Completion := completionBaseAlgebra v
    letI : SMul K v.Completion := completionBaseSMul v
    letI : Module K v.Completion := completionBaseModule v
    let f : D →ₐ[K] v.Completion :=
      decompositionEmbeddingCompletion v hvna w
    letI : Algebra D v.Completion := f.toAlgebra
    letI : IsScalarTower K D v.Completion := by
      apply IsScalarTower.of_algebraMap_eq
      intro a
      exact (f.commutes a).symm
    change brauerBaseChange K D x = 1 at hD
    rw [← base_change_tower K D v.Completion x, hD, map_one]

/-- Triviality after scalar extension transports across a field equivalence
that respects the two embeddings of the base field. -/
theorem brauer_change_ring
    (K L M : Type u) [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra K M]
    (e : L ≃+* M)
    (he : e.toRingHom.comp (algebraMap K L) = algebraMap K M)
    (x : BrauerGroup K)
    (h : brauerBaseChange K L x = 1) :
    brauerBaseChange K M x = 1 := by
  letI : Algebra L M := e.toRingHom.toAlgebra
  letI : IsScalarTower K L M := by
    apply IsScalarTower.of_algebraMap_eq'
    exact he.symm
  rw [← base_change_tower K L M x, h, map_one]

/-- The algebra structure induced by the completion embedding agrees with the
canonical completion algebra structure. -/
theorem completion_embedding_base
    {K : Type u} [Field K] (v : AbsoluteValue K ℝ) :
    (Towers.NumberTheory.Milne.completionEmbedding v).toAlgebra =
      Towers.NumberTheory.Milne.completionBaseAlgebra v := by
  apply Algebra.algebra_ext
  intro x
  rfl

/-- A number field containing a primitive cube root of unity has only complex
infinite places, so every Brauer class becomes trivial at an infinite
completion. -/
theorem brauer_primitive_cube
    {K : Type u} [Field K] [NumberField K]
    (zeta : K) (hzeta : IsPrimitiveRoot zeta 3)
    (v : InfinitePlace K) (x : BrauerGroup K) :
    letI : Algebra K v.1.Completion :=
      Towers.NumberTheory.Milne.completionBaseAlgebra v.1
    brauerBaseChange K v.1.Completion x = 1 := by
  open Towers.NumberTheory.Milne in
    have hvComplex : v.IsComplex := by
      apply InfinitePlace.not_isReal_iff_isComplex.mp
      intro hvReal
      let embedding : K →+* ℝ := InfinitePlace.embedding_of_isReal hvReal
      have hroot : IsPrimitiveRoot (embedding zeta) 3 :=
        hzeta.map_of_injective embedding.injective
      have hpow : embedding zeta ^ 3 = (1 : ℝ) ^ 3 := by
        simpa using hroot.pow_eq_one
      have hone : embedding zeta = 1 :=
        (show Odd 3 by norm_num).pow_injective hpow
      have hdiv : 3 ∣ 1 :=
        (hroot.pow_eq_one_iff_dvd 1).mp (by simp [hone])
      norm_num at hdiv
    letI : Algebra K v.1.Completion := completionBaseAlgebra v.1
    let e : v.1.Completion ≃+* ℂ :=
      InfinitePlace.Completion.ringEquivComplexOfIsComplex hvComplex
    letI : IsAlgClosed v.1.Completion := by
      apply IsAlgClosed.of_exists_root
      intro p _hpMonic hpIrreducible
      let pC : Polynomial ℂ := p.map e.toRingHom
      have hpC : pC.degree ≠ 0 := by
        simpa [pC, Polynomial.degree_map] using
          (Polynomial.degree_pos_of_irreducible hpIrreducible).ne'
      obtain ⟨z, hz⟩ := IsAlgClosed.exists_root pC hpC
      refine ⟨e.symm z, ?_⟩
      apply e.injective
      calc
        e (p.eval (e.symm z)) =
            (p.map e.toRingHom).eval (e (e.symm z)) :=
          (Polynomial.eval_map_apply (p := p) e.toRingHom (e.symm z)).symm
        _ = pC.eval z := by simp [pC]
        _ = 0 := hz
        _ = e 0 := e.map_zero.symm
    letI : Subsingleton (BrauerGroup v.1.Completion) :=
      brauer_subsingleton_closed v.1.Completion
    exact Subsingleton.elim _ _

/-- Global Brauer localization kills the transported central-extension class
as soon as it is trivial over every completion. -/
theorem central_all_completions
    {E : Type v} {G : Type w} [Group E] [Group G]
    {K L : Type u} [Field K] [NumberField K]
    [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (q : E →* G) (hq : Function.Surjective q)
    (hcentral : q.ker ≤ Subgroup.center E)
    (galoisEquiv : Gal(L/K) ≃* G)
    (kernelToUnits : q.ker →* Lˣ)
    (hfixed : ∀ sigma : Gal(L/K), ∀ z : q.ker,
      sigma • kernelToUnits z = kernelToUnits z)
    (loc : GlobalLocalizationData K)
    (placeInvariant : ∀ place : NumberFieldPlace K,
      Additive (BrauerGroup (placeCompletion K place)) →+
        Towers.CField.LBrauer.LocalInvariant)
    (hsequence : GlobalBrauerSequence K loc placeInvariant)
    (hlocal : ∀ place : NumberFieldPlace K,
      brauerBaseChange K (placeCompletion K place)
          (extensionRelativeBrauer q hq hcentral galoisEquiv
            kernelToUnits hfixed : BrauerGroup K) = 1) :
    centralExtensionClass q hq hcentral galoisEquiv
      kernelToUnits hfixed = 1 := by
  let x : relativeBrauerGroup K L :=
    extensionRelativeBrauer q hq hcentral galoisEquiv
      kernelToUnits hfixed
  have hx : (x : BrauerGroup K) = 1 := by
    apply Additive.ofMul.injective
    apply hsequence.2.1
    apply DirectSum.ext
    intro place
    change
      DirectSum.component ℤ (NumberFieldPlace K)
          (fun v => Additive (BrauerGroup (placeCompletion K v))) place
          (loc.localization (Additive.ofMul (x : BrauerGroup K))) =
        DirectSum.component ℤ (NumberFieldPlace K)
          (fun v => Additive (BrauerGroup (placeCompletion K v))) place
          (loc.localization (Additive.ofMul (1 : BrauerGroup K)))
    rw [loc.localization_apply, loc.localization_apply]
    rw [hsequence.1 (x : BrauerGroup K) place,
      hsequence.1 (1 : BrauerGroup K) place]
    exact congrArg Additive.ofMul
      ((hlocal place).trans
        (map_one (brauerBaseChange K (placeCompletion K place))).symm)
  apply
    (extension_relative_brauer q hq hcentral
      galoisEquiv kernelToUnits hfixed).1
  apply Subtype.ext
  exact hx

/-- Over a number field containing a primitive cube root of unity, it is
enough to kill a central obstruction at the finite completions: all infinite
completions are complex and hence have trivial Brauer group. -/
theorem central_extension_completions
    {E : Type v} {G : Type w} [Group E] [Group G]
    {K L : Type u} [Field K] [NumberField K]
    [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (q : E →* G) (hq : Function.Surjective q)
    (hcentral : q.ker ≤ Subgroup.center E)
    (galoisEquiv : Gal(L/K) ≃* G)
    (kernelToUnits : q.ker →* Lˣ)
    (hfixed : ∀ sigma : Gal(L/K), ∀ z : q.ker,
      sigma • kernelToUnits z = kernelToUnits z)
    (zeta : K) (hzeta : IsPrimitiveRoot zeta 3)
    (loc : GlobalLocalizationData K)
    (placeInvariant : ∀ place : NumberFieldPlace K,
      Additive (BrauerGroup (placeCompletion K place)) →+
        Towers.CField.LBrauer.LocalInvariant)
    (hsequence : GlobalBrauerSequence K loc placeInvariant)
    (hfinite : ∀ v : HeightOneSpectrum (NumberField.RingOfIntegers K),
      @brauerBaseChange K (v.adicCompletion K) inferInstance inferInstance
        (FinitePlace.embedding v).toAlgebra
          (extensionRelativeBrauer q hq hcentral galoisEquiv
            kernelToUnits hfixed : BrauerGroup K) = 1) :
    centralExtensionClass q hq hcentral galoisEquiv
      kernelToUnits hfixed = 1 := by
  apply central_all_completions
    q hq hcentral galoisEquiv kernelToUnits hfixed
      loc placeInvariant hsequence
  intro place
  cases place with
  | inl v =>
      change @brauerBaseChange K (v.adicCompletion K)
        inferInstance inferInstance (FinitePlace.embedding v).toAlgebra
          (extensionRelativeBrauer q hq hcentral galoisEquiv
            kernelToUnits hfixed : BrauerGroup K) = 1
      exact hfinite v
  | inr v =>
      change @brauerBaseChange K v.1.Completion
        inferInstance inferInstance
          (Towers.NumberTheory.Milne.completionEmbedding v.1).toAlgebra
          (extensionRelativeBrauer q hq hcentral galoisEquiv
            kernelToUnits hfixed : BrauerGroup K) = 1
      rw [completion_embedding_base]
      exact brauer_primitive_cube
        zeta hzeta v
          (extensionRelativeBrauer q hq hcentral galoisEquiv
            kernelToUnits hfixed : BrauerGroup K)

/-- The global cyclicity theorem supplies a cyclic splitting field for an
arbitrary Brauer class.  This is the form needed for a central embedding
obstruction, whose representative is a crossed product rather than an
already chosen division algebra. -/
theorem cyclic_brauer_splitter
    (K : Type u) [Field K] [NumberField K]
    (hcyclic :
      Towers.CField.GWang.DivisionCyclicityTheorem K)
    (x : BrauerGroup K) :
    ∃ L : Towers.CField.LFTheory.FASubext K,
      IsCyclic Gal(L.1/K) ∧ brauerBaseChange K L.1 x = 1 := by
  induction x using Quotient.inductionOn with
  | _ A =>
      obtain ⟨D, hDdiv, hDalg, hDcentral, hDfinite, hAD⟩ :=
        division_brauer_representative K A
      letI : DivisionRing D := hDdiv
      letI : Algebra K D := hDalg
      letI : Algebra.IsCentral K D := hDcentral
      letI : Module.Finite K D := hDfinite
      obtain ⟨_, L, hLcyclic, i, hmaximal, hsplit⟩ := hcyclic D
      refine ⟨L, hLcyclic, ?_⟩
      have hclass :
          brauerClass K A = brauerClass K (centralDivisionCSA K D) :=
        (brauer_class K A (centralDivisionCSA K D)).2 hAD
      change brauerBaseChange K L.1 (brauerClass K A) = 1
      rw [hclass]
      have hmem :
          brauerClass K (centralDivisionCSA K D) ∈
            relativeBrauerGroup K L.1 :=
        (brauer_relative_split
          K L.1 (centralDivisionCSA K D)).2 hsplit
      exact hmem

set_option synthInstance.maxHeartbeats 100000 in
-- Extra heartbeats are needed for the typeclass search in this proof.
set_option maxHeartbeats 1000000 in
/-- A cyclic splitter can be joined to any prescribed finite Galois
coefficient field.  The resulting finite Galois overfield still splits the
Brauer class. -/
theorem overfield_splitting_brauer
    (K : Type u) [Field K] [NumberField K]
    (hcyclic :
      Towers.CField.GWang.DivisionCyclicityTheorem K)
    (F : FiniteGaloisIntermediateField K (SeparableClosure K))
    (x : BrauerGroup K) :
    ∃ E : FiniteGaloisIntermediateField K (SeparableClosure K),
      (F : IntermediateField K (SeparableClosure K)) ≤ E ∧
        brauerBaseChange K E x = 1 := by
  obtain ⟨L, hLcyclic, hLsplit⟩ := cyclic_brauer_splitter K hcyclic x
  let E : FiniteGaloisIntermediateField K (SeparableClosure K) := F ⊔ L.1
  refine ⟨E, le_sup_left, ?_⟩
  let hLE : (L.1 : IntermediateField K (SeparableClosure K)) ≤ E :=
    le_sup_right
  letI : Algebra L.1 E := (IntermediateField.inclusion hLE).toAlgebra
  letI : IsScalarTower K L.1 E :=
    IsScalarTower.of_algebraMap_eq (congrFun rfl)
  rw [← base_change_tower K L.1 E x, hLsplit, map_one]

end TBluepr
end Towers
