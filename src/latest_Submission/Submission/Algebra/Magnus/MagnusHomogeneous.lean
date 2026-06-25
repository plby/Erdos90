import Submission.Algebra.Magnus.IntegralCokernel
import Submission.Algebra.Magnus.MagnusWeightedCoefficients


noncomputable section

/-!
# Homogeneous coefficients of the Magnus map

This file connects coefficients in the completed Magnus ring to the
homogeneous word-polynomial and augmentation-layer models used by the graded
integral Magnus map.
-/

namespace EChapma
namespace MSeries

open Submission
open Submission.TBluepr

variable {R X : Type*} [CommRing R] [DecidableEq X]

local instance : DecidableEq (FreeMonoid X) := Classical.decEq _

/-- The delta series supported at one noncommutative word. -/
def wordSeries (w : FreeMonoid X) : MSeries R X :=
  ⟨fun v => if v = w then 1 else 0⟩

omit [DecidableEq X] in
@[simp]
theorem wordSeries_apply (w v : FreeMonoid X) :
    wordSeries (R := R) w v = if v = w then 1 else 0 :=
  rfl

omit [DecidableEq X] in
@[simp]
theorem wordSeries_one :
    wordSeries (R := R) (X := X) 1 = 1 := by
  ext w
  by_cases hw : w = 1
  · subst w
    simp [wordSeries]
  · have hlen : w.length ≠ 0 := by
      intro hzero
      exact hw (FreeMonoid.length_eq_zero.mp hzero)
    simp [wordSeries, hw, hlen]

omit [DecidableEq X] in
@[simp]
theorem variable_series (x : X) :
    variableSeries (R := R) x =
      wordSeries (R := R) (FreeMonoid.of x) := by
  ext w
  simp [variableSeries, wordSeries]

omit [DecidableEq X] in
private theorem of_of_iff
    (x y : X) (w : FreeMonoid X) :
    FreeMonoid.of y * w = FreeMonoid.of x ↔ y = x ∧ w = 1 := by
  constructor
  · intro h
    have hlist := congrArg FreeMonoid.toList h
    simp only [FreeMonoid.toList_mul, FreeMonoid.toList_of] at hlist
    have hyx : y = x := by
      simpa using congrArg List.head? hlist
    subst y
    have hwlist : w.toList = [] := by
      simpa using hlist
    exact ⟨rfl, FreeMonoid.toList.injective (by simpa using hwlist)⟩
  · rintro ⟨rfl, rfl⟩
    simp

omit [DecidableEq X] in
private theorem of_eq_iff
    (x y : X) (u v : FreeMonoid X) :
    FreeMonoid.of y * u = FreeMonoid.of x * v ↔ y = x ∧ u = v := by
  constructor
  · intro h
    have hlist := congrArg FreeMonoid.toList h
    simp only [FreeMonoid.toList_mul, FreeMonoid.toList_of] at hlist
    have hyx : y = x := by
      simpa using congrArg List.head? hlist
    subst y
    have huv : u.toList = v.toList := by
      simpa using congrArg List.tail hlist
    exact ⟨rfl, FreeMonoid.toList.injective huv⟩
  · rintro ⟨rfl, rfl⟩
    rfl

@[simp]
theorem shift_variableSeries (x y : X) :
    shift y (variableSeries (R := R) x) =
      if y = x then 1 else 0 := by
  classical
  ext w
  by_cases hyx : y = x
  · subst y
    by_cases hw : w = 1
    · subst w
      simp [shift, variableSeries]
    · have hlen : w.length ≠ 0 := by
        intro hzero
        exact hw (FreeMonoid.length_eq_zero.mp hzero)
      simp [shift, variableSeries, hw, hlen]
  · simp [shift, variableSeries, of_of_iff, hyx]

omit [DecidableEq X] in
/-- Multiplying a word series on the left by one variable prepends that
variable to its supporting word. -/
theorem variable_series_mul
    (x : X) (w : FreeMonoid X) :
    variableSeries (R := R) x * wordSeries (R := R) w =
      wordSeries (R := R) (FreeMonoid.of x * w) := by
  classical
  ext v
  refine FreeMonoid.casesOn
    (C := fun v =>
      (variableSeries (R := R) x * wordSeries (R := R) w) v =
        wordSeries (R := R) (FreeMonoid.of x * w) v)
    v ?_ ?_
  · change
      (variableSeries (R := R) x * wordSeries (R := R) w) 1 =
        wordSeries (R := R) (FreeMonoid.of x * w) 1
    rw [mul_apply_one]
    have hne :
        (1 : FreeMonoid X) ≠ FreeMonoid.of x * w := by
      intro h
      have hlength := congrArg FreeMonoid.length h
      simp at hlength
      omega
    simp [variableSeries, wordSeries, hne]
  · intro y u
    rw [apply_of_mul, shift_variableSeries]
    by_cases hyx : y = x
    · subst y
      simp [wordSeries]
    · simp [hyx, wordSeries, of_eq_iff]

omit [DecidableEq X] in
/-- Delta word series multiply by concatenating their supporting words. -/
theorem wordSeries_mul (u v : FreeMonoid X) :
    wordSeries (R := R) u * wordSeries (R := R) v =
      wordSeries (R := R) (u * v) := by
  classical
  induction u using FreeMonoid.inductionOn' with
  | one => simp
  | mul_of x u ih =>
      calc
        wordSeries (R := R) (FreeMonoid.of x * u) *
              wordSeries (R := R) v =
            (variableSeries (R := R) x * wordSeries (R := R) u) *
              wordSeries (R := R) v := by
                rw [variable_series_mul]
        _ =
            variableSeries (R := R) x *
              (wordSeries (R := R) u * wordSeries (R := R) v) := by
                rw [mul_assoc]
        _ =
            variableSeries (R := R) x *
              wordSeries (R := R) (u * v) := by rw [ih]
        _ =
            wordSeries (R := R) (FreeMonoid.of x * (u * v)) :=
              variable_series_mul x (u * v)
        _ =
            wordSeries (R := R) ((FreeMonoid.of x * u) * v) := by
              congr 1

omit [DecidableEq X] in
/-- The Magnus extension sends a scalar in the group algebra to its constant
series. -/
theorem group_algebra_magnus
    (r : R) :
    GAWt.groupAlgebraMagnus
        (R := R) (X := X)
        (algebraMap R (MonoidAlgebra R (FreeGroup X)) r) =
      GAWt.constantSeries (X := X) r := by
  change
    MonoidAlgebra.liftNCRingHom
        (GAWt.constantSeriesHom (R := R) (X := X))
        (GAWt.magnusMonoidHom (R := R) (X := X))
        _
        (MonoidAlgebra.single 1 r) =
      GAWt.constantSeries (X := X) r
  rw [MonoidAlgebra.liftNCRingHom_single]
  simp [GAWt.constantSeriesHom]

omit [DecidableEq X] in
/-- A forward augmentation word maps to the delta series at the same word. -/
theorem magnus_free_forward
    (w : FreeMonoid X) :
    GAWt.groupAlgebraMagnus
        (R := R) (X := X)
        (freeForwardWord R X w) =
      wordSeries (R := R) w := by
  classical
  induction w using FreeMonoid.inductionOn' with
  | one =>
      simp
  | mul_of x w ih =>
      rw [free_forward_append, map_mul]
      simp only [free_forward_singleton]
      change
        GAWt.groupAlgebraMagnus
            (R := R) (X := X)
            (MonoidAlgebra.of R (FreeGroup X) (FreeGroup.of x) - 1) *
          GAWt.groupAlgebraMagnus
            (R := R) (X := X)
            (freeForwardWord R X w) =
          wordSeries (R := R) (FreeMonoid.of x * w)
      rw [map_sub, map_one,
        GAWt.algebra_magnus, ih]
      simp [variable_series, magnusSeries_of,
        wordSeries_mul]

/-- A finite noncommutative word polynomial, regarded as a formal Magnus
series with the same coefficients. -/
def wordPolynomialSeries
    (p : MonoidAlgebra R (FreeMonoid X)) :
    MSeries R X :=
  ⟨fun w => p w⟩

omit [DecidableEq X] in
@[simp]
theorem word_polynomial_series
    (p : MonoidAlgebra R (FreeMonoid X)) (w : FreeMonoid X) :
    wordPolynomialSeries p w = p w :=
  rfl

omit [DecidableEq X] in
@[simp]
theorem word_series_zero :
    wordPolynomialSeries
        (R := R) (X := X) (0 : MonoidAlgebra R (FreeMonoid X)) =
      0 := by
  ext w
  change (0 : R) = 0
  rfl

omit [DecidableEq X] in
@[simp]
theorem word_series_add
    (p q : MonoidAlgebra R (FreeMonoid X)) :
    wordPolynomialSeries (p + q) =
      wordPolynomialSeries p + wordPolynomialSeries q := by
  ext w
  simp [wordPolynomialSeries]

omit [DecidableEq X] in
@[simp]
theorem word_series_single
    (w : FreeMonoid X) (r : R) :
    wordPolynomialSeries
        (R := R) (X := X) (MonoidAlgebra.single w r) =
      GAWt.constantSeries (X := X) r *
        wordSeries (R := R) w := by
  ext v
  rw [GAWt.constantSeries_mul]
  by_cases hv : v = w
  · subst v
    simp [wordPolynomialSeries, wordSeries,
      ]
  · simp [wordPolynomialSeries, wordSeries,
      hv]

omit [DecidableEq X] in
/-- Realizing a finite word polynomial in the free-group algebra and applying
the Magnus extension recovers exactly the same coefficient polynomial in the
completed Magnus ring. -/
theorem magnus_associative_realization
    (p : MonoidAlgebra R (FreeMonoid X)) :
    GAWt.groupAlgebraMagnus
        (R := R) (X := X)
        (freeAssociativeRealization R X p) =
      wordPolynomialSeries p := by
  classical
  induction p using Finsupp.induction with
  | zero =>
      calc
        GAWt.groupAlgebraMagnus
              (R := R) (X := X)
              (freeAssociativeRealization R X
                (0 : MonoidAlgebra R (FreeMonoid X))) =
            GAWt.groupAlgebraMagnus
              (R := R) (X := X) 0 := by
                congr 1
        _ = 0 := map_zero _
        _ = wordPolynomialSeries
              (R := R) (X := X)
              (0 : MonoidAlgebra R (FreeMonoid X)) :=
            word_series_zero.symm
  | @single_add w r p hw hr ih =>
      change
        GAWt.groupAlgebraMagnus
            (R := R) (X := X)
            (freeAssociativeRealization R X
              (Finsupp.single w r + p)) =
          wordPolynomialSeries (Finsupp.single w r + p)
      have hsingle :
          GAWt.groupAlgebraMagnus
              (R := R) (X := X)
              (freeAssociativeRealization R X (Finsupp.single w r)) =
            wordPolynomialSeries (Finsupp.single w r) := by
        rw [free_realization_single, map_mul,
          group_algebra_magnus,
          magnus_free_forward,
          word_series_single]
      calc
        GAWt.groupAlgebraMagnus
              (R := R) (X := X)
              (freeAssociativeRealization R X
                (Finsupp.single w r + p)) =
            GAWt.groupAlgebraMagnus
              (R := R) (X := X)
              (freeAssociativeRealization R X (Finsupp.single w r) +
                freeAssociativeRealization R X p) := by
                  congr 1
                  exact map_add _ _ _
        _ =
            GAWt.groupAlgebraMagnus
                (R := R) (X := X)
                (freeAssociativeRealization R X (Finsupp.single w r)) +
              GAWt.groupAlgebraMagnus
                (R := R) (X := X)
                (freeAssociativeRealization R X p) := map_add _ _ _
        _ =
            wordPolynomialSeries (Finsupp.single w r) +
              wordPolynomialSeries p := by rw [hsingle, ih]
        _ = wordPolynomialSeries (Finsupp.single w r + p) :=
          (word_series_add _ _).symm

section FiniteAlphabet

variable [Fintype X] [Encodable X]

/-- The homogeneous degree-`n` coefficient polynomial of a Magnus series. -/
noncomputable def homogeneousPart
    (n : ℕ) (f : MSeries ℤ X) :
    AssociativeHomogeneousWords ℤ X n :=
  (Finsupp.supportedEquivFinsupp
      (R := ℤ) {w : FreeMonoid X | w.length = n}).symm
    ((Finsupp.linearEquivFunOnFinite
      ℤ ℤ (AssociativeWordsLength X n)).symm
        (fun w => f w.1))

omit [DecidableEq X] [Encodable X] in
@[simp]
theorem homogeneousPart_apply
    (n : ℕ) (f : MSeries ℤ X)
    (w : AssociativeWordsLength X n) :
    (homogeneousPart n f).1 w.1 = f w.1 := by
  change
    ((Finsupp.supportedEquivFinsupp
        (R := ℤ) {w : FreeMonoid X | w.length = n}).symm
      ((Finsupp.linearEquivFunOnFinite
        ℤ ℤ (AssociativeWordsLength X n)).symm
          (fun w => f w.1)) : FreeMonoid X →₀ ℤ) w.1 =
      f w.1
  rw [Finsupp.supportedEquivFinsupp_symm_apply_coe]
  simp [Finsupp.extendDomain_apply, w.2]

omit [DecidableEq X] [Encodable X] in
/-- Taking the homogeneous part of a homogeneous finite polynomial recovers
that polynomial. -/
theorem homogeneous_part_series
    (n : ℕ) (p : AssociativeHomogeneousWords ℤ X n) :
    homogeneousPart n (wordPolynomialSeries p.1) = p := by
  apply
    (Finsupp.supportedEquivFinsupp
      (R := ℤ) {w : FreeMonoid X | w.length = n}).injective
  ext w
  change
    ((Finsupp.supportedEquivFinsupp
      (R := ℤ) {w : FreeMonoid X | w.length = n})
        ((Finsupp.supportedEquivFinsupp
          (R := ℤ) {w : FreeMonoid X | w.length = n}).symm
            ((Finsupp.linearEquivFunOnFinite
              ℤ ℤ (AssociativeWordsLength X n)).symm
                (fun w => p.1 w.1)))) w =
      ((Finsupp.supportedEquivFinsupp
        (R := ℤ) {w : FreeMonoid X | w.length = n}) p) w
  rw [LinearEquiv.apply_symm_apply]
  change
    ((Finsupp.linearEquivFunOnFinite
      ℤ ℤ (AssociativeWordsLength X n)).symm
        (fun w => p.1 w.1)) w =
      p.1 w.1
  rfl

omit [Fintype X] [DecidableEq X] [Encodable X] in
/-- Coordinatewise divisibility in a homogeneous word polynomial is the same
as divisibility by that integer in the homogeneous module. -/
theorem homogeneous_smul_dvd
    [Finite X]
    {n : ℕ} {a : ℤ}
    {p : AssociativeHomogeneousWords ℤ X n}
    (hp :
      ∀ w : AssociativeWordsLength X n,
        a ∣ p.1 w.1) :
    ∃ q : AssociativeHomogeneousWords ℤ X n,
      p = a • q := by
  classical
  letI : Fintype X := Fintype.ofFinite X
  let q : AssociativeHomogeneousWords ℤ X n :=
    (Finsupp.supportedEquivFinsupp
      (R := ℤ) {w : FreeMonoid X | w.length = n}).symm
        ((Finsupp.linearEquivFunOnFinite
          ℤ ℤ (AssociativeWordsLength X n)).symm
            (fun w => Classical.choose (hp w)))
  refine ⟨q, ?_⟩
  apply
    (Finsupp.supportedEquivFinsupp
      (R := ℤ) {w : FreeMonoid X | w.length = n}).injective
  ext w
  rw [map_smul]
  change
    p.1 w.1 =
      a *
        ((Finsupp.supportedEquivFinsupp
          (R := ℤ) {w : FreeMonoid X | w.length = n}) q) w
  rw [show
    (Finsupp.supportedEquivFinsupp
      (R := ℤ) {w : FreeMonoid X | w.length = n}) q =
        (Finsupp.linearEquivFunOnFinite
          ℤ ℤ (AssociativeWordsLength X n)).symm
            (fun w => Classical.choose (hp w)) by
      exact LinearEquiv.apply_symm_apply _ _]
  change
    p.1 w.1 =
      a *
        ((Finsupp.linearEquivFunOnFinite
          ℤ ℤ (AssociativeWordsLength X n)).symm
            (fun w => Classical.choose (hp w))) w
  exact Classical.choose_spec (hp w)

omit [DecidableEq X] [Encodable X] in
/-- The polynomial coordinates of an augmentation-layer representative are
the corresponding homogeneous Magnus coefficients. -/
theorem homogeneous_realization_magnus
    (n : ℕ)
    (a : GroupAlgebra.augmentationPowerSubmodule
      ℤ (FreeGroup X) n)
    (w : AssociativeWordsLength X n) :
    ((ICokern.homogeneousRealizationLinear
        (X := X) n).symm
      (Submodule.Quotient.mk a)).1 w.1 =
        GAWt.groupAlgebraMagnus
          (R := ℤ) (X := X)
          (a : MonoidAlgebra ℤ (FreeGroup X)) w.1 := by
  classical
  let p : AssociativeHomogeneousWords ℤ X n :=
    (ICokern.homogeneousRealizationLinear
      (X := X) n).symm (Submodule.Quotient.mk a)
  have hlayer :
      associativeHomogeneousRealization ℤ X n p =
        Submodule.Quotient.mk a := by
    exact
      (ICokern.homogeneousRealizationLinear
        (X := X) n).apply_symm_apply (Submodule.Quotient.mk a)
  have hdiff :
      freeAssociativeRealization ℤ X p.1 -
          (a : MonoidAlgebra ℤ (FreeGroup X)) ∈
        GroupAlgebra.augmentationPower ℤ (FreeGroup X) (n + 1) := by
    exact
      (Submodule.Quotient.eq
        (GroupAlgebra.augmentationLayerDenom
          ℤ (FreeGroup X) n)).mp hlayer
  have hdiff' :
      freeAssociativeRealization ℤ X p.1 -
          (a : MonoidAlgebra ℤ (FreeGroup X)) ∈
        Submission.GShafar.augmentationIdeal
            ℤ (FreeGroup X) ^ (n + 1) := by
    simpa [GroupAlgebra.augmentationPower,
      ← GAWt.augmentation_ideal_algebra] using hdiff
  have horder :=
    GAWt.magnus_least_pow
      (R := ℤ) (X := X) hdiff'
  have hzero := horder w.1 (by simp [w.2])
  change
    GAWt.groupAlgebraMagnus
        (R := ℤ) (X := X)
        (freeAssociativeRealization ℤ X p.1 -
          (a : MonoidAlgebra ℤ (FreeGroup X))) w.1 =
      0 at hzero
  rw [map_sub,
    magnus_associative_realization] at hzero
  change
    p.1 w.1 -
        GAWt.groupAlgebraMagnus
          (R := ℤ) (X := X)
          (a : MonoidAlgebra ℤ (FreeGroup X)) w.1 =
      0 at hzero
  exact sub_eq_zero.mp hzero

end FiniteAlphabet

end MSeries
end EChapma
