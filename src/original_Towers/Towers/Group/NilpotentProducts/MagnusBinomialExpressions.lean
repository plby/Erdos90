import Towers.Group.NilpotentProducts.GeneralPolynomialCoordinates
import Towers.Group.Edmonton.HallEmbeddings

/-!
# Theorem H1 in standard Hall coordinates at arbitrary cutoff

The weighted symbolic collector gives sharper formulas through cutoff four.
For arbitrary cutoff, Magnus coefficients give a separate route to the
polynomial part of Theorem H1.  This file develops the multivariate analogue
of `MPOrd` without a degree bound: every Magnus coefficient
is represented by a compositional binomial expression.  The usual
weight-by-weight Hall-coordinate extraction then proves polynomiality in the
same standard Hall coordinates as `normalForm`.
-/

namespace Struik
namespace P1960

open EChapma
open EChapma.MSeries
open Towers
open Towers.Edmonton
open Towers.TBluepr
open Towers.TCTex

universe u v

noncomputable section

/-- A multivariate family of Magnus series whose every coefficient is a
compositional integer-valued binomial expression in the input variables. -/
structure MBExpr
    {X : Type u}
    {ι : Type v}
    (family : (ι → ℤ) → MSeries ℤ X) : Prop where
  coefficient :
    ∀ w, IEMap (fun x => family x w)

namespace MBExpr

variable {X : Type u} {ι : Type v}
variable {f g : (ι → ℤ) → MSeries ℤ X}

noncomputable local instance : DecidableEq X := Classical.decEq X

private theorem finsetSum
    {κ : Type*}
    (S : Finset κ)
    (h : κ → (ι → ℤ) → ℤ)
    (hh : ∀ k ∈ S, IEMap (h k)) :
    IEMap (fun x => ∑ k ∈ S, h k x) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      simpa using binomial_expression_const (ι := ι) 0
  | @insert k S hk ih =>
      have hkExpression := hh k (by simp)
      have hSExpression := ih fun j hj => hh j (by simp [hj])
      simpa [hk] using hkExpression.add hSExpression

/-- The zero Magnus family is coefficientwise binomial. -/
theorem zero :
    MBExpr
      (fun _ : ι → ℤ => (0 : MSeries ℤ X)) := by
  constructor
  intro w
  simpa using binomial_expression_const (ι := ι) 0

/-- A constant Magnus family is coefficientwise binomial. -/
theorem constant (a : MSeries ℤ X) :
    MBExpr (fun _ : ι → ℤ => a) := by
  constructor
  intro w
  exact binomial_expression_const (a w)

/-- Addition preserves coefficientwise binomiality. -/
theorem add
    (hf : MBExpr f)
    (hg : MBExpr g) :
    MBExpr (fun x => f x + g x) := by
  constructor
  intro w
  simpa only [MSeries.add_apply, Pi.add_apply] using
    (hf.coefficient w).add (hg.coefficient w)

/-- Negation preserves coefficientwise binomiality. -/
theorem neg
    (hf : MBExpr f) :
    MBExpr (fun x => -f x) := by
  constructor
  intro w
  simpa only [MSeries.neg_apply, Pi.neg_apply] using
    (hf.coefficient w).neg

/-- Subtraction preserves coefficientwise binomiality. -/
theorem sub
    (hf : MBExpr f)
    (hg : MBExpr g) :
    MBExpr (fun x => f x - g x) := by
  constructor
  intro w
  simpa only [MSeries.sub_apply, Pi.sub_apply] using
    (hf.coefficient w).sub (hg.coefficient w)

/-- Cauchy multiplication preserves coefficientwise binomiality. -/
theorem mul
    (hf : MBExpr f)
    (hg : MBExpr g) :
    MBExpr (fun x => f x * g x) := by
  constructor
  intro w
  let xs := w.toList
  have hfamily :
      (fun x : ι → ℤ => (f x * g x) w) =
        fun x =>
          ∑ k ∈ Finset.range (xs.length + 1),
            f x (FreeMonoid.ofList (xs.take k)) *
              g x (FreeMonoid.ofList (xs.drop k)) := by
    funext x
    change convolutionList (f x) (g x) xs = _
    exact convolution_sum_range (f x) (g x) xs
  rw [hfamily]
  apply finsetSum
  intro k _hk
  exact
    (hf.coefficient (FreeMonoid.ofList (xs.take k))).mul
      (hg.coefficient (FreeMonoid.ofList (xs.drop k)))

/-- Natural powers preserve coefficientwise binomiality. -/
theorem pow
    (hf : MBExpr f) :
    ∀ k : ℕ,
      MBExpr (fun x => (f x) ^ k)
  | 0 => by
      simpa using constant (ι := ι) (1 : MSeries ℤ X)
  | k + 1 => by
      simpa [pow_succ] using (pow hf k).mul hf

/-- The nonconstant part of the geometric inverse preserves
coefficientwise binomiality. -/
theorem geometric_neg_sub
    (hf : MBExpr f) :
    MBExpr
      (fun x => geometricInverse (-f x) - 1) := by
  have hneg :
      MBExpr (fun x => -f x) :=
    hf.neg
  constructor
  intro w
  have hfamily :
      (fun x : ι → ℤ => (geometricInverse (-f x) - 1) w) =
        fun x =>
          ∑ k ∈ Finset.range w.length,
            ((-f x) ^ (k + 1)) w := by
    funext x
    change geometricInverse (-f x) w -
        (1 : MSeries ℤ X) w = _
    rw [geometricInverse_apply, Finset.sum_range_succ']
    simp only [pow_zero]
    rw [add_sub_cancel_right]
  rw [hfamily]
  apply finsetSum
  intro k _hk
  exact (hneg.pow (k + 1)).coefficient w

/-- Inversion preserves coefficientwise binomiality for free-group Magnus
differences. -/
theorem magnusDifference_inv
    {x : (ι → ℤ) → FreeGroup X}
    (hx :
      MBExpr
        (fun z => magnusDifference (R := ℤ) (x z))) :
    MBExpr
      (fun z => magnusDifference (R := ℤ) (x z)⁻¹) := by
  rw [show
      (fun z => magnusDifference (R := ℤ) (x z)⁻¹) =
        fun z =>
          geometricInverse
              (-magnusDifference (R := ℤ) (x z)) -
            1 by
      funext z
      exact
        MPOrd.magnus_difference_geometric
          (x z)]
  exact hx.geometric_neg_sub

/-- Products preserve coefficientwise binomiality for free-group Magnus
differences. -/
theorem magnusDifference_mul
    {x y : (ι → ℤ) → FreeGroup X}
    (hx :
      MBExpr
        (fun z => magnusDifference (R := ℤ) (x z)))
    (hy :
      MBExpr
        (fun z => magnusDifference (R := ℤ) (y z))) :
    MBExpr
      (fun z => magnusDifference (R := ℤ) (x z * y z)) := by
  have hproduct :
      MBExpr
        (fun z =>
          magnusDifference (R := ℤ) (x z) *
            magnusDifference (R := ℤ) (y z)) :=
    hx.mul hy
  rw [show
      (fun z => magnusDifference (R := ℤ) (x z * y z)) =
        fun z =>
          magnusDifference (R := ℤ) (x z) +
            magnusDifference (R := ℤ) (y z) +
              magnusDifference (R := ℤ) (x z) *
                magnusDifference (R := ℤ) (y z) by
      funext z
      exact MPOrd.magnus_difference_mul (x z) (y z)]
  exact (hx.add hy).add hproduct

/-- An ordered finite product preserves coefficientwise binomiality. -/
theorem magnus_difference_prod
    (xs : List ((ι → ℤ) → FreeGroup X))
    (hxs :
      ∀ x ∈ xs,
        MBExpr
          (fun z => magnusDifference (R := ℤ) (x z))) :
    MBExpr
      (fun z =>
        magnusDifference (R := ℤ)
          ((xs.map fun x => x z).prod)) := by
  induction xs with
  | nil =>
      simpa [magnusDifference] using (zero (X := X) (ι := ι))
  | cons x xs ih =>
      have hx := hxs x (by simp)
      have htail := ih fun y hy => hxs y (by simp [hy])
      simpa only [List.map_cons, List.prod_cons] using
        hx.magnusDifference_mul htail

/-- A fixed free-group element raised to a binomial-expression exponent has
coefficientwise binomial Magnus difference. -/
theorem fixedZPow
    (x : FreeGroup X)
    {exponent : (ι → ℤ) → ℤ}
    (hexponent : IEMap exponent) :
    MBExpr
      (fun z =>
        magnusDifference (R := ℤ) (x ^ exponent z)) := by
  let a := magnusDifference (R := ℤ) x
  have hfamily :
      (fun z =>
        magnusDifference (R := ℤ) (x ^ exponent z)) =
        fun z =>
          MPOrd.integerBinomialSeries (exponent z) a - 1 := by
    funext z
    have hseries :=
      MPOrd.binomial_magnus_difference
        x (exponent z)
    exact congrArg (fun s => s - 1) hseries.symm
  rw [hfamily]
  constructor
  intro w
  have hcoefficientFamily :
      (fun z : ι → ℤ =>
        (MPOrd.integerBinomialSeries (exponent z) a - 1) w) =
        fun z =>
          ∑ k ∈ Finset.range w.length,
            Ring.choose (exponent z) (k + 1) *
              (a ^ (k + 1)) w := by
    funext z
    change MPOrd.integerBinomialSeries (exponent z) a w -
        (1 : MSeries ℤ X) w = _
    rw [MPOrd.integer_binomial_series,
      Finset.sum_range_succ']
    simp only [Ring.choose_zero_right, one_smul, pow_zero]
    rw [add_sub_cancel_right]
    apply Finset.sum_congr rfl
    intro k _hk
    rw [smul_eq_mul]
  rw [hcoefficientFamily]
  apply finsetSum
  intro k _hk
  exact
    (hexponent.choose (k + 1)).mul
      (binomial_expression_const ((a ^ (k + 1)) w))

/-- Every integer-linear functional of one homogeneous Magnus degree
inherits coefficientwise binomiality. -/
theorem linear_homogeneous_part
    [Fintype X] [Encodable X]
    {degree : ℕ}
    (hf : MBExpr f)
    (L :
      AssociativeHomogeneousWords ℤ X degree →ₗ[ℤ] ℤ) :
    IEMap
      (fun z => L (homogeneousPart degree (f z))) := by
  letI : Fintype (AssociativeWordsLength X degree) :=
    Fintype.ofFinite _
  let b :=
    associativeHomogeneousWords ℤ X degree
  have hrepr :
      ∀ (p : AssociativeHomogeneousWords ℤ X degree)
        (w : AssociativeWordsLength X degree),
        b.repr p w = p.1 w.1 := by
    intro p w
    change
      (Finsupp.supportedEquivFinsupp
        (R := ℤ) {w : FreeMonoid X | w.length = degree}) p w =
      p.1 w.1
    rfl
  have hfamily :
      (fun z => L (homogeneousPart degree (f z))) =
        fun z =>
          ∑ w : AssociativeWordsLength X degree,
            (homogeneousPart degree (f z)).1 w.1 *
              L (b w) := by
    funext z
    let p := homogeneousPart degree (f z)
    calc
      L p =
          L (∑ w, (b.repr p w) • b w) := by
            rw [b.sum_repr]
      _ =
          ∑ w, (b.repr p w) * L (b w) := by
            simp only [map_sum, map_smul, smul_eq_mul]
      _ =
          ∑ w, p.1 w.1 * L (b w) := by
            apply Finset.sum_congr rfl
            intro w _hw
            rw [hrepr]
  rw [hfamily]
  apply finsetSum
  intro w _hw
  have hcoefficient :
      IEMap
        (fun z =>
          (homogeneousPart degree (f z)).1 w.1) := by
    simpa only [homogeneousPart_apply, w.2] using
      hf.coefficient w.1
  exact
    hcoefficient.mul
      (binomial_expression_const (L (b w)))

end MBExpr

/-- A fixed-weight standard Hall block with binomial-expression exponents has
coefficientwise binomial Magnus difference. -/
theorem standard_magnus_expression
    {ι : Type v}
    (t weight : ℕ)
    (e :
      (ι → ℤ) →
        (standardHallFamily.{u} t weight).index → ℤ)
    (he :
      ∀ j,
        IEMap (fun x => e x j)) :
    MBExpr
      (fun x =>
        magnusDifference (R := ℤ)
          (freeStandardProduct t weight (e x))) := by
  let indices :=
    Finset.univ.sort
      fun i j : (standardHallFamily.{u} t weight).index => i ≤ j
  let factors : List ((ι → ℤ) → FreeGroup (FreeGenerator.{u} t)) :=
    indices.map fun j x =>
      ((standardHallFamily.{u} t weight).commutator j
        |>.eval_in_freegroup) ^ e x j
  have hfactor :
      ∀ factor ∈ factors,
        MBExpr
          (fun x => magnusDifference (R := ℤ) (factor x)) := by
    intro factor hfactorMem
    rcases List.mem_map.mp hfactorMem with ⟨j, _hj, rfl⟩
    exact
      MBExpr.fixedZPow
        ((standardHallFamily.{u} t weight).commutator j
          |>.eval_in_freegroup)
        (he j)
  have hproduct :=
    MBExpr.magnus_difference_prod
      factors hfactor
  simpa [factors, indices, freeStandardProduct,
    freeStandardTerm, SubmonoidClass.coe_list_prod,
    List.map_map] using hproduct

/-- An ordered standard Hall prefix with coefficientwise binomial exponents
has coefficientwise binomial Magnus difference. -/
theorem magnus_binomial_expression
    {ι : Type v}
    (t k : ℕ)
    (e : (ι → ℤ) → StandardExponentFamily.{u} t)
    (he :
      ∀ weight,
        1 ≤ weight →
          weight ≤ k →
            ∀ j,
              IEMap
                (fun x => e x weight j)) :
    MBExpr
      (fun x =>
        magnusDifference (R := ℤ)
          (freeStandardPrefix t (e x) k)) := by
  let factors : List ((ι → ℤ) → FreeGroup (FreeGenerator.{u} t)) :=
    (List.range k).map fun j x =>
      freeStandardProduct t (j + 1) (e x (j + 1))
  have hfactor :
      ∀ factor ∈ factors,
        MBExpr
          (fun x => magnusDifference (R := ℤ) (factor x)) := by
    intro factor hfactorMem
    rcases List.mem_map.mp hfactorMem with ⟨j, hj, rfl⟩
    apply
      standard_magnus_expression
        t (j + 1) (fun x => e x (j + 1))
    intro i
    exact he (j + 1) (by omega) (by
      simp only [List.mem_range] at hj
      omega) i
  have hproduct :=
    MBExpr.magnus_difference_prod
      factors hfactor
  simpa [factors, freeStandardPrefix,
    List.map_map] using hproduct

/-- Coefficientwise binomial Magnus dependence implies binomial standard Hall
coordinates, by the same weight-by-weight Magnus extraction used for Lemma
H2. -/
theorem standard_expression_magnus
    {ι : Type v}
    (t n : ℕ)
    (hn : 2 ≤ n)
    (yFree : (ι → ℤ) → FreeGroup (FreeGenerator.{u} t))
    (hy :
      MBExpr
        (fun x =>
          magnusDifference (R := ℤ) (yFree x))) :
    ∀ weight : ℕ,
      1 ≤ weight →
        weight < n →
          ∀ j : (standardHallFamily.{u} t weight).index,
            IEMap
              (fun x =>
                standardHallCoordinates t n hn
                    (lowerCentralTruncation
                      (FreeGroup (FreeGenerator.{u} t)) n (yFree x))
                    weight j) := by
  let yTrunc :
      (ι → ℤ) →
        LowerCentralTruncation
          (FreeGroup (FreeGenerator.{u} t)) n :=
    fun x =>
      lowerCentralTruncation
        (FreeGroup (FreeGenerator.{u} t)) n (yFree x)
  let coordinates :
      (ι → ℤ) → StandardExponentFamily.{u} t :=
    fun x => standardHallCoordinates t n hn (yTrunc x)
  have hcoordinatesEvaluate :
      ∀ x,
        standardHallProduct t n (coordinates x) =
          lowerCentralTruncation
            (FreeGroup (FreeGenerator.{u} t)) n (yFree x) := by
    intro x
    exact standard_product_coordinates
      t n hn (yTrunc x)
  have hcoordinateExpression :
      ∀ weight : ℕ,
        1 ≤ weight →
          weight < n →
            ∀ j : (standardHallFamily.{u} t weight).index,
              IEMap
                (fun x => coordinates x weight j) := by
    intro weight
    induction weight using Nat.strong_induction_on with
    | h weight ih =>
        intro hweight hweightn j
        have hprefix :
            MBExpr
              (fun x =>
                magnusDifference (R := ℤ)
                  (freeStandardPrefix
                    t (coordinates x) (weight - 1))) := by
          apply
            magnus_binomial_expression
              t (weight - 1) coordinates
          intro earlier hearlier hearlierLe earlierIndex
          exact ih earlier (by omega)
            hearlier (by omega) earlierIndex
        have hresidual :
            MBExpr
              (fun x =>
                magnusDifference (R := ℤ)
                  ((freeStandardPrefix
                      t (coordinates x) (weight - 1))⁻¹ *
                    yFree x)) :=
          hprefix.magnusDifference_inv.magnusDifference_mul hy
        let L :
            AssociativeHomogeneousWords
                ℤ (FreeGenerator.{u} t) weight →ₗ[ℤ] ℤ :=
          HMCoord.linearMap j.down
        have hexpression :=
          hresidual.linear_homogeneous_part L
        have hread :
            (fun x =>
              L (homogeneousPart weight
                (magnusDifference (R := ℤ)
                  ((freeStandardPrefix
                      t (coordinates x) (weight - 1))⁻¹ *
                    yFree x)))) =
              fun x => coordinates x weight j := by
          funext x
          have hresidualMem :
              (freeStandardPrefix
                    t (coordinates x) (weight - 1))⁻¹ *
                  yFree x ∈
                Subgroup.lowerCentralSeries
                  (FreeGroup (FreeGenerator.{u} t))
                  (weight - 1) :=
            free_standard_series
              t n (weight - 1) (by omega)
              (coordinates x) (yFree x)
              (hcoordinatesEvaluate x)
          calc
            L (homogeneousPart weight
                (magnusDifference (R := ℤ)
                  ((freeStandardPrefix
                      t (coordinates x) (weight - 1))⁻¹ *
                    yFree x))) =
                (HallTree.freePBWUniqueness
                    (IMagnus.hallPBWInput
                      (X := FreeGenerator.{u} t)) hweight).repr
                  (lowerCentralWeight hresidualMem) j.down := by
                    exact
                      HMCoord.linear_lower_class
                        hweight hresidualMem j.down
            _ = coordinates x weight j :=
              free_standard_coordinate
                t n weight hweight hweightn
                (coordinates x) (yFree x)
                (hcoordinatesEvaluate x)
                hresidualMem j
        rw [hread] at hexpression
        exact hexpression
  simpa [coordinates, yTrunc] using hcoordinateExpression

/-- Variables for two standard Hall exponent families. -/
abbrev StandardBinaryAddress (d : ℕ) :=
  Fin 2 × HEAddres (standardHallFamily.{u} d)

/-- Read one of two standard Hall exponent families from a single variable
assignment. -/
def standardBinaryFamily
    (d : ℕ)
    (side : Fin 2)
    (x : StandardBinaryAddress.{u} d → ℤ) :
    StandardExponentFamily.{u} d :=
  fun weight i => x (side, ⟨weight, i⟩)

/-- At every cutoff, each standard Hall coordinate of a product of two
standard Hall normal forms is a compositional binomial expression in the two
input standard Hall exponent families. -/
theorem standard_multiplication_expression
    {d n weight : ℕ}
    (hn : 2 ≤ n)
    (hweight : 1 ≤ weight)
    (hweightn : weight < n)
    (i : (standardHallFamily.{u} d weight).index) :
    IEMap
      (fun x : StandardBinaryAddress.{u} d → ℤ =>
        standardHallCoordinates d n hn
          (standardHallProduct d n
              (standardBinaryFamily d 0 x) *
            standardHallProduct d n
              (standardBinaryFamily d 1 x))
          weight i) := by
  let left :
      (StandardBinaryAddress.{u} d → ℤ) →
        StandardExponentFamily.{u} d :=
    fun x => standardBinaryFamily d 0 x
  let right :
      (StandardBinaryAddress.{u} d → ℤ) →
        StandardExponentFamily.{u} d :=
    fun x => standardBinaryFamily d 1 x
  let leftFree :
      (StandardBinaryAddress.{u} d → ℤ) →
        FreeGroup (FreeGenerator.{u} d) :=
    fun x => freeStandardPrefix d (left x) (n - 1)
  let rightFree :
      (StandardBinaryAddress.{u} d → ℤ) →
        FreeGroup (FreeGenerator.{u} d) :=
    fun x => freeStandardPrefix d (right x) (n - 1)
  have hleft :
      MBExpr
        (fun x =>
          magnusDifference (R := ℤ) (leftFree x)) := by
    apply
      magnus_binomial_expression
        d (n - 1) left
    intro s _hs _hsn j
    simpa [left, standardBinaryFamily] using
      binomial_expression
        ((0 : Fin 2), (⟨s, j⟩ :
          HEAddres (standardHallFamily.{u} d)))
  have hright :
      MBExpr
        (fun x =>
          magnusDifference (R := ℤ) (rightFree x)) := by
    apply
      magnus_binomial_expression
        d (n - 1) right
    intro s _hs _hsn j
    simpa [right, standardBinaryFamily] using
      binomial_expression
        ((1 : Fin 2), (⟨s, j⟩ :
          HEAddres (standardHallFamily.{u} d)))
  have hcoordinate :=
    standard_expression_magnus
      d n hn
      (fun x => leftFree x * rightFree x)
      (hleft.magnusDifference_mul hright)
      weight hweight hweightn i
  have hleftMap :
      ∀ x,
        lowerCentralTruncation
            (FreeGroup (FreeGenerator.{u} d)) n (leftFree x) =
          standardHallProduct d n
            (standardBinaryFamily d 0 x) := by
    intro x
    simpa [leftFree, left, standardHallProduct] using
      truncation_standard_prefix
        d n (n - 1) (standardBinaryFamily d 0 x)
  have hrightMap :
      ∀ x,
        lowerCentralTruncation
            (FreeGroup (FreeGenerator.{u} d)) n (rightFree x) =
          standardHallProduct d n
            (standardBinaryFamily d 1 x) := by
    intro x
    simpa [rightFree, right, standardHallProduct] using
      truncation_standard_prefix
        d n (n - 1) (standardBinaryFamily d 1 x)
  convert hcoordinate using 1
  funext x
  rw [map_mul, hleftMap, hrightMap]

/-- Explicit expression form of the arbitrary-cutoff standard Hall
multiplication-coordinate theorem. -/
theorem multiplication_coordinate_expression
    {d n weight : ℕ}
    (hn : 2 ≤ n)
    (hweight : 1 ≤ weight)
    (hweightn : weight < n)
    (i : (standardHallFamily.{u} d weight).index) :
    ∃ p : BExpr (StandardBinaryAddress.{u} d),
      ∀ x,
        BExpr.eval x p =
          standardHallCoordinates d n hn
            (standardHallProduct d n
                (standardBinaryFamily d 0 x) *
              standardHallProduct d n
                (standardBinaryFamily d 1 x))
            weight i :=
  standard_multiplication_expression
    hn hweight hweightn i

/-- The arbitrary-cutoff multiplication expression evaluated on two supplied
standard Hall exponent families. -/
theorem multiplication_binomial_expression
    {d n weight : ℕ}
    (hn : 2 ≤ n)
    (hweight : 1 ≤ weight)
    (hweightn : weight < n)
    (i : (standardHallFamily.{u} d weight).index) :
    ∃ p : BExpr (StandardBinaryAddress.{u} d),
      ∀ e f : StandardExponentFamily.{u} d,
        BExpr.eval
            (fun address =>
              if address.1 = (0 : Fin 2) then
                e address.2.1 address.2.2
              else
                f address.2.1 address.2.2)
            p =
          standardHallCoordinates d n hn
            (standardHallProduct d n e *
              standardHallProduct d n f)
            weight i := by
  obtain ⟨p, hp⟩ :=
    multiplication_coordinate_expression
      hn hweight hweightn i
  refine ⟨p, ?_⟩
  intro e f
  let x : StandardBinaryAddress.{u} d → ℤ :=
    fun address =>
      if address.1 = (0 : Fin 2) then
        e address.2.1 address.2.2
      else
        f address.2.1 address.2.2
  have hleft :
      standardBinaryFamily d 0 x = e := by
    funext s j
    simp [standardBinaryFamily, x]
  have hright :
      standardBinaryFamily d 1 x = f := by
    funext s j
    simp [standardBinaryFamily, x]
  simpa [x, hleft, hright] using hp x

/-- Read one standard Hall exponent family from variables indexed by Hall
addresses. -/
def standardExponentVariables
    (d : ℕ)
    (x : HEAddres (standardHallFamily.{u} d) → ℤ) :
    StandardExponentFamily.{u} d :=
  fun weight i => x ⟨weight, i⟩

/-- At every cutoff, each standard Hall coordinate of the inverse of a
standard Hall normal form is a compositional binomial expression in its
standard Hall exponents. -/
theorem standard_binomial_expression
    {d n weight : ℕ}
    (hn : 2 ≤ n)
    (hweight : 1 ≤ weight)
    (hweightn : weight < n)
    (i : (standardHallFamily.{u} d weight).index) :
    IEMap
      (fun x : HEAddres (standardHallFamily.{u} d) → ℤ =>
        standardHallCoordinates d n hn
          (standardHallProduct d n
            (standardExponentVariables d x))⁻¹
          weight i) := by
  let exponent :
      (HEAddres (standardHallFamily.{u} d) → ℤ) →
        StandardExponentFamily.{u} d :=
    fun x => standardExponentVariables d x
  let valueFree :
      (HEAddres (standardHallFamily.{u} d) → ℤ) →
        FreeGroup (FreeGenerator.{u} d) :=
    fun x => freeStandardPrefix d (exponent x) (n - 1)
  have hvalue :
      MBExpr
        (fun x =>
          magnusDifference (R := ℤ) (valueFree x)) := by
    apply
      magnus_binomial_expression
        d (n - 1) exponent
    intro s _hs _hsn j
    simpa [exponent, standardExponentVariables] using
      binomial_expression
        (⟨s, j⟩ : HEAddres (standardHallFamily.{u} d))
  have hcoordinate :=
    standard_expression_magnus
      d n hn
      (fun x => (valueFree x)⁻¹)
      hvalue.magnusDifference_inv
      weight hweight hweightn i
  have hvalueMap :
      ∀ x,
        lowerCentralTruncation
            (FreeGroup (FreeGenerator.{u} d)) n (valueFree x) =
          standardHallProduct d n
            (standardExponentVariables d x) := by
    intro x
    simpa [valueFree, exponent, standardHallProduct] using
      truncation_standard_prefix
        d n (n - 1) (standardExponentVariables d x)
  convert hcoordinate using 1
  funext x
  rw [map_inv, hvalueMap]

/-- Explicit expression form of the arbitrary-cutoff standard Hall inverse
coordinate theorem. -/
theorem coordinate_binomial_expression
    {d n weight : ℕ}
    (hn : 2 ≤ n)
    (hweight : 1 ≤ weight)
    (hweightn : weight < n)
    (i : (standardHallFamily.{u} d weight).index) :
    ∃ p :
        BExpr
          (HEAddres (standardHallFamily.{u} d)),
      ∀ x,
        BExpr.eval x p =
          standardHallCoordinates d n hn
            (standardHallProduct d n
              (standardExponentVariables d x))⁻¹
            weight i :=
  standard_binomial_expression
    hn hweight hweightn i

/-- The arbitrary-cutoff inverse expression evaluated on one supplied
standard Hall exponent family. -/
theorem standard_inverse_expression
    {d n weight : ℕ}
    (hn : 2 ≤ n)
    (hweight : 1 ≤ weight)
    (hweightn : weight < n)
    (i : (standardHallFamily.{u} d weight).index) :
    ∃ p :
        BExpr
          (HEAddres (standardHallFamily.{u} d)),
      ∀ e : StandardExponentFamily.{u} d,
        BExpr.eval
            (fun address => e address.1 address.2)
            p =
          standardHallCoordinates d n hn
            (standardHallProduct d n e)⁻¹
            weight i := by
  obtain ⟨p, hp⟩ :=
    coordinate_binomial_expression
      hn hweight hweightn i
  refine ⟨p, ?_⟩
  intro e
  let x : HEAddres (standardHallFamily.{u} d) → ℤ :=
    fun address => e address.1 address.2
  have hexponent :
      standardExponentVariables d x = e := by
    funext s j
    rfl
  simpa [x, hexponent] using hp x

end

end P1960
end Struik
