import Towers.Algebra.Magnus.UnitriangularMagnus
import Towers.Algebra.Magnus.MagnusHomogeneous
import Towers.Algebra.Magnus.RecursiveWeightedIdeals
import Towers.Algebra.Magnus.WeightedConverse
import Towers.Group.NilpotentProducts.LeafPowering
import Towers.Group.Zassenhaus.ChooseNormalization
import Towers.Group.Zassenhaus.PolynomialPartialSums


/-!
# Magnus coefficient bounds for Struik's Lemma H2

The degree estimate in Lemma H2 is most naturally expressed before Hall
collection.  A family of Magnus series has polynomial order `r` when it
vanishes below degree `r` and its coefficient in degree `s` is an
integer-valued polynomial of degree at most `s - r`.

This file develops the elementary closure properties of that invariant.
-/

namespace Struik
namespace P1960

open EChapma
open EChapma.MSeries
open Towers
open Towers.TBluepr
open Towers.TCTex
open scoped commutatorElement

universe u

/-- A family of Magnus series whose degree-`s` coefficient is polynomial of
degree at most `s - order`, and which has no terms below `order`. -/
structure MPOrd
    {X : Type u}
    (family : ℕ → MSeries ℤ X)
    (order : ℕ) : Prop where
  vanishesBelow :
    ∀ q, VanishesBelow (family q) order
  coefficientPolynomial :
    ∀ w, IVMost
      (fun q : ℕ => family q w)
      (w.length - order)

namespace MPOrd

variable {X : Type u}
variable {f g : ℕ → MSeries ℤ X}
variable {leftOrder rightOrder : ℕ}

noncomputable local instance : DecidableEq X := Classical.decEq X

/-- The zero family has every polynomial order. -/
theorem zero (order : ℕ) :
    MPOrd
      (fun _ : ℕ => (0 : MSeries ℤ X)) order := by
  constructor
  · intro q w hw
    simp
  · intro w
    simpa using IVMost.zero (w.length - order)

/-- Lowering the claimed vanishing order weakens a polynomial-order bound. -/
theorem mono
    {strongOrder weakOrder : ℕ}
    (horder : weakOrder ≤ strongOrder)
    (hf : MPOrd f strongOrder) :
    MPOrd f weakOrder := by
  constructor
  · intro q w hw
    exact hf.vanishesBelow q w (hw.trans_le horder)
  · intro w
    exact (hf.coefficientPolynomial w).mono (by omega)

/-- Sums preserve a common polynomial order. -/
theorem add
    (hf : MPOrd f leftOrder)
    (hg : MPOrd g leftOrder) :
    MPOrd (fun q => f q + g q) leftOrder := by
  constructor
  · intro q w hw
    simp [hf.vanishesBelow q w hw, hg.vanishesBelow q w hw]
  · intro w
    simpa only [MSeries.add_apply, Pi.add_apply] using
      (hf.coefficientPolynomial w).add (hg.coefficientPolynomial w)

/-- Negation preserves polynomial order. -/
theorem neg
    (hf : MPOrd f leftOrder) :
    MPOrd (fun q => -f q) leftOrder := by
  constructor
  · intro q w hw
    simp [hf.vanishesBelow q w hw]
  · intro w
    change IVMost
      (fun q : ℕ => -(f q w)) (w.length - leftOrder)
    rw [show
      (fun q : ℕ => -(f q w)) =
        (-1 : ℤ) • (fun q : ℕ => f q w) by
          funext q
          simp]
    exact IVMost.smul
      (-1) (hf.coefficientPolynomial w)

/-- Differences preserve a common polynomial order. -/
theorem sub
    (hf : MPOrd f leftOrder)
    (hg : MPOrd g leftOrder) :
    MPOrd (fun q => f q - g q) leftOrder := by
  constructor
  · intro q w hw
    simp [hf.vanishesBelow q w hw, hg.vanishesBelow q w hw]
  · intro w
    simpa only [MSeries.sub_apply, Pi.sub_apply] using
      (hf.coefficientPolynomial w).sub (hg.coefficientPolynomial w)

private theorem finsetSum
    {ι : Type*}
    (S : Finset ι)
    (h : ι → ℕ → ℤ)
    (degreeBound : ℕ)
    (hh :
      ∀ i ∈ S,
        IVMost (h i) degreeBound) :
    IVMost
      (fun q : ℕ => ∑ i ∈ S, h i q)
      degreeBound := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      simpa using IVMost.zero degreeBound
  | @insert i S hi ih =>
      have hiPolynomial := hh i (by simp)
      have hSPolynomial := ih fun j hj => hh j (by simp [hj])
      simpa [hi] using hiPolynomial.add hSPolynomial

/-- Cauchy multiplication adds both vanishing orders while preserving the
sharp coefficient degree bound. -/
theorem mul
    (hf : MPOrd f leftOrder)
    (hg : MPOrd g rightOrder) :
    MPOrd
      (fun q => f q * g q)
      (leftOrder + rightOrder) := by
  constructor
  · intro q
    exact vanishes_below_add
      (hf.vanishesBelow q) (hg.vanishesBelow q)
  · intro w
    let xs := w.toList
    have hfamily :
        (fun q : ℕ => (f q * g q) w) =
          fun q : ℕ =>
            ∑ k ∈ Finset.range (xs.length + 1),
              f q (FreeMonoid.ofList (xs.take k)) *
                g q (FreeMonoid.ofList (xs.drop k)) := by
      funext q
      change convolutionList (f q) (g q) xs = _
      exact convolution_sum_range (f q) (g q) xs
    rw [hfamily]
    apply finsetSum
    intro k hk
    have hkle : k ≤ xs.length := by
      simpa only [Finset.mem_range, Nat.lt_add_one_iff] using hk
    let u := FreeMonoid.ofList (xs.take k)
    let v := FreeMonoid.ofList (xs.drop k)
    have huLength : u.length = k := by
      change (xs.take k).length = k
      simp [hkle]
    have hvLength : v.length = xs.length - k := by
      change (xs.drop k).length = xs.length - k
      simp
    by_cases hkleft : k < leftOrder
    · have hzero :
          (fun q : ℕ => f q u * g q v) = 0 := by
        funext q
        rw [hf.vanishesBelow q u (by simpa [huLength])]
        simp
      rw [hzero]
      exact IVMost.zero _
    · have hleft : leftOrder ≤ k := Nat.le_of_not_gt hkleft
      by_cases hkright : xs.length - k < rightOrder
      · have hzero :
            (fun q : ℕ => f q u * g q v) = 0 := by
          funext q
          rw [hg.vanishesBelow q v (by simpa [hvLength])]
          simp
        rw [hzero]
        exact IVMost.zero _
      · have hright : rightOrder ≤ xs.length - k :=
          Nat.le_of_not_gt hkright
        have hproduct :
            IVMost
              (fun q : ℕ => f q u * g q v)
              ((k - leftOrder) +
                ((xs.length - k) - rightOrder)) := by
          simpa only [Pi.mul_apply, huLength, hvLength] using
            (hf.coefficientPolynomial u).mul
              (hg.coefficientPolynomial v)
        exact hproduct.mono (by
          change
            (k - leftOrder) +
                ((xs.length - k) - rightOrder) ≤
              xs.length - (leftOrder + rightOrder)
          omega)

/-- A constant family has polynomial order equal to any vanishing order of
the constant series. -/
theorem constant
    (a : MSeries ℤ X)
    (order : ℕ)
    (ha : VanishesBelow a order) :
    MPOrd (fun _ : ℕ => a) order := by
  constructor
  · intro q
    exact ha
  · intro w
    refine ⟨Polynomial.C (a w : ℚ), ?_, ?_⟩
    · simp
    · intro q
      simp

/-- Powers multiply the polynomial order by the exponent. -/
theorem pow
    (hf : MPOrd f leftOrder) :
    ∀ k : ℕ,
      MPOrd
        (fun q => (f q) ^ k)
        (k * leftOrder)
  | 0 => by
      simpa using constant
        (1 : MSeries ℤ X) 0 (vanishesBelow_zero _)
  | k + 1 => by
      simpa [pow_succ, Nat.succ_mul] using
        (pow hf k).mul hf

/-- Powers multiply an ordinary Magnus vanishing order by the exponent. -/
theorem pow_vanishes_below
    {a : MSeries ℤ X}
    {order : ℕ}
    (ha : VanishesBelow a order) :
    ∀ k : ℕ, VanishesBelow (a ^ k) (k * order)
  | 0 => by
      simpa using vanishesBelow_zero (1 : MSeries ℤ X)
  | k + 1 => by
      rw [pow_succ]
      simpa [Nat.succ_mul] using
        vanishes_below_add (pow_vanishes_below ha k) ha

/-- The nonconstant part of the inverse of `1 + f` has the same polynomial
order as `f`.  The extra hypothesis is the ordinary augmentation condition
that makes the geometric inverse valid coefficientwise. -/
theorem geometric_neg_sub
    (hf : MPOrd f leftOrder) :
    MPOrd
      (fun q => geometricInverse (-f q) - 1)
      leftOrder := by
  have hneg :
      MPOrd (fun q => -f q) leftOrder :=
    hf.neg
  constructor
  · intro q w hw
    by_cases horder : leftOrder = 0
    · subst leftOrder
      exact vanishesBelow_zero _ w hw
    · have horderPos : 0 < leftOrder := Nat.pos_of_ne_zero horder
      change geometricInverse (-f q) w -
          (1 : MSeries ℤ X) w = 0
      rw [geometricInverse_apply, Finset.sum_range_succ']
      simp only [pow_zero]
      rw [add_sub_cancel_right]
      apply Finset.sum_eq_zero
      intro k hk
      exact
        ((hneg.pow (k + 1)).vanishesBelow q w
          (by
            have : leftOrder ≤ (k + 1) * leftOrder := by
              nlinarith
            omega))
  · intro w
    have hfamily :
        (fun q : ℕ => (geometricInverse (-f q) - 1) w) =
          fun q : ℕ =>
            ∑ k ∈ Finset.range w.length,
              ((-f q) ^ (k + 1)) w := by
      funext q
      change geometricInverse (-f q) w -
          (1 : MSeries ℤ X) w = _
      rw [geometricInverse_apply, Finset.sum_range_succ']
      simp only [pow_zero]
      rw [add_sub_cancel_right]
    rw [hfamily]
    apply finsetSum
    intro k hk
    have hpower :=
      (hneg.pow (k + 1)).coefficientPolynomial w
    exact hpower.mono (by
      have horderLe :
          leftOrder ≤ (k + 1) * leftOrder := by
        nlinarith
      omega)

/-- The Magnus difference of an inverse is the nonconstant geometric inverse
of the original Magnus difference. -/
theorem magnus_difference_geometric
    (x : FreeGroup X) :
    magnusDifference (R := ℤ) x⁻¹ =
      geometricInverse (-magnusDifference (R := ℤ) x) - 1 := by
  let a : MSeries ℤ X := magnusDifference (R := ℤ) x
  have haOne : (-a) 1 = 0 := by
    simpa [a] using
      magnus_difference_ideal (R := ℤ) x
  have hseries :
      1 - (-a) = magnusSeries (R := ℤ) x := by
    simp [a, magnusDifference]
  have hleft :
      magnusSeries (R := ℤ) x⁻¹ * (1 - (-a)) = 1 := by
    rw [hseries, ← magnusSeries_mul]
    simp
  have hright :
      (1 - (-a)) * magnusSeries (R := ℤ) x⁻¹ = 1 := by
    rw [hseries, ← magnusSeries_mul]
    simp
  have hinverse :
      magnusSeries (R := ℤ) x⁻¹ =
        geometricInverse (-a) :=
    geometricInverse_unique haOne hleft hright
  simp only [magnusDifference, hinverse, a]

/-- Inversion preserves polynomial order for families of free-group Magnus
differences. -/
theorem magnusDifference_inv
    {x : ℕ → FreeGroup X}
    (hx :
      MPOrd
        (fun q => magnusDifference (R := ℤ) (x q))
        leftOrder) :
    MPOrd
      (fun q => magnusDifference (R := ℤ) (x q)⁻¹)
      leftOrder := by
  rw [show
      (fun q => magnusDifference (R := ℤ) (x q)⁻¹) =
        fun q =>
          geometricInverse
              (-magnusDifference (R := ℤ) (x q)) -
            1 by
      funext q
      exact
        magnus_difference_geometric
          (x q)]
  exact hx.geometric_neg_sub

/-- Exact Magnus-difference formula for a group product. -/
theorem magnus_difference_mul
    (x y : FreeGroup X) :
    magnusDifference (R := ℤ) (x * y) =
      magnusDifference (R := ℤ) x +
        magnusDifference (R := ℤ) y +
          magnusDifference (R := ℤ) x *
            magnusDifference (R := ℤ) y := by
  simp only [magnusDifference, magnusSeries_mul]
  noncomm_ring

/-- Products preserve a common polynomial order for families of free-group
Magnus differences. -/
theorem magnusDifference_mul
    {x y : ℕ → FreeGroup X}
    (hx :
      MPOrd
        (fun q => magnusDifference (R := ℤ) (x q))
        leftOrder)
    (hy :
      MPOrd
        (fun q => magnusDifference (R := ℤ) (y q))
        leftOrder) :
    MPOrd
      (fun q => magnusDifference (R := ℤ) (x q * y q))
      leftOrder := by
  have hproduct :
      MPOrd
        (fun q =>
          magnusDifference (R := ℤ) (x q) *
            magnusDifference (R := ℤ) (y q))
        leftOrder :=
    (hx.mul hy).mono (by omega)
  rw [show
      (fun q => magnusDifference (R := ℤ) (x q * y q)) =
        fun q =>
          magnusDifference (R := ℤ) (x q) +
            magnusDifference (R := ℤ) (y q) +
              magnusDifference (R := ℤ) (x q) *
                magnusDifference (R := ℤ) (y q) by
      funext q
      exact magnus_difference_mul (x q) (y q)]
  exact (hx.add hy).add hproduct

/-- An ordered finite product of free-group families preserves a common
Magnus polynomial order. -/
theorem magnus_difference_prod
    (xs : List (ℕ → FreeGroup X))
    (hxs :
      ∀ x ∈ xs,
        MPOrd
          (fun q => magnusDifference (R := ℤ) (x q))
          leftOrder) :
    MPOrd
      (fun q =>
        magnusDifference (R := ℤ)
          ((xs.map fun x => x q).prod))
      leftOrder := by
  induction xs with
  | nil =>
      simpa [magnusDifference] using
        (zero (X := X) leftOrder)
  | cons x xs ih =>
      have hx := hxs x (by simp)
      have htail := ih fun y hy => hxs y (by simp [hy])
      simpa only [List.map_cons, List.prod_cons] using
        hx.magnusDifference_mul htail

/-- Exact Magnus-difference formula for a group commutator. -/
theorem magnus_difference_commutator
    (x y : FreeGroup X) :
    magnusDifference (R := ℤ) ⁅x, y⁆ =
      ((magnusDifference (R := ℤ) x *
            magnusDifference (R := ℤ) y -
          magnusDifference (R := ℤ) y *
            magnusDifference (R := ℤ) x) *
        magnusSeries (R := ℤ) x⁻¹) *
      magnusSeries (R := ℤ) y⁻¹ := by
  let Xs : MSeries ℤ X := magnusSeries (R := ℤ) x
  let Ys : MSeries ℤ X := magnusSeries (R := ℤ) y
  let Xi : MSeries ℤ X := magnusSeries (R := ℤ) x⁻¹
  let Yi : MSeries ℤ X := magnusSeries (R := ℤ) y⁻¹
  have hXXi : Xs * Xi = 1 := by
    dsimp [Xs, Xi]
    rw [← magnusSeries_mul]
    simp
  have hYYi : Ys * Yi = 1 := by
    dsimp [Ys, Yi]
    rw [← magnusSeries_mul]
    simp
  have hcancel : Ys * Xs * Xi * Yi = 1 := by
    calc
      Ys * Xs * Xi * Yi =
          Ys * (Xs * Xi) * Yi := by
            noncomm_ring
      _ = Ys * 1 * Yi := by rw [hXXi]
      _ = 1 := by simpa using hYYi
  rw [commutatorElement_def]
  simp only [magnusDifference, magnusSeries_mul]
  change
    Xs * Ys * Xi * Yi - 1 =
      (((Xs - 1) * (Ys - 1) -
          (Ys - 1) * (Xs - 1)) * Xi) * Yi
  calc
    Xs * Ys * Xi * Yi - 1 =
        Xs * Ys * Xi * Yi -
          (Ys * Xs * Xi * Yi) := by rw [hcancel]
    _ =
        (((Xs - 1) * (Ys - 1) -
            (Ys - 1) * (Xs - 1)) * Xi) * Yi := by
          noncomm_ring

/-- Commutators add polynomial order for families of free-group Magnus
differences. -/
theorem magnusDifference_commutator
    {x y : ℕ → FreeGroup X}
    (hx :
      MPOrd
        (fun q => magnusDifference (R := ℤ) (x q))
        leftOrder)
    (hy :
      MPOrd
        (fun q => magnusDifference (R := ℤ) (y q))
        rightOrder) :
    MPOrd
      (fun q => magnusDifference (R := ℤ) ⁅x q, y q⁆)
      (leftOrder + rightOrder) := by
  have hxy :
      MPOrd
        (fun q =>
          magnusDifference (R := ℤ) (x q) *
            magnusDifference (R := ℤ) (y q))
        (leftOrder + rightOrder) :=
    hx.mul hy
  have hyx :
      MPOrd
        (fun q =>
          magnusDifference (R := ℤ) (y q) *
            magnusDifference (R := ℤ) (x q))
        (leftOrder + rightOrder) := by
    simpa [Nat.add_comm] using hy.mul hx
  have hbracket :
      MPOrd
        (fun q =>
          magnusDifference (R := ℤ) (x q) *
                magnusDifference (R := ℤ) (y q) -
            magnusDifference (R := ℤ) (y q) *
                magnusDifference (R := ℤ) (x q))
        (leftOrder + rightOrder) :=
    hxy.sub hyx
  have hone :
      MPOrd
        (fun _ : ℕ => (1 : MSeries ℤ X)) 0 :=
    constant 1 0 (vanishesBelow_zero _)
  have hxInvDifference :
      MPOrd
        (fun q =>
          magnusDifference (R := ℤ) (x q)⁻¹)
        leftOrder :=
    hx.magnusDifference_inv
  have hyInvDifference :
      MPOrd
        (fun q =>
          magnusDifference (R := ℤ) (y q)⁻¹)
        rightOrder :=
    hy.magnusDifference_inv
  have hxInvSeries :
      MPOrd
        (fun q => magnusSeries (R := ℤ) (x q)⁻¹) 0 := by
    rw [show
        (fun q => magnusSeries (R := ℤ) (x q)⁻¹) =
          fun q =>
            1 + magnusDifference (R := ℤ) (x q)⁻¹ by
        funext q
        simp [magnusDifference]]
    exact hone.add (hxInvDifference.mono (Nat.zero_le _))
  have hyInvSeries :
      MPOrd
        (fun q => magnusSeries (R := ℤ) (y q)⁻¹) 0 := by
    rw [show
        (fun q => magnusSeries (R := ℤ) (y q)⁻¹) =
          fun q =>
            1 + magnusDifference (R := ℤ) (y q)⁻¹ by
        funext q
        simp [magnusDifference]]
    exact hone.add (hyInvDifference.mono (Nat.zero_le _))
  rw [show
      (fun q => magnusDifference (R := ℤ) ⁅x q, y q⁆) =
        fun q =>
          ((magnusDifference (R := ℤ) (x q) *
                magnusDifference (R := ℤ) (y q) -
              magnusDifference (R := ℤ) (y q) *
                magnusDifference (R := ℤ) (x q)) *
            magnusSeries (R := ℤ) (x q)⁻¹) *
          magnusSeries (R := ℤ) (y q)⁻¹ by
      funext q
      exact magnus_difference_commutator (x q) (y q)]
  simpa using (hbracket.mul hxInvSeries).mul hyInvSeries

/-- Powers of a one-variable series are delta series on the repeated word. -/
theorem variable_series_word
    (a : X) :
    ∀ k : ℕ,
      (variableSeries (R := ℤ) a) ^ k =
        wordSeries (R := ℤ) ((FreeMonoid.of a) ^ k)
  | 0 => by
      simp
  | k + 1 => by
      rw [pow_succ, variable_series_word a k,
        variable_series, wordSeries_mul, pow_succ]

/-- The repeated one-letter word has length equal to its exponent. -/
theorem length_of_pow
    (a : X) :
    ∀ k : ℕ, ((FreeMonoid.of a) ^ k).length = k
  | 0 => by simp
  | k + 1 => by
      rw [pow_succ, FreeMonoid.length_mul, length_of_pow a k]
      simp

/-- Exact coefficient formula for the Magnus difference of a powered free
generator. -/
theorem magnus_difference_pow
    (a : X) (q : ℕ) (w : FreeMonoid X) :
    magnusDifference (R := ℤ) (FreeGroup.of a ^ q) w =
      if 1 ≤ w.length ∧
          w = (FreeMonoid.of a) ^ w.length then
        (Nat.choose q w.length : ℤ)
      else
        0 := by
  classical
  have hdiff :
      magnusDifference (R := ℤ) (FreeGroup.of a ^ q) =
        MAFilt.powerConditionTail q
          (variableSeries (R := ℤ) a) := by
    calc
      magnusDifference (R := ℤ) (FreeGroup.of a ^ q) =
          magnusSeries (R := ℤ) (FreeGroup.of a) ^ q - 1 := by
            simp [magnusDifference, map_pow, magnusSeries,
              magnusUnitHom]
      _ = (1 + variableSeries (R := ℤ) a) ^ q - 1 := by
            rw [magnusSeries_of]
      _ =
          MAFilt.powerConditionTail q
            (variableSeries (R := ℤ) a) :=
        MAFilt.sub_condition_tail
          q (variableSeries (R := ℤ) a)
  rw [hdiff]
  simp only [MAFilt.powerConditionTail,
    sum_apply_series, nsmul_apply, variable_series_word,
    wordSeries_apply]
  by_cases hwpos : 1 ≤ w.length
  · have hsubadd : w.length - 1 + 1 = w.length := by
      omega
    by_cases hselected : w.length - 1 ∈ Finset.range q
    · rw [Finset.sum_eq_single (w.length - 1)]
      · simp [hsubadd, hwpos]
      · intro k hk hkne
        have hwordNe :
            w ≠ (FreeMonoid.of a) ^ (k + 1) := by
          intro heq
          have hlength := congrArg FreeMonoid.length heq
          rw [length_of_pow a] at hlength
          omega
        simp [hwordNe]
      · exact fun hnot => (hnot hselected).elim
    · have hqlt : q < w.length := by
        simp only [Finset.mem_range] at hselected
        omega
      have hchoose : Nat.choose q w.length = 0 :=
        Nat.choose_eq_zero_of_lt hqlt
      simp only [hchoose, Int.ofNat_zero, ite_self]
      apply Finset.sum_eq_zero
      intro k hk
      have hkne : k ≠ w.length - 1 := by
        intro heq
        subst k
        exact hselected hk
      have hwordNe :
          w ≠ (FreeMonoid.of a) ^ (k + 1) := by
        intro heq
        have hlength := congrArg FreeMonoid.length heq
        rw [length_of_pow a] at hlength
        omega
      simp [hwordNe]
  · have hwzero : w.length = 0 := by omega
    have hwone : w = 1 := FreeMonoid.length_eq_zero.mp hwzero
    subst w
    simp only [FreeMonoid.length_one,       ]
    apply Finset.sum_eq_zero
    intro k hk
    have hwordNe :
        (1 : FreeMonoid X) ≠
          (FreeMonoid.of a) ^ (k + 1) := by
      intro heq
      have hlength := congrArg FreeMonoid.length heq
      rw [FreeMonoid.length_one, length_of_pow a] at hlength
      omega
    simp [hwordNe]

/-- The powered-generator family has polynomial order zero. -/
theorem poweredGenerator
    (a : X) :
    MPOrd
      (fun q =>
        magnusDifference (R := ℤ) (FreeGroup.of a ^ q))
      0 := by
  constructor
  · intro q
    exact vanishesBelow_zero _
  · intro w
    rw [show
        (fun q =>
          magnusDifference (R := ℤ) (FreeGroup.of a ^ q) w) =
          fun q =>
            if 1 ≤ w.length ∧
                w = (FreeMonoid.of a) ^ w.length then
              (Nat.choose q w.length : ℤ)
            else
              0 by
        funext q
        exact magnus_difference_pow a q w]
    by_cases hw :
        1 ≤ w.length ∧
          w = (FreeMonoid.of a) ^ w.length
    · simp only [if_pos hw, Nat.sub_zero]
      exact
        ⟨natChoosePolynomial w.length,
          degree_choose_polynomial w.length,
          fun q => by
            simpa using eval_nat_choose q w.length⟩
    · simp only [if_neg hw]
      exact IVMost.zero _

/-- The ordinary evaluation of a Hall tree has Magnus order at least its
physical weight. -/
theorem tree_vanishes_below
    (tree : HallTree X) :
    VanishesBelow
      (magnusDifference (R := ℤ)
        (tree.toCWord.eval FreeGroup.of))
      tree.weight := by
  induction tree with
  | atom a =>
      simpa [HallTree.toCWord] using
        (magnus_vanishes_below
          (R := ℤ) (FreeGroup.of a))
  | commutator left right hleft hright =>
      simpa [HallTree.toCWord] using
        magnus_difference_vanishes
          hleft hright

/-- Replacing one specified leaf by its `q`th power lowers the polynomial
order of the tree's Magnus difference by exactly one. -/
theorem leafOccurrencePow
    (tree : HallTree X)
    (leaf : HallTree.LOccur tree) :
    MPOrd
      (fun q =>
        magnusDifference (R := ℤ)
          (HallTree.leafOccurrencePow
            FreeGroup.of q tree leaf))
      (tree.weight - 1) := by
  induction leaf with
  | atom a =>
      simpa [HallTree.leafOccurrencePow] using
        poweredGenerator (X := X) a
  | @left left right leaf ih =>
      have hright :
          MPOrd
            (fun _ : ℕ =>
              magnusDifference (R := ℤ)
                (right.toCWord.eval FreeGroup.of))
            right.weight :=
        constant _ right.weight
          (tree_vanishes_below right)
      have hcommutator :=
        ih.magnusDifference_commutator hright
      have horder :
          (left.weight - 1) + right.weight =
            (left.weight + right.weight) - 1 := by
        have := left.weight_pos
        omega
      simpa only [HallTree.leafOccurrencePow,
        HallTree.weight_commutator, horder] using hcommutator
  | @right left right leaf ih =>
      have hleft :
          MPOrd
            (fun _ : ℕ =>
              magnusDifference (R := ℤ)
                (left.toCWord.eval FreeGroup.of))
            left.weight :=
        constant _ left.weight
          (tree_vanishes_below left)
      have hcommutator :=
        hleft.magnusDifference_commutator ih
      have horder :
          left.weight + (right.weight - 1) =
            (left.weight + right.weight) - 1 := by
        have := right.weight_pos
        omega
      simpa only [HallTree.leafOccurrencePow,
        HallTree.weight_commutator, horder] using hcommutator

/-- Every integer-linear functional of one homogeneous Magnus degree inherits
the coefficientwise polynomial bound. -/
theorem linear_homogeneous_part
    [Fintype X] [Encodable X]
    {degree : ℕ}
    (hf : MPOrd f leftOrder)
    (L :
      AssociativeHomogeneousWords ℤ X degree →ₗ[ℤ] ℤ) :
    IVMost
      (fun q => L (homogeneousPart degree (f q)))
      (degree - leftOrder) := by
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
      (fun q => L (homogeneousPart degree (f q))) =
        fun q =>
          ∑ w : AssociativeWordsLength X degree,
            (homogeneousPart degree (f q)).1 w.1 *
              L (b w) := by
    funext q
    let p := homogeneousPart degree (f q)
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
            intro w hw
            rw [hrepr]
  rw [hfamily]
  apply finsetSum
  intro w hw
  have hcoefficient :
      IVMost
        (fun q =>
          (homogeneousPart degree (f q)).1 w.1)
        (degree - leftOrder) := by
    simpa only [homogeneousPart_apply, w.2] using
      hf.coefficientPolynomial w.1
  have hscaled :=
    IVMost.smul (L (b w)) hcoefficient
  simpa [mul_comm] using hscaled

/-- The degree-`m` part of the Magnus difference of an element in `γ_m` is
the homogeneous realization of its lower-central class. -/
theorem homogeneous_part_magnus
    [Fintype X] [Encodable X]
    {m : ℕ}
    (hm : 0 < m)
    {g : FreeGroup X}
    (hg :
      g ∈ Subgroup.lowerCentralSeries (FreeGroup X) (m - 1)) :
    homogeneousPart m (magnusDifference (R := ℤ) g) =
      (ICokern.homogeneousRealizationLinear
        (X := X) m).symm
        (Submodule.Quotient.mk
          (lowerRepWeight hm hg)) := by
  apply
    (Finsupp.supportedEquivFinsupp
      (R := ℤ) {w : FreeMonoid X | w.length = m}).injective
  ext w
  change
    (homogeneousPart m (magnusDifference (R := ℤ) g)).1 w.1 =
      ((ICokern.homogeneousRealizationLinear
        (X := X) m).symm
        (Submodule.Quotient.mk
          (lowerRepWeight hm hg))).1 w.1
  rw [homogeneousPart_apply,
    homogeneous_realization_magnus,
    magnus_rep_weight hm hg]

/-- The homogeneous Magnus functional which reads the coefficient of one
singleton Hall basis vector in the augmentation PBW basis. -/
noncomputable def magnusCoordinateLinear
    [Fintype X] [Encodable X]
    {m : ℕ}
    (j : HallTree.BasicIndex (α := X) m) :
    AssociativeHomogeneousWords ℤ X m →ₗ[ℤ] ℤ :=
  (Finsupp.lapply
      (ICokern.basicSingletonSequence j)).comp
    (((ICokern.augmentationPBWBasis
      (X := X) m).repr).toLinearMap.comp
      (ICokern.homogeneousRealizationLinear
        (X := X) m).toLinearMap)

/-- On a lower-central element, the singleton PBW functional reads its
coordinate in the canonical Hall basis of that graded layer. -/
theorem magnus_linear_class
    [Fintype X] [Encodable X]
    {m : ℕ}
    (hm : 0 < m)
    {g : FreeGroup X}
    (hg :
      g ∈ Subgroup.lowerCentralSeries (FreeGroup X) (m - 1))
    (j : HallTree.BasicIndex (α := X) m) :
    magnusCoordinateLinear j
        (homogeneousPart m (magnusDifference (R := ℤ) g)) =
      (HallTree.freePBWUniqueness
          (IMagnus.hallPBWInput (X := X)) hm).repr
        (lowerCentralWeight hg) j := by
  let lowerBasis :=
    HallTree.freePBWUniqueness
      (IMagnus.hallPBWInput (X := X)) hm
  let augmentationBasis :=
    ICokern.augmentationPBWBasis (X := X) m
  let magnusMap :=
    HallTree.freeMagnusInt X hm
  have hsingleton :
      Function.Injective
        (ICokern.basicSingletonSequence
          (X := X) (n := m)) := by
    intro i k hik
    apply HallTree.indexed_tree_injective
    apply List.singleton_injective
    exact congrArg Subtype.val hik
  have hmappedBasis :
      ∀ i,
        magnusMap (lowerBasis i) =
          augmentationBasis
            (ICokern.basicSingletonSequence i) := by
    intro i
    have hlower :
        lowerBasis i =
          (HallTree.indexedBasicTree i).freeLowerWeight
            (HallTree.indexed_tree_weight i) := by
      simp only [lowerBasis,
        HallTree.freePBWUniqueness,
        Module.Basis.mk_apply]
    rw [hlower]
    exact
      (ICokern.pbw_singleton_sequence
        (X := X) hm i).symm
  have hcoordinateMap :
      (augmentationBasis.coord
          (ICokern.basicSingletonSequence j)).comp magnusMap =
        lowerBasis.coord j := by
    apply lowerBasis.ext
    intro i
    rw [LinearMap.comp_apply, hmappedBasis]
    simp only [Module.Basis.coord_apply, Module.Basis.repr_self,
      ]
    by_cases hij : i = j
    · subst i
      simp
    · have hsingletonNe :
          ICokern.basicSingletonSequence i ≠
            ICokern.basicSingletonSequence j :=
        fun h => hij (hsingleton h)
      simp [hsingletonNe, hij]
  rw [homogeneous_part_magnus hm hg]
  simp only [magnusCoordinateLinear, LinearMap.comp_apply,
    LinearEquiv.coe_toLinearMap, LinearEquiv.apply_symm_apply,
    Finsupp.lapply_apply]
  have hclassMap :=
    free_magnus_class
      hm hg
  change
    augmentationBasis.coord
        (ICokern.basicSingletonSequence j)
        (Submodule.Quotient.mk
          (lowerRepWeight hm hg)) =
      lowerBasis.coord j (lowerCentralWeight hg)
  rw [← hclassMap]
  exact LinearMap.congr_fun hcoordinateMap (lowerCentralWeight hg)

/-- The finite generalized-binomial partial sum in one augmentation series. -/
def integerBinomialPartial
    (z : ℤ)
    (a : MSeries ℤ X)
    (N : ℕ) :
    MSeries ℤ X :=
  ∑ k ∈ Finset.range N, Ring.choose z k • a ^ k

theorem binomial_partial_succ
    (z : ℤ)
    (a : MSeries ℤ X)
    (N : ℕ) :
    integerBinomialPartial z a (N + 1) =
      integerBinomialPartial z a N +
        Ring.choose z N • a ^ N := by
  simp [integerBinomialPartial, Finset.sum_range_succ]

/-- Pascal recurrence for generalized-binomial partial sums. -/
theorem binomial_partial_add
    (z : ℤ)
    (a : MSeries ℤ X) :
    ∀ N : ℕ,
      integerBinomialPartial z a (N + 1) * (1 + a) =
        integerBinomialPartial (z + 1) a (N + 1) +
          Ring.choose z N • a ^ (N + 1)
  | 0 => by
      simp [integerBinomialPartial]
  | N + 1 => by
      calc
        integerBinomialPartial z a (N + 1 + 1) * (1 + a) =
            (integerBinomialPartial z a (N + 1) +
                Ring.choose z (N + 1) • a ^ (N + 1)) *
              (1 + a) := by
                rw [binomial_partial_succ]
        _ =
            integerBinomialPartial z a (N + 1) * (1 + a) +
              Ring.choose z (N + 1) •
                (a ^ (N + 1) * (1 + a)) := by
                  rw [EChapma.MSeries.add_mul,
                    zsmul_eq_mul, zsmul_eq_mul,
                    EChapma.MSeries.mul_assoc]
        _ =
            (integerBinomialPartial (z + 1) a (N + 1) +
                Ring.choose z N • a ^ (N + 1)) +
              Ring.choose z (N + 1) •
                (a ^ (N + 1) + a ^ (N + 1 + 1)) := by
                  rw [binomial_partial_add z a N,
                    EChapma.MSeries.mul_add,
                    EChapma.MSeries.mul_one, ← pow_succ]
        _ =
            integerBinomialPartial (z + 1) a (N + 1 + 1) +
              Ring.choose z (N + 1) • a ^ (N + 1 + 1) := by
                have hpartial :
                    integerBinomialPartial (z + 1) a (N + 1 + 1) =
                      integerBinomialPartial (z + 1) a (N + 1) +
                        Ring.choose (z + 1) (N + 1) •
                          a ^ (N + 1) :=
                  binomial_partial_succ (z + 1) a (N + 1)
                rw [hpartial, Ring.choose_succ_succ]
                simp only [add_smul, smul_add]
                abel

/-- The coefficientwise generalized binomial series. -/
def integerBinomialSeries
    (z : ℤ)
    (a : MSeries ℤ X) :
    MSeries ℤ X :=
  ⟨fun w =>
    ∑ k ∈ Finset.range (w.length + 1),
      Ring.choose z k • (a ^ k) w⟩

@[simp]
theorem integer_binomial_series
    (z : ℤ)
    (a : MSeries ℤ X)
    (w : FreeMonoid X) :
    integerBinomialSeries z a w =
      ∑ k ∈ Finset.range (w.length + 1),
        Ring.choose z k • (a ^ k) w :=
  rfl

/-- Any sufficiently long partial sum computes a fixed word coefficient of
the generalized binomial series. -/
theorem integer_binomial_partial
    {a : MSeries ℤ X}
    (ha : a 1 = 0)
    (z : ℤ)
    {N : ℕ}
    {w : FreeMonoid X}
    (hw : w.length < N) :
    integerBinomialSeries z a w =
      integerBinomialPartial z a N w := by
  rw [integer_binomial_series, integerBinomialPartial,
    sum_apply_series]
  apply Finset.sum_subset (Finset.range_mono (by omega))
  intro k hkN hkSmall
  simp only [Finset.mem_range] at hkN
  have hwk : w.length < k := by
    simpa only [Finset.mem_range, Nat.not_lt] using hkSmall
  rw [pow_vanishesBelow ha k w hwk]
  simp

/-- Multiplication by `1 + a` increments the generalized-binomial exponent. -/
theorem integer_binomial_add
    {a : MSeries ℤ X}
    (ha : a 1 = 0)
    (z : ℤ) :
    integerBinomialSeries z a * (1 + a) =
      integerBinomialSeries (z + 1) a := by
  ext w
  let N := w.length + 1
  let S := integerBinomialPartial z a N
  have hleft :
      (integerBinomialSeries z a * (1 + a)) w =
        (S * (1 + a)) w := by
    apply mul_apply_congr
    · intro v hv
      exact integer_binomial_partial ha z
        (by simp only [N]; omega)
    · intro v hv
      rfl
  rw [hleft]
  rw [show
      S * (1 + a) =
        integerBinomialPartial (z + 1) a N +
          Ring.choose z w.length • a ^ N by
      simpa only [S, N] using
        binomial_partial_add z a w.length]
  rw [MSeries.add_apply]
  have hpowzero :
      (Ring.choose z w.length • a ^ N) w = 0 := by
    rw [MSeries.zsmul_apply,
      pow_vanishesBelow ha N w (by simp [N])]
    simp
  rw [hpowzero, add_zero]
  exact
    (integer_binomial_partial ha (z + 1)
      (by simp only [N]; omega)).symm

/-- The generalized-binomial Magnus series is the actual Magnus expansion of
an arbitrary integer power. -/
theorem binomial_magnus_difference
    (x : FreeGroup X)
    (z : ℤ) :
    integerBinomialSeries z
        (magnusDifference (R := ℤ) x) =
      magnusSeries (R := ℤ) (x ^ z) := by
  let a := magnusDifference (R := ℤ) x
  have ha : a 1 = 0 := by
    exact magnus_difference_ideal x
  have hseries :
      1 + a = magnusSeries (R := ℤ) x := by
    simp [a, magnusDifference]
  induction z using Int.induction_on with
  | zero =>
      ext w
      rw [integer_binomial_series]
      by_cases hw : w = 1
      · subst w
        simp 
      · have hwpos : 0 < w.length := by
          exact Nat.pos_of_ne_zero fun hzero =>
            hw (FreeMonoid.length_eq_zero.mp hzero)
        rw [Finset.sum_eq_single 0]
        · simp [hw]
        · intro k hk hkne
          have hkpos : 0 < k := Nat.pos_of_ne_zero hkne
          rw [Ring.choose_zero_pos ℤ hkpos]
          simp
        · simp
  | succ z ih =>
      rw [← integer_binomial_add ha z, ih,
        hseries, ← magnusSeries_mul, zpow_add_one]
  | pred z ih =>
      let candidate :=
        integerBinomialSeries (-(z : ℤ) - 1) a
      have hcandidate :
          candidate * magnusSeries (R := ℤ) x =
            magnusSeries (R := ℤ) (x ^ (-(z : ℤ))) := by
        have hrec :=
          integer_binomial_add ha (-(z : ℤ) - 1)
        have hexponent :
            -(z : ℤ) - 1 + 1 = -(z : ℤ) := by
          omega
        rw [hexponent] at hrec
        rw [hseries] at hrec
        rw [show
            integerBinomialSeries (-(z : ℤ)) a =
              magnusSeries (R := ℤ) (x ^ (-(z : ℤ))) by
            simpa [a] using ih] at hrec
        exact hrec
      have hactual :
          magnusSeries (R := ℤ) (x ^ (-(z : ℤ) - 1)) *
              magnusSeries (R := ℤ) x =
            magnusSeries (R := ℤ) (x ^ (-(z : ℤ))) := by
        rw [← magnusSeries_mul]
        congr 1
        rw [zpow_sub_one]
        group
      have heq :
          candidate * magnusSeries (R := ℤ) x =
            magnusSeries (R := ℤ) (x ^ (-(z : ℤ) - 1)) *
              magnusSeries (R := ℤ) x :=
        hcandidate.trans hactual.symm
      have hunit :
          magnusSeries (R := ℤ) x *
              magnusSeries (R := ℤ) x⁻¹ = 1 := by
        rw [← magnusSeries_mul]
        simp
      change candidate =
        magnusSeries (R := ℤ) (x ^ (-(z : ℤ) - 1))
      calc
        candidate = candidate * 1 := by simp
        _ =
            candidate *
              (magnusSeries (R := ℤ) x *
                magnusSeries (R := ℤ) x⁻¹) := by rw [hunit]
        _ =
            (candidate * magnusSeries (R := ℤ) x) *
              magnusSeries (R := ℤ) x⁻¹ := by
                rw [EChapma.MSeries.mul_assoc]
        _ =
            (magnusSeries (R := ℤ) (x ^ (-(z : ℤ) - 1)) *
                magnusSeries (R := ℤ) x) *
              magnusSeries (R := ℤ) x⁻¹ := by rw [heq]
        _ =
            magnusSeries (R := ℤ) (x ^ (-(z : ℤ) - 1)) *
              (magnusSeries (R := ℤ) x *
                magnusSeries (R := ℤ) x⁻¹) := by
                  rw [EChapma.MSeries.mul_assoc]
        _ = magnusSeries (R := ℤ) (x ^ (-(z : ℤ) - 1)) := by
              rw [hunit, EChapma.MSeries.mul_one]

/-- A fixed element of physical Magnus order `k`, raised to a signed
polynomial exponent of degree `k - c`, has polynomial order `c`. -/
theorem fixedZPow
    (x : FreeGroup X)
    {physicalOrder offset : ℕ}
    (hx :
      VanishesBelow
        (magnusDifference (R := ℤ) x)
        physicalOrder)
    (hoffset : offset ≤ physicalOrder)
    {exponent : ℕ → ℤ}
    (hexponent :
      IVMost exponent
        (physicalOrder - offset)) :
    MPOrd
      (fun q =>
        magnusDifference (R := ℤ) (x ^ exponent q))
      offset := by
  let a := magnusDifference (R := ℤ) x
  have haOne : a 1 = 0 := by
    exact magnus_difference_ideal x
  have haPhysical : VanishesBelow a physicalOrder := by
    simpa only [a] using hx
  have hfamily :
      (fun q =>
        magnusDifference (R := ℤ) (x ^ exponent q)) =
        fun q =>
          integerBinomialSeries (exponent q) a - 1 := by
    funext q
    have hseries :=
      binomial_magnus_difference x (exponent q)
    exact congrArg (fun s => s - 1) hseries.symm
  rw [hfamily]
  constructor
  · intro q w hw
    change integerBinomialSeries (exponent q) a w -
        (1 : MSeries ℤ X) w = 0
    rw [integer_binomial_series, Finset.sum_range_succ']
    simp only [Ring.choose_zero_right, one_smul, pow_zero]
    rw [add_sub_cancel_right]
    apply Finset.sum_eq_zero
    intro k hk
    rw [pow_vanishes_below haPhysical (k + 1) w
      (by
        have hle :
            physicalOrder ≤ (k + 1) * physicalOrder := by
          nlinarith
        omega)]
    simp
  · intro w
    have hcoefficientFamily :
        (fun q =>
          (integerBinomialSeries (exponent q) a - 1) w) =
          fun q =>
            ∑ k ∈ Finset.range w.length,
              Ring.choose (exponent q) (k + 1) *
                (a ^ (k + 1)) w := by
      funext q
      change integerBinomialSeries (exponent q) a w -
          (1 : MSeries ℤ X) w = _
      rw [integer_binomial_series, Finset.sum_range_succ']
      simp only [Ring.choose_zero_right, one_smul, pow_zero]
      rw [add_sub_cancel_right]
      apply Finset.sum_congr rfl
      intro k hk
      rw [smul_eq_mul]
    rw [hcoefficientFamily]
    apply finsetSum
    intro k hk
    let l := k + 1
    by_cases hlength : w.length < l * physicalOrder
    · have hzero :
          (fun q =>
            Ring.choose (exponent q) l *
              (a ^ l) w) = 0 := by
        funext q
        rw [pow_vanishes_below haPhysical l w
          (by
            exact hlength)]
        simp
      rw [hzero]
      exact IVMost.zero _
    · have hphysicalLe : l * physicalOrder ≤ w.length :=
        Nat.le_of_not_gt hlength
      have hchoose :=
        hexponent.ringChoose l
      have hscaled :=
        IVMost.smul ((a ^ l) w) hchoose
      have hdegree :
          l * (physicalOrder - offset) ≤
            w.length - offset := by
        have hdecomp :
            physicalOrder =
              (physicalOrder - offset) + offset := by
          omega
        have hoffsetMul : offset ≤ l * offset := by
          have : 1 ≤ l := by simp [l]
          nlinarith
        rw [hdecomp, Nat.mul_add] at hphysicalLe
        omega
      simpa [l, mul_comm] using hscaled.mono hdegree

/-- Replacing one specified leaf by a polynomial integer power lowers the
polynomial order of the tree's Magnus difference by exactly one. -/
theorem leafOccurrenceZ
    (tree : HallTree X)
    (leaf : HallTree.LOccur tree)
    {exponent : ℕ → ℤ}
    (hexponent : IVMost exponent 1) :
    MPOrd
      (fun q =>
        magnusDifference (R := ℤ)
          (HallTree.leafOccurrenceZ
            FreeGroup.of (exponent q) tree leaf))
      (tree.weight - 1) := by
  induction leaf with
  | atom a =>
      simpa [HallTree.leafOccurrenceZ] using
        fixedZPow (X := X) (FreeGroup.of a)
          (magnus_vanishes_below
            (R := ℤ) (FreeGroup.of a))
          (show 0 ≤ 1 by omega) hexponent
  | @left left right leaf ih =>
      have hright :
          MPOrd
            (fun _ : ℕ =>
              magnusDifference (R := ℤ)
                (right.toCWord.eval FreeGroup.of))
            right.weight :=
        constant _ right.weight
          (tree_vanishes_below right)
      have hcommutator :=
        ih.magnusDifference_commutator hright
      have horder :
          (left.weight - 1) + right.weight =
            (left.weight + right.weight) - 1 := by
        have := left.weight_pos
        omega
      simpa only [HallTree.leafOccurrenceZ,
        HallTree.weight_commutator, horder] using hcommutator
  | @right left right leaf ih =>
      have hleft :
          MPOrd
            (fun _ : ℕ =>
              magnusDifference (R := ℤ)
                (left.toCWord.eval FreeGroup.of))
            left.weight :=
        constant _ left.weight
          (tree_vanishes_below left)
      have hcommutator :=
        hleft.magnusDifference_commutator ih
      have horder :
          left.weight + (right.weight - 1) =
            (left.weight + right.weight) - 1 := by
        have := right.weight_pos
        omega
      simpa only [HallTree.leafOccurrenceZ,
        HallTree.weight_commutator, horder] using hcommutator

end MPOrd

namespace HMCoord

variable {X : Type u}

/-- The degree-`m` Magnus difference of an element of `γ_m`, stated using
the caller's indexing instance. -/
theorem homogeneous_part_magnus
    [Fintype X] [Encodable X]
    {m : ℕ}
    (hm : 0 < m)
    {g : FreeGroup X}
    (hg :
      g ∈ Subgroup.lowerCentralSeries (FreeGroup X) (m - 1)) :
    homogeneousPart m (magnusDifference (R := ℤ) g) =
      (ICokern.homogeneousRealizationLinear
        (X := X) m).symm
        (Submodule.Quotient.mk
          (lowerRepWeight hm hg)) := by
  classical
  apply
    (Finsupp.supportedEquivFinsupp
      (R := ℤ) {w : FreeMonoid X | w.length = m}).injective
  ext w
  change
    (homogeneousPart m (magnusDifference (R := ℤ) g)).1 w.1 =
      ((ICokern.homogeneousRealizationLinear
        (X := X) m).symm
        (Submodule.Quotient.mk
          (lowerRepWeight hm hg))).1 w.1
  rw [homogeneousPart_apply,
    homogeneous_realization_magnus,
    magnus_rep_weight hm hg]

/-- The homogeneous Magnus functional which reads the coefficient of one
singleton Hall basis vector, with the caller's Hall indexing instance. -/
noncomputable def linearMap
    [DecidableEq X] [Fintype X] [Encodable X]
    {m : ℕ}
    (j : HallTree.BasicIndex (α := X) m) :
    AssociativeHomogeneousWords ℤ X m →ₗ[ℤ] ℤ :=
  (Finsupp.lapply
      (ICokern.basicSingletonSequence j)).comp
    (((ICokern.augmentationPBWBasis
      (X := X) m).repr).toLinearMap.comp
      (ICokern.homogeneousRealizationLinear
        (X := X) m).toLinearMap)

/-- On a lower-central element, the instance-generic singleton PBW
functional reads its coordinate in the canonical Hall basis. -/
theorem linear_lower_class
    [DecidableEq X] [Fintype X] [Encodable X]
    {m : ℕ}
    (hm : 0 < m)
    {g : FreeGroup X}
    (hg :
      g ∈ Subgroup.lowerCentralSeries (FreeGroup X) (m - 1))
    (j : HallTree.BasicIndex (α := X) m) :
    linearMap j
        (homogeneousPart m (magnusDifference (R := ℤ) g)) =
      (HallTree.freePBWUniqueness
          (IMagnus.hallPBWInput (X := X)) hm).repr
        (lowerCentralWeight hg) j := by
  let lowerBasis :=
    HallTree.freePBWUniqueness
      (IMagnus.hallPBWInput (X := X)) hm
  let augmentationBasis :=
    ICokern.augmentationPBWBasis (X := X) m
  let magnusMap :=
    HallTree.freeMagnusInt X hm
  have hsingleton :
      Function.Injective
        (ICokern.basicSingletonSequence
          (X := X) (n := m)) := by
    intro i k hik
    apply HallTree.indexed_tree_injective
    apply List.singleton_injective
    exact congrArg Subtype.val hik
  have hmappedBasis :
      ∀ i,
        magnusMap (lowerBasis i) =
          augmentationBasis
            (ICokern.basicSingletonSequence i) := by
    intro i
    have hlower :
        lowerBasis i =
          (HallTree.indexedBasicTree i).freeLowerWeight
            (HallTree.indexed_tree_weight i) := by
      simp only [lowerBasis,
        HallTree.freePBWUniqueness,
        Module.Basis.mk_apply]
    rw [hlower]
    exact
      (ICokern.pbw_singleton_sequence
        (X := X) hm i).symm
  have hcoordinateMap :
      (augmentationBasis.coord
          (ICokern.basicSingletonSequence j)).comp magnusMap =
        lowerBasis.coord j := by
    apply lowerBasis.ext
    intro i
    rw [LinearMap.comp_apply, hmappedBasis]
    simp only [Module.Basis.coord_apply, Module.Basis.repr_self,
      ]
    by_cases hij : i = j
    · subst i
      simp
    · have hsingletonNe :
          ICokern.basicSingletonSequence i ≠
            ICokern.basicSingletonSequence j :=
        fun h => hij (hsingleton h)
      simp [hsingletonNe, hij]
  rw [homogeneous_part_magnus hm hg]
  simp only [linearMap, LinearMap.comp_apply,
    LinearEquiv.coe_toLinearMap, Finsupp.lapply_apply]
  rw [LinearEquiv.apply_symm_apply]
  have hclassMap :=
    free_magnus_class
      hm hg
  change
    augmentationBasis.coord
        (ICokern.basicSingletonSequence j)
        (Submodule.Quotient.mk
          (lowerRepWeight hm hg)) =
      lowerBasis.coord j (lowerCentralWeight hg)
  rw [← hclassMap]
  exact LinearMap.congr_fun hcoordinateMap (lowerCentralWeight hg)

end HMCoord

end P1960
end Struik
