import Submission.Group.Cohomology.MagnusMassey
import Submission.Group.HallBasic.HallWittFormula
import Submission.Algebra.Magnus.WeightedConverse
import Mathlib.Algebra.NoZeroSMulDivisors.Pi
import Mathlib.Data.Finite.Vector
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FreeModule.PID


/-!
# Finite-alphabet integral ranks of Magnus--Massey classes

This file specializes the Section 9 pairing to integral coefficients.  The
trivial multiplicatively descending map identifies the integral Magnus
filtration with the lower-central filtration, so Hall's basis computes the
rank of the resulting Massey submodule when the free basis is finite.
-/

noncomputable section

namespace EChapma
namespace MSeries
namespace MMassey

open scoped IsMulCommutative

open Submission
open Submission.TBluepr

variable {X : Type} [Fintype X] [DecidableEq X] [Encodable X]

omit [Fintype X] [DecidableEq X] [Encodable X] in
/-- Zeroth powers generate the trivial subgroup. -/
@[simp]
theorem subgroupPower_zero (H : Subgroup (FreeGroup X)) :
    subgroupPower H 0 = ⊥ := by
  apply bot_unique
  unfold subgroupPower
  apply Subgroup.normalClosure_le_normal
  rintro y ⟨x, hx, rfl⟩
  simp

omit [Fintype X] [DecidableEq X] [Encodable X] in
/-- For the trivial weight map, the weighted lower-central product is the
ordinary `n`th lower-central term. -/
theorem weighted_lower_trivial
    {n : ℕ} (hn : 1 ≤ n) :
    weightedLowerProduct (X := X)
        MDescen.trivial n =
      Subgroup.lowerCentralSeries (FreeGroup X) (n - 1) := by
  classical
  apply le_antisymm
  · unfold weightedLowerProduct
    apply iSup_le
    intro i
    by_cases hin : i.1 = n
    · simp [hin, MDescen.trivial_apply_diagonal,
        subgroupPower_one]
    · have hil : i.1 < n := lt_of_le_of_ne i.2.2 hin
      simp [MDescen.trivial_apply_lt hil]
  · have hfactor :
        subgroupPower
            (Subgroup.lowerCentralSeries (FreeGroup X) (n - 1))
            (MDescen.trivial n n) ≤
          weightedLowerProduct (X := X)
            MDescen.trivial n :=
      le_iSup
        (fun i : {i : ℕ // 1 ≤ i ∧ i ≤ n} =>
          subgroupPower
            (Subgroup.lowerCentralSeries (FreeGroup X) (i.1 - 1))
            (MDescen.trivial n i.1))
        ⟨n, hn, le_rfl⟩
    simpa [MDescen.trivial_apply_diagonal,
      subgroupPower_one] using hfactor

omit [Fintype X] [DecidableEq X] [Encodable X] in
/-- For the trivial weight map, the weighted Magnus ideal is exactly the
order-`n` ideal. -/
theorem weightedIdeal_trivial
    {n : ℕ} (hn : 1 ≤ n) :
    weightedIdeal (R := ℤ) (X := X)
        MDescen.trivial n =
      orderLeastIdeal (R := ℤ) (X := X) n := by
  apply SetLike.ext'
  apply le_antisymm
  · intro f hf
    induction hf using AddSubgroup.closure_induction with
    | mem f hf =>
        rcases hf with ⟨i, hi, hin, y, hy, rfl⟩
        by_cases hin' : i = n
        · subst i
          simpa [MDescen.trivial_apply_diagonal] using hy
        · have hil : i < n := lt_of_le_of_ne hin hin'
          simp [MDescen.trivial_apply_lt hil]
    | zero => exact Submodule.zero_mem _
    | add f g _ _ hf hg => exact Submodule.add_mem _ hf hg
    | neg f _ hf => exact Submodule.neg_mem _ hf
  · intro f hf
    simpa [MDescen.trivial_apply_diagonal] using
      (magnusAddFiltration (R := ℤ) (X := X)).weightedGenerator_mem
          MDescen.trivial hn le_rfl
          (by simpa [magnusAddFiltration] using hf)

omit [Fintype X] [DecidableEq X] in
/-- For integral coefficients, the `n`th Magnus-order subgroup is the
one-based `n`th lower-central term. -/
theorem magnus_int_series
    [Finite X]
    {n : ℕ} (hn : 1 ≤ n) :
    magnusOrderSubgroup (R := ℤ) (X := X) n =
      Subgroup.lowerCentralSeries (FreeGroup X) (n - 1) := by
  classical
  letI : Fintype X := Fintype.ofFinite X
  calc
    magnusOrderSubgroup (R := ℤ) (X := X) n =
        magnusWeightedSubgroup (R := ℤ) (X := X)
          MDescen.trivial n := by
            ext g
            rw [magnus_order_subgroup,
              magnus_weighted_subgroup,
              weightedIdeal_trivial (X := X) hn]
            rfl
    _ =
        weightedLowerProduct (X := X)
          MDescen.trivial n := by
            symm
            exact
              weighted_magnus_int
                (X := X) MDescen.trivial
                MDescen.trivial_isBinomial hn
    _ = Subgroup.lowerCentralSeries (FreeGroup X) (n - 1) :=
      weighted_lower_trivial (X := X) hn

omit [Fintype X] [DecidableEq X] in
/-- In integral coefficients, the consecutive Magnus layer is the
corresponding zero-based lower-central layer. -/
theorem magnus_int_type
    [Finite X]
    {n : ℕ} (hn : 1 ≤ n) :
    MagnusLayer (R := ℤ) (X := X) n =
      LowerGradedLayer
        (FreeGroup X) (n - 1) := by
  classical
  letI : Fintype X := Fintype.ofFinite X
  unfold MagnusLayer LowerGradedLayer
  rw [magnus_int_series (X := X) hn,
    magnus_int_series
      (X := X) (n := n + 1) (by omega)]
  simp [Nat.sub_add_cancel hn]

/-- The integer-linear equivalence from the integral Magnus layer to the
lower-central layer. -/
noncomputable def magnusIntCentral
    {n : ℕ} (hn : 1 ≤ n) :
    Additive (MagnusLayer (R := ℤ) (X := X) n) ≃ₗ[ℤ]
      Additive
        (LowerGradedLayer
          (FreeGroup X) (n - 1)) := by
  let hNumerator :
      magnusOrderSubgroup (R := ℤ) (X := X) n =
        Subgroup.lowerCentralSeries (FreeGroup X) (n - 1) :=
    magnus_int_series (X := X) hn
  let hDenominator :
      magnusOrderSubgroup (R := ℤ) (X := X) (n + 1) =
        Subgroup.lowerCentralSeries (FreeGroup X) ((n - 1) + 1) := by
    rw [magnus_int_series
      (X := X) (n := n + 1) (by omega)]
    congr 1
    omega
  exact
    (MulEquiv.toAdditive
      (QuotientGroup.equivQuotientSubgroupOfOfEq
        hDenominator hNumerator)).toIntLinearEquiv

/-- Hall's basis, transported to the integral Magnus layer. -/
noncomputable def integralMagnusBasis
    {n : ℕ} (hn : 1 ≤ n) :
    Module.Basis
      (Submission.HallTree.BasicIndex (α := X) n) ℤ
      (Additive (MagnusLayer (R := ℤ) (X := X) n)) := by
  let b :=
    (IMagnus.lowerCentralBasis
      (X := X) (n - 1)).map
        (magnusIntCentral
          (X := X) hn).symm
  simpa [Nat.sub_add_cancel hn] using b

/-- The integral Magnus layer has rank equal to the number of weight-`n`
basic Hall commutators. -/
theorem integral_magnus_finrank
    {n : ℕ} (hn : 1 ≤ n) :
    Module.finrank ℤ
        (Additive (MagnusLayer (R := ℤ) (X := X) n)) =
      Fintype.card (Submission.HallTree.BasicIndex (α := X) n) :=
  Module.finrank_eq_card_basis
    (integralMagnusBasis (X := X) hn)

/-- The integral coefficient-character pairing, linearized in the Magnus
layer variable. -/
def coefficientPairingLinear
    {n : ℕ} (hn : 0 < n) :
    Additive (MagnusLayer (R := ℤ) (X := X) n) →ₗ[ℤ]
      Module.Dual ℤ
        (CoefficientCharacterSpan
          (R := ℤ) (X := X) hn) :=
  (coefficientCharacterPairing (R := ℤ) (X := X) hn).toIntLinearMap

/-- The same integral pairing, with its two variables exchanged. -/
def pairingFlipLinear
    {n : ℕ} (hn : 0 < n) :
    CoefficientCharacterSpan (R := ℤ) (X := X) hn →ₗ[ℤ]
      Module.Dual ℤ
        (Additive (MagnusLayer (R := ℤ) (X := X) n)) :=
  LinearMap.flip
    (coefficientPairingLinear (X := X) hn)

omit [Fintype X] [DecidableEq X] [Encodable X] in
/-- Nondegeneracy on the Magnus-layer side gives injectivity of the first
integral adjoint map. -/
theorem coefficient_pairing_injective
    {n : ℕ} (hn : 0 < n) :
    Function.Injective
      (coefficientPairingLinear
        (X := X) hn) :=
  character_pairing_injective
    (R := ℤ) (X := X) hn

omit [Fintype X] [DecidableEq X] [Encodable X] in
/-- Nondegeneracy on the character side gives injectivity of the flipped
integral adjoint map. -/
theorem pairing_flip_injective
    {n : ℕ} (hn : 0 < n) :
    Function.Injective
      (pairingFlipLinear
        (X := X) hn) := by
  intro f g hfg
  apply sub_eq_zero.mp
  apply coefficient_character_pairing
    (R := ℤ) (X := X) hn (f - g)
  intro q
  have hq :=
    DFunLike.congr_fun hfg q
  change
    coefficientCharacterPairing (R := ℤ) hn q f =
      coefficientCharacterPairing (R := ℤ) hn q g at hq
  change
    coefficientCharacterPairing (R := ℤ) hn q (f - g) = 0
  calc
    coefficientCharacterPairing (R := ℤ) hn q (f - g) =
        coefficientCharacterPairing (R := ℤ) hn q f -
          coefficientCharacterPairing (R := ℤ) hn q g :=
      map_sub _ f g
    _ = 0 := sub_eq_zero.mpr hq

omit [Fintype X] [DecidableEq X] in
/-- The character span and the consecutive integral Magnus layer have the
same finite rank.  This is the rank consequence of nondegeneracy in both
variables. -/
theorem coefficient_character_magnus
    [Finite X]
    {n : ℕ} (hn : 0 < n) :
    Module.finrank ℤ
        (CoefficientCharacterSpan
          (R := ℤ) (X := X) hn) =
      Module.finrank ℤ
        (Additive (MagnusLayer (R := ℤ) (X := X) n)) := by
  classical
  letI : Fintype X := Fintype.ofFinite X
  let bL :=
    integralMagnusBasis (X := X)
      (Nat.one_le_iff_ne_zero.mpr hn.ne')
  letI :
      Module.Free ℤ
        (Additive (MagnusLayer (R := ℤ) (X := X) n)) :=
    Module.Free.of_basis bL
  letI :
      Module.Finite ℤ
        (Additive (MagnusLayer (R := ℤ) (X := X) n)) :=
    Module.Finite.of_basis bL
  letI : Finite (DegreeWord X n) :=
    List.Vector.finite
  letI :
      Module.Finite ℤ
        (CoefficientCharacterSpan
          (R := ℤ) (X := X) hn) := by
    change
      Module.Finite ℤ
        (LinearMap.range
          (coefficientCharacterMap
            (R := ℤ) (X := X) hn))
    exact Module.Finite.range _
  letI :
      Module.IsTorsionFree ℤ
        (CoefficientCharacterSpan
          (R := ℤ) (X := X) hn) := by
    let ev :
        CoefficientCharacterSpan
            (R := ℤ) (X := X) hn →
          (Additive
              (magnusOrderSubgroup
                (R := ℤ) (X := X) n) →
            ℤ) :=
      fun f x => f.1.1 x
    exact
      Function.Injective.moduleIsTorsionFree ev
        (by
          intro f g hfg
          apply Subtype.ext
          apply Subtype.ext
          apply AddMonoidHom.ext
          intro x
          exact congrFun hfg x)
        (by
          intro r f
          funext x
          rfl)
  letI :
      Module.Free ℤ
        (CoefficientCharacterSpan
          (R := ℤ) (X := X) hn) :=
    Module.free_of_finite_type_torsion_free'
      (R := ℤ)
      (M :=
        CoefficientCharacterSpan
          (R := ℤ) (X := X) hn)
  let bC :=
    (Module.basisOfFiniteTypeTorsionFree'
      (R := ℤ)
      (M :=
        CoefficientCharacterSpan
          (R := ℤ) (X := X) hn)).2
  letI :
      Module.Finite ℤ
        (Module.Dual ℤ
          (CoefficientCharacterSpan
            (R := ℤ) (X := X) hn)) :=
    Module.Finite.of_basis bC.dualBasis
  letI :
      Module.Finite ℤ
        (Module.Dual ℤ
          (Additive
            (MagnusLayer (R := ℤ) (X := X) n))) :=
    Module.Finite.of_basis bL.dualBasis
  have hleft :
      Module.finrank ℤ
          (Additive (MagnusLayer (R := ℤ) (X := X) n)) ≤
        Module.finrank ℤ
          (Module.Dual ℤ
            (CoefficientCharacterSpan
              (R := ℤ) (X := X) hn)) :=
    LinearMap.finrank_le_finrank_of_injective
      (coefficient_pairing_injective
        (X := X) hn)
  have hright :
      Module.finrank ℤ
          (CoefficientCharacterSpan
            (R := ℤ) (X := X) hn) ≤
        Module.finrank ℤ
          (Module.Dual ℤ
            (Additive
              (MagnusLayer (R := ℤ) (X := X) n))) :=
    LinearMap.finrank_le_finrank_of_injective
      (pairing_flip_injective
        (X := X) hn)
  have hdualC :
      Module.finrank ℤ
          (Module.Dual ℤ
            (CoefficientCharacterSpan
              (R := ℤ) (X := X) hn)) =
        Module.finrank ℤ
          (CoefficientCharacterSpan
            (R := ℤ) (X := X) hn) := by
    rw [Module.finrank_eq_card_basis bC.dualBasis,
      Module.finrank_eq_card_basis bC]
  have hdualL :
      Module.finrank ℤ
          (Module.Dual ℤ
            (Additive
              (MagnusLayer (R := ℤ) (X := X) n))) =
        Module.finrank ℤ
          (Additive
            (MagnusLayer (R := ℤ) (X := X) n)) := by
    rw [Module.finrank_eq_card_basis bL.dualBasis,
      Module.finrank_eq_card_basis bL]
  exact
    le_antisymm
      (hright.trans_eq hdualL)
      (hleft.trans_eq hdualC)

omit [Fintype X] [DecidableEq X] [Encodable X] in
/-- The integral coefficient-character span is torsion-free. -/
theorem coefficient_torsion_int
    {n : ℕ} (hn : 0 < n) :
    Module.IsTorsionFree ℤ
      (CoefficientCharacterSpan
        (R := ℤ) (X := X) hn) := by
  let ev :
      CoefficientCharacterSpan
          (R := ℤ) (X := X) hn →
        (Additive
            (magnusOrderSubgroup
              (R := ℤ) (X := X) n) →
          ℤ) :=
    fun f x => f.1.1 x
  exact
    Function.Injective.moduleIsTorsionFree ev
      (by
        intro f g hfg
        apply Subtype.ext
        apply Subtype.ext
        apply AddMonoidHom.ext
        intro x
        exact congrFun hfg x)
      (by
        intro r f
        funext x
        rfl)

/-- A chosen finite integral basis of the coefficient-character span. -/
noncomputable def coefficientCharacterBasis
    {n : ℕ} (hn : 0 < n) :
    Σ k : ℕ,
      Module.Basis (Fin k) ℤ
        (CoefficientCharacterSpan
          (R := ℤ) (X := X) hn) := by
  letI : Finite (DegreeWord X n) :=
    List.Vector.finite
  letI :
      Module.Finite ℤ
        (CoefficientCharacterSpan
          (R := ℤ) (X := X) hn) := by
    change
      Module.Finite ℤ
        (LinearMap.range
          (coefficientCharacterMap
            (R := ℤ) (X := X) hn))
    exact Module.Finite.range _
  letI :
      Module.IsTorsionFree ℤ
        (CoefficientCharacterSpan
          (R := ℤ) (X := X) hn) :=
    coefficient_torsion_int
      (X := X) hn
  exact
    Module.basisOfFiniteTypeTorsionFree'
      (R := ℤ)
      (M :=
        CoefficientCharacterSpan
          (R := ℤ) (X := X) hn)

/-- A finite integral basis of the `n`-fold word-Massey image, transported
through transgression from coefficient characters. -/
noncomputable def integralMasseyBasis
    {n : ℕ} (hn : 2 ≤ n) :
    Module.Basis
      (Fin
        (coefficientCharacterBasis
          (X := X)
          (lt_of_lt_of_le Nat.zero_lt_two hn)).1)
      ℤ
      (ExplicitMasseyImage
        (R := ℤ) (X := X)
        (lt_of_lt_of_le Nat.zero_lt_two hn)) :=
  (coefficientCharacterBasis
      (X := X)
      (lt_of_lt_of_le Nat.zero_lt_two hn)).2.map
    (coefficientMasseyImage
      (R := ℤ) (X := X) hn)

omit [Fintype X] [DecidableEq X] [Encodable X] in
/-- The integral `n`-fold word-Massey image is a free abelian group. -/
theorem integral_massey_free
    [Finite X]
    {n : ℕ} (hn : 2 ≤ n) :
    Module.Free ℤ
      (ExplicitMasseyImage
        (R := ℤ) (X := X)
        (lt_of_lt_of_le Nat.zero_lt_two hn)) :=
  by
    classical
    letI : Fintype X := Fintype.ofFinite X
    exact Module.Free.of_basis
      (integralMasseyBasis (X := X) hn)

/-- The integral `n`-fold word-Massey image has rank equal to the number of
weight-`n` basic Hall commutators. -/
theorem integral_massey_index
    {n : ℕ} (hn : 2 ≤ n) :
    Module.finrank ℤ
        (ExplicitMasseyImage
          (R := ℤ) (X := X)
          (lt_of_lt_of_le Nat.zero_lt_two hn)) =
      Fintype.card
        (Submission.HallTree.BasicIndex (α := X) n) := by
  let hnpos : 0 < n :=
    lt_of_lt_of_le Nat.zero_lt_two hn
  calc
    Module.finrank ℤ
        (ExplicitMasseyImage
          (R := ℤ) (X := X) hnpos) =
        Module.finrank ℤ
          (CoefficientCharacterSpan
            (R := ℤ) (X := X) hnpos) :=
      (coefficientMasseyImage
        (R := ℤ) (X := X) hn).finrank_eq.symm
    _ =
        Module.finrank ℤ
          (Additive
            (MagnusLayer (R := ℤ) (X := X) n)) :=
      coefficient_character_magnus
        (X := X) hnpos
    _ =
        Fintype.card
          (Submission.HallTree.BasicIndex (α := X) n) :=
      integral_magnus_finrank
        (X := X) (by omega)

omit [DecidableEq X] in
/-- Finite-alphabet integral form of Corollary 9.3: the rank of the `n`-fold
integral word-Massey image satisfies Witt's numerator formula. -/
theorem massey_witt_numerator
    {n : ℕ} (hn : 2 ≤ n) :
    (n : ℤ) *
        (Module.finrank ℤ
          (ExplicitMasseyImage
            (R := ℤ) (X := X)
            (lt_of_lt_of_le Nat.zero_lt_two hn)) : ℤ) =
      Submission.Edmonton.wittNumerator (Fintype.card X) n := by
  classical
  rw [integral_massey_index
    (X := X) hn]
  exact Submission.HallTree.card_witt_numerator
    (α := X) n (lt_of_lt_of_le Nat.zero_lt_two hn)

omit [DecidableEq X] in
/-- Rational form of Corollary 9.3, displaying the usual Möbius sum divided
by `n`. -/
theorem massey_witt_formula
    {n : ℕ} (hn : 2 ≤ n) :
    (Module.finrank ℤ
        (ExplicitMasseyImage
          (R := ℤ) (X := X)
          (lt_of_lt_of_le Nat.zero_lt_two hn)) : ℚ) =
      n.divisors.sum
          (fun d : ℕ =>
            (ArithmeticFunction.moebius d : ℚ) *
              (Fintype.card X : ℚ) ^ (n / d)) /
        (n : ℚ) := by
  classical
  rw [integral_massey_index
    (X := X) hn]
  exact Submission.HallTree.card_witt_formula
    (α := X) n (lt_of_lt_of_le Nat.zero_lt_two hn)

omit [DecidableEq X] in
/-- For two-fold Massey products, hence cup products, the integral image has
rank `choose |X| 2`.  This is the specialization stated after Corollary 9.3. -/
theorem integral_cup_finrank :
    Module.finrank ℤ
        (ExplicitMasseyImage
          (R := ℤ) (X := X)
          (show 0 < 2 by omega)) =
      (Fintype.card X).choose 2 := by
  classical
  rw [integral_massey_index
    (X := X) (n := 2) (by omega)]
  exact Submission.HallTree.card_basic_index

end MMassey
end MSeries
end EChapma
