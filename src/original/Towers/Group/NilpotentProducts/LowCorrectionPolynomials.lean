import Towers.Group.NilpotentProducts.LowPolynomialOperations
import Towers.Group.NilpotentProducts.HallPetrescoPowers
import Towers.Group.NilpotentProducts.GeneralPolynomialCoordinates
import Towers.Group.Zassenhaus.RecipePositiveBelow

/-!
# Theorem H3 correction coordinates through cutoff four

The universal cutoff-four product, inverse, and power collectors can be
composed.  For a fixed finite tuple and a fixed permutation, this constructs
the actual standard Hall coordinates of Struik's reordered power correction
and proves the stated polynomial degree bound on those coordinates.
-/

namespace Struik
namespace P1960

open Towers
open Towers.Edmonton
open Towers.TCTex

universe u

noncomputable section

/-- Through cutoff four, Struik's Theorem H3 has one standard Hall correction
family whose coordinates are integer-valued polynomials of degree at most
their ordinary Hall weight.  The correction has no weight-one coordinates. -/
theorem tuple_coordinates_four
    (d n k : ℕ)
    (hn : 2 ≤ n)
    (hn4 : n ≤ 4)
    (x :
      Fin k →
        LowerCentralTruncation
          (FreeGroup (FreeGenerator.{u} d)) n)
    (σ : Equiv.Perm (Fin k)) :
    ∃ correction : ℕ → StandardExponentFamily.{u} d,
      (∀ q : ℕ,
        (List.ofFn x).prod ^ q =
          ((List.ofFn (x ∘ σ)).map fun g => g ^ q).prod *
            standardHallProduct d n (correction q)) ∧
        (∀ q s : ℕ,
          1 ≤ s →
            s < 2 →
              s < n →
                correction q s = 0) ∧
          ∀ s : ℕ,
            1 ≤ s →
              s < n →
                ∀ i : (standardHallFamily.{u} d s).index,
                  IVMost
                    (fun q : ℕ => correction q s i) s := by
  let H := standardHallFamily.{u} d
  have hH :
      ∀ r : ℕ,
        1 ≤ r →
          r < n →
            (H r).FormsAssocGradedbasis (n := n) :=
    fun r hr hrn =>
      standard_forms_associated d n r hr hrn
  let ordered := List.ofFn x
  let reordered := List.ofFn (x ∘ σ)
  let productRecipes :=
    collected_recipes_n
      (k := k) hn hn4 H hH
  let inverseRecipes :=
    collected_recipes_four
      hn hn4 H hH
  let binaryRecipes :=
    collected_recipes_n
      (k := 2) hn hn4 H hH
  let reorderedPowerCoordinates :
      ℕ → Fin k → StandardExponentFamily.{u} d :=
    fun q j =>
      truncateStandardFamily d n
        (standardHallCoordinates d n hn ((x (σ j)) ^ q))
  have hReorderedPowerCoordinates :
      HallCoordinateFamily H (Fin k) 1
        reorderedPowerCoordinates := by
    intro j s i
    by_cases hs : 1 ≤ s ∧ s < n
    · have hcoordinate :=
        coordinate_n_four
          (r := 1) hn hn4 H hH (x (σ j)) (by simp) (by omega)
            hs.1 hs.2 i
      simpa [reorderedPowerCoordinates,
        truncateStandardFamily, hs,
        standardHallCoordinates, hallCoordinate] using hcoordinate
    · have hzero :
          (fun q : ℕ => reorderedPowerCoordinates q j s i) = 0 := by
        funext q
        simp [reorderedPowerCoordinates,
          truncateStandardFamily, hs]
      rw [hzero]
      exact IVMost.zero _
  let reorderedProductCoordinates :
      ℕ → StandardExponentFamily.{u} d :=
    fun q => productRecipes.eval (reorderedPowerCoordinates q)
  have hReorderedProductCoordinates :
      HallCoordinateFamily H (Fin 1) 1
        (fun q _ => reorderedProductCoordinates q) := by
    exact
      productRecipes.coordinate_family_single
        reorderedPowerCoordinates hReorderedPowerCoordinates
  let inverseInput :
      ℕ → Fin 1 → StandardExponentFamily.{u} d :=
    fun q _ => negExponentFamily (reorderedProductCoordinates q)
  have hInverseInput :
      HallCoordinateFamily H (Fin 1) 1 inverseInput := by
    intro j s i
    have hcoordinate := hReorderedProductCoordinates j s i
    have hnegative := hcoordinate.smul (-1)
    simpa [inverseInput, negExponentFamily, Pi.smul_apply,
      smul_eq_mul] using hnegative
  let inverseReorderedProductCoordinates :
      ℕ → StandardExponentFamily.{u} d :=
    fun q => inverseRecipes.eval (inverseInput q)
  have hInverseReorderedProductCoordinates :
      HallCoordinateFamily H (Fin 1) 1
        (fun q _ => inverseReorderedProductCoordinates q) := by
    exact
      inverseRecipes.coordinate_family_single
        inverseInput hInverseInput
  let originalPowerCoordinates :
      ℕ → StandardExponentFamily.{u} d :=
    fun q =>
      truncateStandardFamily d n
        (standardHallCoordinates d n hn (ordered.prod ^ q))
  have hOriginalPowerCoordinates :
      HallCoordinateFamily H (Fin 1) 1
        (fun q _ => originalPowerCoordinates q) := by
    intro _ s i
    by_cases hs : 1 ≤ s ∧ s < n
    · have hcoordinate :=
        coordinate_n_four
          (r := 1) hn hn4 H hH ordered.prod (by simp) (by omega)
            hs.1 hs.2 i
      simpa [originalPowerCoordinates,
        truncateStandardFamily, hs,
        standardHallCoordinates, hallCoordinate] using hcoordinate
    · have hzero :
          (fun q : ℕ => originalPowerCoordinates q s i) = 0 := by
        funext q
        simp [originalPowerCoordinates,
          truncateStandardFamily, hs]
      rw [hzero]
      exact IVMost.zero _
  let correctionInput :
      ℕ → Fin 2 → StandardExponentFamily.{u} d :=
    fun q j =>
      if j = 0 then
        inverseReorderedProductCoordinates q
      else
        originalPowerCoordinates q
  have hCorrectionInput :
      HallCoordinateFamily H (Fin 2) 1 correctionInput := by
    intro j s i
    fin_cases j
    · simpa [correctionInput] using
        hInverseReorderedProductCoordinates (0 : Fin 1) s i
    · simpa [correctionInput] using
        hOriginalPowerCoordinates (0 : Fin 1) s i
  let correction : ℕ → StandardExponentFamily.{u} d :=
    fun q => binaryRecipes.eval (correctionInput q)
  have hCorrectionCoordinates :
      HallCoordinateFamily H (Fin 1) 1
        (fun q _ => correction q) := by
    exact
      binaryRecipes.coordinate_family_single
        correctionInput hCorrectionInput
  have hReorderedProduct (q : ℕ) :
      standardHallProduct d n (reorderedProductCoordinates q) =
        (reordered.map fun g => g ^ q).prod := by
    change
      collectedHallProduct (n := n) H (productRecipes.eval
        (reorderedPowerCoordinates q)) =
        (reordered.map fun g => g ^ q).prod
    rw [collected_recipes_spec
      hn hn4 H hH (reorderedPowerCoordinates q)]
    rw [show reordered = (List.finRange k).map (x ∘ σ) by
      simp [reordered, List.ofFn_eq_map]]
    apply congrArg List.prod
    simp only [List.map_map]
    apply List.map_congr_left
    intro j _hj
    change
      standardHallProduct d n (reorderedPowerCoordinates q j) =
        x (σ j) ^ q
    dsimp only [reorderedPowerCoordinates]
    rw [
      standard_truncate_family,
      standard_product_coordinates]
  have hInverseReorderedProduct (q : ℕ) :
      standardHallProduct d n (inverseReorderedProductCoordinates q) =
        ((reordered.map fun g => g ^ q).prod)⁻¹ := by
    change
      collectedHallProduct (n := n) H
          (inverseRecipes.eval (inverseInput q)) =
        ((reordered.map fun g => g ^ q).prod)⁻¹
    rw [show inverseInput q =
        fun _ : Fin 1 =>
          negExponentFamily (reorderedProductCoordinates q) by
      rfl]
    rw [recipes_n_spec
      hn hn4 H hH (reorderedProductCoordinates q)]
    exact congrArg Inv.inv (hReorderedProduct q)
  have hOriginalPower (q : ℕ) :
      standardHallProduct d n (originalPowerCoordinates q) =
        ordered.prod ^ q := by
    dsimp only [originalPowerCoordinates]
    rw [
      standard_truncate_family,
      standard_product_coordinates]
  have hCorrection (q : ℕ) :
      standardHallProduct d n (correction q) =
        ((reordered.map fun g => g ^ q).prod)⁻¹ *
          ordered.prod ^ q := by
    change
      collectedHallProduct (n := n) H
          (binaryRecipes.eval (correctionInput q)) =
        ((reordered.map fun g => g ^ q).prod)⁻¹ *
          ordered.prod ^ q
    rw [collected_recipes_spec
      hn hn4 H hH (correctionInput q)]
    simp only [List.finRange_succ, List.map_cons, List.prod_cons,
      List.finRange_zero, List.map_nil, List.prod_nil, mul_one]
    simp only [correctionInput, ↓reduceIte, Fin.succ_ne_zero]
    change
      standardHallProduct d n (inverseReorderedProductCoordinates q) *
          standardHallProduct d n (originalPowerCoordinates q) =
        ((reordered.map fun g => g ^ q).prod)⁻¹ *
          ordered.prod ^ q
    rw [hInverseReorderedProduct q, hOriginalPower q]
  have hperm : ordered.Perm reordered := by
    exact (σ.ofFn_comp_perm x).symm
  refine ⟨correction, ?_, ?_, ?_⟩
  · intro q
    change
      ordered.prod ^ q =
        (reordered.map fun g => g ^ q).prod *
          standardHallProduct d n (correction q)
    rw [hCorrection q]
    group
  · intro q s hs hs2 hsn
    have hmem :
        standardHallProduct d n (correction q) ∈
          Subgroup.lowerCentralSeries
            (LowerCentralTruncation
              (FreeGroup (FreeGenerator.{u} d)) n) 1 := by
      rw [hCorrection q]
      simpa [hallReorderedCorrection] using
        reordered_lower_series hperm q
    exact
      imp_coordinates_below
        hn H hH (correction q) hmem s hs hs2 hsn
  · intro s hs hsn i
    have hcoordinate := hCorrectionCoordinates (0 : Fin 1) s i
    simpa using hcoordinate

/-- Source-facing form of Theorem H3 through cutoff four.  In an arbitrary
group with `G_n = 1`, the universal standard Hall correction coordinates
evaluate to the required correction under the homomorphism determined by
the chosen tuple. -/
theorem tuple_nilpotency_four
    {G : Type u} [Group G]
    (n k : ℕ)
    (hn : 2 ≤ n)
    (hn4 : n ≤ 4)
    (x : Fin k → G)
    (σ : Equiv.Perm (Fin k))
    (hG : Subgroup.lowerCentralSeries G (n - 1) = ⊥) :
    ∃ correction : ℕ → StandardExponentFamily.{u} k,
      (∀ q : ℕ,
        (List.ofFn x).prod ^ q =
          ((List.ofFn (x ∘ σ)).map fun g => g ^ q).prod *
            freeTruncationLift
              (fun a : FreeGenerator.{u} k => x a.down) hG
              (standardHallProduct k n (correction q))) ∧
        (∀ q s : ℕ,
          1 ≤ s →
            s < 2 →
              s < n →
                correction q s = 0) ∧
          ∀ s : ℕ,
            1 ≤ s →
              s < n →
                ∀ i : (standardHallFamily.{u} k s).index,
                  IVMost
                    (fun q : ℕ => correction q s i) s := by
  let generators :
      Fin k →
        LowerCentralTruncation
          (FreeGroup (FreeGenerator.{u} k)) n :=
    fun j =>
      freeTruncationValue k n (ULift.up j)
  obtain ⟨correction, hEquality, hZero, hPolynomial⟩ :=
    tuple_coordinates_four
      k n k hn hn4 generators σ
  refine ⟨correction, ?_, hZero, hPolynomial⟩
  intro q
  have hmapped :=
    congrArg
      (freeTruncationLift
        (fun a : FreeGenerator.{u} k => x a.down) hG)
      (hEquality q)
  simpa only [map_mul, map_pow, map_list_prod, List.map_map,
    Function.comp_def, List.ofFn_eq_map, generators,
    truncation_lift_generator] using hmapped

/-- The two-factor, identity-permutation specialization gives the actual
standard Hall correction coordinates in Theorem H2 through cutoff four. -/
theorem correction_coordinates_four
    (d n : ℕ)
    (hn : 2 ≤ n)
    (hn4 : n ≤ 4)
    (R S :
      LowerCentralTruncation
        (FreeGroup (FreeGenerator.{u} d)) n) :
    ∃ correction : ℕ → StandardExponentFamily.{u} d,
      (∀ q : ℕ,
        (R * S) ^ q =
          R ^ q * S ^ q *
            standardHallProduct d n (correction q)) ∧
        (∀ q s : ℕ,
          1 ≤ s →
            s < 2 →
              s < n →
                correction q s = 0) ∧
          ∀ s : ℕ,
            1 ≤ s →
              s < n →
                ∀ i : (standardHallFamily.{u} d s).index,
                  IVMost
                    (fun q : ℕ => correction q s i) s := by
  let pair :
      Fin 2 →
        LowerCentralTruncation
          (FreeGroup (FreeGenerator.{u} d)) n :=
    ![R, S]
  obtain ⟨correction, hEquality, hZero, hPolynomial⟩ :=
    tuple_coordinates_four
      d n 2 hn hn4 pair 1
  refine ⟨correction, ?_, hZero, hPolynomial⟩
  intro q
  simpa [pair] using hEquality q

/-- Source-facing two-factor form of Theorem H2 through cutoff four. -/
theorem nilpotency_cutoff_four
    {G : Type u} [Group G]
    (n : ℕ)
    (hn : 2 ≤ n)
    (hn4 : n ≤ 4)
    (R S : G)
    (hG : Subgroup.lowerCentralSeries G (n - 1) = ⊥) :
    ∃ correction : ℕ → StandardExponentFamily.{u} 2,
      (∀ q : ℕ,
        (R * S) ^ q =
          R ^ q * S ^ q *
            freeTruncationLift
              (fun a : FreeGenerator.{u} 2 => ![R, S] a.down) hG
              (standardHallProduct 2 n (correction q))) ∧
        (∀ q s : ℕ,
          1 ≤ s →
            s < 2 →
              s < n →
                correction q s = 0) ∧
          ∀ s : ℕ,
            1 ≤ s →
              s < n →
                ∀ i : (standardHallFamily.{u} 2 s).index,
                  IVMost
                    (fun q : ℕ => correction q s i) s := by
  let pair : Fin 2 → G := ![R, S]
  obtain ⟨correction, hEquality, hZero, hPolynomial⟩ :=
    tuple_nilpotency_four
      n 2 hn hn4 pair 1 hG
  refine ⟨correction, ?_, hZero, hPolynomial⟩
  intro q
  simpa [pair, mul_assoc] using hEquality q

/-- Through cutoff four, the correction coordinates in Struik's Lemma H1
are polynomial of degree at most their ordinary Hall weight.  The correction
has no coordinates of weights one or two. -/
theorem coordinates_cutoff_four
    (d n : ℕ)
    (hn : 2 ≤ n)
    (hn4 : n ≤ 4)
    (X Y :
      LowerCentralTruncation
        (FreeGroup (FreeGenerator.{u} d)) n) :
    ∃ correction : ℕ → StandardExponentFamily.{u} d,
      (∀ q : ℕ,
        hallCommutator (X ^ q) Y =
          hallCommutator X Y ^ q *
            standardHallProduct d n (correction q)) ∧
        (∀ q s : ℕ,
          1 ≤ s →
            s < 3 →
              s < n →
                correction q s = 0) ∧
          ∀ s : ℕ,
            1 ≤ s →
              s < n →
                ∀ i : (standardHallFamily.{u} d s).index,
                  IVMost
                    (fun q : ℕ => correction q s i) s := by
  let C := hallCommutator X Y
  obtain ⟨correction, hPower, _hZero, hPolynomial⟩ :=
    correction_coordinates_four
      d n hn hn4 X C
  have hCorrection (q : ℕ) :
      standardHallProduct d n (correction q) =
        hallCommutatorCorrection X Y q := by
    apply mul_left_cancel (a := X ^ q * C ^ q)
    rw [← hPower q]
    simpa [C, hallCommutatorCorrection, mul_assoc] using
      mul_powers_correction X C q
  refine ⟨correction, ?_, ?_, hPolynomial⟩
  · intro q
    rw [hCorrection q]
    exact commutator_pow_correction X Y q
  · intro q s hs hs3 hsn
    have hmem :
        standardHallProduct d n (correction q) ∈
          Subgroup.lowerCentralSeries
            (LowerCentralTruncation
              (FreeGroup (FreeGenerator.{u} d)) n) 2 := by
      rw [hCorrection q]
      exact lower_series_two X Y q
    exact
      imp_coordinates_below
        hn (standardHallFamily.{u} d)
          (fun r hr hrn =>
            standard_forms_associated d n r hr hrn)
        (correction q) hmem s hs hs3 hsn

/-- Source-facing form of Lemma H1 through cutoff four. -/
theorem coordinates_nilpotency_four
    {G : Type u} [Group G]
    (n : ℕ)
    (hn : 2 ≤ n)
    (hn4 : n ≤ 4)
    (X Y : G)
    (hG : Subgroup.lowerCentralSeries G (n - 1) = ⊥) :
    ∃ correction : ℕ → StandardExponentFamily.{u} 2,
      (∀ q : ℕ,
        hallCommutator (X ^ q) Y =
          hallCommutator X Y ^ q *
            freeTruncationLift
              (fun a : FreeGenerator.{u} 2 =>
                ![X, Y] a.down) hG
              (standardHallProduct 2 n (correction q))) ∧
        (∀ q s : ℕ,
          1 ≤ s →
            s < 3 →
              s < n →
                correction q s = 0) ∧
          ∀ s : ℕ,
            1 ≤ s →
              s < n →
                ∀ i : (standardHallFamily.{u} 2 s).index,
                  IVMost
                    (fun q : ℕ => correction q s i) s := by
  let xFree :=
    freeTruncationValue 2 n
      (ULift.up (0 : Fin 2))
  let yFree :=
    freeTruncationValue 2 n
      (ULift.up (1 : Fin 2))
  obtain ⟨correction, hEquality, hZero, hPolynomial⟩ :=
    coordinates_cutoff_four
      2 n hn hn4 xFree yFree
  refine ⟨correction, ?_, hZero, hPolynomial⟩
  intro q
  have hmapped :=
    congrArg
      (freeTruncationLift
        (fun a : FreeGenerator.{u} 2 => ![X, Y] a.down) hG)
      (hEquality q)
  simpa [xFree, yFree, hallCommutator] using hmapped

end

end P1960
end Struik
