import Towers.Group.NilpotentProducts.Support
import Towers.Group.NilpotentProducts.PolynomialOrderBounds

/-!
# General polynomial Hall coordinates for Struik's Lemma H2

This file lifts the canonical collected Hall products from the free nilpotent
truncation back to the free group.  The lifts let us remove already-known
lower-weight Hall factors while retaining access to Magnus coefficients.
-/

namespace Struik
namespace P1960

open EChapma
open EChapma.MSeries
open Towers
open Towers.TBluepr
open Towers.TCTex

universe u

noncomputable section

/-- The ordered weight-`r` Hall segment as an element of `γ_r` in the free
group. -/
def freeStandardTerm
    (t r : ℕ)
    (e : (standardHallFamily.{u} t r).index → ℤ) :
    Subgroup.lowerCentralSeries
      (FreeGroup (FreeGenerator.{u} t)) (r - 1) :=
  ((Finset.univ.sort
      fun i j : (standardHallFamily.{u} t r).index => i ≤ j).map
    fun i =>
      (⟨((standardHallFamily.{u} t r).commutator i).eval_in_freegroup,
        ((standardHallFamily.{u} t r).commutator i
          ).evalin_freegroupmem_lowecentseri⟩ :
        Subgroup.lowerCentralSeries
          (FreeGroup (FreeGenerator.{u} t)) (r - 1)) ^
            e i).prod

/-- The ambient free-group value of the ordered weight-`r` Hall segment. -/
def freeStandardProduct
    (t r : ℕ)
    (e : (standardHallFamily.{u} t r).index → ℤ) :
    FreeGroup (FreeGenerator.{u} t) :=
  freeStandardTerm t r e

@[simp]
theorem free_standard_zero
    (t r : ℕ) :
    freeStandardProduct t r
        (0 : (standardHallFamily.{u} t r).index → ℤ) =
      1 := by
  simp [freeStandardProduct,
    freeStandardTerm]

/-- The ordered Hall prefix through ordinary weight `k`, evaluated in the
free group before nilpotent truncation. -/
def freeStandardPrefix
    (t : ℕ)
    (e : StandardExponentFamily.{u} t)
    (k : ℕ) :
    FreeGroup (FreeGenerator.{u} t) :=
  ((List.range k).map fun j =>
    freeStandardProduct t (j + 1) (e (j + 1))).prod

theorem lower_truncation_standard
    (t n r : ℕ)
    (e : (standardHallFamily.{u} t r).index → ℤ) :
    lowerCentralTruncation
        (FreeGroup (FreeGenerator.{u} t)) n
        (freeStandardProduct t r e) =
      (standardHallFamily.{u} t r).collectedWeightProduct
        (n := n) e := by
  classical
  unfold freeStandardProduct
    freeStandardTerm
    BCWta.collectedWeightProduct
    BCWta.collected_lower_centralterm
  rw [SubmonoidClass.coe_list_prod, SubmonoidClass.coe_list_prod,
    map_list_prod]
  apply congrArg List.prod
  simp only [List.map_map]
  apply List.map_congr_left
  intro i _hi
  simp only [Function.comp_apply]
  change
    lowerCentralTruncation
          (FreeGroup (FreeGenerator.{u} t)) n
          (((standardHallFamily.{u} t r).commutator i
            |>.eval_in_freegroup) ^ e i) =
      ((standardHallFamily.{u} t r).commutator i
        |>.freeLowerTruncation (n := n)) ^
          e i
  rw [map_zpow,
    BCWt.mapevalinfree_groupeqevalin_frelowcentru]

/-- The associated-graded class of a lifted weight segment is the linear
combination of the free Hall classes with its integer exponents. -/
theorem free_standard_sum
    (t r : ℕ)
    (e : (standardHallFamily.{u} t r).index → ℤ) :
    QuotientGroup.mk'
        ((Subgroup.lowerCentralSeries
          (FreeGroup (FreeGenerator.{u} t)) r).subgroupOf
            (Subgroup.lowerCentralSeries
              (FreeGroup (FreeGenerator.{u} t)) (r - 1)))
        (freeStandardTerm t r e) =
      Additive.toMul
        (∑ i,
          e i •
            ((standardHallFamily.{u} t r).commutator i
              |>.free_groupassoc_gradedclass)) := by
  let F := FreeGroup (FreeGenerator.{u} t)
  let A : Subgroup F := Subgroup.lowerCentralSeries F (r - 1)
  let B : Subgroup A := (Subgroup.lowerCentralSeries F r).subgroupOf A
  let q : A →* A ⧸ B := QuotientGroup.mk' B
  letI : IsMulCommutative (A ⧸ B) :=
    associated_graded_commutative r
  change
    q (freeStandardTerm t r e) =
      Additive.toMul
        (∑ i,
          e i •
            ((standardHallFamily.{u} t r).commutator i
              |>.free_groupassoc_gradedclass))
  rw [freeStandardTerm, map_list_prod, List.map_map,
    sort_univ_fintype]
  simp only [Function.comp_apply, map_zpow, toMul_sum, toMul_zsmul]
  apply Finset.prod_congr rfl
  intro i _hi
  rfl

theorem truncation_standard_prefix
    (t n k : ℕ)
    (e : StandardExponentFamily.{u} t) :
    lowerCentralTruncation
        (FreeGroup (FreeGenerator.{u} t)) n
        (freeStandardPrefix t e k) =
      collectedPrefixProduct
        (n := n) (standardHallFamily.{u} t) e k := by
  unfold freeStandardPrefix collectedPrefixProduct
  rw [map_list_prod]
  apply congrArg List.prod
  simp only [List.map_map]
  apply List.map_congr_left
  intro j _hj
  exact lower_truncation_standard
    t n (j + 1) (e (j + 1))

theorem free_standard_succ
    (t k : ℕ)
    (e : StandardExponentFamily.{u} t) :
    freeStandardPrefix t e (k + 1) =
      freeStandardPrefix t e k *
        freeStandardProduct t (k + 1) (e (k + 1)) := by
  simp [freeStandardPrefix, List.range_succ,
    List.map_append, List.prod_append]

/-- Removing the first `k` lifted Hall weights leaves an element of
`γ_(k+1)` in the free group, provided the lifted coordinates collect to the
given element in the nilpotent truncation. -/
theorem free_standard_series
    (t n k : ℕ)
    (hk : k ≤ n - 1)
    (e : StandardExponentFamily.{u} t)
    (y : FreeGroup (FreeGenerator.{u} t))
    (he :
      standardHallProduct t n e =
        lowerCentralTruncation
          (FreeGroup (FreeGenerator.{u} t)) n y) :
    (freeStandardPrefix t e k)⁻¹ * y ∈
      Subgroup.lowerCentralSeries
        (FreeGroup (FreeGenerator.{u} t)) k := by
  let F := FreeGroup (FreeGenerator.{u} t)
  let K : Subgroup F := Subgroup.lowerCentralSeries F (n - 1)
  let q : F →* F ⧸ K := QuotientGroup.mk' K
  have hmap :
      q ((freeStandardPrefix t e k)⁻¹ * y) =
        collectedTailProduct
          (n := n) (standardHallFamily.{u} t) e k := by
    rw [map_mul, map_inv]
    change
      (lowerCentralTruncation
          (FreeGroup (FreeGenerator.{u} t)) n
          (freeStandardPrefix t e k))⁻¹ *
          lowerCentralTruncation
            (FreeGroup (FreeGenerator.{u} t)) n y =
        collectedTailProduct
          (n := n) (standardHallFamily.{u} t) e k
    rw [truncation_standard_prefix]
    rw [← he]
    change
      (collectedPrefixProduct
          (n := n) (standardHallFamily.{u} t) e k)⁻¹ *
          collectedHallProduct
            (n := n) (standardHallFamily.{u} t) e =
        collectedTailProduct
          (n := n) (standardHallFamily.{u} t) e k
    rw [← collected_prefix_tail
      (standardHallFamily.{u} t) e k hk]
    group
  have hmapMem :
      q ((freeStandardPrefix t e k)⁻¹ * y) ∈
        Subgroup.lowerCentralSeries (F ⧸ K) k := by
    rw [hmap]
    exact collected_tail_series
      (standardHallFamily.{u} t) e k
  have hpreimage :
      (freeStandardPrefix t e k)⁻¹ * y ∈
        Subgroup.comap q (Subgroup.lowerCentralSeries (F ⧸ K) k) :=
    hmapMem
  rw [Edmonton.lower_series_comap K k] at hpreimage
  have hkernelLe :
      K ≤ Subgroup.lowerCentralSeries F k := by
    exact Subgroup.lowerCentralSeries_antitone hk
  rw [sup_eq_right.mpr hkernelLe] at hpreimage
  exact hpreimage

/-- After additionally removing the weight-`s` segment, the residual advances
from `γ_s` to `γ_(s+1)`. -/
theorem standard_next_series
    (t n s : ℕ)
    (hs : 1 ≤ s)
    (hsn : s < n)
    (e : StandardExponentFamily.{u} t)
    (y : FreeGroup (FreeGenerator.{u} t))
    (he :
      standardHallProduct t n e =
        lowerCentralTruncation
          (FreeGroup (FreeGenerator.{u} t)) n y) :
    (freeStandardProduct t s (e s))⁻¹ *
          ((freeStandardPrefix t e (s - 1))⁻¹ * y) ∈
      Subgroup.lowerCentralSeries
        (FreeGroup (FreeGenerator.{u} t)) s := by
  have hresidual :=
    free_standard_series
      t n s (by omega) e y he
  have hsucc :
      freeStandardPrefix t e s =
        freeStandardPrefix t e (s - 1) *
          freeStandardProduct t s (e s) := by
    have hsPred : s - 1 + 1 = s := by omega
    have h :=
      free_standard_succ t (s - 1) e
    rw [hsPred] at h
    exact h
  rw [hsucc] at hresidual
  simpa only [mul_inv_rev, _root_.mul_assoc] using hresidual

/-- The canonical free lower-central Hall coordinate of a collected residual
is the corresponding stored standard Hall exponent. -/
theorem free_standard_coordinate
    (t n s : ℕ)
    (hs : 1 ≤ s)
    (hsn : s < n)
    (e : StandardExponentFamily.{u} t)
    (y : FreeGroup (FreeGenerator.{u} t))
    (he :
      standardHallProduct t n e =
        lowerCentralTruncation
          (FreeGroup (FreeGenerator.{u} t)) n y)
    (hg :
      (freeStandardPrefix t e (s - 1))⁻¹ * y ∈
        Subgroup.lowerCentralSeries
          (FreeGroup (FreeGenerator.{u} t)) (s - 1))
    (j : (standardHallFamily.{u} t s).index) :
    (HallTree.freePBWUniqueness
        (IMagnus.hallPBWInput
          (X := FreeGenerator.{u} t)) hs).repr
        (lowerCentralWeight hg) j.down =
      e s j := by
  let F := FreeGroup (FreeGenerator.{u} t)
  let A : Subgroup F := Subgroup.lowerCentralSeries F (s - 1)
  let B : Subgroup A := (Subgroup.lowerCentralSeries F s).subgroupOf A
  let q : A →* A ⧸ B := QuotientGroup.mk' B
  let residual : F :=
    (freeStandardPrefix t e (s - 1))⁻¹ * y
  let residualTerm : A := ⟨residual, hg⟩
  let segmentTerm : A :=
    freeStandardTerm t s (e s)
  have hnext :
      (freeStandardProduct t s (e s))⁻¹ * residual ∈
        Subgroup.lowerCentralSeries F s := by
    exact standard_next_series
      t n s hs hsn e y he
  have hclass :
      q residualTerm = q segmentTerm := by
    have hone :
        q (segmentTerm⁻¹ * residualTerm) = 1 :=
      (QuotientGroup.eq_one_iff
        (N := B) (segmentTerm⁻¹ * residualTerm)).2 hnext
    rw [map_mul, map_inv] at hone
    exact (inv_mul_eq_one.mp hone).symm
  have hclassAdditive :
      Additive.ofMul (q residualTerm) =
        ∑ i,
          e s i •
            ((standardHallFamily.{u} t s).commutator i
              |>.free_groupassoc_gradedclass) := by
    apply Additive.toMul.injective
    change
      q residualTerm =
        Additive.toMul
          (∑ i,
            e s i •
              ((standardHallFamily.{u} t s).commutator i
                |>.free_groupassoc_gradedclass))
    rw [hclass,
      free_standard_sum]
  let lowerBasis :=
    HallTree.freePBWUniqueness
      (IMagnus.hallPBWInput
        (X := FreeGenerator.{u} t)) hs
  let layerEquiv :=
    lowerGradedLinear F s hs
  let concreteBasis :=
    concretePBWUniqueness
      (IMagnus.hallPBWInput
        (X := FreeGenerator.{u} t)) hs
  have hconcreteBasis :
      ∀ i,
        concreteBasis i =
          ((standardHallFamily.{u} t s).commutator i
            |>.free_groupassoc_gradedclass) := by
    intro i
    dsimp [concreteBasis]
    rw [concretePBWUniqueness,
      Module.Basis.reindex_apply, Module.Basis.map_apply]
    simpa [lowerBasis,
      HallTree.freePBWUniqueness,
      Module.Basis.mk_apply] using
        graded_indexed_tree
          hs i.down
  have hlayerClass :
      layerEquiv (lowerCentralWeight hg) =
        Additive.ofMul (q residualTerm) := by
    apply Additive.ofMul.injective
    rfl
  have hconcreteCoordinate :
      concreteBasis.repr
          (layerEquiv (lowerCentralWeight hg)) j =
        e s j := by
    rw [hlayerClass, hclassAdditive]
    have hsum :
        (∑ i,
          e s i •
            ((standardHallFamily.{u} t s).commutator i
              |>.free_groupassoc_gradedclass)) =
          ∑ i, e s i • concreteBasis i := by
      apply Finset.sum_congr rfl
      intro i _hi
      rw [hconcreteBasis i]
    rw [hsum]
    simp only [map_sum, map_zsmul, Module.Basis.repr_self,
      Finsupp.smul_single_one]
    change
      (Finsupp.lapply j :
        ((standardHallFamily.{u} t s).index →₀ ℤ) →ₗ[ℤ] ℤ)
          (∑ i, Finsupp.single i (e s i)) =
        e s j
    rw [map_sum]
    simp only [Finsupp.lapply_apply]
    rw [Finset.sum_eq_single j]
    · simp
    · intro i _hi hij
      simp [hij]
    · simp
  have hcoordinateTransport :
      concreteBasis.repr
          (layerEquiv (lowerCentralWeight hg)) j =
        lowerBasis.repr (lowerCentralWeight hg) j.down := by
    dsimp [concreteBasis]
    change
      (((lowerBasis.map layerEquiv).reindex Equiv.ulift.symm).repr
          (layerEquiv (lowerCentralWeight hg))) j =
        lowerBasis.repr (lowerCentralWeight hg) j.down
    rw [Module.Basis.repr_reindex_apply]
    simp
  rw [← hcoordinateTransport]
  exact hconcreteCoordinate

/-- A fixed-weight Hall segment with polynomial exponent functions has the
corresponding Magnus polynomial order. -/
theorem standard_magnus_order
    (t weight offset : ℕ)
    (hoffset : offset ≤ weight)
    {e :
      ℕ → (standardHallFamily.{u} t weight).index → ℤ}
    (he :
      ∀ j,
        IVMost
          (fun q => e q j)
          (weight - offset)) :
    MPOrd
      (fun q =>
        magnusDifference (R := ℤ)
          (freeStandardProduct t weight (e q)))
      offset := by
  let indices :=
    Finset.univ.sort
      fun i j : (standardHallFamily.{u} t weight).index => i ≤ j
  let factors : List (ℕ → FreeGroup (FreeGenerator.{u} t)) :=
    indices.map fun j q =>
      ((standardHallFamily.{u} t weight).commutator j
        |>.eval_in_freegroup) ^ e q j
  have hfactor :
      ∀ factor ∈ factors,
        MPOrd
          (fun q => magnusDifference (R := ℤ) (factor q))
          offset := by
    intro factor hfactorMem
    rcases List.mem_map.mp hfactorMem with ⟨j, _hj, rfl⟩
    have hphysical :
        VanishesBelow
          (magnusDifference (R := ℤ)
            ((standardHallFamily.{u} t weight).commutator j
              |>.eval_in_freegroup))
          weight := by
      simpa [BCWt.eval_in_freegroup,
        concrete_basic_word] using
          MPOrd.tree_vanishes_below
            (concreteBasicTree j)
    exact MPOrd.fixedZPow
      ((standardHallFamily.{u} t weight).commutator j
        |>.eval_in_freegroup)
      hphysical hoffset (he j)
  have hproduct :=
    MPOrd.magnus_difference_prod
      factors hfactor
  simpa [factors, indices, freeStandardProduct,
    freeStandardTerm, SubmonoidClass.coe_list_prod,
    List.map_map] using hproduct

/-- If every fixed-weight block in a Hall prefix has a common Magnus
polynomial order, then the whole ordered prefix has that order. -/
theorem free_standard_magnus
    (t k offset : ℕ)
    {e : ℕ → StandardExponentFamily.{u} t}
    (he :
      ∀ weight,
        1 ≤ weight →
          weight ≤ k →
            MPOrd
              (fun q =>
                magnusDifference (R := ℤ)
                  (freeStandardProduct
                    t weight (e q weight)))
              offset) :
    MPOrd
      (fun q =>
        magnusDifference (R := ℤ)
          (freeStandardPrefix t (e q) k))
      offset := by
  let factors : List (ℕ → FreeGroup (FreeGenerator.{u} t)) :=
    (List.range k).map fun j q =>
      freeStandardProduct t (j + 1) (e q (j + 1))
  have hfactor :
      ∀ factor ∈ factors,
        MPOrd
          (fun q => magnusDifference (R := ℤ) (factor q))
          offset := by
    intro factor hfactorMem
    rcases List.mem_map.mp hfactorMem with ⟨j, hj, rfl⟩
    exact he (j + 1) (by omega) (by
      simp only [List.mem_range] at hj
      omega)
  have hproduct :=
    MPOrd.magnus_difference_prod
      factors hfactor
  simpa [factors, freeStandardPrefix,
    List.map_map] using hproduct

/-- A free-group family with uniform lower-central depth and Magnus
polynomial order has polynomial standard Hall coordinates.  The two
parameters are intentionally separate: cancellation may improve the
lower-central depth without improving the polynomial-order offset. -/
theorem standard_coordinates_magnus
    (t n depth offset : ℕ)
    (hn : 2 ≤ n)
    (hoffset : offset ≤ depth)
    (yFree : ℕ → FreeGroup (FreeGenerator.{u} t))
    (hyMem :
      ∀ q,
        yFree q ∈
          Subgroup.lowerCentralSeries
            (FreeGroup (FreeGenerator.{u} t)) depth)
    (hyOrder :
      MPOrd
        (fun q =>
          magnusDifference (R := ℤ) (yFree q))
        offset) :
    ∀ weight : ℕ,
      1 ≤ weight →
        weight < n →
          ∀ j : (standardHallFamily.{u} t weight).index,
            IVMost
              (fun q : ℕ =>
                standardHallCoordinates t n hn
                    (lowerCentralTruncation
                      (FreeGroup (FreeGenerator.{u} t)) n (yFree q))
                    weight j)
              (weight - offset) := by
  let yTrunc :
      ℕ →
        LowerCentralTruncation
          (FreeGroup (FreeGenerator.{u} t)) n :=
    fun q =>
      lowerCentralTruncation
        (FreeGroup (FreeGenerator.{u} t)) n (yFree q)
  let coordinates : ℕ → StandardExponentFamily.{u} t :=
    fun q => standardHallCoordinates t n hn (yTrunc q)
  have hcoordinatesEvaluate :
      ∀ q,
        standardHallProduct t n (coordinates q) =
          lowerCentralTruncation
            (FreeGroup (FreeGenerator.{u} t)) n (yFree q) := by
    intro q
    exact standard_product_coordinates
      t n hn (yTrunc q)
  have hcoordinatePolynomial :
      ∀ weight : ℕ,
        1 ≤ weight →
          weight < n →
            ∀ j : (standardHallFamily.{u} t weight).index,
              IVMost
                (fun q => coordinates q weight j)
                (weight - offset) := by
    intro weight
    induction weight using Nat.strong_induction_on with
    | h weight ih =>
        intro hweight hweightn j
        by_cases hbelow : weight < depth + 1
        · have hzero :
              (fun q => coordinates q weight j) = 0 := by
            funext q
            have hyTrunc :
                yTrunc q ∈ Subgroup.lowerCentralSeries
                  (LowerCentralTruncation
                    (FreeGroup (FreeGenerator.{u} t)) n) depth :=
              Subgroup.lowerCentralSeries.map
                (lowerCentralTruncation
                  (FreeGroup (FreeGenerator.{u} t)) n)
                depth
                (Subgroup.mem_map_of_mem
                  (lowerCentralTruncation
                    (FreeGroup (FreeGenerator.{u} t)) n)
                  (hyMem q))
            have hlow :=
              imp_coordinates_below
                hn (standardHallFamily.{u} t)
                (fun w _hw hwn =>
                  standard_forms_associated
                    t n w (by omega) hwn)
                (coordinates q)
                (by
                  change
                    standardHallProduct t n (coordinates q) ∈
                      Subgroup.lowerCentralSeries
                        (LowerCentralTruncation
                          (FreeGroup (FreeGenerator.{u} t)) n) depth
                  rw [hcoordinatesEvaluate q]
                  exact hyTrunc)
                weight hweight hbelow hweightn
            exact congrFun hlow j
          rw [hzero]
          exact IVMost.zero _
        · have hdepthWeight : depth + 1 ≤ weight :=
            Nat.le_of_not_gt hbelow
          have hprefix :
              MPOrd
                (fun q =>
                  magnusDifference (R := ℤ)
                    (freeStandardPrefix
                      t (coordinates q) (weight - 1)))
                offset := by
            apply
              free_standard_magnus
                t (weight - 1) offset
            intro earlier hearlier hearlierLe
            by_cases hearlierBelow : earlier < depth + 1
            · have hzero :
                  ∀ q, coordinates q earlier = 0 := by
                intro q
                have hyTrunc :
                    yTrunc q ∈ Subgroup.lowerCentralSeries
                      (LowerCentralTruncation
                        (FreeGroup (FreeGenerator.{u} t)) n) depth :=
                  Subgroup.lowerCentralSeries.map
                    (lowerCentralTruncation
                      (FreeGroup (FreeGenerator.{u} t)) n)
                    depth
                    (Subgroup.mem_map_of_mem
                      (lowerCentralTruncation
                        (FreeGroup (FreeGenerator.{u} t)) n)
                      (hyMem q))
                exact
                  imp_coordinates_below
                    hn (standardHallFamily.{u} t)
                    (fun w _hw hwn =>
                      standard_forms_associated
                        t n w (by omega) hwn)
                    (coordinates q)
                    (by
                      change
                        standardHallProduct t n (coordinates q) ∈
                          Subgroup.lowerCentralSeries
                            (LowerCentralTruncation
                              (FreeGroup (FreeGenerator.{u} t)) n) depth
                      rw [hcoordinatesEvaluate q]
                      exact hyTrunc)
                    earlier hearlier hearlierBelow (by omega)
              have hfamily :
                  (fun q =>
                    magnusDifference (R := ℤ)
                      (freeStandardProduct
                        t earlier (coordinates q earlier))) =
                      fun _ => 0 := by
                funext q
                rw [hzero q, free_standard_zero]
                simp [magnusDifference]
              rw [hfamily]
              exact MPOrd.zero offset
            · apply
                standard_magnus_order
                  t earlier offset (by omega)
              intro earlierIndex
              exact ih earlier (by omega)
                hearlier (by omega) earlierIndex
          have hresidual :
              MPOrd
                (fun q =>
                  magnusDifference (R := ℤ)
                    ((freeStandardPrefix
                        t (coordinates q) (weight - 1))⁻¹ *
                      yFree q))
                offset :=
            hprefix.magnusDifference_inv.magnusDifference_mul
              hyOrder
          let L :
              AssociativeHomogeneousWords
                  ℤ (FreeGenerator.{u} t) weight →ₗ[ℤ] ℤ :=
            HMCoord.linearMap j.down
          have hpolynomial :=
            hresidual.linear_homogeneous_part L
          have hread :
              (fun q =>
                L (homogeneousPart weight
                  (magnusDifference (R := ℤ)
                    ((freeStandardPrefix
                        t (coordinates q) (weight - 1))⁻¹ *
                      yFree q)))) =
                fun q => coordinates q weight j := by
            funext q
            have hresidualMem :
                (freeStandardPrefix
                      t (coordinates q) (weight - 1))⁻¹ *
                    yFree q ∈
                  Subgroup.lowerCentralSeries
                    (FreeGroup (FreeGenerator.{u} t))
                    (weight - 1) :=
              free_standard_series
                t n (weight - 1) (by omega)
                (coordinates q) (yFree q)
                (hcoordinatesEvaluate q)
            calc
              L (homogeneousPart weight
                  (magnusDifference (R := ℤ)
                    ((freeStandardPrefix
                        t (coordinates q) (weight - 1))⁻¹ *
                      yFree q))) =
                  (HallTree.freePBWUniqueness
                      (IMagnus.hallPBWInput
                        (X := FreeGenerator.{u} t)) hweight).repr
                    (lowerCentralWeight hresidualMem) j.down := by
                      exact
                        HMCoord.linear_lower_class
                          hweight hresidualMem j.down
              _ = coordinates q weight j :=
                free_standard_coordinate
                  t n weight hweight hweightn
                  (coordinates q) (yFree q)
                  (hcoordinatesEvaluate q)
                  hresidualMem j
          rw [hread] at hpolynomial
          exact hpolynomial
  simpa [coordinates, yTrunc] using hcoordinatePolynomial

/-- The Hall coordinate of a fixed lower-central element raised to its
`q`th power is an integer-valued polynomial in `q`.  If the element starts
in one-based weight `r`, the coordinate in weight `s` has degree at most
`s - (r - 1)`.  The case `r = 1` is the polynomial assertion in Struik's
Theorems H2 and H3. -/
theorem standard_coordinates_fixed
    (t n r : ℕ)
    (hn : 2 ≤ n)
    (hr : 1 ≤ r)
    (y : FreeGroup (FreeGenerator.{u} t))
    (hy :
      y ∈ Subgroup.lowerCentralSeries
        (FreeGroup (FreeGenerator.{u} t)) (r - 1)) :
    ∀ s : ℕ,
      1 ≤ s →
        s < n →
          ∀ j : (standardHallFamily.{u} t s).index,
            IVMost
              (fun q : ℕ =>
                standardHallCoordinates t n hn
                    (lowerCentralTruncation
                      (FreeGroup (FreeGenerator.{u} t)) n (y ^ q))
                    s j)
              (s - (r - 1)) := by
  let yFree : ℕ → FreeGroup (FreeGenerator.{u} t) :=
    fun q => y ^ q
  let yTrunc :
      ℕ →
        LowerCentralTruncation
          (FreeGroup (FreeGenerator.{u} t)) n :=
    fun q =>
      lowerCentralTruncation
        (FreeGroup (FreeGenerator.{u} t)) n (yFree q)
  let coordinates : ℕ → StandardExponentFamily.{u} t :=
    fun q => standardHallCoordinates t n hn (yTrunc q)
  have hcoordinatesEvaluate :
      ∀ q,
        standardHallProduct t n (coordinates q) =
          lowerCentralTruncation
            (FreeGroup (FreeGenerator.{u} t)) n (yFree q) := by
    intro q
    exact standard_product_coordinates
      t n hn (yTrunc q)
  have hyMagnus :
      VanishesBelow
        (magnusDifference (R := ℤ) y) r := by
    have hy' :
        y ∈
          EChapma.MSeries.magnusOrderSubgroup
            (R := ℤ) (X := FreeGenerator.{u} t) r := by
      have hle :=
        EChapma.MSeries.lower_magnus_subgroup
            (R := ℤ) (X := FreeGenerator.{u} t) (r - 1)
      simpa [Nat.sub_add_cancel hr] using hle hy
    exact hy'
  have hcoordinatePolynomial :
      ∀ weight : ℕ,
        1 ≤ weight →
          weight < n →
            ∀ j : (standardHallFamily.{u} t weight).index,
              IVMost
                (fun q => coordinates q weight j)
                (weight - (r - 1)) := by
    intro weight
    induction weight using Nat.strong_induction_on with
    | h weight ih =>
        intro hweight hweightn j
        by_cases hbelow : weight < r
        · have hzero :
              (fun q => coordinates q weight j) = 0 := by
            funext q
            have hyPower :
                yFree q ∈ Subgroup.lowerCentralSeries
                  (FreeGroup (FreeGenerator.{u} t)) (r - 1) :=
              (Subgroup.lowerCentralSeries
                (FreeGroup (FreeGenerator.{u} t)) (r - 1)).pow_mem hy q
            have hyTrunc :
                yTrunc q ∈ Subgroup.lowerCentralSeries
                  (LowerCentralTruncation
                    (FreeGroup (FreeGenerator.{u} t)) n) (r - 1) :=
              Subgroup.lowerCentralSeries.map
                (lowerCentralTruncation
                  (FreeGroup (FreeGenerator.{u} t)) n)
                (r - 1)
                (Subgroup.mem_map_of_mem
                  (lowerCentralTruncation
                    (FreeGroup (FreeGenerator.{u} t)) n)
                  hyPower)
            have hlow :=
              imp_coordinates_below
                hn (standardHallFamily.{u} t)
                (fun w _hw hwn =>
                  standard_forms_associated
                    t n w (by omega) hwn)
                (coordinates q)
                (by
                  change
                    standardHallProduct t n (coordinates q) ∈
                      Subgroup.lowerCentralSeries
                        (LowerCentralTruncation
                          (FreeGroup (FreeGenerator.{u} t)) n) (r - 1)
                  rw [hcoordinatesEvaluate q]
                  exact hyTrunc)
                weight hweight hbelow hweightn
            exact congrFun hlow j
          rw [hzero]
          exact IVMost.zero _
        · have hrle : r ≤ weight := Nat.le_of_not_gt hbelow
          have hprefix :
              MPOrd
                (fun q =>
                  magnusDifference (R := ℤ)
                    (freeStandardPrefix
                      t (coordinates q) (weight - 1)))
                (r - 1) := by
            apply
              free_standard_magnus
                t (weight - 1) (r - 1)
            intro earlier hearlier hearlierLe
            by_cases hearlierBelow : earlier < r
            · have hzero :
                  ∀ q, coordinates q earlier = 0 := by
                intro q
                have hyPower :
                    yFree q ∈ Subgroup.lowerCentralSeries
                      (FreeGroup (FreeGenerator.{u} t)) (r - 1) :=
                  (Subgroup.lowerCentralSeries
                    (FreeGroup (FreeGenerator.{u} t)) (r - 1)).pow_mem hy q
                have hyTrunc :
                    yTrunc q ∈ Subgroup.lowerCentralSeries
                      (LowerCentralTruncation
                        (FreeGroup (FreeGenerator.{u} t)) n) (r - 1) :=
                  Subgroup.lowerCentralSeries.map
                    (lowerCentralTruncation
                      (FreeGroup (FreeGenerator.{u} t)) n)
                    (r - 1)
                    (Subgroup.mem_map_of_mem
                      (lowerCentralTruncation
                        (FreeGroup (FreeGenerator.{u} t)) n)
                      hyPower)
                exact
                  imp_coordinates_below
                    hn (standardHallFamily.{u} t)
                    (fun w _hw hwn =>
                      standard_forms_associated
                        t n w (by omega) hwn)
                    (coordinates q)
                    (by
                      change
                        standardHallProduct t n (coordinates q) ∈
                          Subgroup.lowerCentralSeries
                            (LowerCentralTruncation
                              (FreeGroup (FreeGenerator.{u} t)) n) (r - 1)
                      rw [hcoordinatesEvaluate q]
                      exact hyTrunc)
                    earlier hearlier hearlierBelow (by omega)
              have hfamily :
                  (fun q =>
                    magnusDifference (R := ℤ)
                      (freeStandardProduct
                        t earlier (coordinates q earlier))) =
                    fun _ => 0 := by
                funext q
                rw [hzero q, free_standard_zero]
                simp [magnusDifference]
              rw [hfamily]
              exact MPOrd.zero (r - 1)
            · apply
                standard_magnus_order
                  t earlier (r - 1) (by omega)
              intro earlierIndex
              exact ih earlier (by omega)
                hearlier (by omega) earlierIndex
          have hyOrder :
              MPOrd
                (fun q =>
                  magnusDifference (R := ℤ) (yFree q))
                (r - 1) := by
            let exponent : ℕ → ℤ := fun q => q
            have hexponent :
                IVMost exponent 1 := by
              refine ⟨Polynomial.X, by simp, ?_⟩
              intro q
              simp [exponent]
            have hexponent' :
                IVMost exponent (r - (r - 1)) := by
              simpa [show r - (r - 1) = 1 by omega] using hexponent
            simpa [yFree, exponent, Nat.sub_add_cancel hr] using
              MPOrd.fixedZPow
                y hyMagnus (Nat.sub_le r 1) hexponent'
          have hresidual :
              MPOrd
                (fun q =>
                  magnusDifference (R := ℤ)
                    ((freeStandardPrefix
                        t (coordinates q) (weight - 1))⁻¹ *
                      yFree q))
                (r - 1) :=
            hprefix.magnusDifference_inv.magnusDifference_mul hyOrder
          let L :
              AssociativeHomogeneousWords
                  ℤ (FreeGenerator.{u} t) weight →ₗ[ℤ] ℤ :=
            HMCoord.linearMap j.down
          have hpolynomial :=
            hresidual.linear_homogeneous_part L
          have hread :
              (fun q =>
                L (homogeneousPart weight
                  (magnusDifference (R := ℤ)
                    ((freeStandardPrefix
                        t (coordinates q) (weight - 1))⁻¹ *
                      yFree q)))) =
                fun q => coordinates q weight j := by
            funext q
            have hresidualMem :
                (freeStandardPrefix
                      t (coordinates q) (weight - 1))⁻¹ *
                    yFree q ∈
                  Subgroup.lowerCentralSeries
                    (FreeGroup (FreeGenerator.{u} t))
                    (weight - 1) :=
              free_standard_series
                t n (weight - 1) (by omega)
                (coordinates q) (yFree q)
                (hcoordinatesEvaluate q)
            calc
              L (homogeneousPart weight
                  (magnusDifference (R := ℤ)
                    ((freeStandardPrefix
                        t (coordinates q) (weight - 1))⁻¹ *
                      yFree q))) =
                  (HallTree.freePBWUniqueness
                      (IMagnus.hallPBWInput
                        (X := FreeGenerator.{u} t)) hweight).repr
                    (lowerCentralWeight hresidualMem) j.down := by
                      exact
                        HMCoord.linear_lower_class
                          hweight hresidualMem j.down
              _ = coordinates q weight j :=
                free_standard_coordinate
                  t n weight hweight hweightn
                  (coordinates q) (yFree q)
                  (hcoordinatesEvaluate q)
                  hresidualMem j
          rw [hread] at hpolynomial
          exact hpolynomial
  simpa [coordinates, yTrunc, yFree] using
    hcoordinatePolynomial

/-- Equation (3) for the canonical Hall coordinates: the polynomial
coordinate of a fixed power has an integral Newton expansion in ordinary
binomial coefficients. -/
theorem standard_binomial_expansion
    (t n : ℕ)
    (hn : 2 ≤ n)
    (y : FreeGroup (FreeGenerator.{u} t))
    (s : ℕ)
    (hs : 1 ≤ s)
    (hsn : s < n)
    (j : (standardHallFamily.{u} t s).index)
    (q : ℕ) :
    let f : ℕ → ℤ :=
      fun m =>
        standardHallCoordinates t n hn
            (lowerCentralTruncation
              (FreeGroup (FreeGenerator.{u} t)) n (y ^ m))
            s j
    f q =
      ∑ k ∈ Finset.range (s + 1),
        natBinomialCoefficient f k * (Nat.choose q k : ℤ) := by
  dsimp only
  have hpolynomial :=
    standard_coordinates_fixed
      t n 1 hn (by omega) y (by simp)
      s hs hsn j
  simpa using hpolynomial.nat_binomial_basisexpansion q

/-- General polynomial degree bound for the powered-leaf coordinates of an
arbitrary parenthesized Hall tree in Struik's Lemma H2. -/
theorem powered_leaf_general
    (t n : ℕ)
    (hn : 2 ≤ n) :
    TreePoweredLeaf.{u} t n := by
  intro tree hrn leaf s hrs hsn j
  let r := tree.weight
  have hr : 1 ≤ r := by
    simpa [r] using tree.weight_pos
  have hrn' : r < n := by
    simpa [r] using hrn
  let yFree : ℕ → FreeGroup (FreeGenerator.{u} t) :=
    fun q =>
      HallTree.leafOccurrencePow
        FreeGroup.of q tree leaf
  let yTrunc :
      ℕ →
        LowerCentralTruncation
          (FreeGroup (FreeGenerator.{u} t)) n :=
    fun q =>
      HallTree.leafOccurrencePow
        (freeTruncationValue t n) q tree leaf
  let coordinates : ℕ → StandardExponentFamily.{u} t :=
    fun q => standardHallCoordinates t n hn (yTrunc q)
  have hyMap :
      ∀ q,
        lowerCentralTruncation
            (FreeGroup (FreeGenerator.{u} t)) n (yFree q) =
          yTrunc q := by
    intro q
    dsimp only [yFree, yTrunc]
    simpa only [freeTruncationValue] using
      HallTree.eval_leaf_pow
        (lowerCentralTruncation
          (FreeGroup (FreeGenerator.{u} t)) n)
        FreeGroup.of q leaf
  have hcoordinatesEvaluate :
      ∀ q,
        standardHallProduct t n (coordinates q) =
          lowerCentralTruncation
            (FreeGroup (FreeGenerator.{u} t)) n (yFree q) := by
    intro q
    rw [show
      standardHallProduct t n (coordinates q) =
        yTrunc q by
          exact standard_product_coordinates
            t n hn (yTrunc q)]
    exact (hyMap q).symm
  have hcoordinatePolynomial :
      ∀ weight : ℕ,
        1 ≤ weight →
          weight < n →
            ∀ k : (standardHallFamily.{u} t weight).index,
              IVMost
                (fun q => coordinates q weight k)
                (weight - (r - 1)) := by
    intro weight
    induction weight using Nat.strong_induction_on with
    | h weight ih =>
        intro hweight hweightn k
        by_cases hbelow : weight < r
        · have hzero :
              (fun q => coordinates q weight k) = 0 := by
            funext q
            have hlow :=
              (powered_leaf_leading
                hn tree hrn leaf q).1
                weight hweight hbelow hweightn
            exact congrFun hlow k
          rw [hzero]
          exact IVMost.zero _
        · have hrle : r ≤ weight := Nat.le_of_not_gt hbelow
          by_cases hweightEq : weight = r
          · subst weight
            let base :=
              tree.toCWord.eval
                (freeTruncationValue t n)
            have hleading :
                ∀ q,
                  coordinates q r k =
                    (q : ℤ) *
                      standardHallCoordinates t n hn base r k := by
              intro q
              exact congrFun
                (powered_leaf_leading
                  hn tree hrn leaf q).2 k
            have hnatCast :
                IVMost
                  (fun q : ℕ => (q : ℤ))
                  1 := by
              refine ⟨Polynomial.X, by simp, ?_⟩
              intro q
              simp
            have hlinear :=
              IVMost.smul
                (standardHallCoordinates t n hn base r k) hnatCast
            have hfamily :
                (fun q => coordinates q r k) =
                  (standardHallCoordinates t n hn base r k) •
                    (fun q : ℕ => (q : ℤ)) := by
              funext q
              rw [hleading q]
              simp [mul_comm]
            rw [hfamily]
            exact hlinear.mono (by omega)
          · have hrlt : r < weight := by omega
            have hprefix :
                MPOrd
                  (fun q =>
                    magnusDifference (R := ℤ)
                      (freeStandardPrefix
                        t (coordinates q) (weight - 1)))
                  (r - 1) := by
              apply
                free_standard_magnus
                  t (weight - 1) (r - 1)
              intro earlier hearliar hearliarLe
              by_cases hearliarBelow : earlier < r
              · have hzero :
                    ∀ q, coordinates q earlier = 0 := by
                  intro q
                  have hlow :=
                    (powered_leaf_leading
                      hn tree hrn leaf q).1
                      earlier hearliar hearliarBelow (by omega)
                  exact hlow
                have hfamily :
                    (fun q =>
                      magnusDifference (R := ℤ)
                        (freeStandardProduct
                          t earlier (coordinates q earlier))) =
                      fun _ => 0 := by
                  funext q
                  rw [hzero q,
                    free_standard_zero]
                  simp [magnusDifference]
                rw [hfamily]
                exact MPOrd.zero (r - 1)
              · apply
                  standard_magnus_order
                    t earlier (r - 1) (by omega)
                intro earlierIndex
                exact ih earlier (by omega)
                  hearliar (by omega) earlierIndex
            have hyOrder :
                MPOrd
                  (fun q =>
                    magnusDifference (R := ℤ) (yFree q))
                  (r - 1) := by
              simpa [yFree, r] using
                  MPOrd.leafOccurrencePow
                    tree leaf
            have hresidual :
                MPOrd
                  (fun q =>
                    magnusDifference (R := ℤ)
                      ((freeStandardPrefix
                          t (coordinates q) (weight - 1))⁻¹ *
                        yFree q))
                  (r - 1) :=
              hprefix.magnusDifference_inv.magnusDifference_mul
                hyOrder
            let L :
                AssociativeHomogeneousWords
                    ℤ (FreeGenerator.{u} t) weight →ₗ[ℤ] ℤ :=
              HMCoord.linearMap
                k.down
            have hpolynomial :=
              hresidual.linear_homogeneous_part L
            have hread :
                (fun q =>
                  L (homogeneousPart weight
                    (magnusDifference (R := ℤ)
                      ((freeStandardPrefix
                          t (coordinates q) (weight - 1))⁻¹ *
                        yFree q)))) =
                  fun q => coordinates q weight k := by
              funext q
              have hresidualMem :
                  (freeStandardPrefix
                        t (coordinates q) (weight - 1))⁻¹ *
                      yFree q ∈
                    Subgroup.lowerCentralSeries
                      (FreeGroup (FreeGenerator.{u} t))
                      (weight - 1) :=
                free_standard_series
                  t n (weight - 1) (by omega)
                  (coordinates q) (yFree q)
                  (hcoordinatesEvaluate q)
              calc
                L (homogeneousPart weight
                    (magnusDifference (R := ℤ)
                      ((freeStandardPrefix
                          t (coordinates q) (weight - 1))⁻¹ *
                        yFree q))) =
                    (HallTree.freePBWUniqueness
                        (IMagnus.hallPBWInput
                          (X := FreeGenerator.{u} t)) hweight).repr
                      (lowerCentralWeight hresidualMem) k.down := by
                        exact
                          HMCoord.linear_lower_class
                            hweight hresidualMem k.down
                _ = coordinates q weight k :=
                  free_standard_coordinate
                    t n weight hweight hweightn
                    (coordinates q) (yFree q)
                    (hcoordinatesEvaluate q)
                    hresidualMem k
            rw [hread] at hpolynomial
            exact hpolynomial
  simpa [coordinates, yTrunc, r] using
    hcoordinatePolynomial s (by omega) hsn j

/-- The arbitrary-tree polynomial theorem specializes to the canonical
standard Hall basis used by Lemma 1. -/
theorem powered_data_general
    (t n : ℕ)
    (hn : 2 ≤ n) :
    PoweredLeafCoordinate.{u} t n := by
  intro r _hr hrn i leaf s hrs hsn j
  simpa [concrete_tree_weight] using
    powered_leaf_general t n hn
      (concreteBasicTree i)
      (by simpa [concrete_tree_weight] using hrn)
      leaf s (by simpa [concrete_tree_weight] using hrs) hsn j

/-- The displayed group equality in Lemma H2 for an arbitrary parenthesized
commutator tree in the universal free nilpotent truncation.  The correction
is recollected into one standard Hall product, and all of its coordinates
through the source-tree weight vanish. -/
theorem generalCoordinatesRecollection
    (t n : ℕ)
    (hn : 2 ≤ n)
    (tree : HallTree (FreeGenerator.{u} t))
    (leaf : HallTree.LOccur tree)
    (m : ℕ) :
    let y :=
      HallTree.leafOccurrencePow
        (freeTruncationValue t n) m tree leaf
    let base :=
      tree.toCWord.eval
        (freeTruncationValue t n)
    ∃ e : StandardExponentFamily.{u} t,
      (∀ s : ℕ,
        1 ≤ s →
          s < tree.weight + 1 →
            s < n →
              e s = 0) ∧
        (∀ a : FreeGenerator.{u} t,
          hallTreeUses a tree →
            ∀ (s : ℕ),
              1 ≤ s →
                s < n →
                  ∀ j : (standardHallFamily.{u} t s).index,
                    ¬hallTreeUses a (concreteBasicTree j) →
                      e s j = 0) ∧
        y = base ^ m * standardHallProduct t n e := by
  let y :=
    HallTree.leafOccurrencePow
      (freeTruncationValue t n) m tree leaf
  let base :=
    tree.toCWord.eval
      (freeTruncationValue t n)
  let correction := (base ^ m)⁻¹ * y
  have hscaled :
      y * (base ^ m)⁻¹ ∈
        Subgroup.lowerCentralSeries
          (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} t)) n)
          tree.weight := by
    exact
      HallTree.leaf_occurrence_series
        (freeTruncationValue t n) tree leaf m
  have hcorrection :
      correction ∈
        Subgroup.lowerCentralSeries
          (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} t)) n)
          tree.weight := by
    have hconjugate :=
      (inferInstance :
        (Subgroup.lowerCentralSeries
          (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} t)) n)
          tree.weight).Normal).conj_mem
        (y * (base ^ m)⁻¹) hscaled (base ^ m)⁻¹
    change (base ^ m)⁻¹ * y ∈
      Subgroup.lowerCentralSeries
        (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} t)) n)
        tree.weight
    rw [show
      (base ^ m)⁻¹ * y =
        (base ^ m)⁻¹ * (y * (base ^ m)⁻¹) * base ^ m by group]
    simpa only [inv_inv] using hconjugate
  let e := standardHallCoordinates t n hn correction
  have heProduct : standardHallProduct t n e = correction :=
    standard_product_coordinates t n hn correction
  have heZero :
      ∀ s : ℕ,
        1 ≤ s →
          s < tree.weight + 1 →
            s < n →
              e s = 0 :=
    standard_coordinates_series
      t n (tree.weight + 1) hn correction
        (by simpa using hcorrection)
  have heSupport :
      ∀ a : FreeGenerator.{u} t,
        hallTreeUses a tree →
          ∀ (s : ℕ),
            1 ≤ s →
              s < n →
                ∀ j : (standardHallFamily.{u} t s).index,
                  ¬hallTreeUses a (concreteBasicTree j) →
                    e s j = 0 := by
    intro a huses s hs hsn j hnotUses
    have hmap :
        eraseTruncationGenerator t n a correction = 1 := by
      rw [map_mul, map_inv, map_pow]
      change
        (eraseTruncationGenerator t n a
            (tree.toCWord.eval
              (freeTruncationValue t n)) ^ m)⁻¹ *
            eraseTruncationGenerator t n a
              (HallTree.leafOccurrencePow
                (freeTruncationValue t n) m tree leaf) =
          1
      rw [
        erase_truncation_uses
          t n a tree huses,
        erase_tree_uses
          t n a tree leaf m huses]
      simp
    exact
      standard_erase_uses
        t n hn a correction hmap s hs hsn j hnotUses
  refine ⟨e, heZero, heSupport, ?_⟩
  rw [heProduct]
  change y = base ^ m * correction
  simp [correction]

/-- Struik's natural-power Lemma H2 with one canonical correction family
for all exponents.  The exact correction coordinates simultaneously satisfy
the strict higher-weight condition, the all-input support condition, and the
sharp polynomial degree bound from the paper. -/
theorem standardCorrectionCoordinates
    (t n : ℕ)
    (hn : 2 ≤ n)
    (tree : HallTree (FreeGenerator.{u} t))
    (leaf : HallTree.LOccur tree) :
    ∃ correction : ℕ → StandardExponentFamily.{u} t,
      (∀ q : ℕ,
        HallTree.leafOccurrencePow
            (freeTruncationValue t n) q tree leaf =
          (tree.toCWord.eval
              (freeTruncationValue t n)) ^ q *
            standardHallProduct t n (correction q)) ∧
        (∀ q s : ℕ,
          1 ≤ s →
            s < tree.weight + 1 →
              s < n →
                correction q s = 0) ∧
          (∀ q : ℕ,
            ∀ a : FreeGenerator.{u} t,
              hallTreeUses a tree →
                ∀ (s : ℕ),
                  1 ≤ s →
                    s < n →
                      ∀ j : (standardHallFamily.{u} t s).index,
                        ¬hallTreeUses a (concreteBasicTree j) →
                          correction q s j = 0) ∧
            ∀ s : ℕ,
              1 ≤ s →
                s < n →
                  ∀ j : (standardHallFamily.{u} t s).index,
                    IVMost
                      (fun q : ℕ => correction q s j)
                      (s - (tree.weight - 1)) := by
  let baseFree : FreeGroup (FreeGenerator.{u} t) :=
    tree.toCWord.eval FreeGroup.of
  let poweredFree : ℕ → FreeGroup (FreeGenerator.{u} t) :=
    fun q =>
      HallTree.leafOccurrencePow FreeGroup.of q tree leaf
  let correctionFree : ℕ → FreeGroup (FreeGenerator.{u} t) :=
    fun q => (baseFree ^ q)⁻¹ * poweredFree q
  let truncationMap :
      FreeGroup (FreeGenerator.{u} t) →*
        LowerCentralTruncation
          (FreeGroup (FreeGenerator.{u} t)) n :=
    lowerCentralTruncation
      (FreeGroup (FreeGenerator.{u} t)) n
  let correction : ℕ → StandardExponentFamily.{u} t :=
    fun q =>
      standardHallCoordinates t n hn
        (truncationMap (correctionFree q))
  have hbaseMap :
      truncationMap baseFree =
        tree.toCWord.eval
          (freeTruncationValue t n) := by
    simpa [truncationMap, baseFree,
      freeTruncationValue] using
        (CWord.map_eval
          (lowerCentralTruncation
            (FreeGroup (FreeGenerator.{u} t)) n)
          FreeGroup.of tree.toCWord)
  have hpoweredMap (q : ℕ) :
      truncationMap (poweredFree q) =
        HallTree.leafOccurrencePow
          (freeTruncationValue t n) q tree leaf := by
    change
      lowerCentralTruncation
          (FreeGroup (FreeGenerator.{u} t)) n
          (HallTree.leafOccurrencePow
            FreeGroup.of q tree leaf) =
        HallTree.leafOccurrencePow
          (freeTruncationValue t n) q tree leaf
    rw [HallTree.eval_leaf_pow]
    rfl
  have hcorrectionMem :
      ∀ q,
        correctionFree q ∈
          Subgroup.lowerCentralSeries
            (FreeGroup (FreeGenerator.{u} t)) tree.weight := by
    intro q
    have hscaled :
        poweredFree q * (baseFree ^ q)⁻¹ ∈
          Subgroup.lowerCentralSeries
            (FreeGroup (FreeGenerator.{u} t)) tree.weight := by
      simpa [poweredFree, baseFree] using
        HallTree.leaf_occurrence_series
          FreeGroup.of tree leaf q
    have hconjugate :=
      (inferInstance :
        (Subgroup.lowerCentralSeries
          (FreeGroup (FreeGenerator.{u} t))
          tree.weight).Normal).conj_mem
        (poweredFree q * (baseFree ^ q)⁻¹) hscaled
        (baseFree ^ q)⁻¹
    change
      (baseFree ^ q)⁻¹ * poweredFree q ∈
        Subgroup.lowerCentralSeries
          (FreeGroup (FreeGenerator.{u} t)) tree.weight
    rw [show
      (baseFree ^ q)⁻¹ * poweredFree q =
        (baseFree ^ q)⁻¹ *
          (poweredFree q * (baseFree ^ q)⁻¹) *
            baseFree ^ q by group]
    simpa only [inv_inv] using hconjugate
  have hbaseMagnus :
      VanishesBelow
        (magnusDifference (R := ℤ) baseFree) tree.weight := by
    simpa [baseFree] using
      MPOrd.tree_vanishes_below tree
  let exponent : ℕ → ℤ := fun q => q
  have hexponent :
      IVMost exponent 1 := by
    refine ⟨Polynomial.X, by simp, ?_⟩
    intro q
    simp [exponent]
  have htreeWeight : 1 ≤ tree.weight := tree.weight_pos
  have hexponent' :
      IVMost exponent
        (tree.weight - (tree.weight - 1)) := by
    simpa [show tree.weight - (tree.weight - 1) = 1 by
      omega] using hexponent
  have hbasePowerOrder :
      MPOrd
        (fun q =>
          magnusDifference (R := ℤ) (baseFree ^ q))
        (tree.weight - 1) := by
    simpa [exponent] using
      MPOrd.fixedZPow
        baseFree hbaseMagnus
        (Nat.sub_le tree.weight 1) hexponent'
  have hpoweredOrder :
      MPOrd
        (fun q =>
          magnusDifference (R := ℤ) (poweredFree q))
        (tree.weight - 1) := by
    simpa [poweredFree] using
      MPOrd.leafOccurrencePow tree leaf
  have hcorrectionOrder :
      MPOrd
        (fun q =>
          magnusDifference (R := ℤ) (correctionFree q))
        (tree.weight - 1) := by
    simpa [correctionFree] using
      hbasePowerOrder.magnusDifference_inv.magnusDifference_mul
        hpoweredOrder
  have hPolynomial :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            ∀ j : (standardHallFamily.{u} t s).index,
              IVMost
                (fun q : ℕ => correction q s j)
                (s - (tree.weight - 1)) := by
    simpa [correction, truncationMap] using
      standard_coordinates_magnus
        t n tree.weight (tree.weight - 1) hn
        (Nat.sub_le tree.weight 1)
        correctionFree hcorrectionMem hcorrectionOrder
  refine ⟨correction, ?_, ?_, ?_, hPolynomial⟩
  · intro q
    rw [← hpoweredMap q, ← hbaseMap]
    rw [show
      standardHallProduct t n (correction q) =
        truncationMap (correctionFree q) by
          exact standard_product_coordinates
            t n hn (truncationMap (correctionFree q))]
    rw [← map_pow, ← map_mul]
    congr 1
    simp [correctionFree]
  · intro q s hs hsTree hsn
    have htruncMem :
        truncationMap (correctionFree q) ∈
          Subgroup.lowerCentralSeries
            (LowerCentralTruncation
              (FreeGroup (FreeGenerator.{u} t)) n)
            tree.weight :=
      Subgroup.lowerCentralSeries.map truncationMap tree.weight
        (Subgroup.mem_map_of_mem truncationMap (hcorrectionMem q))
    exact
      standard_coordinates_series
        t n (tree.weight + 1) hn
          (truncationMap (correctionFree q))
          (by simpa using htruncMem)
          s hs hsTree hsn
  · intro q a huses s hs hsn j hnotUses
    have hmap :
        eraseTruncationGenerator t n a
            (truncationMap (correctionFree q)) =
          1 := by
      rw [show
        truncationMap (correctionFree q) =
          (truncationMap baseFree ^ q)⁻¹ *
            truncationMap (poweredFree q) by
          simp [correctionFree]]
      rw [map_mul, map_inv, map_pow]
      rw [hbaseMap, hpoweredMap]
      rw [
        erase_truncation_uses
          t n a tree huses,
        erase_tree_uses
          t n a tree leaf q huses]
      simp
    exact
      standard_erase_uses
        t n hn a
          (truncationMap (correctionFree q)) hmap
          s hs hsn j hnotUses

/-- A signed integer-valued polynomial is represented by one rational
polynomial on every integer input, not merely on the natural half-line. -/
def ValuedIntegersMost
    (f : ℤ → ℤ)
    (degreeBound : ℕ) :
    Prop :=
  ∃ P : Polynomial ℚ,
    P.natDegree ≤ degreeBound ∧
      ∀ z : ℤ, P.eval (z : ℚ) = (f z : ℚ)

/-- The canonical signed correction coordinates in Lemma H2. -/
noncomputable def signedCorrectionCoordinates
    (t n : ℕ)
    (hn : 2 ≤ n)
    (tree : HallTree (FreeGenerator.{u} t))
    (leaf : HallTree.LOccur tree)
    (z : ℤ) :
    StandardExponentFamily.{u} t :=
  standardHallCoordinates t n hn
    ((tree.toCWord.eval
        (freeTruncationValue t n) ^ z)⁻¹ *
      HallTree.leafOccurrenceZ
        (freeTruncationValue t n) z tree leaf)

/-- Composing the canonical signed correction coordinate with any
degree-one integer polynomial preserves Struik's sharp coordinate-degree
bound. -/
theorem signed_correction_comp
    (t n : ℕ)
    (hn : 2 ≤ n)
    (tree : HallTree (FreeGenerator.{u} t))
    (leaf : HallTree.LOccur tree)
    (exponent : ℕ → ℤ)
    (hexponent : IVMost exponent 1)
    (s : ℕ)
    (hs : 1 ≤ s)
    (hsn : s < n)
    (j : (standardHallFamily.{u} t s).index) :
    IVMost
      (fun q =>
        signedCorrectionCoordinates
          t n hn tree leaf (exponent q) s j)
      (s - (tree.weight - 1)) := by
  let baseFree : FreeGroup (FreeGenerator.{u} t) :=
    tree.toCWord.eval FreeGroup.of
  let poweredFree : ℕ → FreeGroup (FreeGenerator.{u} t) :=
    fun q =>
      HallTree.leafOccurrenceZ
        FreeGroup.of (exponent q) tree leaf
  let correctionFree : ℕ → FreeGroup (FreeGenerator.{u} t) :=
    fun q => (baseFree ^ exponent q)⁻¹ * poweredFree q
  let truncationMap :
      FreeGroup (FreeGenerator.{u} t) →*
        LowerCentralTruncation
          (FreeGroup (FreeGenerator.{u} t)) n :=
    lowerCentralTruncation
      (FreeGroup (FreeGenerator.{u} t)) n
  have hbaseMap :
      truncationMap baseFree =
        tree.toCWord.eval
          (freeTruncationValue t n) := by
    simpa [truncationMap, baseFree,
      freeTruncationValue] using
        (CWord.map_eval
          (lowerCentralTruncation
            (FreeGroup (FreeGenerator.{u} t)) n)
          FreeGroup.of tree.toCWord)
  have hpoweredMap (q : ℕ) :
      truncationMap (poweredFree q) =
        HallTree.leafOccurrenceZ
          (freeTruncationValue t n)
          (exponent q) tree leaf := by
    change
      lowerCentralTruncation
          (FreeGroup (FreeGenerator.{u} t)) n
          (HallTree.leafOccurrenceZ
            FreeGroup.of (exponent q) tree leaf) =
        HallTree.leafOccurrenceZ
          (freeTruncationValue t n)
          (exponent q) tree leaf
    rw [HallTree.leaf_z_pow]
    rfl
  have hcorrectionMap :
      ∀ q,
        truncationMap (correctionFree q) =
          (tree.toCWord.eval
              (freeTruncationValue t n) ^
                exponent q)⁻¹ *
            HallTree.leafOccurrenceZ
              (freeTruncationValue t n)
              (exponent q) tree leaf := by
    intro q
    change
      truncationMap ((baseFree ^ exponent q)⁻¹ * poweredFree q) = _
    rw [map_mul, map_inv, map_zpow, hbaseMap, hpoweredMap]
  have hcorrectionMem :
      ∀ q,
        correctionFree q ∈
          Subgroup.lowerCentralSeries
            (FreeGroup (FreeGenerator.{u} t)) tree.weight := by
    intro q
    have hscaled :
        poweredFree q * (baseFree ^ exponent q)⁻¹ ∈
          Subgroup.lowerCentralSeries
            (FreeGroup (FreeGenerator.{u} t)) tree.weight := by
      simpa [poweredFree, baseFree] using
        HallTree.leaf_occurrence_z
          FreeGroup.of tree leaf (exponent q)
    have hconjugate :=
      (inferInstance :
        (Subgroup.lowerCentralSeries
          (FreeGroup (FreeGenerator.{u} t))
          tree.weight).Normal).conj_mem
        (poweredFree q * (baseFree ^ exponent q)⁻¹) hscaled
        (baseFree ^ exponent q)⁻¹
    change
      (baseFree ^ exponent q)⁻¹ * poweredFree q ∈
        Subgroup.lowerCentralSeries
          (FreeGroup (FreeGenerator.{u} t)) tree.weight
    rw [show
      (baseFree ^ exponent q)⁻¹ * poweredFree q =
        (baseFree ^ exponent q)⁻¹ *
          (poweredFree q * (baseFree ^ exponent q)⁻¹) *
            baseFree ^ exponent q by group]
    simpa only [inv_inv] using hconjugate
  have hbaseMagnus :
      VanishesBelow
        (magnusDifference (R := ℤ) baseFree) tree.weight := by
    simpa [baseFree] using
      MPOrd.tree_vanishes_below tree
  have htreeWeight : 1 ≤ tree.weight := tree.weight_pos
  have hexponent' :
      IVMost exponent
        (tree.weight - (tree.weight - 1)) := by
    simpa [show tree.weight - (tree.weight - 1) = 1 by
      omega] using hexponent
  have hbasePowerOrder :
      MPOrd
        (fun q =>
          magnusDifference (R := ℤ)
            (baseFree ^ exponent q))
        (tree.weight - 1) := by
    exact
      MPOrd.fixedZPow
        baseFree hbaseMagnus
        (Nat.sub_le tree.weight 1) hexponent'
  have hpoweredOrder :
      MPOrd
        (fun q =>
          magnusDifference (R := ℤ) (poweredFree q))
        (tree.weight - 1) := by
    simpa [poweredFree] using
      MPOrd.leafOccurrenceZ
        tree leaf hexponent
  have hcorrectionOrder :
      MPOrd
        (fun q =>
          magnusDifference (R := ℤ) (correctionFree q))
        (tree.weight - 1) := by
    simpa [correctionFree] using
      hbasePowerOrder.magnusDifference_inv.magnusDifference_mul
        hpoweredOrder
  have hfamily :
      (fun q =>
        signedCorrectionCoordinates
          t n hn tree leaf (exponent q) s j) =
        fun q =>
          standardHallCoordinates t n hn
            (truncationMap (correctionFree q)) s j := by
    funext q
    simp [signedCorrectionCoordinates, hcorrectionMap q]
  rw [hfamily]
  exact
    standard_coordinates_magnus
      t n tree.weight (tree.weight - 1) hn
      (Nat.sub_le tree.weight 1)
      correctionFree hcorrectionMem hcorrectionOrder
      s hs hsn j

/-- Every canonical signed correction coordinate in Lemma H2 is given by
one integer-valued polynomial on all integer exponents, with the same sharp
degree bound as on natural exponents. -/
theorem signed_coordinate_polynomial
    (t n : ℕ)
    (hn : 2 ≤ n)
    (tree : HallTree (FreeGenerator.{u} t))
    (leaf : HallTree.LOccur tree)
    (s : ℕ)
    (hs : 1 ≤ s)
    (hsn : s < n)
    (j : (standardHallFamily.{u} t s).index) :
    ValuedIntegersMost
      (fun z =>
        signedCorrectionCoordinates
          t n hn tree leaf z s j)
      (s - (tree.weight - 1)) := by
  let naturalExponent : ℕ → ℤ := fun q => q
  have hnaturalExponent :
      IVMost naturalExponent 1 := by
    refine ⟨Polynomial.X, by simp, ?_⟩
    intro q
    simp [naturalExponent]
  obtain ⟨P, hPdegree, hPeval⟩ :=
    signed_correction_comp
      t n hn tree leaf naturalExponent hnaturalExponent
      s hs hsn j
  refine ⟨P, hPdegree, ?_⟩
  intro z
  cases z with
  | ofNat q =>
      simpa [naturalExponent] using hPeval q
  | negSucc k =>
      let K := k + 1
      let shiftedExponent : ℕ → ℤ :=
        fun q => (q : ℤ) - K
      have hshiftedExponent :
          IVMost shiftedExponent 1 := by
        refine ⟨Polynomial.X - Polynomial.C (K : ℚ),
          Polynomial.natDegree_X_sub_C_le (K : ℚ), ?_⟩
        intro q
        simp [shiftedExponent]
      obtain ⟨Q, hQdegree, hQeval⟩ :=
        signed_correction_comp
          t n hn tree leaf shiftedExponent hshiftedExponent
          s hs hsn j
      let shift : Polynomial ℚ :=
        Polynomial.X - Polynomial.C (K : ℚ)
      have hQP : Q = P.comp shift := by
        apply Polynomial.eq_of_infinite_eval_eq
        apply Set.infinite_of_injective_forall_mem
          (f := fun r : ℕ => ((r + K : ℕ) : ℚ))
        · intro r r' hrr
          have hrr' : r + K = r' + K := by
            exact Nat.cast_injective hrr
          exact Nat.add_right_cancel hrr'
        · intro r
          change
            Q.eval ((r + K : ℕ) : ℚ) =
              (P.comp shift).eval ((r + K : ℕ) : ℚ)
          rw [hQeval (r + K), Polynomial.eval_comp]
          have hshiftEval :
              shift.eval ((r + K : ℕ) : ℚ) = (r : ℚ) := by
            simp [shift, K]
          rw [hshiftEval, hPeval r]
          simp [shiftedExponent, naturalExponent, K]
      calc
        P.eval ((Int.negSucc k : ℤ) : ℚ) =
            (P.comp shift).eval 0 := by
              simp [shift, K]
        _ = Q.eval 0 := by rw [← hQP]
        _ =
            (signedCorrectionCoordinates
              t n hn tree leaf (shiftedExponent 0) s j : ℚ) :=
          hQeval 0
        _ =
            (signedCorrectionCoordinates
              t n hn tree leaf (Int.negSucc k) s j : ℚ) := by
          rw [show shiftedExponent 0 = Int.negSucc k by
            simp [shiftedExponent, K, Int.negSucc_eq]]

/-- The signed form of Struik's Lemma H2 with one canonical correction
family for every integer exponent.  Its coordinates are strictly higher
weight, contain every source label, and are represented by one polynomial
on all integers. -/
theorem signed_standard_coordinates
    (t n : ℕ)
    (hn : 2 ≤ n)
    (tree : HallTree (FreeGenerator.{u} t))
    (leaf : HallTree.LOccur tree) :
    let correction :=
      signedCorrectionCoordinates t n hn tree leaf
    (∀ z : ℤ,
      HallTree.leafOccurrenceZ
          (freeTruncationValue t n) z tree leaf =
        (tree.toCWord.eval
            (freeTruncationValue t n)) ^ z *
          standardHallProduct t n (correction z)) ∧
      (∀ z : ℤ,
        ∀ s : ℕ,
          1 ≤ s →
            s < tree.weight + 1 →
              s < n →
                correction z s = 0) ∧
        (∀ z : ℤ,
          ∀ a : FreeGenerator.{u} t,
            hallTreeUses a tree →
              ∀ (s : ℕ),
                1 ≤ s →
                  s < n →
                    ∀ j : (standardHallFamily.{u} t s).index,
                      ¬hallTreeUses a (concreteBasicTree j) →
                        correction z s j = 0) ∧
          ∀ s : ℕ,
            1 ≤ s →
              s < n →
                ∀ j : (standardHallFamily.{u} t s).index,
                  ValuedIntegersMost
                    (fun z => correction z s j)
                    (s - (tree.weight - 1)) := by
  dsimp only
  let base :=
    tree.toCWord.eval
      (freeTruncationValue t n)
  let powered : ℤ →
      LowerCentralTruncation
        (FreeGroup (FreeGenerator.{u} t)) n :=
    fun z =>
      HallTree.leafOccurrenceZ
        (freeTruncationValue t n) z tree leaf
  let correctionElement : ℤ →
      LowerCentralTruncation
        (FreeGroup (FreeGenerator.{u} t)) n :=
    fun z => (base ^ z)⁻¹ * powered z
  have hcorrectionProduct :
      ∀ z,
        standardHallProduct t n
            (signedCorrectionCoordinates
              t n hn tree leaf z) =
          correctionElement z := by
    intro z
    exact
      standard_product_coordinates
        t n hn (correctionElement z)
  have hcorrectionMem :
      ∀ z,
        correctionElement z ∈
          Subgroup.lowerCentralSeries
            (LowerCentralTruncation
              (FreeGroup (FreeGenerator.{u} t)) n)
            tree.weight := by
    intro z
    have hscaled :
        powered z * (base ^ z)⁻¹ ∈
          Subgroup.lowerCentralSeries
            (LowerCentralTruncation
              (FreeGroup (FreeGenerator.{u} t)) n)
            tree.weight := by
      simpa [powered, base] using
        HallTree.leaf_occurrence_z
          (freeTruncationValue t n)
          tree leaf z
    have hconjugate :=
      (inferInstance :
        (Subgroup.lowerCentralSeries
          (LowerCentralTruncation
            (FreeGroup (FreeGenerator.{u} t)) n)
          tree.weight).Normal).conj_mem
        (powered z * (base ^ z)⁻¹) hscaled
        (base ^ z)⁻¹
    change
      (base ^ z)⁻¹ * powered z ∈
        Subgroup.lowerCentralSeries
          (LowerCentralTruncation
            (FreeGroup (FreeGenerator.{u} t)) n)
          tree.weight
    rw [show
      (base ^ z)⁻¹ * powered z =
        (base ^ z)⁻¹ * (powered z * (base ^ z)⁻¹) *
          base ^ z by group]
    simpa only [inv_inv] using hconjugate
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro z
    rw [hcorrectionProduct z]
    change powered z = base ^ z * correctionElement z
    simp [correctionElement]
  · intro z s hs hsTree hsn
    exact
      standard_coordinates_series
        t n (tree.weight + 1) hn (correctionElement z)
        (by simpa using hcorrectionMem z)
        s hs hsTree hsn
  · intro z a huses s hs hsn j hnotUses
    have hmap :
        eraseTruncationGenerator t n a
            (correctionElement z) =
          1 := by
      rw [show
        correctionElement z =
          (base ^ z)⁻¹ * powered z by rfl]
      rw [map_mul, map_inv, map_zpow]
      change
        (eraseTruncationGenerator t n a
            (tree.toCWord.eval
              (freeTruncationValue t n)) ^ z)⁻¹ *
            eraseTruncationGenerator t n a
              (HallTree.leafOccurrenceZ
                (freeTruncationValue t n)
                z tree leaf) =
          1
      rw [
        erase_truncation_uses
          t n a tree huses,
        erase_powered_uses
          t n a tree leaf z huses]
      simp
    exact
      standard_erase_uses
        t n hn a (correctionElement z) hmap
        s hs hsn j hnotUses
  · intro s hs hsn j
    exact
      signed_coordinate_polynomial
        t n hn tree leaf s hs hsn j

/-- The signed form of Struik's Lemma H2.  One selected leaf may be raised
to an arbitrary integer power.  The correction is a standard Hall product
of strictly higher weight, and every nonzero correction factor uses every
label occurring in the original commutator tree. -/
theorem signed_standard_recollection
    (t n : ℕ)
    (hn : 2 ≤ n)
    (tree : HallTree (FreeGenerator.{u} t))
    (leaf : HallTree.LOccur tree)
    (m : ℤ) :
    let y :=
      HallTree.leafOccurrenceZ
        (freeTruncationValue t n) m tree leaf
    let base :=
      tree.toCWord.eval
        (freeTruncationValue t n)
    ∃ e : StandardExponentFamily.{u} t,
      (∀ s : ℕ,
        1 ≤ s →
          s < tree.weight + 1 →
            s < n →
              e s = 0) ∧
        (∀ a : FreeGenerator.{u} t,
          hallTreeUses a tree →
            ∀ (s : ℕ),
              1 ≤ s →
                s < n →
                  ∀ j : (standardHallFamily.{u} t s).index,
                    ¬hallTreeUses a (concreteBasicTree j) →
                      e s j = 0) ∧
        y = base ^ m * standardHallProduct t n e := by
  let y :=
    HallTree.leafOccurrenceZ
      (freeTruncationValue t n) m tree leaf
  let base :=
    tree.toCWord.eval
      (freeTruncationValue t n)
  let correction := (base ^ m)⁻¹ * y
  have hscaled :
      y * (base ^ m)⁻¹ ∈
        Subgroup.lowerCentralSeries
          (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} t)) n)
          tree.weight := by
    exact
      HallTree.leaf_occurrence_z
        (freeTruncationValue t n) tree leaf m
  have hcorrection :
      correction ∈
        Subgroup.lowerCentralSeries
          (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} t)) n)
          tree.weight := by
    have hconjugate :=
      (inferInstance :
        (Subgroup.lowerCentralSeries
          (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} t)) n)
          tree.weight).Normal).conj_mem
        (y * (base ^ m)⁻¹) hscaled (base ^ m)⁻¹
    change (base ^ m)⁻¹ * y ∈
      Subgroup.lowerCentralSeries
        (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} t)) n)
        tree.weight
    rw [show
      (base ^ m)⁻¹ * y =
        (base ^ m)⁻¹ * (y * (base ^ m)⁻¹) * base ^ m by group]
    simpa only [inv_inv] using hconjugate
  let e := standardHallCoordinates t n hn correction
  have heProduct : standardHallProduct t n e = correction :=
    standard_product_coordinates t n hn correction
  have heZero :
      ∀ s : ℕ,
        1 ≤ s →
          s < tree.weight + 1 →
            s < n →
              e s = 0 :=
    standard_coordinates_series
      t n (tree.weight + 1) hn correction
        (by simpa using hcorrection)
  have heSupport :
      ∀ a : FreeGenerator.{u} t,
        hallTreeUses a tree →
          ∀ (s : ℕ),
            1 ≤ s →
              s < n →
                ∀ j : (standardHallFamily.{u} t s).index,
                  ¬hallTreeUses a (concreteBasicTree j) →
                    e s j = 0 := by
    intro a huses s hs hsn j hnotUses
    have hmap :
        eraseTruncationGenerator t n a correction = 1 := by
      rw [map_mul, map_inv, map_zpow]
      change
        (eraseTruncationGenerator t n a
            (tree.toCWord.eval
              (freeTruncationValue t n)) ^ m)⁻¹ *
            eraseTruncationGenerator t n a
              (HallTree.leafOccurrenceZ
                (freeTruncationValue t n) m tree leaf) =
          1
      rw [
        erase_truncation_uses
          t n a tree huses,
        erase_powered_uses
          t n a tree leaf m huses]
      simp
    exact
      standard_erase_uses
        t n hn a correction hmap s hs hsn j hnotUses
  refine ⟨e, heZero, heSupport, ?_⟩
  rw [heProduct]
  change y = base ^ m * correction
  simp [correction]

/-- Evaluate the free nilpotent truncation in any group satisfying the same
lower-central cutoff. -/
noncomputable def freeTruncationLift
    {t n : ℕ}
    {G : Type*} [Group G]
    (value : FreeGenerator.{u} t → G)
    (hG : Subgroup.lowerCentralSeries G (n - 1) = ⊥) :
    LowerCentralTruncation
        (FreeGroup (FreeGenerator.{u} t)) n →*
      G := by
  let f : FreeGroup (FreeGenerator.{u} t) →* G :=
    FreeGroup.lift value
  apply QuotientGroup.lift
    (Subgroup.lowerCentralSeries
      (FreeGroup (FreeGenerator.{u} t)) (n - 1)) f
  intro x hx
  apply MonoidHom.mem_ker.mpr
  have hxmap :
      f x ∈ Subgroup.lowerCentralSeries G (n - 1) :=
    Subgroup.lowerCentralSeries.map f (n - 1)
      (Subgroup.mem_map_of_mem f hx)
  rw [hG] at hxmap
  exact hxmap

@[simp] theorem truncation_lift_generator
    {t n : ℕ}
    {G : Type*} [Group G]
    (value : FreeGenerator.{u} t → G)
    (hG : Subgroup.lowerCentralSeries G (n - 1) = ⊥)
    (a : FreeGenerator.{u} t) :
    freeTruncationLift value hG
        (freeTruncationValue t n a) =
      value a := by
  simp [freeTruncationLift,
    freeTruncationValue]

/-- Struik's natural-power Lemma H2 in an arbitrary group with `G_n = 1`,
including the polynomial degree and all-input support properties of the
universal correction coordinates. -/
theorem standard_coordinates_bot
    {G : Type*} [Group G]
    (t n : ℕ)
    (hn : 2 ≤ n)
    (value : FreeGenerator.{u} t → G)
    (hG : Subgroup.lowerCentralSeries G (n - 1) = ⊥)
    (tree : HallTree (FreeGenerator.{u} t))
    (leaf : HallTree.LOccur tree) :
    ∃ correction : ℕ → StandardExponentFamily.{u} t,
      (∀ q : ℕ,
        HallTree.leafOccurrencePow value q tree leaf =
          (tree.toCWord.eval value) ^ q *
            freeTruncationLift value hG
              (standardHallProduct t n (correction q))) ∧
        (∀ q s : ℕ,
          1 ≤ s →
            s < tree.weight + 1 →
              s < n →
                correction q s = 0) ∧
          (∀ q : ℕ,
            ∀ a : FreeGenerator.{u} t,
              hallTreeUses a tree →
                ∀ (s : ℕ),
                  1 ≤ s →
                    s < n →
                      ∀ j : (standardHallFamily.{u} t s).index,
                        ¬hallTreeUses a (concreteBasicTree j) →
                          correction q s j = 0) ∧
            ∀ s : ℕ,
              1 ≤ s →
                s < n →
                  ∀ j : (standardHallFamily.{u} t s).index,
                    IVMost
                      (fun q : ℕ => correction q s j)
                      (s - (tree.weight - 1)) := by
  obtain ⟨correction, hEquality, hZero, hSupport, hPolynomial⟩ :=
    standardCorrectionCoordinates t n hn tree leaf
  refine ⟨correction, ?_, hZero, hSupport, hPolynomial⟩
  intro q
  have hmapped :=
    congrArg (freeTruncationLift value hG)
      (hEquality q)
  simpa only [map_mul, map_pow,
    HallTree.eval_leaf_pow,
    CWord.map_eval,
    truncation_lift_generator] using hmapped

/-- Struik's signed Lemma H2 in an arbitrary group with `G_n = 1`.
The correction is the image of a standard Hall product from the universal
free truncation.  Its universal factors have strictly higher weight and each
uses every label occurring in the original commutator tree. -/
theorem signed_series_bot
    {G : Type*} [Group G]
    (t n : ℕ)
    (hn : 2 ≤ n)
    (value : FreeGenerator.{u} t → G)
    (hG : Subgroup.lowerCentralSeries G (n - 1) = ⊥)
    (tree : HallTree (FreeGenerator.{u} t))
    (leaf : HallTree.LOccur tree)
    (m : ℤ) :
    ∃ e : StandardExponentFamily.{u} t,
      (∀ s : ℕ,
        1 ≤ s →
          s < tree.weight + 1 →
            s < n →
              e s = 0) ∧
        (∀ a : FreeGenerator.{u} t,
          hallTreeUses a tree →
            ∀ (s : ℕ),
              1 ≤ s →
                s < n →
                  ∀ j : (standardHallFamily.{u} t s).index,
                    ¬hallTreeUses a (concreteBasicTree j) →
                      e s j = 0) ∧
        HallTree.leafOccurrenceZ value m tree leaf =
          (tree.toCWord.eval value) ^ m *
            freeTruncationLift value hG
              (standardHallProduct t n e) := by
  obtain ⟨e, heZero, heSupport, heEquality⟩ :=
    signed_standard_recollection t n hn tree leaf m
  refine ⟨e, heZero, heSupport, ?_⟩
  have hmapped :=
    congrArg (freeTruncationLift value hG) heEquality
  simpa only [map_mul, map_zpow,
    HallTree.leaf_z_pow,
    CWord.map_eval,
    truncation_lift_generator] using hmapped

/-- Struik's Lemma 1 Hall-factor order bound for every tame truncation
cutoff. -/
theorem bound_tame_orders
    {t n : ℕ}
    (order : Fin t → ℕ)
    (hn : 2 ≤ n)
    (htame : TameOrdersCutoff order n) :
    FactorOrderBound.{u} order n :=
  powered_leaf_polynomial
    order hn htame
      (powered_data_general t n hn)

end

end P1960
end Struik
