import Towers.Group.NilpotentProducts.MagnusUniqueness
import Towers.Group.NilpotentProducts.OrderNine


/-!
# The finite-order case of the corollary to Struik's Theorem 3

This file proves Case II of the unnumbered corollary following Theorem 3
when all cyclic factors are finite and their orders divide the displayed
common multiple `N`.

The proof follows the paper's Magnus-coefficient argument.  For each target
Hall tree, the recursive Hall modulus divides `N`.  The target word
representations therefore kill the `N`th power.  Induction over Hall weight
then shows that every coordinate of that power is divisible by its modulus.
-/

namespace Struik
namespace P1960

open EChapma
open EChapma.MSeries
open Towers
open Towers.Edmonton
open Towers.HallTree
open Towers.TBluepr
open Towers.TCTex

universe u


theorem tree_common_multiple
    {α : Type*} (order : α → ℕ) (N : ℕ)
    (hN : ∀ a, order a ∣ N) :
    ∀ tree : HallTree α, hallTreeOrder order tree ∣ N
  | .atom a => hN a
  | .commutator left right =>
      (Nat.gcd_dvd_left
        (hallTreeOrder order left)
        (hallTreeOrder order right)).trans
          (tree_common_multiple order N hN left)

/-- Every Hall coordinate of an `N`th power is divisible by its recursive
Hall modulus when each target tree either has modulus dividing `N` or sees a
trivial retained part of the powered word. -/
theorem general_standard_target
    {t n N : ℕ}
    (order : Fin t → ℕ)
    (htame : TameOrdersCutoff order n)
    (g : FreeGroup (FreeGenerator.{u} t))
    (hN :
      ∀ target : HallTree (FreeGenerator.{u} t),
        hallTreeOrder
            (fun a : FreeGenerator.{u} t => order a.down)
            target ∣
          N ∨
        keepTreeHom target g = 1)
    (e : StandardExponentFamily.{u} t)
    (he :
      standardHallProduct t n e =
        lowerCentralTruncation
          (FreeGroup (FreeGenerator.{u} t)) n (g ^ N)) :
    ∀ s, 1 ≤ s → s < n →
      ∀ i : (standardHallFamily.{u} t s).index,
        (generalStandardOrder order i : ℤ) ∣
          e s i := by
  intro s
  induction s using Nat.strong_induction_on with
  | h s ih =>
      intro hs hsn i
      classical
      let y : FreeGroup (FreeGenerator.{u} t) :=
        freeStandardPrefix t e (n - 1)
      have heY :
          standardHallProduct t n e =
            lowerCentralTruncation
              (FreeGroup (FreeGenerator.{u} t)) n y := by
        calc
          standardHallProduct t n e =
              collectedPrefixProduct
                (n := n) (standardHallFamily.{u} t) e (n - 1) :=
            rfl
          _ =
              lowerCentralTruncation
                (FreeGroup (FreeGenerator.{u} t)) n
                (freeStandardPrefix t e (n - 1)) :=
            (truncation_standard_prefix
              t n (n - 1) e).symm
          _ =
              lowerCentralTruncation
                (FreeGroup (FreeGenerator.{u} t)) n y :=
            rfl
      have hyPower :
          lowerCentralTruncation
              (FreeGroup (FreeGenerator.{u} t)) n y =
            lowerCentralTruncation
              (FreeGroup (FreeGenerator.{u} t)) n (g ^ N) :=
        heY.symm.trans he
      let target : HallTree (FreeGenerator.{u} t) :=
        concreteBasicTree i
      let keptE : StandardExponentFamily.{u} t :=
        keepTreeFamily target e
      let keptY : FreeGroup (FreeGenerator.{u} t) :=
        keepTreeHom target y
      have heKeep :
          standardHallProduct t n keptE =
            lowerCentralTruncation
              (FreeGroup (FreeGenerator.{u} t)) n keptY := by
        have hkeptY :
            keptY =
              freeStandardPrefix t keptE (n - 1) := by
          dsimp [keptY, keptE, y]
          exact
            keep_tree_prefix
              t target e (n - 1)
        calc
          standardHallProduct t n keptE =
              collectedPrefixProduct
                (n := n) (standardHallFamily.{u} t)
                keptE (n - 1) :=
            rfl
          _ =
              lowerCentralTruncation
                (FreeGroup (FreeGenerator.{u} t)) n
                (freeStandardPrefix
                  t keptE (n - 1)) :=
            (truncation_standard_prefix
              t n (n - 1) keptE).symm
          _ =
              lowerCentralTruncation
                (FreeGroup (FreeGenerator.{u} t)) n keptY := by
            rw [hkeptY]
      let residual : FreeGroup (FreeGenerator.{u} t) :=
        (freeStandardPrefix t keptE (s - 1))⁻¹ *
          keptY
      have hresidualMem :
          residual ∈
            Subgroup.lowerCentralSeries
              (FreeGroup (FreeGenerator.{u} t)) (s - 1) := by
        exact
          free_standard_series
            t n (s - 1) (by omega) keptE keptY heKeep
      have hresidualRepresentations :
          ∀ xs : List (FreeGenerator.{u} t),
            xs.length = s →
            wordCoefficientRepresentation
                (R := ZMod
                  (generalStandardOrder order i))
                xs residual =
              1 := by
        intro xs hxsLength
        have hxs : xs.length ≤ n - 1 := by
          rw [hxsLength]
          omega
        have hfull :
            wordCoefficientRepresentation
                (R := ZMod
                  (generalStandardOrder order i))
                xs keptY =
              1 := by
          have hpower :
              wordCoefficientRepresentation
                  (R := ZMod
                    (generalStandardOrder order i))
                xs
                  (keepTreeHom target (g ^ N)) =
                1 := by
            rcases hN target with htargetDvdN | htargetTrivial
            · have hpowerRaw :=
                coefficient_representation_dvd
                  (tree_tame_cutoff
                    order htame target)
                  xs hxs
                  (keepTreeHom target g)
                  (m := (N : ℤ))
                  (by exact_mod_cast htargetDvdN)
              rw [map_pow, map_pow]
              simpa [target, zpow_natCast,
                generalStandardOrder] using hpowerRaw
            · rw [map_pow, htargetTrivial, one_pow]
              simp
          have himage :
              inverseFreeTruncation order n
                    (lowerCentralTruncation
                      (FreeGroup (FreeGenerator.{u} t)) n y) =
                inverseFreeTruncation order n
                    (lowerCentralTruncation
                      (FreeGroup (FreeGenerator.{u} t)) n (g ^ N)) :=
            congrArg (inverseFreeTruncation order n) hyPower
          have hdetector :=
            congrArg
              (treeCyclicRepresentation
                order htame target xs hxs) himage
          have hcompatPower :=
            tree_representation_truncation
              order htame target xs hxs (g ^ N)
          change
            treeCyclicRepresentation
                order htame target xs hxs
                  (inverseFreeTruncation order n
                    (lowerCentralTruncation
                      (FreeGroup (FreeGenerator.{u} t)) n (g ^ N))) =
              wordCoefficientRepresentation
                (R := ZMod
                  (generalStandardOrder order i))
                xs
                (keepTreeHom target (g ^ N))
            at hcompatPower
          have hcompatY :
              wordCoefficientRepresentation
                    (R := ZMod
                      (generalStandardOrder order i))
                    xs keptY =
                  treeCyclicRepresentation
                    order htame target xs hxs
                      (inverseFreeTruncation order n
                        (lowerCentralTruncation
                          (FreeGroup (FreeGenerator.{u} t)) n y)) := by
            simpa only [keptY, target,
              generalStandardOrder] using
              (tree_representation_truncation
                order htame target xs hxs y).symm
          exact
            hcompatY.trans
              (hdetector.trans (hcompatPower.trans hpower))
        have hprefix :
            wordCoefficientRepresentation
                (R := ZMod
                  (generalStandardOrder order i))
                xs
                (freeStandardPrefix
                  t keptE (s - 1)) =
              1 := by
          rw [← keep_tree_prefix
            t target e (s - 1)]
          apply
            representation_keep_tree
              order htame target xs hxs e (s - 1)
          intro r hr hrs j
          exact ih r (by omega) hr (by omega) j
        simp [residual, map_mul, map_inv, hprefix, hfull]
      have hpdiv :
          ∀ w :
              AssociativeWordsLength
                (FreeGenerator.{u} t) s,
            (generalStandardOrder order i : ℤ) ∣
              (homogeneousPart s
                (magnusDifference (R := ℤ) residual)).1 w.1 := by
        intro w
        rw [homogeneousPart_apply]
        exact
          magnus_difference_representations
            residual hresidualRepresentations w
      obtain ⟨q, hscalar⟩ :=
        homogeneous_smul_dvd
          (X := FreeGenerator.{u} t) hpdiv
      let L :
          AssociativeHomogeneousWords
            ℤ (FreeGenerator.{u} t) s →ₗ[ℤ] ℤ :=
        HMCoord.linearMap i.down
      have hcoordinate :
          L (homogeneousPart s
              (magnusDifference (R := ℤ) residual)) =
            e s i := by
        calc
          L (homogeneousPart s
              (magnusDifference (R := ℤ) residual)) =
              (HallTree.freePBWUniqueness
                  (IMagnus.hallPBWInput
                    (X := FreeGenerator.{u} t)) hs).repr
                (lowerCentralWeight hresidualMem) i.down := by
                  exact
                    HMCoord.linear_lower_class
                      hs hresidualMem i.down
          _ = keptE s i :=
            free_standard_coordinate
              t n s hs hsn keptE keptY heKeep hresidualMem i
          _ = e s i := by
            simp [keptE, keepTreeFamily, target,
              tree_label_refl]
      refine ⟨L q, ?_⟩
      rw [← hcoordinate, hscalar, map_smul]
      simp

/-- Every Hall coordinate of an `N`th power is divisible by its recursive
Hall modulus when all generator orders divide `N`. -/
theorem general_standard_exponent
    {t n N : ℕ}
    (order : Fin t → ℕ)
    (htame : TameOrdersCutoff order n)
    (hN : ∀ i, order i ∣ N)
    (g : FreeGroup (FreeGenerator.{u} t))
    (e : StandardExponentFamily.{u} t)
    (he :
      standardHallProduct t n e =
        lowerCentralTruncation
          (FreeGroup (FreeGenerator.{u} t)) n (g ^ N)) :
    ∀ s, 1 ≤ s → s < n →
      ∀ i : (standardHallFamily.{u} t s).index,
        (generalStandardOrder order i : ℤ) ∣
          e s i :=
  general_standard_target
    order htame g
      (fun target =>
        Or.inl
          (tree_common_multiple
            (fun a : FreeGenerator.{u} t => order a.down) N
            (fun a => hN a.down) target))
    e he

/-- For a collected free Hall word, every target tree either has recursive
order dividing the displayed common multiple or retains no displayed factor
and hence sees the identity. -/
theorem or_keep_displayed
    {t n N : ℕ}
    (order : Fin t → ℕ)
    (e : StandardExponentFamily.{u} t)
    (hN :
      ∀ s, 1 ≤ s → s < n →
        ∀ i : (standardHallFamily.{u} t s).index,
          e s i ≠ 0 →
            generalStandardOrder order i ∣ N)
    (target : HallTree (FreeGenerator.{u} t)) :
    hallTreeOrder
          (fun a : FreeGenerator.{u} t => order a.down)
          target ∣
        N ∨
      keepTreeHom target
          (freeStandardPrefix t e (n - 1)) =
        1 := by
  classical
  by_cases hexists :
      ∃ s, 1 ≤ s ∧ s < n ∧
        ∃ i : (standardHallFamily.{u} t s).index,
          treeLabelSupport target (concreteBasicTree i) ∧
            e s i ≠ 0
  · left
    obtain ⟨s, hs, hsn, i, hsupport, hne⟩ := hexists
    exact
      (tree_label_support
        (fun a : FreeGenerator.{u} t => order a.down)
        hsupport).trans
          (by
            simpa [generalStandardOrder] using
              hN s hs hsn i hne)
  · right
    rw [keep_tree_prefix]
    unfold freeStandardPrefix
    apply List.prod_eq_one
    intro z hz
    rcases List.mem_map.mp hz with ⟨j, hj, rfl⟩
    have hjlt : j < n - 1 := List.mem_range.mp hj
    have hzero :
        keepTreeFamily target e (j + 1) = 0 := by
      funext i
      by_cases hsupport :
          treeLabelSupport target (concreteBasicTree i)
      · have hei : e (j + 1) i = 0 := by
          by_contra hne
          exact hexists
            ⟨j + 1, by omega, by omega, i, hsupport, hne⟩
        simp [keepTreeFamily, hsupport, hei]
      · simp [keepTreeFamily, hsupport]
    rw [hzero, free_standard_zero]

/-- A collected Hall product maps to the identity once every coordinate is
divisible by the recursive order of its factor. -/
theorem truncation_standard_dvd
    {t n : ℕ}
    (order : Fin t → ℕ)
    (hn : 2 ≤ n)
    (hbound : FactorOrderBound.{u} order n)
    (e : StandardExponentFamily.{u} t)
    (hdiv :
      ∀ s, 1 ≤ s → s < n →
        ∀ i : (standardHallFamily.{u} t s).index,
          (generalStandardOrder order i : ℤ) ∣
            e s i) :
    inverseFreeTruncation order n
        (standardHallProduct t n e) =
      1 := by
  have hresidues :
      generalResiduesFamily order n e = 0 := by
    funext r i
    change
      ((e (r + 1) i : ℤ) :
          ZMod (generalStandardOrder order i)) =
        0
    exact
      (ZMod.intCast_zmod_eq_zero_iff_dvd
        (e (r + 1) i)
        (generalStandardOrder order i)).2
          (hdiv (r + 1) (by omega) (by omega) i)
  have hzeroEval :
      generalResidueEval.{u} order n 0 = 1 := by
    have hzeroResidues :
        generalResiduesFamily order n
            (0 : StandardExponentFamily.{u} t) =
          0 := by
      funext r i
      simp [generalResiduesFamily]
    calc
      generalResidueEval.{u} order n 0 =
          generalResidueEval.{u} order n
            (generalResiduesFamily order n
              (0 : StandardExponentFamily.{u} t)) := by
        rw [hzeroResidues]
      _ =
          inverseFreeTruncation.{u} order n
            (standardHallProduct t n
              (0 : StandardExponentFamily.{u} t)) :=
        general_exponent_family
          order hbound 0
      _ = 1 := by
        rw [show
          standardHallProduct t n
              (0 : StandardExponentFamily.{u} t) =
            1 by
              apply
                collected_prefix_coordinates
                  (standardHallFamily.{u} t) 0 (n - 1)
              intro r _hr _hrn
              rfl]
        simp
  rw [← general_exponent_family
    order hbound e, hresidues]
  exact hzeroEval

/-- **Corollary to Theorem 3, Case II, in Struik's displayed-factor form.**
Any common multiple of the recursive orders of the factors occurring with
nonzero exponent in one collected normal form kills that element. -/
theorem corollary_standard_displayed
    {t n N : ℕ}
    (order : Fin t → ℕ)
    (hn : 2 ≤ n)
    (htame : TameOrdersCutoff order n)
    (e : StandardExponentFamily.{u} t)
    (hN :
      ∀ s, 1 ≤ s → s < n →
        ∀ i : (standardHallFamily.{u} t s).index,
          e s i ≠ 0 →
            generalStandardOrder order i ∣ N) :
    (inverseFreeTruncation order n
        (standardHallProduct t n e)) ^ N =
      1 := by
  let g : FreeGroup (FreeGenerator.{u} t) :=
    freeStandardPrefix t e (n - 1)
  have hg :
      lowerCentralTruncation
          (FreeGroup (FreeGenerator.{u} t)) n g =
        standardHallProduct t n e := by
    exact
      truncation_standard_prefix
        t n (n - 1) e
  let z :=
    lowerCentralTruncation
      (FreeGroup (FreeGenerator.{u} t)) n (g ^ N)
  let f : StandardExponentFamily.{u} t :=
    standardHallCoordinates t n hn z
  have hf : standardHallProduct t n f = z :=
    standard_product_coordinates t n hn z
  have hfDiv :
      ∀ s, 1 ≤ s → s < n →
        ∀ i : (standardHallFamily.{u} t s).index,
          (generalStandardOrder order i : ℤ) ∣
            f s i := by
    exact
      general_standard_target
        order htame g
          (or_keep_displayed
            order e hN)
        f hf
  calc
    (inverseFreeTruncation order n
        (standardHallProduct t n e)) ^ N =
        inverseFreeTruncation order n
          ((standardHallProduct t n e) ^ N) := by
            rw [map_pow]
    _ = inverseFreeTruncation order n z := by
      simp [z, ← hg, map_pow]
    _ = inverseFreeTruncation order n
          (standardHallProduct t n f) := by
            rw [hf]
    _ = 1 :=
      truncation_standard_dvd
        order hn
          (bound_tame_orders order hn htame)
        f hfDiv

/-- Lemma 1 for an arbitrary parenthesized commutator tree, with no weight
restriction.  Its recursive leaf-gcd order kills its value in the nilpotent
cyclic product. -/
theorem tree_order_orders
    {t n : ℕ}
    (order : Fin t → ℕ)
    (hn : 2 ≤ n)
    (htame : TameOrdersCutoff order n)
    (tree : HallTree (FreeGenerator.{u} t)) :
    inverseFreeTruncation order n
          (tree.toCWord.eval
            (freeTruncationValue t n)) ^
        hallTreeOrder
          (fun a : FreeGenerator.{u} t => order a.down)
          tree =
      1 := by
  let y :=
    tree.toCWord.eval
      (freeTruncationValue t n)
  let e : StandardExponentFamily.{u} t :=
    standardHallCoordinates t n hn y
  have he : standardHallProduct t n e = y :=
    standard_product_coordinates t n hn y
  have hdisplay :
      ∀ s, 1 ≤ s → s < n →
        ∀ i : (standardHallFamily.{u} t s).index,
          e s i ≠ 0 →
            generalStandardOrder order i ∣
              hallTreeOrder
                (fun a : FreeGenerator.{u} t => order a.down)
                tree := by
    intro s hs hsn i hne
    have hsupport :
        treeLabelSupport (concreteBasicTree i) tree := by
      apply label_forall_uses
      intro a ha
      obtain ⟨leaf, hleaf⟩ :=
        leaf_occurrence_uses ha
      by_contra hnotUses
      have hzero :=
        powered_leaf_uses
          t n hn tree leaf 1 s hs hsn i
            (by simpa [hleaf] using hnotUses)
      have : e s i = 0 := by
        simpa [e, y] using hzero
      exact hne this
    simpa [generalStandardOrder] using
      tree_label_support
        (fun a : FreeGenerator.{u} t => order a.down)
        hsupport
  have hresult :=
    corollary_standard_displayed
      order hn htame e hdisplay
  rw [he] at hresult
  exact hresult

/-- The source's below-cutoff formulation is an immediate specialization of
the unconditional arbitrary-tree order theorem. -/
theorem tree_tame_orders
    {t n : ℕ}
    (order : Fin t → ℕ)
    (hn : 2 ≤ n)
    (htame : TameOrdersCutoff order n)
    (tree : HallTree (FreeGenerator.{u} t))
    (_hrn : tree.weight < n) :
    inverseFreeTruncation order n
          (tree.toCWord.eval
            (freeTruncationValue t n)) ^
        hallTreeOrder
          (fun a : FreeGenerator.{u} t => order a.down)
          tree =
      1 :=
  tree_order_orders
    order hn htame tree

/-- Lemma 1's product clause in collected Hall form.  If every displayed
factor contains all labels occurring in `source`, their product is killed by
the recursive leaf-gcd order of `source`. -/
theorem standard_tree_support
    {t n : ℕ}
    (order : Fin t → ℕ)
    (hn : 2 ≤ n)
    (htame : TameOrdersCutoff order n)
    (source : HallTree (FreeGenerator.{u} t))
    (e : StandardExponentFamily.{u} t)
    (hsupport :
      ∀ s, 1 ≤ s → s < n →
        ∀ i : (standardHallFamily.{u} t s).index,
          e s i ≠ 0 →
            treeLabelSupport
              (concreteBasicTree i) source) :
    (inverseFreeTruncation order n
        (standardHallProduct t n e)) ^
        hallTreeOrder
          (fun a : FreeGenerator.{u} t => order a.down)
          source =
      1 := by
  apply
    corollary_standard_displayed
      order hn htame e
  intro s hs hsn i hne
  simpa [generalStandardOrder] using
    tree_label_support
      (fun a : FreeGenerator.{u} t => order a.down)
      (hsupport s hs hsn i hne)

/-- **Corollary to Theorem 3, Case II (all factors finite).**  If every
cyclic factor order divides `N`, then every element of the tame nilpotent
product has `N`th power equal to one. -/
theorem corollary_pow_one
    {t n N : ℕ}
    (order : Fin t → ℕ)
    (hn : 2 ≤ n)
    (htame : TameOrdersCutoff order n)
    (hN : ∀ i, order i ∣ N)
    (x : NilpotentCyclicProduct order n) :
    x ^ N = 1 := by
  obtain ⟨y, rfl⟩ :=
    inverse_truncation_surjective.{0} order n x
  obtain ⟨g, rfl⟩ :=
    QuotientGroup.mk'_surjective
      (Subgroup.lowerCentralSeries
        (FreeGroup (FreeGenerator.{0} t)) (n - 1)) y
  let z :=
    lowerCentralTruncation
      (FreeGroup (FreeGenerator.{0} t)) n (g ^ N)
  let e : StandardExponentFamily.{0} t :=
    standardHallCoordinates t n hn z
  have he : standardHallProduct t n e = z :=
    standard_product_coordinates t n hn z
  have hdiv :
      ∀ s, 1 ≤ s → s < n →
        ∀ i : (standardHallFamily.{0} t s).index,
          (generalStandardOrder order i : ℤ) ∣
            e s i := by
    exact
      general_standard_exponent.{0}
        order htame hN g e he
  have hresidues :
      generalResiduesFamily order n e = 0 := by
    funext r i
    change
      ((e (r + 1) i : ℤ) :
          ZMod (generalStandardOrder order i)) =
        0
    exact
      (ZMod.intCast_zmod_eq_zero_iff_dvd
        (e (r + 1) i)
        (generalStandardOrder order i)).2
          (hdiv (r + 1) (by omega) (by omega) i)
  have hzeroEval :
      generalResidueEval.{0} order n 0 = 1 := by
    have hzeroResidues :
        generalResiduesFamily order n
            (0 : StandardExponentFamily.{0} t) =
          0 := by
      funext r i
      simp [generalResiduesFamily]
    calc
      generalResidueEval.{0} order n 0 =
          generalResidueEval.{0} order n
            (generalResiduesFamily order n
              (0 : StandardExponentFamily.{0} t)) := by
        rw [hzeroResidues]
      _ =
          inverseFreeTruncation.{0} order n
            (standardHallProduct t n
              (0 : StandardExponentFamily.{0} t)) :=
        general_exponent_family
          order (bound_tame_orders order hn htame) 0
      _ = 1 := by
        rw [show
          standardHallProduct t n
              (0 : StandardExponentFamily.{0} t) =
            1 by
              apply
                collected_prefix_coordinates
                  (standardHallFamily.{0} t) 0 (n - 1)
              intro r _hr _hrn
              rfl]
        simp
  have hmapped : inverseFreeTruncation order n z = 1 := by
    rw [← he,
      ← general_exponent_family
        order (bound_tame_orders order hn htame) e,
      hresidues]
    exact hzeroEval
  calc
    (inverseFreeTruncation order n
        (lowerCentralTruncation
          (FreeGroup (FreeGenerator.{0} t)) n g)) ^ N =
        inverseFreeTruncation order n
          ((lowerCentralTruncation
            (FreeGroup (FreeGenerator.{0} t)) n g) ^ N) := by
      rw [map_pow]
    _ = inverseFreeTruncation order n z := by
      simp [z, map_pow]
    _ = 1 := hmapped

/-- **Corollary to Theorem 3, Case I.**  Suppose `e` is a collected Hall
normal form whose coordinates below weight `r` vanish.  If a weight-`r`
factor has recursive Hall order zero and occurs with nonzero exponent, then
the represented element has infinite order.

The hypothesis that lower coordinates vanish expresses the paper's choice of
an infinite cyclic factor of least weight. -/
theorem corollary_not_coordinate
    {t n r : ℕ}
    (order : Fin t → ℕ)
    (hn : 2 ≤ n)
    (htame : TameOrdersCutoff order n)
    (e : StandardExponentFamily.{u} t)
    (hr : 1 ≤ r)
    (hrn : r < n)
    (hzeroBelow :
      ∀ s, 1 ≤ s → s < r → e s = 0)
    (i : (standardHallFamily.{u} t r).index)
    (horder :
      generalStandardOrder order i = 0)
    (hexponent : e r i ≠ 0) :
    ¬ IsOfFinOrder
      (inverseFreeTruncation order n
        (standardHallProduct t n e)) := by
  intro hfinite
  obtain ⟨q, hq, hpow⟩ := hfinite.exists_pow_eq_one
  let y : LowerCentralTruncation
      (FreeGroup (FreeGenerator.{u} t)) n :=
    standardHallProduct t n e
  let f : StandardExponentFamily.{u} t :=
    standardHallCoordinates t n hn (y ^ q)
  have hprefix :
      collectedPrefixProduct
          (n := n) (standardHallFamily.{u} t) e (r - 1) =
        1 := by
    calc
      collectedPrefixProduct
          (n := n) (standardHallFamily.{u} t) e (r - 1) =
          collectedPrefixProduct
            (n := n) (standardHallFamily.{u} t)
            (0 : StandardExponentFamily.{u} t) (r - 1) := by
        apply collected_product_coordinates
        intro s hs hsr
        funext j
        simp [hzeroBelow s hs (by omega)]
      _ = 1 := by
        simp [collectedPrefixProduct,
          BCWta.collected_weight_productzero]
  have hy :
      y ∈ Subgroup.lowerCentralSeries
        (LowerCentralTruncation
          (FreeGroup (FreeGenerator.{u} t)) n) (r - 1) := by
    have hdecomposition :=
      collected_prefix_tail
        (n := n) (standardHallFamily.{u} t) e (r - 1)
        (by omega)
    have htail :=
      collected_tail_series
        (n := n) (standardHallFamily.{u} t) e (r - 1)
    change collectedHallProduct
        (n := n) (standardHallFamily.{u} t) e ∈
      Subgroup.lowerCentralSeries
        (LowerCentralTruncation
          (FreeGroup (FreeGenerator.{u} t)) n) (r - 1)
    rw [← hdecomposition, hprefix, _root_.one_mul]
    exact htail
  have hfMap :
      inverseFreeTruncation order n
          (standardHallProduct t n f) =
        1 := by
    rw [standard_product_coordinates]
    rw [map_pow]
    exact hpow
  have hdiv :
      (generalStandardOrder order i : ℤ) ∣
        f r i :=
    general_standard_dvd
      order htame f hfMap r hr hrn i
  have hfZero : f r i = 0 := by
    rw [horder] at hdiv
    simpa using hdiv
  have hpowerCoordinates :=
    form_coordinates_series
      hn (standardHallFamily.{u} t)
      (fun s hs hsn =>
        standard_forms_associated
          t n s hs hsn)
      hr hrn y hy q
  have hyCoordinates :
      standardHallCoordinates t n hn y r = e r :=
    standard_coordinates_product
      t n hn e y rfl r hr hrn
  have hyCoordinate :
      normalFormCoordinates hn (standardHallFamily.{u} t)
          (fun s _hs hsn =>
            standard_forms_associated
              t n s (by omega) hsn)
          y r i =
        e r i := by
    exact congrFun hyCoordinates i
  have hscaled :
      f r i = (q : ℤ) * e r i := by
    change
      normalFormCoordinates hn (standardHallFamily.{u} t)
          (fun s _hs hsn =>
            standard_forms_associated
              t n s (by omega) hsn)
          (y ^ q) r i =
        (q : ℤ) * e r i
    rw [congrFun hpowerCoordinates i, hyCoordinate]
  have hqInt : (q : ℤ) ≠ 0 :=
    Int.natCast_ne_zero_iff_pos.mpr hq
  exact hexponent
    ((Int.mul_eq_zero.mp
      (hscaled ▸ hfZero)).resolve_left hqInt)

/-- Order-zero form of Case I. -/
theorem corollary_order_coordinate
    {t n r : ℕ}
    (order : Fin t → ℕ)
    (hn : 2 ≤ n)
    (htame : TameOrdersCutoff order n)
    (e : StandardExponentFamily.{u} t)
    (hr : 1 ≤ r)
    (hrn : r < n)
    (hzeroBelow :
      ∀ s, 1 ≤ s → s < r → e s = 0)
    (i : (standardHallFamily.{u} t r).index)
    (horder :
      generalStandardOrder order i = 0)
    (hexponent : e r i ≠ 0) :
    orderOf
      (inverseFreeTruncation order n
        (standardHallProduct t n e)) =
      0 :=
  orderOf_eq_zero_iff.mpr
    (corollary_not_coordinate
      order hn htame e hr hrn hzeroBelow i horder hexponent)

/-- The correct general binomial divisibility at the Case III exponent:
`N` divides `choose (p * N) p` for every positive `p`.

Struik's printed claim has the stronger divisor `p * N`; the next theorem
records that this is false. -/
theorem common_multiple_choose
    (N p : ℕ) (hp : 0 < p) :
    N ∣ Nat.choose (p * N) p := by
  have hpN : 0 < p * N ∨ N = 0 := by
    by_cases hN : N = 0
    · exact Or.inr hN
    · exact Or.inl (Nat.mul_pos hp (Nat.pos_of_ne_zero hN))
  rcases hpN with hpN | rfl
  · have hidentity :=
      Nat.add_one_mul_choose_eq (p * N - 1) (p - 1)
    rw [Nat.sub_add_cancel hpN, Nat.sub_add_cancel hp] at hidentity
    have hcancel :
        p * (N * Nat.choose (p * N - 1) (p - 1)) =
          p * Nat.choose (p * N) p := by
      simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using
        hidentity
    refine ⟨Nat.choose (p * N - 1) (p - 1), ?_⟩
    exact (Nat.eq_of_mul_eq_mul_left hp hcancel).symm
  · cases p with
    | zero => omega
    | succ p => simp

/-- The finite-factor hypotheses printed in Case III are incompatible with
Theorem 3 itself: a prime divisor of a finite cyclic order must be strictly
larger than `n - 1`, so it cannot equal `n - 1`. -/
theorem iii_incompatible_orders
    {t n p : ℕ}
    (order : Fin t → ℕ)
    (htame : TameOrdersCutoff order n)
    (i : Fin t)
    (hfinite : order i ≠ 0)
    (hp : p.Prime)
    (hpOrder : p ∣ order i)
    (hboundary : p = n - 1) :
    False := by
  rcases htame i with hzero | hprime
  · exact hfinite hzero
  · have hlt : n - 1 < p := hprime p hp hpOrder
    omega

/-- Counterexample to the divisibility printed in Case III:
`p * N ∣ choose (p * N) p` fails for `p = N = 3`. -/
theorem iii_printed_false :
    ¬3 * 3 ∣ Nat.choose (3 * 3) 3 := by
  norm_num [Nat.choose]

/-- **Corollary to Theorem 3, Case III, sharp example.**  In the third
nilpotent product of two cyclic groups of order three, Struik's element
`ab` is not killed by the common factor order `N = 3`, but is killed by
`pN = 9` for the boundary prime `p = n - 1 = 3`. -/
theorem corollary_iii_example :
    orderPairProduct ^ 3 ≠ 1 ∧
      orderPairProduct ^ (3 * 3) = 1 := by
  constructor
  · intro hcube
    have hdvd :
        orderOf orderPairProduct ∣ 3 :=
      orderOf_dvd_of_pow_eq_one hcube
    rw [order_pair_product] at hdvd
    norm_num at hdvd
  · norm_num
    rw [← order_pair_product]
    exact pow_orderOf_eq_one orderPairProduct

end P1960
end Struik
