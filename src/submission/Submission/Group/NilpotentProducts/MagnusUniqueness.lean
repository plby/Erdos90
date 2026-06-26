import Submission.Group.NilpotentProducts.CoordinateKernel
import Submission.Group.NilpotentProducts.GeneralPolynomialCoordinates
import Submission.Algebra.Magnus.MagnusFunctoriality
import Submission.Algebra.Magnus.UniversalUnitriangularKernels


/-!
# The general uniqueness part of Struik's Theorem 3

For one Hall factor, reduce Magnus coefficients modulo the recursive gcd of
its leaf orders and send every unused free generator to the identity.  The
tame-prime hypothesis makes every cyclic order relation vanish in each
unitriangular word representation below the nilpotency cutoff.
-/

namespace Struik
namespace P1960

open EChapma
open EChapma.MSeries
open Submission
open Submission.Edmonton
open Submission.HallTree
open Submission.TCTex

universe u

noncomputable section

/-- Every label used by `source` is also used by `target`. -/
def treeLabelSupport
    {α : Type*} (target : HallTree α) :
    HallTree α → Prop
  | .atom a => hallTreeUses a target
  | .commutator left right =>
      treeLabelSupport target left ∧
        treeLabelSupport target right

noncomputable instance treeLabelDecidable
    {α : Type*} (target source : HallTree α) :
    Decidable (treeLabelSupport target source) :=
  Classical.propDecidable _

theorem label_forall_uses
    {α : Type*} {target source : HallTree α}
    (h :
      ∀ a, hallTreeUses a source → hallTreeUses a target) :
    treeLabelSupport target source := by
  induction source with
  | atom a =>
      exact h a (by simp [hallTreeUses])
  | commutator left right ihLeft ihRight =>
      constructor
      · exact ihLeft fun a ha =>
          h a (Or.inl ha)
      · exact ihRight fun a ha =>
          h a (Or.inr ha)

theorem tree_label_refl
    {α : Type*} (tree : HallTree α) :
    treeLabelSupport tree tree :=
  label_forall_uses
    (fun _ h => h)

theorem HallTree.evaleq_oneuses_valueeqone
    {α G : Type*} [Group G]
    (value : α → G) {a : α} :
    ∀ {tree : HallTree α}, hallTreeUses a tree → value a = 1 →
      tree.toCWord.eval value = 1
  | .atom b, huses, ha => by
      change b = a at huses
      subst b
      simpa using ha
  | .commutator left right, huses, ha => by
      rcases huses with hleft | hright
      · rw [HallTree.to_commutator_commutator,
          CWord.eval_commutator,
          HallTree.evaleq_oneuses_valueeqone
            value hleft ha]
        simp
      · rw [HallTree.to_commutator_commutator,
          CWord.eval_commutator,
          HallTree.evaleq_oneuses_valueeqone
            value hright ha]
        simp

/-- Keep exactly the free generators occurring in `target`. -/
def keepTreeValue
    {α G : Type*} [DecidableEq α] [Group G]
    (target : HallTree α) (value : α → G) (a : α) : G :=
  if hallTreeUses a target then value a else 1

theorem HallTree.eval_keephall_treevalue
    {α G : Type*} [DecidableEq α] [Group G]
    (target : HallTree α) (value : α → G) :
    ∀ source : HallTree α,
      source.toCWord.eval
          (keepTreeValue target value) =
        if treeLabelSupport target source then
          source.toCWord.eval value
        else 1
  | .atom a => by
      by_cases ha : hallTreeUses a target
      · simp [keepTreeValue, treeLabelSupport,
          ha]
      · simp [keepTreeValue, treeLabelSupport,
          ha]
  | .commutator left right => by
      rw [HallTree.to_commutator_commutator,
        CWord.eval_commutator,
        HallTree.eval_keephall_treevalue target value left,
        HallTree.eval_keephall_treevalue target value right]
      by_cases hleft : treeLabelSupport target left
      · by_cases hright : treeLabelSupport target right
        · simp [hleft, hright, treeLabelSupport]
        · simp [hleft, hright, treeLabelSupport]
      · simp [hleft, treeLabelSupport]

/-- Endomorphism of the free group which kills all generators not occurring
in `target`. -/
def keepTreeHom
    {α : Type*} [DecidableEq α]
    (target : HallTree α) :
    FreeGroup α →* FreeGroup α :=
  FreeGroup.lift
    (keepTreeValue target FreeGroup.of)

@[simp]
theorem keep_tree_generator
    {α : Type*} [DecidableEq α]
    (target : HallTree α) (a : α) :
    keepTreeHom target (FreeGroup.of a) =
      keepTreeValue target FreeGroup.of a := by
  simp [keepTreeHom]

theorem keep_tree_factor
    (t r : ℕ)
    (target : HallTree (FreeGenerator.{u} t))
    (i : (standardHallFamily.{u} t r).index) :
    keepTreeHom target
        ((standardHallFamily.{u} t r).commutator i
          |>.eval_in_freegroup) =
      if treeLabelSupport target (concreteBasicTree i) then
        (standardHallFamily.{u} t r).commutator i
          |>.eval_in_freegroup
      else 1 := by
  classical
  rw [BCWt.eval_in_freegroup]
  have hword :
      ((standardHallFamily.{u} t r).commutator i).word =
        (concreteBasicTree i).toCWord := by
    rfl
  rw [hword, CWord.map_eval]
  simp_rw [keep_tree_generator]
  exact HallTree.eval_keephall_treevalue
    target FreeGroup.of (concreteBasicTree i)

/-- Keep only Hall coordinates whose label support is contained in `target`. -/
def keepTreeFamily
    {t : ℕ}
    (target : HallTree (FreeGenerator.{u} t))
    (e : StandardExponentFamily.{u} t) :
    StandardExponentFamily.{u} t :=
  fun r i =>
    if treeLabelSupport target (concreteBasicTree i) then
      e r i
    else 0

theorem keep_tree_product
    (t r : ℕ)
    (target : HallTree (FreeGenerator.{u} t))
    (e : StandardExponentFamily.{u} t) :
    keepTreeHom target
        (freeStandardProduct t r (e r)) =
      freeStandardProduct t r
        ((keepTreeFamily target e) r) := by
  classical
  unfold freeStandardProduct freeStandardTerm
  rw [SubmonoidClass.coe_list_prod, SubmonoidClass.coe_list_prod,
    map_list_prod]
  apply congrArg List.prod
  simp only [List.map_map]
  apply List.map_congr_left
  intro i _hi
  change
    keepTreeHom target
        (((standardHallFamily.{u} t r).commutator i
          |>.eval_in_freegroup) ^ e r i) =
      ((standardHallFamily.{u} t r).commutator i
        |>.eval_in_freegroup) ^
          keepTreeFamily target e r i
  rw [map_zpow, keep_tree_factor]
  by_cases hsupport :
      treeLabelSupport target (concreteBasicTree i)
  · simp [hsupport, keepTreeFamily]
  · simp [hsupport, keepTreeFamily]

theorem keep_tree_prefix
    (t : ℕ)
    (target : HallTree (FreeGenerator.{u} t))
    (e : StandardExponentFamily.{u} t)
    (k : ℕ) :
    keepTreeHom target
        (freeStandardPrefix t e k) =
      freeStandardPrefix t
        (keepTreeFamily target e) k := by
  unfold freeStandardPrefix
  rw [map_list_prod]
  apply congrArg List.prod
  simp only [List.map_map]
  apply List.map_congr_left
  intro r _hr
  exact keep_tree_product
    t (r + 1) target e

theorem tree_label_support
    {α : Type*}
    (order : α → ℕ)
    {source target : HallTree α}
    (h : treeLabelSupport target source) :
    hallTreeOrder order target ∣ hallTreeOrder order source := by
  induction source generalizing target with
  | atom a =>
      exact tree_dvd_uses order a
        h
  | commutator left right ihLeft ihRight =>
      exact Nat.dvd_gcd
        (ihLeft h.1)
        (ihRight h.2)

theorem tree_tame_cutoff
    {t n : ℕ}
    (order : Fin t → ℕ)
    (htame : TameOrdersCutoff order n)
    (tree : HallTree (FreeGenerator.{u} t)) :
    TameOrderCutoff
      (hallTreeOrder (fun a : FreeGenerator.{u} t => order a.down) tree)
      (n - 1) := by
  induction tree with
  | atom a =>
      exact htame a.down
  | commutator left right ihLeft ihRight =>
      unfold hallTreeOrder
      by_cases hzero :
          Nat.gcd
              (hallTreeOrder
                (fun a : FreeGenerator.{u} t => order a.down) left)
              (hallTreeOrder
                (fun a : FreeGenerator.{u} t => order a.down) right) = 0
      · exact Or.inl hzero
      · refine Or.inr ?_
        intro p hp hporder
        rcases ihLeft with hleftZero | hleftPrime
        · rcases ihRight with hrightZero | hrightPrime
          · simp [hleftZero, hrightZero] at hzero
          · exact hrightPrime p hp
              (hporder.trans (Nat.gcd_dvd_right _ _))
        · exact hleftPrime p hp
            (hporder.trans (Nat.gcd_dvd_left _ _))

/-- A signed linear function on natural inputs is an integer-valued
polynomial of degree at most one. -/
theorem int_valued_most
    (c : ℤ) :
    IVMost
      (fun q : ℕ => (q : ℤ) * c)
      1 := by
  have hnatCast :
      IVMost
        (fun q : ℕ => (q : ℤ))
        1 := by
    refine ⟨Polynomial.X, by simp, ?_⟩
    intro q
    simp
  have hscaled :=
    IVMost.smul c hnatCast
  have heq :
      (fun q : ℕ => (q : ℤ) * c) =
        c • (fun q : ℕ => (q : ℤ)) := by
    funext q
    simp [mul_comm]
  rw [heq]
  exact hscaled

/-- A tame modulus divides every Magnus coefficient, through the cutoff,
of a power whose exponent is divisible by that modulus. -/
theorem magnus_difference_zpow
    {X : Type*}
    {modulus cutoff : ℕ}
    (htame : TameOrderCutoff modulus cutoff)
    (g : FreeGroup X)
    {m : ℤ}
    (hm : (modulus : ℤ) ∣ m)
    (w : FreeMonoid X)
    (hw : w.length ≤ cutoff) :
    (modulus : ℤ) ∣
      magnusDifference (R := ℤ) (g ^ m) w := by
  rcases hm with ⟨c, rfl⟩
  let exponent : ℕ → ℤ :=
    fun q => (q : ℤ) * c
  have hexponent :
      IVMost exponent 1 := by
    simpa [exponent] using
      int_valued_most c
  have horder :
      MPOrd
        (fun q =>
          magnusDifference (R := ℤ) (g ^ exponent q))
        0 :=
    MPOrd.fixedZPow
      g
      (magnus_vanishes_below g)
      (by omega)
      hexponent
  have hzero :
      magnusDifference (R := ℤ) (g ^ exponent 0) w = 0 := by
    simp [exponent, magnusDifference]
  simpa [exponent] using
    tame_valued_degree
      htame
      hw
      (horder.coefficientPolynomial w)
      hzero

/-- Word-coefficient representations of bounded length kill powers whose
exponents are divisible by a tame modulus. -/
theorem coefficient_representation_dvd
    {X : Type*}
    {modulus cutoff : ℕ}
    (htame : TameOrderCutoff modulus cutoff)
    (xs : List X)
    (hxs : xs.length ≤ cutoff)
    (g : FreeGroup X)
    {m : ℤ}
    (hm : (modulus : ℤ) ∣ m) :
    wordCoefficientRepresentation (R := ZMod modulus) xs (g ^ m) =
      1 := by
  classical
  apply Subtype.ext
  apply Units.ext
  apply IncidenceAlgebra.ext
  intro i j hij
  rw [word_coefficient_representation xs (g ^ m) i j hij]
  by_cases hijeq : i = j
  · subst j
    have hsegment :
        wordSegment xs i i = 1 := by
      apply FreeMonoid.length_eq_zero.mp
      rw [wordSegment_length xs i i le_rfl]
      simp
    rw [hsegment]
    simpa [IncidenceAlgebra.one_apply] using
      magnus_series_one
        (R := ZMod modulus) (X := X) (g ^ m)
  · have hsegmentPos :
        0 < (wordSegment xs i j).length := by
      rw [wordSegment_length xs i j hij]
      have hine : i.1 ≠ j.1 := by
        intro h
        exact hijeq (Fin.ext h)
      omega
    have hsegmentLe :
        (wordSegment xs i j).length ≤ cutoff := by
      rw [wordSegment_length xs i j hij]
      have hj : j.1 ≤ xs.length := by
        exact Nat.lt_succ_iff.mp j.isLt
      omega
    have hdvd :
        (modulus : ℤ) ∣
          magnusDifference (R := ℤ) (g ^ m)
            (wordSegment xs i j) :=
      magnus_difference_zpow
        htame g hm (wordSegment xs i j) hsegmentLe
    have hzero :
        magnusDifference (R := ZMod modulus) (g ^ m)
            (wordSegment xs i j) =
          0 := by
      rw [← coefficients_magnus_difference
        (Int.castRingHom (ZMod modulus)) (g ^ m)]
      change
        ((magnusDifference (R := ℤ) (g ^ m)
            (wordSegment xs i j) : ℤ) : ZMod modulus) = 0
      exact
        (ZMod.intCast_zmod_eq_zero_iff_dvd
          (magnusDifference (R := ℤ) (g ^ m)
            (wordSegment xs i j))
          modulus).2 hdvd
    have hone :
        (1 : MSeries (ZMod modulus) X)
            (wordSegment xs i j) =
          0 := by
      rw [one_apply]
      simp [hsegmentPos.ne']
    have hseries :
        magnusSeries (R := ZMod modulus) (g ^ m)
            (wordSegment xs i j) =
          0 := by
      rw [magnusDifference] at hzero
      exact (sub_eq_zero.mp hzero).trans hone
    rw [hseries]
    simp [IncidenceAlgebra.one_apply, hijeq]

/-- Exponents congruent modulo a tame modulus give the same bounded word
representation. -/
theorem representation_zpow_dvd
    {X : Type*}
    {modulus cutoff : ℕ}
    (htame : TameOrderCutoff modulus cutoff)
    (xs : List X)
    (hxs : xs.length ≤ cutoff)
    (g : FreeGroup X)
    (a b : ℤ)
    (hsub : (modulus : ℤ) ∣ b - a) :
    wordCoefficientRepresentation
        (R := ZMod modulus) xs (g ^ a) =
      wordCoefficientRepresentation
        (R := ZMod modulus) xs (g ^ b) := by
  have hdiff :=
    coefficient_representation_dvd
      htame xs hxs g hsub
  calc
    wordCoefficientRepresentation
        (R := ZMod modulus) xs (g ^ a) =
        wordCoefficientRepresentation
            (R := ZMod modulus) xs (g ^ a) *
          wordCoefficientRepresentation
            (R := ZMod modulus) xs (g ^ (b - a)) := by
      rw [hdiff]
      exact (_root_.mul_one _).symm
    _ =
        wordCoefficientRepresentation
          (R := ZMod modulus) xs
          (g ^ a * g ^ (b - a)) := by
      rw [map_mul]
    _ =
        wordCoefficientRepresentation
          (R := ZMod modulus) xs (g ^ b) := by
      congr 2
      rw [← zpow_add]
      congr
      omega

/-- After killing unused generators, a Hall weight block maps trivially in
the target word representation when all of its exponents are divisible by
their own recursive Hall orders. -/
theorem coefficient_representation_keep
    {t n r : ℕ}
    (order : Fin t → ℕ)
    (htame : TameOrdersCutoff order n)
    (target : HallTree (FreeGenerator.{u} t))
    (xs : List (FreeGenerator.{u} t))
    (hxs : xs.length ≤ n - 1)
    (e : (standardHallFamily.{u} t r).index → ℤ)
    (hdiv :
      ∀ i,
        (generalStandardOrder order i : ℤ) ∣ e i) :
    wordCoefficientRepresentation
        (R := ZMod
          (hallTreeOrder
            (fun a : FreeGenerator.{u} t => order a.down)
            target))
        xs
        (keepTreeHom target
          (freeStandardProduct t r e)) =
      1 := by
  classical
  unfold freeStandardProduct freeStandardTerm
  rw [SubmonoidClass.coe_list_prod, map_list_prod, map_list_prod]
  simp only [List.map_map]
  apply List.prod_eq_one
  intro z hz
  simp only [List.mem_map] at hz
  rcases hz with ⟨i, _hi, rfl⟩
  change
    wordCoefficientRepresentation
        (R := ZMod
          (hallTreeOrder
            (fun a : FreeGenerator.{u} t => order a.down)
            target))
        xs
        (keepTreeHom target
          (((standardHallFamily.{u} t r).commutator i
            |>.eval_in_freegroup) ^ e i)) =
      1
  rw [map_zpow, keep_tree_factor]
  by_cases hsupport :
      treeLabelSupport target (concreteBasicTree i)
  · have hdvdNat :
        hallTreeOrder
            (fun a : FreeGenerator.{u} t => order a.down)
            target ∣
          generalStandardOrder order i := by
      exact
        tree_label_support
          (fun a : FreeGenerator.{u} t => order a.down)
          hsupport
    have hdvdInt :
        (hallTreeOrder
            (fun a : FreeGenerator.{u} t => order a.down)
            target : ℤ) ∣
          e i := by
      exact (Int.ofNat_dvd.mpr hdvdNat).trans (hdiv i)
    simpa [hsupport] using
      coefficient_representation_dvd
        (tree_tame_cutoff order htame target)
        xs hxs
        ((standardHallFamily.{u} t r).commutator i
          |>.eval_in_freegroup)
        hdvdInt
  · simp [hsupport]

/-- The retained Hall prefix through weight `k` maps trivially when every
Hall exponent in that prefix is divisible by its recursive Hall order. -/
theorem representation_keep_tree
    {t n : ℕ}
    (order : Fin t → ℕ)
    (htame : TameOrdersCutoff order n)
    (target : HallTree (FreeGenerator.{u} t))
    (xs : List (FreeGenerator.{u} t))
    (hxs : xs.length ≤ n - 1)
    (e : StandardExponentFamily.{u} t)
    (k : ℕ)
    (hdiv :
      ∀ r, 1 ≤ r → r ≤ k →
        ∀ i : (standardHallFamily.{u} t r).index,
          (generalStandardOrder order i : ℤ) ∣
            e r i) :
    wordCoefficientRepresentation
        (R := ZMod
          (hallTreeOrder
            (fun a : FreeGenerator.{u} t => order a.down)
            target))
        xs
        (keepTreeHom target
          (freeStandardPrefix t e k)) =
      1 := by
  classical
  unfold freeStandardPrefix
  rw [map_list_prod, map_list_prod]
  simp only [List.map_map]
  apply List.prod_eq_one
  intro z hz
  simp only [List.mem_map] at hz
  rcases hz with ⟨j, hj, rfl⟩
  apply
    coefficient_representation_keep
      order htame target xs hxs (e (j + 1))
  intro i
  exact hdiv (j + 1) (by omega)
    (by
      have hjlt : j < k := List.mem_range.mp hj
      omega)
    i

/-- Two retained Hall prefixes have the same target word representation when
their corresponding exponents are congruent modulo their recursive Hall
orders. -/
theorem representation_keep_prefix
    {t n : ℕ}
    (order : Fin t → ℕ)
    (htame : TameOrdersCutoff order n)
    (target : HallTree (FreeGenerator.{u} t))
    (xs : List (FreeGenerator.{u} t))
    (hxs : xs.length ≤ n - 1)
    (e f : StandardExponentFamily.{u} t)
    (k : ℕ)
    (hcongr :
      ∀ r, 1 ≤ r → r ≤ k →
        ∀ i : (standardHallFamily.{u} t r).index,
          (generalStandardOrder order i : ℤ) ∣
            f r i - e r i) :
    wordCoefficientRepresentation
        (R := ZMod
          (hallTreeOrder
            (fun a : FreeGenerator.{u} t => order a.down)
            target))
        xs
        (keepTreeHom target
          (freeStandardPrefix t e k)) =
      wordCoefficientRepresentation
        (R := ZMod
          (hallTreeOrder
            (fun a : FreeGenerator.{u} t => order a.down)
            target))
        xs
        (keepTreeHom target
          (freeStandardPrefix t f k)) := by
  classical
  unfold freeStandardPrefix
  rw [map_list_prod, map_list_prod, map_list_prod, map_list_prod]
  simp only [List.map_map]
  apply congrArg List.prod
  apply List.map_congr_left
  intro j hj
  change
    wordCoefficientRepresentation
        (R := ZMod
          (hallTreeOrder
            (fun a : FreeGenerator.{u} t => order a.down)
            target))
        xs
        (keepTreeHom target
          (freeStandardProduct
            t (j + 1) (e (j + 1)))) =
      wordCoefficientRepresentation
        (R := ZMod
          (hallTreeOrder
            (fun a : FreeGenerator.{u} t => order a.down)
            target))
        xs
        (keepTreeHom target
          (freeStandardProduct
            t (j + 1) (f (j + 1))))
  unfold freeStandardProduct freeStandardTerm
  rw [SubmonoidClass.coe_list_prod, SubmonoidClass.coe_list_prod,
    map_list_prod, map_list_prod, map_list_prod, map_list_prod]
  simp only [List.map_map]
  apply congrArg List.prod
  apply List.map_congr_left
  intro i _hi
  change
    wordCoefficientRepresentation
        (R := ZMod
          (hallTreeOrder
            (fun a : FreeGenerator.{u} t => order a.down)
            target))
        xs
        (keepTreeHom target
          (((standardHallFamily.{u} t (j + 1)).commutator i
            |>.eval_in_freegroup) ^ e (j + 1) i)) =
      wordCoefficientRepresentation
        (R := ZMod
          (hallTreeOrder
            (fun a : FreeGenerator.{u} t => order a.down)
            target))
        xs
        (keepTreeHom target
          (((standardHallFamily.{u} t (j + 1)).commutator i
            |>.eval_in_freegroup) ^ f (j + 1) i))
  simp only [map_zpow, keep_tree_factor]
  by_cases hsupport :
      treeLabelSupport target (concreteBasicTree i)
  · have hdvdNat :
        hallTreeOrder
            (fun a : FreeGenerator.{u} t => order a.down)
            target ∣
          generalStandardOrder order i :=
      tree_label_support
        (fun a : FreeGenerator.{u} t => order a.down)
        hsupport
    have hdvdInt :
        (hallTreeOrder
            (fun a : FreeGenerator.{u} t => order a.down)
            target : ℤ) ∣
          f (j + 1) i - e (j + 1) i := by
      exact
        (Int.ofNat_dvd.mpr hdvdNat).trans
          (hcongr (j + 1) (by omega)
            (by
              have hjlt : j < k := List.mem_range.mp hj
              omega)
            i)
    simpa [hsupport] using
      representation_zpow_dvd
        (tree_tame_cutoff order htame target)
        xs hxs
        ((standardHallFamily.{u} t (j + 1)).commutator i
          |>.eval_in_freegroup)
        (e (j + 1) i)
        (f (j + 1) i)
        hdvdInt
  · simp [hsupport]

/-- If every word representation of a fixed length is trivial modulo
`modulus`, then every Magnus coefficient of that length is divisible by
`modulus` over the integers. -/
theorem magnus_difference_representations
    {X : Type*}
    {modulus s : ℕ}
    (g : FreeGroup X)
    (hrepresentations :
      ∀ xs : List X, xs.length = s →
        wordCoefficientRepresentation
            (R := ZMod modulus) xs g =
          1)
    (w : Submission.TBluepr.AssociativeWordsLength X s) :
    (modulus : ℤ) ∣
      magnusDifference (R := ℤ) g w.1 := by
  have hg :
      g ∈ magnusOrderSubgroup
        (R := ZMod modulus) (X := X) (s + 1) := by
    rw [magnus_coefficient_intersection
      (R := ZMod modulus) (X := X) (s + 1) (by omega)]
    change
      g ∈ ⨅ xs : {xs : List X // xs.length = s},
        MonoidHom.ker
          (wordCoefficientRepresentation
            (R := ZMod modulus) xs.1)
    rw [Subgroup.mem_iInf]
    intro xs
    rw [MonoidHom.mem_ker]
    exact hrepresentations xs.1 xs.2
  have hzero :
      magnusDifference (R := ZMod modulus) g w.1 = 0 := by
    exact hg w.1 (by
      rw [w.2]
      omega)
  rw [← coefficients_magnus_difference
    (Int.castRingHom (ZMod modulus)) g] at hzero
  change
    ((magnusDifference (R := ℤ) g w.1 : ℤ) :
      ZMod modulus) = 0 at hzero
  exact
    (ZMod.intCast_zmod_eq_zero_iff_dvd
      (magnusDifference (R := ℤ) g w.1)
      modulus).mp hzero

/-- The upper-unitriangular incidence group of dimension `N` has
zero-based nilpotency class at most `N - 1`. -/
theorem unitriangular_incidence_bot
    {R : Type*} [CommRing R]
    {N : ℕ}
    (hN : 1 ≤ N) :
    Subgroup.lowerCentralSeries
        (unitriangularIncidenceSubgroup R N) (N - 1) =
      ⊥ := by
  let U := unitriangularIncidenceSubgroup R N
  let φ : FreeGroup U →* U :=
    FreeGroup.lift id
  have hφsurj : Function.Surjective φ := by
    intro u
    refine ⟨FreeGroup.of u, ?_⟩
    simp [φ]
  rw [← Submission.Edmonton.central_series_surjective
    φ hφsurj (N - 1)]
  apply (Subgroup.map_eq_bot_iff
    (Subgroup.lowerCentralSeries (FreeGroup U) (N - 1))).2
  intro g hg
  have hMagnus :
      g ∈ magnusOrderSubgroup
        (R := R) (X := U) N := by
    have hraw :=
      lower_magnus_subgroup
        (R := R) (X := U) (N - 1) hg
    simpa [Nat.sub_add_cancel hN] using hraw
  have hUniversal :=
    subgroup_unitriangular_intersection
      (R := R) (X := U) N hMagnus
  change
    g ∈ ⨅ ψ : FreeGroup U →*
        unitriangularIncidenceSubgroup R N,
      MonoidHom.ker ψ at hUniversal
  rw [Subgroup.mem_iInf] at hUniversal
  exact hUniversal φ

/-- Matrix value assigned to one canonical cyclic generator.  The inverse
orientation compensates for `inverseFreeTruncation`. -/
def treeRepresentationValue
    {t : ℕ}
    (order : Fin t → ℕ)
    (target : HallTree (FreeGenerator.{u} t))
    (xs : List (FreeGenerator.{u} t))
    (i : Fin t) :
    unitriangularIncidenceSubgroup
      (ZMod
        (hallTreeOrder
          (fun a : FreeGenerator.{u} t => order a.down)
          target))
      (xs.length + 1) :=
  (wordCoefficientRepresentation
      (R := ZMod
        (hallTreeOrder
          (fun a : FreeGenerator.{u} t => order a.down)
          target))
      xs
      (keepTreeHom target
        (FreeGroup.of (ULift.up i))))⁻¹

theorem tree_cyclic_representation
    {t n : ℕ}
    (order : Fin t → ℕ)
    (htame : TameOrdersCutoff order n)
    (target : HallTree (FreeGenerator.{u} t))
    (xs : List (FreeGenerator.{u} t))
    (hxs : xs.length ≤ n - 1)
    (i : Fin t) :
    treeRepresentationValue order target xs i ^
        order i =
      1 := by
  classical
  by_cases hi :
      hallTreeUses (ULift.up i) target
  · have hdvdNat :
        hallTreeOrder
            (fun a : FreeGenerator.{u} t => order a.down)
            target ∣
          order i :=
      tree_dvd_uses
        (fun a : FreeGenerator.{u} t => order a.down)
        (ULift.up i)
        hi
    have hdvdInt :
        (hallTreeOrder
            (fun a : FreeGenerator.{u} t => order a.down)
            target : ℤ) ∣
          (order i : ℤ) := by
      exact_mod_cast hdvdNat
    have hrepresentation :=
      coefficient_representation_dvd
        (tree_tame_cutoff order htame target)
        xs hxs
        (keepTreeHom target
          (FreeGroup.of (ULift.up i)))
        hdvdInt
    have hrepresentationNat :
        wordCoefficientRepresentation
            (R := ZMod
              (hallTreeOrder
                (fun a : FreeGenerator.{u} t => order a.down)
                target))
            xs
            ((keepTreeHom target
              (FreeGroup.of (ULift.up i))) ^ order i) =
          1 := by
      simpa [zpow_natCast] using hrepresentation
    unfold treeRepresentationValue
    rw [inv_pow, ← map_pow, hrepresentationNat, inv_one]
  · simp [treeRepresentationValue,
      keep_tree_generator,
      keepTreeValue, hi]

/-- The word-coefficient detector descended to the nilpotent product of
cyclic groups. -/
noncomputable def treeCyclicRepresentation
    {t n : ℕ}
    (order : Fin t → ℕ)
    (htame : TameOrdersCutoff order n)
    (target : HallTree (FreeGenerator.{u} t))
    (xs : List (FreeGenerator.{u} t))
    (hxs : xs.length ≤ n - 1) :
    NilpotentCyclicProduct order n →*
      unitriangularIncidenceSubgroup
        (ZMod
          (hallTreeOrder
            (fun a : FreeGenerator.{u} t => order a.down)
            target))
        (xs.length + 1) := by
  let value :=
    treeRepresentationValue order target xs
  have hrelations :
      ∀ r ∈ cyclicOrderRelators order,
        FreeGroup.lift value r = 1 := by
    rintro r ⟨i, rfl⟩
    rw [map_pow, FreeGroup.lift_apply_of]
    exact
      tree_cyclic_representation
        order htame target xs hxs i
  let f : CyclicFreeProduct order →*
      unitriangularIncidenceSubgroup
        (ZMod
          (hallTreeOrder
            (fun a : FreeGenerator.{u} t => order a.down)
            target))
        (xs.length + 1) :=
    PresentedGroup.toGroup hrelations
  have hdimension :
      Subgroup.lowerCentralSeries
          (unitriangularIncidenceSubgroup
            (ZMod
              (hallTreeOrder
                (fun a : FreeGenerator.{u} t => order a.down)
                target))
            (xs.length + 1))
          xs.length =
        ⊥ := by
    simpa using
      unitriangular_incidence_bot
        (R := ZMod
          (hallTreeOrder
            (fun a : FreeGenerator.{u} t => order a.down)
            target))
        (N := xs.length + 1)
        (by omega)
  have hcutoff :
      Subgroup.lowerCentralSeries
          (unitriangularIncidenceSubgroup
            (ZMod
              (hallTreeOrder
                (fun a : FreeGenerator.{u} t => order a.down)
                target))
            (xs.length + 1))
          (n - 1) =
        ⊥ := by
    apply eq_bot_iff.mpr
    rw [← hdimension]
    exact Subgroup.lowerCentralSeries_antitone hxs
  exact QuotientGroup.lift
    (Subgroup.lowerCentralSeries (CyclicFreeProduct order) (n - 1))
    f
    (by
      intro x hx
      apply MonoidHom.mem_ker.mpr
      have hxmap :
          f x ∈
            Subgroup.lowerCentralSeries
              (unitriangularIncidenceSubgroup
                (ZMod
                  (hallTreeOrder
                    (fun a : FreeGenerator.{u} t => order a.down)
                    target))
                (xs.length + 1))
              (n - 1) :=
        Subgroup.lowerCentralSeries.map f (n - 1)
          (Subgroup.mem_map_of_mem f hx)
      rw [hcutoff] at hxmap
      exact hxmap)

@[simp]
theorem tree_representation_generator
    {t n : ℕ}
    (order : Fin t → ℕ)
    (htame : TameOrdersCutoff order n)
    (target : HallTree (FreeGenerator.{u} t))
    (xs : List (FreeGenerator.{u} t))
    (hxs : xs.length ≤ n - 1)
    (i : Fin t) :
    treeCyclicRepresentation order htame target xs hxs
        (nilpotentCyclicGenerator order n i) =
      treeRepresentationValue order target xs i := by
  simp [treeCyclicRepresentation,
    treeRepresentationValue,
    nilpotentCyclicGenerator, cyclicGenerator]

/-- Composing the descended detector with Struik's inverse-generator map
recovers the word representation of the kept free word. -/
theorem tree_representation_truncation
    {t n : ℕ}
    (order : Fin t → ℕ)
    (htame : TameOrdersCutoff order n)
    (target : HallTree (FreeGenerator.{u} t))
    (xs : List (FreeGenerator.{u} t))
    (hxs : xs.length ≤ n - 1)
    (y : FreeGroup (FreeGenerator.{u} t)) :
    treeCyclicRepresentation order htame target xs hxs
        (inverseFreeTruncation order n
          (lowerCentralTruncation
            (FreeGroup (FreeGenerator.{u} t)) n y)) =
      wordCoefficientRepresentation
        (R := ZMod
          (hallTreeOrder
            (fun a : FreeGenerator.{u} t => order a.down)
            target))
        xs
        (keepTreeHom target y) := by
  classical
  let left :
      FreeGroup (FreeGenerator.{u} t) →*
        unitriangularIncidenceSubgroup
          (ZMod
            (hallTreeOrder
              (fun a : FreeGenerator.{u} t => order a.down)
              target))
          (xs.length + 1) :=
    (treeCyclicRepresentation
      order htame target xs hxs).comp
        ((inverseFreeTruncation order n).comp
          (lowerCentralTruncation
            (FreeGroup (FreeGenerator.{u} t)) n))
  let right :
      FreeGroup (FreeGenerator.{u} t) →*
        unitriangularIncidenceSubgroup
          (ZMod
            (hallTreeOrder
              (fun a : FreeGenerator.{u} t => order a.down)
              target))
          (xs.length + 1) :=
    (wordCoefficientRepresentation
      (R := ZMod
        (hallTreeOrder
          (fun a : FreeGenerator.{u} t => order a.down)
          target))
      xs).comp
        (keepTreeHom target)
  have hhom : left = right := by
    apply FreeGroup.ext_hom
    intro a
    change
      treeCyclicRepresentation order htame target xs hxs
          (inverseFreeTruncation order n
            (lowerCentralTruncation
              (FreeGroup (FreeGenerator.{u} t)) n
              (FreeGroup.of a))) =
        wordCoefficientRepresentation
          (R := ZMod
            (hallTreeOrder
              (fun b : FreeGenerator.{u} t => order b.down)
              target))
          xs
          (keepTreeHom target (FreeGroup.of a))
    rw [inverse_truncation_generator, map_inv,
      tree_representation_generator]
    simp [treeRepresentationValue]
  exact DFunLike.congr_fun hhom y

/-- Choose the standard nonnegative integer representative of every Hall
residue coordinate, and use zero outside the represented weight range. -/
noncomputable def generalExponentRepresentatives
    {t : ℕ}
    (order : Fin t → ℕ)
    (n : ℕ)
    (z : GeneralHallResidues.{u} order n) :
    StandardExponentFamily.{u} t :=
  fun r =>
    match r with
    | 0 => fun _ => 0
    | k + 1 =>
        fun i =>
          if hk : k < n - 1 then
            zmodRepresentative (z ⟨k, hk⟩ i)
          else 0

@[simp]
theorem general_residues_representatives
    {t : ℕ}
    (order : Fin t → ℕ)
    (n : ℕ)
    (z : GeneralHallResidues.{u} order n) :
    generalResiduesFamily order n
        (generalExponentRepresentatives order n z) =
      z := by
  funext r i
  simp [generalResiduesFamily,
    generalExponentRepresentatives,
    zmodRepresentative_cast]

set_option maxHeartbeats 800000 in
-- Expanding and comparing the collected Hall coordinates is computationally intensive.
/-- Evaluating reduced integral Hall coordinates agrees with first forming
their collected Hall product and then mapping to the cyclic nilpotent
product. -/
theorem general_exponent_family
    {t n : ℕ}
    (order : Fin t → ℕ)
    (hbound : FactorOrderBound.{u} order n)
    (e : StandardExponentFamily.{u} t) :
    generalResidueEval.{u} order n
        (generalResiduesFamily order n e) =
      inverseFreeTruncation.{u} order n
        (standardHallProduct t n e) := by
  unfold generalResidueEval
  rw [show
      ((List.range (n - 1)).attach.map fun r =>
        mappedGeneralProduct order n (r.1 + 1)
          (generalResiduesFamily order n e
            ⟨r.1, List.mem_range.mp r.2⟩)).prod =
        ((List.range (n - 1)).attach.map fun r =>
          inverseFreeTruncation.{u} order n
            ((standardHallFamily.{u} t (r.1 + 1)).collectedWeightProduct
              (n := n) (e (r.1 + 1)))).prod by
      apply congrArg List.prod
      apply List.map_congr_left
      intro r _hr
      apply mapped_general_cast
        order n (r.1 + 1) hbound
      · omega
      · have hrlt : r.1 < n - 1 := List.mem_range.mp r.2
        omega]
  let factors : ℕ →
      LowerCentralTruncation
        (FreeGroup (FreeGenerator.{u} t)) n :=
    fun r =>
      (standardHallFamily.{u} t (r + 1)).collectedWeightProduct
        (n := n) (e (r + 1))
  let mappedFactors : ℕ → NilpotentCyclicProduct order n :=
    fun r => inverseFreeTruncation.{u} order n (factors r)
  change
    ((List.range (n - 1)).attach.map fun r =>
      mappedFactors r.1).prod =
      inverseFreeTruncation.{u} order n
        (standardHallProduct t n e)
  rw [show
      ((List.range (n - 1)).attach.map fun r =>
        mappedFactors r.1).prod =
        ((List.range (n - 1)).map mappedFactors).prod by
      exact congrArg List.prod
        (List.attach_map_val
          (l := List.range (n - 1)) (f := mappedFactors))]
  calc
    ((List.range (n - 1)).map mappedFactors).prod =
        inverseFreeTruncation.{u} order n
          (((List.range (n - 1)).map factors).prod) := by
      simpa [mappedFactors] using
        (map_list_prod (inverseFreeTruncation.{u} order n)
          ((List.range (n - 1)).map factors)).symm
    _ = inverseFreeTruncation.{u} order n
          (standardHallProduct t n e) := by
      rfl

/-- If a collected integral Hall product maps to the identity in the
nilpotent product of cyclic groups, then every Hall exponent is divisible by
its recursive Hall order. -/
theorem general_standard_dvd
    {t n : ℕ}
    (order : Fin t → ℕ)
    (htame : TameOrdersCutoff order n)
    (e : StandardExponentFamily.{u} t)
    (hmap :
      inverseFreeTruncation order n
          (standardHallProduct t n e) =
        1) :
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
      have he :
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
          have hcompatibility :=
            tree_representation_truncation
              order htame target xs hxs y
          change
            treeCyclicRepresentation
                order htame target xs hxs
                (inverseFreeTruncation order n
                  (lowerCentralTruncation
                    (FreeGroup (FreeGenerator.{u} t)) n y)) =
              wordCoefficientRepresentation
                (R := ZMod
                  (generalStandardOrder order i))
                xs keptY at hcompatibility
          rw [← he, hmap, map_one] at hcompatibility
          exact hcompatibility.symm
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
              Submission.TBluepr.AssociativeWordsLength
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
          Submission.TBluepr.AssociativeHomogeneousWords
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

/-- Equality of two mapped collected Hall products forces coordinatewise
congruence modulo every recursive Hall-factor order. -/
theorem general_standard_sub
    {t n : ℕ}
    (order : Fin t → ℕ)
    (htame : TameOrdersCutoff order n)
    (e f : StandardExponentFamily.{u} t)
    (hmap :
      inverseFreeTruncation order n
          (standardHallProduct t n e) =
        inverseFreeTruncation order n
          (standardHallProduct t n f)) :
    ∀ s, 1 ≤ s → s < n →
      ∀ i : (standardHallFamily.{u} t s).index,
        (generalStandardOrder order i : ℤ) ∣
          f s i - e s i := by
  intro s
  induction s using Nat.strong_induction_on with
  | h s ih =>
      intro hs hsn i
      classical
      let yE : FreeGroup (FreeGenerator.{u} t) :=
        freeStandardPrefix t e (n - 1)
      let yF : FreeGroup (FreeGenerator.{u} t) :=
        freeStandardPrefix t f (n - 1)
      have he :
          standardHallProduct t n e =
            lowerCentralTruncation
              (FreeGroup (FreeGenerator.{u} t)) n yE := by
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
                (FreeGroup (FreeGenerator.{u} t)) n yE :=
            rfl
      have hf :
          standardHallProduct t n f =
            lowerCentralTruncation
              (FreeGroup (FreeGenerator.{u} t)) n yF := by
        calc
          standardHallProduct t n f =
              collectedPrefixProduct
                (n := n) (standardHallFamily.{u} t) f (n - 1) :=
            rfl
          _ =
              lowerCentralTruncation
                (FreeGroup (FreeGenerator.{u} t)) n
                (freeStandardPrefix t f (n - 1)) :=
            (truncation_standard_prefix
              t n (n - 1) f).symm
          _ =
              lowerCentralTruncation
                (FreeGroup (FreeGenerator.{u} t)) n yF :=
            rfl
      let target : HallTree (FreeGenerator.{u} t) :=
        concreteBasicTree i
      let keptE : StandardExponentFamily.{u} t :=
        keepTreeFamily target e
      let keptF : StandardExponentFamily.{u} t :=
        keepTreeFamily target f
      let keptYE : FreeGroup (FreeGenerator.{u} t) :=
        keepTreeHom target yE
      let keptYF : FreeGroup (FreeGenerator.{u} t) :=
        keepTreeHom target yF
      have heKeep :
          standardHallProduct t n keptE =
            lowerCentralTruncation
              (FreeGroup (FreeGenerator.{u} t)) n keptYE := by
        have hkeptY :
            keptYE =
              freeStandardPrefix t keptE (n - 1) := by
          dsimp [keptYE, keptE, yE]
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
                (FreeGroup (FreeGenerator.{u} t)) n keptYE := by
            rw [hkeptY]
      have hfKeep :
          standardHallProduct t n keptF =
            lowerCentralTruncation
              (FreeGroup (FreeGenerator.{u} t)) n keptYF := by
        have hkeptY :
            keptYF =
              freeStandardPrefix t keptF (n - 1) := by
          dsimp [keptYF, keptF, yF]
          exact
            keep_tree_prefix
              t target f (n - 1)
        calc
          standardHallProduct t n keptF =
              collectedPrefixProduct
                (n := n) (standardHallFamily.{u} t)
                keptF (n - 1) :=
            rfl
          _ =
              lowerCentralTruncation
                (FreeGroup (FreeGenerator.{u} t)) n
                (freeStandardPrefix
                  t keptF (n - 1)) :=
            (truncation_standard_prefix
              t n (n - 1) keptF).symm
          _ =
              lowerCentralTruncation
                (FreeGroup (FreeGenerator.{u} t)) n keptYF := by
            rw [hkeptY]
      let residualE : FreeGroup (FreeGenerator.{u} t) :=
        (freeStandardPrefix t keptE (s - 1))⁻¹ *
          keptYE
      let residualF : FreeGroup (FreeGenerator.{u} t) :=
        (freeStandardPrefix t keptF (s - 1))⁻¹ *
          keptYF
      have hresidualEMem :
          residualE ∈
            Subgroup.lowerCentralSeries
              (FreeGroup (FreeGenerator.{u} t)) (s - 1) :=
        free_standard_series
          t n (s - 1) (by omega) keptE keptYE heKeep
      have hresidualFMem :
          residualF ∈
            Subgroup.lowerCentralSeries
              (FreeGroup (FreeGenerator.{u} t)) (s - 1) :=
        free_standard_series
          t n (s - 1) (by omega) keptF keptYF hfKeep
      let quotientResidual : FreeGroup (FreeGenerator.{u} t) :=
        residualE⁻¹ * residualF
      have hquotientMem :
          quotientResidual ∈
            Subgroup.lowerCentralSeries
              (FreeGroup (FreeGenerator.{u} t)) (s - 1) :=
        (Subgroup.lowerCentralSeries
          (FreeGroup (FreeGenerator.{u} t)) (s - 1)).mul_mem
          ((Subgroup.lowerCentralSeries
            (FreeGroup (FreeGenerator.{u} t)) (s - 1)).inv_mem
            hresidualEMem)
          hresidualFMem
      have hquotientRepresentations :
          ∀ xs : List (FreeGenerator.{u} t),
            xs.length = s →
            wordCoefficientRepresentation
                (R := ZMod
                  (generalStandardOrder order i))
                xs quotientResidual =
              1 := by
        intro xs hxsLength
        have hxs : xs.length ≤ n - 1 := by
          rw [hxsLength]
          omega
        have hfull :
            wordCoefficientRepresentation
                (R := ZMod
                  (generalStandardOrder order i))
                xs keptYE =
              wordCoefficientRepresentation
                (R := ZMod
                  (generalStandardOrder order i))
                xs keptYF := by
          have hcompatibilityE :=
            tree_representation_truncation
              order htame target xs hxs yE
          have hcompatibilityF :=
            tree_representation_truncation
              order htame target xs hxs yF
          change
            treeCyclicRepresentation
                order htame target xs hxs
                (inverseFreeTruncation order n
                  (lowerCentralTruncation
                    (FreeGroup (FreeGenerator.{u} t)) n yE)) =
              wordCoefficientRepresentation
                (R := ZMod
                  (generalStandardOrder order i))
                xs keptYE at hcompatibilityE
          change
            treeCyclicRepresentation
                order htame target xs hxs
                (inverseFreeTruncation order n
                  (lowerCentralTruncation
                    (FreeGroup (FreeGenerator.{u} t)) n yF)) =
              wordCoefficientRepresentation
                (R := ZMod
                  (generalStandardOrder order i))
                xs keptYF at hcompatibilityF
          rw [← he] at hcompatibilityE
          rw [← hf] at hcompatibilityF
          exact hcompatibilityE.symm.trans
            ((congrArg
              (treeCyclicRepresentation
                order htame target xs hxs)
              hmap).trans hcompatibilityF)
        have hprefix :
            wordCoefficientRepresentation
                (R := ZMod
                  (generalStandardOrder order i))
                xs
                (freeStandardPrefix
                  t keptE (s - 1)) =
              wordCoefficientRepresentation
                (R := ZMod
                  (generalStandardOrder order i))
                xs
                (freeStandardPrefix
                  t keptF (s - 1)) := by
          rw [← keep_tree_prefix
              t target e (s - 1),
            ← keep_tree_prefix
              t target f (s - 1)]
          apply
            representation_keep_prefix
              order htame target xs hxs e f (s - 1)
          intro r hr hrs j
          exact ih r (by omega) hr (by omega) j
        have hresidual :
            wordCoefficientRepresentation
                (R := ZMod
                  (generalStandardOrder order i))
                xs residualE =
              wordCoefficientRepresentation
                (R := ZMod
                  (generalStandardOrder order i))
                xs residualF := by
          simp [residualE, residualF, map_mul, map_inv,
            hprefix, hfull]
        simp [quotientResidual, map_mul, map_inv, hresidual]
      have hpdiv :
          ∀ w :
              Submission.TBluepr.AssociativeWordsLength
                (FreeGenerator.{u} t) s,
            (generalStandardOrder order i : ℤ) ∣
              (homogeneousPart s
                (magnusDifference
                  (R := ℤ) quotientResidual)).1 w.1 := by
        intro w
        rw [homogeneousPart_apply]
        exact
          magnus_difference_representations
            quotientResidual hquotientRepresentations w
      obtain ⟨q, hscalar⟩ :=
        homogeneous_smul_dvd
          (X := FreeGenerator.{u} t) hpdiv
      let L :
          Submission.TBluepr.AssociativeHomogeneousWords
            ℤ (FreeGenerator.{u} t) s →ₗ[ℤ] ℤ :=
        HMCoord.linearMap i.down
      have hclass :
          lowerCentralWeight hquotientMem =
            - lowerCentralWeight hresidualEMem +
              lowerCentralWeight hresidualFMem := by
        let F := FreeGroup (FreeGenerator.{u} t)
        let A : Subgroup F := Subgroup.lowerCentralSeries F (s - 1)
        let B : Subgroup A :=
          (Subgroup.lowerCentralSeries F ((s - 1) + 1)).subgroupOf A
        let qmap : A →* A ⧸ B := QuotientGroup.mk' B
        change
          Additive.ofMul
              (qmap ⟨quotientResidual, hquotientMem⟩) =
            - Additive.ofMul
                (qmap ⟨residualE, hresidualEMem⟩) +
              Additive.ofMul
                (qmap ⟨residualF, hresidualFMem⟩)
        have hsubgroup :
            (⟨quotientResidual, hquotientMem⟩ : A) =
              (⟨residualE, hresidualEMem⟩ : A)⁻¹ *
                (⟨residualF, hresidualFMem⟩ : A) := by
          rfl
        rw [hsubgroup, map_mul, map_inv]
        rfl
      have hcoordinate :
          L (homogeneousPart s
              (magnusDifference (R := ℤ) quotientResidual)) =
            f s i - e s i := by
        calc
          L (homogeneousPart s
              (magnusDifference (R := ℤ) quotientResidual)) =
              (HallTree.freePBWUniqueness
                  (IMagnus.hallPBWInput
                    (X := FreeGenerator.{u} t)) hs).repr
                (lowerCentralWeight hquotientMem) i.down := by
                  exact
                    HMCoord.linear_lower_class
                      hs hquotientMem i.down
          _ =
              - (HallTree.freePBWUniqueness
                  (IMagnus.hallPBWInput
                    (X := FreeGenerator.{u} t)) hs).repr
                    (lowerCentralWeight hresidualEMem) i.down +
                (HallTree.freePBWUniqueness
                  (IMagnus.hallPBWInput
                    (X := FreeGenerator.{u} t)) hs).repr
                    (lowerCentralWeight hresidualFMem) i.down := by
              rw [hclass]
              simp
          _ = -(keptE s i) + keptF s i := by
              rw [
                free_standard_coordinate
                  t n s hs hsn keptE keptYE heKeep
                  hresidualEMem i,
                free_standard_coordinate
                  t n s hs hsn keptF keptYF hfKeep
                  hresidualFMem i]
          _ = f s i - e s i := by
              simp [keptE, keptF, keepTreeFamily,
                target, tree_label_refl]
              ring
      refine ⟨L q, ?_⟩
      rw [← hcoordinate, hscalar, map_smul]
      simp

/-- The uniqueness kernel in Struik's Theorem 3 for every tame cutoff. -/
theorem kernel_statement_orders
    {t n : ℕ}
    (order : Fin t → ℕ)
    (hn : 2 ≤ n)
    (htame : TameOrdersCutoff order n) :
    (Function.Injective (generalResidueEval.{u} order n)) := by
  intro z w hzw
  classical
  let e : StandardExponentFamily.{u} t :=
    generalExponentRepresentatives order n z
  let f : StandardExponentFamily.{u} t :=
    generalExponentRepresentatives order n w
  have hbound : FactorOrderBound.{u} order n :=
    bound_tame_orders order hn htame
  have hmap :
      inverseFreeTruncation order n
          (standardHallProduct t n e) =
        inverseFreeTruncation order n
          (standardHallProduct t n f) := by
    calc
      inverseFreeTruncation order n
          (standardHallProduct t n e) =
          generalResidueEval.{u} order n
            (generalResiduesFamily order n e) :=
        (general_exponent_family
          order hbound e).symm
      _ = generalResidueEval.{u} order n z := by
        rw [show
          generalResiduesFamily order n e = z by
            exact
              general_residues_representatives
                order n z]
      _ = generalResidueEval.{u} order n w := hzw
      _ =
          generalResidueEval.{u} order n
            (generalResiduesFamily order n f) := by
        rw [show
          generalResiduesFamily order n f = w by
            exact
              general_residues_representatives
                order n w]
      _ =
          inverseFreeTruncation order n
            (standardHallProduct t n f) :=
        general_exponent_family
          order hbound f
  have hdiv :=
    general_standard_sub
      order htame e f hmap
  funext r i
  have hz :=
    congrArg
      (fun q : GeneralHallResidues.{u} order n => q r i)
      (general_residues_representatives
        order n z)
  have hw :=
    congrArg
      (fun q : GeneralHallResidues.{u} order n => q r i)
      (general_residues_representatives
        order n w)
  change
    ((e (r + 1) i : ℤ) :
      ZMod (generalStandardOrder order i)) =
      z r i at hz
  change
    ((f (r + 1) i : ℤ) :
      ZMod (generalStandardOrder order i)) =
      w r i at hw
  have hdvd :
      (generalStandardOrder order i : ℤ) ∣
        f (r + 1) i - e (r + 1) i :=
    hdiv (r + 1) (by omega)
      (by
        have hr := r.isLt
        omega)
      i
  have hzero :
      ((f (r + 1) i - e (r + 1) i : ℤ) :
        ZMod (generalStandardOrder order i)) =
        0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd
      (f (r + 1) i - e (r + 1) i)
      (generalStandardOrder order i)).2 hdvd
  have hcast :
      ((e (r + 1) i : ℤ) :
          ZMod (generalStandardOrder order i)) =
        ((f (r + 1) i : ℤ) :
          ZMod (generalStandardOrder order i)) := by
    exact
      (sub_eq_zero.mp
        (by simpa only [Int.cast_sub] using hzero)).symm
  exact hz.symm.trans (hcast.trans hw)

/-- Struik's Theorem 3: tame generator orders give unique Hall-residue
coordinates at every nondegenerate cutoff. -/
theorem statement_tame_orders
    {t n : ℕ}
    (order : Fin t → ℕ)
    (hn : 2 ≤ n)
    (htame : TameOrdersCutoff order n) :
    (Function.Bijective (generalResidueEval.{u} order n)) := by
  apply
    (coordinateStatement_iff order n
      (bound_tame_orders order hn htame)).2
  exact kernel_statement_orders order hn htame

end

end P1960
end Struik
