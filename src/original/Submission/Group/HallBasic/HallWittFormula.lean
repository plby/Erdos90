import Submission.Group.HallBasic.HallWittRank
import Mathlib.Data.Finsupp.Weight
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Subtype
import Mathlib.Data.Multiset.Sort
import Mathlib.Data.Finsupp.Multiset
import Submission.Group.HallBasic.StandardSequence
import Submission.Group.Edmonton.HallBasicCommutators


noncomputable section

open scoped BigOperators

namespace Submission
namespace HallWitt

variable {σ : Type} [Fintype σ] [DecidableEq σ]

def WeightedFinsupp (w : σ → ℕ) (n : ℕ) :=
  {f : σ →₀ ℕ // f.weight w = n}

class PositiveWeights (w : σ → ℕ) : Prop where
  ne_zero (s : σ) : w s ≠ 0

noncomputable instance weightedFinsuppFintype
    (w : σ → ℕ) [PositiveWeights w] (n : ℕ) :
    Fintype (WeightedFinsupp w n) :=
  Set.Finite.fintype
    ((Finsupp.finite_of_nat_weight_le w PositiveWeights.ne_zero n).subset
      (fun _ h => le_of_eq h))

def PositiveCopies (w : σ → ℕ) (s : σ) (n : ℕ) :=
  {k : ℕ // 1 ≤ k ∧ k * w s ≤ n}

noncomputable instance positiveCopiesFintype
    (w : σ → ℕ) [PositiveWeights w] (s : σ) (n : ℕ) :
    Fintype (PositiveCopies w s n) :=
  Set.Finite.fintype
    (Set.finite_Icc 1 n |>.subset fun k hk => by
      constructor
      · exact hk.1
      · have hkle : k ≤ k * w s := by
          exact Nat.le_mul_of_pos_right
            k (Nat.zero_lt_of_ne_zero
              (PositiveWeights.ne_zero s))
        exact hkle.trans hk.2)

omit [Fintype σ] [DecidableEq σ] in
private theorem sub_single_nat
    (w : σ → ℕ) (f : σ →₀ ℕ) (s : σ) (k : ℕ)
    (hk : k ≤ f s) :
    (f - Finsupp.single s k).weight w + k * w s =
      f.weight w := by
  have hsingle :
      Finsupp.single s k ≤ f :=
    Finsupp.single_le_iff.mpr hk
  have hdecomp :
      f - Finsupp.single s k + Finsupp.single s k = f :=
    tsub_add_cancel_of_le hsingle
  have hweight := congrArg (Finsupp.weight w) hdecomp
  simpa [map_add, Finsupp.weight_single, nsmul_eq_mul] using hweight

omit [Fintype σ] [DecidableEq σ] in
private theorem weight_single_nat
    (w : σ → ℕ) (f : σ →₀ ℕ) (s : σ) (k : ℕ) :
    (f + Finsupp.single s k).weight w =
      f.weight w + k * w s := by
  simp [map_add, Finsupp.weight_single]

def removeMarkedCopies
    (w : σ → ℕ) (n : ℕ) (s : σ)
    (x : Σ f : WeightedFinsupp w n, Fin (f.1 s)) :
    Σ k : PositiveCopies w s n,
      WeightedFinsupp w (n - k.1 * w s) := by
  let k := x.2.1 + 1
  have hk_le : k ≤ x.1.1 s := by
    exact Nat.succ_le_iff.mpr x.2.2
  have hkw_le : k * w s ≤ n := by
    rw [← x.1.2]
    exact (Nat.le_add_left _ _).trans_eq
      (sub_single_nat w x.1.1 s k hk_le)
  exact
    ⟨⟨k, Nat.succ_pos _, hkw_le⟩,
      ⟨x.1.1 - Finsupp.single s k, by
        have hsub :=
          sub_single_nat w x.1.1 s k hk_le
        rw [x.1.2] at hsub
        exact
          ((tsub_eq_iff_eq_add_of_le hkw_le).2
            hsub.symm).symm⟩⟩

def insertMarkedCopies
    (w : σ → ℕ) (n : ℕ) (s : σ)
    (x : Σ k : PositiveCopies w s n,
      WeightedFinsupp w (n - k.1 * w s)) :
    Σ f : WeightedFinsupp w n, Fin (f.1 s) := by
  let f := x.2.1 + Finsupp.single s x.1.1
  have hfweight : f.weight w = n := by
    rw [weight_single_nat, x.2.2,
      Nat.sub_add_cancel x.1.2.2]
  have hklt : x.1.1 - 1 < f s := by
    have hkpos := x.1.2.1
    simp only [f, Finsupp.add_apply, Finsupp.single_eq_same]
    omega
  exact ⟨⟨f, hfweight⟩, ⟨x.1.1 - 1, hklt⟩⟩

noncomputable def markedCopiesEquiv
    (w : σ → ℕ) (n : ℕ) (s : σ) :
    (Σ f : WeightedFinsupp w n, Fin (f.1 s)) ≃
      (Σ k : PositiveCopies w s n,
        WeightedFinsupp w (n - k.1 * w s)) where
  toFun := removeMarkedCopies w n s
  invFun := insertMarkedCopies w n s
  left_inv := by
    rintro ⟨⟨f, hf⟩, j⟩
    have hfback :
        f - Finsupp.single s (j.1 + 1) +
            Finsupp.single s (j.1 + 1) = f :=
      tsub_add_cancel_of_le
        (Finsupp.single_le_iff.mpr
          (Nat.succ_le_iff.mpr j.2))
    have hfirst :
        (insertMarkedCopies w n s
          (removeMarkedCopies w n s ⟨⟨f, hf⟩, j⟩)).1 =
          ⟨f, hf⟩ := by
      apply Subtype.ext
      simpa [removeMarkedCopies, insertMarkedCopies] using hfback
    apply Sigma.ext hfirst
    apply
      (Fin.heq_ext_iff
        (congrArg
          (fun g : WeightedFinsupp w n => g.1 s)
          hfirst)).2
    simp [removeMarkedCopies, insertMarkedCopies]
  right_inv := by
    rintro ⟨k, ⟨f, hf⟩⟩
    have hkback : k.1 - 1 + 1 = k.1 := by
      exact Nat.sub_add_cancel k.2.1
    have hfirst :
        (removeMarkedCopies w n s
          (insertMarkedCopies w n s ⟨k, ⟨f, hf⟩⟩)).1 = k := by
      apply Subtype.ext
      simpa [removeMarkedCopies, insertMarkedCopies] using hkback
    apply Sigma.ext hfirst
    apply
      (Subtype.heq_iff_coe_eq
        (fun g : σ →₀ ℕ => by
          rw [hfirst])).2
    simp only [removeMarkedCopies, insertMarkedCopies]
    rw [hkback, add_tsub_cancel_right]

def weightedFinsuppCount
    (w : σ → ℕ) [PositiveWeights w] (n : ℕ) : ℕ :=
  Fintype.card (WeightedFinsupp w n)

omit [DecidableEq σ] in
theorem weighted_finsupp_count
    (w : σ → ℕ) [PositiveWeights w]
    (n : ℕ) (s : σ) :
    ∑ f : WeightedFinsupp w n, f.1 s =
      ∑ k : PositiveCopies w s n,
        weightedFinsuppCount w (n - k.1 * w s) := by
  classical
  calc
    ∑ f : WeightedFinsupp w n, f.1 s =
        Fintype.card
          (Σ f : WeightedFinsupp w n, Fin (f.1 s)) := by
      rw [Fintype.card_sigma]
      simp
    _ =
        Fintype.card
          (Σ k : PositiveCopies w s n,
            WeightedFinsupp w (n - k.1 * w s)) :=
      Fintype.card_congr (markedCopiesEquiv w n s)
    _ = _ := by
      rw [Fintype.card_sigma]
      rfl

omit [DecidableEq σ] in
theorem weighted_finsupp_recurrence
    (w : σ → ℕ) [PositiveWeights w]
    (n : ℕ) :
    n * weightedFinsuppCount w n =
      ∑ s : σ, w s *
        ∑ k : PositiveCopies w s n,
          weightedFinsuppCount w (n - k.1 * w s) := by
  classical
  calc
    n * weightedFinsuppCount w n =
        ∑ f : WeightedFinsupp w n, n := by
          simp [weightedFinsuppCount, mul_comm]
    _ = ∑ f : WeightedFinsupp w n, f.1.weight w := by
      refine Finset.sum_congr rfl ?_
      intro f _
      exact f.2.symm
    _ = ∑ f : WeightedFinsupp w n,
        ∑ s : σ, f.1 s * w s := by
      apply Finset.sum_congr rfl
      intro f _
      simp [Finsupp.weight_apply, Finsupp.sum_fintype,
        mul_comm]
    _ = ∑ s : σ, w s * ∑ f : WeightedFinsupp w n, f.1 s := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro s _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro f _
      simp [mul_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro s _
      rw [weighted_finsupp_count
        w n s]

abbrev RepeatedWeightIndex
    (w : σ → ℕ) [PositiveWeights w] (n : ℕ) :=
  Σ s : σ, PositiveCopies w s n

abbrev DividingWeightIndex
    (w : σ → ℕ) (r : ℕ) :=
  {s : σ // w s ∣ r}

private def repeatedWeightDividing
    (w : σ → ℕ) [PositiveWeights w]
    (n r : ℕ)
    (x : {x : RepeatedWeightIndex w n //
      x.2.1 * w x.1 = r}) :
    DividingWeightIndex w r :=
  ⟨x.1.1, ⟨x.1.2.1, by
    simpa [mul_comm] using x.2.symm⟩⟩

omit [Fintype σ] [DecidableEq σ] in
private theorem repeated_dividing_bijective
    (w : σ → ℕ) [PositiveWeights w]
    (n r : ℕ) (hrpos : 0 < r) (hrn : r ≤ n) :
    Function.Bijective
      (repeatedWeightDividing w n r) := by
  constructor
  · intro x y hxy
    have hs : x.1.1 = y.1.1 :=
      congrArg
        (fun z : DividingWeightIndex w r => z.1)
        hxy
    apply Subtype.ext
    apply Sigma.ext hs
    apply
      (Subtype.heq_iff_coe_eq
        (fun k : ℕ => by rw [hs])).2
    exact Nat.mul_right_cancel
      (Nat.zero_lt_of_ne_zero
        (PositiveWeights.ne_zero x.1.1))
      (x.2.trans (by simpa [hs] using y.2.symm))
  · intro s
    have hwpos : 0 < w s.1 :=
      Nat.zero_lt_of_ne_zero (PositiveWeights.ne_zero s.1)
    have hwle : w s.1 ≤ r :=
      Nat.le_of_dvd hrpos s.2
    have hkpos : 0 < r / w s.1 :=
      Nat.div_pos hwle hwpos
    have hmul : r / w s.1 * w s.1 = r :=
      Nat.div_mul_cancel s.2
    refine
      ⟨⟨⟨s.1,
          ⟨r / w s.1, hkpos, hmul.le.trans hrn⟩⟩,
        hmul⟩, ?_⟩
    apply Subtype.ext
    rfl

noncomputable def repeatedFiberDividing
    (w : σ → ℕ) [PositiveWeights w]
    (n r : ℕ) (hrpos : 0 < r) (hrn : r ≤ n) :
    {x : RepeatedWeightIndex w n //
      x.2.1 * w x.1 = r} ≃
      DividingWeightIndex w r :=
  Equiv.ofBijective
    (repeatedWeightDividing w n r)
    (repeated_dividing_bijective
      w n r hrpos hrn)

omit [DecidableEq σ] in
theorem repeated_sum_grouped
    (w : σ → ℕ) [PositiveWeights w]
    (F : ℕ → ℕ) (n : ℕ) :
    ∑ s : σ, w s *
        ∑ k : PositiveCopies w s n,
          F (n - k.1 * w s) =
      ∑ r ∈ Finset.Icc 1 n,
        (∑ s : DividingWeightIndex w r, w s.1) *
          F (n - r) := by
  classical
  let repeatedWeight : RepeatedWeightIndex w n → ℕ :=
    fun x => x.2.1 * w x.1
  have hrepeatedWeight_mem :
      ∀ x : RepeatedWeightIndex w n,
        repeatedWeight x ∈ Finset.Icc 1 n := by
    intro x
    rw [Finset.mem_Icc]
    constructor
    · exact Nat.one_le_iff_ne_zero.mpr
        (mul_ne_zero
          (Nat.ne_of_gt x.2.2.1)
          (PositiveWeights.ne_zero x.1))
    · exact x.2.2.2
  calc
    ∑ s : σ, w s *
        ∑ k : PositiveCopies w s n,
          F (n - k.1 * w s) =
        ∑ s : σ,
          ∑ k : PositiveCopies w s n,
            w s * F (n - k.1 * w s) := by
      apply Finset.sum_congr rfl
      intro s _
      rw [Finset.mul_sum]
    _ = ∑ x : RepeatedWeightIndex w n,
        w x.1 * F (n - repeatedWeight x) := by
      simpa [repeatedWeight] using
        (Fintype.sum_sigma'
          (fun s (k : PositiveCopies w s n) =>
            w s * F (n - k.1 * w s))).symm
    _ = ∑ r ∈ Finset.Icc 1 n,
        ∑ x ∈ Finset.univ with repeatedWeight x = r,
          w x.1 * F (n - repeatedWeight x) := by
      symm
      exact Finset.sum_fiberwise_of_maps_to
        (s := Finset.univ)
        (t := Finset.Icc 1 n)
        (fun x _ => hrepeatedWeight_mem x)
        (fun x => w x.1 * F (n - repeatedWeight x))
    _ = ∑ r ∈ Finset.Icc 1 n,
        (∑ x ∈ Finset.univ with repeatedWeight x = r,
          w x.1) * F (n - r) := by
      apply Finset.sum_congr rfl
      intro r hr
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro x hx
      have hxweight : repeatedWeight x = r := by
        simpa using hx
      rw [hxweight]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro r hr
      have hr' : 1 ≤ r ∧ r ≤ n :=
        Finset.mem_Icc.mp hr
      have hrpos : 0 < r :=
        Nat.zero_lt_of_lt hr'.1
      congr 1
      rw [Finset.sum_subtype
        (p := fun x : RepeatedWeightIndex w n =>
          repeatedWeight x = r)
        (s := Finset.univ.filter
          (fun x : RepeatedWeightIndex w n =>
            repeatedWeight x = r))
        (by simp)
        (fun x : RepeatedWeightIndex w n => w x.1)]
      exact Fintype.sum_equiv
        (repeatedFiberDividing
          w n r hrpos hr'.2)
        (fun x => w x.1.1)
        (fun s => w s.1)
        (fun _ => rfl)

omit [DecidableEq σ] in
theorem dividing_sum_pow
    (w : σ → ℕ) [PositiveWeights w]
    (q n : ℕ)
    (hcount : ∀ m ≤ n,
      weightedFinsuppCount w m = q ^ m) :
    ∀ r, 0 < r → r ≤ n →
      (∑ s : DividingWeightIndex w r, w s.1) =
        q ^ r := by
  classical
  intro r
  induction r using Nat.strong_induction_on with
  | h r ih =>
      intro hrpos hrn
      obtain ⟨m, rfl⟩ :=
        Nat.exists_eq_succ_of_ne_zero
          (Nat.ne_of_gt hrpos)
      let coefficient : ℕ → ℕ :=
        fun k =>
          ∑ s : DividingWeightIndex w k, w s.1
      have hrec :=
        weighted_finsupp_recurrence w (m + 1)
      rw [repeated_sum_grouped] at hrec
      have hrec' :
          (m + 1) * q ^ (m + 1) =
            ∑ k ∈ Finset.Icc 1 (m + 1),
              coefficient k * q ^ (m + 1 - k) := by
        rw [← hcount (m + 1) hrn]
        calc
          (m + 1) *
              weightedFinsuppCount w (m + 1) =
              ∑ k ∈ Finset.Icc 1 (m + 1),
                coefficient k *
                  weightedFinsuppCount w (m + 1 - k) :=
            hrec
          _ = _ := by
            apply Finset.sum_congr rfl
            intro k _hk
            rw [hcount (m + 1 - k)
              ((Nat.sub_le _ _).trans hrn)]
      have hlower :
          (∑ k ∈ Finset.Icc 1 m,
              coefficient k * q ^ (m + 1 - k)) =
            m * q ^ (m + 1) := by
        calc
          (∑ k ∈ Finset.Icc 1 m,
              coefficient k * q ^ (m + 1 - k)) =
              ∑ _k ∈ Finset.Icc 1 m, q ^ (m + 1) := by
            apply Finset.sum_congr rfl
            intro k hk
            have hk' : 1 ≤ k ∧ k ≤ m :=
              Finset.mem_Icc.mp hk
            have hcoefficient :
                coefficient k = q ^ k := by
              dsimp only [coefficient]
              exact ih k (by omega) (by omega) (by omega)
            rw [hcoefficient]
            rw [← pow_add]
            congr 1
            omega
          _ = m * q ^ (m + 1) := by
            simp [Nat.card_Icc]
      rw [Finset.sum_Icc_succ_top (Nat.succ_pos m)] at hrec'
      rw [hlower] at hrec'
      simp only [Nat.sub_self, pow_zero, mul_one] at hrec'
      rw [Nat.succ_mul] at hrec'
      change coefficient (m + 1) = q ^ (m + 1)
      exact (Nat.add_left_cancel hrec').symm

end HallWitt
end Submission

namespace Submission
namespace HallTree

variable {α : Type} [Fintype α] [DecidableEq α] [Encodable α]

abbrev BoundedBasicTree (n : ℕ) :=
  {t : HallTree α // t.IsBasic ∧ t.weight ≤ n}

noncomputable instance boundedTreeFintype (n : ℕ) :
    Fintype (BoundedBasicTree (α := α) n) :=
  Set.Finite.fintype
    ((finite_set_weight (α := α) n).subset
      (fun _ h => h.2))

instance boundedTreeWeights (n : ℕ) :
    HallWitt.PositiveWeights
      (fun t : BoundedBasicTree (α := α) n => t.1.weight) where
  ne_zero t := Nat.ne_of_gt t.1.weight_pos

private theorem sum_multiset_weight
    {σ : Type}
    (w : σ → ℕ) (f : σ →₀ ℕ) :
    (f.toMultiset.map w).sum = f.weight w := by
  classical
  induction f using Finsupp.induction with
  | zero =>
      simp
  | single_add a b f _ha _hb ih =>
      rw [Finsupp.toMultiset_add, Finsupp.toMultiset_single,
        Multiset.map_add, Multiset.sum_add, map_add,
        Finsupp.weight_single]
      rw [Multiset.map_nsmul, Multiset.sum_nsmul]
      simp [ih]

private def boundedFinsuppSequence
    (n m : ℕ)
    (f : HallWitt.WeightedFinsupp
      (fun t : BoundedBasicTree (α := α) n => t.1.weight) m) :
    {sequence : List (HallTree α) //
      OrderedStandardSequence m sequence} := by
  let sorted :=
    f.1.toMultiset.sort (· ≤ ·)
  let sequence := sorted.map
    (fun t : BoundedBasicTree (α := α) n => t.1)
  have hordered : IsOrderedSequence sequence := by
    change (sorted.map
      (fun t : BoundedBasicTree (α := α) n => t.1)).Pairwise
        (· ≤ ·)
    rw [List.pairwise_map]
    exact
      (Multiset.pairwise_sort
        (s := f.1.toMultiset) (r := (· ≤ ·))).imp
          (fun {_ _} h => h)
  have hbasic : ∀ t ∈ sequence, t.IsBasic := by
    intro t ht
    simp only [sequence, List.mem_map] at ht
    rcases ht with ⟨u, _hu, rfl⟩
    exact u.2.1
  refine ⟨sequence,
    ⟨standard_sequence_forall
      hbasic hordered,
      hordered⟩,
    ?_⟩
  change (sequence.map weight).sum = m
  rw [← f.2]
  change
    ((sorted.map
      (fun t : BoundedBasicTree (α := α) n => t.1)).map weight).sum =
      f.1.weight
        (fun t : BoundedBasicTree (α := α) n => t.1.weight)
  rw [← sum_multiset_weight]
  have hsort :
      (↑sorted : Multiset
        (BoundedBasicTree (α := α) n)) =
        f.1.toMultiset :=
    Multiset.sort_eq _ _
  have hmap :=
    congrArg
      (Multiset.map
        (fun t : BoundedBasicTree (α := α) n => t.1.weight))
      hsort
  simpa [sequence, List.map_map, Function.comp_def] using
    congrArg Multiset.sum hmap

private def sequenceTreeFinsupp
    (n m : ℕ) (hmn : m ≤ n)
    (sequence :
      {sequence : List (HallTree α) //
        OrderedStandardSequence m sequence}) :
    HallWitt.WeightedFinsupp
      (fun t : BoundedBasicTree (α := α) n => t.1.weight) m := by
  let bounded : List (BoundedBasicTree (α := α) n) :=
    sequence.1.attach.map fun t =>
      ⟨t.1,
        sequence.2.1.1.mem_isBasic t.2,
        (weight_standard_sequence t.2).trans
          (sequence.2.2.trans_le hmn)⟩
  refine ⟨Multiset.toFinsupp bounded, ?_⟩
  rw [← sum_multiset_weight]
  rw [Multiset.toFinsupp_toMultiset]
  change (bounded.map
    (fun t : BoundedBasicTree (α := α) n => t.1.weight)).sum = m
  simpa [bounded, standardSequenceWeight] using sequence.2.2

omit [Fintype α] [DecidableEq α] in
private theorem tree_finsupp_bijective
    (n m : ℕ) (hmn : m ≤ n) :
    Function.Bijective
      (boundedFinsuppSequence
        (α := α) n m) := by
  classical
  constructor
  · intro f g hfg
    apply Subtype.ext
    apply Multiset.toFinsupp.symm.injective
    have hsequence := congrArg Subtype.val hfg
    have hsorted :
        f.1.toMultiset.sort (· ≤ ·) =
          g.1.toMultiset.sort (· ≤ ·) := by
      apply
        (List.map_injective_iff.mpr
          (fun _ _ h => Subtype.ext h))
      simpa [boundedFinsuppSequence]
        using hsequence
    calc
      f.1.toMultiset =
          ↑(f.1.toMultiset.sort (· ≤ ·)) :=
        (Multiset.sort_eq _ _).symm
      _ = ↑(g.1.toMultiset.sort (· ≤ ·)) :=
        congrArg
          (fun l : List (BoundedBasicTree (α := α) n) =>
            (l : Multiset (BoundedBasicTree (α := α) n)))
          hsorted
      _ = g.1.toMultiset :=
        Multiset.sort_eq _ _
  · intro sequence
    let bounded : List (BoundedBasicTree (α := α) n) :=
      sequence.1.attach.map fun t =>
        ⟨t.1,
          sequence.2.1.1.mem_isBasic t.2,
          (weight_standard_sequence t.2).trans
            (sequence.2.2.trans_le hmn)⟩
    have hboundedOrdered : bounded.Pairwise (· ≤ ·) := by
      change
        (sequence.1.attach.map fun t =>
          (⟨t.1,
            sequence.2.1.1.mem_isBasic t.2,
            (weight_standard_sequence t.2).trans
              (sequence.2.2.trans_le hmn)⟩ :
            BoundedBasicTree (α := α) n)).Pairwise (· ≤ ·)
      rw [List.pairwise_map]
      change
        sequence.1.attach.Pairwise
          (fun a b => a.1 ≤ b.1)
      rw [← List.pairwise_map]
      simpa using sequence.2.1.2
    have hsortBounded :
        (↑bounded : Multiset
          (BoundedBasicTree (α := α) n)).sort (· ≤ ·) =
          bounded := by
      apply List.Perm.eq_of_pairwise'
        (Multiset.pairwise_sort _ _) hboundedOrdered
      exact
        Multiset.coe_eq_coe.mp
          (Multiset.sort_eq _ _)
    refine
      ⟨sequenceTreeFinsupp
        (α := α) n m hmn sequence, ?_⟩
    apply Subtype.ext
    change
      ((Multiset.toFinsupp (↑bounded :
        Multiset (BoundedBasicTree (α := α) n))).toMultiset.sort
          (· ≤ ·)).map
            (fun t : BoundedBasicTree (α := α) n => t.1) =
        sequence.1
    rw [Multiset.toFinsupp_toMultiset, hsortBounded]
    simp [bounded]

private noncomputable def treeFinsuppSequence
    (n m : ℕ) (hmn : m ≤ n) :
    HallWitt.WeightedFinsupp
        (fun t : BoundedBasicTree (α := α) n => t.1.weight) m ≃
      {sequence : List (HallTree α) //
        OrderedStandardSequence m sequence} :=
  Equiv.ofBijective
    (boundedFinsuppSequence
      (α := α) n m)
    (tree_finsupp_bijective
      (α := α) n m hmn)

omit [DecidableEq α] in
theorem tree_weighted_finsupp
    (n m : ℕ) (hmn : m ≤ n) :
    HallWitt.weightedFinsuppCount
        (fun t : BoundedBasicTree (α := α) n => t.1.weight) m =
      Fintype.card α ^ m := by
  classical
  calc
    HallWitt.weightedFinsuppCount
        (fun t : BoundedBasicTree (α := α) n => t.1.weight) m =
        Nat.card
          (HallWitt.WeightedFinsupp
            (fun t : BoundedBasicTree (α := α) n => t.1.weight) m) := by
      simp [HallWitt.weightedFinsuppCount,
        Nat.card_eq_fintype_card]
    _ = Nat.card
        {sequence : List (HallTree α) //
          OrderedStandardSequence m sequence} :=
      Nat.card_congr
        (treeFinsuppSequence
          (α := α) n m hmn)
    _ = Nat.card
        (Submission.TBluepr.AssociativeWordsLength α m) :=
      HallTree.foliageFactorizationInput.formCodingInput
        |>.cardinalityInput |>.card_eq m
    _ = Nat.card (List.Vector α m) :=
      Nat.card_congr
        (Submission.TBluepr.associativeVectorEquiv α m)
    _ = Fintype.card α ^ m := by
      rw [Nat.card_eq_fintype_card, card_vector]

private noncomputable def dividingTreeFiber
    (n d : ℕ) (hn : 0 < n) (hd : d ∣ n) :
    {s : HallWitt.DividingWeightIndex
        (fun t : BoundedBasicTree (α := α) n => t.1.weight) n //
      s.1.1.weight = d} ≃
      BasicIndex (α := α) d where
  toFun s :=
    (basicIndexEquiv (α := α) d).symm
      ⟨s.1.1.1, s.1.1.2.1, s.2⟩
  invFun i :=
    ⟨⟨⟨indexedBasicTree i,
          indexed_tree i,
          (Nat.le_of_dvd hn
            (by simpa [indexed_tree_weight] using hd))⟩,
        by simpa [indexed_tree_weight] using hd⟩,
      indexed_tree_weight i⟩
  left_inv s := by
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    change
      indexedBasicTree
          ((basicIndexEquiv (α := α) d).symm
            ⟨s.1.1.1, s.1.1.2.1, s.2⟩) =
        s.1.1.1
    have h :=
      (basicIndexEquiv (α := α) d).apply_symm_apply
        ⟨s.1.1.1, s.1.1.2.1, s.2⟩
    exact Subtype.ext_iff.mp h
  right_inv i := by
    exact (basicIndexEquiv (α := α) d).symm_apply_apply i

/-- The Hall coefficient identity: words of length `n` are uniquely products
of basic commutators, so the divisor-weighted Hall numbers sum to `|α|^n`. -/
theorem sum_divisors_pow
    (n : ℕ) (hn : 0 < n) :
    n.divisors.sum
        (fun d => d * Fintype.card (BasicIndex (α := α) d)) =
      Fintype.card α ^ n := by
  let w :
      BoundedBasicTree (α := α) n → ℕ :=
    fun t => t.1.weight
  have hdividing :
      (∑ s : HallWitt.DividingWeightIndex w n, w s.1) =
        Fintype.card α ^ n := by
    exact HallWitt.dividing_sum_pow
      w (Fintype.card α) n
      (fun m hm =>
        tree_weighted_finsupp
          (α := α) n m hm)
      n hn le_rfl
  have hmaps :
      ∀ s : HallWitt.DividingWeightIndex w n,
        w s.1 ∈ n.divisors := by
    intro s
    exact Nat.mem_divisors.mpr ⟨s.2, Nat.ne_of_gt hn⟩
  calc
    n.divisors.sum
        (fun d => d * Fintype.card (BasicIndex (α := α) d)) =
        ∑ d ∈ n.divisors,
          ∑ s ∈
              (Finset.univ :
                Finset (HallWitt.DividingWeightIndex w n)) with
            w s.1 = d, w s.1 := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [Finset.sum_subtype
        (p := fun s : HallWitt.DividingWeightIndex w n =>
          w s.1 = d)
        (s := Finset.univ.filter
          (fun s : HallWitt.DividingWeightIndex w n =>
            w s.1 = d))
        (by simp)
        (fun s : HallWitt.DividingWeightIndex w n => w s.1)]
      · symm
        simpa [mul_comm] using
          (Fintype.sum_equiv
            (dividingTreeFiber
              (α := α) n d hn (Nat.mem_divisors.mp hd).1)
            (fun s => w s.1.1)
            (fun _i : BasicIndex (α := α) d => d)
            (fun s => s.2))
    _ = ∑ s : HallWitt.DividingWeightIndex w n, w s.1 := by
      exact Finset.sum_fiberwise_of_maps_to
        (s := Finset.univ)
        (t := n.divisors)
        (fun s _ => hmaps s)
        (fun s : HallWitt.DividingWeightIndex w n => w s.1)
    _ = Fintype.card α ^ n :=
      hdividing

/-- Integral Witt formula for the cardinality of the weight-`n` Hall basis. -/
theorem card_witt_numerator
    (n : ℕ) (hn : 0 < n) :
    (n : ℤ) *
        (Fintype.card (BasicIndex (α := α) n) : ℤ) =
      Edmonton.wittNumerator (Fintype.card α) n := by
  refine Edmonton.witt_numerator_count
    (Fintype.card α)
    (fun d => Fintype.card (BasicIndex (α := α) d))
    ?_ n hn
  intro w hw
  exact_mod_cast sum_divisors_pow
    (α := α) w hw

/-- Rational form of Witt's formula for the number of weight-`n` Hall basic
commutators. -/
theorem card_witt_formula
    (n : ℕ) (hn : 0 < n) :
    (Fintype.card (BasicIndex (α := α) n) : ℚ) =
      n.divisors.sum
          (fun d : ℕ =>
            (ArithmeticFunction.moebius d : ℚ) *
              (Fintype.card α : ℚ) ^ (n / d)) /
        (n : ℚ) := by
  refine Edmonton.wittFormula
    (Fintype.card α)
    (fun d => Fintype.card (BasicIndex (α := α) d))
    ?_ n hn
  intro w hw
  exact_mod_cast sum_divisors_pow
    (α := α) w hw

end HallTree
end Submission
