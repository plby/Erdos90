import Towers.Group.GSBookkeeping

/-!
# Small certificate input adapters for GS bookkeeping

This module contains thin wrappers around `GSBookkeeping` for certificate data in
forms convenient for external searches (currently finite lists of bucket bounds).
The core mathematics remains in `GSBookkeeping`.
-/

namespace Towers
namespace FPres

noncomputable section

/-- Interpret a finite list as a depth-indexed natural upper-bound function,
using zero beyond the end of the list. -/
def listDepthBound (xs : List ℕ) (q : ℕ) : ℕ := xs.getD q 0

@[simp] theorem depth_bound_nil (q : ℕ) : listDepthBound [] q = 0 := by
  simp [listDepthBound]

@[simp] theorem bound_cons_zero (x : ℕ) (xs : List ℕ) :
    listDepthBound (x :: xs) 0 = x := by
  simp [listDepthBound]

@[simp] theorem list_cons_succ (x : ℕ) (xs : List ℕ) (q : ℕ) :
    listDepthBound (x :: xs) (q + 1) = listDepthBound xs q := by
  simp [listDepthBound]

/-- The zeroth entry of a singleton natural-bound list is its value. -/
@[simp] theorem bound_singleton_zero (x : ℕ) :
    listDepthBound [x] 0 = x := by
  simp [listDepthBound]

/-- A singleton natural-bound list is zero in every positive depth. -/
@[simp] theorem list_singleton_succ (x q : ℕ) :
    listDepthBound [x] (q + 1) = 0 := by
  simp [listDepthBound]

/-- First entry of a two-entry natural-bound list. -/
@[simp] theorem bound_pair_zero (x y : ℕ) :
    listDepthBound [x, y] 0 = x := by
  simp [listDepthBound]

/-- Second entry of a two-entry natural-bound list. -/
@[simp] theorem list_bound_pair (x y : ℕ) :
    listDepthBound [x, y] 1 = y := by
  simp [listDepthBound]

/-- A two-entry natural-bound list is zero from depth two onward. -/
@[simp] theorem list_pair_succ (x y q : ℕ) :
    listDepthBound [x, y] (q + 2) = 0 := by
  cases q <;> simp [listDepthBound]

/-- Scaling a natural-bound list scales its pointwise depth-bound sequence. -/
@[simp] theorem depth_bound_left (a : ℕ) (xs : List ℕ) (q : ℕ) :
    listDepthBound (xs.map (fun z : ℕ => a * z)) q = a * listDepthBound xs q := by
  induction xs generalizing q with
  | nil => simp
  | cons x xs ih =>
      cases q with
      | zero => simp [listDepthBound]
      | succ q => simpa using ih q

/-- Right-scaling a natural-bound list scales its pointwise depth-bound sequence. -/
@[simp] theorem depth_bound_right (xs : List ℕ) (a : ℕ) (q : ℕ) :
    listDepthBound (xs.map (fun z : ℕ => z * a)) q = listDepthBound xs q * a := by
  induction xs generalizing q with
  | nil => simp
  | cons x xs ih =>
      cases q with
      | zero => simp [listDepthBound]
      | succ q => simpa using ih q

/-- Pointwise addition of equal-length natural bound lists is read pointwise. -/
@[simp] theorem bound_zip_length
    {xs ys : List ℕ} (h : xs.length = ys.length) (q : ℕ) :
    listDepthBound (List.zipWith (fun a b : ℕ => a + b) xs ys) q =
      listDepthBound xs q + listDepthBound ys q := by
  induction xs generalizing ys q with
  | nil =>
      cases ys with
      | nil => simp [listDepthBound]
      | cons y ys => simp at h
  | cons x xs ih =>
      cases ys with
      | nil => simp at h
      | cons y ys =>
          have hlen : xs.length = ys.length := by simpa using h
          cases q with
          | zero => simp [listDepthBound]
          | succ q => simpa using ih hlen q

/-- List depth bounds vanish beyond the supplied list. -/
theorem depth_bound_length (xs : List ℕ) {q : ℕ}
    (h : xs.length ≤ q) : listDepthBound xs q = 0 := by
  rw [listDepthBound, List.getD_eq_getElem?_getD, List.getElem?_eq_none]
  · rfl
  · omega

/-- Appending a tail does not change list depth bounds before the original length. -/
theorem list_append_left (xs ys : List ℕ) {q : ℕ} (h : q < xs.length) :
    listDepthBound (xs ++ ys) q = listDepthBound xs q := by
  rw [listDepthBound, listDepthBound, List.getD_eq_getElem?_getD,
    List.getD_eq_getElem?_getD, List.getElem?_append_left h]

/-- Past the original length, an appended tail is read with shifted index. -/
theorem depth_bound_append (xs ys : List ℕ) {q : ℕ} (h : xs.length ≤ q) :
    listDepthBound (xs ++ ys) q = listDepthBound ys (q - xs.length) := by
  rw [listDepthBound, listDepthBound, List.getD_eq_getElem?_getD,
    List.getD_eq_getElem?_getD, List.getElem?_append_right h]

/-- Dropping a prefix shifts natural list depth bounds by the drop length. -/
@[simp] theorem depth_bound_drop (xs : List ℕ) (k q : ℕ) :
    listDepthBound (xs.drop k) q = listDepthBound xs (k + q) := by
  rw [listDepthBound, listDepthBound, List.getD_eq_getElem?_getD,
    List.getD_eq_getElem?_getD, List.getElem?_drop]

/-- Dropping exactly a prepended zero block recovers the original natural depth bounds. -/
@[simp] theorem bound_drop_replicate
    (k : ℕ) (xs : List ℕ) (q : ℕ) :
    listDepthBound ((List.replicate k 0 ++ xs).drop k) q =
      listDepthBound xs q := by
  simp

/-- Taking at least the whole natural-bound list does not change its depth function. -/
@[simp] theorem list_take_length (xs : List ℕ) {N q : ℕ}
    (h : xs.length ≤ N) : listDepthBound (xs.take N) q = listDepthBound xs q := by
  rw [List.take_of_length_le h]

/-- Taking exactly the whole natural-bound list does not change its depth function. -/
@[simp] theorem depth_take_length (xs : List ℕ) (q : ℕ) :
    listDepthBound (xs.take xs.length) q = listDepthBound xs q := by
  exact list_take_length xs (q := q) le_rfl

/-- Taking enough entries preserves a natural list depth bound at covered indices. -/
theorem depth_bound_take (xs : List ℕ) {M q : ℕ} (hq : q ≤ M) :
    listDepthBound (xs.take (M + 1)) q = listDepthBound xs q := by
  rw [listDepthBound, listDepthBound, List.getD_eq_getElem?_getD,
    List.getD_eq_getElem?_getD, List.getElem?_take]
  have hlt : q < M + 1 := by omega
  simp [hlt]

/-- At the splice point of an append, reading starts at the tail's zeroth entry. -/
@[simp] theorem list_append_length (xs ys : List ℕ) :
    listDepthBound (xs ++ ys) xs.length = listDepthBound ys 0 := by
  simpa using (depth_bound_append xs ys (q := xs.length) (le_rfl))

/-- Reading an appended tail at an offset from the splice point. -/
@[simp] theorem bound_append_length (xs ys : List ℕ) (q : ℕ) :
    listDepthBound (xs ++ ys) (xs.length + q) = listDepthBound ys q := by
  have h := depth_bound_append xs ys (q := xs.length + q) (Nat.le_add_right _ _)
  simpa [Nat.add_sub_cancel_left] using h

/-- Inside a replicated natural-bound list, every entry is the replicated value. -/
theorem list_depth_replicate (a : ℕ) {n q : ℕ} (h : q < n) :
    listDepthBound (List.replicate n a) q = a := by
  rw [listDepthBound, List.getD_eq_getElem?_getD, List.getElem?_replicate]
  simp [h]

/-- Beyond a replicated natural-bound list, entries are zero. -/
theorem list_bound_replicate (a : ℕ) {n q : ℕ} (h : n ≤ q) :
    listDepthBound (List.replicate n a) q = 0 := by
  exact depth_bound_length _ (by simpa using h)


/-- A replicated zero natural-bound list is pointwise zero. -/
@[simp] theorem list_replicate_zero (n q : ℕ) :
    listDepthBound (List.replicate n 0) q = 0 := by
  by_cases h : q < n
  · simpa using (list_depth_replicate 0 (n := n) (q := q) h)
  · exact list_bound_replicate 0 (n := n) (q := q) (by omega)

/-- Taking exactly a prepended zero block gives a pointwise-zero natural bound. -/
@[simp] theorem bound_take_replicate
    (k : ℕ) (xs : List ℕ) (q : ℕ) :
    listDepthBound ((List.replicate k 0 ++ xs).take k) q = 0 := by
  have htake :
      (List.replicate k (0 : ℕ) ++ xs).take k = List.replicate k 0 := by
    simp
  rw [htake]
  exact list_replicate_zero k q

/-- Appending zero padding to a natural-bound list does not change its depth function. -/
@[simp] theorem append_replicate_zero (xs : List ℕ) (n q : ℕ) :
    listDepthBound (xs ++ List.replicate n 0) q = listDepthBound xs q := by
  by_cases h : q < xs.length
  · exact list_append_left xs (List.replicate n 0) h
  · have hle : xs.length ≤ q := by omega
    rw [depth_bound_append xs (List.replicate n 0) hle]
    rw [depth_bound_length xs hle]
    exact list_replicate_zero n (q - xs.length)

/-- Prepending zero padding shifts a natural-bound list to the right. -/
@[simp] theorem list_replicate_append (k : ℕ) (xs : List ℕ) (q : ℕ) :
    listDepthBound (List.replicate k 0 ++ xs) q =
      if k ≤ q then listDepthBound xs (q - k) else 0 := by
  by_cases h : k ≤ q
  · rw [depth_bound_append (List.replicate k 0) xs (by simpa using h)]
    simp [h]
  · have hlt : q < (List.replicate k (0 : ℕ)).length := by
      simpa using (Nat.lt_of_not_ge h)
    rw [list_append_left (List.replicate k 0) xs hlt]
    simp [h, list_replicate_zero]

/-- A list-backed natural sequence has finite support, coarsely bounded by its length. -/
theorem bound_seq_length (xs : List ℕ) :
    SSBound (fun q => listDepthBound xs q) xs.length := by
  intro q hq
  exact depth_bound_length xs (by omega)

/-- A sharper predecessor support bound for a list-backed natural sequence.  This form is
convenient when summing through the last possible nonzero index. -/
theorem bound_seq_pred (xs : List ℕ) :
    SSBound (fun q => listDepthBound xs q) (xs.length - 1) := by
  intro q hq
  exact depth_bound_length xs (by omega)

/-- Prepending zero padding shifts the sharp predecessor support bound. -/
theorem replicate_append_pred
    (k : ℕ) (xs : List ℕ) :
    SSBound
      (fun q => listDepthBound (List.replicate k 0 ++ xs) q)
      (xs.length - 1 + k) := by
  have hb := (bound_seq_pred xs).shiftRight k
  refine hb.congr ?_
  intro q
  simp [list_replicate_append]

/-- Appending zero padding does not affect any natural support-bound assertion. -/
theorem append_replicate_seq
    (xs : List ℕ) (k B : ℕ) :
    SSBound (fun q => listDepthBound (xs ++ List.replicate k 0) q) B ↔
      SSBound (fun q => listDepthBound xs q) B := by
  constructor
  · intro h
    refine h.congr ?_
    intro q
    simp [append_replicate_zero]
  · intro h
    refine h.congr ?_
    intro q
    simp [append_replicate_zero]

/-- Multiplying every natural entry on the left by a nonzero scalar does not change
support bounds. -/
theorem depth_seq_support
    (a : ℕ) (ha : a ≠ 0) (xs : List ℕ) (B : ℕ) :
    SSBound (fun q => listDepthBound (xs.map (fun z : ℕ => a * z)) q) B ↔
      SSBound (fun q => listDepthBound xs q) B := by
  constructor
  · intro h q hq
    have hz := h q hq
    change listDepthBound (xs.map (fun z : ℕ => a * z)) q = 0 at hz
    rw [depth_bound_left] at hz
    rcases Nat.mul_eq_zero.mp hz with hz | hz
    · exact False.elim (ha hz)
    · exact hz
  · intro h q hq
    simp [h q hq]

/-- Multiplying every natural entry on the right by a nonzero scalar does not change
support bounds. -/
theorem list_seq_support
    (xs : List ℕ) (a : ℕ) (ha : a ≠ 0) (B : ℕ) :
    SSBound (fun q => listDepthBound (xs.map (fun z : ℕ => z * a)) q) B ↔
      SSBound (fun q => listDepthBound xs q) B := by
  constructor
  · intro h q hq
    have hz := h q hq
    change listDepthBound (xs.map (fun z : ℕ => z * a)) q = 0 at hz
    rw [depth_bound_right] at hz
    rcases Nat.mul_eq_zero.mp hz with hz | hz
    · exact hz
    · exact False.elim (ha hz)
  · intro h q hq
    simp [h q hq]

/-- Prefix sums of a natural list-backed sequence stabilize after the last possible
nonzero entry. -/
theorem sum_bound_pred (xs : List ℕ) {M N : ℕ}
    (hM : xs.length - 1 ≤ M) (hMN : M ≤ N) :
    (∑ q ∈ Finset.range (N + 1), listDepthBound xs q) =
      ∑ q ∈ Finset.range (M + 1), listDepthBound xs q := by
  exact range_support_bound
    (bound_seq_pred xs) hM hMN

/-- Denominator-cleared relator sum computed from a finite list of bucket bounds. -/
def clearedGSList (M : ℕ) (xs : List ℕ) (num den : ℕ) : ℤ :=
  ∑ q ∈ Finset.range (M + 1),
    (listDepthBound xs q : ℤ) * (num : ℤ) ^ q * (den : ℤ) ^ (M + 1 - q)

/-- Cons recurrence for cleared list relator sums: the head contributes in degree zero,
and the tail is shifted by one power of `num`. -/
theorem cleared_cons_succ
    (M x : ℕ) (xs : List ℕ) (num den : ℕ) :
    clearedGSList (M + 1) (x :: xs) num den =
      (x : ℤ) * (den : ℤ) ^ (M + 2) +
        (num : ℤ) * clearedGSList M xs num den := by
  unfold clearedGSList
  rw [Finset.sum_range_succ' (fun q =>
    (listDepthBound (x :: xs) q : ℤ) * (num : ℤ) ^ q *
      (den : ℤ) ^ (M + 1 + 1 - q)) (M + 1)]
  have htail :
      (∑ q ∈ Finset.range (M + 1),
        (listDepthBound (x :: xs) (q + 1) : ℤ) * (num : ℤ) ^ (q + 1) *
          (den : ℤ) ^ (M + 1 + 1 - (q + 1))) =
        (num : ℤ) *
          ∑ q ∈ Finset.range (M + 1),
            (listDepthBound xs q : ℤ) * (num : ℤ) ^ q *
              (den : ℤ) ^ (M + 1 - q) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro q hq
    have hqle : q ≤ M := by
      have hlt : q < M + 1 := by simpa using hq
      omega
    have hsub : M + 1 + 1 - (q + 1) = M + 1 - q := by omega
    simp [list_cons_succ, hsub, pow_succ, mul_assoc, mul_left_comm, mul_comm]
  rw [htail]
  simp [bound_cons_zero, pow_zero]
  ring_nf
  congr 1
  congr 1
  apply Finset.sum_congr rfl
  intro q hq
  ring

@[simp] theorem cleared_gs_nil (M num den : ℕ) :
    clearedGSList M [] num den = 0 := by
  simp [clearedGSList, listDepthBound]


/-- A zero-filled bound list contributes no cleared relator mass. -/
@[simp] theorem cleared_replicate_zero
    (M n num den : ℕ) :
    clearedGSList M (List.replicate n 0) num den = 0 := by
  simp [clearedGSList]

/-- Degree-zero closed form for a list-backed cleared relator sum. -/
@[simp] theorem cleared_gs_relator (xs : List ℕ) (num den : ℕ) :
    clearedGSList 0 xs num den = (listDepthBound xs 0 : ℤ) * (den : ℤ) := by
  simp [clearedGSList]

/-- Closed form for a singleton list-backed cleared relator sum in any degree. -/
@[simp] theorem cleared_gs_singleton (M x num den : ℕ) :
    clearedGSList M [x] num den = (x : ℤ) * (den : ℤ) ^ (M + 1) := by
  unfold clearedGSList
  rw [Finset.sum_eq_single 0]
  · simp [listDepthBound]
  · intro b _ hb0
    rcases Nat.exists_eq_succ_of_ne_zero hb0 with ⟨k, rfl⟩
    simp [listDepthBound]
  · intro h0
    simp at h0

/-- Degree-one closed form for a list-backed cleared relator sum. -/
theorem cleared_gs_sum (xs : List ℕ) (num den : ℕ) :
    clearedGSList 1 xs num den =
      (listDepthBound xs 0 : ℤ) * (den : ℤ) ^ 2 +
        (listDepthBound xs 1 : ℤ) * (num : ℤ) * (den : ℤ) := by
  simp [clearedGSList, Finset.sum_range_succ]

/-- Degree-two closed form for a list-backed cleared relator sum. -/
theorem cleared_gs_two (xs : List ℕ) (num den : ℕ) :
    clearedGSList 2 xs num den =
      (listDepthBound xs 0 : ℤ) * (den : ℤ) ^ 3 +
        (listDepthBound xs 1 : ℤ) * (num : ℤ) * (den : ℤ) ^ 2 +
          (listDepthBound xs 2 : ℤ) * (num : ℤ) ^ 2 * (den : ℤ) := by
  simp [clearedGSList, Finset.sum_range_succ]

/-- Degree-three closed form for a list-backed cleared relator sum. -/
theorem cleared_gs_three (xs : List ℕ) (num den : ℕ) :
    clearedGSList 3 xs num den =
      (listDepthBound xs 0 : ℤ) * (den : ℤ) ^ 4 +
        (listDepthBound xs 1 : ℤ) * (num : ℤ) * (den : ℤ) ^ 3 +
          (listDepthBound xs 2 : ℤ) * (num : ℤ) ^ 2 * (den : ℤ) ^ 2 +
            (listDepthBound xs 3 : ℤ) * (num : ℤ) ^ 3 * (den : ℤ) := by
  simp [clearedGSList, Finset.sum_range_succ]

/-- The list expression is just the generic relator sum for the induced bound function. -/
theorem cleared_gs_list (M : ℕ) (xs : List ℕ) (num den : ℕ) :
    clearedGSList M xs num den =
      clearedGSRelator M (fun q => listDepthBound xs q) num den := by
  rfl

/-- The cleared list relator sum only depends on entries through degree `M`. -/
theorem cleared_gs_congr (M : ℕ) {xs ys : List ℕ} (num den : ℕ)
    (h : ∀ q, q ≤ M → listDepthBound xs q = listDepthBound ys q) :
    clearedGSList M xs num den = clearedGSList M ys num den := by
  unfold clearedGSList
  apply Finset.sum_congr rfl
  intro q hq
  have hle : q ≤ M := by
    have hlt : q < M + 1 := by simpa using hq
    omega
  rw [h q hle]

/-- The cleared list relator sum is monotone in the sampled natural list entries. -/
theorem cleared_gs_mono {M : ℕ} {xs ys : List ℕ} {num den : ℕ}
    (h : ∀ q, q ≤ M → listDepthBound xs q ≤ listDepthBound ys q) :
    clearedGSList M xs num den ≤ clearedGSList M ys num den := by
  rw [cleared_gs_list, cleared_gs_list]
  exact cleared_mono_hist h

/-- Cleared list relator sums are nonnegative. -/
theorem cleared_gs_nonneg (M : ℕ) (xs : List ℕ) (num den : ℕ) :
    0 ≤ clearedGSList M xs num den := by
  unfold clearedGSList
  apply Finset.sum_nonneg
  intro q hq
  apply mul_nonneg
  · apply mul_nonneg
    · exact_mod_cast Nat.zero_le (listDepthBound xs q)
    · exact pow_nonneg (by exact_mod_cast Nat.zero_le num) q
  · exact pow_nonneg (by exact_mod_cast Nat.zero_le den) (M + 1 - q)

/-- Left-scaling a natural bound list scales its cleared relator sum. -/
@[simp] theorem cleared_gs_left
    (M a : ℕ) (xs : List ℕ) (num den : ℕ) :
    clearedGSList M (xs.map (fun z : ℕ => a * z)) num den =
      (a : ℤ) * clearedGSList M xs num den := by
  unfold clearedGSList
  simp only [depth_bound_left, Nat.cast_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q hq
  ring

/-- Right-scaling a natural bound list scales its cleared relator sum. -/
@[simp] theorem cleared_gs_right
    (M : ℕ) (xs : List ℕ) (a num den : ℕ) :
    clearedGSList M (xs.map (fun z : ℕ => z * a)) num den =
      clearedGSList M xs num den * (a : ℤ) := by
  unfold clearedGSList
  simp only [depth_bound_right, Nat.cast_mul]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro q hq
  ring

/-- Appending zero padding to a natural-bound list does not change its cleared sum. -/
@[simp] theorem cleared_gs_replicate
    (M n num den : ℕ) (xs : List ℕ) :
    clearedGSList M (xs ++ List.replicate n 0) num den =
      clearedGSList M xs num den := by
  apply cleared_gs_congr
  intro q hq
  exact append_replicate_zero xs n q

/-- Taking at least the whole natural-bound list does not change its cleared sum. -/
@[simp] theorem cleared_take_length
    (M num den N : ℕ) (xs : List ℕ) (h : xs.length ≤ N) :
    clearedGSList M (xs.take N) num den =
      clearedGSList M xs num den := by
  rw [List.take_of_length_le h]

/-- Truncating a natural-bound list after degree `M` does not change the cleared sum. -/
theorem cleared_gs_take (M : ℕ) (xs : List ℕ) (num den : ℕ) :
    clearedGSList M (xs.take (M + 1)) num den =
      clearedGSList M xs num den := by
  apply cleared_gs_congr
  intro q hq
  exact depth_bound_take xs hq

/-- Appending entries beyond degree `M` does not change the cleared list sum. -/
theorem cleared_gs_length (M : ℕ) (xs ys : List ℕ)
    (num den : ℕ) (hM : M < xs.length) :
    clearedGSList M (xs ++ ys) num den =
      clearedGSList M xs num den := by
  apply cleared_gs_congr
  intro q hq
  exact list_append_left xs ys (Nat.lt_of_le_of_lt hq hM)

/-- If the sampled degrees lie entirely in a prepended zero block, the cleared
list relator sum is zero. -/
theorem cleared_replicate_append
    (M k num den : ℕ) (xs : List ℕ) (hM : M < k) :
    clearedGSList M (List.replicate k 0 ++ xs) num den = 0 := by
  unfold clearedGSList
  apply Finset.sum_eq_zero
  intro q hq
  have hqle : q ≤ M := by
    have hlt : q < M + 1 := by simpa using hq
    omega
  have hkq : ¬ k ≤ q := by omega
  simp [list_replicate_append, hkq]

variable {p : ℕ} (FP : FPres p)

/-- Build a rational GS certificate from a finite list of per-depth multiplicity
upper bounds.  Entries beyond the list are interpreted as zero, so the hypothesis
explicitly requires the actual histogram to vanish/bound there. -/
def RGCert.multiplicity_bound_list
    [Fintype FP.toPresentation.Relator]
    (num den genLower : ℕ) (bounds : List ℕ)
    (hnum : 0 < num) (hden : 0 < den) (hproper : num < den)
    (hgen : genLower ≤ FP.generatorCount)
    (hhist : ∀ q, q ≤ FP.maxRelatorDepth →
      FP.relatorDepthMultiplicity q ≤ listDepthBound bounds q)
    (hneg : clearedGSBase genLower FP.maxRelatorDepth num den +
        clearedGSList FP.maxRelatorDepth bounds num den < 0) :
    FP.RGCert := by
  refine RGCert.ofMultiplicityBounds FP num den genLower
    (fun q => listDepthBound bounds q) hnum hden hproper hgen hhist ?_
  simpa [cleared_gs_list]
    using hneg

end
end FPres
end Towers

namespace Towers
namespace FPres

noncomputable section

/-- Interpret an integer list as a depth-indexed pointwise contribution bound,
using zero beyond the end. -/
def intDepthBound (xs : List ℤ) (q : ℕ) : ℤ := xs.getD q 0

@[simp] theorem int_bound_nil (q : ℕ) : intDepthBound [] q = 0 := by
  simp [intDepthBound]

@[simp] theorem int_bound_cons (x : ℤ) (xs : List ℤ) :
    intDepthBound (x :: xs) 0 = x := by
  simp [intDepthBound]

@[simp] theorem bound_cons_succ (x : ℤ) (xs : List ℤ) (q : ℕ) :
    intDepthBound (x :: xs) (q + 1) = intDepthBound xs q := by
  simp [intDepthBound]

/-- The zeroth entry of a singleton integer-bound list is its value. -/
@[simp] theorem int_bound_singleton (x : ℤ) :
    intDepthBound [x] 0 = x := by
  simp [intDepthBound]

/-- A singleton integer-bound list is zero in every positive depth. -/
@[simp] theorem bound_singleton_succ (x : ℤ) (q : ℕ) :
    intDepthBound [x] (q + 1) = 0 := by
  simp [intDepthBound]

/-- First entry of a two-entry integer-bound list. -/
@[simp] theorem int_bound_pair (x y : ℤ) :
    intDepthBound [x, y] 0 = x := by
  simp [intDepthBound]

/-- Second entry of a two-entry integer-bound list. -/
@[simp] theorem depth_bound_pair (x y : ℤ) :
    intDepthBound [x, y] 1 = y := by
  simp [intDepthBound]

/-- A two-entry integer-bound list is zero from depth two onward. -/
@[simp] theorem bound_pair_succ (x y : ℤ) (q : ℕ) :
    intDepthBound [x, y] (q + 2) = 0 := by
  cases q <;> simp [intDepthBound]

/-- Integer bounds obtained by casting a natural-bound list agree pointwise with
casting the natural depth bound. -/
@[simp] theorem int_bound_cast (xs : List ℕ) (q : ℕ) :
    intDepthBound (xs.map (fun n : ℕ => (n : ℤ))) q =
      (listDepthBound xs q : ℤ) := by
  induction xs generalizing q with
  | nil => simp
  | cons x xs ih =>
      cases q with
      | zero => simp
      | succ q => simpa using ih q

/-- Cast natural-bound lists give nonnegative integer bounds at every depth. -/
theorem int_cast_nonneg (xs : List ℕ) (q : ℕ) :
    0 ≤ intDepthBound (xs.map (fun n : ℕ => (n : ℤ))) q := by
  rw [int_bound_cast]
  exact Int.natCast_nonneg _

/-- The absolute value of a cast natural list-bound recovers the original natural bound. -/
@[simp] theorem nat_abs_cast (xs : List ℕ) (q : ℕ) :
    (intDepthBound (xs.map (fun n : ℕ => (n : ℤ))) q).natAbs =
      listDepthBound xs q := by
  rw [int_bound_cast]
  simp

/-- Cast natural-bound lists have integer support bounded by their length. -/
theorem cast_seq_length (xs : List ℕ) :
    ISBound
      (fun q => intDepthBound (xs.map (fun n : ℕ => (n : ℤ))) q) xs.length := by
  intro q hq
  change intDepthBound (xs.map (fun n : ℕ => (n : ℤ))) q = 0
  rw [int_bound_cast]
  have hz := depth_bound_length xs (q := q) (by omega)
  simp [hz]

/-- Cast natural-bound lists have the sharper predecessor integer support bound. -/
theorem cast_seq_pred (xs : List ℕ) :
    ISBound
      (fun q => intDepthBound (xs.map (fun n : ℕ => (n : ℤ))) q)
      (xs.length - 1) := by
  intro q hq
  change intDepthBound (xs.map (fun n : ℕ => (n : ℤ))) q = 0
  rw [int_bound_cast]
  have hz := depth_bound_length xs (q := q) (by omega)
  simp [hz]

/-- Scaling an integer-bound list scales its pointwise depth-bound sequence. -/
@[simp] theorem int_bound_left (a : ℤ) (xs : List ℤ) (q : ℕ) :
    intDepthBound (xs.map (fun z : ℤ => a * z)) q =
      a * intDepthBound xs q := by
  induction xs generalizing q with
  | nil => simp
  | cons x xs ih =>
      cases q with
      | zero => simp [intDepthBound]
      | succ q => simpa using ih q

/-- Right-scaling an integer-bound list scales its pointwise depth-bound sequence. -/
@[simp] theorem int_bound_right (xs : List ℤ) (a : ℤ) (q : ℕ) :
    intDepthBound (xs.map (fun z : ℤ => z * a)) q =
      intDepthBound xs q * a := by
  induction xs generalizing q with
  | nil => simp
  | cons x xs ih =>
      cases q with
      | zero => simp [intDepthBound]
      | succ q => simpa using ih q

/-- Negating an integer-bound list negates its pointwise depth-bound sequence. -/
@[simp] theorem int_bound_neg (xs : List ℤ) (q : ℕ) :
    intDepthBound (xs.map Neg.neg) q = - intDepthBound xs q := by
  induction xs generalizing q with
  | nil => simp
  | cons x xs ih =>
      cases q with
      | zero => simp [intDepthBound]
      | succ q => simpa using ih q

/-- Taking absolute values of an integer-bound list takes absolute values pointwise. -/
@[simp] theorem int_bound_abs (xs : List ℤ) (q : ℕ) :
    intDepthBound (xs.map (fun z : ℤ => |z|)) q =
      |intDepthBound xs q| := by
  induction xs generalizing q with
  | nil => simp
  | cons x xs ih =>
      cases q with
      | zero => simp [intDepthBound]
      | succ q => simpa using ih q

/-- Integer list depth bounds vanish beyond the supplied list. -/
theorem int_bound_length (xs : List ℤ) {q : ℕ}
    (h : xs.length ≤ q) : intDepthBound xs q = 0 := by
  rw [intDepthBound, List.getD_eq_getElem?_getD, List.getElem?_eq_none]
  · rfl
  · omega

/-- Appending a tail does not change integer list depth bounds before the original length. -/
theorem bound_append_left (xs ys : List ℤ) {q : ℕ} (h : q < xs.length) :
    intDepthBound (xs ++ ys) q = intDepthBound xs q := by
  rw [intDepthBound, intDepthBound, List.getD_eq_getElem?_getD,
    List.getD_eq_getElem?_getD, List.getElem?_append_left h]

/-- Past the original length, an appended integer tail is read with shifted index. -/
theorem bound_append_right (xs ys : List ℤ) {q : ℕ} (h : xs.length ≤ q) :
    intDepthBound (xs ++ ys) q = intDepthBound ys (q - xs.length) := by
  rw [intDepthBound, intDepthBound, List.getD_eq_getElem?_getD,
    List.getD_eq_getElem?_getD, List.getElem?_append_right h]

/-- Dropping a prefix shifts integer list depth bounds by the drop length. -/
@[simp] theorem int_bound_drop (xs : List ℤ) (k q : ℕ) :
    intDepthBound (xs.drop k) q = intDepthBound xs (k + q) := by
  rw [intDepthBound, intDepthBound, List.getD_eq_getElem?_getD,
    List.getD_eq_getElem?_getD, List.getElem?_drop]

/-- Dropping exactly a prepended zero block recovers the original integer depth bounds. -/
@[simp] theorem drop_replicate_append
    (k : ℕ) (xs : List ℤ) (q : ℕ) :
    intDepthBound ((List.replicate k (0 : ℤ) ++ xs).drop k) q =
      intDepthBound xs q := by
  simp

/-- Taking at least the whole integer-bound list does not change its depth function. -/
@[simp] theorem bound_take_length (xs : List ℤ) {N q : ℕ}
    (h : xs.length ≤ N) : intDepthBound (xs.take N) q = intDepthBound xs q := by
  rw [List.take_of_length_le h]

/-- Taking exactly the whole integer-bound list does not change its depth function. -/
@[simp] theorem int_take_length (xs : List ℤ) (q : ℕ) :
    intDepthBound (xs.take xs.length) q = intDepthBound xs q := by
  exact bound_take_length xs (q := q) le_rfl

/-- Taking enough entries preserves an integer list depth bound at covered indices. -/
theorem int_bound_take (xs : List ℤ) {M q : ℕ} (hq : q ≤ M) :
    intDepthBound (xs.take (M + 1)) q = intDepthBound xs q := by
  rw [intDepthBound, intDepthBound, List.getD_eq_getElem?_getD,
    List.getD_eq_getElem?_getD, List.getElem?_take]
  have hlt : q < M + 1 := by omega
  simp [hlt]

/-- At the splice point of an integer append, reading starts at the tail's zeroth entry. -/
@[simp] theorem int_append_length (xs ys : List ℤ) :
    intDepthBound (xs ++ ys) xs.length = intDepthBound ys 0 := by
  simpa using (bound_append_right xs ys (q := xs.length) (le_rfl))

/-- Reading an appended integer tail at an offset from the splice point. -/
@[simp] theorem append_length_add (xs ys : List ℤ) (q : ℕ) :
    intDepthBound (xs ++ ys) (xs.length + q) = intDepthBound ys q := by
  have h := bound_append_right xs ys (q := xs.length + q) (Nat.le_add_right _ _)
  simpa [Nat.add_sub_cancel_left] using h

/-- Inside a replicated integer-bound list, every entry is the replicated value. -/
theorem depth_bound_replicate (a : ℤ) {n q : ℕ} (h : q < n) :
    intDepthBound (List.replicate n a) q = a := by
  rw [intDepthBound, List.getD_eq_getElem?_getD, List.getElem?_replicate]
  simp [h]

/-- Beyond a replicated integer-bound list, entries are zero. -/
theorem int_bound_replicate (a : ℤ) {n q : ℕ} (h : n ≤ q) :
    intDepthBound (List.replicate n a) q = 0 := by
  exact int_bound_length _ (by simpa using h)


/-- A replicated zero integer-bound list is pointwise zero. -/
@[simp] theorem bound_replicate_zero (n q : ℕ) :
    intDepthBound (List.replicate n (0 : ℤ)) q = 0 := by
  by_cases h : q < n
  · simpa using (depth_bound_replicate (0 : ℤ) (n := n) (q := q) h)
  · exact int_bound_replicate (0 : ℤ) (n := n) (q := q) (by omega)

/-- Taking exactly a prepended zero block gives a pointwise-zero integer bound. -/
@[simp] theorem take_replicate_append
    (k : ℕ) (xs : List ℤ) (q : ℕ) :
    intDepthBound ((List.replicate k (0 : ℤ) ++ xs).take k) q = 0 := by
  have htake :
      (List.replicate k (0 : ℤ) ++ xs).take k = List.replicate k (0 : ℤ) := by
    simp
  rw [htake]
  exact bound_replicate_zero k q

/-- Appending zero padding to an integer-bound list does not change its depth function. -/
@[simp] theorem bound_append_replicate (xs : List ℤ) (n q : ℕ) :
    intDepthBound (xs ++ List.replicate n (0 : ℤ)) q = intDepthBound xs q := by
  by_cases h : q < xs.length
  · exact bound_append_left xs (List.replicate n (0 : ℤ)) h
  · have hle : xs.length ≤ q := by omega
    rw [bound_append_right xs (List.replicate n (0 : ℤ)) hle]
    rw [int_bound_length xs hle]
    exact bound_replicate_zero n (q - xs.length)

/-- Prepending zero padding shifts an integer-bound list to the right. -/
@[simp] theorem int_replicate_append (k : ℕ) (xs : List ℤ) (q : ℕ) :
    intDepthBound (List.replicate k (0 : ℤ) ++ xs) q =
      if k ≤ q then intDepthBound xs (q - k) else 0 := by
  by_cases h : k ≤ q
  · rw [bound_append_right (List.replicate k (0 : ℤ)) xs (by simpa using h)]
    simp [h]
  · have hlt : q < (List.replicate k (0 : ℤ)).length := by
      simpa using (Nat.lt_of_not_ge h)
    rw [bound_append_left (List.replicate k (0 : ℤ)) xs hlt]
    simp [h, bound_replicate_zero]

/-- A list-backed integer sequence has finite support, coarsely bounded by its length. -/
theorem seq_support_length (xs : List ℤ) :
    ISBound (fun q => intDepthBound xs q) xs.length := by
  intro q hq
  exact int_bound_length xs (by omega)

/-- A sharper predecessor support bound for a list-backed integer sequence. -/
theorem seq_support_pred (xs : List ℤ) :
    ISBound (fun q => intDepthBound xs q) (xs.length - 1) := by
  intro q hq
  exact int_bound_length xs (by omega)

/-- Prepending zero padding shifts the sharp predecessor support bound for integer lists. -/
theorem replicate_seq_pred
    (k : ℕ) (xs : List ℤ) :
    ISBound
      (fun q => intDepthBound (List.replicate k (0 : ℤ) ++ xs) q)
      (xs.length - 1 + k) := by
  have hb := (seq_support_pred xs).shiftRight k
  refine hb.congr ?_
  intro q
  simp [int_replicate_append]

/-- Appending zero padding does not affect any integer support-bound assertion. -/
theorem replicate_seq_support
    (xs : List ℤ) (k B : ℕ) :
    ISBound
        (fun q => intDepthBound (xs ++ List.replicate k (0 : ℤ)) q) B ↔
      ISBound (fun q => intDepthBound xs q) B := by
  constructor
  · intro h
    refine h.congr ?_
    intro q
    simp [bound_append_replicate]
  · intro h
    refine h.congr ?_
    intro q
    simp [bound_append_replicate]

/-- Negating every entry of an integer-bound list does not change support bounds. -/
theorem neg_seq_support (xs : List ℤ) (B : ℕ) :
    ISBound (fun q => intDepthBound (xs.map Neg.neg) q) B ↔
      ISBound (fun q => intDepthBound xs q) B := by
  constructor
  · intro h q hq
    have hz := h q hq
    change intDepthBound (xs.map Neg.neg) q = 0 at hz
    rw [int_bound_neg] at hz
    exact neg_eq_zero.mp hz
  · intro h q hq
    simp [h q hq]

/-- Taking absolute values entrywise does not change integer support bounds. -/
theorem abs_seq_support (xs : List ℤ) (B : ℕ) :
    ISBound (fun q => intDepthBound (xs.map (fun z : ℤ => |z|)) q) B ↔
      ISBound (fun q => intDepthBound xs q) B := by
  constructor
  · intro h q hq
    have hz := h q hq
    change intDepthBound (xs.map (fun z : ℤ => |z|)) q = 0 at hz
    rw [int_bound_abs] at hz
    exact abs_eq_zero.mp hz
  · intro h q hq
    simp [h q hq]

/-- Multiplying every entry on the left by a nonzero scalar does not change integer
support bounds. -/
theorem bound_seq_support
    (a : ℤ) (ha : a ≠ 0) (xs : List ℤ) (B : ℕ) :
    ISBound (fun q => intDepthBound (xs.map (fun z : ℤ => a * z)) q) B ↔
      ISBound (fun q => intDepthBound xs q) B := by
  constructor
  · intro h q hq
    have hz := h q hq
    change intDepthBound (xs.map (fun z : ℤ => a * z)) q = 0 at hz
    rw [int_bound_left] at hz
    rcases mul_eq_zero.mp hz with hz | hz
    · exact False.elim (ha hz)
    · exact hz
  · intro h q hq
    simp [h q hq]

/-- Multiplying every entry on the right by a nonzero scalar does not change integer
support bounds. -/
theorem int_seq_support
    (xs : List ℤ) (a : ℤ) (ha : a ≠ 0) (B : ℕ) :
    ISBound (fun q => intDepthBound (xs.map (fun z : ℤ => z * a)) q) B ↔
      ISBound (fun q => intDepthBound xs q) B := by
  constructor
  · intro h q hq
    have hz := h q hq
    change intDepthBound (xs.map (fun z : ℤ => z * a)) q = 0 at hz
    rw [int_bound_right] at hz
    rcases mul_eq_zero.mp hz with hz | hz
    · exact hz
    · exact False.elim (ha hz)
  · intro h q hq
    simp [h q hq]

/-- Prefix sums of an integer list-backed sequence stabilize after the last possible
nonzero entry. -/
theorem bound_range_pred (xs : List ℤ) {M N : ℕ}
    (hM : xs.length - 1 ≤ M) (hMN : M ≤ N) :
    (∑ q ∈ Finset.range (N + 1), intDepthBound xs q) =
      ∑ q ∈ Finset.range (M + 1), intDepthBound xs q := by
  exact int_range_bound
    (seq_support_pred xs) hM hMN

/-- Sum of list-supplied integer bounds over the shallow prefix `q < q0`. -/
def prefixBoundSum (M q0 : ℕ) (xs : List ℤ) : ℤ :=
  ∑ q ∈ (Finset.range (M + 1)).filter (fun q => q < q0), intDepthBound xs q

/-- Negating an integer-bound list negates its prefix-bound sum. -/
@[simp] theorem prefix_bound_neg (M q0 : ℕ) (xs : List ℤ) :
    prefixBoundSum M q0 (xs.map Neg.neg) = - prefixBoundSum M q0 xs := by
  unfold prefixBoundSum
  simp [Finset.sum_neg_distrib]

/-- Left-scaling an integer-bound list scales its prefix-bound sum. -/
@[simp] theorem prefix_bound_left (M q0 : ℕ) (a : ℤ) (xs : List ℤ) :
    prefixBoundSum M q0 (xs.map (fun z : ℤ => a * z)) =
      a * prefixBoundSum M q0 xs := by
  unfold prefixBoundSum
  simp [Finset.mul_sum]

/-- Right-scaling an integer-bound list scales its prefix-bound sum. -/
@[simp] theorem prefix_bound_right (M q0 : ℕ) (xs : List ℤ) (a : ℤ) :
    prefixBoundSum M q0 (xs.map (fun z : ℤ => z * a)) =
      prefixBoundSum M q0 xs * a := by
  unfold prefixBoundSum
  simp [Finset.sum_mul]

/-- Prefix-bound sums are nonnegative when every sampled list entry is nonnegative. -/
theorem prefix_nonneg_entries {M q0 : ℕ} {xs : List ℤ}
    (h : ∀ q, q ≤ M → 0 ≤ intDepthBound xs q) :
    0 ≤ prefixBoundSum M q0 xs := by
  unfold prefixBoundSum
  apply Finset.sum_nonneg
  intro q hq
  have hqr : q ∈ Finset.range (M + 1) := (Finset.mem_filter.mp hq).1
  have hle : q ≤ M := by
    have hlt : q < M + 1 := by simpa using hqr
    omega
  exact h q hle

/-- Prefix-bound sums are monotone under pointwise comparison on the sampled range. -/
theorem prefix_bound_mono {M q0 : ℕ} {xs ys : List ℤ}
    (h : ∀ q, q ≤ M → intDepthBound xs q ≤ intDepthBound ys q) :
    prefixBoundSum M q0 xs ≤ prefixBoundSum M q0 ys := by
  unfold prefixBoundSum
  apply Finset.sum_le_sum
  intro q hq
  have hqr : q ∈ Finset.range (M + 1) := (Finset.mem_filter.mp hq).1
  have hle : q ≤ M := by
    have hlt : q < M + 1 := by simpa using hqr
    omega
  exact h q hle

/-- A cast natural-bound list has nonnegative prefix-bound sum. -/
theorem prefix_cast_nonneg (M q0 : ℕ) (xs : List ℕ) :
    0 ≤ prefixBoundSum M q0 (xs.map (fun n : ℕ => (n : ℤ))) := by
  apply prefix_nonneg_entries
  intro q hq
  exact int_cast_nonneg xs q

/-- The empty integer-bound list contributes nothing to any prefix sum. -/
@[simp] theorem prefix_bound_nil (M q0 : ℕ) :
    prefixBoundSum M q0 [] = 0 := by
  simp [prefixBoundSum, intDepthBound]


/-- A zero-filled integer prefix-bound list contributes no prefix mass. -/
@[simp] theorem prefix_bound_replicate (M q0 n : ℕ) :
    prefixBoundSum M q0 (List.replicate n (0 : ℤ)) = 0 := by
  simp [prefixBoundSum]

/-- A prefix ending inside a prepended zero block contributes no integer mass. -/
theorem prefix_replicate_append
    (M q0 k : ℕ) (xs : List ℤ) (h : q0 ≤ k) :
    prefixBoundSum M q0 (List.replicate k (0 : ℤ) ++ xs) = 0 := by
  unfold prefixBoundSum
  apply Finset.sum_eq_zero
  intro q hq
  have hq0 : q < q0 := (Finset.mem_filter.mp hq).2
  have hkq : ¬ k ≤ q := by omega
  simp [int_replicate_append, hkq]

/-- If the ambient sampled range lies inside a prepended zero block, the integer
prefix-bound sum is zero (independently of the prefix cutoff). -/
theorem bound_replicate_append
    (M q0 k : ℕ) (xs : List ℤ) (hM : M < k) :
    prefixBoundSum M q0 (List.replicate k (0 : ℤ) ++ xs) = 0 := by
  unfold prefixBoundSum
  apply Finset.sum_eq_zero
  intro q hq
  have hqr : q ∈ Finset.range (M + 1) := (Finset.mem_filter.mp hq).1
  have hqle : q ≤ M := by
    have hlt : q < M + 1 := by simpa using hqr
    omega
  have hkq : ¬ k ≤ q := by omega
  simp [int_replicate_append, hkq]

/-- If the prefix cutoff is zero, the prefix-bound sum is empty. -/
@[simp] theorem prefix_sum_cutoff (M : ℕ) (xs : List ℤ) :
    prefixBoundSum M 0 xs = 0 := by
  simp [prefixBoundSum]

/-- Degree-zero prefix-bound sum: it is the zeroth entry exactly when the cutoff is positive. -/
theorem prefix_bound_zero (q0 : ℕ) (xs : List ℤ) :
    prefixBoundSum 0 q0 xs = if 0 < q0 then intDepthBound xs 0 else 0 := by
  by_cases h : 0 < q0
  · dsimp [prefixBoundSum]
    rw [Finset.sum_filter]
    simp [h]
  · have hz : q0 = 0 := by omega
    simp [prefixBoundSum, hz]

/-- A singleton integer-bound prefix sum is just its entry when the cutoff is positive. -/
@[simp] theorem prefix_bound_singleton (M q0 : ℕ) (x : ℤ) :
    prefixBoundSum M q0 [x] = if 0 < q0 then x else 0 := by
  by_cases hq : 0 < q0
  · unfold prefixBoundSum
    rw [Finset.sum_eq_single 0]
    · simp [intDepthBound, hq]
    · intro b _ hb0
      rcases Nat.exists_eq_succ_of_ne_zero hb0 with ⟨k, rfl⟩
      simp [intDepthBound]
    · intro h0
      exfalso
      apply h0
      simp [hq]
  · have hz : q0 = 0 := by omega
    simp [prefixBoundSum, hz]


/-- If the cutoff exceeds the ambient degree, the prefix-bound sum is the full degree sum. -/
theorem prefix_bound_cutoff (M q0 : ℕ) (xs : List ℤ)
    (hM : M < q0) :
    prefixBoundSum M q0 xs =
      ∑ q ∈ Finset.range (M + 1), intDepthBound xs q := by
  unfold prefixBoundSum
  apply Finset.sum_congr
  · ext q
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · intro h; exact h.1
    · intro hq; exact ⟨hq, by omega⟩
  · intro x hx; rfl

/-- If the cutoff lies inside the ambient range, the prefix-bound sum is the cutoff range sum. -/
theorem prefix_range_cutoff (M q0 : ℕ) (xs : List ℤ)
    (h : q0 ≤ M + 1) :
    prefixBoundSum M q0 xs =
      ∑ q ∈ Finset.range q0, intDepthBound xs q := by
  unfold prefixBoundSum
  apply Finset.sum_congr
  · ext q
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · intro hq; exact hq.2
    · intro hq; exact ⟨by omega, hq⟩
  · intro x hx; rfl

/-- Degree-one prefix-bound sum as the two possible sampled entries. -/
theorem prefix_bound_degree (q0 : ℕ) (xs : List ℤ) :
    prefixBoundSum 1 q0 xs =
      (if 0 < q0 then intDepthBound xs 0 else 0) +
        (if 1 < q0 then intDepthBound xs 1 else 0) := by
  by_cases h0 : 0 < q0
  · by_cases h1 : 1 < q0
    · rw [prefix_bound_cutoff 1 q0 xs h1]
      simp [Finset.sum_range_succ, h0, h1]
    · have hq0 : q0 = 1 := by omega
      subst q0
      simp [prefixBoundSum]
  · have hq0 : q0 = 0 := by omega
    subst q0
    simp [prefixBoundSum]

/-- The prefix-bound list sum only depends on entries through degree `M`. -/
theorem prefix_bound_congr (M q0 : ℕ) {xs ys : List ℤ}
    (h : ∀ q, q ≤ M → intDepthBound xs q = intDepthBound ys q) :
    prefixBoundSum M q0 xs = prefixBoundSum M q0 ys := by
  unfold prefixBoundSum
  apply Finset.sum_congr rfl
  intro q hq
  have hqr : q ∈ Finset.range (M + 1) := (Finset.mem_filter.mp hq).1
  have hle : q ≤ M := by
    have hlt : q < M + 1 := by simpa using hqr
    omega
  rw [h q hle]

/-- Appending zero padding to an integer-bound list does not change its prefix-bound sum. -/
@[simp] theorem prefix_append_replicate (M q0 n : ℕ) (xs : List ℤ) :
    prefixBoundSum M q0 (xs ++ List.replicate n (0 : ℤ)) =
      prefixBoundSum M q0 xs := by
  apply prefix_bound_congr
  intro q hq
  exact bound_append_replicate xs n q

/-- Taking at least the whole integer-bound list does not change its prefix-bound sum. -/
@[simp] theorem prefix_take_length (M q0 N : ℕ) (xs : List ℤ)
    (h : xs.length ≤ N) :
    prefixBoundSum M q0 (xs.take N) = prefixBoundSum M q0 xs := by
  rw [List.take_of_length_le h]

/-- Truncating an integer-bound list after degree `M` does not change the prefix-bound sum. -/
theorem prefix_bound_take (M q0 : ℕ) (xs : List ℤ) :
    prefixBoundSum M q0 (xs.take (M + 1)) = prefixBoundSum M q0 xs := by
  apply prefix_bound_congr
  intro q hq
  exact int_bound_take xs hq

/-- Appending entries beyond degree `M` does not change the integer prefix-bound sum. -/
theorem prefix_append_length (M q0 : ℕ) (xs ys : List ℤ)
    (hM : M < xs.length) :
    prefixBoundSum M q0 (xs ++ ys) = prefixBoundSum M q0 xs := by
  apply prefix_bound_congr
  intro q hq
  exact bound_append_left xs ys (Nat.lt_of_le_of_lt hq hM)

variable {p : ℕ} (FP : FPres p)

/-- Prefix-tail certificate adapter where the explicitly bounded prefix is given
as an integer list of per-depth contribution bounds. -/
def RGCert.prefix_tail_boundlist
    [Fintype FP.toPresentation.Relator]
    (num den genLower q0 tailCount : ℕ) (lowBounds : List ℤ)
    (hnum : 0 < num) (hden : 0 < den) (hproper : num < den)
    (hgen : genLower ≤ FP.generatorCount)
    (hb : ∀ q ∈ (Finset.range (FP.maxRelatorDepth + 1)).filter (fun q => q < q0),
      clearedGSTerm FP.maxRelatorDepth FP.relatorDepthMultiplicity num den q ≤
        intDepthBound lowBounds q)
    (htailcount : (∑ q ∈ (Finset.range (FP.maxRelatorDepth + 1)).filter
        (fun q => ¬ q < q0), FP.relatorDepthMultiplicity q) ≤ tailCount)
    (hneg : clearedGSBase genLower FP.maxRelatorDepth num den +
        (prefixBoundSum FP.maxRelatorDepth q0 lowBounds +
          (tailCount : ℤ) * ((num : ℤ) ^ q0 *
            (den : ℤ) ^ (FP.maxRelatorDepth + 1 - q0))) < 0) :
    FP.RGCert := by
  refine RGCert.prefix_tail_pointwisebounds FP num den genLower q0 tailCount
    (fun q => intDepthBound lowBounds q) hnum hden hproper hgen hb htailcount ?_
  simpa [prefixBoundSum] using hneg

end
end FPres
end Towers
