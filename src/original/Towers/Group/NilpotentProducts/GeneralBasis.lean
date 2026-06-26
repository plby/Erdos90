import Towers.Group.NilpotentProducts.GeneralModel
import Towers.Group.Edmonton.HallCommutatorIdentities
import Mathlib.Tactic.DeriveFintype


/-!
# The arbitrary-rank basis axes for equation (18)
-/

namespace Struik
namespace P1960

open Towers
open Towers.Edmonton

/-- The six families of coordinate positions in the arbitrary-rank
equation-(18) basis. -/
inductive GeneralBasisIndex (t : ℕ)
  | single : Fin t → GeneralBasisIndex t
  | pair : Pair t → GeneralBasisIndex t
  | pairLeft : Pair t → GeneralBasisIndex t
  | pairRight : Pair t → GeneralBasisIndex t
  | tripleFirst : Triple t → GeneralBasisIndex t
  | tripleSecond : Triple t → GeneralBasisIndex t
  deriving DecidableEq, Fintype

/-- The integral coordinate axis at a prescribed arbitrary-rank basis
position. -/
def generalAxis {t : ℕ} :
    GeneralBasisIndex t → ℤ →
      GCoordi t
  | .single i, n => {
      GCoordi.zero t with
      single := fun j => if j = i then n else 0 }
  | .pair q, n => {
      GCoordi.zero t with
      pair := fun r => if r = q then n else 0 }
  | .pairLeft q, n => {
      GCoordi.zero t with
      pairLeft := fun r => if r = q then n else 0 }
  | .pairRight q, n => {
      GCoordi.zero t with
      pairRight := fun r => if r = q then n else 0 }
  | .tripleFirst q, n => {
      GCoordi.zero t with
      tripleFirst := fun r => if r = q then n else 0 }
  | .tripleSecond q, n => {
      GCoordi.zero t with
      tripleSecond := fun r => if r = q then n else 0 }

@[simp] private lemma general_residue_choose :
    Ring.choose (1 : ℤ) 2 = 0 := by
  decide

@[simp] private lemma general_choose_neg :
    Ring.choose (-1 : ℤ) 2 = 1 := by
  decide

@[simp] theorem general_axis_zero
    {t : ℕ} (i : GeneralBasisIndex t) :
    generalAxis i 0 =
      GCoordi.zero t := by
  cases i <;> ext <;>
    simp [generalAxis,
      GCoordi.zero]

/-- Coordinate axes add under the equation-(18) multiplication. -/
theorem generalAxis_add
    {t : ℕ} (i : GeneralBasisIndex t) (m n : ℤ) :
    GCoordi.mul
        (generalAxis i m)
        (generalAxis i n) =
      generalAxis i (m + n) := by
  cases i with
  | single i =>
      ext r
      · by_cases hri : r = i <;>
          simp [generalAxis,
          GCoordi.mul,
          GCoordi.zero, hri]
      · have hr := r.lt
        by_cases hri : r.i = i <;>
          by_cases hrj : r.j = i <;>
          simp [generalAxis,
          GCoordi.mul,
          GCoordi.zero, hri, hrj] at *
      · have hr := r.lt
        by_cases hri : r.i = i <;>
          by_cases hrj : r.j = i <;>
          simp [generalAxis,
          GCoordi.mul,
          GCoordi.zero, hri, hrj] at *
      · have hr := r.lt
        by_cases hri : r.i = i <;>
          by_cases hrj : r.j = i <;>
          simp [generalAxis,
          GCoordi.mul,
          GCoordi.zero, hri, hrj] at *
      · have hrij := r.lt_ij
        have hrjk := r.lt_jk
        by_cases hri : r.i = i <;>
          by_cases hrj : r.j = i <;>
          by_cases hrk : r.k = i <;>
          simp [generalAxis,
          GCoordi.mul,
          GCoordi.zero,
          Triple.ij, Triple.ik,
          Triple.jk, hri, hrj, hrk] at *
      · have hrij := r.lt_ij
        have hrjk := r.lt_jk
        by_cases hri : r.i = i <;>
          by_cases hrj : r.j = i <;>
          by_cases hrk : r.k = i <;>
          simp [generalAxis,
          GCoordi.mul,
          GCoordi.zero,
          Triple.ij, Triple.ik,
          Triple.jk, hri, hrj, hrk] at *
  | pair q =>
      ext <;>
        simp [generalAxis,
          GCoordi.mul,
          GCoordi.zero] ;
        split_ifs <;>
        ring
  | pairLeft q =>
      ext <;>
        simp [generalAxis,
          GCoordi.mul,
          GCoordi.zero] ;
        split_ifs <;>
        ring
  | pairRight q =>
      ext <;>
        simp [generalAxis,
          GCoordi.mul,
          GCoordi.zero] ;
        split_ifs <;>
        ring
  | tripleFirst q =>
      ext <;>
        simp [generalAxis,
          GCoordi.mul,
          GCoordi.zero] ;
        split_ifs <;>
        ring
  | tripleSecond q =>
      ext <;>
        simp [generalAxis,
          GCoordi.mul,
          GCoordi.zero] ;
        split_ifs <;>
        ring

/-- Inversion negates a coordinate axis. -/
theorem generalAxis_neg
    {t : ℕ} (i : GeneralBasisIndex t) (n : ℤ) :
    GCoordi.rightInv
        (generalAxis i n) =
      generalAxis i (-n) := by
  cases i with
  | single i =>
      ext r
      · by_cases hri : r = i <;>
          simp [generalAxis,
          GCoordi.rightInv,
          GCoordi.zero, hri]
      · have hr := r.lt
        by_cases hri : r.i = i <;>
          by_cases hrj : r.j = i <;>
          simp [generalAxis,
          GCoordi.rightInv,
          GCoordi.zero, hri, hrj] at *
      · have hr := r.lt
        by_cases hri : r.i = i <;>
          by_cases hrj : r.j = i <;>
          simp [generalAxis,
          GCoordi.rightInv,
          GCoordi.zero, hri, hrj] at *
      · have hr := r.lt
        by_cases hri : r.i = i <;>
          by_cases hrj : r.j = i <;>
          simp [generalAxis,
          GCoordi.rightInv,
          GCoordi.zero, hri, hrj] at *
      · have hrij := r.lt_ij
        have hrjk := r.lt_jk
        by_cases hri : r.i = i <;>
          by_cases hrj : r.j = i <;>
          by_cases hrk : r.k = i <;>
          simp [generalAxis,
          GCoordi.rightInv,
          GCoordi.zero,
          Triple.ij, Triple.ik,
          Triple.jk, hri, hrj, hrk] at *
      · have hrij := r.lt_ij
        have hrjk := r.lt_jk
        by_cases hri : r.i = i <;>
          by_cases hrj : r.j = i <;>
          by_cases hrk : r.k = i <;>
          simp [generalAxis,
          GCoordi.rightInv,
          GCoordi.zero,
          Triple.ij, Triple.ik,
          Triple.jk, hri, hrj, hrk] at *
  | pair q =>
      ext <;>
        simp [generalAxis,
          GCoordi.rightInv,
          GCoordi.zero] ;
        split_ifs <;>
        ring
  | pairLeft q =>
      ext <;>
        simp [generalAxis,
          GCoordi.rightInv,
          GCoordi.zero] ;
        split_ifs <;>
        ring
  | pairRight q =>
      ext <;>
        simp [generalAxis,
          GCoordi.rightInv,
          GCoordi.zero] ;
        split_ifs <;>
        ring
  | tripleFirst q =>
      ext <;>
        simp [generalAxis,
          GCoordi.rightInv,
          GCoordi.zero] ;
        split_ifs <;>
        ring
  | tripleSecond q =>
      ext <;>
        simp [generalAxis,
          GCoordi.rightInv,
          GCoordi.zero] ;
        split_ifs <;>
        ring

private theorem general_axis_pow
    {t : ℕ} (i : GeneralBasisIndex t) (n : ℕ) :
    generalAxis i 1 ^ n =
      generalAxis i n := by
  induction n with
  | zero =>
      change GCoordi.zero t =
        generalAxis i 0
      exact (general_axis_zero i).symm
  | succ n ih =>
      rw [pow_succ, ih]
      change
        GCoordi.mul
            (generalAxis i n)
            (generalAxis i 1) =
          generalAxis i (n + 1)
      simpa using generalAxis_add i n 1

/-- Integer powers of a unit axis give the corresponding integral
coordinate. -/
theorem general_axis_one
    {t : ℕ} (i : GeneralBasisIndex t) (n : ℤ) :
    generalAxis i 1 ^ n =
      generalAxis i n := by
  cases n with
  | ofNat n =>
      simpa only [zpow_natCast, Int.ofNat_eq_natCast] using
        general_axis_pow i n
  | negSucc n =>
      rw [zpow_negSucc, general_axis_pow]
      change
        GCoordi.rightInv
            (generalAxis i (n + 1)) =
          generalAxis i (Int.negSucc n)
      rw [generalAxis_neg]
      congr

@[simp] theorem general_axis_single
    {t : ℕ} (i : Fin t) :
    generalAxis (.single i) 1 =
      generalGenerator i := by
  ext <;>
    simp [generalAxis, generalGenerator,
      GCoordi.zero]

set_option maxHeartbeats 2000000 in
-- The finite rank-three coordinate normalization needs a larger heartbeat budget.
set_option maxRecDepth 4000 in
-- Exhaustive coordinate normalization across the finite rank-three cases is expensive.
/-- A basic commutator of two increasing coordinate generators is the
corresponding weight-two unit axis. -/
theorem general_hallCommutator
    {t : ℕ} (q : Pair t) :
    hallCommutator
        (generalGenerator q.i)
        (generalGenerator q.j) =
      generalAxis (.pair q) 1 := by
  unfold hallCommutator
  change
    GCoordi.mul
      (GCoordi.mul
        (GCoordi.mul
          (GCoordi.rightInv
            (generalGenerator q.i))
          (GCoordi.rightInv
            (generalGenerator q.j)))
        (generalGenerator q.i)
        )
      (generalGenerator q.j) =
      generalAxis (.pair q) 1
  ext r
  · simp [generalGenerator, generalAxis,
      GCoordi.mul,
      GCoordi.rightInv,
      GCoordi.zero]
  · have hq := q.lt
    have hr := r.lt
    simp [generalGenerator, generalAxis,
      GCoordi.mul,
      GCoordi.rightInv,
      GCoordi.zero]
    split_ifs at * <;>
      simp_all ;
      omega
  · have hq := q.lt
    have hr := r.lt
    simp [generalGenerator, generalAxis,
      GCoordi.mul,
      GCoordi.rightInv,
      GCoordi.zero]
    split_ifs at * <;>
      simp_all
  · have hq := q.lt
    have hr := r.lt
    simp [generalGenerator, generalAxis,
      GCoordi.mul,
      GCoordi.rightInv,
      GCoordi.zero]
    split_ifs at * <;>
      simp_all
  · have hq := q.lt
    have hrij := r.lt_ij
    have hrjk := r.lt_jk
    simp [generalGenerator, generalAxis,
      GCoordi.mul,
      GCoordi.rightInv,
      GCoordi.zero,
      Triple.ij, Triple.ik,
      Triple.jk]
    split_ifs at * <;>
      simp_all <;>
      omega
  · have hq := q.lt
    have hrij := r.lt_ij
    have hrjk := r.lt_jk
    simp [generalGenerator, generalAxis,
      GCoordi.mul,
      GCoordi.rightInv,
      GCoordi.zero,
      Triple.ij, Triple.ik,
      Triple.jk]
    split_ifs at * <;>
      simp_all

set_option maxHeartbeats 2000000 in
-- The finite rank-three coordinate normalization needs a larger heartbeat budget.
set_option maxRecDepth 4000 in
-- Exhaustive coordinate normalization across the finite rank-three cases is expensive.
/-- The repeated-left weight-three Hall commutator is its unit axis. -/
theorem general_triple_left
    {t : ℕ} (q : Pair t) :
    hallTripleCommutator
        (generalGenerator q.i)
        (generalGenerator q.j)
        (generalGenerator q.i) =
      generalAxis (.pairLeft q) 1 := by
  rw [hallTripleCommutator, general_hallCommutator]
  unfold hallCommutator
  change
    GCoordi.mul
      (GCoordi.mul
        (GCoordi.mul
          (GCoordi.rightInv
            (generalAxis (.pair q) 1))
          (GCoordi.rightInv
            (generalGenerator q.i)))
        (generalAxis (.pair q) 1))
      (generalGenerator q.i) =
      generalAxis (.pairLeft q) 1
  ext r
  · simp [generalGenerator, generalAxis,
      GCoordi.mul,
      GCoordi.rightInv,
      GCoordi.zero]
  · have hq := q.lt
    have hr := r.lt
    simp [generalGenerator, generalAxis,
      GCoordi.mul,
      GCoordi.rightInv,
      GCoordi.zero]
    split_ifs at * <;>
      simp_all
  · have hq := q.lt
    have hr := r.lt
    simp [generalGenerator, generalAxis,
      GCoordi.mul,
      GCoordi.rightInv,
      GCoordi.zero]
    split_ifs at * <;>
      simp_all
  · have hq := q.lt
    have hr := r.lt
    simp [generalGenerator, generalAxis,
      GCoordi.mul,
      GCoordi.rightInv,
      GCoordi.zero]
    split_ifs at * <;>
      simp_all
  · have hq := q.lt
    have hrij := r.lt_ij
    have hrjk := r.lt_jk
    simp [generalGenerator, generalAxis,
      GCoordi.mul,
      GCoordi.rightInv,
      GCoordi.zero,
      Triple.ij, Triple.ik,
      Triple.jk]
    split_ifs at * <;>
      simp_all ;
      omega
  · have hq := q.lt
    have hrij := r.lt_ij
    have hrjk := r.lt_jk
    simp [generalGenerator, generalAxis,
      GCoordi.mul,
      GCoordi.rightInv,
      GCoordi.zero,
      Triple.ij, Triple.ik,
      Triple.jk]
    split_ifs at * <;>
      simp_all

set_option maxHeartbeats 2000000 in
-- The finite rank-three coordinate normalization needs a larger heartbeat budget.
set_option maxRecDepth 4000 in
-- Exhaustive coordinate normalization across the finite rank-three cases is expensive.
/-- The repeated-right weight-three Hall commutator is its unit axis. -/
theorem general_triple_pair
    {t : ℕ} (q : Pair t) :
    hallTripleCommutator
        (generalGenerator q.i)
        (generalGenerator q.j)
        (generalGenerator q.j) =
      generalAxis (.pairRight q) 1 := by
  rw [hallTripleCommutator, general_hallCommutator]
  unfold hallCommutator
  change
    GCoordi.mul
      (GCoordi.mul
        (GCoordi.mul
          (GCoordi.rightInv
            (generalAxis (.pair q) 1))
          (GCoordi.rightInv
            (generalGenerator q.j)))
        (generalAxis (.pair q) 1))
      (generalGenerator q.j) =
      generalAxis (.pairRight q) 1
  ext r
  · simp [generalGenerator, generalAxis,
      GCoordi.mul,
      GCoordi.rightInv,
      GCoordi.zero]
  · have hq := q.lt
    have hr := r.lt
    simp [generalGenerator, generalAxis,
      GCoordi.mul,
      GCoordi.rightInv,
      GCoordi.zero]
    split_ifs at * <;>
      simp_all
  · have hq := q.lt
    have hr := r.lt
    simp [generalGenerator, generalAxis,
      GCoordi.mul,
      GCoordi.rightInv,
      GCoordi.zero]
    split_ifs at * <;>
      simp_all
  · have hq := q.lt
    have hr := r.lt
    simp [generalGenerator, generalAxis,
      GCoordi.mul,
      GCoordi.rightInv,
      GCoordi.zero]
    split_ifs at * <;>
      simp_all
  · have hq := q.lt
    have hrij := r.lt_ij
    have hrjk := r.lt_jk
    simp [generalGenerator, generalAxis,
      GCoordi.mul,
      GCoordi.rightInv,
      GCoordi.zero,
      Triple.ij, Triple.ik,
      Triple.jk]
    split_ifs at * <;>
      simp_all
  · have hq := q.lt
    have hrij := r.lt_ij
    have hrjk := r.lt_jk
    simp [generalGenerator, generalAxis,
      GCoordi.mul,
      GCoordi.rightInv,
      GCoordi.zero,
      Triple.ij, Triple.ik,
      Triple.jk]
    split_ifs at * <;>
      simp_all ;
      omega

set_option maxHeartbeats 2000000 in
-- The finite rank-three coordinate normalization needs a larger heartbeat budget.
set_option maxRecDepth 4000 in
-- Exhaustive coordinate normalization across the finite rank-three cases is expensive.
/-- The increasing distinct-index weight-three commutator is the first
triple unit axis. -/
theorem general_triple_first
    {t : ℕ} (q : Triple t) :
    hallTripleCommutator
        (generalGenerator q.i)
        (generalGenerator q.j)
        (generalGenerator q.k) =
      generalAxis (.tripleFirst q) 1 := by
  have hij :
      hallCommutator
          (generalGenerator q.i)
          (generalGenerator q.j) =
        generalAxis (.pair q.ij) 1 := by
    simpa [Triple.ij] using
      general_hallCommutator q.ij
  rw [hallTripleCommutator, hij]
  unfold hallCommutator
  change
    GCoordi.mul
      (GCoordi.mul
        (GCoordi.mul
          (GCoordi.rightInv
            (generalAxis (.pair q.ij) 1))
          (GCoordi.rightInv
            (generalGenerator q.k)))
        (generalAxis (.pair q.ij) 1))
      (generalGenerator q.k) =
      generalAxis (.tripleFirst q) 1
  ext r
  · simp [generalGenerator, generalAxis,
      GCoordi.mul,
      GCoordi.rightInv,
      GCoordi.zero]
  · have hqij := q.lt_ij
    have hqjk := q.lt_jk
    have hr := r.lt
    simp [generalGenerator, generalAxis,
      GCoordi.mul,
      GCoordi.rightInv,
      GCoordi.zero,
      Triple.ij]
    split_ifs at * <;>
      simp_all
  · have hqij := q.lt_ij
    have hqjk := q.lt_jk
    have hr := r.lt
    simp [generalGenerator, generalAxis,
      GCoordi.mul,
      GCoordi.rightInv,
      GCoordi.zero,
      Triple.ij]
    split_ifs at * <;>
      simp_all
  · have hqij := q.lt_ij
    have hqjk := q.lt_jk
    have hr := r.lt
    simp [generalGenerator, generalAxis,
      GCoordi.mul,
      GCoordi.rightInv,
      GCoordi.zero,
      Triple.ij]
    split_ifs at * <;>
      simp_all
  · have hqij := q.lt_ij
    have hqjk := q.lt_jk
    have hrij := r.lt_ij
    have hrjk := r.lt_jk
    simp [generalGenerator, generalAxis,
      GCoordi.mul,
      GCoordi.rightInv,
      GCoordi.zero,
      Triple.ij, Triple.ik,
      Triple.jk]
    split_ifs at * <;>
      simp_all ;
      omega
  · have hqij := q.lt_ij
    have hqjk := q.lt_jk
    have hrij := r.lt_ij
    have hrjk := r.lt_jk
    simp [generalGenerator, generalAxis,
      GCoordi.mul,
      GCoordi.rightInv,
      GCoordi.zero,
      Triple.ij, Triple.ik,
      Triple.jk]
    split_ifs at * <;>
      simp_all <;>
      omega

set_option maxHeartbeats 2000000 in
-- The finite rank-three coordinate normalization needs a larger heartbeat budget.
set_option maxRecDepth 4000 in
-- Exhaustive coordinate normalization across the finite rank-three cases is expensive.
/-- The other Hall commutator on three increasing indices is the second
triple unit axis. -/
theorem general_triple_second
    {t : ℕ} (q : Triple t) :
    hallTripleCommutator
        (generalGenerator q.j)
        (generalGenerator q.k)
        (generalGenerator q.i) =
      generalAxis (.tripleSecond q) 1 := by
  have hjk :
      hallCommutator
          (generalGenerator q.j)
          (generalGenerator q.k) =
        generalAxis (.pair q.jk) 1 := by
    simpa [Triple.jk] using
      general_hallCommutator q.jk
  rw [hallTripleCommutator, hjk]
  unfold hallCommutator
  change
    GCoordi.mul
      (GCoordi.mul
        (GCoordi.mul
          (GCoordi.rightInv
            (generalAxis (.pair q.jk) 1))
          (GCoordi.rightInv
            (generalGenerator q.i)))
        (generalAxis (.pair q.jk) 1))
      (generalGenerator q.i) =
      generalAxis (.tripleSecond q) 1
  ext r
  · simp [generalGenerator, generalAxis,
      GCoordi.mul,
      GCoordi.rightInv,
      GCoordi.zero]
  · have hqij := q.lt_ij
    have hqjk := q.lt_jk
    have hr := r.lt
    simp [generalGenerator, generalAxis,
      GCoordi.mul,
      GCoordi.rightInv,
      GCoordi.zero,
      Triple.jk]
    split_ifs at * <;>
      simp_all
  · have hqij := q.lt_ij
    have hqjk := q.lt_jk
    have hr := r.lt
    simp [generalGenerator, generalAxis,
      GCoordi.mul,
      GCoordi.rightInv,
      GCoordi.zero,
      Triple.jk]
    split_ifs at * <;>
      simp_all
  · have hqij := q.lt_ij
    have hqjk := q.lt_jk
    have hr := r.lt
    simp [generalGenerator, generalAxis,
      GCoordi.mul,
      GCoordi.rightInv,
      GCoordi.zero,
      Triple.jk]
    split_ifs at * <;>
      simp_all
  · have hqij := q.lt_ij
    have hqjk := q.lt_jk
    have hrij := r.lt_ij
    have hrjk := r.lt_jk
    simp [generalGenerator, generalAxis,
      GCoordi.mul,
      GCoordi.rightInv,
      GCoordi.zero,
      Triple.ij, Triple.ik,
      Triple.jk]
    split_ifs at * <;>
      simp_all <;>
      omega
  · have hqij := q.lt_ij
    have hqjk := q.lt_jk
    have hrij := r.lt_ij
    have hrjk := r.lt_jk
    simp [generalGenerator, generalAxis,
      GCoordi.mul,
      GCoordi.rightInv,
      GCoordi.zero,
      Triple.ij, Triple.ik,
      Triple.jk]
    split_ifs at * <;>
      simp_all ;
      omega

end P1960
end Struik
