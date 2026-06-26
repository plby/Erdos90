import Submission.CantEick.PresentationData
import Mathlib.Algebra.Group.Conj
import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Coordinate operations in a consistent presentation

Cant--Eick first defines multiplication, powering, and conjugation functions
by taking coordinates of the corresponding group elements in the unique normal
form.  This file records those semantic functions and their basic laws.
-/

namespace Submission
namespace CantEick

/-- Zero out the last coordinate of a tuple. -/
def withoutLastCoord {n : ℕ} (x : Fin (n + 1) → ℤ) : Fin (n + 1) → ℤ :=
  fun i => if i = Fin.last n then 0 else x i

/-- Add `z` to the last coordinate of a tuple. -/
def addLastCoord {n : ℕ} (x : Fin (n + 1) → ℤ) (z : ℤ) : Fin (n + 1) → ℤ :=
  fun i => if i = Fin.last n then x i + z else x i

@[simp]
lemma without_coord {n : ℕ} (x : Fin (n + 1) → ℤ) :
    withoutLastCoord x (Fin.last n) = 0 := by
  simp [withoutLastCoord]

@[simp]
lemma without_last_ne {n : ℕ} (x : Fin (n + 1) → ℤ)
    {i : Fin (n + 1)} (hi : i ≠ Fin.last n) :
    withoutLastCoord x i = x i := by
  simp [withoutLastCoord, hi]

@[simp]
lemma add_last_coord {n : ℕ} (x : Fin (n + 1) → ℤ) (z : ℤ) :
    addLastCoord x z (Fin.last n) = x (Fin.last n) + z := by
  simp [addLastCoord]

@[simp]
lemma last_coord_ne {n : ℕ} (x : Fin (n + 1) → ℤ) (z : ℤ)
    {i : Fin (n + 1)} (hi : i ≠ Fin.last n) :
    addLastCoord x z i = x i := by
  simp [addLastCoord, hi]

lemma last_coord_without {n : ℕ} (x : Fin (n + 1) → ℤ) :
    addLastCoord (withoutLastCoord x) (x (Fin.last n)) = x := by
  funext i
  by_cases hi : i = Fin.last n
  · subst i
    simp [addLastCoord, withoutLastCoord]
  · simp [addLastCoord, withoutLastCoord, hi]

lemma last_snoc_init {n : ℕ} (x : Fin (n + 1) → ℤ) :
    addLastCoord (Fin.snoc (Fin.init x) 0) (x (Fin.last n)) = x := by
  funext i
  cases i using Fin.lastCases with
  | last => simp [addLastCoord]
  | cast i => simp [addLastCoord, Fin.init_def]

/-- Zero out the first coordinate of a tuple. -/
def withoutFirstCoord {n : ℕ} (x : Fin (n + 1) → ℤ) : Fin (n + 1) → ℤ :=
  fun i => if i = 0 then 0 else x i

@[simp]
lemma without_first_coord {n : ℕ} (x : Fin (n + 1) → ℤ) :
    withoutFirstCoord x 0 = 0 := by
  simp [withoutFirstCoord]

@[simp]
lemma without_coord_ne {n : ℕ} (x : Fin (n + 1) → ℤ)
    {i : Fin (n + 1)} (hi : i ≠ 0) :
    withoutFirstCoord x i = x i := by
  simp [withoutFirstCoord, hi]

/-- Insert a zero in the second coordinate of a tuple. -/
def insertSecondCoord {n : ℕ} (x : Fin (n + 1) → ℤ) : Fin (n + 2) → ℤ :=
  Fin.cases (x 0) (Fin.cases 0 (fun i : Fin n => x (Fin.succ i)))

/-- Delete the second coordinate of a tuple. -/
def deleteSecondCoord {n : ℕ} (x : Fin (n + 2) → ℤ) : Fin (n + 1) → ℤ :=
  fun i => x ((1 : Fin (n + 2)).succAbove i)

@[simp]
lemma insert_second_one {n : ℕ} (x : Fin (n + 1) → ℤ) :
    insertSecondCoord x 1 = 0 :=
  rfl

@[simp]
lemma insert_second_above {n : ℕ}
    (x : Fin (n + 1) → ℤ) (i : Fin (n + 1)) :
    insertSecondCoord x ((1 : Fin (n + 2)).succAbove i) = x i := by
  cases i using Fin.cases with
  | zero => rfl
  | succ i => rfl

lemma insert_second_delete {n : ℕ}
    (x : Fin (n + 2) → ℤ) (hx : x 1 = 0) :
    insertSecondCoord (deleteSecondCoord x) = x := by
  funext i
  cases i using Fin.cases with
  | zero => rfl
  | succ i =>
      cases i using Fin.cases with
      | zero => simpa [insertSecondCoord, deleteSecondCoord] using hx.symm
      | succ i => rfl

/--
Class-two collection for a single relation.  If `B * A = A * B * C` and the
correction term `C` commutes with both generators, then all integer powers
collect with correction exponent `u * v`.
-/
lemma zpow_mul_central
    {G : Type*} [Group G] {A B C : G}
    (hCA : Commute C A) (hCB : Commute C B)
    (hBA : B * A = A * B * C) (u v : ℤ) :
    B ^ u * A ^ v = A ^ v * B ^ u * C ^ (u * v) := by
  have hstep : B * A ^ v = A ^ v * B * C ^ v := by
    have hsem : SemiconjBy B A (A * C) := by
      change B * A = (A * C) * B
      calc
        B * A = A * B * C := hBA
        _ = A * (B * C) := by group
        _ = A * (C * B) := by rw [hCB.eq]
        _ = (A * C) * B := by group
    have hv := hsem.zpow_right v
    calc
      B * A ^ v = (A * C) ^ v * B := hv.eq
      _ = (A ^ v * C ^ v) * B := by rw [(hCA.symm).mul_zpow]
      _ = A ^ v * (C ^ v * B) := by group
      _ = A ^ v * (B * C ^ v) := by rw [(hCB.zpow_left v).eq]
      _ = A ^ v * B * C ^ v := by group
  have hstep_inv : B⁻¹ * A ^ v = A ^ v * B⁻¹ * C ^ (-v) := by
    apply mul_left_cancel (a := B)
    have htarget : B * (A ^ v * B⁻¹ * C ^ (-v)) = A ^ v := by
      calc
        B * (A ^ v * B⁻¹ * C ^ (-v)) =
            (B * A ^ v) * B⁻¹ * C ^ (-v) := by group
        _ = (A ^ v * B * C ^ v) * B⁻¹ * C ^ (-v) := by rw [hstep]
        _ = A ^ v * B * (C ^ v * B⁻¹) * C ^ (-v) := by group
        _ = A ^ v * B * (B⁻¹ * C ^ v) * C ^ (-v) := by
          rw [((hCB.zpow_left v).inv_right).eq]
        _ = A ^ v * (C ^ v * C ^ (-v)) := by group
        _ = A ^ v := by
          rw [← zpow_add]
          simp
    calc
      B * (B⁻¹ * A ^ v) = A ^ v := by group
      _ = B * (A ^ v * B⁻¹ * C ^ (-v)) := htarget.symm
  induction u using Int.induction_on with
  | zero => simp
  | succ m ih =>
      conv_lhs => rw [zpow_add_one]
      calc
        (B ^ (m : ℤ) * B) * A ^ v =
            B ^ (m : ℤ) * (B * A ^ v) := by group
        _ = B ^ (m : ℤ) * (A ^ v * B * C ^ v) := by rw [hstep]
        _ = (B ^ (m : ℤ) * A ^ v) * B * C ^ v := by group
        _ = (A ^ v * B ^ (m : ℤ) * C ^ ((m : ℤ) * v)) * B * C ^ v := by
          rw [ih]
        _ = A ^ v * B ^ (m : ℤ) * (C ^ ((m : ℤ) * v) * B) * C ^ v := by
          group
        _ = A ^ v * B ^ (m : ℤ) *
              (B * C ^ ((m : ℤ) * v)) * C ^ v := by
          rw [((hCB.zpow_left ((m : ℤ) * v))).eq]
        _ = A ^ v * (B ^ (m : ℤ) * B) *
              (C ^ ((m : ℤ) * v) * C ^ v) := by group
        _ = A ^ v * B ^ ((m : ℤ) + 1) *
              C ^ (((m : ℤ) + 1) * v) := by
          rw [show C ^ ((m : ℤ) * v) * C ^ v =
              C ^ (((m : ℤ) + 1) * v) by
            rw [← zpow_add]
            congr 1
            ring]
          rw [zpow_add_one]
  | pred m ih =>
      conv_lhs => rw [zpow_sub_one]
      calc
        (B ^ (-(m : ℤ)) * B⁻¹) * A ^ v =
            B ^ (-(m : ℤ)) * (B⁻¹ * A ^ v) := by group
        _ = B ^ (-(m : ℤ)) * (A ^ v * B⁻¹ * C ^ (-v)) := by
          rw [hstep_inv]
        _ = (B ^ (-(m : ℤ)) * A ^ v) * B⁻¹ * C ^ (-v) := by group
        _ = (A ^ v * B ^ (-(m : ℤ)) * C ^ ((-(m : ℤ)) * v)) *
              B⁻¹ * C ^ (-v) := by
          rw [ih]
        _ = A ^ v * B ^ (-(m : ℤ)) *
              (C ^ ((-(m : ℤ)) * v) * B⁻¹) * C ^ (-v) := by group
        _ = A ^ v * B ^ (-(m : ℤ)) *
              (B⁻¹ * C ^ ((-(m : ℤ)) * v)) * C ^ (-v) := by
          rw [((hCB.zpow_left ((-(m : ℤ)) * v))).inv_right.eq]
        _ = A ^ v * (B ^ (-(m : ℤ)) * B⁻¹) *
              (C ^ ((-(m : ℤ)) * v) * C ^ (-v)) := by group
        _ = A ^ v * B ^ (-(m : ℤ) - 1) *
              C ^ ((-(m : ℤ) - 1) * v) := by
          rw [show C ^ ((-(m : ℤ)) * v) * C ^ (-v) =
              C ^ ((-(m : ℤ) - 1) * v) by
            rw [← zpow_add]
            congr 1
            ring]
          rw [zpow_sub_one]

/-- The integer-valued quadratic binomial coefficient `z choose 2`. -/
def chooseTwoInt (z : ℤ) : ℤ :=
  z * (z - 1) / 2

lemma choose_int_succ (z : ℤ) :
    chooseTwoInt (z + 1) = chooseTwoInt z + z := by
  unfold chooseTwoInt
  rw [show (z + 1) * (z + 1 - 1) = z * (z - 1) + 2 * z by ring]
  rw [Int.add_ediv_of_dvd_right
    (show (2 : ℤ) ∣ 2 * z by exact ⟨z, by ring⟩)]
  rw [Int.mul_ediv_cancel_left z (by decide : (2 : ℤ) ≠ 0)]

lemma choose_int_pred (z : ℤ) :
    chooseTwoInt (z - 1) = chooseTwoInt z - (z - 1) := by
  unfold chooseTwoInt
  rw [show (z - 1) * (z - 1 - 1) =
    z * (z - 1) + 2 * (-(z - 1)) by ring]
  rw [Int.add_ediv_of_dvd_right
    (show (2 : ℤ) ∣ 2 * (-(z - 1)) by exact ⟨-(z - 1), by ring⟩)]
  rw [Int.mul_ediv_cancel_left (-(z - 1)) (by decide : (2 : ℤ) ≠ 0)]
  ring

lemma choose_cast_rat (z : ℤ) :
    ((chooseTwoInt z : ℤ) : ℚ) = (z : ℚ) * ((z : ℚ) - 1) / 2 := by
  unfold chooseTwoInt
  rw [Int.cast_div (show (2 : ℤ) ∣ z * (z - 1) by
    exact even_iff_two_dvd.mp (Int.even_mul_pred_self z))
    (by norm_num : ((2 : ℤ) : ℚ) ≠ 0)]
  norm_num

/--
One-sided collection across a two-step tail.  If `B * A` produces a `C^p`
tail and `C * A` produces the central correction `Z^r`, then collecting
`B * A^v` has the expected quadratic central term.
-/
lemma mul_zpow_central
    {G : Type*} [Group G] {A B C Z : G} {p q r : ℤ}
    (hZA : Commute Z A) (hZC : Commute Z C)
    (hBA : B * A = A * B * C ^ p * Z ^ q)
    (hCA : C * A = A * C * Z ^ r) (v : ℤ) :
    B * A ^ v =
      A ^ v * B * C ^ (p * v) * Z ^ (q * v + p * r * chooseTwoInt v) := by
  have hcollectCA : ∀ s t : ℤ,
      C ^ s * A ^ t = A ^ t * C ^ s * Z ^ (r * (s * t)) := by
    intro s t
    have h := zpow_mul_central
      (A := A) (B := C) (C := Z ^ r)
      (hZA.zpow_left r) (hZC.zpow_left r) hCA s t
    rw [h]
    rw [← zpow_mul]
  have hsucc : ∀ z : ℤ,
      B * C ^ (p * z) * Z ^ (q * z + p * r * chooseTwoInt z) * A =
        A * B * C ^ (p * (z + 1)) *
          Z ^ (q * (z + 1) + p * r * chooseTwoInt (z + 1)) := by
    intro z
    let e : ℤ := q * z + p * r * chooseTwoInt z
    have hCA1 : C ^ (p * z) * A =
        A * C ^ (p * z) * Z ^ (r * ((p * z) * 1)) := by
      simpa using hcollectCA (p * z) 1
    calc
      B * C ^ (p * z) * Z ^ e * A =
          B * (C ^ (p * z) * A) * Z ^ e := by
            rw [show B * C ^ (p * z) * Z ^ e * A =
                B * C ^ (p * z) * (Z ^ e * A) by group]
            rw [(hZA.zpow_left e).eq]
            group
      _ = B * (A * C ^ (p * z) * Z ^ (r * ((p * z) * 1))) *
            Z ^ e := by
            rw [hCA1]
      _ = (B * A) * C ^ (p * z) * Z ^ (r * ((p * z) * 1)) *
            Z ^ e := by group
      _ = (A * B * C ^ p * Z ^ q) * C ^ (p * z) *
            Z ^ (r * ((p * z) * 1)) * Z ^ e := by rw [hBA]
      _ = A * B * (C ^ p * C ^ (p * z)) *
            (Z ^ q * Z ^ (r * ((p * z) * 1)) * Z ^ e) := by
            have hqC : Commute (Z ^ q) (C ^ (p * z)) :=
              (hZC.zpow_left q).zpow_right (p * z)
            calc
              (A * B * C ^ p * Z ^ q) * C ^ (p * z) *
                  Z ^ (r * ((p * z) * 1)) * Z ^ e =
                A * B * C ^ p * (Z ^ q * C ^ (p * z)) *
                  Z ^ (r * ((p * z) * 1)) * Z ^ e := by group
              _ = A * B * C ^ p * (C ^ (p * z) * Z ^ q) *
                  Z ^ (r * ((p * z) * 1)) * Z ^ e := by rw [hqC.eq]
              _ = A * B * (C ^ p * C ^ (p * z)) *
                  (Z ^ q * Z ^ (r * ((p * z) * 1)) * Z ^ e) := by group
      _ = A * B * C ^ (p * (z + 1)) *
            Z ^ (q * (z + 1) + p * r * chooseTwoInt (z + 1)) := by
            rw [← zpow_add, ← zpow_add, ← zpow_add]
            rw [choose_int_succ]
            rw [show p + p * z = p * (z + 1) by ring]
            rw [show q + r * (p * z * 1) + e =
                q * (z + 1) + p * r * (chooseTwoInt z + z) by
              simp [e]
              ring]
  have hpred : ∀ z : ℤ,
      B * C ^ (p * z) * Z ^ (q * z + p * r * chooseTwoInt z) * A⁻¹ =
        A⁻¹ * B * C ^ (p * (z - 1)) *
          Z ^ (q * (z - 1) + p * r * chooseTwoInt (z - 1)) := by
    intro z
    let e : ℤ := q * z + p * r * chooseTwoInt z
    have hbase : B * C ^ p * Z ^ q * A⁻¹ = A⁻¹ * B := by
      have hcalc :
          (B * C ^ p * Z ^ q * A⁻¹) * A = (A⁻¹ * B) * A := by
        calc
          (B * C ^ p * Z ^ q * A⁻¹) * A = B * C ^ p * Z ^ q := by
            group
          _ = A⁻¹ * (A * B * C ^ p * Z ^ q) := by group
          _ = A⁻¹ * (B * A) := by rw [hBA]
          _ = (A⁻¹ * B) * A := by group
      exact mul_right_cancel hcalc
    have hCAm1 : C ^ (p * (z - 1)) * A⁻¹ =
        A⁻¹ * C ^ (p * (z - 1)) *
          Z ^ (r * (p * (z - 1) * (-1))) := by
      simpa using hcollectCA (p * (z - 1)) (-1)
    calc
      B * C ^ (p * z) * Z ^ e * A⁻¹ =
          B * C ^ p * Z ^ q * (C ^ (p * (z - 1)) *
            Z ^ (e - q) * A⁻¹) := by
            have hsplitC : C ^ (p * z) = C ^ p * C ^ (p * (z - 1)) := by
              rw [← zpow_add]
              rw [show p + p * (z - 1) = p * z by ring]
            have hsplitZ : Z ^ e = Z ^ q * Z ^ (e - q) := by
              rw [← zpow_add]
              rw [show q + (e - q) = e by ring]
            have hcz : Commute (Z ^ q) (C ^ (p * (z - 1))) :=
              (hZC.zpow_left _).zpow_right _
            rw [hsplitC, hsplitZ]
            calc
              B * (C ^ p * C ^ (p * (z - 1))) *
                  (Z ^ q * Z ^ (e - q)) * A⁻¹ =
                B * C ^ p * (C ^ (p * (z - 1)) * Z ^ q) *
                  Z ^ (e - q) * A⁻¹ := by group
              _ = B * C ^ p * (Z ^ q * C ^ (p * (z - 1))) *
                  Z ^ (e - q) * A⁻¹ := by rw [hcz.eq]
              _ = B * C ^ p * Z ^ q *
                  (C ^ (p * (z - 1)) * Z ^ (e - q) * A⁻¹) := by
                    group
      _ = B * C ^ p * Z ^ q *
            (A⁻¹ * C ^ (p * (z - 1)) *
              Z ^ (r * (p * (z - 1) * (-1)) + (e - q))) := by
            rw [show C ^ (p * (z - 1)) * Z ^ (e - q) * A⁻¹ =
                C ^ (p * (z - 1)) * A⁻¹ * Z ^ (e - q) by
              have hzA : Commute (Z ^ (e - q)) A⁻¹ :=
                (hZA.zpow_left _).inv_right
              calc
                C ^ (p * (z - 1)) * Z ^ (e - q) * A⁻¹ =
                    C ^ (p * (z - 1)) * (Z ^ (e - q) * A⁻¹) := by
                    group
                _ = C ^ (p * (z - 1)) * (A⁻¹ * Z ^ (e - q)) := by
                    rw [hzA.eq]
                _ = C ^ (p * (z - 1)) * A⁻¹ * Z ^ (e - q) := by group]
            rw [hCAm1]
            rw [show A⁻¹ * C ^ (p * (z - 1)) *
                Z ^ (r * (p * (z - 1) * (-1))) * Z ^ (e - q) =
                A⁻¹ * C ^ (p * (z - 1)) *
                  Z ^ (r * (p * (z - 1) * (-1)) + (e - q)) by
              calc
                A⁻¹ * C ^ (p * (z - 1)) *
                    Z ^ (r * (p * (z - 1) * (-1))) * Z ^ (e - q) =
                  A⁻¹ * C ^ (p * (z - 1)) *
                    (Z ^ (r * (p * (z - 1) * (-1))) * Z ^ (e - q)) := by
                    group
                _ = A⁻¹ * C ^ (p * (z - 1)) *
                    Z ^ (r * (p * (z - 1) * (-1)) + (e - q)) := by
                    rw [zpow_add]]
      _ = (B * C ^ p * Z ^ q * A⁻¹) * C ^ (p * (z - 1)) *
            Z ^ (r * (p * (z - 1) * (-1)) + (e - q)) := by group
      _ = A⁻¹ * B * C ^ (p * (z - 1)) *
          Z ^ (q * (z - 1) + p * r * chooseTwoInt (z - 1)) := by
            rw [hbase]
            rw [choose_int_pred]
            rw [show r * (p * (z - 1) * (-1)) + (e - q) =
                q * (z - 1) + p * r * (chooseTwoInt z - (z - 1)) by
              simp [e]
              ring]
  induction v using Int.induction_on with
  | zero => simp [chooseTwoInt]
  | succ m ih =>
      conv_lhs => rw [zpow_add_one]
      calc
        B * (A ^ (m : ℤ) * A) = (B * A ^ (m : ℤ)) * A := by group
        _ = (A ^ (m : ℤ) * B * C ^ (p * (m : ℤ)) *
              Z ^ (q * (m : ℤ) + p * r * chooseTwoInt (m : ℤ))) * A := by
              rw [ih]
        _ = A ^ (m : ℤ) * (B * C ^ (p * (m : ℤ)) *
              Z ^ (q * (m : ℤ) + p * r * chooseTwoInt (m : ℤ)) * A) := by
              group
        _ = A ^ (m : ℤ) * (A * B * C ^ (p * ((m : ℤ) + 1)) *
              Z ^ (q * ((m : ℤ) + 1) +
                p * r * chooseTwoInt ((m : ℤ) + 1))) := by
              rw [hsucc]
        _ = A ^ ((m : ℤ) + 1) * B * C ^ (p * ((m : ℤ) + 1)) *
              Z ^ (q * ((m : ℤ) + 1) +
                p * r * chooseTwoInt ((m : ℤ) + 1)) := by
              rw [zpow_add_one]
              group
  | pred m ih =>
      conv_lhs => rw [zpow_sub_one]
      calc
        B * (A ^ (-(m : ℤ)) * A⁻¹) =
            (B * A ^ (-(m : ℤ))) * A⁻¹ := by group
        _ = (A ^ (-(m : ℤ)) * B * C ^ (p * (-(m : ℤ))) *
              Z ^ (q * (-(m : ℤ)) + p * r * chooseTwoInt (-(m : ℤ)))) *
              A⁻¹ := by
              rw [ih]
        _ = A ^ (-(m : ℤ)) * (B * C ^ (p * (-(m : ℤ))) *
              Z ^ (q * (-(m : ℤ)) + p * r * chooseTwoInt (-(m : ℤ))) *
              A⁻¹) := by group
        _ = A ^ (-(m : ℤ)) * (A⁻¹ * B * C ^ (p * (-(m : ℤ) - 1)) *
              Z ^ (q * (-(m : ℤ) - 1) +
                p * r * chooseTwoInt (-(m : ℤ) - 1))) := by
              rw [hpred]
        _ = A ^ (-(m : ℤ) - 1) * B * C ^ (p * (-(m : ℤ) - 1)) *
              Z ^ (q * (-(m : ℤ) - 1) +
                p * r * chooseTwoInt (-(m : ℤ) - 1)) := by
              rw [zpow_sub_one]
              group

/-- Central exponent in the two-step rank-four-style collection formula. -/
def twoStepExponent (p q r s u v : ℤ) : ℤ :=
  q * (u * v) + p * r * u * chooseTwoInt v + p * s * v * chooseTwoInt u

/--
Full two-step collection.  The parameters describe
`B * A = A * B * C^p * Z^q`, `C * A = A * C * Z^r`, and
`C * B = B * C * Z^s`, with `Z` central against the displayed generators.
-/
lemma zpow_step_central
    {G : Type*} [Group G] {A B C Z : G} {p q r s : ℤ}
    (hZA : Commute Z A) (hZB : Commute Z B) (hZC : Commute Z C)
    (hBA : B * A = A * B * C ^ p * Z ^ q)
    (hCA : C * A = A * C * Z ^ r)
    (hCB : C * B = B * C * Z ^ s) (u v : ℤ) :
    B ^ u * A ^ v =
      A ^ v * B ^ u * C ^ (p * (u * v)) *
        Z ^ (twoStepExponent p q r s u v) := by
  have hB : B * A ^ v =
      A ^ v * B * C ^ (p * v) * Z ^ (q * v + p * r * chooseTwoInt v) :=
    mul_zpow_central hZA hZC hBA hCA v
  have hcollectCB : ∀ d t : ℤ,
      C ^ d * B ^ t = B ^ t * C ^ d * Z ^ (s * (d * t)) := by
    intro d t
    have h := zpow_mul_central
      (A := B) (B := C) (C := Z ^ s)
      (hZB.zpow_left s) (hZC.zpow_left s) hCB d t
    rw [h]
    rw [← zpow_mul]
  have hBinv : B⁻¹ * A ^ v =
      A ^ v * B⁻¹ * C ^ (-(p * v)) *
        Z ^ (-(q * v + p * r * chooseTwoInt v) + s * (p * v)) := by
    let a : ℤ := p * v
    let b : ℤ := q * v + p * r * chooseTwoInt v
    apply mul_left_cancel (a := B)
    calc
      B * (B⁻¹ * A ^ v) = A ^ v := by group
      _ = B * (A ^ v * B⁻¹ * C ^ (-a) * Z ^ (-b + s * a)) := by
        symm
        calc
          B * (A ^ v * B⁻¹ * C ^ (-a) * Z ^ (-b + s * a)) =
              (B * A ^ v) * B⁻¹ * C ^ (-a) * Z ^ (-b + s * a) := by
                group
          _ = (A ^ v * B * C ^ a * Z ^ b) * B⁻¹ * C ^ (-a) *
                Z ^ (-b + s * a) := by
                rw [show B * A ^ v = A ^ v * B * C ^ a * Z ^ b by
                  simpa [a, b] using hB]
          _ = A ^ v * B * C ^ a * (Z ^ b * B⁻¹) * C ^ (-a) *
                Z ^ (-b + s * a) := by group
          _ = A ^ v * B * C ^ a * (B⁻¹ * Z ^ b) * C ^ (-a) *
                Z ^ (-b + s * a) := by
                rw [((hZB.zpow_left b).inv_right).eq]
          _ = A ^ v * B * (C ^ a * B⁻¹) * Z ^ b * C ^ (-a) *
                Z ^ (-b + s * a) := by group
          _ = A ^ v * B * (B⁻¹ * C ^ a * Z ^ (s * (a * (-1)))) *
                Z ^ b * C ^ (-a) * Z ^ (-b + s * a) := by
                have hCBinv : C ^ a * B⁻¹ =
                    B⁻¹ * C ^ a * Z ^ (s * (a * (-1))) := by
                  simpa using hcollectCB a (-1)
                rw [hCBinv]
          _ = A ^ v * (C ^ a * C ^ (-a)) *
                (Z ^ (s * (a * (-1))) * Z ^ b * Z ^ (-b + s * a)) := by
                have hzc :
                    Commute (Z ^ (s * (a * (-1))) * Z ^ b) (C ^ (-a)) :=
                  Commute.mul_left
                    ((hZC.zpow_left (s * (a * (-1)))).zpow_right (-a))
                    ((hZC.zpow_left b).zpow_right (-a))
                calc
                  A ^ v * B * (B⁻¹ * C ^ a * Z ^ (s * (a * (-1)))) *
                      Z ^ b * C ^ (-a) * Z ^ (-b + s * a) =
                    A ^ v * C ^ a *
                      ((Z ^ (s * (a * (-1))) * Z ^ b) * C ^ (-a)) *
                      Z ^ (-b + s * a) := by group
                  _ = A ^ v * C ^ a *
                      (C ^ (-a) * (Z ^ (s * (a * (-1))) * Z ^ b)) *
                      Z ^ (-b + s * a) := by rw [hzc.eq]
                  _ = A ^ v * (C ^ a * C ^ (-a)) *
                      (Z ^ (s * (a * (-1))) * Z ^ b * Z ^ (-b + s * a)) := by
                      group
          _ = A ^ v := by
                rw [← zpow_add]
                rw [show a + -a = 0 by ring]
                simp only [zpow_zero, mul_one]
                rw [← zpow_add, ← zpow_add]
                rw [show s * (a * (-1)) + b + (-b + s * a) = 0 by ring]
                simp
  induction u using Int.induction_on with
  | zero => simp [twoStepExponent, chooseTwoInt]
  | succ m ih =>
      let um : ℤ := m
      let d : ℤ := p * (um * v)
      let a : ℤ := p * v
      let e : ℤ := twoStepExponent p q r s um v
      let g : ℤ := q * v + p * r * chooseTwoInt v
      conv_lhs => rw [zpow_add_one]
      calc
        (B ^ um * B) * A ^ v = B ^ um * (B * A ^ v) := by group
        _ = B ^ um * (A ^ v * B * C ^ a * Z ^ g) := by
              rw [show B * A ^ v = A ^ v * B * C ^ a * Z ^ g by
                simpa [a, g] using hB]
        _ = (B ^ um * A ^ v) * B * C ^ a * Z ^ g := by group
        _ = (A ^ v * B ^ um * C ^ d * Z ^ e) * B * C ^ a * Z ^ g := by
              rw [show B ^ um * A ^ v = A ^ v * B ^ um * C ^ d * Z ^ e by
                simpa [um, d, e] using ih]
        _ = A ^ v * B ^ um * C ^ d * (Z ^ e * B) * C ^ a * Z ^ g := by
              group
        _ = A ^ v * B ^ um * C ^ d * (B * Z ^ e) * C ^ a * Z ^ g := by
              rw [(hZB.zpow_left e).eq]
        _ = A ^ v * B ^ um * (C ^ d * B) * Z ^ e * C ^ a * Z ^ g := by
              group
        _ = A ^ v * B ^ um * (B * C ^ d * Z ^ (s * (d * 1))) *
              Z ^ e * C ^ a * Z ^ g := by
              have hCBone : C ^ d * B = B * C ^ d * Z ^ (s * (d * 1)) := by
                simpa using hcollectCB d 1
              rw [hCBone]
        _ = A ^ v * (B ^ um * B) * (C ^ d * C ^ a) *
              (Z ^ (s * (d * 1)) * Z ^ e * Z ^ g) := by
              have hzc : Commute (Z ^ (s * (d * 1)) * Z ^ e) (C ^ a) :=
                Commute.mul_left
                  ((hZC.zpow_left (s * (d * 1))).zpow_right a)
                  ((hZC.zpow_left e).zpow_right a)
              calc
                A ^ v * B ^ um * (B * C ^ d * Z ^ (s * (d * 1))) *
                    Z ^ e * C ^ a * Z ^ g =
                  A ^ v * (B ^ um * B) * C ^ d *
                    ((Z ^ (s * (d * 1)) * Z ^ e) * C ^ a) * Z ^ g := by
                    group
                _ = A ^ v * (B ^ um * B) * C ^ d *
                    (C ^ a * (Z ^ (s * (d * 1)) * Z ^ e)) * Z ^ g := by
                    rw [hzc.eq]
                _ = A ^ v * (B ^ um * B) * (C ^ d * C ^ a) *
                    (Z ^ (s * (d * 1)) * Z ^ e * Z ^ g) := by group
        _ = A ^ v * B ^ (um + 1) * C ^ (p * ((um + 1) * v)) *
              Z ^ (twoStepExponent p q r s (um + 1) v) := by
              rw [zpow_add_one]
              rw [← zpow_add]
              rw [show d + a = p * ((um + 1) * v) by
                simp [d, a, um]
                ring]
              rw [← zpow_add, ← zpow_add]
              rw [show s * (d * 1) + e + g =
                  twoStepExponent p q r s (um + 1) v by
                simp [d, e, g, twoStepExponent, um, choose_int_succ]
                ring]
  | pred m ih =>
      let um : ℤ := -(m : ℤ)
      let d : ℤ := p * (um * v)
      let a : ℤ := p * v
      let e : ℤ := twoStepExponent p q r s um v
      let ginv : ℤ := -(q * v + p * r * chooseTwoInt v) + s * (p * v)
      conv_lhs => rw [zpow_sub_one]
      calc
        (B ^ um * B⁻¹) * A ^ v = B ^ um * (B⁻¹ * A ^ v) := by group
        _ = B ^ um * (A ^ v * B⁻¹ * C ^ (-a) * Z ^ ginv) := by
              rw [show B⁻¹ * A ^ v = A ^ v * B⁻¹ * C ^ (-a) * Z ^ ginv by
                simpa [a, ginv] using hBinv]
        _ = (B ^ um * A ^ v) * B⁻¹ * C ^ (-a) * Z ^ ginv := by group
        _ = (A ^ v * B ^ um * C ^ d * Z ^ e) *
              B⁻¹ * C ^ (-a) * Z ^ ginv := by
              rw [show B ^ um * A ^ v = A ^ v * B ^ um * C ^ d * Z ^ e by
                simpa [um, d, e] using ih]
        _ = A ^ v * B ^ um * C ^ d * (Z ^ e * B⁻¹) *
              C ^ (-a) * Z ^ ginv := by group
        _ = A ^ v * B ^ um * C ^ d * (B⁻¹ * Z ^ e) *
              C ^ (-a) * Z ^ ginv := by
              rw [((hZB.zpow_left e).inv_right).eq]
        _ = A ^ v * B ^ um * (C ^ d * B⁻¹) * Z ^ e *
              C ^ (-a) * Z ^ ginv := by group
        _ = A ^ v * B ^ um * (B⁻¹ * C ^ d * Z ^ (s * (d * (-1)))) *
              Z ^ e * C ^ (-a) * Z ^ ginv := by
              have hCBinv : C ^ d * B⁻¹ =
                  B⁻¹ * C ^ d * Z ^ (s * (d * (-1))) := by
                simpa using hcollectCB d (-1)
              rw [hCBinv]
        _ = A ^ v * (B ^ um * B⁻¹) * (C ^ d * C ^ (-a)) *
              (Z ^ (s * (d * (-1))) * Z ^ e * Z ^ ginv) := by
              have hzc : Commute (Z ^ (s * (d * (-1))) * Z ^ e) (C ^ (-a)) :=
                Commute.mul_left
                  ((hZC.zpow_left (s * (d * (-1)))).zpow_right (-a))
                  ((hZC.zpow_left e).zpow_right (-a))
              calc
                A ^ v * B ^ um * (B⁻¹ * C ^ d * Z ^ (s * (d * (-1)))) *
                    Z ^ e * C ^ (-a) * Z ^ ginv =
                  A ^ v * (B ^ um * B⁻¹) * C ^ d *
                    ((Z ^ (s * (d * (-1))) * Z ^ e) * C ^ (-a)) *
                    Z ^ ginv := by group
                _ = A ^ v * (B ^ um * B⁻¹) * C ^ d *
                    (C ^ (-a) * (Z ^ (s * (d * (-1))) * Z ^ e)) *
                    Z ^ ginv := by rw [hzc.eq]
                _ = A ^ v * (B ^ um * B⁻¹) * (C ^ d * C ^ (-a)) *
                    (Z ^ (s * (d * (-1))) * Z ^ e * Z ^ ginv) := by group
        _ = A ^ v * B ^ (um - 1) * C ^ (p * ((um - 1) * v)) *
              Z ^ (twoStepExponent p q r s (um - 1) v) := by
              rw [zpow_sub_one]
              rw [← zpow_add]
              rw [show d + -a = p * ((um - 1) * v) by
                simp [d, a, um]
                ring]
              rw [← zpow_add, ← zpow_add]
              rw [show s * (d * (-1)) + e + ginv =
                  twoStepExponent p q r s (um - 1) v by
                simp [d, e, ginv, twoStepExponent, um, choose_int_pred]
                ring]

namespace CPres

variable {n : ℕ} {T : ParameterIndex n → ℤ}
variable (M : CPres n T)

/-- The coordinate tuple of `a^x a^y`. -/
noncomputable def multiplicationTuple (x y : Fin n → ℤ) : Fin n → ℤ :=
  M.coord (M.normalWord x * M.normalWord y)

/-- The `i`th multiplication coordinate function. -/
noncomputable def multiplicationCoordinate (i : Fin n) (x y : Fin n → ℤ) : ℤ :=
  M.multiplicationTuple x y i

/-- The coordinate tuple of `(a^x)^z`. -/
noncomputable def poweringTuple (x : Fin n → ℤ) (z : ℤ) : Fin n → ℤ :=
  M.coord (M.normalWord x ^ z)

/-- The `i`th powering coordinate function. -/
noncomputable def poweringCoordinate (i : Fin n) (x : Fin n → ℤ) (z : ℤ) : ℤ :=
  M.poweringTuple x z i

/-- The coordinate tuple of `a_j^u a_i^v`. -/
noncomputable def conjugationTuple (i j : Fin n) (u v : ℤ) : Fin n → ℤ :=
  M.coord (M.gen j ^ u * M.gen i ^ v)

/-- The coordinate tuple of the conjugated word `a_i^{-v} a_j^u a_i^v`. -/
noncomputable def leftConjugationTuple (i j : Fin n) (u v : ℤ) : Fin n → ℤ :=
  M.coord (M.gen i ^ (-v) * M.gen j ^ u * M.gen i ^ v)

/-- The `k`th conjugation coordinate function. -/
noncomputable def conjugationCoordinate
    (i j k : Fin n) (u v : ℤ) : ℤ :=
  M.conjugationTuple i j u v k

lemma normal_multiplication_tuple (x y : Fin n → ℤ) :
    M.normalWord (M.multiplicationTuple x y) =
      M.normalWord x * M.normalWord y :=
  M.normalWord_coord (M.normalWord x * M.normalWord y)

lemma normal_powering_tuple (x : Fin n → ℤ) (z : ℤ) :
    M.normalWord (M.poweringTuple x z) = M.normalWord x ^ z :=
  M.normalWord_coord (M.normalWord x ^ z)

lemma word_conjugation_tuple (i j : Fin n) (u v : ℤ) :
    M.normalWord (M.conjugationTuple i j u v) =
      M.gen j ^ u * M.gen i ^ v :=
  M.normalWord_coord (M.gen j ^ u * M.gen i ^ v)

lemma normal_conjugation_tuple (i j : Fin n) (u v : ℤ) :
    M.normalWord (M.leftConjugationTuple i j u v) =
      M.gen i ^ (-v) * M.gen j ^ u * M.gen i ^ v :=
  M.normalWord_coord (M.gen i ^ (-v) * M.gen j ^ u * M.gen i ^ v)

lemma normal_single_coord (i : Fin n) (z : ℤ) :
    M.normalWord (singleCoord i z) = M.gen i ^ z := by
  simp [CPres.normalWord, ordered_z_single]

lemma upper_indices_single {G : Type*} [Monoid G]
    {n : ℕ} {i j : Fin n} (hij : i < j) (b : G) :
    ((upperIndices i).map fun k => if k.1 = j then b else 1).prod = b := by
  unfold upperIndices
  rw [list_filter_dite
    (p := fun k : Fin n => i < k)
    (f := fun k h => (⟨k, h⟩ : {k : Fin n // i < k}))
    (g := fun k : {k : Fin n // i < k} => if k.1 = j then b else 1)]
  rw [List.prod_map_eq_pow_single j]
  · rw [List.count_finRange]
    simp [hij]
  · intro k hkj _hk
    by_cases hik : i < k
    · simp [hik, hkj]
    · simp [hik]

lemma normal_two_coord
    (i j : Fin n) (hij : i < j) (v u : ℤ) :
    M.normalWord (fun k => if k = i then v else if k = j then u else 0) =
      M.gen i ^ v * M.gen j ^ u := by
  change
    ((List.finRange n).map fun k =>
      M.gen k ^ (if k = i then v else if k = j then u else 0)).prod =
        M.gen i ^ v * M.gen j ^ u
  have hmap :
      (List.finRange n).map
          (fun k =>
            M.gen k ^ (if k = i then v else if k = j then u else 0)) =
        (List.finRange n).map
          (fun k =>
            if _h : k = i then M.gen i ^ v
            else if _h : i < k then if k = j then M.gen j ^ u else 1
            else 1) := by
    apply List.map_congr_left
    intro k _hk
    by_cases hki : k = i
    · subst k
      simp
    · by_cases hkj : k = j
      · subst k
        simp [hki, hij]
      · by_cases hik : i < k
        · simp [hki, hkj, hik]
        · simp [hki, hkj, hik]
  rw [hmap]
  rw [list_single_upper i (M.gen i ^ v)
    (fun k _hk => if k = j then M.gen j ^ u else 1)]
  rw [upper_indices_single hij]

lemma coord_gen_zpow (i : Fin n) (z : ℤ) :
    M.coord (M.gen i ^ z) = singleCoord i z := by
  rw [← normal_single_coord]
  exact M.coord_normalWord _

lemma coord_gen (i : Fin n) :
    M.coord (M.gen i) = singleCoord i 1 := by
  simpa using M.coord_gen_zpow i 1

@[simp]
lemma conjugation_tuple_right (i j : Fin n) (u : ℤ) :
    M.conjugationTuple i j u 0 = singleCoord j u := by
  change M.coord (M.gen j ^ u * M.gen i ^ (0 : ℤ)) = singleCoord j u
  simp [M.coord_gen_zpow]

@[simp]
lemma conjugation_tuple_left (i j : Fin n) (v : ℤ) :
    M.conjugationTuple i j 0 v = singleCoord i v := by
  change M.coord (M.gen j ^ (0 : ℤ) * M.gen i ^ v) = singleCoord i v
  simp [M.coord_gen_zpow]

/--
The carrier cut out by one zero coordinate is closed under the group
operations.  This is the semantic hypothesis needed for the subgroup steps
`U(T)` and `V(T)` in Section 3.1.
-/
def CoordinateZeroClosed {n : ℕ} {T : ParameterIndex n → ℤ}
    (M : CPres n T) (i : Fin n) : Prop :=
  (∀ a b : M.G,
    M.coord a i = 0 → M.coord b i = 0 → M.coord (a * b) i = 0) ∧
  (∀ a : M.G, M.coord a i = 0 → M.coord a⁻¹ i = 0)

/--
Coordinate-level form of zero-coordinate closure.  This says the semantic
multiplication and inverse coordinate functions preserve the zero fiber of
coordinate `i`.
-/
def CoordinateTupleClosed {n : ℕ} {T : ParameterIndex n → ℤ}
    (M : CPres n T) (i : Fin n) : Prop :=
  (∀ x y : Fin n → ℤ,
    x i = 0 → y i = 0 → M.multiplicationTuple x y i = 0) ∧
  (∀ x : Fin n → ℤ, x i = 0 → M.poweringTuple x (-1) i = 0)

/--
A coordinate is additive if it is a homomorphism from the ambient group to
the additive group of integers.  For the Section 3.1 subgroup steps, this is
the precise semantic fact that implies the zero-coordinate carrier is a
subgroup.
-/
def CoordinateAdditive {n : ℕ} {T : ParameterIndex n → ℤ}
    (M : CPres n T) (i : Fin n) : Prop :=
  ∀ a b : M.G, M.coord (a * b) i = M.coord a i + M.coord b i

lemma coord_one {n : ℕ} {T : ParameterIndex n → ℤ}
    (M : CPres n T) (i : Fin n) :
    M.coord 1 i = 0 := by
  have h := congrFun (M.coord_normalWord (fun _ : Fin n => 0)) i
  simpa [M.normalWord_zero] using h

lemma additive_multiplication_tuple {n : ℕ}
    {T : ParameterIndex n → ℤ}
    (M : CPres n T) (i : Fin n) :
    CoordinateAdditive M i ↔
      ∀ x y : Fin n → ℤ, M.multiplicationTuple x y i = x i + y i := by
  constructor
  · intro h x y
    have hxy := h (M.normalWord x) (M.normalWord y)
    rw [M.coord_normalWord x, M.coord_normalWord y] at hxy
    simpa [multiplicationTuple] using hxy
  · intro h a b
    calc
      M.coord (a * b) i =
          M.coord (M.normalWord (M.coord a) * M.normalWord (M.coord b)) i := by
            rw [M.normalWord_coord a, M.normalWord_coord b]
      _ = M.multiplicationTuple (M.coord a) (M.coord b) i := rfl
      _ = M.coord a i + M.coord b i := h (M.coord a) (M.coord b)

theorem coordinate_closed_tuple {n : ℕ}
    {T : ParameterIndex n → ℤ}
    (M : CPres n T) (i : Fin n) :
    CoordinateZeroClosed M i ↔ CoordinateTupleClosed M i := by
  constructor
  · intro hClosed
    constructor
    · intro x y hx hy
      have h :=
        hClosed.1 (M.normalWord x) (M.normalWord y)
          (by rw [M.coord_normalWord]; exact hx)
          (by rw [M.coord_normalWord]; exact hy)
      simpa [multiplicationTuple] using h
    · intro x hx
      have h :=
        hClosed.2 (M.normalWord x)
          (by rw [M.coord_normalWord]; exact hx)
      simpa [poweringTuple] using h
  · intro hTuple
    constructor
    · intro a b ha hb
      have h :=
        hTuple.1 (M.coord a) (M.coord b) ha hb
      calc
        M.coord (a * b) i =
            M.multiplicationTuple (M.coord a) (M.coord b) i := by
              simp [multiplicationTuple, M.normalWord_coord]
        _ = 0 := h
    · intro a ha
      have h := hTuple.2 (M.coord a) ha
      calc
        M.coord a⁻¹ i =
            M.poweringTuple (M.coord a) (-1) i := by
              simp [poweringTuple, M.normalWord_coord]
        _ = 0 := h

theorem coordinate_closed_additive {n : ℕ}
    {T : ParameterIndex n → ℤ}
    (M : CPres n T) (i : Fin n)
    (hAdd : CoordinateAdditive M i) :
    CoordinateZeroClosed M i := by
  constructor
  · intro a b ha hb
    rw [hAdd a b, ha, hb, zero_add]
  · intro a ha
    have h := hAdd a a⁻¹
    rw [mul_inv_cancel, M.coord_one i, ha, zero_add] at h
    exact h.symm

lemma coord_inv_additive {n : ℕ} {T : ParameterIndex n → ℤ}
    (M : CPres n T) (i : Fin n)
    (hAdd : CoordinateAdditive M i) (a : M.G) :
    M.coord a⁻¹ i = -M.coord a i := by
  have h := hAdd a a⁻¹
  rw [mul_inv_cancel, M.coord_one i] at h
  omega

/-- A tail normal word, using all generators except the first one. -/
def tailNormalWord {n : ℕ} {T : ParameterIndex (n + 1) → ℤ}
    (M : CPres (n + 1) T) (x : Fin n → ℤ) : M.G :=
  orderedZPow (fun i : Fin n => M.gen (Fin.succ i)) x

lemma normal_cons_zero {n : ℕ} {T : ParameterIndex (n + 1) → ℤ}
    (M : CPres (n + 1) T) (x : Fin n → ℤ) :
    M.normalWord (Fin.cons 0 x) = M.tailNormalWord x := by
  change orderedZPow M.gen (Fin.cons 0 x) =
    orderedZPow (fun i : Fin n => M.gen (Fin.succ i)) x
  unfold orderedZPow
  rw [List.finRange_succ]
  simp [List.map_map, Function.comp_def]

lemma normalWord_cons {n : ℕ} {T : ParameterIndex (n + 1) → ℤ}
    (M : CPres (n + 1) T) (z : ℤ) (x : Fin n → ℤ) :
    M.normalWord (Fin.cons z x) = M.gen 0 ^ z * M.tailNormalWord x := by
  change orderedZPow M.gen (Fin.cons z x) =
    M.gen 0 ^ z * orderedZPow (fun i : Fin n => M.gen (Fin.succ i)) x
  unfold orderedZPow
  rw [List.finRange_succ]
  simp [List.map_map, Function.comp_def]

lemma coord_head_tail {n : ℕ} {T : ParameterIndex (n + 1) → ℤ}
    (M : CPres (n + 1) T) (z : ℤ) (x : Fin n → ℤ) :
    M.coord (M.gen 0 ^ z * M.tailNormalWord x) = Fin.cons z x := by
  rw [← M.normalWord_cons]
  exact M.coord_normalWord _

lemma coord_tail_normal {n : ℕ} {T : ParameterIndex (n + 1) → ℤ}
    (M : CPres (n + 1) T) (x : Fin n → ℤ) :
    M.coord (M.tailNormalWord x) = Fin.cons 0 x := by
  rw [← M.normal_cons_zero]
  exact M.coord_normalWord _

lemma coord_tail_zero {n : ℕ} {T : ParameterIndex (n + 1) → ℤ}
    (M : CPres (n + 1) T) (x : Fin n → ℤ) :
    M.coord (M.tailNormalWord x) 0 = 0 := by
  rw [M.coord_tail_normal]
  simp

lemma coord_tail_succ {n : ℕ} {T : ParameterIndex (n + 1) → ℤ}
    (M : CPres (n + 1) T) (x : Fin n → ℤ) (i : Fin n) :
    M.coord (M.tailNormalWord x) (Fin.succ i) = x i := by
  rw [M.coord_tail_normal]
  simp

lemma tail_normal_injective {n : ℕ} {T : ParameterIndex (n + 1) → ℤ}
    (M : CPres (n + 1) T) :
    Function.Injective M.tailNormalWord := by
  intro x y hxy
  have hfull : M.normalWord (Fin.cons 0 x) = M.normalWord (Fin.cons 0 y) := by
    rw [M.normal_cons_zero, M.normal_cons_zero]
    exact hxy
  have hcoord := M.normalWord_injective hfull
  simpa using congrArg Fin.tail hcoord

lemma normal_tail_first {n : ℕ}
    {T : ParameterIndex (n + 1) → ℤ}
    (M : CPres (n + 1) T) (x : Fin (n + 1) → ℤ)
    (hx : x 0 = 0) :
    M.normalWord x = M.tailNormalWord (Fin.tail x) := by
  have hcons : Fin.cons 0 (Fin.tail x) = x := by
    rw [show (0 : ℤ) = x 0 from hx.symm]
    exact Fin.cons_self_tail x
  rw [← M.normal_cons_zero]
  rw [hcons]

lemma without_coord_tail {n : ℕ}
    {T : ParameterIndex (n + 1) → ℤ}
    (M : CPres (n + 1) T) (x : Fin (n + 1) → ℤ) :
    M.normalWord (withoutFirstCoord x) = M.tailNormalWord (Fin.tail x) := by
  rw [M.normal_tail_first (withoutFirstCoord x) (by simp)]
  apply congrArg M.tailNormalWord
  funext i
  change withoutFirstCoord x (Fin.succ i) = x (Fin.succ i)
  exact without_coord_ne x (Fin.succ_ne_zero i)

lemma tail_coord_zero {n : ℕ}
    {T : ParameterIndex (n + 1) → ℤ}
    (M : CPres (n + 1) T) (g : M.G)
    (hg : M.coord g 0 = 0) :
    g = M.tailNormalWord (Fin.tail (M.coord g)) := by
  calc
    g = M.normalWord (M.coord g) := (M.normalWord_coord g).symm
    _ = M.tailNormalWord (Fin.tail (M.coord g)) :=
      M.normal_tail_first (M.coord g) hg

lemma coord_gen_mul {n : ℕ} {T : ParameterIndex (n + 1) → ℤ}
    (M : CPres (n + 1) T) (z : ℤ) (g : M.G)
    (hg : M.coord g 0 = 0) :
    M.coord (M.gen 0 ^ z * g) = Fin.cons z (Fin.tail (M.coord g)) := by
  calc
    M.coord (M.gen 0 ^ z * g)
        = M.coord (M.gen 0 ^ z * M.tailNormalWord (Fin.tail (M.coord g))) := by
          exact congrArg M.coord
            (congrArg (fun h : M.G => M.gen 0 ^ z * h)
              (M.tail_coord_zero g hg))
    _ = Fin.cons z (Fin.tail (M.coord g)) := by
          rw [M.coord_head_tail]

lemma coord_gen_succ {n : ℕ}
    {T : ParameterIndex (n + 1) → ℤ}
    (M : CPres (n + 1) T) (z : ℤ) (g : M.G)
    (hg : M.coord g 0 = 0) (i : Fin n) :
    M.coord (M.gen 0 ^ z * g) (Fin.succ i) = M.coord g (Fin.succ i) := by
  rw [M.coord_gen_mul z g hg]
  simp [Fin.tail_def]

/-- A normal word using all generators except the second one. -/
def secondTailNormal {n : ℕ} {T : ParameterIndex (n + 2) → ℤ}
    (M : CPres (n + 2) T) (x : Fin (n + 1) → ℤ) : M.G :=
  orderedZPow
    (fun i : Fin (n + 1) => M.gen ((1 : Fin (n + 2)).succAbove i)) x

set_option linter.flexible false in
lemma insert_second_coord {n : ℕ}
    {T : ParameterIndex (n + 2) → ℤ}
    (M : CPres (n + 2) T) (x : Fin (n + 1) → ℤ) :
    M.normalWord (insertSecondCoord x) = M.secondTailNormal x := by
  change orderedZPow M.gen (insertSecondCoord x) =
    orderedZPow
      (fun i : Fin (n + 1) => M.gen ((1 : Fin (n + 2)).succAbove i)) x
  unfold orderedZPow insertSecondCoord
  rw [List.finRange_succ]
  rw [List.finRange_succ]
  simp [List.map_map, Function.comp_def]
  change M.gen (1 : Fin (n + 2)) ^ (0 : ℤ) = 1
  simp

lemma coord_second_word {n : ℕ}
    {T : ParameterIndex (n + 2) → ℤ}
    (M : CPres (n + 2) T) (x : Fin (n + 1) → ℤ) :
    M.coord (M.secondTailNormal x) = insertSecondCoord x := by
  rw [← M.insert_second_coord]
  exact M.coord_normalWord _

lemma coord_second_tail {n : ℕ}
    {T : ParameterIndex (n + 2) → ℤ}
    (M : CPres (n + 2) T) (x : Fin (n + 1) → ℤ) :
    M.coord (M.secondTailNormal x) 1 = 0 := by
  rw [M.coord_second_word]
  simp

lemma coord_second_above {n : ℕ}
    {T : ParameterIndex (n + 2) → ℤ}
    (M : CPres (n + 2) T) (x : Fin (n + 1) → ℤ)
    (i : Fin (n + 1)) :
    M.coord (M.secondTailNormal x) ((1 : Fin (n + 2)).succAbove i) = x i := by
  rw [M.coord_second_word]
  simp

lemma second_tail_injective {n : ℕ}
    {T : ParameterIndex (n + 2) → ℤ}
    (M : CPres (n + 2) T) :
    Function.Injective M.secondTailNormal := by
  intro x y hxy
  have hfull :
      M.normalWord (insertSecondCoord x) =
        M.normalWord (insertSecondCoord y) := by
    rw [M.insert_second_coord, M.insert_second_coord]
    exact hxy
  have hcoord := M.normalWord_injective hfull
  funext i
  have hi := congrFun hcoord ((1 : Fin (n + 2)).succAbove i)
  simpa using hi

lemma normal_second_tail {n : ℕ}
    {T : ParameterIndex (n + 2) → ℤ}
    (M : CPres (n + 2) T) (x : Fin (n + 2) → ℤ)
    (hx : x 1 = 0) :
    M.normalWord x = M.secondTailNormal (deleteSecondCoord x) := by
  have hinsert := insert_second_delete x hx
  rw [← M.insert_second_coord]
  rw [hinsert]

lemma second_tail_coord {n : ℕ}
    {T : ParameterIndex (n + 2) → ℤ}
    (M : CPres (n + 2) T) (g : M.G)
    (hg : M.coord g 1 = 0) :
    g = M.secondTailNormal (deleteSecondCoord (M.coord g)) := by
  calc
    g = M.normalWord (M.coord g) := (M.normalWord_coord g).symm
    _ = M.secondTailNormal (deleteSecondCoord (M.coord g)) :=
      M.normal_second_tail (M.coord g) hg

/--
The carrier of elements whose first coordinate is zero, assuming that this
carrier is closed under multiplication and inverse.
-/
def firstCoordinateSubgroup {n : ℕ} {T : ParameterIndex (n + 1) → ℤ}
    (M : CPres (n + 1) T)
    (hMul : ∀ a b : M.G,
      M.coord a 0 = 0 → M.coord b 0 = 0 → M.coord (a * b) 0 = 0)
    (hInv : ∀ a : M.G, M.coord a 0 = 0 → M.coord a⁻¹ 0 = 0) :
    Subgroup M.G where
  carrier := {g | M.coord g 0 = 0}
  one_mem' := by
    have h := congrFun (M.coord_normalWord (fun _ : Fin (n + 1) => 0)) 0
    simpa [M.normalWord_zero] using h
  mul_mem' := by
    intro a b ha hb
    exact hMul a b ha hb
  inv_mem' := by
    intro a ha
    exact hInv a ha

lemma first_coordinate_gen {n : ℕ}
    {T : ParameterIndex (n + 1) → ℤ}
    (M : CPres (n + 1) T)
    (hMul : ∀ a b : M.G,
      M.coord a 0 = 0 → M.coord b 0 = 0 → M.coord (a * b) 0 = 0)
    (hInv : ∀ a : M.G, M.coord a 0 = 0 → M.coord a⁻¹ 0 = 0)
    (i : Fin n) :
    M.gen (Fin.succ i) ∈ M.firstCoordinateSubgroup hMul hInv := by
  change M.coord (M.gen (Fin.succ i)) 0 = 0
  rw [M.coord_gen]
  simp [singleCoord, (Fin.succ_ne_zero i).symm]

lemma first_z_val {n : ℕ}
    {T : ParameterIndex (n + 1) → ℤ}
    (M : CPres (n + 1) T)
    (hMul : ∀ a b : M.G,
      M.coord a 0 = 0 → M.coord b 0 = 0 → M.coord (a * b) 0 = 0)
    (hInv : ∀ a : M.G, M.coord a 0 = 0 → M.coord a⁻¹ 0 = 0)
    (x : Fin n → ℤ) :
    (((orderedZPow
      (fun i : Fin n =>
        (⟨M.gen (Fin.succ i),
          M.first_coordinate_gen hMul hInv i⟩ :
          M.firstCoordinateSubgroup hMul hInv)) x) :
        M.firstCoordinateSubgroup hMul hInv) : M.G) =
      M.tailNormalWord x := by
  unfold orderedZPow tailNormalWord
  rw [Subgroup.val_list_prod]
  simp only [List.map_map]
  apply congrArg List.prod
  apply List.map_congr_left
  intro i _hi
  simp

/--
Normal coordinates on the zero-first-coordinate subgroup, conditional on the
closure properties needed to make that carrier a subgroup.
-/
noncomputable def firstNormalSystem {n : ℕ}
    {T : ParameterIndex (n + 1) → ℤ}
    (M : CPres (n + 1) T)
    (hMul : ∀ a b : M.G,
      M.coord a 0 = 0 → M.coord b 0 = 0 → M.coord (a * b) 0 = 0)
    (hInv : ∀ a : M.G, M.coord a 0 = 0 → M.coord a⁻¹ 0 = 0) :
    NCSystem (M.firstCoordinateSubgroup hMul hInv) n where
  gen := fun i =>
    ⟨M.gen (Fin.succ i),
      M.first_coordinate_gen hMul hInv i⟩
  normalForm_bijective := by
    constructor
    · intro x y hxy
      apply M.tail_normal_injective
      have hval := congrArg Subtype.val hxy
      rw [M.first_z_val hMul hInv x,
        M.first_z_val hMul hInv y] at hval
      exact hval
    · intro g
      refine ⟨Fin.tail (M.coord g.1), ?_⟩
      apply Subtype.ext
      rw [M.first_z_val]
      exact (M.tail_coord_zero g.1 g.2).symm

/--
The concrete `U(T)` presentation on the zero-first-coordinate subgroup,
conditional on the closure properties needed to make that carrier a subgroup.
-/
noncomputable def firstConsistentPresentation {n : ℕ}
    {T : ParameterIndex (n + 1) → ℤ}
    (M : CPres (n + 1) T)
    (hMul : ∀ a b : M.G,
      M.coord a 0 = 0 → M.coord b 0 = 0 → M.coord (a * b) 0 = 0)
    (hInv : ∀ a : M.G, M.coord a 0 = 0 → M.coord a⁻¹ 0 = 0) :
    CPres n (firstParameterTuple T) where
  G := M.firstCoordinateSubgroup hMul hInv
  coords := M.firstNormalSystem hMul hInv
  relation := by
    intro i j hij
    apply Subtype.ext
    have hrel := first_parameter_tuple M i j hij
    have htail :
        ↑(relationTail (M.firstNormalSystem hMul hInv).gen
            (firstParameterTuple T) i j hij) =
          relationTail (fun k : Fin n => M.gen (Fin.succ k))
            (firstParameterTuple T) i j hij := by
      simpa [firstNormalSystem] using
        map_relationTail (M.firstCoordinateSubgroup hMul hInv).subtype
          (M.firstNormalSystem hMul hInv).gen
          (firstParameterTuple T) i j hij
    change M.gen (Fin.succ j) * M.gen (Fin.succ i) =
      M.gen (Fin.succ i) * M.gen (Fin.succ j) *
        ↑(relationTail (M.firstNormalSystem hMul hInv).gen
          (firstParameterTuple T) i j hij)
    rw [htail]
    exact hrel

lemma first_consistent_coe {n : ℕ}
    {T : ParameterIndex (n + 1) → ℤ}
    (M : CPres (n + 1) T)
    (hMul : ∀ a b : M.G,
      M.coord a 0 = 0 → M.coord b 0 = 0 → M.coord (a * b) 0 = 0)
    (hInv : ∀ a : M.G, M.coord a 0 = 0 → M.coord a⁻¹ 0 = 0)
    (x : Fin n → ℤ) :
    ((show M.firstCoordinateSubgroup hMul hInv from
        (M.firstConsistentPresentation hMul hInv).normalWord x) : M.G) =
      M.tailNormalWord x := by
  simpa [firstConsistentPresentation, CPres.normalWord,
    firstNormalSystem] using
      M.first_z_val hMul hInv x

lemma first_consistent_coord {n : ℕ}
    {T : ParameterIndex (n + 1) → ℤ}
    (M : CPres (n + 1) T)
    (hMul : ∀ a b : M.G,
      M.coord a 0 = 0 → M.coord b 0 = 0 → M.coord (a * b) 0 = 0)
    (hInv : ∀ a : M.G, M.coord a 0 = 0 → M.coord a⁻¹ 0 = 0)
    (g : M.firstCoordinateSubgroup hMul hInv) :
    (M.firstConsistentPresentation hMul hInv).coord g =
      Fin.tail (M.coord (g : M.G)) := by
  let MU := M.firstConsistentPresentation hMul hInv
  apply MU.normalWord_injective
  apply Subtype.ext
  rw [MU.normalWord_coord]
  change (g : M.G) = ((show M.firstCoordinateSubgroup hMul hInv from
      (M.firstConsistentPresentation hMul hInv).normalWord
        (Fin.tail (M.coord (g : M.G)))) : M.G)
  rw [M.first_consistent_coe hMul hInv]
  exact M.tail_coord_zero (g : M.G) g.property

/--
Conditional semantic `U(T)` step: once the zero-first-coordinate carrier is
known to be closed under multiplication and inverse, deleting the first
generator gives a consistent tuple.
-/
theorem consistent_tuple_closed {n : ℕ}
    {T : ParameterIndex (n + 1) → ℤ}
    (M : CPres (n + 1) T)
    (hMul : ∀ a b : M.G,
      M.coord a 0 = 0 → M.coord b 0 = 0 → M.coord (a * b) 0 = 0)
    (hInv : ∀ a : M.G, M.coord a 0 = 0 → M.coord a⁻¹ 0 = 0) :
    IsConsistent (firstParameterTuple T) := by
  exact ⟨M.firstConsistentPresentation hMul hInv⟩

/-- Section 3.1 `U(T)` step, packaged using `CoordinateZeroClosed`. -/
theorem consistent_delete_parameter {n : ℕ}
    {T : ParameterIndex (n + 1) → ℤ}
    (M : CPres (n + 1) T)
    (hClosed : CoordinateZeroClosed M 0) :
    IsConsistent (firstParameterTuple T) :=
  consistent_tuple_closed M
    hClosed.1 hClosed.2

/-- Section 3.1 `U(T)` step, from tuple-level zero-coordinate closure. -/
theorem consistent_delete_closed {n : ℕ}
    {T : ParameterIndex (n + 1) → ℤ}
    (M : CPres (n + 1) T)
    (hClosed : CoordinateTupleClosed M 0) :
    IsConsistent (firstParameterTuple T) :=
  consistent_delete_parameter M
    ((M.coordinate_closed_tuple 0).mpr hClosed)

/--
Section 3.1 `U(T)` step from the sharper additive-coordinate hypothesis.
Proving additivity of the first coordinate is enough to remove the separate
closure assumptions for the zero-first-coordinate carrier.
-/
theorem consistent_tuple_additive {n : ℕ}
    {T : ParameterIndex (n + 1) → ℤ}
    (M : CPres (n + 1) T)
    (hAdd : CoordinateAdditive M 0) :
    IsConsistent (firstParameterTuple T) :=
  consistent_delete_parameter M
    (coordinate_closed_additive M 0 hAdd)

/-- The concrete `U(T)` presentation obtained from first-coordinate additivity. -/
noncomputable def firstConsistentAdditive {n : ℕ}
    {T : ParameterIndex (n + 1) → ℤ}
    (M : CPres (n + 1) T)
    (hAdd : CoordinateAdditive M 0) :
    CPres n (firstParameterTuple T) :=
  let hClosed := coordinate_closed_additive M 0 hAdd
  M.firstConsistentPresentation hClosed.1 hClosed.2

lemma consistent_additive_coord {n : ℕ}
    {T : ParameterIndex (n + 1) → ℤ}
    (M : CPres (n + 1) T)
    (hAdd : CoordinateAdditive M 0)
    (g : M.firstCoordinateSubgroup
        (coordinate_closed_additive M 0 hAdd).1
        (coordinate_closed_additive M 0 hAdd).2) :
    (M.firstConsistentAdditive hAdd).coord g =
      Fin.tail (M.coord (g : M.G)) := by
  exact M.first_consistent_coord
    (coordinate_closed_additive M 0 hAdd).1
    (coordinate_closed_additive M 0 hAdd).2 g

/-- Section 3.1 set-level `U(T)` step in consistency-locus notation. -/
theorem parameter_consistency_closed {n : ℕ}
    {T : ParameterIndex (n + 1) → ℤ}
    (M : CPres (n + 1) T)
    (hClosed : CoordinateZeroClosed M 0) :
    firstParameterTuple T ∈ consistencyLocus n :=
  consistent_delete_parameter M hClosed

/-- Section 3.1 set-level `U(T)` step from tuple-level zero-coordinate closure. -/
theorem parameter_locus_closed {n : ℕ}
    {T : ParameterIndex (n + 1) → ℤ}
    (M : CPres (n + 1) T)
    (hClosed : CoordinateTupleClosed M 0) :
    firstParameterTuple T ∈ consistencyLocus n :=
  consistent_delete_closed M hClosed

/-- Section 3.1 set-level `U(T)` step from first-coordinate additivity. -/
theorem tuple_consistency_locus {n : ℕ}
    {T : ParameterIndex (n + 1) → ℤ}
    (M : CPres (n + 1) T)
    (hAdd : CoordinateAdditive M 0) :
    firstParameterTuple T ∈ consistencyLocus n :=
  consistent_tuple_additive M hAdd

/--
The carrier of elements whose second coordinate is zero, assuming that this
carrier is closed under multiplication and inverse.
-/
def secondCoordinateSubgroup {n : ℕ} {T : ParameterIndex (n + 2) → ℤ}
    (M : CPres (n + 2) T)
    (hMul : ∀ a b : M.G,
      M.coord a 1 = 0 → M.coord b 1 = 0 → M.coord (a * b) 1 = 0)
    (hInv : ∀ a : M.G, M.coord a 1 = 0 → M.coord a⁻¹ 1 = 0) :
    Subgroup M.G where
  carrier := {g | M.coord g 1 = 0}
  one_mem' := by
    have h := congrFun (M.coord_normalWord (fun _ : Fin (n + 2) => 0)) 1
    simpa [M.normalWord_zero] using h
  mul_mem' := by
    intro a b ha hb
    exact hMul a b ha hb
  inv_mem' := by
    intro a ha
    exact hInv a ha

lemma second_coordinate_gen {n : ℕ}
    {T : ParameterIndex (n + 2) → ℤ}
    (M : CPres (n + 2) T)
    (hMul : ∀ a b : M.G,
      M.coord a 1 = 0 → M.coord b 1 = 0 → M.coord (a * b) 1 = 0)
    (hInv : ∀ a : M.G, M.coord a 1 = 0 → M.coord a⁻¹ 1 = 0)
    (i : Fin (n + 1)) :
    M.gen ((1 : Fin (n + 2)).succAbove i) ∈
      M.secondCoordinateSubgroup hMul hInv := by
  change M.coord (M.gen ((1 : Fin (n + 2)).succAbove i)) 1 = 0
  rw [M.coord_gen]
  cases i using Fin.cases with
  | zero => simp [singleCoord]
  | succ i =>
      simp only [singleCoord, ite_eq_right_iff]
      intro h
      have hval := congrArg Fin.val h
      simp at hval

lemma second_z_val {n : ℕ}
    {T : ParameterIndex (n + 2) → ℤ}
    (M : CPres (n + 2) T)
    (hMul : ∀ a b : M.G,
      M.coord a 1 = 0 → M.coord b 1 = 0 → M.coord (a * b) 1 = 0)
    (hInv : ∀ a : M.G, M.coord a 1 = 0 → M.coord a⁻¹ 1 = 0)
    (x : Fin (n + 1) → ℤ) :
    (((orderedZPow
      (fun i : Fin (n + 1) =>
        (⟨M.gen ((1 : Fin (n + 2)).succAbove i),
          M.second_coordinate_gen hMul hInv i⟩ :
          M.secondCoordinateSubgroup hMul hInv)) x) :
        M.secondCoordinateSubgroup hMul hInv) : M.G) =
      M.secondTailNormal x := by
  unfold orderedZPow secondTailNormal
  rw [Subgroup.val_list_prod]
  simp only [List.map_map]
  apply congrArg List.prod
  apply List.map_congr_left
  intro i _hi
  simp

/--
Normal coordinates on the zero-second-coordinate subgroup, conditional on the
closure properties needed to make that carrier a subgroup.
-/
noncomputable def secondNormalSystem {n : ℕ}
    {T : ParameterIndex (n + 2) → ℤ}
    (M : CPres (n + 2) T)
    (hMul : ∀ a b : M.G,
      M.coord a 1 = 0 → M.coord b 1 = 0 → M.coord (a * b) 1 = 0)
    (hInv : ∀ a : M.G, M.coord a 1 = 0 → M.coord a⁻¹ 1 = 0) :
    NCSystem (M.secondCoordinateSubgroup hMul hInv) (n + 1) where
  gen := fun i =>
    ⟨M.gen ((1 : Fin (n + 2)).succAbove i),
      M.second_coordinate_gen hMul hInv i⟩
  normalForm_bijective := by
    constructor
    · intro x y hxy
      apply M.second_tail_injective
      have hval := congrArg Subtype.val hxy
      rw [M.second_z_val hMul hInv x,
        M.second_z_val hMul hInv y] at hval
      exact hval
    · intro g
      refine ⟨deleteSecondCoord (M.coord g.1), ?_⟩
      apply Subtype.ext
      rw [M.second_z_val]
      exact (M.second_tail_coord g.1 g.2).symm

/--
The concrete `V(T)` presentation on the zero-second-coordinate subgroup,
conditional on the closure properties needed to make that carrier a subgroup.
-/
noncomputable def secondConsistentPresentation {n : ℕ}
    {T : ParameterIndex (n + 2) → ℤ}
    (M : CPres (n + 2) T)
    (hMul : ∀ a b : M.G,
      M.coord a 1 = 0 → M.coord b 1 = 0 → M.coord (a * b) 1 = 0)
    (hInv : ∀ a : M.G, M.coord a 1 = 0 → M.coord a⁻¹ 1 = 0) :
    CPres (n + 1) (secondParameterTuple T) where
  G := M.secondCoordinateSubgroup hMul hInv
  coords := M.secondNormalSystem hMul hInv
  relation := by
    intro i j hij
    apply Subtype.ext
    have hrel := relation_second_parameter M i j hij
    have htail :
        ↑(relationTail (M.secondNormalSystem hMul hInv).gen
            (secondParameterTuple T) i j hij) =
          relationTail
            (fun k : Fin (n + 1) => M.gen ((1 : Fin (n + 2)).succAbove k))
            (secondParameterTuple T) i j hij := by
      simpa [secondNormalSystem] using
        map_relationTail (M.secondCoordinateSubgroup hMul hInv).subtype
          (M.secondNormalSystem hMul hInv).gen
          (secondParameterTuple T) i j hij
    change M.gen ((1 : Fin (n + 2)).succAbove j) *
        M.gen ((1 : Fin (n + 2)).succAbove i) =
      M.gen ((1 : Fin (n + 2)).succAbove i) *
        M.gen ((1 : Fin (n + 2)).succAbove j) *
          ↑(relationTail (M.secondNormalSystem hMul hInv).gen
            (secondParameterTuple T) i j hij)
    rw [htail]
    exact hrel

lemma consistent_presentation_coe {n : ℕ}
    {T : ParameterIndex (n + 2) → ℤ}
    (M : CPres (n + 2) T)
    (hMul : ∀ a b : M.G,
      M.coord a 1 = 0 → M.coord b 1 = 0 → M.coord (a * b) 1 = 0)
    (hInv : ∀ a : M.G, M.coord a 1 = 0 → M.coord a⁻¹ 1 = 0)
    (x : Fin (n + 1) → ℤ) :
    ((show M.secondCoordinateSubgroup hMul hInv from
        (M.secondConsistentPresentation hMul hInv).normalWord x) : M.G) =
      M.secondTailNormal x := by
  simpa [secondConsistentPresentation, CPres.normalWord,
    secondNormalSystem] using
      M.second_z_val hMul hInv x

lemma second_consistent_coord {n : ℕ}
    {T : ParameterIndex (n + 2) → ℤ}
    (M : CPres (n + 2) T)
    (hMul : ∀ a b : M.G,
      M.coord a 1 = 0 → M.coord b 1 = 0 → M.coord (a * b) 1 = 0)
    (hInv : ∀ a : M.G, M.coord a 1 = 0 → M.coord a⁻¹ 1 = 0)
    (g : M.secondCoordinateSubgroup hMul hInv) :
    (M.secondConsistentPresentation hMul hInv).coord g =
      deleteSecondCoord (M.coord (g : M.G)) := by
  let MV := M.secondConsistentPresentation hMul hInv
  apply MV.normalWord_injective
  apply Subtype.ext
  rw [MV.normalWord_coord]
  change (g : M.G) = ((show M.secondCoordinateSubgroup hMul hInv from
      (M.secondConsistentPresentation hMul hInv).normalWord
        (deleteSecondCoord (M.coord (g : M.G)))) : M.G)
  rw [M.consistent_presentation_coe hMul hInv]
  exact M.second_tail_coord (g : M.G) g.property

/--
Conditional semantic `V(T)` step: once the zero-second-coordinate carrier is
known to be closed under multiplication and inverse, deleting the second
generator gives a consistent tuple.
-/
theorem consistent_parameter_closed {n : ℕ}
    {T : ParameterIndex (n + 2) → ℤ}
    (M : CPres (n + 2) T)
    (hMul : ∀ a b : M.G,
      M.coord a 1 = 0 → M.coord b 1 = 0 → M.coord (a * b) 1 = 0)
    (hInv : ∀ a : M.G, M.coord a 1 = 0 → M.coord a⁻¹ 1 = 0) :
    IsConsistent (secondParameterTuple T) := by
  exact ⟨M.secondConsistentPresentation hMul hInv⟩

/-- Section 3.1 `V(T)` step, packaged using `CoordinateZeroClosed`. -/
theorem consistent_second_closed {n : ℕ}
    {T : ParameterIndex (n + 2) → ℤ}
    (M : CPres (n + 2) T)
    (hClosed : CoordinateZeroClosed M 1) :
    IsConsistent (secondParameterTuple T) :=
  consistent_parameter_closed M
    hClosed.1 hClosed.2

/-- Section 3.1 `V(T)` step, from tuple-level zero-coordinate closure. -/
theorem consistent_parameter_tuple {n : ℕ}
    {T : ParameterIndex (n + 2) → ℤ}
    (M : CPres (n + 2) T)
    (hClosed : CoordinateTupleClosed M 1) :
    IsConsistent (secondParameterTuple T) :=
  consistent_second_closed M
    ((M.coordinate_closed_tuple 1).mpr hClosed)

/--
Section 3.1 `V(T)` step from the sharper additive-coordinate hypothesis.
The theorem `secondCoordinateAdditive` below supplies this hypothesis for every
consistent presentation.
-/
theorem consistent_second_parameter {n : ℕ}
    {T : ParameterIndex (n + 2) → ℤ}
    (M : CPres (n + 2) T)
    (hAdd : CoordinateAdditive M 1) :
    IsConsistent (secondParameterTuple T) :=
  consistent_second_closed M
    (coordinate_closed_additive M 1 hAdd)

/-- The concrete `V(T)` presentation obtained from second-coordinate additivity. -/
noncomputable def consistentPresentationAdditive {n : ℕ}
    {T : ParameterIndex (n + 2) → ℤ}
    (M : CPres (n + 2) T)
    (hAdd : CoordinateAdditive M 1) :
    CPres (n + 1) (secondParameterTuple T) :=
  let hClosed := coordinate_closed_additive M 1 hAdd
  M.secondConsistentPresentation hClosed.1 hClosed.2

lemma consistent_presentation_coord {n : ℕ}
    {T : ParameterIndex (n + 2) → ℤ}
    (M : CPres (n + 2) T)
    (hAdd : CoordinateAdditive M 1)
    (g : M.secondCoordinateSubgroup
        (coordinate_closed_additive M 1 hAdd).1
        (coordinate_closed_additive M 1 hAdd).2) :
    (M.consistentPresentationAdditive hAdd).coord g =
      deleteSecondCoord (M.coord (g : M.G)) := by
  exact M.second_consistent_coord
    (coordinate_closed_additive M 1 hAdd).1
    (coordinate_closed_additive M 1 hAdd).2 g

/-- Section 3.1 set-level `V(T)` step in consistency-locus notation. -/
theorem delete_consistency_locus {n : ℕ}
    {T : ParameterIndex (n + 2) → ℤ}
    (M : CPres (n + 2) T)
    (hClosed : CoordinateZeroClosed M 1) :
    secondParameterTuple T ∈ consistencyLocus (n + 1) :=
  consistent_second_closed M hClosed

/-- Section 3.1 set-level `V(T)` step from tuple-level zero-coordinate closure. -/
theorem consistency_locus_closed {n : ℕ}
    {T : ParameterIndex (n + 2) → ℤ}
    (M : CPres (n + 2) T)
    (hClosed : CoordinateTupleClosed M 1) :
    secondParameterTuple T ∈ consistencyLocus (n + 1) :=
  consistent_parameter_tuple M hClosed

/-- Section 3.1 set-level `V(T)` step from second-coordinate additivity. -/
theorem parameter_locus_additive {n : ℕ}
    {T : ParameterIndex (n + 2) → ℤ}
    (M : CPres (n + 2) T)
    (hAdd : CoordinateAdditive M 1) :
    secondParameterTuple T ∈ consistencyLocus (n + 1) :=
  consistent_second_parameter M hAdd

lemma normal_last_coord {n : ℕ} {T : ParameterIndex (n + 1) → ℤ}
    (M : CPres (n + 1) T)
    (x : Fin (n + 1) → ℤ) (z : ℤ) :
    M.normalWord (addLastCoord x z) =
      M.normalWord x * M.gen (Fin.last n) ^ z := by
  change orderedZPow M.gen (addLastCoord x z) =
    orderedZPow M.gen x * M.gen (Fin.last n) ^ z
  unfold orderedZPow addLastCoord
  rw [List.finRange_succ_last]
  simp [List.map_append, List.prod_append, Function.comp_def, Fin.castSucc_ne_last, zpow_add]
  group

lemma without_last_coord {n : ℕ}
    {T : ParameterIndex (n + 1) → ℤ}
    (M : CPres (n + 1) T)
    (x : Fin (n + 1) → ℤ) :
    M.normalWord x =
      M.normalWord (withoutLastCoord x) * M.gen (Fin.last n) ^ x (Fin.last n) := by
  rw [← normal_last_coord M (withoutLastCoord x) (x (Fin.last n))]
  rw [last_coord_without]

lemma normal_without_coord {n : ℕ}
    {T : ParameterIndex (n + 1) → ℤ}
    (M : CPres (n + 1) T)
    (x : Fin (n + 1) → ℤ) :
    M.normalWord x = M.gen 0 ^ x 0 * M.normalWord (withoutFirstCoord x) := by
  change orderedZPow M.gen x =
    M.gen 0 ^ x 0 * orderedZPow M.gen (withoutFirstCoord x)
  unfold orderedZPow withoutFirstCoord
  rw [List.finRange_succ]
  simp [Function.comp_def]

lemma coord_zpow_neg {n : ℕ}
    {T : ParameterIndex (n + 1) → ℤ}
    (M : CPres (n + 1) T)
    (x : Fin (n + 1) → ℤ) :
    M.coord (M.gen 0 ^ (-(x 0)) * M.normalWord x) = withoutFirstCoord x := by
  rw [normal_without_coord]
  rw [← mul_assoc]
  rw [← zpow_add]
  simp only [neg_add_cancel, zpow_zero, one_mul]
  exact M.coord_normalWord _

/--
Semantic core behind the first-generator conjugation rewrite: if the
`a_j^u a_0^v` normal form has first coordinate `v`, then left conjugation by
`a_0^v` simply removes that first coordinate.
-/
theorem conjugation_without_coord
    {n : ℕ} {T : ParameterIndex (n + 1) → ℤ}
    (M : CPres (n + 1) T)
    (j : Fin (n + 1)) (u v : ℤ)
    (hc0 : M.conjugationTuple 0 j u v 0 = v) :
    M.leftConjugationTuple 0 j u v =
      withoutFirstCoord (M.conjugationTuple 0 j u v) := by
  let c := M.conjugationTuple 0 j u v
  have hc0c : c 0 = v := by
    simpa [c] using hc0
  have hpow : M.gen 0 ^ (-v) = M.gen 0 ^ (-(c 0)) := by rw [hc0c]
  change M.coord (M.gen 0 ^ (-v) * M.gen j ^ u * M.gen 0 ^ v) =
    withoutFirstCoord c
  rw [show M.gen 0 ^ (-v) * M.gen j ^ u * M.gen 0 ^ v =
      M.gen 0 ^ (-v) * (M.gen j ^ u * M.gen 0 ^ v) by group]
  rw [← M.word_conjugation_tuple 0 j u v]
  rw [hpow]
  exact M.coord_zpow_neg c

lemma left_conjugation_coord
    {n : ℕ} {T : ParameterIndex (n + 1) → ℤ}
    (M : CPres (n + 1) T)
    (j : Fin (n + 1)) (u v : ℤ)
    (hc0 : M.conjugationTuple 0 j u v 0 = v) :
    M.leftConjugationTuple 0 j u v 0 = 0 := by
  rw [M.conjugation_without_coord
    j u v hc0]
  simp

lemma conjugation_tuple_coord
    {n : ℕ} {T : ParameterIndex (n + 1) → ℤ}
    (M : CPres (n + 1) T)
    (j k : Fin (n + 1)) (u v : ℤ)
    (hc0 : M.conjugationTuple 0 j u v 0 = v) (hk0 : k ≠ 0) :
    M.leftConjugationTuple 0 j u v k =
      M.conjugationTuple 0 j u v k := by
  rw [M.conjugation_without_coord
    j u v hc0]
  exact without_coord_ne _ hk0

/--
Semantic decomposition used in the multiplication-polynomial construction:
split off the first generator and move the first coordinate of the right
factor to the front, leaving conjugation by that first generator.
-/
theorem normal_first_decomposition {n : ℕ}
    {T : ParameterIndex (n + 1) → ℤ}
    (M : CPres (n + 1) T)
    (x y : Fin (n + 1) → ℤ) :
    M.normalWord x * M.normalWord y =
      M.gen 0 ^ (x 0 + y 0) *
        (M.gen 0 ^ (-(y 0)) * M.normalWord (withoutFirstCoord x) * M.gen 0 ^ y 0) *
          M.normalWord (withoutFirstCoord y) := by
  rw [M.normal_without_coord x, M.normal_without_coord y]
  group

/--
The ordered product of the individually conjugated tail factors appearing in
the multiplication-polynomial construction.
-/
noncomputable def firstConjugatedProduct {n : ℕ}
    {T : ParameterIndex (n + 1) → ℤ}
    (M : CPres (n + 1) T)
    (x : Fin (n + 1) → ℤ) (v : ℤ) : M.G :=
  ((List.finRange n).map fun i =>
    M.normalWord (M.leftConjugationTuple 0 (Fin.succ i) (x (Fin.succ i)) v)).prod

lemma first_conjugated_aux {n : ℕ}
    {T : ParameterIndex (n + 1) → ℤ}
    (M : CPres (n + 1) T)
    (x : Fin (n + 1) → ℤ) (v : ℤ) :
    ∀ l : List (Fin n),
      M.gen 0 ^ (-v) * ((l.map fun i => M.gen (Fin.succ i) ^ x (Fin.succ i)).prod) *
          M.gen 0 ^ v =
        (l.map fun i =>
          M.normalWord (M.leftConjugationTuple 0 (Fin.succ i) (x (Fin.succ i)) v)).prod
  | [] => by simp
  | i :: l => by
      simp only [List.map_cons, List.prod_cons]
      calc
        M.gen 0 ^ (-v) *
            (M.gen (Fin.succ i) ^ x (Fin.succ i) *
              (List.map (fun i => M.gen (Fin.succ i) ^ x (Fin.succ i)) l).prod) *
            M.gen 0 ^ v
            = (M.gen 0 ^ (-v) * M.gen (Fin.succ i) ^ x (Fin.succ i) * M.gen 0 ^ v) *
                (M.gen 0 ^ (-v) *
                  (List.map (fun i => M.gen (Fin.succ i) ^ x (Fin.succ i)) l).prod *
                  M.gen 0 ^ v) := by group
        _ = M.normalWord (M.leftConjugationTuple 0 (Fin.succ i) (x (Fin.succ i)) v) *
              (List.map (fun i =>
                M.normalWord
                  (M.leftConjugationTuple 0 (Fin.succ i) (x (Fin.succ i)) v)) l).prod := by
            rw [← normal_conjugation_tuple, first_conjugated_aux]

/--
Conjugating the tail of a normal word by the first generator is the ordered
product of the individually left-conjugated tail factors.
-/
theorem first_conjugated_product {n : ℕ}
    {T : ParameterIndex (n + 1) → ℤ}
    (M : CPres (n + 1) T)
    (x : Fin (n + 1) → ℤ) (v : ℤ) :
    M.gen 0 ^ (-v) * M.normalWord (withoutFirstCoord x) * M.gen 0 ^ v =
      M.firstConjugatedProduct x v := by
  change M.gen 0 ^ (-v) * orderedZPow M.gen (withoutFirstCoord x) * M.gen 0 ^ v =
      M.firstConjugatedProduct x v
  unfold orderedZPow withoutFirstCoord firstConjugatedProduct
  rw [List.finRange_succ]
  simp only [zpow_neg, pow_ite, zpow_zero, List.map_cons, ↓reduceIte, List.map_map,
    List.prod_cons, one_mul]
  rw [← zpow_neg]
  exact first_conjugated_aux M x v (List.finRange n)

/--
The exact semantic condition needed to keep the first-conjugated tail product
inside the zero-first-coordinate carrier: the carrier is closed under
multiplication, and every displayed left-conjugated factor has zero first
coordinate.
-/
lemma first_conjugated_factors {n : ℕ}
    {T : ParameterIndex (n + 1) → ℤ}
    (M : CPres (n + 1) T)
    (hMul : ∀ a b : M.G,
      M.coord a 0 = 0 → M.coord b 0 = 0 → M.coord (a * b) 0 = 0)
    (x : Fin (n + 1) → ℤ) (v : ℤ)
    (hFactor :
      ∀ i : Fin n,
        M.leftConjugationTuple 0 (Fin.succ i) (x (Fin.succ i)) v 0 = 0) :
    M.coord (M.firstConjugatedProduct x v) 0 = 0 := by
  unfold firstConjugatedProduct
  generalize List.finRange n = l
  induction l with
  | nil =>
      simpa using M.coord_one (0 : Fin (n + 1))
  | cons i is ih =>
      simp only [List.map_cons, List.prod_cons]
      apply hMul
      · rw [M.coord_normalWord]
        exact hFactor i
      · exact ih

lemma conjugation_tuple_conjugator
    (i j : Fin n) (u : ℤ) :
    M.leftConjugationTuple i j u 0 = singleCoord j u := by
  change M.coord (M.gen i ^ (0 : ℤ) * M.gen j ^ u * M.gen i ^ (0 : ℤ)) =
    singleCoord j u
  simp [M.coord_gen_zpow]

/--
One-step left conjugation is exactly the displayed defining relation tail:
`a_i⁻¹ a_j a_i = a_j · tail(i,j)`.
-/
theorem conjugation_tuple_tail
    (i j : Fin n) (hij : i < j) :
    M.leftConjugationTuple i j 1 1 =
      M.coord (M.gen j * relationTail M.gen T i j hij) := by
  change M.coord (M.gen i ^ (-1 : ℤ) * M.gen j ^ (1 : ℤ) * M.gen i ^ (1 : ℤ)) =
    M.coord (M.gen j * relationTail M.gen T i j hij)
  congr 1
  rw [zpow_one, zpow_one]
  have hrel : M.gen j * M.gen i =
      M.gen i * M.gen j * relationTail M.gen T i j hij := by
    simpa [CPres.gen] using M.relation i j hij
  calc
    M.gen i ^ (-1 : ℤ) * M.gen j * M.gen i =
        M.gen i ^ (-1 : ℤ) * (M.gen j * M.gen i) := by
          group
    _ = M.gen i ^ (-1 : ℤ) * (M.gen i * M.gen j * relationTail M.gen T i j hij) := by
          rw [hrel]
    _ = M.gen j * relationTail M.gen T i j hij := by
          rw [zpow_neg, zpow_one]
          group

/--
Unconditional one-step left-conjugation normal tuple.  This upgrades the
relation-level rewrite to coordinates without assuming any represented
conjugation polynomial family.
-/
theorem conjugation_tuple_relation
    (i j : Fin n) (hij : i < j) :
    M.leftConjugationTuple i j 1 1 =
      relationProductTuple T i j hij := by
  rw [M.conjugation_tuple_tail i j hij]
  exact M.coord_relationProduct i j hij

lemma conjugation_tuple_self
    (i j : Fin n) (hij : i < j) :
    M.leftConjugationTuple i j 1 1 j = 1 := by
  rw [M.conjugation_tuple_relation i j hij]
  simp

lemma left_tuple_one
    (i j k : Fin n) (hij : i < j) (hjk : j < k) :
    M.leftConjugationTuple i j 1 1 k =
      T ⟨(i, j, k), hij, hjk⟩ := by
  rw [M.conjugation_tuple_relation i j hij]
  simp [hjk]

lemma conjugation_tuple_not
    (i j k : Fin n) (hij : i < j) (hkj : k ≠ j) (hjk : ¬ j < k) :
    M.leftConjugationTuple i j 1 1 k = 0 := by
  rw [M.conjugation_tuple_relation i j hij]
  exact relation_tuple_not T i j k hij hkj hjk

lemma conjugation_tuple_first {n : ℕ}
    {T : ParameterIndex (n + 1) → ℤ}
    (M : CPres (n + 1) T)
    (j : Fin (n + 1)) (h0j : (0 : Fin (n + 1)) < j) :
    M.leftConjugationTuple 0 j 1 1 0 = 0 :=
  M.conjugation_tuple_not
    0 j 0 h0j (ne_of_lt h0j) (not_lt_of_ge (Fin.zero_le j))

/--
Unconditional first nontrivial one-step conjugation tuple:
`a_0⁻¹ a_1 a_0` has the displayed normal coordinates from the `(0,1)`
defining relation.
-/
theorem left_conjugation_one {n : ℕ}
    {T : ParameterIndex (n + 2) → ℤ}
    (M : CPres (n + 2) T) :
    M.leftConjugationTuple 0 1 1 1 =
      zeroRelationTuple T := by
  simpa using
    M.conjugation_tuple_relation
      0 1 fin_add_two

lemma conjugation_tuple_one {n : ℕ}
    {T : ParameterIndex (n + 2) → ℤ}
    (M : CPres (n + 2) T) :
    M.leftConjugationTuple 0 1 1 1 0 = 0 := by
  rw [M.left_conjugation_one]
  simp

lemma conjugation_tuple_zero {n : ℕ}
    {T : ParameterIndex (n + 2) → ℤ}
    (M : CPres (n + 2) T) :
    M.leftConjugationTuple 0 1 1 1 1 = 1 := by
  rw [M.left_conjugation_one]
  simp

lemma conjugation_tuple_succ {n : ℕ}
    {T : ParameterIndex (n + 2) → ℤ}
    (M : CPres (n + 2) T) (k : Fin n) :
    M.leftConjugationTuple 0 1 1 1 (Fin.succ (Fin.succ k)) =
      T ⟨((0 : Fin (n + 2)), (1 : Fin (n + 2)),
        Fin.succ (Fin.succ k)), fin_add_two,
        succSucc_pos k⟩ := by
  rw [M.left_conjugation_one]
  simp

lemma first_conjugated_tail {n : ℕ}
    {T : ParameterIndex (n + 1) → ℤ}
    (M : CPres (n + 1) T)
    (x : Fin (n + 1) → ℤ) :
    M.firstConjugatedProduct x 0 = M.normalWord (withoutFirstCoord x) := by
  rw [← M.first_conjugated_product x 0]
  simp

/--
If the first-conjugated tail product has zero first coordinate, then appending
the right tail from the multiplication display still has zero first coordinate,
provided the zero-first-coordinate carrier is closed under multiplication.
-/
lemma multiplication_display_conjugated {n : ℕ}
    {T : ParameterIndex (n + 1) → ℤ}
    (M : CPres (n + 1) T)
    (hMul : ∀ a b : M.G,
      M.coord a 0 = 0 → M.coord b 0 = 0 → M.coord (a * b) 0 = 0)
    (x y : Fin (n + 1) → ℤ)
    (hFirst : M.coord (M.firstConjugatedProduct x (y 0)) 0 = 0) :
    M.coord (M.firstConjugatedProduct x (y 0) *
      M.normalWord (withoutFirstCoord y)) 0 = 0 := by
  apply hMul
  · exact hFirst
  · change M.coord (M.normalWord (withoutFirstCoord y)) 0 = 0
    rw [M.coord_normalWord]
    simp

/--
Semantic form of the displayed multiplication formula `(*)` in Section 3.3,
before replacing the individual conjugation coordinates by polynomials.
-/
theorem normal_conjugated_tail {n : ℕ}
    {T : ParameterIndex (n + 1) → ℤ}
    (M : CPres (n + 1) T)
    (x y : Fin (n + 1) → ℤ) :
    M.normalWord x * M.normalWord y =
      M.gen 0 ^ (x 0 + y 0) *
        M.firstConjugatedProduct x (y 0) *
          M.normalWord (withoutFirstCoord y) := by
  rw [M.normal_first_decomposition x y]
  rw [first_conjugated_product]

/-- Normal-form coordinate version of the Section 3.3 multiplication display. -/
theorem multiplication_tuple_conjugated {n : ℕ}
    {T : ParameterIndex (n + 1) → ℤ}
    (M : CPres (n + 1) T)
    (x y : Fin (n + 1) → ℤ) :
    M.normalWord (M.multiplicationTuple x y) =
      M.gen 0 ^ (x 0 + y 0) *
        M.firstConjugatedProduct x (y 0) *
          M.normalWord (withoutFirstCoord y) := by
  rw [M.normal_multiplication_tuple]
  exact M.normal_conjugated_tail x y

/--
Coordinate form of the Section 3.3 multiplication display: the semantic
multiplication tuple is obtained by taking coordinates of the displayed
right-hand side.
-/
theorem multiplication_coord_conjugated {n : ℕ}
    {T : ParameterIndex (n + 1) → ℤ}
    (M : CPres (n + 1) T)
    (x y : Fin (n + 1) → ℤ) :
    M.multiplicationTuple x y =
      M.coord (M.gen 0 ^ (x 0 + y 0) *
        M.firstConjugatedProduct x (y 0) *
          M.normalWord (withoutFirstCoord y)) := by
  rw [← M.multiplication_tuple_conjugated x y]
  exact (M.coord_normalWord (M.multiplicationTuple x y)).symm

/--
The exact semantic obstruction to first-coordinate additivity in the Section
3.3 display: after the leading `a_0^(x_0+y_0)` has been split off, the
remaining displayed tail has first coordinate zero.
-/
def FirstDisplayTail {n : ℕ} {T : ParameterIndex (n + 1) → ℤ}
    (M : CPres (n + 1) T) : Prop :=
  ∀ x y : Fin (n + 1) → ℤ,
    M.coord (M.firstConjugatedProduct x (y 0) *
      M.normalWord (withoutFirstCoord y)) 0 = 0

theorem first_display_additive {n : ℕ}
    {T : ParameterIndex (n + 1) → ℤ}
    (M : CPres (n + 1) T)
    (hAdd : CoordinateAdditive M 0) :
    FirstDisplayTail M := by
  intro x y
  let tailProduct :=
    M.firstConjugatedProduct x (y 0) * M.normalWord (withoutFirstCoord y)
  have htail :
      tailProduct =
        (M.gen 0 ^ (x 0 + y 0))⁻¹ * (M.normalWord x * M.normalWord y) := by
    have hdisplay := M.normal_conjugated_tail x y
    have hdisplay' :
        M.normalWord x * M.normalWord y =
          M.gen 0 ^ (x 0 + y 0) * tailProduct := by
      rw [hdisplay]
      simp [tailProduct]
      group
    rw [hdisplay']
    group
  have hprod := hAdd (M.normalWord x) (M.normalWord y)
  rw [M.coord_normalWord x, M.coord_normalWord y] at hprod
  have hgen : M.coord (M.gen 0 ^ (x 0 + y 0)) 0 = x 0 + y 0 := by
    simpa [singleCoord] using congrFun (M.coord_gen_zpow 0 (x 0 + y 0)) 0
  change M.coord tailProduct 0 = 0
  rw [htail, hAdd, M.coord_inv_additive 0 hAdd,
    hprod, hgen]
  omega

theorem coordinate_additive_display {n : ℕ}
    {T : ParameterIndex (n + 1) → ℤ}
    (M : CPres (n + 1) T) :
    CoordinateAdditive M 0 ↔ FirstDisplayTail M := by
  constructor
  · exact M.first_display_additive
  · intro htailZero
    rw [M.additive_multiplication_tuple 0]
    intro x y
    have hdisplay :=
      congrFun (M.multiplication_coord_conjugated x y) 0
    let tailProduct :=
      M.firstConjugatedProduct x (y 0) * M.normalWord (withoutFirstCoord y)
    have htail : M.coord tailProduct 0 = 0 := htailZero x y
    rw [hdisplay]
    have hassoc :
        M.gen 0 ^ (x 0 + y 0) *
            M.firstConjugatedProduct x (y 0) *
            M.normalWord (withoutFirstCoord y) =
          M.gen 0 ^ (x 0 + y 0) * tailProduct := by
      simp [tailProduct]
      group
    rw [hassoc]
    rw [M.coord_gen_mul (x 0 + y 0) tailProduct htail]
    simp

/--
The V-side display condition left after the first coordinate has been split
off in Section 3.3: the displayed tail carries exactly the expected second
coordinate `x_1 + y_1`.
-/
def SecondDisplayAdditive {n : ℕ}
    {T : ParameterIndex (n + 2) → ℤ}
    (M : CPres (n + 2) T) : Prop :=
  ∀ x y : Fin (n + 2) → ℤ,
    M.coord (M.firstConjugatedProduct x (y 0) *
      M.normalWord (withoutFirstCoord y)) 1 = x 1 + y 1

theorem second_display_additive {n : ℕ}
    {T : ParameterIndex (n + 2) → ℤ}
    (M : CPres (n + 2) T)
    (hFirst : FirstDisplayTail M)
    (hSecond : CoordinateAdditive M 1) :
    SecondDisplayAdditive M := by
  intro x y
  let tailProduct :=
    M.firstConjugatedProduct x (y 0) * M.normalWord (withoutFirstCoord y)
  have htail : M.coord tailProduct 0 = 0 := hFirst x y
  have hprod := hSecond (M.normalWord x) (M.normalWord y)
  rw [M.coord_normalWord x, M.coord_normalWord y] at hprod
  have hdisplay := M.normal_conjugated_tail x y
  calc
    M.coord tailProduct 1 =
        M.coord (M.gen 0 ^ (x 0 + y 0) * tailProduct) 1 := by
          symm
          simpa using
            M.coord_gen_succ
              (x 0 + y 0) tailProduct htail 0
    _ = M.coord (M.normalWord x * M.normalWord y) 1 := by
          rw [hdisplay]
          simp [tailProduct]
          group
    _ = x 1 + y 1 := hprod

theorem second_display_tail {n : ℕ}
    {T : ParameterIndex (n + 2) → ℤ}
    (M : CPres (n + 2) T)
    (hFirst : FirstDisplayTail M)
    (hSecond : SecondDisplayAdditive M) :
    CoordinateAdditive M 1 := by
  rw [M.additive_multiplication_tuple 1]
  intro x y
  have hdisplay :=
    congrFun (M.multiplication_coord_conjugated x y) 1
  let tailProduct :=
    M.firstConjugatedProduct x (y 0) * M.normalWord (withoutFirstCoord y)
  have htail : M.coord tailProduct 0 = 0 := hFirst x y
  rw [hdisplay]
  have hassoc :
      M.gen 0 ^ (x 0 + y 0) *
          M.firstConjugatedProduct x (y 0) *
          M.normalWord (withoutFirstCoord y) =
        M.gen 0 ^ (x 0 + y 0) * tailProduct := by
    simp [tailProduct]
    group
  rw [hassoc]
  have hdrop :=
    M.coord_gen_succ (x 0 + y 0) tailProduct htail
      (0 : Fin (n + 1))
  change
    M.coord (M.gen 0 ^ (x 0 + y 0) * tailProduct)
        (Fin.succ (0 : Fin (n + 1))) =
      x (Fin.succ (0 : Fin (n + 1))) + y (Fin.succ (0 : Fin (n + 1)))
  rw [hdrop]
  change M.coord tailProduct 1 = x 1 + y 1
  exact hSecond x y

theorem second_additive_display {n : ℕ}
    {T : ParameterIndex (n + 2) → ℤ}
    (M : CPres (n + 2) T)
    (hFirst : FirstDisplayTail M) :
    CoordinateAdditive M 1 ↔ SecondDisplayAdditive M := by
  constructor
  · exact M.second_display_additive hFirst
  · exact M.second_display_tail hFirst

theorem consistent_display_additive {n : ℕ}
    {T : ParameterIndex (n + 2) → ℤ}
    (M : CPres (n + 2) T)
    (hFirst : FirstDisplayTail M)
    (hSecond : SecondDisplayAdditive M) :
    IsConsistent (secondParameterTuple T) :=
  consistent_second_parameter M
    ((M.second_additive_display hFirst).mpr hSecond)

theorem consistency_locus_additive
    {n : ℕ} {T : ParameterIndex (n + 2) → ℤ}
    (M : CPres (n + 2) T)
    (hFirst : FirstDisplayTail M)
    (hSecond : SecondDisplayAdditive M) :
    secondParameterTuple T ∈ consistencyLocus (n + 1) :=
  consistent_display_additive M hFirst hSecond

theorem consistent_parameter_display
    {n : ℕ} {T : ParameterIndex (n + 1) → ℤ}
    (M : CPres (n + 1) T)
    (hTail : FirstDisplayTail M) :
    IsConsistent (firstParameterTuple T) :=
  consistent_tuple_additive M
    ((M.coordinate_additive_display).mpr hTail)

theorem parameter_consistency_locus
    {n : ℕ} {T : ParameterIndex (n + 1) → ℤ}
    (M : CPres (n + 1) T)
    (hTail : FirstDisplayTail M) :
    firstParameterTuple T ∈ consistencyLocus n :=
  consistent_parameter_display M hTail

lemma relationTail_last {n : ℕ} {T : ParameterIndex (n + 1) → ℤ}
    (M : CPres (n + 1) T)
    (i : Fin (n + 1)) (h : i < Fin.last n) :
    relationTail M.gen T i (Fin.last n) h = 1 := by
  simp [relationTail, upperIndices, not_lt_of_ge (Fin.le_last _)]

lemma upperIndices_penultimate {n : ℕ} :
    upperIndices (Fin.castSucc (Fin.last n) : Fin (n + 2)) =
      [⟨Fin.last (n + 1), Fin.castSucc_lt_last _⟩] := by
  unfold upperIndices
  rw [List.finRange_succ_last]
  simp [Fin.castSucc_lt_castSucc_iff, Fin.castSucc_lt_last,
    not_lt_of_ge (Fin.le_last _)]

lemma relationTail_penultimate {n : ℕ} {T : ParameterIndex (n + 2) → ℤ}
    (M : CPres (n + 2) T)
    (i : Fin (n + 2)) (h : i < Fin.castSucc (Fin.last n)) :
    relationTail M.gen T i (Fin.castSucc (Fin.last n)) h =
      M.gen (Fin.last (n + 1)) ^
        T ⟨(i, Fin.castSucc (Fin.last n), Fin.last (n + 1)),
          h, Fin.castSucc_lt_last _⟩ := by
  simp [relationTail, upperIndices_penultimate]

/-- The last generator is central among the chosen generators. -/
lemma gen_commute {n : ℕ} {T : ParameterIndex (n + 1) → ℤ}
    (M : CPres (n + 1) T)
    (i : Fin (n + 1)) :
    Commute (M.gen (Fin.last n)) (M.gen i) := by
  by_cases hi : i = Fin.last n
  · subst i
    exact Commute.refl _
  · have hlt : i < Fin.last n := Fin.lt_last_iff_ne_last.mpr hi
    have hrel := M.relation i (Fin.last n) hlt
    rw [show relationTail M.coords.gen T i (Fin.last n) hlt = 1 by
      simpa [gen] using relationTail_last M i hlt] at hrel
    simpa [Commute, SemiconjBy] using hrel

/-- The last generator commutes with every normal word. -/
lemma gen_commute_normal {n : ℕ} {T : ParameterIndex (n + 1) → ℤ}
    (M : CPres (n + 1) T)
    (x : Fin (n + 1) → ℤ) :
    Commute (M.gen (Fin.last n)) (M.normalWord x) := by
  unfold normalWord orderedZPow
  apply Commute.list_prod_right
  intro y hy
  rcases List.mem_map.mp hy with ⟨i, _hi, rfl⟩
  exact (M.gen_commute i).zpow_right (x i)

lemma gen_last_commute {n : ℕ} {T : ParameterIndex (n + 1) → ℤ}
    (M : CPres (n + 1) T) (g : M.G) :
    Commute (M.gen (Fin.last n)) g := by
  rw [← M.normalWord_coord g]
  exact M.gen_commute_normal (M.coord g)

/--
Unconditional last-generator conjugation: since the last generator is central,
left conjugating a power of it by any generator leaves only the last coordinate.
-/
theorem left_tuple_last {n : ℕ} {T : ParameterIndex (n + 1) → ℤ}
    (M : CPres (n + 1) T)
    (i : Fin (n + 1)) (u v : ℤ) :
    M.leftConjugationTuple i (Fin.last n) u v =
      singleCoord (Fin.last n) u := by
  change M.coord (M.gen i ^ (-v) * M.gen (Fin.last n) ^ u * M.gen i ^ v) =
    singleCoord (Fin.last n) u
  rw [← M.coord_gen_zpow (Fin.last n) u]
  congr 1
  have hcomm : Commute (M.gen (Fin.last n) ^ u) (M.gen i ^ v) :=
    (M.gen_commute i).zpow_left u |>.zpow_right v
  calc
    M.gen i ^ (-v) * M.gen (Fin.last n) ^ u * M.gen i ^ v =
        M.gen i ^ (-v) * (M.gen (Fin.last n) ^ u * M.gen i ^ v) := by
          group
    _ = M.gen i ^ (-v) * (M.gen i ^ v * M.gen (Fin.last n) ^ u) := by
          rw [hcomm.eq]
    _ = M.gen (Fin.last n) ^ u := by
          have hcancel : M.gen i ^ (-v) * M.gen i ^ v = 1 := by
            rw [← zpow_add]
            ring_nf
            simp
          rw [← mul_assoc, hcancel, one_mul]

lemma left_conjugation_last {n : ℕ} {T : ParameterIndex (n + 1) → ℤ}
    (M : CPres (n + 1) T)
    (i k : Fin (n + 1)) (u v : ℤ) :
    M.leftConjugationTuple i (Fin.last n) u v k =
      if k = Fin.last n then u else 0 := by
  rw [M.left_tuple_last]
  rfl

lemma tuple_last_ne {n : ℕ}
    {T : ParameterIndex (n + 1) → ℤ}
    (M : CPres (n + 1) T)
    (i k : Fin (n + 1)) (u v : ℤ) (hk : k ≠ Fin.last n) :
    M.leftConjugationTuple i (Fin.last n) u v k = 0 := by
  rw [M.left_conjugation_last]
  simp [hk]

/--
Unconditional last-generator product conjugation: since the last generator is
central, `a_last^u a_i^v` is already the normal word with coordinate `v` at
`i` and coordinate `u` at the last generator.
-/
theorem tuple_last {n : ℕ} {T : ParameterIndex (n + 1) → ℤ}
    (M : CPres (n + 1) T)
    (i : Fin (n + 1)) (hi : i < Fin.last n) (u v : ℤ) :
    M.conjugationTuple i (Fin.last n) u v =
      fun k => if k = i then v else if k = Fin.last n then u else 0 := by
  let x : Fin (n + 1) → ℤ :=
    fun k => if k = i then v else if k = Fin.last n then u else 0
  change M.coord (M.gen (Fin.last n) ^ u * M.gen i ^ v) = x
  have hx : x = addLastCoord (singleCoord i v) u := by
    funext k
    by_cases hk : k = Fin.last n
    · subst k
      simp [x, addLastCoord, singleCoord, ne_of_gt hi]
    · simp [x, addLastCoord, singleCoord, hk]
  apply M.normalWord_injective
  rw [M.normalWord_coord]
  rw [hx, M.normal_last_coord, M.normal_single_coord]
  exact ((M.gen_commute i).zpow_zpow u v).eq

lemma conjugation_last {n : ℕ}
    {T : ParameterIndex (n + 1) → ℤ}
    (M : CPres (n + 1) T)
    (i k : Fin (n + 1)) (hi : i < Fin.last n) (u v : ℤ) :
    M.conjugationTuple i (Fin.last n) u v k =
      if k = i then v else if k = Fin.last n then u else 0 := by
  rw [M.tuple_last i hi u v]

/--
Penultimate-generator product conjugation in every rank.  Since the only
relation tail above the penultimate generator is the central last generator,
the all-power collection is a class-two central-tail formula.
-/
theorem gen_penultimate_zpow {n : ℕ}
    {T : ParameterIndex (n + 2) → ℤ}
    (M : CPres (n + 2) T)
    (i : Fin (n + 2)) (hi : i < Fin.castSucc (Fin.last n))
    (u v : ℤ) :
    M.gen (Fin.castSucc (Fin.last n)) ^ u * M.gen i ^ v =
      M.gen i ^ v * M.gen (Fin.castSucc (Fin.last n)) ^ u *
        M.gen (Fin.last (n + 1)) ^
          (T ⟨(i, Fin.castSucc (Fin.last n), Fin.last (n + 1)),
              hi, Fin.castSucc_lt_last _⟩ * (u * v)) := by
  let j : Fin (n + 2) := Fin.castSucc (Fin.last n)
  let last : Fin (n + 2) := Fin.last (n + 1)
  let I : ParameterIndex (n + 2) :=
    ⟨(i, j, last), hi, by
      simp [j, last]⟩
  have hBA : M.gen j * M.gen i = M.gen i * M.gen j * M.gen last ^ T I := by
    have htail : relationTail M.coords.gen T i j hi =
        M.coords.gen last ^ T I := by
      simpa [gen, j, last, I] using M.relationTail_penultimate i hi
    simpa [gen, j, last, I, htail] using M.relation i j hi
  have hcollect := zpow_mul_central
    (A := M.gen i) (B := M.gen j) (C := M.gen last ^ T I)
    ((M.gen_commute i).zpow_left (T I))
    ((M.gen_commute j).zpow_left (T I)) hBA u v
  rw [hcollect]
  rw [← zpow_mul]

theorem conjugationTuple_penultimate {n : ℕ}
    {T : ParameterIndex (n + 2) → ℤ}
    (M : CPres (n + 2) T)
    (i : Fin (n + 2)) (hi : i < Fin.castSucc (Fin.last n))
    (u v : ℤ) :
    M.conjugationTuple i (Fin.castSucc (Fin.last n)) u v =
      fun k =>
        if k = i then v else if k = Fin.castSucc (Fin.last n) then u
        else if k = Fin.last (n + 1) then
          T ⟨(i, Fin.castSucc (Fin.last n), Fin.last (n + 1)),
            hi, Fin.castSucc_lt_last _⟩ * (u * v)
        else 0 := by
  let j : Fin (n + 2) := Fin.castSucc (Fin.last n)
  let last : Fin (n + 2) := Fin.last (n + 1)
  let c : ℤ :=
    T ⟨(i, j, last), hi, by
      simp [j, last]⟩ * (u * v)
  let x : Fin (n + 2) → ℤ :=
    fun k => if k = i then v else if k = j then u else if k = last then c else 0
  change M.coord (M.gen j ^ u * M.gen i ^ v) = x
  have hx :
      x = addLastCoord
        (fun k => if k = i then v else if k = j then u else 0) c := by
    funext k
    by_cases hlast : k = last
    · subst k
      have hjltlast : j < last := by simp [j, last]
      have hilast : last ≠ i := ne_of_gt (hi.trans hjltlast)
      have hjlast : last ≠ j := ne_of_gt hjltlast
      simp [x, addLastCoord, hilast, hjlast, c, last]
    · simp [x, addLastCoord, hlast, last]
  apply M.normalWord_injective
  rw [M.normalWord_coord]
  rw [hx, M.normal_last_coord, M.normal_two_coord i j hi]
  exact M.gen_penultimate_zpow i hi u v

lemma conjugation_tuple_penultimate {n : ℕ}
    {T : ParameterIndex (n + 2) → ℤ}
    (M : CPres (n + 2) T)
    (i k : Fin (n + 2)) (hi : i < Fin.castSucc (Fin.last n))
    (u v : ℤ) :
    M.conjugationTuple i (Fin.castSucc (Fin.last n)) u v k =
      if k = i then v else if k = Fin.castSucc (Fin.last n) then u
      else if k = Fin.last (n + 1) then
        T ⟨(i, Fin.castSucc (Fin.last n), Fin.last (n + 1)),
          hi, Fin.castSucc_lt_last _⟩ * (u * v)
      else 0 := by
  rw [M.conjugationTuple_penultimate i hi u v]

lemma normal_word_three
    {T : ParameterIndex 3 → ℤ} (M : CPres 3 T)
    (x : Fin 3 → ℤ) :
    M.normalWord x = M.gen 0 ^ x 0 * M.gen 1 ^ x 1 * M.gen 2 ^ x 2 := by
  norm_num [normalWord, orderedZPow, gen, List.finRange]
  group

lemma relation_tail_one
    {T : ParameterIndex 3 → ℤ} (M : CPres 3 T) :
    relationTail M.gen T 0 1 (by decide) =
      M.gen 2 ^
        T ⟨((0 : Fin 3), (1 : Fin 3), (2 : Fin 3)), by decide, by decide⟩ := by
  norm_num [relationTail, upperIndices, gen, List.finRange]
  simp

/--
The unique nontrivial rank-three collection identity.  The last generator is
central, so the single relation `a₁ a₀ = a₀ a₁ a₂^t` collects all integer
powers with correction exponent `t * u * v`.
-/
theorem gen_zpow_three
    {T : ParameterIndex 3 → ℤ} (M : CPres 3 T)
    (u v : ℤ) :
    M.gen 1 ^ u * M.gen 0 ^ v =
      M.gen 0 ^ v * M.gen 1 ^ u *
        M.gen 2 ^
          (T ⟨((0 : Fin 3), (1 : Fin 3), (2 : Fin 3)), by decide, by decide⟩ *
            (u * v)) := by
  let I : ParameterIndex 3 :=
    ⟨((0 : Fin 3), (1 : Fin 3), (2 : Fin 3)), by decide, by decide⟩
  have hcollect := zpow_mul_central
    (A := M.gen 0) (B := M.gen 1) (C := M.gen 2 ^ T I)
    ((M.gen_commute 0).zpow_left (T I))
    ((M.gen_commute 1).zpow_left (T I))
    (by
      have htail : relationTail M.coords.gen T 0 1 (by decide) =
          M.coords.gen 2 ^ T I := by
        simpa [gen, I] using M.relation_tail_one
      simpa [gen, I, htail] using M.relation 0 1 (by decide))
    u v
  rw [hcollect]
  rw [← zpow_mul]

/--
Normal coordinates for `a₁^u a₀^v` in rank three.  This removes the
represented-conjugation hypothesis for the first non-abelian rank.
-/
theorem conjugation_zero_three
    {T : ParameterIndex 3 → ℤ} (M : CPres 3 T)
    (u v : ℤ) :
    M.conjugationTuple 0 1 u v =
      fun k => if k = 0 then v else if k = 1 then u else
        T ⟨((0 : Fin 3), (1 : Fin 3), (2 : Fin 3)), by decide, by decide⟩ *
          (u * v) := by
  let I : ParameterIndex 3 :=
    ⟨((0 : Fin 3), (1 : Fin 3), (2 : Fin 3)), by decide, by decide⟩
  let x : Fin 3 → ℤ :=
    fun k => if k = 0 then v else if k = 1 then u else T I * (u * v)
  change M.coord (M.gen 1 ^ u * M.gen 0 ^ v) = x
  apply M.normalWord_injective
  rw [M.normalWord_coord]
  rw [M.normal_word_three]
  have hx0 : x 0 = v := by simp [x]
  have hx1 : x 1 = u := by simp [x]
  have hx2 : x 2 = T I * (u * v) := by
    have h20 : (2 : Fin 3) ≠ 0 := by decide
    have h21 : (2 : Fin 3) ≠ 1 := by decide
    simp [x, h20, h21]
  rw [hx0, hx1, hx2]
  exact M.gen_zpow_three u v

lemma conjugation_tuple_three
    {T : ParameterIndex 3 → ℤ} (M : CPres 3 T)
    (u v : ℤ) (k : Fin 3) :
    M.conjugationTuple 0 1 u v k =
      if k = 0 then v else if k = 1 then u else
        T ⟨((0 : Fin 3), (1 : Fin 3), (2 : Fin 3)), by decide, by decide⟩ *
          (u * v) := by
  rw [M.conjugation_zero_three u v]

lemma normal_word_four
    {T : ParameterIndex 4 → ℤ} (M : CPres 4 T)
    (x : Fin 4 → ℤ) :
    M.normalWord x =
      M.gen 0 ^ x 0 * M.gen 1 ^ x 1 *
        M.gen 2 ^ x 2 * M.gen 3 ^ x 3 := by
  norm_num [normalWord, orderedZPow, gen, List.finRange]
  rw [show (Fin.succ (2 : Fin 3) : Fin 4) = 3 by decide]
  group

lemma relation_tail_four
    {T : ParameterIndex 4 → ℤ} (M : CPres 4 T) :
    relationTail M.gen T 0 1 (by decide) =
      M.gen 2 ^
        T ⟨((0 : Fin 4), (1 : Fin 4), (2 : Fin 4)), by decide, by decide⟩ *
      M.gen 3 ^
        T ⟨((0 : Fin 4), (1 : Fin 4), (3 : Fin 4)), by decide, by decide⟩ := by
  norm_num [relationTail, upperIndices, gen, List.finRange]
  simp

lemma relation_four_two
    {T : ParameterIndex 4 → ℤ} (M : CPres 4 T) :
    relationTail M.gen T 0 2 (by decide) =
      M.gen 3 ^
        T ⟨((0 : Fin 4), (2 : Fin 4), (3 : Fin 4)), by decide, by decide⟩ := by
  norm_num [relationTail, upperIndices, gen, List.finRange]
  simp

lemma relation_tail_two
    {T : ParameterIndex 4 → ℤ} (M : CPres 4 T) :
    relationTail M.gen T 1 2 (by decide) =
      M.gen 3 ^
        T ⟨((1 : Fin 4), (2 : Fin 4), (3 : Fin 4)), by decide, by decide⟩ := by
  norm_num [relationTail, upperIndices, gen, List.finRange]
  simp

theorem gen_two_four
    {T : ParameterIndex 4 → ℤ} (M : CPres 4 T)
    (u v : ℤ) :
    M.gen 2 ^ u * M.gen 0 ^ v =
      M.gen 0 ^ v * M.gen 2 ^ u *
        M.gen 3 ^
          (T ⟨((0 : Fin 4), (2 : Fin 4), (3 : Fin 4)), by decide, by decide⟩ *
            (u * v)) := by
  let I : ParameterIndex 4 :=
    ⟨((0 : Fin 4), (2 : Fin 4), (3 : Fin 4)), by decide, by decide⟩
  have hcollect := zpow_mul_central
    (A := M.gen 0) (B := M.gen 2) (C := M.gen 3 ^ T I)
    ((M.gen_commute 0).zpow_left (T I))
    ((M.gen_commute 2).zpow_left (T I))
    (by
      have htail : relationTail M.coords.gen T 0 2 (by decide) =
          M.coords.gen 3 ^ T I := by
        simpa [gen, I] using M.relation_four_two
      simpa [gen, I, htail] using M.relation 0 2 (by decide))
    u v
  rw [hcollect]
  rw [← zpow_mul]

/--
The rank-four one-sided `(0,1)` collection formula.  Moving one `a₁` past
`a₀^v` creates the expected `a₂` tail and the quadratic central correction
from subsequently moving that `a₂` tail past the `a₀` powers.
-/
theorem gen_zero_four
    {T : ParameterIndex 4 → ℤ} (M : CPres 4 T)
    (v : ℤ) :
    M.gen 1 * M.gen 0 ^ v =
      M.gen 0 ^ v * M.gen 1 *
        M.gen 2 ^
          (T ⟨((0 : Fin 4), (1 : Fin 4), (2 : Fin 4)), by decide, by decide⟩ *
            v) *
        M.gen 3 ^
          (T ⟨((0 : Fin 4), (1 : Fin 4), (3 : Fin 4)), by decide, by decide⟩ *
              v +
            T ⟨((0 : Fin 4), (1 : Fin 4), (2 : Fin 4)), by decide, by decide⟩ *
              T ⟨((0 : Fin 4), (2 : Fin 4), (3 : Fin 4)), by decide, by decide⟩ *
                chooseTwoInt v) := by
  let I012 : ParameterIndex 4 :=
    ⟨((0 : Fin 4), (1 : Fin 4), (2 : Fin 4)), by decide, by decide⟩
  let I013 : ParameterIndex 4 :=
    ⟨((0 : Fin 4), (1 : Fin 4), (3 : Fin 4)), by decide, by decide⟩
  let I023 : ParameterIndex 4 :=
    ⟨((0 : Fin 4), (2 : Fin 4), (3 : Fin 4)), by decide, by decide⟩
  have hBA : M.gen 1 * M.gen 0 =
      M.gen 0 * M.gen 1 * M.gen 2 ^ T I012 * M.gen 3 ^ T I013 := by
    have htail : relationTail M.coords.gen T 0 1 (by decide) =
        M.coords.gen 2 ^ T I012 * M.coords.gen 3 ^ T I013 := by
      simpa [gen, I012, I013] using M.relation_tail_four
    simpa [gen, I012, I013, htail, mul_assoc] using
      M.relation 0 1 (by decide)
  have hCA : M.gen 2 * M.gen 0 =
      M.gen 0 * M.gen 2 * M.gen 3 ^ T I023 := by
    have htail : relationTail M.coords.gen T 0 2 (by decide) =
        M.coords.gen 3 ^ T I023 := by
      simpa [gen, I023] using M.relation_four_two
    simpa [gen, I023, htail, mul_assoc] using
      M.relation 0 2 (by decide)
  simpa [I012, I013, I023, mul_assoc] using
    mul_zpow_central
      (A := M.gen 0) (B := M.gen 1) (C := M.gen 2) (Z := M.gen 3)
      (p := T I012) (q := T I013) (r := T I023)
      (M.gen_commute 0) (M.gen_commute 2) hBA hCA v

/--
The full rank-four `(0,1)` collection formula.  This is the all-`u` version
of `gen_zero_four`; the extra quadratic term records the
central contribution from moving the accumulated `a₂` tail past `a₁^u`.
-/
theorem gen_zpow_four
    {T : ParameterIndex 4 → ℤ} (M : CPres 4 T)
    (u v : ℤ) :
    M.gen 1 ^ u * M.gen 0 ^ v =
      M.gen 0 ^ v * M.gen 1 ^ u *
        M.gen 2 ^
          (T ⟨((0 : Fin 4), (1 : Fin 4), (2 : Fin 4)), by decide, by decide⟩ *
            (u * v)) *
        M.gen 3 ^
          twoStepExponent
            (T ⟨((0 : Fin 4), (1 : Fin 4), (2 : Fin 4)), by decide, by decide⟩)
            (T ⟨((0 : Fin 4), (1 : Fin 4), (3 : Fin 4)), by decide, by decide⟩)
            (T ⟨((0 : Fin 4), (2 : Fin 4), (3 : Fin 4)), by decide, by decide⟩)
            (T ⟨((1 : Fin 4), (2 : Fin 4), (3 : Fin 4)), by decide, by decide⟩)
            u v := by
  let I012 : ParameterIndex 4 :=
    ⟨((0 : Fin 4), (1 : Fin 4), (2 : Fin 4)), by decide, by decide⟩
  let I013 : ParameterIndex 4 :=
    ⟨((0 : Fin 4), (1 : Fin 4), (3 : Fin 4)), by decide, by decide⟩
  let I023 : ParameterIndex 4 :=
    ⟨((0 : Fin 4), (2 : Fin 4), (3 : Fin 4)), by decide, by decide⟩
  let I123 : ParameterIndex 4 :=
    ⟨((1 : Fin 4), (2 : Fin 4), (3 : Fin 4)), by decide, by decide⟩
  have hBA : M.gen 1 * M.gen 0 =
      M.gen 0 * M.gen 1 * M.gen 2 ^ T I012 * M.gen 3 ^ T I013 := by
    have htail : relationTail M.coords.gen T 0 1 (by decide) =
        M.coords.gen 2 ^ T I012 * M.coords.gen 3 ^ T I013 := by
      simpa [gen, I012, I013] using M.relation_tail_four
    simpa [gen, I012, I013, htail, mul_assoc] using
      M.relation 0 1 (by decide)
  have hCA : M.gen 2 * M.gen 0 =
      M.gen 0 * M.gen 2 * M.gen 3 ^ T I023 := by
    have htail : relationTail M.coords.gen T 0 2 (by decide) =
        M.coords.gen 3 ^ T I023 := by
      simpa [gen, I023] using M.relation_four_two
    simpa [gen, I023, htail, mul_assoc] using
      M.relation 0 2 (by decide)
  have hCB : M.gen 2 * M.gen 1 =
      M.gen 1 * M.gen 2 * M.gen 3 ^ T I123 := by
    have htail : relationTail M.coords.gen T 1 2 (by decide) =
        M.coords.gen 3 ^ T I123 := by
      simpa [gen, I123] using M.relation_tail_two
    simpa [gen, I123, htail, mul_assoc] using
      M.relation 1 2 (by decide)
  simpa [I012, I013, I023, I123, mul_assoc] using
    zpow_step_central
      (A := M.gen 0) (B := M.gen 1) (C := M.gen 2) (Z := M.gen 3)
      (p := T I012) (q := T I013) (r := T I023) (s := T I123)
      (M.gen_commute 0) (M.gen_commute 1)
      (M.gen_commute 2) hBA hCA hCB u v

/--
Normal coordinates for the `u = 1` slice of the rank-four `(0,1)`
conjugation tuple.
-/
theorem conjugation_one_four
    {T : ParameterIndex 4 → ℤ} (M : CPres 4 T)
    (v : ℤ) :
    M.conjugationTuple 0 1 1 v =
      fun k => if k = 0 then v else if k = 1 then 1 else if k = 2 then
        T ⟨((0 : Fin 4), (1 : Fin 4), (2 : Fin 4)), by decide, by decide⟩ *
          v
      else
        T ⟨((0 : Fin 4), (1 : Fin 4), (3 : Fin 4)), by decide, by decide⟩ *
            v +
          T ⟨((0 : Fin 4), (1 : Fin 4), (2 : Fin 4)), by decide, by decide⟩ *
            T ⟨((0 : Fin 4), (2 : Fin 4), (3 : Fin 4)), by decide, by decide⟩ *
              chooseTwoInt v := by
  let I012 : ParameterIndex 4 :=
    ⟨((0 : Fin 4), (1 : Fin 4), (2 : Fin 4)), by decide, by decide⟩
  let I013 : ParameterIndex 4 :=
    ⟨((0 : Fin 4), (1 : Fin 4), (3 : Fin 4)), by decide, by decide⟩
  let I023 : ParameterIndex 4 :=
    ⟨((0 : Fin 4), (2 : Fin 4), (3 : Fin 4)), by decide, by decide⟩
  let x : Fin 4 → ℤ :=
    fun k => if k = 0 then v else if k = 1 then 1 else if k = 2 then
      T I012 * v else T I013 * v + T I012 * T I023 * chooseTwoInt v
  change M.coord (M.gen 1 ^ (1 : ℤ) * M.gen 0 ^ v) = x
  apply M.normalWord_injective
  rw [M.normalWord_coord]
  rw [M.normal_word_four]
  have hx0 : x 0 = v := by simp [x]
  have hx1 : x 1 = 1 := by simp [x]
  have hx2 : x 2 = T I012 * v := by simp [x]
  have hx3 : x 3 = T I013 * v + T I012 * T I023 * chooseTwoInt v := by
    simp [x]
  rw [hx0, hx1, hx2, hx3]
  simp only [Fin.isValue, zpow_one]
  exact M.gen_zero_four v

lemma conjugation_tuple_four
    {T : ParameterIndex 4 → ℤ} (M : CPres 4 T)
    (v : ℤ) (k : Fin 4) :
    M.conjugationTuple 0 1 1 v k =
      if k = 0 then v else if k = 1 then 1 else if k = 2 then
        T ⟨((0 : Fin 4), (1 : Fin 4), (2 : Fin 4)), by decide, by decide⟩ *
          v
      else
        T ⟨((0 : Fin 4), (1 : Fin 4), (3 : Fin 4)), by decide, by decide⟩ *
            v +
          T ⟨((0 : Fin 4), (1 : Fin 4), (2 : Fin 4)), by decide, by decide⟩ *
            T ⟨((0 : Fin 4), (2 : Fin 4), (3 : Fin 4)), by decide, by decide⟩ *
              chooseTwoInt v := by
  rw [M.conjugation_one_four v]

/--
Normal coordinates for the full rank-four `(0,1)` conjugation tuple.
-/
theorem tuple_zero_four
    {T : ParameterIndex 4 → ℤ} (M : CPres 4 T)
    (u v : ℤ) :
    M.conjugationTuple 0 1 u v =
      fun k => if k = 0 then v else if k = 1 then u else if k = 2 then
        T ⟨((0 : Fin 4), (1 : Fin 4), (2 : Fin 4)), by decide, by decide⟩ *
          (u * v)
      else
        twoStepExponent
          (T ⟨((0 : Fin 4), (1 : Fin 4), (2 : Fin 4)), by decide, by decide⟩)
          (T ⟨((0 : Fin 4), (1 : Fin 4), (3 : Fin 4)), by decide, by decide⟩)
          (T ⟨((0 : Fin 4), (2 : Fin 4), (3 : Fin 4)), by decide, by decide⟩)
          (T ⟨((1 : Fin 4), (2 : Fin 4), (3 : Fin 4)), by decide, by decide⟩)
          u v := by
  let I012 : ParameterIndex 4 :=
    ⟨((0 : Fin 4), (1 : Fin 4), (2 : Fin 4)), by decide, by decide⟩
  let I013 : ParameterIndex 4 :=
    ⟨((0 : Fin 4), (1 : Fin 4), (3 : Fin 4)), by decide, by decide⟩
  let I023 : ParameterIndex 4 :=
    ⟨((0 : Fin 4), (2 : Fin 4), (3 : Fin 4)), by decide, by decide⟩
  let I123 : ParameterIndex 4 :=
    ⟨((1 : Fin 4), (2 : Fin 4), (3 : Fin 4)), by decide, by decide⟩
  let x : Fin 4 → ℤ :=
    fun k => if k = 0 then v else if k = 1 then u else if k = 2 then
      T I012 * (u * v) else
        twoStepExponent (T I012) (T I013) (T I023) (T I123) u v
  change M.coord (M.gen 1 ^ u * M.gen 0 ^ v) = x
  apply M.normalWord_injective
  rw [M.normalWord_coord]
  rw [M.normal_word_four]
  have hx0 : x 0 = v := by simp [x]
  have hx1 : x 1 = u := by simp [x]
  have hx2 : x 2 = T I012 * (u * v) := by simp [x]
  have hx3 :
      x 3 =
        twoStepExponent (T I012) (T I013) (T I023) (T I123) u v := by
    simp [x]
  rw [hx0, hx1, hx2, hx3]
  exact M.gen_zpow_four u v

lemma conjugation_zero_four
    {T : ParameterIndex 4 → ℤ} (M : CPres 4 T)
    (u v : ℤ) (k : Fin 4) :
    M.conjugationTuple 0 1 u v k =
      if k = 0 then v else if k = 1 then u else if k = 2 then
        T ⟨((0 : Fin 4), (1 : Fin 4), (2 : Fin 4)), by decide, by decide⟩ *
          (u * v)
      else
        twoStepExponent
          (T ⟨((0 : Fin 4), (1 : Fin 4), (2 : Fin 4)), by decide, by decide⟩)
          (T ⟨((0 : Fin 4), (1 : Fin 4), (3 : Fin 4)), by decide, by decide⟩)
          (T ⟨((0 : Fin 4), (2 : Fin 4), (3 : Fin 4)), by decide, by decide⟩)
          (T ⟨((1 : Fin 4), (2 : Fin 4), (3 : Fin 4)), by decide, by decide⟩)
          u v := by
  rw [M.tuple_zero_four u v]

theorem gen_two_zpow
    {T : ParameterIndex 4 → ℤ} (M : CPres 4 T)
    (u v : ℤ) :
    M.gen 2 ^ u * M.gen 1 ^ v =
      M.gen 1 ^ v * M.gen 2 ^ u *
        M.gen 3 ^
          (T ⟨((1 : Fin 4), (2 : Fin 4), (3 : Fin 4)), by decide, by decide⟩ *
            (u * v)) := by
  let I : ParameterIndex 4 :=
    ⟨((1 : Fin 4), (2 : Fin 4), (3 : Fin 4)), by decide, by decide⟩
  have hcollect := zpow_mul_central
    (A := M.gen 1) (B := M.gen 2) (C := M.gen 3 ^ T I)
    ((M.gen_commute 1).zpow_left (T I))
    ((M.gen_commute 2).zpow_left (T I))
    (by
      have htail : relationTail M.coords.gen T 1 2 (by decide) =
          M.coords.gen 3 ^ T I := by
        simpa [gen, I] using M.relation_tail_two
      simpa [gen, I, htail] using M.relation 1 2 (by decide))
    u v
  rw [hcollect]
  rw [← zpow_mul]

theorem tuple_two_four
    {T : ParameterIndex 4 → ℤ} (M : CPres 4 T)
    (u v : ℤ) :
    M.conjugationTuple 0 2 u v =
      fun k => if k = 0 then v else if k = 2 then u else if k = 3 then
        T ⟨((0 : Fin 4), (2 : Fin 4), (3 : Fin 4)), by decide, by decide⟩ *
          (u * v) else 0 := by
  let I : ParameterIndex 4 :=
    ⟨((0 : Fin 4), (2 : Fin 4), (3 : Fin 4)), by decide, by decide⟩
  let x : Fin 4 → ℤ :=
    fun k => if k = 0 then v else if k = 2 then u else if k = 3 then
      T I * (u * v) else 0
  change M.coord (M.gen 2 ^ u * M.gen 0 ^ v) = x
  apply M.normalWord_injective
  rw [M.normalWord_coord]
  rw [M.normal_word_four]
  have hx0 : x 0 = v := by simp [x]
  have hx1 : x 1 = 0 := by simp [x]
  have hx2 : x 2 = u := by simp [x]
  have hx3 : x 3 = T I * (u * v) := by simp [x]
  rw [hx0, hx1, hx2, hx3]
  simp only [Fin.isValue, zpow_zero, mul_one]
  exact M.gen_two_four u v

lemma conjugation_two_four
    {T : ParameterIndex 4 → ℤ} (M : CPres 4 T)
    (u v : ℤ) (k : Fin 4) :
    M.conjugationTuple 0 2 u v k =
      if k = 0 then v else if k = 2 then u else if k = 3 then
        T ⟨((0 : Fin 4), (2 : Fin 4), (3 : Fin 4)), by decide, by decide⟩ *
          (u * v) else 0 := by
  rw [M.tuple_two_four u v]

theorem tuple_one_four
    {T : ParameterIndex 4 → ℤ} (M : CPres 4 T)
    (u v : ℤ) :
    M.conjugationTuple 1 2 u v =
      fun k => if k = 1 then v else if k = 2 then u else if k = 3 then
        T ⟨((1 : Fin 4), (2 : Fin 4), (3 : Fin 4)), by decide, by decide⟩ *
          (u * v) else 0 := by
  let I : ParameterIndex 4 :=
    ⟨((1 : Fin 4), (2 : Fin 4), (3 : Fin 4)), by decide, by decide⟩
  let x : Fin 4 → ℤ :=
    fun k => if k = 1 then v else if k = 2 then u else if k = 3 then
      T I * (u * v) else 0
  change M.coord (M.gen 2 ^ u * M.gen 1 ^ v) = x
  apply M.normalWord_injective
  rw [M.normalWord_coord]
  rw [M.normal_word_four]
  have hx0 : x 0 = 0 := by simp [x]
  have hx1 : x 1 = v := by simp [x]
  have hx2 : x 2 = u := by simp [x]
  have hx3 : x 3 = T I * (u * v) := by simp [x]
  rw [hx0, hx1, hx2, hx3]
  simp only [Fin.isValue, zpow_zero, one_mul]
  exact M.gen_two_zpow u v

lemma conjugation_tuple_two
    {T : ParameterIndex 4 → ℤ} (M : CPres 4 T)
    (u v : ℤ) (k : Fin 4) :
    M.conjugationTuple 1 2 u v k =
      if k = 1 then v else if k = 2 then u else if k = 3 then
        T ⟨((1 : Fin 4), (2 : Fin 4), (3 : Fin 4)), by decide, by decide⟩ *
          (u * v) else 0 := by
  rw [M.tuple_one_four u v]

lemma conjugation_tuple_last {n : ℕ}
    {T : ParameterIndex (n + 2) → ℤ}
    (M : CPres (n + 2) T)
    (i : Fin (n + 2)) (u v : ℤ) :
    M.leftConjugationTuple i (Fin.last (n + 1)) u v 0 = 0 := by
  rw [M.left_conjugation_last]
  simp

instance zpowersLast_normal {n : ℕ} {T : ParameterIndex (n + 1) → ℤ}
    (M : CPres (n + 1) T) :
    (Subgroup.zpowers (M.gen (Fin.last n))).Normal where
  conj_mem g hg x := by
    rcases Subgroup.mem_zpowers_iff.mp hg with ⟨z, rfl⟩
    have hcomm : Commute (M.gen (Fin.last n) ^ z) x :=
      (M.gen_last_commute x).zpow_left z
    rw [show x * M.gen (Fin.last n) ^ z * x⁻¹ = M.gen (Fin.last n) ^ z by
      calc
        x * M.gen (Fin.last n) ^ z * x⁻¹ =
            (M.gen (Fin.last n) ^ z * x) * x⁻¹ := by rw [hcomm.symm.eq]
        _ = M.gen (Fin.last n) ^ z := by group]
    exact Subgroup.zpow_mem_zpowers (M.gen (Fin.last n)) z

lemma normal_snoc_zero {n : ℕ} {T : ParameterIndex (n + 1) → ℤ}
    (M : CPres (n + 1) T) (x : Fin n → ℤ) :
    M.normalWord (Fin.snoc x 0) =
      orderedZPow (fun i : Fin n => M.gen (Fin.castSucc i)) x := by
  change orderedZPow M.gen (Fin.snoc x 0) =
    orderedZPow (fun i : Fin n => M.gen (Fin.castSucc i)) x
  unfold orderedZPow
  rw [List.finRange_succ_last]
  simp [List.map_append, List.prod_append, Function.comp_def]

lemma z_cast_succ {n : ℕ}
    {T : ParameterIndex (n + 1) → ℤ}
    (M : CPres (n + 1) T) (x : Fin n → ℤ) :
    orderedZPow
        (fun i : Fin n =>
          QuotientGroup.mk' (Subgroup.zpowers (M.gen (Fin.last n))) (M.gen (Fin.castSucc i)))
        x =
      QuotientGroup.mk' (Subgroup.zpowers (M.gen (Fin.last n)))
        (M.normalWord (Fin.snoc x 0)) := by
  rw [normal_snoc_zero]
  unfold orderedZPow
  change
    (List.map
        (fun i : Fin n =>
          QuotientGroup.mk' (Subgroup.zpowers (M.gen (Fin.last n)))
            (M.gen (Fin.castSucc i)) ^ x i)
        (List.finRange n)).prod =
      QuotientGroup.mk' (Subgroup.zpowers (M.gen (Fin.last n)))
        ((List.map (fun i : Fin n => M.gen (Fin.castSucc i) ^ x i)
          (List.finRange n)).prod)
  rw [map_list_prod (QuotientGroup.mk' (Subgroup.zpowers (M.gen (Fin.last n))))]
  simp only [List.map_map]
  apply congrArg List.prod
  apply List.map_congr_left
  intro i _hi
  exact (map_zpow
    (QuotientGroup.mk' (Subgroup.zpowers (M.gen (Fin.last n))))
    (M.gen (Fin.castSucc i)) (x i)).symm

/--
Normal coordinates for the quotient `G / ⟨aₙ⟩`, with generators the images of
`a₁, ..., aₙ₋₁`.
-/
noncomputable def deleteLastSystem {n : ℕ}
    {T : ParameterIndex (n + 1) → ℤ}
    (M : CPres (n + 1) T) :
    NCSystem
      (M.G ⧸ Subgroup.zpowers (M.gen (Fin.last n))) n where
  gen := fun i =>
    QuotientGroup.mk' (Subgroup.zpowers (M.gen (Fin.last n))) (M.gen (Fin.castSucc i))
  normalForm_bijective := by
    constructor
    · intro x y hxy
      rw [z_cast_succ M x,
        z_cast_succ M y] at hxy
      rcases ((QuotientGroup.mk'_eq_mk'
          (N := Subgroup.zpowers (M.gen (Fin.last n)))).mp hxy) with ⟨g, hg, hgxy⟩
      rcases Subgroup.mem_zpowers_iff.mp hg with ⟨z, rfl⟩
      have hword :
          M.normalWord (addLastCoord (Fin.snoc x 0) z) =
            M.normalWord (Fin.snoc y 0) := by
        rw [M.normal_last_coord, hgxy]
      have hcoord := M.normalWord_injective hword
      funext i
      have hi := congrFun hcoord (Fin.castSucc i)
      simpa [addLastCoord] using hi
    · intro q
      rcases QuotientGroup.mk'_surjective
          (Subgroup.zpowers (M.gen (Fin.last n))) q with ⟨g, rfl⟩
      refine ⟨Fin.init (M.coord g), ?_⟩
      rw [z_cast_succ]
      have hword :
          M.normalWord (M.coord g) =
            M.normalWord (Fin.snoc (Fin.init (M.coord g)) 0) *
              M.gen (Fin.last n) ^ (M.coord g (Fin.last n)) := by
        have hfull := congrArg M.normalWord (last_snoc_init (M.coord g))
        rw [M.normal_last_coord] at hfull
        exact hfull.symm
      change
        QuotientGroup.mk' (Subgroup.zpowers (M.gen (Fin.last n)))
            (M.normalWord (Fin.snoc (Fin.init (M.coord g)) 0)) =
          QuotientGroup.mk' (Subgroup.zpowers (M.gen (Fin.last n))) g
      trans QuotientGroup.mk' (Subgroup.zpowers (M.gen (Fin.last n)))
        (M.normalWord (M.coord g))
      · rw [hword]
        simp [map_mul, map_zpow,
          (QuotientGroup.eq_one_iff (M.gen (Fin.last n))).mpr
            (Subgroup.mem_zpowers (M.gen (Fin.last n)))]
      · rw [M.normalWord_coord]

/-- The concrete quotient presentation for `W(T) = G(T) / ⟨aₙ⟩`. -/
noncomputable def deleteConsistentPresentation {n : ℕ}
    {T : ParameterIndex (n + 1) → ℤ}
    (M : CPres (n + 1) T) :
    CPres n (lastParameterTuple T) where
  G := M.G ⧸ Subgroup.zpowers (M.gen (Fin.last n))
  coords := M.deleteLastSystem
  relation := by
    intro i j hij
    have hlast :
        QuotientGroup.mk' (Subgroup.zpowers (M.gen (Fin.last n)))
            (M.gen (Fin.last n)) = 1 :=
      (QuotientGroup.eq_one_iff (M.gen (Fin.last n))).mpr
        (Subgroup.mem_zpowers (M.gen (Fin.last n)))
    have hrel :=
      relation_last_parameter M
        (QuotientGroup.mk' (Subgroup.zpowers (M.gen (Fin.last n))))
        hlast i j hij
    simpa [deleteLastSystem] using hrel

lemma last_consistent_presentation {n : ℕ}
    {T : ParameterIndex (n + 1) → ℤ}
    (M : CPres (n + 1) T) (x : Fin n → ℤ) :
    (M.deleteConsistentPresentation).normalWord x =
      QuotientGroup.mk' (Subgroup.zpowers (M.gen (Fin.last n)))
        (M.normalWord (Fin.snoc x 0)) := by
  simpa [deleteConsistentPresentation, CPres.normalWord,
    deleteLastSystem] using
      M.z_cast_succ x

lemma consistent_presentation_snoc {n : ℕ}
    {T : ParameterIndex (n + 1) → ℤ}
    (M : CPres (n + 1) T) (x : Fin n → ℤ) :
    (M.deleteConsistentPresentation).coord
        (QuotientGroup.mk' (Subgroup.zpowers (M.gen (Fin.last n)))
          (M.normalWord (Fin.snoc x 0))) = x := by
  rw [← M.last_consistent_presentation x]
  exact (M.deleteConsistentPresentation).coord_normalWord x

lemma consistent_presentation_init {n : ℕ}
    {T : ParameterIndex (n + 1) → ℤ}
    (M : CPres (n + 1) T) (x : Fin (n + 1) → ℤ) :
    (M.deleteConsistentPresentation).normalWord (Fin.init x) =
      QuotientGroup.mk' (Subgroup.zpowers (M.gen (Fin.last n)))
        (M.normalWord x) := by
  rw [M.last_consistent_presentation]
  have hword :
      M.normalWord x =
        M.normalWord (Fin.snoc (Fin.init x) 0) *
          M.gen (Fin.last n) ^ x (Fin.last n) := by
    have hfull := congrArg M.normalWord (last_snoc_init x)
    rw [M.normal_last_coord] at hfull
    exact hfull.symm
  rw [hword]
  simp [map_mul, map_zpow,
    (QuotientGroup.eq_one_iff (M.gen (Fin.last n))).mpr
      (Subgroup.mem_zpowers (M.gen (Fin.last n)))]

lemma delete_consistent_presentation {n : ℕ}
    {T : ParameterIndex (n + 1) → ℤ}
    (M : CPres (n + 1) T) (x : Fin (n + 1) → ℤ) :
    (M.deleteConsistentPresentation).coord
        (QuotientGroup.mk' (Subgroup.zpowers (M.gen (Fin.last n)))
          (M.normalWord x)) = Fin.init x := by
  rw [← M.consistent_presentation_init x]
  exact (M.deleteConsistentPresentation).coord_normalWord _

lemma consistent_multiplication_tuple {n : ℕ}
    {T : ParameterIndex (n + 1) → ℤ}
    (M : CPres (n + 1) T)
    (x y : Fin (n + 1) → ℤ) :
    (M.deleteConsistentPresentation).multiplicationTuple
        (Fin.init x) (Fin.init y) =
      Fin.init (M.multiplicationTuple x y) := by
  let MW := M.deleteConsistentPresentation
  apply MW.normalWord_injective
  rw [MW.normal_multiplication_tuple]
  rw [M.consistent_presentation_init x,
    M.consistent_presentation_init y,
    M.consistent_presentation_init
      (M.multiplicationTuple x y)]
  rw [M.normal_multiplication_tuple]
  exact (map_mul (QuotientGroup.mk' (Subgroup.zpowers (M.gen (Fin.last n)))
    ) (M.normalWord x) (M.normalWord y)).symm

lemma delete_consistent_tuple {n : ℕ}
    {T : ParameterIndex (n + 1) → ℤ}
    (M : CPres (n + 1) T)
    (x : Fin (n + 1) → ℤ) (z : ℤ) :
    (M.deleteConsistentPresentation).poweringTuple (Fin.init x) z =
      Fin.init (M.poweringTuple x z) := by
  let MW := M.deleteConsistentPresentation
  apply MW.normalWord_injective
  rw [MW.normal_powering_tuple]
  rw [M.consistent_presentation_init x]
  rw [M.consistent_presentation_init
    (M.poweringTuple x z)]
  rw [M.normal_powering_tuple x z]
  exact (map_zpow (QuotientGroup.mk' (Subgroup.zpowers (M.gen (Fin.last n)))
    ) (M.normalWord x) z).symm

lemma consistent_conjugation_tuple {n : ℕ}
    {T : ParameterIndex (n + 1) → ℤ}
    (M : CPres (n + 1) T)
    (i j : Fin n) (u v : ℤ) :
    (M.deleteConsistentPresentation).conjugationTuple i j u v =
      Fin.init (M.conjugationTuple (Fin.castSucc i) (Fin.castSucc j) u v) := by
  let MW := M.deleteConsistentPresentation
  apply MW.normalWord_injective
  rw [MW.word_conjugation_tuple]
  rw [M.consistent_presentation_init]
  rw [M.word_conjugation_tuple]
  change
    QuotientGroup.mk' (Subgroup.zpowers (M.gen (Fin.last n)))
          (M.gen (Fin.castSucc j)) ^ u *
        QuotientGroup.mk' (Subgroup.zpowers (M.gen (Fin.last n)))
          (M.gen (Fin.castSucc i)) ^ v =
      QuotientGroup.mk' (Subgroup.zpowers (M.gen (Fin.last n)))
        (M.gen (Fin.castSucc j) ^ u * M.gen (Fin.castSucc i) ^ v)
  rw [map_mul, map_zpow, map_zpow]

/--
Below the conjugation tail, the coordinates of `a_j^u a_i^v` are structural:
coordinate `i` is `v`, coordinate `j` is `u`, and the remaining coordinates
at or below `j` are zero.  Thus the only polynomial content of product
conjugation lies in the tail coordinates `k` with `j < k`.
-/
theorem conjugation_tuple_structural {n : ℕ}
    {T : ParameterIndex n → ℤ}
    (M : CPres n T)
    (i j k : Fin n) (hij : i < j) (hjk : ¬ j < k) (u v : ℤ) :
    M.conjugationTuple i j u v k =
      if k = i then v else if k = j then u else 0 := by
  induction n with
  | zero =>
      exact Fin.elim0 i
  | succ n ih =>
      by_cases hjlast : j = Fin.last n
      · subst j
        rw [conjugation_last M i k hij u v]
      · have hj_lt_last : j < Fin.last n := Fin.lt_last_iff_ne_last.mpr hjlast
        have hi_ne_last : i ≠ Fin.last n :=
          ne_of_lt (hij.trans hj_lt_last)
        have hk_ne_last : k ≠ Fin.last n := by
          have hkle : k ≤ j := not_lt.mp hjk
          exact ne_of_lt (lt_of_le_of_lt hkle hj_lt_last)
        rcases Fin.eq_castSucc_of_ne_last hi_ne_last with ⟨i', rfl⟩
        rcases Fin.eq_castSucc_of_ne_last hjlast with ⟨j', rfl⟩
        rcases Fin.eq_castSucc_of_ne_last hk_ne_last with ⟨k', rfl⟩
        have hij' : i' < j' := Fin.castSucc_lt_castSucc_iff.mp hij
        have hjk' : ¬ j' < k' := by
          intro h
          exact hjk (Fin.castSucc_lt_castSucc_iff.mpr h)
        have hquot :=
          congrFun
            (M.consistent_conjugation_tuple
              i' j' u v) k'
        change
          M.deleteConsistentPresentation.conjugationTuple i' j' u v k' =
            M.conjugationTuple (Fin.castSucc i') (Fin.castSucc j') u v
              (Fin.castSucc k') at hquot
        have hlower :=
          ih M.deleteConsistentPresentation
            i' j' k' hij' hjk'
        change
          M.conjugationTuple (Fin.castSucc i') (Fin.castSucc j') u v
            (Fin.castSucc k') =
            (if Fin.castSucc k' = Fin.castSucc i' then v
             else if Fin.castSucc k' = Fin.castSucc j' then u else 0)
        rw [← hquot]
        simpa using hlower

/--
Semantic Section 3.1 quotient step: if `T` is consistent, then deleting the
last generator gives a consistent tuple for `W(T) = G(T)/⟨aₙ⟩`.
-/
theorem consistent_last_tuple {n : ℕ}
    {T : ParameterIndex (n + 1) → ℤ}
    (M : CPres (n + 1) T) :
    IsConsistent (lastParameterTuple T) := by
  exact ⟨M.deleteConsistentPresentation⟩

/-- Section 3.1 set-level quotient step: `t ∈ Cₙ` implies `t_w ∈ Cₙ₋₁`. -/
theorem consistent_last_parameter {n : ℕ}
    {T : ParameterIndex (n + 1) → ℤ}
    (hT : IsConsistent T) :
    IsConsistent (lastParameterTuple T) := by
  rcases hT with ⟨M⟩
  exact consistent_last_tuple M

/-- Section 3.1 set-level quotient step in consistency-locus notation. -/
theorem last_consistency_locus {n : ℕ}
    {T : ParameterIndex (n + 1) → ℤ}
    (hT : T ∈ consistencyLocus (n + 1)) :
    lastParameterTuple T ∈ consistencyLocus n :=
  consistent_last_parameter hT

/--
The first normal coordinate is additive in every consistent triangular
presentation.  The proof descends through the central last-generator quotient
until the rank-one case, where normal forms are just powers of the first
generator.
-/
theorem firstCoordinateAdditive {n : ℕ}
    {T : ParameterIndex (n + 1) → ℤ}
    (M : CPres (n + 1) T) :
    CoordinateAdditive M 0 := by
  induction n with
  | zero =>
      rw [M.additive_multiplication_tuple 0]
      intro x y
      have hx : x = singleCoord (0 : Fin 1) (x 0) := by
        funext i
        fin_cases i
        simp [singleCoord]
      have hy : y = singleCoord (0 : Fin 1) (y 0) := by
        funext i
        fin_cases i
        simp [singleCoord]
      have htuple :
          M.multiplicationTuple x y =
            singleCoord (0 : Fin 1) (x 0 + y 0) := by
        apply M.normalWord_injective
        rw [M.normal_multiplication_tuple, hx, hy,
          M.normal_single_coord, M.normal_single_coord,
          M.normal_single_coord]
        rw [← zpow_add]
        simp [singleCoord]
      simpa [singleCoord] using congrFun htuple 0
  | succ n ih =>
      rw [M.additive_multiplication_tuple 0]
      intro x y
      let MW := M.deleteConsistentPresentation
      have hMW : CoordinateAdditive MW 0 := ih (T := lastParameterTuple T) MW
      have hmul :=
        congrFun
          (M.consistent_multiplication_tuple x y)
          (0 : Fin (n + 1))
      have hMWmul :=
        (MW.additive_multiplication_tuple 0).mp hMW
          (Fin.init x) (Fin.init y)
      rw [hMWmul] at hmul
      change
        (Fin.init x (0 : Fin (n + 1)) + Fin.init y (0 : Fin (n + 1))) =
          Fin.init (M.multiplicationTuple x y) (0 : Fin (n + 1)) at hmul
      simpa [Fin.init_def] using hmul.symm

theorem firstDisplayTail {n : ℕ}
    {T : ParameterIndex (n + 1) → ℤ}
    (M : CPres (n + 1) T) :
    FirstDisplayTail M :=
  (M.coordinate_additive_display).mp
    M.firstCoordinateAdditive

/--
Conjugating a non-leading generator by the leading generator stays in the
canonical `U(T)` subgroup: its first coordinate is zero.
-/
lemma conjugation_tuple_coordinate {n : ℕ}
    {T : ParameterIndex (n + 1) → ℤ}
    (M : CPres (n + 1) T)
    (j : Fin (n + 1)) (h0j : (0 : Fin (n + 1)) < j) (u v : ℤ) :
    M.leftConjugationTuple 0 j u v 0 = 0 := by
  change M.coord (M.gen 0 ^ (-v) * M.gen j ^ u * M.gen 0 ^ v) 0 = 0
  rw [M.firstCoordinateAdditive (M.gen 0 ^ (-v) * M.gen j ^ u) (M.gen 0 ^ v)]
  rw [M.firstCoordinateAdditive (M.gen 0 ^ (-v)) (M.gen j ^ u)]
  rw [M.coord_gen_zpow, M.coord_gen_zpow, M.coord_gen_zpow]
  simp [singleCoord, ne_of_lt h0j]

/--
The second normal coordinate is additive in every consistent triangular
presentation of rank at least two.  The proof descends through the central
last-generator quotient until the rank-two case, where the defining relation
has empty tail and the two generators commute.
-/
theorem secondCoordinateAdditive {n : ℕ}
    {T : ParameterIndex (n + 2) → ℤ}
    (M : CPres (n + 2) T) :
    CoordinateAdditive M 1 := by
  induction n with
  | zero =>
      rw [M.additive_multiplication_tuple 1]
      intro x y
      have hnorm :
          ∀ z : Fin 2 → ℤ,
            M.normalWord z = M.gen 0 ^ z 0 * M.gen 1 ^ z 1 := by
        intro z
        change orderedZPow M.gen z = M.gen 0 ^ z 0 * M.gen 1 ^ z 1
        unfold orderedZPow
        rw [List.finRange_succ]
        rw [List.finRange_succ]
        simp
      let z : Fin 2 → ℤ := fun i => if i = 0 then x 0 + y 0 else x 1 + y 1
      have htuple : M.multiplicationTuple x y = z := by
        apply M.normalWord_injective
        rw [M.normal_multiplication_tuple, hnorm x, hnorm y, hnorm z]
        have hcomm : Commute (M.gen 1 ^ x 1) (M.gen 0 ^ y 0) := by
          simpa using
            ((M.gen_commute (0 : Fin 2)).zpow_left (x 1)).zpow_right
              (y 0)
        rw [show
            (M.gen 0 ^ x 0 * M.gen 1 ^ x 1) *
                (M.gen 0 ^ y 0 * M.gen 1 ^ y 1) =
              M.gen 0 ^ x 0 * (M.gen 1 ^ x 1 * M.gen 0 ^ y 0) *
                M.gen 1 ^ y 1 by group]
        rw [hcomm.eq]
        rw [show
            M.gen 0 ^ x 0 * (M.gen 0 ^ y 0 * M.gen 1 ^ x 1) *
                M.gen 1 ^ y 1 =
              (M.gen 0 ^ x 0 * M.gen 0 ^ y 0) *
                (M.gen 1 ^ x 1 * M.gen 1 ^ y 1) by group]
        rw [← zpow_add, ← zpow_add]
        simp [z]
      simpa [z] using congrFun htuple 1
  | succ n ih =>
      rw [M.additive_multiplication_tuple 1]
      intro x y
      let MW := M.deleteConsistentPresentation
      have hMW : CoordinateAdditive MW 1 := ih (T := lastParameterTuple T) MW
      have hmul :=
        congrFun
          (M.consistent_multiplication_tuple x y)
          (1 : Fin (n + 2))
      have hMWmul :=
        (MW.additive_multiplication_tuple 1).mp hMW
          (Fin.init x) (Fin.init y)
      rw [hMWmul] at hmul
      change
        (Fin.init x (1 : Fin (n + 2)) + Fin.init y (1 : Fin (n + 2))) =
          Fin.init (M.multiplicationTuple x y) (1 : Fin (n + 2)) at hmul
      simpa [Fin.init_def] using hmul.symm

theorem secondDisplayAdditive {n : ℕ}
    {T : ParameterIndex (n + 2) → ℤ}
    (M : CPres (n + 2) T) :
    SecondDisplayAdditive M :=
  M.second_display_additive
    M.firstDisplayTail M.secondCoordinateAdditive

/-- The canonical concrete `U(T)` presentation obtained by deleting `a₀`. -/
noncomputable def deleteFirstConsistent {n : ℕ}
    {T : ParameterIndex (n + 1) → ℤ}
    (M : CPres (n + 1) T) :
    CPres n (firstParameterTuple T) :=
  M.firstConsistentAdditive
    M.firstCoordinateAdditive

theorem consistent_powering_tuple {n : ℕ}
    {T : ParameterIndex (n + 1) → ℤ}
    (M : CPres (n + 1) T)
    (hMul : ∀ a b : M.G,
      M.coord a 0 = 0 → M.coord b 0 = 0 → M.coord (a * b) 0 = 0)
    (hInv : ∀ a : M.G, M.coord a 0 = 0 → M.coord a⁻¹ 0 = 0)
    (x : Fin (n + 1) → ℤ) (hx0 : x 0 = 0) (z : ℤ) :
    (M.firstConsistentPresentation hMul hInv).poweringTuple
        (Fin.tail x) z =
      Fin.tail (M.poweringTuple x z) := by
  let MU := M.firstConsistentPresentation hMul hInv
  have hnorm :
      ((show M.firstCoordinateSubgroup hMul hInv from
          MU.normalWord (Fin.tail x)) : M.G) = M.normalWord x := by
    rw [show
        ((show M.firstCoordinateSubgroup hMul hInv from
            MU.normalWord (Fin.tail x)) : M.G) =
          M.tailNormalWord (Fin.tail x) by
        simpa [MU] using
          M.first_consistent_coe
            hMul hInv (Fin.tail x)]
    exact (M.normal_tail_first x hx0).symm
  ext i
  rw [CPres.poweringTuple]
  rw [M.first_consistent_coord hMul hInv]
  change
    M.coord
        ((show M.firstCoordinateSubgroup hMul hInv from
          MU.normalWord (Fin.tail x) ^ z) : M.G)
        (Fin.succ i) =
      M.poweringTuple x z (Fin.succ i)
  rw [show
      ((show M.firstCoordinateSubgroup hMul hInv from
          MU.normalWord (Fin.tail x) ^ z) : M.G) =
        M.normalWord x ^ z by
      rw [show
          ((show M.firstCoordinateSubgroup hMul hInv from
              MU.normalWord (Fin.tail x) ^ z) : M.G) =
            ((show M.firstCoordinateSubgroup hMul hInv from
              MU.normalWord (Fin.tail x)) : M.G) ^ z by
          exact
            (M.firstCoordinateSubgroup hMul hInv).subtype.map_zpow
              (MU.normalWord (Fin.tail x)) z]
      rw [hnorm]]
  rfl

theorem consistent_presentation_powering {n : ℕ}
    {T : ParameterIndex (n + 1) → ℤ}
    (M : CPres (n + 1) T)
    (x : Fin (n + 1) → ℤ) (hx0 : x 0 = 0) (z : ℤ) :
    M.deleteFirstConsistent.poweringTuple (Fin.tail x) z =
      Fin.tail (M.poweringTuple x z) := by
  let hClosed := coordinate_closed_additive M 0 M.firstCoordinateAdditive
  simpa [deleteFirstConsistent,
    firstConsistentAdditive, hClosed] using
    M.consistent_powering_tuple
      hClosed.1 hClosed.2 x hx0 z

theorem consistent_presentation_tuple {n : ℕ}
    {T : ParameterIndex (n + 1) → ℤ}
    (M : CPres (n + 1) T)
    (hMul : ∀ a b : M.G,
      M.coord a 0 = 0 → M.coord b 0 = 0 → M.coord (a * b) 0 = 0)
    (hInv : ∀ a : M.G, M.coord a 0 = 0 → M.coord a⁻¹ 0 = 0)
    (i j : Fin n) (u v : ℤ) :
    (M.firstConsistentPresentation hMul hInv).conjugationTuple i j u v =
      Fin.tail (M.conjugationTuple (Fin.succ i) (Fin.succ j) u v) := by
  let MU := M.firstConsistentPresentation hMul hInv
  ext k
  have hcoord := congrFun
    (M.first_consistent_coord hMul hInv
      ((show M.firstCoordinateSubgroup hMul hInv from
        MU.gen j ^ u * MU.gen i ^ v))) k
  change
    (MU.coord (MU.gen j ^ u * MU.gen i ^ v) k) =
      M.coord (M.gen (Fin.succ j) ^ u * M.gen (Fin.succ i) ^ v) (Fin.succ k)
  rw [hcoord]
  congr 1

theorem consistent_presentation_conjugation {n : ℕ}
    {T : ParameterIndex (n + 1) → ℤ}
    (M : CPres (n + 1) T)
    (i j : Fin n) (u v : ℤ) :
    M.deleteFirstConsistent.conjugationTuple i j u v =
      Fin.tail (M.conjugationTuple (Fin.succ i) (Fin.succ j) u v) := by
  let hClosed := coordinate_closed_additive M 0 M.firstCoordinateAdditive
  simpa [deleteFirstConsistent,
    firstConsistentAdditive, hClosed] using
    M.consistent_presentation_tuple
      hClosed.1 hClosed.2 i j u v

/-- The canonical concrete `V(T)` presentation obtained by deleting `a₁`. -/
noncomputable def deleteSecondConsistent {n : ℕ}
    {T : ParameterIndex (n + 2) → ℤ}
    (M : CPres (n + 2) T) :
    CPres (n + 1) (secondParameterTuple T) :=
  M.consistentPresentationAdditive
    M.secondCoordinateAdditive

theorem consistent_parameter_additive
    {n : ℕ} {T : ParameterIndex (n + 2) → ℤ}
    (M : CPres (n + 2) T)
    (hSecond : SecondDisplayAdditive M) :
    IsConsistent (secondParameterTuple T) :=
  consistent_display_additive M
    M.firstDisplayTail hSecond

theorem consistency_locus_display
    {n : ℕ} {T : ParameterIndex (n + 2) → ℤ}
    (M : CPres (n + 2) T)
    (hSecond : SecondDisplayAdditive M) :
    secondParameterTuple T ∈ consistencyLocus (n + 1) :=
  consistent_parameter_additive M hSecond

/-- Unconditional Section 3.1 `V(T)` consistency step. -/
theorem second_parameter_tuple {n : ℕ}
    {T : ParameterIndex (n + 2) → ℤ}
    (M : CPres (n + 2) T) :
    IsConsistent (secondParameterTuple T) :=
  ⟨M.deleteSecondConsistent⟩

/-- Section 3.1 set-level `V(T)` step from a consistent presentation. -/
theorem parameter_tuple_locus {n : ℕ}
    {T : ParameterIndex (n + 2) → ℤ}
    (M : CPres (n + 2) T) :
    secondParameterTuple T ∈ consistencyLocus (n + 1) :=
  second_parameter_tuple M

/-- Section 3.1 set-level `V(T)` step from semantic consistency. -/
theorem consistent_second_tuple {n : ℕ}
    {T : ParameterIndex (n + 2) → ℤ}
    (hT : IsConsistent T) :
    IsConsistent (secondParameterTuple T) := by
  rcases hT with ⟨M⟩
  exact second_parameter_tuple M

/-- Section 3.1 set-level `V(T)` step in consistency-locus notation. -/
theorem second_consistency_locus {n : ℕ}
    {T : ParameterIndex (n + 2) → ℤ}
    (hT : T ∈ consistencyLocus (n + 2)) :
    secondParameterTuple T ∈ consistencyLocus (n + 1) :=
  consistent_second_tuple hT

/-- Unconditional Section 3.1 `U(T)` consistency step. -/
theorem consistent_first_tuple {n : ℕ}
    {T : ParameterIndex (n + 1) → ℤ}
    (M : CPres (n + 1) T) :
    IsConsistent (firstParameterTuple T) :=
  ⟨M.deleteFirstConsistent⟩

/-- Section 3.1 set-level `U(T)` step from a consistent presentation. -/
theorem first_consistency_locus {n : ℕ}
    {T : ParameterIndex (n + 1) → ℤ}
    (M : CPres (n + 1) T) :
    firstParameterTuple T ∈ consistencyLocus n :=
  consistent_first_tuple M

/-- Section 3.1 set-level `U(T)` step from semantic consistency. -/
theorem consistent_delete_tuple {n : ℕ}
    {T : ParameterIndex (n + 1) → ℤ}
    (hT : IsConsistent T) :
    IsConsistent (firstParameterTuple T) := by
  rcases hT with ⟨M⟩
  exact consistent_first_tuple M

/-- Section 3.1 set-level `U(T)` step in consistency-locus notation. -/
theorem delete_parameter_locus {n : ℕ}
    {T : ParameterIndex (n + 1) → ℤ}
    (hT : T ∈ consistencyLocus (n + 1)) :
    firstParameterTuple T ∈ consistencyLocus n :=
  consistent_delete_tuple hT

/--
Section 3.1 induction package: for a consistent length-`n+2`
presentation, the parameter tuples for `U(T)`, `V(T)`, and `W(T)` lie in
the lower consistency locus, provided the two coordinate-zero carriers used
for `U(T)` and `V(T)` are closed under the group operations.
-/
theorem induction_subquotients_closed {n : ℕ}
    {T : ParameterIndex (n + 2) → ℤ}
    (M : CPres (n + 2) T)
    (hFirst : CoordinateZeroClosed M 0)
    (hSecond : CoordinateZeroClosed M 1) :
    firstParameterTuple T ∈ consistencyLocus (n + 1) ∧
      secondParameterTuple T ∈ consistencyLocus (n + 1) ∧
        lastParameterTuple T ∈ consistencyLocus (n + 1) := by
  refine ⟨?_, ?_, ?_⟩
  · exact parameter_consistency_closed M hFirst
  · exact delete_consistency_locus M hSecond
  · exact last_consistency_locus (mem_consistencyLocus M)

/--
Section 3.1 induction package with tuple-level closure hypotheses.  This
compatibility form states the `U(T)` and `V(T)` subgroup closures directly in
terms of the semantic multiplication and inverse coordinate functions.
-/
theorem induction_subquotients_consistency {n : ℕ}
    {T : ParameterIndex (n + 2) → ℤ}
    (M : CPres (n + 2) T)
    (hFirst : CoordinateTupleClosed M 0)
    (hSecond : CoordinateTupleClosed M 1) :
    firstParameterTuple T ∈ consistencyLocus (n + 1) ∧
      secondParameterTuple T ∈ consistencyLocus (n + 1) ∧
        lastParameterTuple T ∈ consistencyLocus (n + 1) := by
  refine ⟨?_, ?_, ?_⟩
  · exact parameter_locus_closed M hFirst
  · exact consistency_locus_closed M hSecond
  · exact last_consistency_locus (mem_consistencyLocus M)

/--
Section 3.1 induction package with additive-coordinate hypotheses replacing
the raw closure hypotheses.  The unconditional theorem below supplies both
additivity hypotheses for every consistent presentation.
-/
theorem subquotients_consistency_locus {n : ℕ}
    {T : ParameterIndex (n + 2) → ℤ}
    (M : CPres (n + 2) T)
    (hFirst : CoordinateAdditive M 0)
    (hSecond : CoordinateAdditive M 1) :
    firstParameterTuple T ∈ consistencyLocus (n + 1) ∧
      secondParameterTuple T ∈ consistencyLocus (n + 1) ∧
        lastParameterTuple T ∈ consistencyLocus (n + 1) := by
  refine ⟨?_, ?_, ?_⟩
  · exact tuple_consistency_locus M hFirst
  · exact parameter_locus_additive M hSecond
  · exact last_consistency_locus (mem_consistencyLocus M)

/--
Section 3.1 induction package with the `U(T)` obligation stated in the sharper
display-tail form and the `V(T)` obligation stated as second-coordinate
additivity.
-/
theorem induction_subquotients_locus
    {n : ℕ} {T : ParameterIndex (n + 2) → ℤ}
    (M : CPres (n + 2) T)
    (hFirst : FirstDisplayTail M)
    (hSecond : CoordinateAdditive M 1) :
    firstParameterTuple T ∈ consistencyLocus (n + 1) ∧
      secondParameterTuple T ∈ consistencyLocus (n + 1) ∧
        lastParameterTuple T ∈ consistencyLocus (n + 1) := by
  refine ⟨?_, ?_, ?_⟩
  · exact parameter_consistency_locus M hFirst
  · exact parameter_locus_additive M hSecond
  · exact last_consistency_locus (mem_consistencyLocus M)

/--
Section 3.1 induction package with the unconditional `U(T)` step and only the
`V(T)` coordinate-additivity hypothesis explicit.  The unconditional theorem
below supplies that hypothesis automa.
-/
theorem induction_subquotients_second
    {n : ℕ} {T : ParameterIndex (n + 2) → ℤ}
    (M : CPres (n + 2) T)
    (hSecond : CoordinateAdditive M 1) :
    firstParameterTuple T ∈ consistencyLocus (n + 1) ∧
      secondParameterTuple T ∈ consistencyLocus (n + 1) ∧
        lastParameterTuple T ∈ consistencyLocus (n + 1) := by
  refine ⟨?_, ?_, ?_⟩
  · exact first_consistency_locus M
  · exact parameter_locus_additive M hSecond
  · exact last_consistency_locus (mem_consistencyLocus M)

/--
Section 3.1 induction package with the subgroup obligations stated as
display-tail conditions from the Section 3.3 multiplication formula.  The
unconditional theorem below supplies both display-tail facts.
-/
theorem induction_subquotients_conditions
    {n : ℕ} {T : ParameterIndex (n + 2) → ℤ}
    (M : CPres (n + 2) T)
    (hFirst : FirstDisplayTail M)
    (hSecond : SecondDisplayAdditive M) :
    firstParameterTuple T ∈ consistencyLocus (n + 1) ∧
      secondParameterTuple T ∈ consistencyLocus (n + 1) ∧
        lastParameterTuple T ∈ consistencyLocus (n + 1) := by
  refine ⟨?_, ?_, ?_⟩
  · exact parameter_consistency_locus M
      hFirst
  · exact consistency_locus_additive M hFirst
      hSecond
  · exact last_consistency_locus (mem_consistencyLocus M)

/--
Section 3.1 induction package with the unconditional `U(T)` step and the
`V(T)` obligation stated as the second-coordinate display-tail condition from
the Section 3.3 multiplication formula.  The unconditional theorem below
supplies this display-tail fact automa.
-/
theorem induction_subquotients_additive
    {n : ℕ} {T : ParameterIndex (n + 2) → ℤ}
    (M : CPres (n + 2) T)
    (hSecond : SecondDisplayAdditive M) :
    firstParameterTuple T ∈ consistencyLocus (n + 1) ∧
      secondParameterTuple T ∈ consistencyLocus (n + 1) ∧
        lastParameterTuple T ∈ consistencyLocus (n + 1) := by
  refine ⟨?_, ?_, ?_⟩
  · exact first_consistency_locus M
  · exact consistency_locus_display M
      hSecond
  · exact last_consistency_locus (mem_consistencyLocus M)

/--
Unconditional Section 3.1 induction package: for a consistent length-`n+2`
presentation, the parameter tuples for `U(T)`, `V(T)`, and `W(T)` all lie in
the lower consistency locus.
-/
theorem induction_subquotients
    {n : ℕ} {T : ParameterIndex (n + 2) → ℤ}
    (M : CPres (n + 2) T) :
    firstParameterTuple T ∈ consistencyLocus (n + 1) ∧
      secondParameterTuple T ∈ consistencyLocus (n + 1) ∧
        lastParameterTuple T ∈ consistencyLocus (n + 1) := by
  refine ⟨?_, ?_, ?_⟩
  · exact first_consistency_locus M
  · exact parameter_tuple_locus M
  · exact last_consistency_locus (mem_consistencyLocus M)

/-- Set-level form of the unconditional Section 3.1 induction package. -/
theorem induction_consistency_locus
    {n : ℕ} {T : ParameterIndex (n + 2) → ℤ}
    (hT : T ∈ consistencyLocus (n + 2)) :
    firstParameterTuple T ∈ consistencyLocus (n + 1) ∧
      secondParameterTuple T ∈ consistencyLocus (n + 1) ∧
        lastParameterTuple T ∈ consistencyLocus (n + 1) := by
  rcases hT with ⟨M⟩
  exact induction_subquotients M

/--
The last multiplication coordinate splits into the contribution from the
coordinates below the last generator plus the two last exponents.  This is the
semantic core of Cant--Eick Remark `formF`.
-/
theorem multiplication_tuple_last {n : ℕ}
    {T : ParameterIndex (n + 1) → ℤ}
    (M : CPres (n + 1) T)
    (x y : Fin (n + 1) → ℤ) :
    M.multiplicationTuple x y (Fin.last n) =
      M.multiplicationTuple (withoutLastCoord x) (withoutLastCoord y) (Fin.last n) +
        x (Fin.last n) + y (Fin.last n) := by
  let last := Fin.last n
  let x0 := withoutLastCoord x
  let y0 := withoutLastCoord y
  let z0 := M.multiplicationTuple x0 y0
  have hx : M.normalWord x = M.normalWord x0 * M.gen last ^ x last := by
    simpa [x0, last] using M.without_last_coord x
  have hy : M.normalWord y = M.normalWord y0 * M.gen last ^ y last := by
    simpa [y0, last] using M.without_last_coord y
  have hcomm : Commute (M.gen last ^ x last) (M.normalWord y0) :=
    (M.gen_commute_normal y0).zpow_left (x last)
  have hprod :
      M.normalWord x * M.normalWord y =
        M.normalWord z0 * M.gen last ^ (x last + y last) := by
    rw [hx, hy]
    rw [show (M.normalWord x0 * M.gen last ^ x last) *
          (M.normalWord y0 * M.gen last ^ y last) =
        (M.normalWord x0 * M.normalWord y0) *
          (M.gen last ^ x last * M.gen last ^ y last) by
        calc
          (M.normalWord x0 * M.gen last ^ x last) *
              (M.normalWord y0 * M.gen last ^ y last)
              = M.normalWord x0 * (M.gen last ^ x last * M.normalWord y0) *
                  M.gen last ^ y last := by group
          _ = M.normalWord x0 * (M.normalWord y0 * M.gen last ^ x last) *
                  M.gen last ^ y last := by rw [hcomm.eq]
          _ = (M.normalWord x0 * M.normalWord y0) *
                  (M.gen last ^ x last * M.gen last ^ y last) := by group]
    rw [← zpow_add]
    rw [← M.normal_multiplication_tuple x0 y0]
  have htarget :
      M.normalWord (addLastCoord z0 (x last + y last)) =
        M.normalWord x * M.normalWord y := by
    rw [normal_last_coord, hprod]
  have htuple : M.multiplicationTuple x y = addLastCoord z0 (x last + y last) := by
    change M.coord (M.normalWord x * M.normalWord y) =
      addLastCoord z0 (x last + y last)
    rw [← htarget]
    exact M.coord_normalWord _
  have hlast := congrFun htuple last
  simpa [addLastCoord, z0, last, add_assoc] using hlast

@[simp]
lemma multiplication_tuple_left (x : Fin n → ℤ) :
    M.multiplicationTuple (fun _ => 0) x = x := by
  rw [multiplicationTuple]
  simpa using M.coord_normalWord x

@[simp]
lemma multiplication_tuple_right (x : Fin n → ℤ) :
    M.multiplicationTuple x (fun _ => 0) = x := by
  rw [multiplicationTuple]
  simpa using M.coord_normalWord x

@[simp]
lemma poweringTuple_zero (x : Fin n → ℤ) :
    M.poweringTuple x 0 = fun _ => 0 := by
  rw [poweringTuple]
  simpa using M.coord_normalWord (fun _ : Fin n => 0)

@[simp]
lemma poweringTuple_one (x : Fin n → ℤ) :
    M.poweringTuple x 1 = x := by
  rw [poweringTuple]
  simpa using M.coord_normalWord x

/-- Coordinate multiplication is associative because group multiplication is. -/
theorem multiplicationTuple_assoc (x y z : Fin n → ℤ) :
    M.multiplicationTuple (M.multiplicationTuple x y) z =
      M.multiplicationTuple x (M.multiplicationTuple y z) := by
  change
    M.coord (M.normalWord (M.multiplicationTuple x y) * M.normalWord z) =
      M.coord (M.normalWord x * M.normalWord (M.multiplicationTuple y z))
  congr 1
  rw [normal_multiplication_tuple, normal_multiplication_tuple, mul_assoc]

/-- The semantic powering recursion from Section 3.4. -/
theorem poweringTuple_succ (x : Fin n → ℤ) (z : ℤ) :
    M.poweringTuple x (z + 1) =
      M.multiplicationTuple (M.poweringTuple x z) x := by
  change
    M.coord (M.normalWord x ^ (z + 1)) =
      M.coord (M.normalWord (M.poweringTuple x z) * M.normalWord x)
  congr 1
  rw [normal_powering_tuple, zpow_add, zpow_one]

/--
Semantic last-coordinate form of Cant--Eick Section 3.4 Lemma `step3`.
The final powering coordinate advances by the old final coordinate, the
incoming last exponent, and the truncated-last multiplication contribution.
-/
theorem powering_tuple_truncated {n : ℕ}
    {T : ParameterIndex (n + 1) → ℤ}
    (M : CPres (n + 1) T)
    (x : Fin (n + 1) → ℤ) (z : ℤ) :
    M.poweringTuple x (z + 1) (Fin.last n) =
      M.poweringTuple x z (Fin.last n) +
        x (Fin.last n) +
          M.multiplicationTuple
            (withoutLastCoord (M.poweringTuple x z))
            (withoutLastCoord x) (Fin.last n) := by
  rw [M.poweringTuple_succ x z]
  rw [M.multiplication_tuple_last (M.poweringTuple x z) x]
  ring

/--
Forward-difference version of the semantic last-coordinate powering recursion:
the increment is the last exponent plus the truncated multiplication term.
-/
theorem powering_forward_difference {n : ℕ}
    {T : ParameterIndex (n + 1) → ℤ}
    (M : CPres (n + 1) T)
    (x : Fin (n + 1) → ℤ) (z : ℤ) :
    M.poweringTuple x (z + 1) (Fin.last n) -
        M.poweringTuple x z (Fin.last n) =
      x (Fin.last n) +
        M.multiplicationTuple
          (withoutLastCoord (M.poweringTuple x z))
          (withoutLastCoord x) (Fin.last n) := by
  rw [M.powering_tuple_truncated x z]
  ring

/-- Powering by a sum is coordinate multiplication of powers. -/
theorem poweringTuple_add (x : Fin n → ℤ) (z w : ℤ) :
    M.poweringTuple x (z + w) =
      M.multiplicationTuple (M.poweringTuple x z) (M.poweringTuple x w) := by
  change
    M.coord (M.normalWord x ^ (z + w)) =
      M.coord
        (M.normalWord (M.poweringTuple x z) *
          M.normalWord (M.poweringTuple x w))
  congr 1
  rw [normal_powering_tuple, normal_powering_tuple, zpow_add]

/--
Semantic form of Cant--Eick Lemma `step1`: the coordinates of
`a_i^{-v} a_j^u a_i^v` are obtained by powering the coordinates of
`a_i^{-v} a_j a_i^v`.
-/
theorem left_conjugation_powering
    (i j : Fin n) (u v : ℤ) :
    M.leftConjugationTuple i j u v =
      M.poweringTuple (M.leftConjugationTuple i j 1 v) u := by
  change
    M.coord (M.gen i ^ (-v) * M.gen j ^ u * M.gen i ^ v) =
      M.coord (M.normalWord (M.leftConjugationTuple i j 1 v) ^ u)
  congr 1
  rw [normal_conjugation_tuple]
  have hginv : M.gen i ^ v = (M.gen i ^ (-v))⁻¹ := by
    rw [zpow_neg, inv_inv]
  rw [hginv, zpow_one]
  change
    (MulAut.conj (M.gen i ^ (-v))) (M.gen j ^ u) =
      ((MulAut.conj (M.gen i ^ (-v))) (M.gen j)) ^ u
  exact map_zpow (MulAut.conj (M.gen i ^ (-v))) (M.gen j) u

/--
Semantic `step1` at conjugating exponent `1`: conjugating a power of `a_j`
once by `a_i` is the powering tuple of the explicit relation-product tuple.
-/
theorem left_conjugation_tuple
    (i j : Fin n) (hij : i < j) (u : ℤ) :
    M.leftConjugationTuple i j u 1 =
      M.poweringTuple (relationProductTuple T i j hij) u := by
  rw [M.left_conjugation_powering i j u 1]
  rw [M.conjugation_tuple_relation i j hij]

theorem conjugation_powering_relation {n : ℕ}
    {T : ParameterIndex (n + 1) → ℤ}
    (M : CPres (n + 1) T)
    (j : Fin (n + 1)) (h0j : (0 : Fin (n + 1)) < j) (u : ℤ) :
    M.leftConjugationTuple 0 j u 1 =
      M.poweringTuple (relationProductTuple T 0 j h0j) u :=
  M.left_conjugation_tuple 0 j h0j u

theorem conjugation_tuple_powering {n : ℕ}
    {T : ParameterIndex (n + 2) → ℤ}
    (M : CPres (n + 2) T) (u : ℤ) :
    M.leftConjugationTuple 0 1 u 1 =
      M.poweringTuple (zeroRelationTuple T) u := by
  rw [M.left_conjugation_powering 0 1 u 1]
  rw [M.left_conjugation_one]

/--
Semantic form of Cant--Eick Lemma `step2`: increasing the conjugating
exponent by one is obtained by conjugating the previous conjugated word by
`a_i`.
-/
theorem conjugation_tuple_v
    (i j : Fin n) (v : ℤ) :
    M.leftConjugationTuple i j 1 (v + 1) =
      M.coord (M.gen i ^ (-1 : ℤ) *
        M.normalWord (M.leftConjugationTuple i j 1 v) * M.gen i) := by
  change
    M.coord (M.gen i ^ (-(v + 1)) * M.gen j ^ (1 : ℤ) * M.gen i ^ (v + 1)) =
      M.coord (M.gen i ^ (-1 : ℤ) *
        M.normalWord (M.leftConjugationTuple i j 1 v) * M.gen i)
  congr 1
  rw [normal_conjugation_tuple, zpow_one]
  have hneg : (-(v + 1) : ℤ) = (-1 : ℤ) + -v := by ring
  rw [hneg, zpow_add, zpow_add, zpow_one]
  group

/--
Sharper semantic form of Cant--Eick Lemma `step2`: if the current conjugated
word has zero first coordinate, then increasing the conjugating exponent by
one is the coordinate tuple of the displayed product of the first-conjugated
tail factors.
-/
theorem conjugation_v_conjugated
    {n : ℕ} {T : ParameterIndex (n + 1) → ℤ}
    (M : CPres (n + 1) T)
    (j : Fin (n + 1)) (v : ℤ)
    (hc0 : M.leftConjugationTuple 0 j 1 v 0 = 0) :
    M.leftConjugationTuple 0 j 1 (v + 1) =
      M.coord (M.firstConjugatedProduct (M.leftConjugationTuple 0 j 1 v) 1) := by
  rw [M.conjugation_tuple_v 0 j v]
  congr 1
  let c := M.leftConjugationTuple 0 j 1 v
  have hc0c : c 0 = 0 := by
    simpa [c] using hc0
  calc
    M.gen 0 ^ (-1 : ℤ) * M.normalWord c * M.gen 0 =
        M.gen 0 ^ (-1 : ℤ) * M.normalWord (withoutFirstCoord c) *
          M.gen 0 ^ (1 : ℤ) := by
      rw [M.normal_without_coord c, hc0c, zpow_zero, one_mul, zpow_one]
    _ = M.firstConjugatedProduct c 1 := by
      exact M.first_conjugated_product c 1

end CPres

end CantEick
end Submission
