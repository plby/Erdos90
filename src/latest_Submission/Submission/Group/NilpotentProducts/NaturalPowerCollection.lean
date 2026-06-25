import Submission.Group.NilpotentProducts.CommutatorIdentities


/-!
# Elementary natural-power collection in class-three groups

These are the small class-three identities needed for Struik's
Theorem 4.  They are proved directly from equation (1), independently of
the general signed Hall-Petresco collector.
-/

namespace Struik
namespace P1960

open Submission
open Submission.Edmonton
open scoped commutatorElement

variable {G : Type*} [Group G]

lemma commutator_commute_elementary (x y : G) :
    hallCommutator x y = 1 ↔ Commute x y := by
  rw [hall_element_inv,
    commutatorElement_eq_one_iff_commute, Commute.inv_inv_iff]

lemma lower_series_elementary
    {i j : ℕ} {x y : G}
    (hx : x ∈ Subgroup.lowerCentralSeries G i)
    (hy : y ∈ Subgroup.lowerCentralSeries G j) :
    hallCommutator x y ∈ Subgroup.lowerCentralSeries G (i + j + 1) := by
  rw [hall_element_inv]
  exact lower_commutator_succ i j
    (Subgroup.commutator_mem_commutator
      ((Subgroup.lowerCentralSeries G i).inv_mem hx)
      ((Subgroup.lowerCentralSeries G j).inv_mem hy))

lemma triple_series_elementary
    (x y z : G) :
    hallTripleCommutator x y z ∈ Subgroup.lowerCentralSeries G 2 := by
  rw [hallTripleCommutator]
  have hxy :=
    lower_series_elementary
      (i := 0) (j := 0) (x := x) (y := y) (by simp) (by simp)
  simpa using lower_series_elementary
    (i := 1) (j := 0) (x := hallCommutator x y) (y := z)
    hxy (by simp)

lemma commute_series_elementary
    (hG4 : Subgroup.lowerCentralSeries G 3 = ⊥)
    (x : G) {z : G} (hz : z ∈ Subgroup.lowerCentralSeries G 2) :
    Commute x z := by
  have hx : x ∈ Subgroup.lowerCentralSeries G 0 := by simp
  have hxz : ⁅x, z⁆ ∈ Subgroup.lowerCentralSeries G 3 := by
    simpa using lower_commutator_succ 0 2
      (Subgroup.commutator_mem_commutator hx hz)
  rw [hG4] at hxz
  rw [← commutatorElement_eq_one_iff_commute]
  exact Subgroup.mem_bot.mp hxz

lemma commute_triple_elementary
    (hG4 : Subgroup.lowerCentralSeries G 3 = ⊥)
    (g x y z : G) :
    Commute g (hallTripleCommutator x y z) :=
  commute_series_elementary hG4 g
    (triple_series_elementary x y z)

lemma left_central_elementary
    {x y z : G} (hz : ∀ g : G, Commute g z) :
    hallCommutator (x * z) y = hallCommutator x y := by
  rw [commutatorIdentitiesFirst]
  have hmid :
      hallCommutator (hallCommutator x y) z = 1 :=
    (commutator_commute_elementary _ _).2
      (hz (hallCommutator x y))
  have hlast :
      hallCommutator z y = 1 :=
    (commutator_commute_elementary _ _).2
      (hz y).symm
  rw [hmid, hlast]
  simp

lemma commutator_left_elementary
    {x y : G}
    (hcentral : ∀ g : G, Commute g (hallCommutator x y))
    (n : ℕ) :
    hallCommutator (x ^ n) y = hallCommutator x y ^ n := by
  induction n with
  | zero => simp [hallCommutator]
  | succ n ih =>
      rw [pow_succ, commutatorIdentitiesFirst, ih]
      have hmid :
          hallCommutator (hallCommutator x y ^ n) x = 1 :=
        (commutator_commute_elementary _ _).2
          ((hcentral x).pow_right n).symm
      rw [hmid]
      simp [pow_succ]

lemma commutator_central_elementary
    {x y : G}
    (hcentral : ∀ g : G, Commute g (hallCommutator x y))
    (n : ℕ) :
    hallCommutator x (y ^ n) = hallCommutator x y ^ n := by
  induction n with
  | zero => simp [hallCommutator]
  | succ n ih =>
      rw [pow_succ, commutatorIdentitiesSecond, ih]
      have hswap :
          hallCommutator (y ^ n) x =
            (hallCommutator x y ^ n)⁻¹ := by
        rw [commutator_swap_inv, ih]
      have hmid :
          hallCommutator y (hallCommutator (y ^ n) x) = 1 := by
        rw [hswap]
        exact (commutator_commute_elementary _ _).2
          ((hcentral y).pow_right n).inv_right
      rw [hmid]
      simp [pow_succ']

lemma commutator_inv_elementary
    {x y : G}
    (hcentral : ∀ g : G, Commute g (hallCommutator x y)) :
    hallCommutator x⁻¹ y = (hallCommutator x y)⁻¹ := by
  let C := hallCommutator x y
  have hmid : hallCommutator C x⁻¹ = 1 :=
    (commutator_commute_elementary _ _).2
      (hcentral x⁻¹).symm
  have hproduct : C * hallCommutator x⁻¹ y = 1 := by
    have h := commutatorIdentitiesFirst x x⁻¹ y
    rw [hmid] at h
    simpa [C, hallCommutator] using h.symm
  calc
    hallCommutator x⁻¹ y =
        C⁻¹ * (C * hallCommutator x⁻¹ y) := by simp
    _ = C⁻¹ := by rw [hproduct, mul_one]
    _ = (hallCommutator x y)⁻¹ := rfl

/-- Natural-power form of the left half of Struik's Lemma 2. -/
theorem commutator_pow_elementary
    (hG4 : Subgroup.lowerCentralSeries G 3 = ⊥)
    (a b : G) (n : ℕ) :
    hallCommutator (a ^ n) b =
      hallCommutator a b ^ n *
        hallTripleCommutator a b a ^ n.choose 2 := by
  let C := hallCommutator a b
  let D := hallTripleCommutator a b a
  have hcentralD : ∀ g : G, Commute g D :=
    fun g => commute_triple_elementary hG4 g a b a
  have hCD : Commute C D := hcentralD C
  induction n with
  | zero => simp [hallCommutator]
  | succ n ih =>
      rw [pow_succ, commutatorIdentitiesFirst, ih]
      have hmiddle :
          hallCommutator (C ^ n * D ^ n.choose 2) a = D ^ n := by
        rw [left_central_elementary
          (fun g => (hcentralD g).pow_right (n.choose 2))]
        exact commutator_left_elementary
          hcentralD n
      rw [hmiddle]
      have hcomm :
          Commute C (D ^ n.choose 2 * D ^ n) :=
        (hCD.pow_right (n.choose 2)).mul_right (hCD.pow_right n)
      calc
        C ^ n * D ^ n.choose 2 * D ^ n * C =
            C ^ n * (D ^ n.choose 2 * D ^ n) * C := by group
        _ = C ^ n * C * (D ^ n.choose 2 * D ^ n) := by
          calc
            C ^ n * (D ^ n.choose 2 * D ^ n) * C =
                C ^ n * ((D ^ n.choose 2 * D ^ n) * C) := by group
            _ = C ^ n * (C * (D ^ n.choose 2 * D ^ n)) := by
              rw [← hcomm.eq]
            _ = C ^ n * C * (D ^ n.choose 2 * D ^ n) := by group
        _ = C ^ (n + 1) * D ^ (n.choose 2 + n) := by
          rw [pow_succ, pow_add]
        _ = hallCommutator a b ^ (n + 1) *
              hallTripleCommutator a b a ^ (Nat.succ n).choose 2 := by
          have hchoose :
              (Nat.succ n).choose 2 = n.choose 2 + n := by
            rw [show 2 = Nat.succ 1 by omega, Nat.choose_succ_succ,
              Nat.choose_one_right, Nat.add_comm]
          simp only [C, D, hchoose]

/-- Natural-power form of the right half of Struik's Lemma 2. -/
theorem hall_commutator_elementary
    (hG4 : Subgroup.lowerCentralSeries G 3 = ⊥)
    (a b : G) (n : ℕ) :
    hallCommutator a (b ^ n) =
      hallCommutator a b ^ n *
        hallTripleCommutator a b b ^ n.choose 2 := by
  let C := hallCommutator a b
  let E := hallTripleCommutator a b b
  have hcentralE : ∀ g : G, Commute g E :=
    fun g => commute_triple_elementary hG4 g a b b
  have hswap : hallCommutator b a = C⁻¹ := by
    rw [commutator_swap_inv]
  have hinv :
      hallCommutator C⁻¹ b = E⁻¹ := by
    exact commutator_inv_elementary hcentralE
  have htriple :
      hallTripleCommutator b a b = E⁻¹ := by
    rw [hallTripleCommutator, hswap]
    exact hinv
  have hleft :=
    commutator_pow_elementary hG4 b a n
  have hcomm :
      Commute (C ^ n) (E ^ n.choose 2) :=
    (hcentralE (C ^ n)).pow_right (n.choose 2)
  calc
    hallCommutator a (b ^ n) =
        (hallCommutator (b ^ n) a)⁻¹ := by
      rw [commutator_swap_inv]
    _ = ((C⁻¹) ^ n * (E⁻¹) ^ n.choose 2)⁻¹ := by
      rw [hleft, hswap, htriple]
    _ = E ^ n.choose 2 * C ^ n := by
      simp only [mul_inv_rev, inv_pow, inv_inv]
    _ = C ^ n * E ^ n.choose 2 := hcomm.eq.symm
    _ = hallCommutator a b ^ n *
          hallTripleCommutator a b b ^ n.choose 2 := rfl

/-- A relation on the third input kills the same power of a Hall triple
commutator in a class-three group. -/
lemma triple_order_elementary
    (hG4 : Subgroup.lowerCentralSeries G 3 = ⊥)
    {a b c : G} {n : ℕ} (hc : c ^ n = 1) :
    hallTripleCommutator a b c ^ n = 1 := by
  let C := hallCommutator a b
  let T := hallTripleCommutator a b c
  have hcentralT : ∀ g : G, Commute g T :=
    fun g => commute_triple_elementary hG4 g a b c
  have hpower :=
    commutator_central_elementary
      (x := C) (y := c) hcentralT n
  change hallCommutator C (c ^ n) = T ^ n at hpower
  rw [hc] at hpower
  simpa [hallCommutator] using hpower.symm

/-- A relation on the first input kills the same power of a Hall triple
commutator in a class-three group. -/
lemma triple_commutator_elementary
    (hG4 : Subgroup.lowerCentralSeries G 3 = ⊥)
    {a b c : G} {n : ℕ} (ha : a ^ n = 1) :
    hallTripleCommutator a b c ^ n = 1 := by
  let C := hallCommutator a b
  let D := hallTripleCommutator a b a
  let T := hallTripleCommutator a b c
  have hcentralD : ∀ g : G, Commute g D :=
    fun g => commute_triple_elementary hG4 g a b a
  have hcentralT : ∀ g : G, Commute g T :=
    fun g => commute_triple_elementary hG4 g a b c
  have hcol :=
    commutator_pow_elementary hG4 a b n
  have hproduct : C ^ n * D ^ n.choose 2 = 1 := by
    simpa [C, D, ha, hallCommutator] using hcol.symm
  have hCn : C ^ n = (D ^ n.choose 2)⁻¹ :=
    eq_inv_of_mul_eq_one_left hproduct
  have hleftOne : hallCommutator (C ^ n) c = 1 := by
    rw [hCn]
    exact (commutator_commute_elementary _ _).2
      ((hcentralD c).pow_right (n.choose 2)).inv_right.symm
  have hpower :=
    commutator_left_elementary
      (x := C) (y := c) hcentralT n
  rw [hleftOne] at hpower
  exact hpower.symm

/-- A relation on the second input kills the same power of a Hall triple
commutator in a class-three group. -/
lemma triple_middle_elementary
    (hG4 : Subgroup.lowerCentralSeries G 3 = ⊥)
    {a b c : G} {n : ℕ} (hb : b ^ n = 1) :
    hallTripleCommutator a b c ^ n = 1 := by
  let C := hallCommutator a b
  let E := hallTripleCommutator a b b
  let T := hallTripleCommutator a b c
  have hcentralE : ∀ g : G, Commute g E :=
    fun g => commute_triple_elementary hG4 g a b b
  have hcentralT : ∀ g : G, Commute g T :=
    fun g => commute_triple_elementary hG4 g a b c
  have hcol :=
    hall_commutator_elementary hG4 a b n
  have hproduct : C ^ n * E ^ n.choose 2 = 1 := by
    simpa [C, E, hb, hallCommutator] using hcol.symm
  have hCn : C ^ n = (E ^ n.choose 2)⁻¹ :=
    eq_inv_of_mul_eq_one_left hproduct
  have hleftOne : hallCommutator (C ^ n) c = 1 := by
    rw [hCn]
    exact (commutator_commute_elementary _ _).2
      ((hcentralE c).pow_right (n.choose 2)).inv_right.symm
  have hpower :=
    commutator_left_elementary
      (x := C) (y := c) hcentralT n
  rw [hleftOne] at hpower
  exact hpower.symm

/-- Struik's first formula (28), proved without the signed collector. -/
theorem first_elementary
    (hG4 : Subgroup.lowerCentralSeries G 3 = ⊥)
    (a b : G) :
    hallCommutator (a ^ (2 : ℤ)) b =
      hallCommutator a b ^ (2 : ℤ) *
        hallTripleCommutator a b a := by
  simpa only [zpow_ofNat, Nat.choose_self, pow_one] using
    (commutator_pow_elementary hG4 a b 2)

/-- Struik's second formula (28), proved without the signed collector. -/
theorem second_elementary
    (hG4 : Subgroup.lowerCentralSeries G 3 = ⊥)
    (a b : G) :
    hallCommutator a (b ^ (2 : ℤ)) =
      hallCommutator a b ^ (2 : ℤ) *
        hallTripleCommutator a b b := by
  simpa only [zpow_ofNat, Nat.choose_self, pow_one] using
    (hall_commutator_elementary hG4 a b 2)

end P1960
end Struik
