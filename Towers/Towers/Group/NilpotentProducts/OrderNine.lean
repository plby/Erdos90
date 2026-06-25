import Towers.Group.NilpotentProducts.OddSpecializations
import Towers.Group.NilpotentProducts.GeneralCollection
import Towers.Group.NilpotentProducts.GeneralPowers
import Mathlib.Algebra.GCDMonoid.FinsetLemmas
import Mathlib.Tactic.FinCases


/-!
# The sharp order-nine example in Struik's Corollary 1

For the third nilpotent product of two cyclic groups of order three,
Struik notes that `ab`, `ab²`, `a²b`, and `a²b²` all have order nine,
and that their cubes lie in the third lower-central term.  The
equation-(18) coordinate model makes these finite calculations.
-/

namespace Struik
namespace P1960

open Towers
open Towers.Edmonton

/-- The modulus attached to one of the six families of equation-(18)
coordinates. -/
def generalCoordinateModulus
    {t : ℕ} (order : Fin t → ℕ) :
    GeneralBasisIndex t → ℕ
  | .single i => order i
  | .pair q => generalPairModulus order q
  | .pairLeft q => generalPairModulus order q
  | .pairRight q => generalPairModulus order q
  | .tripleFirst q => generalResiduesModulus order q
  | .tripleSecond q => generalResiduesModulus order q

/-- The integral exponent at one of the six families of equation-(18)
coordinates. -/
def generalCoordinateExponent
    {t : ℕ} (c : GCoordi t) :
    GeneralBasisIndex t → ℤ
  | .single i => c.single i
  | .pair q => c.pair q
  | .pairLeft q => c.pairLeft q
  | .pairRight q => c.pairRight q
  | .tripleFirst q => c.tripleFirst q
  | .tripleSecond q => c.tripleSecond q

/-- The order of the factor represented by exponent `a` in a cyclic
coordinate of finite order `m`.  A zero exponent contributes order one. -/
def cyclicCoordinateOrder (m : ℕ) (a : ℤ) : ℕ :=
  if a = 0 then 1 else m / Nat.gcd m a.natAbs

/-- The order of one displayed Hall factor in an equation-(18) normal
form. -/
def generalCoordinateOrder
    {t : ℕ} (order : Fin t → ℕ)
    (c : GCoordi t)
    (i : GeneralBasisIndex t) : ℕ :=
  cyclicCoordinateOrder
    (generalCoordinateModulus order i)
    (generalCoordinateExponent c i)

/-- The least common multiple of the orders of all displayed Hall factors
in an equation-(18) normal form.  Coordinates with exponent zero contribute
one and therefore do not affect the lcm. -/
def generalOrderLCM
    {t : ℕ} (order : Fin t → ℕ)
    (c : GCoordi t) : ℕ :=
  Finset.univ.lcm
    (generalCoordinateOrder order c)

/-- Every Hall factor that actually occurs in the normal form has finite
order.  Coordinates of modulus zero are permitted, but their exponents must
vanish. -/
def GeneralDisplayedFactors
    {t : ℕ} (order : Fin t → ℕ)
    (c : GCoordi t) : Prop :=
  ∀ i : GeneralBasisIndex t,
    generalCoordinateExponent c i ≠ 0 →
      generalCoordinateModulus order i ≠ 0

/-- A coordinate axis is congruent to zero exactly when its exponent is
divisible by that coordinate's modulus. -/
theorem general_axis_mod
    {t : ℕ} (order : Fin t → ℕ)
    (i : GeneralBasisIndex t) (n : ℤ) :
    GMEq order
      (generalAxis i n)
      (GCoordi.zero t) ↔
      (generalCoordinateModulus order i : ℤ) ∣ n := by
  rw [general_residue_cast]
  cases i with
  | single i =>
      simp [generalResidueCast, generalAxis,
        GCoordi.zero,
        generalCoordinateModulus, funext_iff,
        ZMod.intCast_zmod_eq_zero_iff_dvd]
  | pair q | pairLeft q | pairRight q =>
      simp only [generalResidueCast, generalAxis,
        GCoordi.zero,
        generalCoordinateModulus,
        GeneralResidues.mk.injEq, true_and, and_true,
        funext_iff]
      constructor
      · intro h
        have hq := h q
        simpa [ZMod.intCast_zmod_eq_zero_iff_dvd] using hq
      · intro h x
        by_cases hx : x = q
        · subst x
          simpa [ZMod.intCast_zmod_eq_zero_iff_dvd] using h
        · simp [hx]
  | tripleFirst q | tripleSecond q =>
      simp only [generalResidueCast, generalAxis,
        GCoordi.zero,
        generalCoordinateModulus,
        GeneralResidues.mk.injEq, true_and, and_true,
        funext_iff]
      constructor
      · intro h
        have hq := h q
        simpa [ZMod.intCast_zmod_eq_zero_iff_dvd] using hq
      · intro h x
        by_cases hx : x = q
        · subst x
          simpa [ZMod.intCast_zmod_eq_zero_iff_dvd] using h
        · simp [hx]

/-- In the residue group, integer powers of a unit coordinate axis are
the corresponding integral axes. -/
theorem general_axis_zpow
    {t : ℕ} (order : Fin t → ℕ)
    (horder : ∀ i, AOrd (order i))
    (i : GeneralBasisIndex t) (n : ℤ) :
    ((generalAxis i 1 :
        GeneralResidueGroup order horder) ^ n) =
      (generalAxis i n :
        GeneralResidueGroup order horder) := by
  let quotientMap := (generalCon order horder).mk'
  change quotientMap (generalAxis i 1) ^ n =
    quotientMap (generalAxis i n)
  rw [← map_zpow]
  exact congrArg quotientMap (general_axis_one i n)

/-- Natural powers of a unit residue axis vanish exactly at multiples of
its coordinate modulus. -/
theorem general_residue_axis
    {t : ℕ} (order : Fin t → ℕ)
    (horder : ∀ i, AOrd (order i))
    (i : GeneralBasisIndex t) (n : ℕ) :
    (generalAxis i 1 :
        GeneralResidueGroup order horder) ^ n = 1 ↔
      generalCoordinateModulus order i ∣ n := by
  rw [show
    (generalAxis i 1 :
        GeneralResidueGroup order horder) ^ n =
      (generalAxis i (n : ℤ) :
        GeneralResidueGroup order horder) by
      simpa using
        general_axis_zpow
          order horder i (n : ℤ)]
  change
    (generalCon order horder).mk'
        (generalAxis i (n : ℤ)) =
      (generalCon order horder).mk'
        (GCoordi.zero t) ↔ _
  constructor
  · intro h
    have hm := (generalCon order horder).eq.mp h
    exact Int.natCast_dvd_natCast.mp
      ((general_axis_mod
        order i (n : ℤ)).mp hm)
  · intro h
    apply (generalCon order horder).eq.mpr
    exact (general_axis_mod
      order i (n : ℤ)).mpr
        (Int.natCast_dvd_natCast.mpr h)

/-- The unit residue axis has exactly its prescribed coordinate order,
including order zero for an infinite coordinate. -/
theorem general_axis_order
    {t : ℕ} (order : Fin t → ℕ)
    (horder : ∀ i, AOrd (order i))
    (i : GeneralBasisIndex t) :
    orderOf
      (generalAxis i 1 :
        GeneralResidueGroup order horder) =
      generalCoordinateModulus order i := by
  apply Nat.dvd_antisymm
  · rw [orderOf_dvd_iff_pow_eq_one]
    exact
      (general_residue_axis
        order horder i _).2 dvd_rfl
  · exact
      (general_residue_axis
        order horder i _).1
        (pow_orderOf_eq_one _)

private theorem modulus_dvd_abs
    (m : ℕ) (a : ℤ) :
    m ∣ cyclicCoordinateOrder m a * a.natAbs := by
  by_cases ha : a = 0
  · subst a
    simp [cyclicCoordinateOrder]
  obtain ⟨k, hk⟩ := Nat.gcd_dvd_right m a.natAbs
  refine ⟨k, ?_⟩
  rw [cyclicCoordinateOrder, if_neg ha]
  calc
    m / Nat.gcd m a.natAbs * a.natAbs =
        m / Nat.gcd m a.natAbs *
          (Nat.gcd m a.natAbs * k) :=
      congrArg
        (fun x => m / Nat.gcd m a.natAbs * x) hk
    _ = m * k := by
      rw [← Nat.mul_assoc,
        Nat.div_mul_cancel (Nat.gcd_dvd_left m a.natAbs)]

private theorem general_modulus_lcm
    {t : ℕ} (order : Fin t → ℕ)
    (c : GCoordi t)
    (i : GeneralBasisIndex t) :
    (generalCoordinateModulus order i : ℤ) ∣
      (generalOrderLCM order c : ℤ) *
        generalCoordinateExponent c i := by
  rw [Int.natCast_dvd]
  simp only [Int.natAbs_mul, Int.natAbs_natCast]
  exact
    (modulus_dvd_abs
      (generalCoordinateModulus order i)
      (generalCoordinateExponent c i)).trans
      (Nat.mul_dvd_mul_right
        (Finset.dvd_lcm (Finset.mem_univ i))
        (generalCoordinateExponent c i).natAbs)

/-- The lcm of the exact coordinate-factor orders kills every displayed
Hall factor. -/
theorem lcm_orders_divide
    {t : ℕ} (order : Fin t → ℕ)
    (c : GCoordi t) :
    GeneralOrdersDivide order c
      (generalOrderLCM order c) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    simpa [generalCoordinateModulus,
      generalCoordinateExponent] using
      general_modulus_lcm
        order c (.single i)
  · intro q
    simpa [generalCoordinateModulus,
      generalCoordinateExponent] using
      general_modulus_lcm
        order c (.pair q)
  · intro q
    simpa [generalCoordinateModulus,
      generalCoordinateExponent] using
      general_modulus_lcm
        order c (.pairLeft q)
  · intro q
    simpa [generalCoordinateModulus,
      generalCoordinateExponent] using
      general_modulus_lcm
        order c (.pairRight q)
  · intro q
    simpa [generalCoordinateModulus,
      generalCoordinateExponent] using
      general_modulus_lcm
        order c (.tripleFirst q)
  · intro q
    simpa [generalCoordinateModulus,
      generalCoordinateExponent] using
      general_modulus_lcm
        order c (.tripleSecond q)

private theorem general_modulus_odd
    {t : ℕ} (order : Fin t → ℕ)
    (hoddOrder : ∀ i, Odd (order i))
    (i : GeneralBasisIndex t) :
    Odd (generalCoordinateModulus order i) := by
  cases i with
  | single i =>
      exact hoddOrder i
  | pair q | pairLeft q | pairRight q =>
      exact
        (hoddOrder q.i).of_dvd_nat
          (Nat.gcd_dvd_left (order q.i) (order q.j))
  | tripleFirst q | tripleSecond q =>
      exact
        (hoddOrder q.i).of_dvd_nat
          ((Nat.gcd_dvd_left
            (Nat.gcd (order q.i) (order q.j))
            (order q.k)).trans
              (Nat.gcd_dvd_left (order q.i) (order q.j)))

private theorem general_modulus_admissible
    {t : ℕ} (order : Fin t → ℕ)
    (horder : ∀ i, AOrd (order i))
    (i : GeneralBasisIndex t) :
    AOrd (generalCoordinateModulus order i) := by
  cases i with
  | single i =>
      exact horder i
  | pair q | pairLeft q | pairRight q =>
      exact (horder q.i).gcd (horder q.j)
  | tripleFirst q | tripleSecond q =>
      exact ((horder q.i).gcd (horder q.j)).gcd (horder q.k)

private theorem cyclic_order_admissible
    {m : ℕ} (hm : AOrd m) (a : ℤ) :
    AOrd (cyclicCoordinateOrder m a) := by
  by_cases ha : a = 0
  · exact Or.inr (by simp [cyclicCoordinateOrder, ha])
  rw [cyclicCoordinateOrder, if_neg ha]
  rcases hm with rfl | hm
  · exact Or.inl (by simp)
  · exact Or.inr
      (hm.of_dvd_nat
        (Nat.div_dvd_of_dvd
          (Nat.gcd_dvd_left m a.natAbs)))

private theorem general_order_admissible
    {t : ℕ} (order : Fin t → ℕ)
    (horder : ∀ i, AOrd (order i))
    (c : GCoordi t)
    (i : GeneralBasisIndex t) :
    AOrd
      (generalCoordinateOrder order c i) :=
  cyclic_order_admissible
    (general_modulus_admissible order horder i)
    (generalCoordinateExponent c i)

/-- With odd-or-zero ambient orders, the lcm of the displayed factor orders
is itself odd or zero. -/
theorem general_lcm_admissible
    {t : ℕ} (order : Fin t → ℕ)
    (horder : ∀ i, AOrd (order i))
    (c : GCoordi t) :
    AOrd (generalOrderLCM order c) := by
  by_cases hzero : generalOrderLCM order c = 0
  · exact Or.inl hzero
  · refine Or.inr ?_
    have hfactorOdd :
        ∀ i : GeneralBasisIndex t,
          Odd (generalCoordinateOrder order c i) := by
      intro i
      rcases
          general_order_admissible
            order horder c i with hi | hi
      · exfalso
        apply hzero
        rw [generalOrderLCM,
          Finset.lcm_eq_zero_iff]
        exact ⟨i, Finset.mem_univ i, hi⟩
      · exact hi
    have hprod :
        Odd
          ((Finset.univ : Finset (GeneralBasisIndex t)).prod
            (generalCoordinateOrder order c)) := by
      apply Finset.prod_induction
      · exact fun _ _ => Odd.mul
      · exact odd_one
      · intro i _
        exact hfactorOdd i
    exact hprod.of_dvd_nat
      (Finset.lcm_dvd_prod
        (Finset.univ : Finset (GeneralBasisIndex t))
        (generalCoordinateOrder order c))

private theorem general_order_ne
    {t : ℕ} (order : Fin t → ℕ)
    (c : GCoordi t)
    (hfinite : GeneralDisplayedFactors order c)
    (i : GeneralBasisIndex t) :
    generalCoordinateOrder order c i ≠ 0 := by
  by_cases hzero : generalCoordinateExponent c i = 0
  · simp [generalCoordinateOrder,
      cyclicCoordinateOrder, hzero]
  · rw [generalCoordinateOrder,
      cyclicCoordinateOrder, if_neg hzero]
    have hmodulus :
        generalCoordinateModulus order i ≠ 0 :=
      hfinite i hzero
    have hmodulusPos :
        0 < generalCoordinateModulus order i :=
      Nat.pos_of_ne_zero hmodulus
    exact
      (Nat.div_pos
        (Nat.le_of_dvd hmodulusPos
          (Nat.gcd_dvd_left
            (generalCoordinateModulus order i)
            (generalCoordinateExponent c i).natAbs))
        (Nat.gcd_pos_of_pos_left _ hmodulusPos)).ne'

theorem general_lcm_ne
    {t : ℕ} (order : Fin t → ℕ)
    (c : GCoordi t)
    (hfinite : GeneralDisplayedFactors order c) :
    generalOrderLCM order c ≠ 0 := by
  rw [generalOrderLCM,
    Finset.lcm_ne_zero_iff]
  intro i _
  exact
    general_order_ne
      order c hfinite i

theorem general_lcm_odd
    {t : ℕ} (order : Fin t → ℕ)
    (horder : ∀ i, AOrd (order i))
    (c : GCoordi t)
    (hfinite : GeneralDisplayedFactors order c) :
    Odd (generalOrderLCM order c) := by
  rcases general_lcm_admissible
      order horder c with hzero | hodd
  · exact
      (general_lcm_ne
        order c hfinite hzero).elim
  · exact hodd

/-- The cyclic-coordinate formula is the actual group-theoretic order of
the corresponding displayed Hall factor in the residue model. -/
theorem residue_axis_order
    {t : ℕ} (order : Fin t → ℕ)
    (hoddOrder : ∀ i, Odd (order i))
    (c : GCoordi t)
    (i : GeneralBasisIndex t) :
    orderOf
      (generalAxis i
        (generalCoordinateExponent c i) :
          GeneralResidueGroup order
            (fun j => AOrd.of_odd (hoddOrder j))) =
      generalCoordinateOrder order c i := by
  let horder : ∀ j, AOrd (order j) :=
    fun j => AOrd.of_odd (hoddOrder j)
  let x : GeneralResidueGroup order horder :=
    generalAxis i 1
  have hx :
      orderOf x = generalCoordinateModulus order i :=
    general_axis_order order horder i
  change orderOf
    (generalAxis i
      (generalCoordinateExponent c i) :
        GeneralResidueGroup order horder) = _
  rw [← general_axis_zpow order horder]
  have hmodOdd :
      Odd (generalCoordinateModulus order i) :=
    general_modulus_odd order hoddOrder i
  cases h : generalCoordinateExponent c i with
  | ofNat n =>
      cases n with
      | zero =>
          unfold generalCoordinateOrder
            cyclicCoordinateOrder
          rw [h]
          simp
      | succ n =>
          change orderOf (x ^ (n + 1)) = _
          rw [orderOf_pow' x (by omega), hx]
          unfold generalCoordinateOrder
            cyclicCoordinateOrder
          rw [h]
          simp only [Int.ofNat_eq_natCast, Int.natCast_eq_zero,
            Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, if_false]
          rfl
  | negSucc n =>
      change orderOf ((x ^ (n + 1))⁻¹) = _
      rw [orderOf_inv, orderOf_pow' x (by omega), hx]
      unfold generalCoordinateOrder
        cyclicCoordinateOrder
      rw [h]
      simp only [Int.negSucc_ne_zero, if_false]
      rfl

/-- Thus `generalOrderLCM` is literally the least common
multiple of the group-theoretic orders of the displayed residue-axis
factors. -/
theorem general_order_lcm
    {t : ℕ} (order : Fin t → ℕ)
    (hoddOrder : ∀ i, Odd (order i))
    (c : GCoordi t) :
    generalOrderLCM order c =
      Finset.univ.lcm
        (fun i : GeneralBasisIndex t =>
          orderOf
            (generalAxis i
              (generalCoordinateExponent c i) :
                GeneralResidueGroup order
                  (fun j =>
                    AOrd.of_odd (hoddOrder j)))) := by
  apply Finset.lcm_congr rfl
  intro i _
  exact (residue_axis_order
    order hoddOrder c i).symm

private theorem general_order_odd
    {t : ℕ} (order : Fin t → ℕ)
    (hoddOrder : ∀ i, Odd (order i))
    (c : GCoordi t)
    (i : GeneralBasisIndex t) :
    Odd (generalCoordinateOrder order c i) := by
  by_cases hzero : generalCoordinateExponent c i = 0
  · simp [generalCoordinateOrder,
      cyclicCoordinateOrder, hzero]
  · rw [generalCoordinateOrder,
      cyclicCoordinateOrder, if_neg hzero]
    exact
      (general_modulus_odd order hoddOrder i).of_dvd_nat
        (Nat.div_dvd_of_dvd
          (Nat.gcd_dvd_left
            (generalCoordinateModulus order i)
            (generalCoordinateExponent c i).natAbs))

/-- For finite odd cyclic factors, the lcm of all coordinate-factor orders
is itself odd. -/
theorem order_lcm_odd
    {t : ℕ} (order : Fin t → ℕ)
    (hoddOrder : ∀ i, Odd (order i))
    (c : GCoordi t) :
    Odd (generalOrderLCM order c) := by
  have hprod :
      Odd
        ((Finset.univ : Finset (GeneralBasisIndex t)).prod
          (generalCoordinateOrder order c)) := by
    apply Finset.prod_induction
    · exact fun _ _ => Odd.mul
    · exact odd_one
    · intro i _
      exact general_order_odd
        order hoddOrder c i
  exact hprod.of_dvd_nat
    (Finset.lcm_dvd_prod
      (Finset.univ : Finset (GeneralBasisIndex t))
      (generalCoordinateOrder order c))

/-- A nonzero coordinate of modulus zero forces the represented residue
element to have infinite order.  The proof follows the triangular power
table: a finite power first kills the relevant weight-one coordinates,
then weight-two coordinates, and finally weight-three coordinates. -/
theorem general_residue_coordinate
    {t : ℕ} (order : Fin t → ℕ)
    (horder : ∀ i, AOrd (order i))
    (c : GCoordi t)
    (i : GeneralBasisIndex t)
    (hmodulus : generalCoordinateModulus order i = 0)
    (hexponent : generalCoordinateExponent c i ≠ 0) :
    ¬ IsOfFinOrder
      (c : GeneralResidueGroup order horder) := by
  intro hfinite
  obtain ⟨n, hn, hpow⟩ := hfinite.exists_pow_eq_one
  let quotientMap := (generalCon order horder).mk'
  have hpow' :
      quotientMap (c ^ n) =
        quotientMap (GCoordi.zero t) := by
    rw [map_pow]
    exact hpow
  have hm := (generalCon order horder).eq.mp hpow'
  rw [general_pow] at hm
  have hnInt : (n : ℤ) ≠ 0 :=
    Int.natCast_ne_zero_iff_pos.mpr hn
  have hsingle :
      ∀ j, order j = 0 → c.single j = 0 := by
    intro j hj
    have h := hm.single j
    rw [hj] at h
    have hmul : (n : ℤ) * c.single j = 0 := by
      simpa [generalPowCoordinates,
        GCoordi.zero, Int.ModEq] using h
    exact (Int.mul_eq_zero.mp hmul).resolve_left hnInt
  have hpair :
      ∀ q, generalPairModulus order q = 0 → c.pair q = 0 := by
    intro q hq
    have horders : order q.i = 0 ∧ order q.j = 0 :=
      Nat.gcd_eq_zero_iff.mp hq
    have hi := hsingle q.i horders.1
    have hj := hsingle q.j horders.2
    have h := hm.pair q
    rw [hq] at h
    have hmul : (n : ℤ) * c.pair q = 0 := by
      simpa [generalPowCoordinates,
        GCoordi.zero, hi, hj, Int.ModEq] using h
    exact (Int.mul_eq_zero.mp hmul).resolve_left hnInt
  have hpairLeft :
      ∀ q, generalPairModulus order q = 0 →
        c.pairLeft q = 0 := by
    intro q hq
    have horders : order q.i = 0 ∧ order q.j = 0 :=
      Nat.gcd_eq_zero_iff.mp hq
    have hi := hsingle q.i horders.1
    have hj := hsingle q.j horders.2
    have hp := hpair q hq
    have h := hm.pairLeft q
    rw [hq] at h
    have hmul : (n : ℤ) * c.pairLeft q = 0 := by
      simpa [generalPowCoordinates,
        GCoordi.zero, hi, hj, hp, Int.ModEq] using h
    exact (Int.mul_eq_zero.mp hmul).resolve_left hnInt
  have hpairRight :
      ∀ q, generalPairModulus order q = 0 →
        c.pairRight q = 0 := by
    intro q hq
    have horders : order q.i = 0 ∧ order q.j = 0 :=
      Nat.gcd_eq_zero_iff.mp hq
    have hi := hsingle q.i horders.1
    have hj := hsingle q.j horders.2
    have hp := hpair q hq
    have h := hm.pairRight q
    rw [hq] at h
    have hmul : (n : ℤ) * c.pairRight q = 0 := by
      simpa [generalPowCoordinates,
        GCoordi.zero, hi, hj, hp, Int.ModEq] using h
    exact (Int.mul_eq_zero.mp hmul).resolve_left hnInt
  have htripleFirst :
      ∀ q, generalResiduesModulus order q = 0 →
        c.tripleFirst q = 0 := by
    intro q hq
    have horders :
        Nat.gcd (order q.i) (order q.j) = 0 ∧ order q.k = 0 :=
      Nat.gcd_eq_zero_iff.mp hq
    have hij : order q.i = 0 ∧ order q.j = 0 :=
      Nat.gcd_eq_zero_iff.mp horders.1
    have hi := hsingle q.i hij.1
    have hj := hsingle q.j hij.2
    have hk := hsingle q.k horders.2
    have hpik : c.pair q.ik = 0 := by
      apply hpair q.ik
      simp [generalPairModulus, Triple.ik,
        hij.1, horders.2]
    have hpij : c.pair q.ij = 0 := by
      apply hpair q.ij
      simp [generalPairModulus, Triple.ij,
        hij.1, hij.2]
    have h := hm.tripleFirst q
    rw [hq] at h
    have hmul : (n : ℤ) * c.tripleFirst q = 0 := by
      simpa [generalPowCoordinates,
        GCoordi.zero, hi, hj, hk, hpik, hpij,
        Int.ModEq] using h
    exact (Int.mul_eq_zero.mp hmul).resolve_left hnInt
  have htripleSecond :
      ∀ q, generalResiduesModulus order q = 0 →
        c.tripleSecond q = 0 := by
    intro q hq
    have horders :
        Nat.gcd (order q.i) (order q.j) = 0 ∧ order q.k = 0 :=
      Nat.gcd_eq_zero_iff.mp hq
    have hij : order q.i = 0 ∧ order q.j = 0 :=
      Nat.gcd_eq_zero_iff.mp horders.1
    have hi := hsingle q.i hij.1
    have hj := hsingle q.j hij.2
    have hk := hsingle q.k horders.2
    have hpjk : c.pair q.jk = 0 := by
      apply hpair q.jk
      simp [generalPairModulus, Triple.jk,
        hij.2, horders.2]
    have hpik : c.pair q.ik = 0 := by
      apply hpair q.ik
      simp [generalPairModulus, Triple.ik,
        hij.1, horders.2]
    have h := hm.tripleSecond q
    rw [hq] at h
    have hmul : (n : ℤ) * c.tripleSecond q = 0 := by
      simpa [generalPowCoordinates,
        GCoordi.zero, hi, hj, hk, hpjk, hpik,
        Int.ModEq] using h
    exact (Int.mul_eq_zero.mp hmul).resolve_left hnInt
  apply hexponent
  cases i with
  | single i =>
      exact hsingle i hmodulus
  | pair q =>
      exact hpair q hmodulus
  | pairLeft q =>
      exact hpairLeft q hmodulus
  | pairRight q =>
      exact hpairRight q hmodulus
  | tripleFirst q =>
      exact htripleFirst q hmodulus
  | tripleSecond q =>
      exact htripleSecond q hmodulus

/-- Order-zero formulation of the preceding infinite-order theorem. -/
theorem general_order_coordinate
    {t : ℕ} (order : Fin t → ℕ)
    (horder : ∀ i, AOrd (order i))
    (c : GCoordi t)
    (i : GeneralBasisIndex t)
    (hmodulus : generalCoordinateModulus order i = 0)
    (hexponent : generalCoordinateExponent c i ≠ 0) :
    orderOf
      (c : GeneralResidueGroup order horder) = 0 :=
  orderOf_eq_zero_iff.mpr
    (general_residue_coordinate
      order horder c i hmodulus hexponent)

/-- **Struik's Corollary 1, ordinary case.**  Suppose the equation-(18)
normal form of `g` is `c`, and every displayed Hall factor in `c` has
order dividing the odd integer `N`.  If `3 ∤ N`, then `g ^ N = 1`.

The coordinate divisibility hypothesis is exactly the statement that each
factor `uᵢ ^ cᵢ` occurring in the normal form is killed by `N`; hence it
holds when `N` is their least common multiple. -/
theorem pow_not_dvd
    {t N : ℕ} (order : Fin t → ℕ)
    (horder : ∀ i, AOrd (order i))
    (g : NilpotentCyclicProduct order 4)
    (c : GCoordi t)
    (hmap :
      nilpotentGeneralResidues
          order horder g =
        (c : GeneralResidueGroup order horder))
    (hc : GeneralOrdersDivide order c N)
    (hoddN : Odd N)
    (hthree : ¬3 ∣ N) :
    g ^ N = 1 := by
  let f :=
    nilpotentGeneralResidues order horder
  have hf : Function.Injective f :=
    (odd_bijective_admissible
      order horder).1
  apply hf
  rw [map_pow, map_one]
  change
    (f g) ^ N =
      (1 : GeneralResidueGroup order horder)
  rw [hmap]
  exact
    general_residue_dvd
      order horder c hc hoddN hthree

/-- **Struik's Corollary 1, exceptional bound.**  Under the same normal-form
hypothesis, `3N` always kills `g`.  The order-nine examples below show that
the extra factor three can be necessary when `3 ∣ N`. -/
theorem pow_three_one
    {t N : ℕ} (order : Fin t → ℕ)
    (horder : ∀ i, AOrd (order i))
    (g : NilpotentCyclicProduct order 4)
    (c : GCoordi t)
    (hmap :
      nilpotentGeneralResidues
          order horder g =
        (c : GeneralResidueGroup order horder))
    (hc : GeneralOrdersDivide order c N)
    (hoddN : Odd N) :
    g ^ (3 * N) = 1 := by
  let f :=
    nilpotentGeneralResidues order horder
  have hf : Function.Injective f :=
    (odd_bijective_admissible
      order horder).1
  apply hf
  rw [map_pow, map_one]
  change
    (f g) ^ (3 * N) =
      (1 : GeneralResidueGroup order horder)
  rw [hmap]
  exact
    general_residue_pow
      order horder c hc hoddN

/-- **Struik's Corollary 1, exact ordinary bound.**  Let `N` be the least
common multiple of the orders of the displayed factors `uᵢ ^ cᵢ` in the
equation-(18) normal form of `g`.  If `3 ∤ N`, then `g ^ N = 1`. -/
theorem factor_lcm_dvd
    {t : ℕ} (order : Fin t → ℕ)
    (horder : ∀ i, AOrd (order i))
    (g : NilpotentCyclicProduct order 4)
    (c : GCoordi t)
    (hmap :
      nilpotentGeneralResidues
          order horder g =
        (c : GeneralResidueGroup order horder))
    (hthree : ¬3 ∣ generalOrderLCM order c) :
    g ^ generalOrderLCM order c = 1 := by
  have hoddLCM :
      Odd (generalOrderLCM order c) := by
    rcases general_lcm_admissible
        order horder c with hzero | hodd
    · exfalso
      apply hthree
      rw [hzero]
      exact dvd_zero 3
    · exact hodd
  exact pow_not_dvd
    order horder g c hmap
      (lcm_orders_divide order c)
      hoddLCM
      hthree

/-- **Struik's Corollary 1, exact exceptional bound.**  If every displayed
nontrivial factor has finite order, then with the same least common multiple
`N`, the power `3N` always kills `g`. -/
theorem factor_order_lcm
    {t : ℕ} (order : Fin t → ℕ)
    (horder : ∀ i, AOrd (order i))
    (g : NilpotentCyclicProduct order 4)
    (c : GCoordi t)
    (hmap :
      nilpotentGeneralResidues
          order horder g =
        (c : GeneralResidueGroup order horder))
    (hfinite : GeneralDisplayedFactors order c) :
    g ^ (3 * generalOrderLCM order c) = 1 := by
  exact pow_three_one
    order horder g c hmap
      (lcm_orders_divide order c)
      (general_lcm_odd
        order horder c hfinite)

/-- **Corollary to Theorem 3, Case II, commutator branch in class three.**
If the weight-one coordinates of the equation-(18) normal form vanish, then
any common multiple `N` of the displayed factor orders kills the element.
No restriction on divisibility by three is needed. -/
theorem pow_single_zero
    {t N : ℕ} (order : Fin t → ℕ)
    (horder : ∀ i, AOrd (order i))
    (g : NilpotentCyclicProduct order 4)
    (c : GCoordi t)
    (hmap :
      nilpotentGeneralResidues
          order horder g =
        (c : GeneralResidueGroup order horder))
    (hc : GeneralOrdersDivide order c N)
    (hsingle : ∀ i, c.single i = 0) :
    g ^ N = 1 := by
  let f :=
    nilpotentGeneralResidues order horder
  have hf : Function.Injective f :=
    (odd_bijective_admissible
      order horder).1
  apply hf
  rw [map_pow, map_one]
  change
    (f g) ^ N =
      (1 : GeneralResidueGroup order horder)
  rw [hmap]
  exact general_residue_single
    order horder c hc hsingle

/-- Exact-LCM form of the class-three commutator branch. -/
theorem factor_lcm_single
    {t : ℕ} (order : Fin t → ℕ)
    (horder : ∀ i, AOrd (order i))
    (g : NilpotentCyclicProduct order 4)
    (c : GCoordi t)
    (hmap :
      nilpotentGeneralResidues
          order horder g =
        (c : GeneralResidueGroup order horder))
    (hsingle : ∀ i, c.single i = 0) :
    g ^ generalOrderLCM order c = 1 :=
  pow_single_zero
    order horder g c hmap
      (lcm_orders_divide order c)
      hsingle

/-- **Struik's Corollary 1, infinite-factor clause.**  If a displayed
normal-form factor has modulus zero and nonzero exponent, then the element
has infinite order.  This conclusion only needs the canonical map to the
equation-(18) model, not injectivity of that map. -/
theorem not_modulus_coordinate
    {t : ℕ} (order : Fin t → ℕ)
    (horder : ∀ i, AOrd (order i))
    (g : NilpotentCyclicProduct order 4)
    (c : GCoordi t)
    (hmap :
      nilpotentGeneralResidues
          order horder g =
        (c : GeneralResidueGroup order horder))
    (i : GeneralBasisIndex t)
    (hmodulus : generalCoordinateModulus order i = 0)
    (hexponent : generalCoordinateExponent c i ≠ 0) :
    ¬ IsOfFinOrder g := by
  intro hfinite
  obtain ⟨n, hn, hpow⟩ := hfinite.exists_pow_eq_one
  apply general_residue_coordinate
    order horder c i hmodulus hexponent
  refine isOfFinOrder_iff_pow_eq_one.mpr ⟨n, hn, ?_⟩
  rw [← hmap, ← map_pow, hpow, map_one]

/-- Order-zero formulation of Struik's infinite-factor clause. -/
theorem order_modulus_coordinate
    {t : ℕ} (order : Fin t → ℕ)
    (horder : ∀ i, AOrd (order i))
    (g : NilpotentCyclicProduct order 4)
    (c : GCoordi t)
    (hmap :
      nilpotentGeneralResidues
          order horder g =
        (c : GeneralResidueGroup order horder))
    (i : GeneralBasisIndex t)
    (hmodulus : generalCoordinateModulus order i = 0)
    (hexponent : generalCoordinateExponent c i ≠ 0) :
    orderOf g = 0 :=
  orderOf_eq_zero_iff.mpr
    (not_modulus_coordinate
      order horder g c hmap i hmodulus hexponent)

/-- The two cyclic factors in Struik's group (19). -/
def orderThreePair (_ : Fin 2) : ℕ := 3

theorem order_pair_admissible :
    ∀ i, AOrd (orderThreePair i) := by
  intro i
  exact AOrd.of_odd (by norm_num [orderThreePair])

/-- The product `ab` in the third nilpotent product of two cyclic groups
of order three. -/
def orderPairProduct :
    NilpotentCyclicProduct orderThreePair 4 :=
  nilpotentCyclicGenerator orderThreePair 4 0 *
    nilpotentCyclicGenerator orderThreePair 4 1

/-- The four products `aᵘbᵛ` with both exponents nonzero modulo three. -/
def orderPairNonzero (u v : Fin 2) :
    NilpotentCyclicProduct orderThreePair 4 :=
  nilpotentCyclicGenerator orderThreePair 4 0 ^ (u.1 + 1) *
    nilpotentCyclicGenerator orderThreePair 4 1 ^ (v.1 + 1)

private def rankTwoCoordinates
    (leftSingle rightSingle pair pairLeft pairRight : ℤ) :
    GCoordi 2 where
  single i := if i = 0 then leftSingle else rightSingle
  pair _ := pair
  pairLeft _ := pairLeft
  pairRight _ := pairRight
  tripleFirst _ := 0
  tripleSecond _ := 0

private theorem choose_one_two :
    Ring.choose (1 : ℤ) 2 = 0 := by
  decide

private theorem choose_two_two :
    Ring.choose (2 : ℤ) 2 = 1 := by
  decide

private theorem choose_three_two :
    Ring.choose (3 : ℤ) 2 = 3 := by
  decide

private theorem choose_four_two :
    Ring.choose (4 : ℤ) 2 = 6 := by
  decide

private theorem choose_six_two :
    Ring.choose (6 : ℤ) 2 = 15 := by
  decide

private theorem choose_twelve_two :
    Ring.choose (12 : ℤ) 2 = 66 := by
  decide

private theorem rank_coordinates_mul
    (a₀ a₁ p l r b₀ b₁ q m s : ℤ) :
    GCoordi.mul
        (rankTwoCoordinates a₀ a₁ p l r)
        (rankTwoCoordinates b₀ b₁ q m s) =
      rankTwoCoordinates
        (a₀ + b₀)
        (a₁ + b₁)
        (p + q - a₁ * b₀)
        (l + m - a₁ * Ring.choose b₀ 2 + p * b₀)
        (r + s - b₀ * Ring.choose a₁ 2 + p * b₁ - b₀ * b₁ * a₁) := by
  ext i
  · fin_cases i <;>
      simp [rankTwoCoordinates, GCoordi.mul]
  · rcases i with ⟨i, j, hij⟩
    have hi : i = 0 := by omega
    have hj : j = 1 := by omega
    subst i
    subst j
    simp [rankTwoCoordinates, GCoordi.mul]
  · rcases i with ⟨i, j, hij⟩
    have hi : i = 0 := by omega
    have hj : j = 1 := by omega
    subst i
    subst j
    simp [rankTwoCoordinates, GCoordi.mul]
  · rcases i with ⟨i, j, hij⟩
    have hi : i = 0 := by omega
    have hj : j = 1 := by omega
    subst i
    subst j
    simp [rankTwoCoordinates, GCoordi.mul]
  · rcases i with ⟨i, j, k, hij, hjk⟩
    omega
  · rcases i with ⟨i, j, k, hij, hjk⟩
    omega

private noncomputable def rankCubeCoordinates
    (leftSingle rightSingle pair pairLeft pairRight : ℤ) :
    GCoordi 2 :=
  rankTwoCoordinates
    (3 * leftSingle)
    (3 * rightSingle)
    (3 * pair - 3 * rightSingle * leftSingle)
    (3 * pairLeft -
      3 * rightSingle * Ring.choose leftSingle 2 +
      3 * pair * leftSingle -
      rightSingle * leftSingle * leftSingle)
    (3 * pairRight -
      leftSingle * Ring.choose rightSingle 2 -
      leftSingle * Ring.choose (2 * rightSingle) 2 +
      3 * pair * rightSingle -
      4 * leftSingle * rightSingle * rightSingle)

private noncomputable def rankCubeTail
    (leftSingle rightSingle : ℤ) :
    GCoordi 2 :=
  rankTwoCoordinates 0 0 0
    (-3 * rightSingle * Ring.choose leftSingle 2 -
      rightSingle * leftSingle * leftSingle)
    (-leftSingle * Ring.choose rightSingle 2 -
      leftSingle * Ring.choose (2 * rightSingle) 2 -
      4 * leftSingle * rightSingle * rightSingle)

private theorem rank_coordinates_cube
    (leftSingle rightSingle pair pairLeft pairRight : ℤ) :
    rankTwoCoordinates leftSingle rightSingle pair pairLeft pairRight ^ 3 =
      rankCubeCoordinates
        leftSingle rightSingle pair pairLeft pairRight := by
  rw [show
      rankTwoCoordinates leftSingle rightSingle pair pairLeft pairRight ^ 3 =
        (rankTwoCoordinates leftSingle rightSingle pair pairLeft pairRight *
          rankTwoCoordinates leftSingle rightSingle pair pairLeft pairRight) *
            rankTwoCoordinates leftSingle rightSingle pair pairLeft pairRight by
      simp [pow_succ]]
  change
    GCoordi.mul
        (GCoordi.mul
          (rankTwoCoordinates
            leftSingle rightSingle pair pairLeft pairRight)
          (rankTwoCoordinates
            leftSingle rightSingle pair pairLeft pairRight))
        (rankTwoCoordinates
          leftSingle rightSingle pair pairLeft pairRight) =
      rankCubeCoordinates
        leftSingle rightSingle pair pairLeft pairRight
  rw [rank_coordinates_mul, rank_coordinates_mul]
  unfold rankCubeCoordinates
  congr 1 <;> ring_nf

private theorem coordinates_cube_tail
    (leftSingle rightSingle : ℤ) :
    (rankTwoCoordinates leftSingle rightSingle 0 0 0 :
      GeneralResidueGroup
        orderThreePair order_pair_admissible) ^ 3 =
      (rankCubeTail leftSingle rightSingle :
        GeneralResidueGroup
          orderThreePair order_pair_admissible) := by
  apply
    (generalCon
      orderThreePair order_pair_admissible).eq.mpr
  change
    GMEq orderThreePair
      (rankTwoCoordinates leftSingle rightSingle 0 0 0 ^ 3)
      (rankCubeTail leftSingle rightSingle)
  rw [rank_coordinates_cube]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    fin_cases i <;>
      simp [rankCubeCoordinates, rankCubeTail, rankTwoCoordinates,
        orderThreePair, Int.ModEq]
  · intro q
    simp only [Int.ModEq, rankCubeCoordinates, rankTwoCoordinates,
      Fin.isValue, mul_zero, zero_sub, zero_mul, add_zero,
      generalPairModulus, orderThreePair, Nat.gcd_self, Nat.cast_ofNat,
      rankCubeTail, ite_self, Int.reduceNeg, neg_mul,
      EuclideanDomain.zero_mod, EuclideanDomain.mod_eq_zero, dvd_neg]
    exact ⟨rightSingle * leftSingle, by ring⟩
  · intro q
    simp [rankCubeCoordinates, rankCubeTail, rankTwoCoordinates,
      orderThreePair, generalPairModulus]
  · intro q
    simp [rankCubeCoordinates, rankCubeTail, rankTwoCoordinates,
      orderThreePair, generalPairModulus]
  · intro q
    simp [rankCubeCoordinates, rankCubeTail, rankTwoCoordinates]
  · intro q
    simp [rankCubeCoordinates, rankCubeTail, rankTwoCoordinates]

private theorem rank_cube_series
    (leftSingle rightSingle : ℤ) :
    (rankCubeTail leftSingle rightSingle :
      GeneralResidueGroup
        orderThreePair order_pair_admissible) ∈
      Subgroup.lowerCentralSeries
        (GeneralResidueGroup
          orderThreePair order_pair_admissible) 2 := by
  let quotientMap :=
    (generalCon
      orderThreePair order_pair_admissible).mk'
  let q : Pair 2 := ⟨0, 1, by decide⟩
  let leftExponent :=
    -3 * rightSingle * Ring.choose leftSingle 2 -
      rightSingle * leftSingle * leftSingle
  let rightExponent :=
    -leftSingle * Ring.choose rightSingle 2 -
      leftSingle * Ring.choose (2 * rightSingle) 2 -
      4 * leftSingle * rightSingle * rightSingle
  have hleftOne :
      quotientMap (generalAxis (.pairLeft q) 1) ∈
        Subgroup.lowerCentralSeries
          (GeneralResidueGroup
            orderThreePair order_pair_admissible) 2 := by
    have heq :
        quotientMap (generalAxis (.pairLeft q) 1) =
          hallTripleCommutator
            (quotientMap (generalGenerator q.i))
            (quotientMap (generalGenerator q.j))
            (quotientMap (generalGenerator q.i)) := by
      symm
      simpa [hallCommutator, hallTripleCommutator] using
        congrArg quotientMap
          (general_triple_left q)
    rw [heq]
    exact triple_series_general _ _ _
  have hrightOne :
      quotientMap (generalAxis (.pairRight q) 1) ∈
        Subgroup.lowerCentralSeries
          (GeneralResidueGroup
            orderThreePair order_pair_admissible) 2 := by
    have heq :
        quotientMap (generalAxis (.pairRight q) 1) =
          hallTripleCommutator
            (quotientMap (generalGenerator q.i))
            (quotientMap (generalGenerator q.j))
            (quotientMap (generalGenerator q.j)) := by
      symm
      simpa [hallCommutator, hallTripleCommutator] using
        congrArg quotientMap
          (general_triple_pair q)
    rw [heq]
    exact triple_series_general _ _ _
  have hleft :
      quotientMap (generalAxis (.pairLeft q) leftExponent) ∈
        Subgroup.lowerCentralSeries
          (GeneralResidueGroup
            orderThreePair order_pair_admissible) 2 := by
    rw [← general_axis_one, map_zpow]
    exact
      (Subgroup.lowerCentralSeries
        (GeneralResidueGroup
          orderThreePair order_pair_admissible) 2).zpow_mem
        hleftOne leftExponent
  have hright :
      quotientMap (generalAxis (.pairRight q) rightExponent) ∈
        Subgroup.lowerCentralSeries
          (GeneralResidueGroup
            orderThreePair order_pair_admissible) 2 := by
    rw [← general_axis_one, map_zpow]
    exact
      (Subgroup.lowerCentralSeries
        (GeneralResidueGroup
          orderThreePair order_pair_admissible) 2).zpow_mem
        hrightOne rightExponent
  change quotientMap (rankCubeTail leftSingle rightSingle) ∈
    Subgroup.lowerCentralSeries
      (GeneralResidueGroup
        orderThreePair order_pair_admissible) 2
  have htail :
      rankCubeTail leftSingle rightSingle =
        generalAxis (.pairLeft q) leftExponent *
          generalAxis (.pairRight q) rightExponent := by
    change
      rankCubeTail leftSingle rightSingle =
        GCoordi.mul
          (generalAxis (.pairLeft q) leftExponent)
          (generalAxis (.pairRight q) rightExponent)
    ext i
    · fin_cases i <;>
        simp [rankCubeTail, rankTwoCoordinates, generalAxis,
          GCoordi.mul, GCoordi.zero]
    · rcases i with ⟨i, j, hij⟩
      have hi : i = 0 := by omega
      have hj : j = 1 := by omega
      subst i
      subst j
      simp [rankCubeTail, rankTwoCoordinates, generalAxis,
        GCoordi.mul, GCoordi.zero,
        q]
    · rcases i with ⟨i, j, hij⟩
      have hi : i = 0 := by omega
      have hj : j = 1 := by omega
      subst i
      subst j
      simp [rankCubeTail, rankTwoCoordinates, generalAxis,
        GCoordi.mul, GCoordi.zero,
        q, leftExponent]
    · rcases i with ⟨i, j, hij⟩
      have hi : i = 0 := by omega
      have hj : j = 1 := by omega
      subst i
      subst j
      simp [rankCubeTail, rankTwoCoordinates, generalAxis,
        GCoordi.mul, GCoordi.zero,
        q, rightExponent]
    · rcases i with ⟨i, j, k, hij, hjk⟩
      omega
    · rcases i with ⟨i, j, k, hij, hjk⟩
      omega
  rw [htail, map_mul]
  exact
    (Subgroup.lowerCentralSeries
      (GeneralResidueGroup
        orderThreePair order_pair_admissible) 2).mul_mem hleft hright

private noncomputable def orderNonzeroProduct
    (u v : Fin 2) :
    GCoordi 2 :=
  rankTwoCoordinates (u.1 + 1) (v.1 + 1) 0 0 0

private theorem nonzero_cube_ne
    (u v : Fin 2) :
    (orderNonzeroProduct u v :
      GeneralResidueGroup
        orderThreePair order_pair_admissible) ^ 3 ≠ 1 := by
  intro h
  have hmod :
      GMEq orderThreePair
        (orderNonzeroProduct u v ^ 3)
        (GCoordi.zero 2) := by
    change
      ((orderNonzeroProduct u v ^ 3 :
        GCoordi 2) :
          GeneralResidueGroup
            orderThreePair order_pair_admissible) = 1 at h
    exact
      (generalCon
        orderThreePair order_pair_admissible).eq.mp h
  let index : Pair 2 := ⟨0, 1, by decide⟩
  have hright := hmod.pairRight index
  unfold orderNonzeroProduct at hright
  rw [rank_coordinates_cube] at hright
  fin_cases u <;> fin_cases v <;>
    norm_num [rankCubeCoordinates, rankTwoCoordinates, orderThreePair,
      generalPairModulus, index, GCoordi.zero,
      Int.ModEq, choose_one_two, choose_two_two, choose_four_two] at hright

private theorem order_nonzero_nine
    (u v : Fin 2) :
    (orderNonzeroProduct u v :
      GeneralResidueGroup
        orderThreePair order_pair_admissible) ^ 9 = 1 := by
  apply
    (generalCon
      orderThreePair order_pair_admissible).eq.mpr
  change
    GMEq orderThreePair
      (orderNonzeroProduct u v ^ 9)
      (GCoordi.zero 2)
  rw [show orderNonzeroProduct u v ^ 9 =
      (orderNonzeroProduct u v ^ 3) ^ 3 by
      rw [← pow_mul]]
  unfold orderNonzeroProduct
  rw [rank_coordinates_cube]
  unfold rankCubeCoordinates
  rw [rank_coordinates_cube]
  fin_cases u <;> fin_cases v
  all_goals
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals
    intro q
    fin_cases q <;>
      norm_num [rankCubeCoordinates, rankTwoCoordinates, orderThreePair,
        generalPairModulus, GCoordi.zero, Int.ModEq,
        choose_one_two, choose_two_two, choose_three_two, choose_four_two,
        choose_six_two, choose_twelve_two]

private theorem pair_nonzero_cube
    (u v : Fin 2) :
    (orderNonzeroProduct u v :
      GeneralResidueGroup
        orderThreePair order_pair_admissible) ^ 3 ∈
      Subgroup.lowerCentralSeries
        (GeneralResidueGroup
          orderThreePair order_pair_admissible) 2 := by
  change
    (rankTwoCoordinates (u.1 + 1) (v.1 + 1) 0 0 0 :
      GeneralResidueGroup
        orderThreePair order_pair_admissible) ^ 3 ∈
      Subgroup.lowerCentralSeries
        (GeneralResidueGroup
          orderThreePair order_pair_admissible) 2
  rw [coordinates_cube_tail]
  exact
    rank_cube_series
      (u.1 + 1) (v.1 + 1)

private theorem general_nonzero_product
    (u v : Fin 2) :
    generalGenerator (0 : Fin 2) ^ (u.1 + 1) *
        generalGenerator (1 : Fin 2) ^ (v.1 + 1) =
      orderNonzeroProduct u v := by
  rw [generalGenerator_pow, generalGenerator_pow]
  change
    GCoordi.mul
        (generalGeneratorMultiple (0 : Fin 2) (u.1 + 1))
        (generalGeneratorMultiple (1 : Fin 2) (v.1 + 1)) =
      orderNonzeroProduct u v
  ext i
  · fin_cases i <;>
      simp [orderNonzeroProduct, rankTwoCoordinates,
        generalGeneratorMultiple, GCoordi.mul]
  · rcases i with ⟨i, j, hij⟩
    have hi : i = 0 := by omega
    have hj : j = 1 := by omega
    subst i
    subst j
    simp [orderNonzeroProduct, rankTwoCoordinates,
      generalGeneratorMultiple, GCoordi.mul]
  · rcases i with ⟨i, j, hij⟩
    have hi : i = 0 := by omega
    have hj : j = 1 := by omega
    subst i
    subst j
    simp [orderNonzeroProduct, rankTwoCoordinates,
      generalGeneratorMultiple, GCoordi.mul]
  · rcases i with ⟨i, j, hij⟩
    have hi : i = 0 := by omega
    have hj : j = 1 := by omega
    subst i
    subst j
    simp [orderNonzeroProduct, rankTwoCoordinates,
      generalGeneratorMultiple, GCoordi.mul]
  · rcases i with ⟨i, j, k, hij, hjk⟩
    omega
  · rcases i with ⟨i, j, k, hij, hjk⟩
    omega

private theorem order_nonzero_product
    (u v : Fin 2) :
    nilpotentGeneralResidues
        orderThreePair order_pair_admissible
        (orderPairNonzero u v) =
      (orderNonzeroProduct u v :
        GeneralResidueGroup
          orderThreePair order_pair_admissible) := by
  let f :=
    nilpotentGeneralResidues
      orderThreePair order_pair_admissible
  have hgen (i : Fin 2) :
      f (nilpotentCyclicGenerator orderThreePair 4 i) =
        generalResidueGenerator
          orderThreePair order_pair_admissible i := by
    change
      cyclicGeneralResidues
          orderThreePair order_pair_admissible
          (cyclicGenerator orderThreePair i) =
        generalResidueGenerator
          orderThreePair order_pair_admissible i
    unfold cyclicGeneralResidues
    unfold cyclicGenerator generalResidueGenerator
    exact PresentedGroup.toGroup.of _
  change
    f (orderPairNonzero u v) =
      (orderNonzeroProduct u v :
        GeneralResidueGroup
          orderThreePair order_pair_admissible)
  rw [orderPairNonzero, map_mul, map_pow, map_pow, hgen, hgen]
  change
    ((generalGenerator (0 : Fin 2) ^ (u.1 + 1) *
        generalGenerator (1 : Fin 2) ^ (v.1 + 1) :
          GCoordi 2) :
        GeneralResidueGroup
          orderThreePair order_pair_admissible) =
      orderNonzeroProduct u v
  rw [general_nonzero_product]

/-- Struik's four sharp examples following Corollary 1: every
`aᵘbᵛ`, with `u,v ∈ {1,2}`, has order nine. -/
theorem order_pair_nonzero (u v : Fin 2) :
    orderOf (orderPairNonzero u v) = 9 := by
  let f :=
    nilpotentGeneralResidues
      orderThreePair order_pair_admissible
  have hf : Function.Injective f :=
    (nilpotent_residues_bijective
      orderThreePair (fun i => by norm_num [orderThreePair])).1
  have hmap :
      f (orderPairNonzero u v) =
        (orderNonzeroProduct u v :
          GeneralResidueGroup
            orderThreePair order_pair_admissible) := by
    exact order_nonzero_product u v
  apply orderOf_eq_prime_pow (p := 3) (n := 1)
  · intro hcube
    apply nonzero_cube_ne u v
    rw [← hmap, ← map_pow]
    have hcube' : orderPairNonzero u v ^ 3 = 1 := by
      norm_num at hcube ⊢
      exact hcube
    rw [hcube', map_one]
  · apply hf
    rw [map_pow, hmap]
    exact order_nonzero_nine u v

/-- Struik's equation (20): each of the four products has cube in `G₃`
(the second zero-based lower-central term). -/
theorem order_nonzero_cube
    (u v : Fin 2) :
    orderPairNonzero u v ^ 3 ∈
      Subgroup.lowerCentralSeries
        (NilpotentCyclicProduct orderThreePair 4) 2 := by
  let f :=
    nilpotentGeneralResidues
      orderThreePair order_pair_admissible
  have hf :
      Function.Bijective f :=
    nilpotent_residues_bijective
      orderThreePair (fun i => by norm_num [orderThreePair])
  have hxmap :
      f (orderPairNonzero u v ^ 3) ∈
        Subgroup.lowerCentralSeries
          (GeneralResidueGroup
            orderThreePair order_pair_admissible) 2 := by
    rw [map_pow, order_nonzero_product]
    exact pair_nonzero_cube u v
  rw [← central_series_surjective f hf.2 2] at hxmap
  rcases hxmap with ⟨y, hy, hyf⟩
  have hyx : y = orderPairNonzero u v ^ 3 :=
    hf.1 hyf
  simpa [hyx] using hy

/-- Struik's sharp example `ab` is the first of the four nonzero products. -/
theorem order_pair_product :
    orderOf orderPairProduct = 9 := by
  simpa [orderPairProduct, orderPairNonzero] using
    order_pair_nonzero (0 : Fin 2) (0 : Fin 2)

end P1960
end Struik
