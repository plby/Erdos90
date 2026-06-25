import Mathlib.GroupTheory.Congruence.Defs
import Towers.Group.NilpotentProducts.ExceptionalTwoLaw
import Towers.Group.NilpotentProducts.AdmissibleOrders

/-!
# Residue coordinates for Struik's equation (29)

This file formalizes the residue moduli in Theorem 4 and the assertion
following equation (29) that its multiplication law is independent of
the chosen integral representatives.
-/

namespace Struik
namespace P1960

/-- The order of the `i`th cyclic generator in Theorem 4. -/
def singleModulus {t : ℕ} (r : Fin t → ℕ) (i : Fin t) : ℕ :=
  2 ^ r i

/-- The order prescribed for `(aᵢ,aⱼ)`. -/
def exceptionalPairModulus {t : ℕ} (r : Fin t → ℕ)
    (q : Pair t) : ℕ :=
  2 ^ (r q.i + 1)

/-- The order prescribed for `(aᵢ²,aⱼ)`. -/
def leftSquareModulus {t : ℕ} (r : Fin t → ℕ)
    (q : Pair t) : ℕ :=
  2 ^ (r q.i - 1)

/-- The order prescribed for `(aᵢ,aⱼ²)`. -/
def pairSquareModulus {t : ℕ} (r : Fin t → ℕ)
    (q : Pair t) : ℕ :=
  if r q.i = r q.j then 2 ^ (r q.i - 1) else 2 ^ r q.i

/-- The common modulus of the two mixed triple coordinates. -/
def exceptionalResiduesModulus {t : ℕ} (r : Fin t → ℕ)
    (q : Triple t) : ℕ :=
  2 ^ r q.i

/-- A positive power of two is twice the preceding power. -/
theorem single_two_left
    {t : ℕ} (r : Fin t → ℕ) (hpos : ∀ i, 0 < r i) (i : Fin t) :
    singleModulus r i =
      2 * 2 ^ (r i - 1) := by
  calc
    singleModulus r i = 2 ^ (r i - 1 + 1) := by
      rw [singleModulus, Nat.sub_add_cancel (hpos i)]
    _ = 2 * 2 ^ (r i - 1) := by
      rw [Nat.pow_succ, Nat.mul_comm]

private lemma pair_two_single
    {t : ℕ} (r : Fin t → ℕ) (q : Pair t) :
    exceptionalPairModulus r q =
      2 * singleModulus r q.i := by
  simp [exceptionalPairModulus, singleModulus, Nat.pow_succ,
    Nat.mul_comm]

private lemma left_square_single
    {t : ℕ} (r : Fin t → ℕ) (q : Pair t) :
    leftSquareModulus r q ∣
      singleModulus r q.i := by
  exact pow_dvd_pow 2 (Nat.sub_le _ _)

private lemma square_dvd_single
    {t : ℕ} (r : Fin t → ℕ) (q : Pair t) :
    pairSquareModulus r q ∣
      singleModulus r q.i := by
  by_cases h : r q.i = r q.j
  · rw [pairSquareModulus, if_pos h]
    exact pow_dvd_pow 2 (Nat.sub_le _ _)
  · simp [pairSquareModulus, h, singleModulus]

private lemma single_dvd_square
    {t : ℕ} (r : Fin t → ℕ) (hpos : ∀ i, 0 < r i)
    (q : Pair t) :
    singleModulus r q.i ∣
      2 * pairSquareModulus r q := by
  by_cases h : r q.i = r q.j
  · rw [pairSquareModulus, if_pos h,
      single_two_left r hpos q.i]
  · simp [pairSquareModulus, h, singleModulus]

private lemma single_dvd
    {t : ℕ} {r : Fin t → ℕ} {i j : Fin t} (hij : r i ≤ r j) :
    singleModulus r i ∣ singleModulus r j :=
  pow_dvd_pow 2 hij

private lemma double_single_dvd
    {t : ℕ} {r : Fin t → ℕ} {i j : Fin t} (hij : r i < r j) :
    2 * singleModulus r i ∣ singleModulus r j := by
  have hleft :
      2 * singleModulus r i = 2 ^ (r i + 1) := by
    simp [singleModulus, Nat.pow_succ, Nat.mul_comm]
  rw [hleft, singleModulus]
  exact pow_dvd_pow 2 hij

/-- Coordinatewise congruence modulo the orders listed in Theorem 4. -/
structure ERMod {t : ℕ} (r : Fin t → ℕ)
    (c d : ELCoordi t) : Prop where
  single : ∀ i, c.single i ≡ d.single i
    [ZMOD (singleModulus r i : ℤ)]
  pair : ∀ q, c.pair q ≡ d.pair q
    [ZMOD (exceptionalPairModulus r q : ℤ)]
  pairLeftSquare : ∀ q, c.pairLeftSquare q ≡ d.pairLeftSquare q
    [ZMOD (leftSquareModulus r q : ℤ)]
  pairRightSquare : ∀ q, c.pairRightSquare q ≡ d.pairRightSquare q
    [ZMOD (pairSquareModulus r q : ℤ)]
  tripleFirst : ∀ q, c.tripleFirst q ≡ d.tripleFirst q
    [ZMOD (exceptionalResiduesModulus r q : ℤ)]
  tripleSecond : ∀ q, c.tripleSecond q ≡ d.tripleSecond q
    [ZMOD (exceptionalResiduesModulus r q : ℤ)]

namespace ERMod

private def pairCorrection (x y z : ℤ) : ℤ :=
  -x * y + 2 * x * Ring.choose y 2 +
    2 * y * Ring.choose x 2 + 2 * x * y * z

private def pairCorrectionPolynomial (x y z : ℤ) : ℤ :=
  x * y * (x + y + 2 * z - 3)

private lemma pair_correction_polynomial (x y z : ℤ) :
    pairCorrection x y z = pairCorrectionPolynomial x y z := by
  simp only [pairCorrection, pairCorrectionPolynomial]
  rw [show 2 * x * Ring.choose y 2 =
      x * (2 * Ring.choose y 2) by ring,
    show 2 * y * Ring.choose x 2 =
      y * (2 * Ring.choose x 2) by ring,
    two_mul_choose, two_mul_choose]
  ring

private lemma pair_first_expansion (x y z : ℤ) :
    pairCorrectionPolynomial x y z =
      y * (x * x) +
        2 * ((Ring.choose y 2 + y * z - y) * x) := by
  calc
    pairCorrectionPolynomial x y z =
        y * (x * x) + x * (y * (y - 1)) +
          2 * x * y * z - 2 * x * y := by
            simp only [pairCorrectionPolynomial]
            ring
    _ = y * (x * x) + x * (2 * Ring.choose y 2) +
          2 * x * y * z - 2 * x * y := by
            rw [two_mul_choose]
    _ = y * (x * x) +
          2 * ((Ring.choose y 2 + y * z - y) * x) := by ring

private lemma pair_second_expansion (x y z : ℤ) :
    pairCorrectionPolynomial x y z =
      x * (y * y) +
        2 * ((Ring.choose x 2 + x * z - x) * y) := by
  calc
    pairCorrectionPolynomial x y z =
        x * (y * y) + y * (x * (x - 1)) +
          2 * x * y * z - 2 * x * y := by
            simp only [pairCorrectionPolynomial]
            ring
    _ = x * (y * y) + y * (2 * Ring.choose x 2) +
          2 * x * y * z - 2 * x * y := by
            rw [two_mul_choose]
    _ = x * (y * y) +
          2 * ((Ring.choose x 2 + x * z - x) * y) := by ring

private lemma square_mod_mul
    {n x y : ℤ} (heven : ∃ m : ℤ, n = 2 * m)
    (hxy : x ≡ y [ZMOD n]) :
    x * x ≡ y * y [ZMOD (2 * n)] := by
  obtain ⟨m, rfl⟩ := heven
  rw [Int.modEq_iff_add_fac] at hxy ⊢
  obtain ⟨k, rfl⟩ := hxy
  refine ⟨k * (x + m * k), ?_⟩
  ring

private lemma choose_mod_mul
    {m x y : ℤ} (hxy : x ≡ y [ZMOD (2 * m)]) :
    Ring.choose x 2 ≡ Ring.choose y 2 [ZMOD m] := by
  have hprod := hxy.mul (hxy.sub (Int.ModEq.refl 1))
  have hdouble :
      2 * Ring.choose x 2 ≡ 2 * Ring.choose y 2
        [ZMOD (2 * m)] := by
    simpa only [two_mul_choose] using hprod
  exact Int.ModEq.mul_left_cancel' (by norm_num) hdouble

private lemma pair_mod_first
    {n x x' y z : ℤ} (heven : ∃ m : ℤ, n = 2 * m)
    (hx : x ≡ x' [ZMOD n]) :
    pairCorrectionPolynomial x y z ≡
      pairCorrectionPolynomial x' y z [ZMOD (2 * n)] := by
  have hsquare := (square_mod_mul heven hx).mul_left y
  have hlinearBase :=
    hx.mul_left (Ring.choose y 2 + y * z - y)
  have hlinear :=
    Int.ModEq.mul_left' (c := (2 : ℤ)) hlinearBase
  have hsum := hsquare.add hlinear
  rw [pair_first_expansion,
    pair_first_expansion]
  exact hsum

private lemma pair_mod_second
    {n x y y' z : ℤ} (heven : ∃ m : ℤ, n = 2 * m)
    (hy : y ≡ y' [ZMOD n]) :
    pairCorrectionPolynomial x y z ≡
      pairCorrectionPolynomial x y' z [ZMOD (2 * n)] := by
  have hsquare := (square_mod_mul heven hy).mul_left x
  have hlinearBase :=
    hy.mul_left (Ring.choose x 2 + x * z - x)
  have hlinear :=
    Int.ModEq.mul_left' (c := (2 : ℤ)) hlinearBase
  have hsum := hsquare.add hlinear
  rw [pair_second_expansion,
    pair_second_expansion]
  exact hsum

private lemma pair_mod_third
    {n x y z z' : ℤ} (hz : z ≡ z' [ZMOD n]) :
    pairCorrectionPolynomial x y z ≡
      pairCorrectionPolynomial x y z' [ZMOD (2 * n)] := by
  have hbase := hz.mul_left (x * y)
  have hdouble := Int.ModEq.mul_left' (c := (2 : ℤ)) hbase
  have hsum :=
    (Int.ModEq.refl (x * y * (x + y - 3))).add hdouble
  convert hsum using 1 <;>
    simp only [pairCorrectionPolynomial] <;>
    ring

private lemma pair_correction_mod
    {n x x' y y' z z' : ℤ} (heven : ∃ m : ℤ, n = 2 * m)
    (hx : x ≡ x' [ZMOD n]) (hy : y ≡ y' [ZMOD n])
    (hz : z ≡ z' [ZMOD n]) :
    pairCorrection x y z ≡ pairCorrection x' y' z'
      [ZMOD (2 * n)] := by
  rw [pair_correction_polynomial, pair_correction_polynomial]
  exact (pair_mod_first heven hx).trans
    ((pair_mod_second heven hy).trans
      (pair_mod_third hz))

theorem refl {t : ℕ} (r : Fin t → ℕ) (c : ELCoordi t) :
    ERMod r c c :=
  ⟨fun _ => .refl _, fun _ => .refl _, fun _ => .refl _,
    fun _ => .refl _, fun _ => .refl _, fun _ => .refl _⟩

theorem symm {t : ℕ} {r : Fin t → ℕ}
    {c d : ELCoordi t} (h : ERMod r c d) :
    ERMod r d c :=
  ⟨fun i => (h.single i).symm, fun q => (h.pair q).symm,
    fun q => (h.pairLeftSquare q).symm,
    fun q => (h.pairRightSquare q).symm,
    fun q => (h.tripleFirst q).symm,
    fun q => (h.tripleSecond q).symm⟩

theorem trans {t : ℕ} {r : Fin t → ℕ}
    {c d e : ELCoordi t}
    (hcd : ERMod r c d) (hde : ERMod r d e) :
    ERMod r c e :=
  ⟨fun i => (hcd.single i).trans (hde.single i),
    fun q => (hcd.pair q).trans (hde.pair q),
    fun q => (hcd.pairLeftSquare q).trans (hde.pairLeftSquare q),
    fun q => (hcd.pairRightSquare q).trans (hde.pairRightSquare q),
    fun q => (hcd.tripleFirst q).trans (hde.tripleFirst q),
    fun q => (hcd.tripleSecond q).trans (hde.tripleSecond q)⟩

private lemma alpha {t : ℕ} {r : Fin t → ℕ}
    (hpos : ∀ i, 0 < r i) {c d : ELCoordi t}
    (h : ERMod r c d) (q : Pair t) :
    ELCoordi.alpha c q ≡
      ELCoordi.alpha d q
        [ZMOD (singleModulus r q.i : ℤ)] := by
  have hpair :
      c.pair q ≡ d.pair q
        [ZMOD (singleModulus r q.i : ℤ)] :=
    mod_dvd_nat (h.pair q) (by
      simp [pair_two_single])
  have hleft :=
    Int.ModEq.mul_left' (c := (2 : ℤ)) (h.pairLeftSquare q)
  have hleft' :
      2 * c.pairLeftSquare q ≡ 2 * d.pairLeftSquare q
        [ZMOD (singleModulus r q.i : ℤ)] := by
    simpa [leftSquareModulus,
      single_two_left r hpos q.i] using hleft
  have hright :=
    Int.ModEq.mul_left' (c := (2 : ℤ)) (h.pairRightSquare q)
  have hright' :
      2 * c.pairRightSquare q ≡ 2 * d.pairRightSquare q
        [ZMOD (singleModulus r q.i : ℤ)] := by
    exact hright.of_dvd (by
      exact_mod_cast single_dvd_square r hpos q)
  simpa [ELCoordi.alpha, add_assoc] using
    hpair.add (hleft'.add hright')

/-- Struik's multiplication table (29) is independent of all choices of
integral representatives for the residues in Theorem 4. -/
theorem mul {t : ℕ} {r : Fin t → ℕ}
    (hpos : ∀ i, 0 < r i) (hmono : Monotone r)
    {c c' d d' : ELCoordi t}
    (hc : ERMod r c c') (hd : ERMod r d d') :
    ERMod r
      (ELCoordi.mul c d)
      (ELCoordi.mul c' d') := by
  refine ⟨fun i => (hc.single i).add (hd.single i), ?_, ?_, ?_, ?_, ?_⟩
  · intro q
    have hri_rj : r q.i ≤ r q.j := hmono q.lt.le
    have hcj :
        c.single q.j ≡ c'.single q.j
          [ZMOD (singleModulus r q.i : ℤ)] :=
      mod_dvd_nat (hc.single q.j)
        (single_dvd hri_rj)
    have hdi := hd.single q.i
    have hdj :
        d.single q.j ≡ d'.single q.j
          [ZMOD (singleModulus r q.i : ℤ)] :=
      mod_dvd_nat (hd.single q.j)
        (single_dvd hri_rj)
    have halpha := alpha hpos hc q
    have hAlphaDi :
        2 * ELCoordi.alpha c q * d.single q.i ≡
          2 * ELCoordi.alpha c' q * d'.single q.i
            [ZMOD (exceptionalPairModulus r q : ℤ)] := by
      have h := Int.ModEq.mul_left' (c := (2 : ℤ)) (halpha.mul hdi)
      simpa [pair_two_single, mul_assoc] using h
    have hAlphaDj :
        2 * ELCoordi.alpha c q * d.single q.j ≡
          2 * ELCoordi.alpha c' q * d'.single q.j
            [ZMOD (exceptionalPairModulus r q : ℤ)] := by
      have h := Int.ModEq.mul_left' (c := (2 : ℤ)) (halpha.mul hdj)
      simpa [pair_two_single, mul_assoc] using h
    have heven :
        ∃ m : ℤ, (singleModulus r q.i : ℤ) = 2 * m :=
      ⟨(2 ^ (r q.i - 1) : ℕ), by
        exact_mod_cast single_two_left r hpos q.i⟩
    have hcorrection :
        pairCorrection (c.single q.j) (d.single q.i) (d.single q.j) ≡
          pairCorrection (c'.single q.j) (d'.single q.i) (d'.single q.j)
            [ZMOD (exceptionalPairModulus r q : ℤ)] := by
      have h := pair_correction_mod heven hcj hdi hdj
      simpa [pair_two_single] using h
    have hresult :=
      ((((hc.pair q).add (hd.pair q)).sub hAlphaDi).sub hAlphaDj).add
        hcorrection
    simpa [ELCoordi.mul, pairCorrection, add_assoc,
      sub_eq_add_neg] using hresult
  · intro q
    have hri_rj : r q.i ≤ r q.j := hmono q.lt.le
    have hleft_dvd_single :=
      left_square_single r q
    have halpha :
        ELCoordi.alpha c q ≡
          ELCoordi.alpha c' q
            [ZMOD (leftSquareModulus r q : ℤ)] :=
      mod_dvd_nat (alpha hpos hc q) hleft_dvd_single
    have hdi :
        d.single q.i ≡ d'.single q.i
          [ZMOD (leftSquareModulus r q : ℤ)] :=
      mod_dvd_nat (hd.single q.i) hleft_dvd_single
    have hcj :
        c.single q.j ≡ c'.single q.j
          [ZMOD (leftSquareModulus r q : ℤ)] :=
      mod_dvd_nat (hc.single q.j)
        (hleft_dvd_single.trans
          (single_dvd hri_rj))
    have hchoose :
        Ring.choose (d.single q.i) 2 ≡ Ring.choose (d'.single q.i) 2
          [ZMOD (leftSquareModulus r q : ℤ)] := by
      apply choose_mod_mul
      simpa [leftSquareModulus,
        single_two_left r hpos q.i] using
          (hd.single q.i)
    exact (((hc.pairLeftSquare q).add (hd.pairLeftSquare q)).add
      (halpha.mul hdi)).sub (hcj.mul hchoose)
  · intro q
    have hri_rj : r q.i ≤ r q.j := hmono q.lt.le
    by_cases heq : r q.i = r q.j
    · have hright :
          pairSquareModulus r q =
            leftSquareModulus r q := by
        simp [pairSquareModulus,
          leftSquareModulus, heq]
      have hleft_dvd_single :=
        left_square_single r q
      have hdi :
          d.single q.i ≡ d'.single q.i
            [ZMOD (pairSquareModulus r q : ℤ)] := by
        rw [hright]
        exact mod_dvd_nat (hd.single q.i) hleft_dvd_single
      have hcj :
          c.single q.j ≡ c'.single q.j
            [ZMOD (pairSquareModulus r q : ℤ)] := by
        rw [hright]
        exact mod_dvd_nat (hc.single q.j)
          (hleft_dvd_single.trans
            (single_dvd hri_rj))
      have hdj :
          d.single q.j ≡ d'.single q.j
            [ZMOD (pairSquareModulus r q : ℤ)] := by
        rw [hright]
        exact mod_dvd_nat (hd.single q.j)
          (hleft_dvd_single.trans
            (single_dvd hri_rj))
      have halpha :
          ELCoordi.alpha c q ≡
            ELCoordi.alpha c' q
              [ZMOD (pairSquareModulus r q : ℤ)] := by
        rw [hright]
        exact mod_dvd_nat (alpha hpos hc q) hleft_dvd_single
      have hchoose :
          Ring.choose (c.single q.j) 2 ≡ Ring.choose (c'.single q.j) 2
            [ZMOD (pairSquareModulus r q : ℤ)] := by
        rw [hright]
        apply choose_mod_mul
        have hcjSingle :
            c.single q.j ≡ c'.single q.j
              [ZMOD (singleModulus r q.i : ℤ)] :=
          mod_dvd_nat (hc.single q.j)
            (single_dvd hri_rj)
        simpa [leftSquareModulus,
          single_two_left r hpos q.i] using hcjSingle
      exact ((((hc.pairRightSquare q).add
          (hd.pairRightSquare q)).sub (hdi.mul hchoose)).add
          (halpha.mul hdj)).sub ((hcj.mul hdi).mul hdj)
    · have hlt : r q.i < r q.j := lt_of_le_of_ne hri_rj heq
      have hright :
          pairSquareModulus r q =
            singleModulus r q.i := by
        simp [pairSquareModulus,
          singleModulus, heq]
      have hcj :
          c.single q.j ≡ c'.single q.j
            [ZMOD (singleModulus r q.i : ℤ)] :=
        mod_dvd_nat (hc.single q.j)
          (single_dvd hri_rj)
      have hdj :
          d.single q.j ≡ d'.single q.j
            [ZMOD (singleModulus r q.i : ℤ)] :=
        mod_dvd_nat (hd.single q.j)
          (single_dvd hri_rj)
      have hchoose :
          Ring.choose (c.single q.j) 2 ≡ Ring.choose (c'.single q.j) 2
            [ZMOD (singleModulus r q.i : ℤ)] := by
        apply choose_mod_mul
        exact mod_dvd_nat (hc.single q.j)
          (double_single_dvd hlt)
      have hbase :
          c.pairRightSquare q + d.pairRightSquare q ≡
            c'.pairRightSquare q + d'.pairRightSquare q
              [ZMOD (singleModulus r q.i : ℤ)] := by
        simpa [hright] using
          (hc.pairRightSquare q).add (hd.pairRightSquare q)
      have hresult :=
        (((hbase.sub ((hd.single q.i).mul hchoose)).add
          ((alpha hpos hc q).mul hdj)).sub
            ((hcj.mul (hd.single q.i)).mul hdj))
      simpa [ELCoordi.mul,
        pairSquareModulus, heq] using hresult
  · intro q
    have hri_rj : r q.i ≤ r q.j := hmono q.lt_ij.le
    have hrj_rk : r q.j ≤ r q.k := hmono q.lt_jk.le
    have hri_rk : r q.i ≤ r q.k := hri_rj.trans hrj_rk
    have hcj := mod_dvd_nat (hc.single q.j)
      (single_dvd hri_rj)
    have hck := mod_dvd_nat (hc.single q.k)
      (single_dvd hri_rk)
    have hdi := hd.single q.i
    have hdj := mod_dvd_nat (hd.single q.j)
      (single_dvd hri_rj)
    have hdk := mod_dvd_nat (hd.single q.k)
      (single_dvd hri_rk)
    have halphaIk := alpha hpos hc q.ik
    have halphaIj := alpha hpos hc q.ij
    have h0 := (hc.tripleFirst q).add (hd.tripleFirst q)
    have h1 := h0.add (halphaIk.mul hdj)
    have h2 := h1.sub ((hck.mul hdi).mul hdj)
    have h3 := h2.sub ((hdi.mul hcj).mul hck)
    have h4 := h3.add (halphaIj.mul hdk)
    exact h4.sub ((hcj.mul hdi).mul hdk)
  · intro q
    have hri_rj : r q.i ≤ r q.j := hmono q.lt_ij.le
    have hri_rk : r q.i ≤ r q.k :=
      hri_rj.trans (hmono q.lt_jk.le)
    have hck := mod_dvd_nat (hc.single q.k)
      (single_dvd hri_rk)
    have hdi := hd.single q.i
    have hdj := mod_dvd_nat (hd.single q.j)
      (single_dvd hri_rj)
    have halphaJk := mod_dvd_nat (alpha hpos hc q.jk)
      (single_dvd hri_rj)
    have halphaIk := alpha hpos hc q.ik
    have h0 := (hc.tripleSecond q).add (hd.tripleSecond q)
    have h1 := h0.add (halphaJk.mul hdi)
    have h2 := h1.add (halphaIk.mul hdj)
    exact h2.sub ((hck.mul hdi).mul hdj)

end ERMod

/-- The multiplicative congruence determined by Theorem 4's coordinate
moduli. -/
def exceptionalResiduesCon {t : ℕ} (r : Fin t → ℕ)
    (hpos : ∀ i, 0 < r i) (hmono : Monotone r) :
    Con (ELCoordi t) where
  r := ERMod r
  iseqv :=
    ⟨ERMod.refl r, ERMod.symm,
      ERMod.trans⟩
  mul' := ERMod.mul hpos hmono

/-- The residue-coordinate group constructed after equation (29). -/
abbrev ExceptionalResiduesResidue {t : ℕ} (r : Fin t → ℕ)
    (hpos : ∀ i, 0 < r i) (hmono : Monotone r) :=
  (exceptionalResiduesCon r hpos hmono).Quotient

/-- The dependent product of the residue sets appearing in Theorem 4. -/
@[ext]
structure ExceptionalTwoResidues {t : ℕ} (r : Fin t → ℕ) where
  single : ∀ i : Fin t, ZMod (singleModulus r i)
  pair : ∀ q : Pair t, ZMod (exceptionalPairModulus r q)
  pairLeftSquare :
    ∀ q : Pair t, ZMod (leftSquareModulus r q)
  pairRightSquare :
    ∀ q : Pair t, ZMod (pairSquareModulus r q)
  tripleFirst :
    ∀ q : Triple t, ZMod (exceptionalResiduesModulus r q)
  tripleSecond :
    ∀ q : Triple t, ZMod (exceptionalResiduesModulus r q)

/-- Reduce integral equation-(29) coordinates modulo the orders in
Theorem 4. -/
def exceptionalResiduesCast {t : ℕ} (r : Fin t → ℕ)
    (c : ELCoordi t) : ExceptionalTwoResidues r where
  single i := c.single i
  pair q := c.pair q
  pairLeftSquare q := c.pairLeftSquare q
  pairRightSquare q := c.pairRightSquare q
  tripleFirst q := c.tripleFirst q
  tripleSecond q := c.tripleSecond q

theorem exceptional_residues_cast
    {t : ℕ} {r : Fin t → ℕ} {c d : ELCoordi t} :
    ERMod r c d ↔
      exceptionalResiduesCast r c = exceptionalResiduesCast r d := by
  constructor
  · intro h
    ext i <;>
      apply (ZMod.intCast_eq_intCast_iff _ _ _).2 <;>
      first
      | exact h.single i
      | exact h.pair i
      | exact h.pairLeftSquare i
      | exact h.pairRightSquare i
      | exact h.tripleFirst i
      | exact h.tripleSecond i
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro i
      exact (ZMod.intCast_eq_intCast_iff _ _ _).1
        (congrFun (congrArg ExceptionalTwoResidues.single h) i)
    · intro q
      exact (ZMod.intCast_eq_intCast_iff _ _ _).1
        (congrFun (congrArg ExceptionalTwoResidues.pair h) q)
    · intro q
      exact (ZMod.intCast_eq_intCast_iff _ _ _).1
        (congrFun (congrArg ExceptionalTwoResidues.pairLeftSquare h) q)
    · intro q
      exact (ZMod.intCast_eq_intCast_iff _ _ _).1
        (congrFun (congrArg ExceptionalTwoResidues.pairRightSquare h) q)
    · intro q
      exact (ZMod.intCast_eq_intCast_iff _ _ _).1
        (congrFun (congrArg ExceptionalTwoResidues.tripleFirst h) q)
    · intro q
      exact (ZMod.intCast_eq_intCast_iff _ _ _).1
        (congrFun (congrArg ExceptionalTwoResidues.tripleSecond h) q)

private noncomputable def exceptionalResiduesRepresentative
    {n : ℕ} (x : ZMod n) : ℤ :=
  Classical.choose (ZMod.intCast_surjective x)

@[simp] private theorem exceptional_residue_representative
    {n : ℕ} (x : ZMod n) :
    (exceptionalResiduesRepresentative x : ZMod n) = x :=
  Classical.choose_spec (ZMod.intCast_surjective x)

private theorem exceptional_residues_residue
    {t : ℕ} (r : Fin t → ℕ) :
    Function.Surjective (exceptionalResiduesCast r) := by
  intro c
  refine ⟨{
    single := fun i => exceptionalResiduesRepresentative (c.single i)
    pair := fun q => exceptionalResiduesRepresentative (c.pair q)
    pairLeftSquare := fun q =>
      exceptionalResiduesRepresentative (c.pairLeftSquare q)
    pairRightSquare := fun q =>
      exceptionalResiduesRepresentative (c.pairRightSquare q)
    tripleFirst := fun q =>
      exceptionalResiduesRepresentative (c.tripleFirst q)
    tripleSecond := fun q =>
      exceptionalResiduesRepresentative (c.tripleSecond q) }, ?_⟩
  ext <;> simp [exceptionalResiduesCast]

/-- Forget the quotient representative and retain its residue
coordinates. -/
noncomputable def exceptionalResiduesResidue
    {t : ℕ} (r : Fin t → ℕ)
    (hpos : ∀ i, 0 < r i) (hmono : Monotone r) :
    ExceptionalResiduesResidue r hpos hmono → ExceptionalTwoResidues r :=
  fun q =>
    Con.liftOn q (exceptionalResiduesCast r) fun _ _ h =>
      exceptional_residues_cast.mp h

private theorem exceptional_residues_bijective
    {t : ℕ} (r : Fin t → ℕ)
    (hpos : ∀ i, 0 < r i) (hmono : Monotone r) :
    Function.Bijective
      (exceptionalResiduesResidue r hpos hmono) := by
  constructor
  · intro q s hqs
    induction q using Con.induction_on with
    | _ c =>
      induction s using Con.induction_on with
      | _ d =>
        apply (exceptionalResiduesCon r hpos hmono).eq.mpr
        exact exceptional_residues_cast.mpr hqs
  · intro c
    obtain ⟨d, rfl⟩ := exceptional_residues_residue r c
    exact ⟨(d : ExceptionalResiduesResidue r hpos hmono), rfl⟩

/-- The quotient coordinate group has precisely the residue coordinates
listed in Theorem 4. -/
noncomputable def exceptionalTwoResidues
    {t : ℕ} (r : Fin t → ℕ)
    (hpos : ∀ i, 0 < r i) (hmono : Monotone r) :
    ExceptionalResiduesResidue r hpos hmono ≃ ExceptionalTwoResidues r :=
  Equiv.ofBijective
    (exceptionalResiduesResidue r hpos hmono)
    (exceptional_residues_bijective r hpos hmono)

end P1960
end Struik
