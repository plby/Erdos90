import Mathlib.FieldTheory.KummerPolynomial
import Mathlib.NumberTheory.Padics.Hensel
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Polynomial.Eisenstein.Basic


/-!
# Milne, Chapter 7, Exercise 7-8(b)

We give a slightly simpler witness than the one printed in Milne's solutions:

`F(X) = X^6 + 10 X^4 + 6 X^2 + 10`.

It is Eisenstein at `2`, hence irreducible over `ℤ`.  Writing
`F(X) = H(X^2)` with `H(Y) = Y^3 + 10 Y^2 + 6 Y + 10`, the reduction of
`H` modulo `5` has the three simple roots `0`, `2`, and `3`.  Hensel's lemma
lifts them to roots `a₀`, `a₂`, and `a₃` in `ℤ_[5]`, yielding the three
quadratic factors `X^2 - aᵢ` over `ℚ_[5]`.  The factors are irreducible:
`a₂` and `a₃` have nonsquare residues, while `a₀` has odd valuation.
-/

namespace Submission.NumberTheory.Milne

open IsLocalRing Polynomial

noncomputable section

local instance fivePrimeFact_8b : Fact (Nat.Prime 5) := ⟨by decide⟩

/-- The integer sextic used for Exercise 7-8(b). -/
def newtonCounterexamplePolynomial : ℤ[X] :=
  X ^ 6 + C 10 * X ^ 4 + C 6 * X ^ 2 + C 10

/-- The auxiliary cubic `H` satisfying `F(X) = H(X^2)`. -/
private def newtonCounterexampleAuxiliary : ℤ_[5][X] :=
  X ^ 3 + C 10 * X ^ 2 + C 6 * X + C 10

theorem monic_nat_degree :
    newtonCounterexamplePolynomial.Monic ∧ newtonCounterexamplePolynomial.natDegree = 6 := by
  constructor
  · rw [show newtonCounterexamplePolynomial =
        X ^ 6 + (C 10 * X ^ 4 + C 6 * X ^ 2 + C 10) by
      simp only [newtonCounterexamplePolynomial]
      ring]
    apply monic_X_pow_add
    compute_degree
    norm_num
  · dsimp [newtonCounterexamplePolynomial]
    compute_degree
    all_goals norm_num

private theorem Polynomial_eisenstein_two :
    newtonCounterexamplePolynomial.IsEisensteinAt (Ideal.span {(2 : ℤ)}) := by
  have hp : (Ideal.span {(2 : ℤ)}).IsPrime :=
    (Ideal.span_singleton_prime (by norm_num : (2 : ℤ) ≠ 0)).mpr
      (Nat.prime_iff_prime_int.mp Nat.prime_two)
  refine monic_nat_degree.1.isEisensteinAt_of_mem_of_notMem
    hp.ne_top ?_ ?_
  · intro i hi
    rw [monic_nat_degree.2] at hi
    interval_cases i <;>
      norm_num [newtonCounterexamplePolynomial, coeff_add, coeff_mul, coeff_X_pow,
        coeff_C, Ideal.mem_span_singleton]
  · norm_num [newtonCounterexamplePolynomial, coeff_add, coeff_mul, coeff_X_pow, coeff_C,
      Ideal.span_singleton_pow, Ideal.mem_span_singleton]

/-- The displayed sextic is monic and irreducible in `ℤ[X]`. -/
theorem newton_counterexample_irreducible :
    Irreducible newtonCounterexamplePolynomial := by
  exact Polynomial_eisenstein_two.irreducible
    ((Ideal.span_singleton_prime (by norm_num : (2 : ℤ) ≠ 0)).mpr
      (Nat.prime_iff_prime_int.mp Nat.prime_two))
    monic_nat_degree.1.isPrimitive
    (by rw [monic_nat_degree.2]; norm_num)

private theorem Auxiliary_monic : newtonCounterexampleAuxiliary.Monic := by
  rw [show newtonCounterexampleAuxiliary =
      X ^ 3 + (C 10 * X ^ 2 + C 6 * X + C 10) by
    simp only [newtonCounterexampleAuxiliary]
    ring]
  apply monic_X_pow_add
  compute_degree
  norm_num

private theorem Auxiliary_natDegree :
    newtonCounterexampleAuxiliary.natDegree = 3 := by
  dsimp [newtonCounterexampleAuxiliary]
  compute_degree
  all_goals norm_num

@[simp]
private theorem z_mod_cast (n : ℕ) :
    PadicInt.toZMod (n : ℤ_[5]) = (n : ZMod 5) := by
  exact map_natCast PadicInt.toZMod n

private theorem Auxiliary_exists_root
    (r : ℤ_[5])
    (hr : ‖newtonCounterexampleAuxiliary.aeval r‖ <
      ‖newtonCounterexampleAuxiliary.derivative.aeval r‖ ^ 2) :
    ∃ a : ℤ_[5], newtonCounterexampleAuxiliary.IsRoot a ∧
      PadicInt.toZMod a = PadicInt.toZMod r := by
  obtain ⟨a, ha, har, -⟩ := hensels_lemma hr
  refine ⟨a, ?_, ?_⟩
  · simpa [IsRoot.def] using ha
  · rw [← sub_eq_zero, ← map_sub, ← RingHom.mem_ker, PadicInt.ker_toZMod,
      PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton,
      ← PadicInt.norm_lt_one_iff_dvd]
    exact har.trans_le (PadicInt.norm_le_one _)

private theorem Auxiliary_roots :
    ∃ a0 a2 a3 : ℤ_[5],
      newtonCounterexampleAuxiliary.IsRoot a0 ∧ PadicInt.toZMod a0 = 0 ∧
      newtonCounterexampleAuxiliary.IsRoot a2 ∧ PadicInt.toZMod a2 = 2 ∧
      newtonCounterexampleAuxiliary.IsRoot a3 ∧ PadicInt.toZMod a3 = 3 := by
  have h0 : ‖newtonCounterexampleAuxiliary.aeval (0 : ℤ_[5])‖ <
      ‖newtonCounterexampleAuxiliary.derivative.aeval (0 : ℤ_[5])‖ ^ 2 := by
    norm_num [newtonCounterexampleAuxiliary]
    have h6 : ‖(6 : ℤ_[5])‖ = 1 := PadicInt.norm_natCast_eq_one_iff.mpr (by decide)
    have h10 : ‖(10 : ℤ_[5])‖ < 1 := PadicInt.norm_natCast_lt_one_iff.mpr (by decide)
    simpa [h6] using h10
  have h2 : ‖newtonCounterexampleAuxiliary.aeval (2 : ℤ_[5])‖ <
      ‖newtonCounterexampleAuxiliary.derivative.aeval (2 : ℤ_[5])‖ ^ 2 := by
    norm_num [newtonCounterexampleAuxiliary]
    have h58 : ‖(58 : ℤ_[5])‖ = 1 := PadicInt.norm_natCast_eq_one_iff.mpr (by decide)
    have h70 : ‖(70 : ℤ_[5])‖ < 1 := PadicInt.norm_natCast_lt_one_iff.mpr (by decide)
    simpa [h58] using h70
  have h3 : ‖newtonCounterexampleAuxiliary.aeval (3 : ℤ_[5])‖ <
      ‖newtonCounterexampleAuxiliary.derivative.aeval (3 : ℤ_[5])‖ ^ 2 := by
    norm_num [newtonCounterexampleAuxiliary]
    have h93 : ‖(93 : ℤ_[5])‖ = 1 := PadicInt.norm_natCast_eq_one_iff.mpr (by decide)
    have h145 : ‖(145 : ℤ_[5])‖ < 1 := PadicInt.norm_natCast_lt_one_iff.mpr (by decide)
    simpa [h93] using h145
  obtain ⟨a0, ha0, ha0map⟩ := Auxiliary_exists_root 0 h0
  obtain ⟨a2, ha2, ha2map⟩ := Auxiliary_exists_root 2 h2
  obtain ⟨a3, ha3, ha3map⟩ := Auxiliary_exists_root 3 h3
  have ha0map' : PadicInt.toZMod a0 = 0 := by
    exact ha0map.trans (map_natCast PadicInt.toZMod 0)
  have ha2map' : PadicInt.toZMod a2 = 2 := by
    exact ha2map.trans (map_natCast PadicInt.toZMod 2)
  have ha3map' : PadicInt.toZMod a3 = 3 := by
    exact ha3map.trans (map_natCast PadicInt.toZMod 3)
  exact ⟨a0, a2, a3, ha0, ha0map', ha2, ha2map', ha3, ha3map'⟩

private theorem padic_int_z
    {a : ℤ_[5]} (ha : PadicInt.toZMod a ≠ 0) : IsUnit a := by
  apply (IsLocalRing.residue_ne_zero_iff_isUnit a).mp
  intro hres
  apply ha
  rw [PadicInt.toZMod_eq_residueField_comp_residue]
  simp [hres]

private theorem padic_valuation_unit
    {a : ℤ_[5]} (ha : IsUnit a) : a.valuation = 0 := by
  obtain ⟨b, hb⟩ := isUnit_iff_dvd_one.mp ha
  have hb0 : b ≠ 0 := by
    intro hbzero
    subst b
    simp at hb
  have hval := PadicInt.valuation_mul ha.ne_zero hb0
  rw [← hb, PadicInt.valuation_one] at hval
  omega

private theorem padic_z_mod
    {a : ℤ_[5]} (ha : IsUnit a)
    (hnonsquare : ∀ x : ZMod 5, x ^ 2 ≠ PadicInt.toZMod a) :
    ∀ b : ℚ_[5], b ^ 2 ≠ (a : ℚ_[5]) := by
  intro b hb
  have hanorm : ‖(a : ℚ_[5])‖ = 1 := by
    simpa using (PadicInt.isUnit_iff.mp ha)
  have hbnormsq : ‖b‖ ^ 2 = 1 := by
    rw [← norm_pow, hb, hanorm]
  have hbnorm : ‖b‖ = 1 := by
    nlinarith [norm_nonneg b]
  let bInt : ℤ_[5] := ⟨b, hbnorm.le⟩
  have hbInt : bInt ^ 2 = a := by
    apply PadicInt.ext
    simpa [bInt] using hb
  have hmap := congrArg PadicInt.toZMod hbInt
  exact hnonsquare (PadicInt.toZMod bInt) (by simpa using hmap)

private theorem root_zero_valuation
    {a0 : ℤ_[5]} (ha0 : newtonCounterexampleAuxiliary.IsRoot a0)
    (ha0map : PadicInt.toZMod a0 = 0) : a0.valuation = 1 := by
  let u : ℤ_[5] := a0 ^ 2 + 10 * a0 + 6
  have humap : PadicInt.toZMod u = 1 := by
    have h10 : PadicInt.toZMod (10 : ℤ_[5]) = (10 : ZMod 5) := by
      change PadicInt.toZMod ((10 : ℕ) : ℤ_[5]) = (10 : ZMod 5)
      exact map_natCast PadicInt.toZMod 10
    have h6 : PadicInt.toZMod (6 : ℤ_[5]) = (6 : ZMod 5) := by
      change PadicInt.toZMod ((6 : ℕ) : ℤ_[5]) = (6 : ZMod 5)
      exact map_natCast PadicInt.toZMod 6
    dsimp [u]
    rw [map_add, map_add, map_pow, map_mul, ha0map, h10, h6]
    change (6 : ZMod 5) = 1
    decide
  have hu : IsUnit u := padic_int_z (by simp [humap])
  have huval : u.valuation = 0 := padic_valuation_unit hu
  have ha0ne : a0 ≠ 0 := by
    intro ha0zero
    subst a0
    norm_num [newtonCounterexampleAuxiliary, IsRoot.def] at ha0
  have hfactor : a0 * u = -10 := by
    have hroot := ha0
    rw [IsRoot.def] at hroot
    dsimp [newtonCounterexampleAuxiliary] at hroot
    simp only [eval_add, eval_pow, eval_X, eval_mul, eval_C] at hroot
    dsimp [u]
    linear_combination hroot
  have hten : ((10 : ℤ_[5])).valuation = 1 := by
    rw [show (10 : ℤ_[5]) = 5 * 2 by norm_num,
      PadicInt.valuation_mul (by norm_num) (by norm_num)]
    rw [show (5 : ℤ_[5]).valuation = 1 from PadicInt.valuation_p]
    have htwo : IsUnit (2 : ℤ_[5]) := by
      rw [PadicInt.isUnit_iff]
      exact PadicInt.norm_natCast_eq_one_iff.mpr (by decide)
    rw [padic_valuation_unit htwo]
  have hval := PadicInt.valuation_mul ha0ne hu.ne_zero
  rw [hfactor, huval] at hval
  have hneg : ((-10 : ℤ_[5])).valuation = 1 := by
    rw [show (-10 : ℤ_[5]) = (-1) * 10 by ring,
      PadicInt.valuation_mul (by norm_num) (by norm_num), hten]
    rw [padic_valuation_unit
      isUnit_neg_one]
  rw [hneg] at hval
  omega

/-- Milne, Exercise 7-8(b): there is a monic irreducible sextic over `ℤ`
which factors over `ℚ_[5]` as a product of three irreducible quadratics. -/
theorem newtonCounterexample :
    ∃ f : ℤ[X],
      f.Monic ∧ Irreducible f ∧ f.natDegree = 6 ∧
      ∃ q0 q2 q3 : ℚ_[5][X],
        q0.Monic ∧ q0.natDegree = 2 ∧ Irreducible q0 ∧
        q2.Monic ∧ q2.natDegree = 2 ∧ Irreducible q2 ∧
        q3.Monic ∧ q3.natDegree = 2 ∧ Irreducible q3 ∧
        f.map (Int.castRingHom ℚ_[5]) = q0 * q2 * q3 := by
  obtain ⟨a0, a2, a3, ha0root, ha0map, ha2root, ha2map, ha3root, ha3map⟩ :=
    Auxiliary_roots
  let q0 : ℚ_[5][X] := X ^ 2 - C (a0 : ℚ_[5])
  let q2 : ℚ_[5][X] := X ^ 2 - C (a2 : ℚ_[5])
  let q3 : ℚ_[5][X] := X ^ 2 - C (a3 : ℚ_[5])
  have ha02 : (a0 : ℚ_[5]) ≠ (a2 : ℚ_[5]) := by
    intro h
    have hz := congrArg PadicInt.toZMod (PadicInt.ext h)
    exact (by decide : (0 : ZMod 5) ≠ 2) (by simpa [ha0map, ha2map] using hz)
  have ha03 : (a0 : ℚ_[5]) ≠ (a3 : ℚ_[5]) := by
    intro h
    have hz := congrArg PadicInt.toZMod (PadicInt.ext h)
    exact (by decide : (0 : ZMod 5) ≠ 3) (by simpa [ha0map, ha3map] using hz)
  have ha23 : (a2 : ℚ_[5]) ≠ (a3 : ℚ_[5]) := by
    intro h
    have hz := congrArg PadicInt.toZMod (PadicInt.ext h)
    exact (by decide : (2 : ZMod 5) ≠ 3) (by simpa [ha2map, ha3map] using hz)
  let H : ℚ_[5][X] := newtonCounterexampleAuxiliary.map PadicInt.Coe.ringHom
  have hHmonic : H.Monic := Auxiliary_monic.map _
  have hHdegree : H.natDegree = 3 := by
    exact (Auxiliary_monic.natDegree_map _).trans
      Auxiliary_natDegree
  have ha0rootQ : H.IsRoot (a0 : ℚ_[5]) := ha0root.map
  have ha2rootQ : H.IsRoot (a2 : ℚ_[5]) := ha2root.map
  have ha3rootQ : H.IsRoot (a3 : ℚ_[5]) := ha3root.map
  have hcop02 : IsCoprime (X - C (a0 : ℚ_[5])) (X - C (a2 : ℚ_[5])) :=
    isCoprime_X_sub_C_of_isUnit_sub (sub_ne_zero.mpr ha02).isUnit
  have hcop03 : IsCoprime (X - C (a0 : ℚ_[5])) (X - C (a3 : ℚ_[5])) :=
    isCoprime_X_sub_C_of_isUnit_sub (sub_ne_zero.mpr ha03).isUnit
  have hcop23 : IsCoprime (X - C (a2 : ℚ_[5])) (X - C (a3 : ℚ_[5])) :=
    isCoprime_X_sub_C_of_isUnit_sub (sub_ne_zero.mpr ha23).isUnit
  have hlinearDvd :
      (X - C (a0 : ℚ_[5])) *
          ((X - C (a2 : ℚ_[5])) * (X - C (a3 : ℚ_[5]))) ∣ H := by
    have h0dvd : X - C (a0 : ℚ_[5]) ∣ H := (dvd_iff_isRoot).2 ha0rootQ
    have h2dvd : X - C (a2 : ℚ_[5]) ∣ H := (dvd_iff_isRoot).2 ha2rootQ
    have h3dvd : X - C (a3 : ℚ_[5]) ∣ H := (dvd_iff_isRoot).2 ha3rootQ
    exact (hcop02.mul_right hcop03).mul_dvd h0dvd
      (hcop23.mul_dvd h2dvd h3dvd)
  have hHfactor :
      H = (X - C (a0 : ℚ_[5])) *
        ((X - C (a2 : ℚ_[5])) * (X - C (a3 : ℚ_[5]))) := by
    have hprodDegree :
        ((X - C (a0 : ℚ_[5])) *
          ((X - C (a2 : ℚ_[5])) * (X - C (a3 : ℚ_[5])))).natDegree = 3 := by
      compute_degree
      all_goals norm_num
    apply eq_of_monic_of_dvd_of_natDegree_le
      ((monic_X_sub_C _).mul ((monic_X_sub_C _).mul (monic_X_sub_C _)))
      hHmonic hlinearDvd
    rw [hHdegree, hprodDegree]
  have ha2unit : IsUnit a2 :=
    padic_int_z (by
      rw [ha2map]
      decide)
  have ha3unit : IsUnit a3 :=
    padic_int_z (by
      rw [ha3map]
      decide)
  have ha2nonsquare : ∀ b : ℚ_[5], b ^ 2 ≠ (a2 : ℚ_[5]) := by
    apply padic_z_mod ha2unit
    intro x
    rw [ha2map]
    fin_cases x <;> decide
  have ha3nonsquare : ∀ b : ℚ_[5], b ^ 2 ≠ (a3 : ℚ_[5]) := by
    apply padic_z_mod ha3unit
    intro x
    rw [ha3map]
    fin_cases x <;> decide
  have ha0val : a0.valuation = 1 :=
    root_zero_valuation ha0root ha0map
  have ha0nonsquare : ∀ b : ℚ_[5], b ^ 2 ≠ (a0 : ℚ_[5]) := by
    intro b hb
    have hbval := congrArg Padic.valuation hb
    simp [PadicInt.valuation_coe, ha0val] at hbval
    omega
  have hq0irr : Irreducible q0 := by
    exact (X_pow_sub_C_irreducible_iff_of_prime Nat.prime_two).2 ha0nonsquare
  have hq2irr : Irreducible q2 := by
    exact (X_pow_sub_C_irreducible_iff_of_prime Nat.prime_two).2 ha2nonsquare
  have hq3irr : Irreducible q3 := by
    exact (X_pow_sub_C_irreducible_iff_of_prime Nat.prime_two).2 ha3nonsquare
  have hfactor : newtonCounterexamplePolynomial.map (Int.castRingHom ℚ_[5]) = q0 * q2 * q3 := by
    have hcomp : newtonCounterexamplePolynomial.map (Int.castRingHom ℚ_[5]) = H.comp (X ^ 2) := by
      simp only [newtonCounterexamplePolynomial, eq_intCast, Int.cast_ofNat, Polynomial.map_add,
        Polynomial.map_pow,
        map_X, Polynomial.map_mul, Polynomial.map_ofNat, newtonCounterexampleAuxiliary, map_C,
          PadicInt.Coe.ringHom_apply,
        add_comp, pow_comp, X_comp, mul_comp, C_comp, H]
      have h6 : ((6 : ℤ_[5]) : ℚ_[5]) = 6 := rfl
      have h10 : ((10 : ℤ_[5]) : ℚ_[5]) = 10 := rfl
      rw [h6, h10]
      simp only [C_ofNat]
      ring
    rw [hcomp, hHfactor, mul_comp, mul_comp]
    simp [q0, q2, q3, sub_comp]
    ring
  refine ⟨newtonCounterexamplePolynomial, monic_nat_degree.1,
    newton_counterexample_irreducible, monic_nat_degree.2,
    q0, q2, q3, ?_⟩
  refine ⟨monic_X_pow_sub_C _ (by norm_num), natDegree_X_pow_sub_C, hq0irr,
    monic_X_pow_sub_C _ (by norm_num), natDegree_X_pow_sub_C, hq2irr,
    monic_X_pow_sub_C _ (by norm_num), natDegree_X_pow_sub_C, hq3irr, hfactor⟩

end

end Submission.NumberTheory.Milne
