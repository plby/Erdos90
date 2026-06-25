import Mathlib


open scoped BigOperators

namespace Struik

private lemma factorial_choose_prod (A : ℤ) (k : ℕ) :
    (k.factorial : ℤ) * Ring.choose A k =
      ∏ j ∈ Finset.range k, (A - (j : ℤ)) := by
  rw [← nsmul_eq_mul, ← Ring.descPochhammer_eq_factorial_smul_choose]
  rw [← Polynomial.eval_eq_smeval]
  exact descPochhammer_eval_eq_prod_range k A

private lemma choose_coprime_factorial
    {m k : ℕ} {A B : ℤ}
    (hcop : m.Coprime k.factorial)
    (hAB : A ≡ B [ZMOD (m : ℤ)]) :
    Ring.choose A k ≡ Ring.choose B k [ZMOD (m : ℤ)] := by
  have hprod :
      (∏ j ∈ Finset.range k, (A - (j : ℤ))) ≡
        (∏ j ∈ Finset.range k, (B - (j : ℤ))) [ZMOD (m : ℤ)] := by
    apply Int.ModEq.prod
    intro j hj
    exact hAB.sub (Int.ModEq.refl (j : ℤ))
  rw [← factorial_choose_prod, ← factorial_choose_prod] at hprod
  rw [Int.modEq_iff_dvd] at hprod ⊢
  have hdiv :
      (m : ℤ) ∣ (k.factorial : ℤ) *
        (Ring.choose B k - Ring.choose A k) := by
    convert hprod using 1 ; ring
  exact hcop.cast.dvd_of_dvd_mul_left hdiv

/-- Struik's Lemma 6, equation (35). -/
theorem choose_add_pred
    {p α : ℕ} (hp : p.Prime) (A : ℤ) :
    Ring.choose (A + p ^ α) (p - 1) ≡
      Ring.choose A (p - 1) [ZMOD (p ^ α : ℕ)] := by
  have hpfact : p.Coprime (p - 1).factorial :=
    hp.coprime_factorial_of_lt (Nat.sub_lt hp.pos zero_lt_one)
  apply choose_coprime_factorial (hpfact.pow_left α)
  rw [Int.modEq_iff_dvd]
  use -1
  push_cast
  ring

/-- Binomial coefficients of degree strictly below `p` are periodic modulo
`p^α` with period `p^α`. This is the form used in equations (62)--(64). -/
theorem choose_mod_pow
    {p α k : ℕ} (hp : p.Prime) (hk : k < p)
    {A C : ℤ} (hAC : A ≡ C [ZMOD (p ^ α : ℕ)]) :
    Ring.choose A k ≡ Ring.choose C k [ZMOD (p ^ α : ℕ)] := by
  exact choose_coprime_factorial
    ((hp.coprime_factorial_of_lt hk).pow_left α) hAC

private lemma choose_pred_mod
    {p a : ℕ} [Fact p.Prime] :
    Nat.choose (p ^ (a + 1) - 1) (p - 1) ≡ 1 [MOD p] := by
  have hp := (Fact.out : p.Prime)
  have hdecomp : p ^ a * p - 1 = (p ^ a - 1) * p + (p - 1) := by
    have hpos : 0 < p ^ a := pow_pos hp.pos a
    nth_rw 1 [show p ^ a = (p ^ a - 1) + 1 by omega]
    rw [Nat.add_mul, one_mul, Nat.add_sub_assoc hp.one_le]
  have h := Choose.choose_modEq_choose_mod_mul_choose_div_nat
    (n := p ^ (a + 1) - 1) (k := p - 1) (p := p)
  rw [Nat.pow_succ, hdecomp] at h ⊢
  simpa [Nat.add_mul_mod_self_left, Nat.add_mul_div_left, hp.pos,
    Nat.mod_eq_of_lt (Nat.sub_lt hp.pos zero_lt_one),
    Nat.div_eq_of_lt (Nat.sub_lt hp.pos zero_lt_one)] using h

private lemma choose_pow_succ
    {p a : ℕ} (hp : p.Prime) :
    Nat.choose (p ^ (a + 1)) p =
      p ^ a * Nat.choose (p ^ (a + 1) - 1) (p - 1) := by
  have h := Nat.add_one_mul_choose_eq (p ^ (a + 1) - 1) (p - 1)
  have hpow : 0 < p ^ (a + 1) := pow_pos hp.pos _
  rw [Nat.sub_add_cancel hpow, Nat.sub_add_cancel hp.one_le, Nat.pow_succ] at h
  rw [Nat.pow_succ]
  apply Nat.mul_right_cancel hp.pos
  simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using h.symm

private lemma choose_succ_mod
    {p a : ℕ} [Fact p.Prime] :
    Nat.choose (p ^ (a + 1)) p ≡ p ^ a [MOD p ^ (a + 1)] := by
  have hp := (Fact.out : p.Prime)
  rw [choose_pow_succ hp, Nat.pow_succ]
  simpa using
    (choose_pred_mod (p := p) (a := a)).mul_left' (p ^ a)

/-- Struik's Lemma 7, equations (36)--(40). -/
theorem choose_add_mod
    {p α : ℕ} (hp : p.Prime) (A : ℤ) :
    Ring.choose (A + p ^ α) p ≡
      Ring.choose A p + (p ^ (α - 1) : ℕ) [ZMOD (p ^ α : ℕ)] := by
  letI : Fact p.Prime := ⟨hp⟩
  cases α with
  | zero => simp [Int.ModEq]
  | succ a =>
      let q : ℕ := p ^ (a + 1)
      let t : ℕ := p ^ a
      let P : ℤ → Prop := fun Z =>
        Ring.choose (Z + q) p ≡ Ring.choose Z p + t [ZMOD (q : ℤ)]
      have hlower (Z : ℤ) :
          Ring.choose (Z + q) (p - 1) ≡
            Ring.choose Z (p - 1) [ZMOD (q : ℤ)] := by
        simpa [q] using choose_add_pred hp Z (α := a + 1)
      have hstep (Z : ℤ) : P Z ↔ P (Z + 1) := by
        have hpPred : p - 1 + 1 = p := Nat.sub_add_cancel hp.one_le
        have hchooseSucc (X : ℤ) :
            Ring.choose (X + 1) p =
              Ring.choose X (p - 1) + Ring.choose X p := by
          rw [← hpPred]
          exact Ring.choose_succ_succ X (p - 1)
        constructor
        · intro hZ
          have h := (hlower Z).add hZ
          dsimp [P] at h ⊢
          rw [show Z + 1 + (q : ℤ) = (Z + q) + 1 by ring,
            hchooseSucc, hchooseSucc]
          simpa only [add_assoc] using h
        · intro hZ
          dsimp [P] at hZ ⊢
          rw [show Z + 1 + (q : ℤ) = (Z + q) + 1 by ring,
            hchooseSucc, hchooseSucc] at hZ
          have h := hZ.sub (hlower Z)
          simpa only [add_sub_cancel_left, add_assoc] using h
      have hzero : P 0 := by
        have hnat := choose_succ_mod (p := p) (a := a)
        have hint :
            (Nat.choose q p : ℤ) ≡ (t : ℤ) [ZMOD (q : ℤ)] := by
          simpa [q, t, Nat.cast_pow] using (show
            (Nat.choose (p ^ (a + 1)) p : ℤ) ≡
              (p ^ a : ℕ) [ZMOD (p ^ (a + 1) : ℕ)] from by
                exact_mod_cast hnat)
        dsimp [P]
        rw [zero_add, Ring.choose_natCast]
        simpa [Ring.choose_zero_pos ℤ hp.pos] using hint
      change P A
      exact Int.induction_on A hzero
        (fun i hi => (hstep i).mp hi)
        (fun i hi => by
          have hi' : P ((-(i : ℤ) - 1) + 1) := by
            convert hi using 1 ; ring
          exact (hstep (-(i : ℤ) - 1)).mpr hi')

private lemma mod_periodic
    {m n : ℤ} (f : ℤ → ℤ)
    (hperiod : ∀ z, f (z + m) ≡ f z [ZMOD n])
    {A C : ℤ} (hAC : A ≡ C [ZMOD m]) :
    f A ≡ f C [ZMOD n] := by
  rw [Int.modEq_iff_dvd] at hAC
  rcases hAC with ⟨k, hk⟩
  have hC : C = A + m * k := by linarith
  subst C
  let P : ℤ → Prop := fun i => f A ≡ f (A + m * i) [ZMOD n]
  change P k
  exact Int.induction_on k (by simp [P])
    (fun i hi => by
      dsimp [P] at hi ⊢
      have hnext := (hperiod (A + m * i)).symm
      convert hi.trans hnext using 1 ; ring_nf)
    (fun i hi => by
      dsimp [P] at hi ⊢
      have hnext :
          f (A + m * (-(i : ℤ))) ≡
            f (A + m * (-(i : ℤ) - 1)) [ZMOD n] := by
        convert hperiod (A + m * (-(i : ℤ) - 1)) using 1 ; ring_nf
      exact hi.trans hnext)

/-- Degree-`p` binomial coefficients are well-defined modulo
`p^(α-1)` when their argument is specified modulo `p^α`. -/
theorem choose_mod_power
    {p α : ℕ} (hp : p.Prime) (_hα : 0 < α)
    {A C : ℤ} (hAC : A ≡ C [ZMOD (p ^ α : ℕ)]) :
    Ring.choose A p ≡ Ring.choose C p
      [ZMOD (p ^ (α - 1) : ℕ)] := by
  apply mod_periodic (fun X => Ring.choose X p) ?_ hAC
  intro X
  have h := choose_add_mod hp X (α := α)
  have hpowNat : p ^ (α - 1) ∣ p ^ α :=
    pow_dvd_pow p (Nat.sub_le α 1)
  have hpowInt : (p ^ (α - 1) : ℤ) ∣ (p ^ α : ℤ) := by
    exact_mod_cast hpowNat
  have hdown := h.of_dvd hpowInt
  apply hdown.trans
  rw [Int.modEq_iff_dvd]
  use -1
  push_cast
  ring

/-- The integer expression appearing on both sides of Struik's equation (41). -/
def form (p : ℕ) (A B : ℤ) : ℤ :=
  A * B - p * Ring.choose A p * B - p * Ring.choose B p * A

private lemma form_comm (p : ℕ) (A B : ℤ) :
    form p A B = form p B A := by
  simp [form]
  ring

private lemma form_add_mod
    {p α : ℕ} (hp : p.Prime) (hα : 0 < α) (A B : ℤ) :
    form p (A + p ^ α) B ≡
      form p A B [ZMOD (p ^ (α + 1) : ℕ)] := by
  obtain ⟨a, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hα.ne'
  have hchoose := choose_add_mod hp A (α := a + 1)
  have hscaled :
      (p : ℤ) * Ring.choose (A + p ^ (a + 1)) p ≡
        p * (Ring.choose A p + (p ^ a : ℕ))
          [ZMOD (p ^ (a + 2) : ℕ)] := by
    have h := Int.ModEq.mul_left' (c := (p : ℤ)) hchoose
    simpa [Nat.pow_succ, mul_comm, mul_left_comm, mul_assoc] using h
  have hreplace :
      form p (A + p ^ (a + 1)) B ≡
        (A + p ^ (a + 1)) * B -
          (p * (Ring.choose A p + p ^ a)) * B -
          p * Ring.choose B p * (A + p ^ (a + 1))
        [ZMOD (p ^ (a + 2) : ℕ)] := by
    dsimp [form]
    have hterm := hscaled.mul_right B
    convert (Int.ModEq.refl ((A + (p ^ (a + 1) : ℕ)) * B)).sub
      (hterm.add (Int.ModEq.refl
        ((p : ℤ) * Ring.choose B p * (A + (p ^ (a + 1) : ℕ))))) using 1 <;>
      simp only [Nat.cast_pow] <;> ring
  apply hreplace.trans
  rw [Int.modEq_iff_dvd]
  use Ring.choose B p
  dsimp [form]
  ring

/-- Struik's Lemma 8, equations (41)--(42). -/
theorem prime_congruence_form
    {p α : ℕ} (hp : p.Prime) (hα : 0 < α)
    {A B C D : ℤ}
    (hAC : A ≡ C [ZMOD (p ^ α : ℕ)])
    (hBD : B ≡ D [ZMOD (p ^ α : ℕ)]) :
    form p A B ≡ form p C D [ZMOD (p ^ (α + 1) : ℕ)] := by
  have hfirst :
      form p A B ≡ form p C B [ZMOD (p ^ (α + 1) : ℕ)] :=
    mod_periodic (fun X => form p X B)
      (fun X => form_add_mod hp hα X B) hAC
  have hsecond' :
      form p B C ≡ form p D C [ZMOD (p ^ (α + 1) : ℕ)] :=
    mod_periodic (fun X => form p X C)
      (fun X => form_add_mod hp hα X C) hBD
  have hsecond :
      form p C B ≡ form p C D [ZMOD (p ^ (α + 1) : ℕ)] := by
    simpa only [form_comm] using hsecond'
  exact hfirst.trans hsecond

end Struik
