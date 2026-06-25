import Submission.NumberTheory.Quadratic.ContinuedFractionExpansion
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.RingTheory.Polynomial.SmallDegreeVieta

/-!
# Milne, Algebraic Number Theory, periodic continued fractions

This file develops the algebraic half of Lagrange's theorem used in Milne's discussion of real
quadratic units.  A positive finite continued-fraction block acts by a rational linear fractional
transformation.  A positive irrational fixed by a nonempty block is therefore a quadratic
irrational.
-/

namespace Submission.NumberTheory.Milne

open Polynomial

/-- The four rational coefficients of a linear fractional transformation. -/
structure CFMobius where
  a : ℚ
  b : ℚ
  c : ℚ
  d : ℚ

/-- Prepending the quotient `q` changes `M(x)` into `q + 1 / M(x)`. -/
def CFMobius.prepend (q : ℚ) (M : CFMobius) :
    CFMobius :=
  ⟨q * M.a + M.c, q * M.b + M.d, M.a, M.b⟩

/-- The linear fractional transformation associated to a finite continued-fraction block. -/
def continuedFractionMobius : List ℚ → CFMobius
  | [] => ⟨1, 0, 0, 1⟩
  | q :: qs => (continuedFractionMobius qs).prepend q

/-- Evaluate a finite continued-fraction block with a variable final tail. -/
noncomputable def finiteContinuedFraction : List ℚ → ℝ → ℝ
  | [], x => x
  | q :: qs, x => (q : ℝ) + (finiteContinuedFraction qs x)⁻¹

theorem mobius_coeffs_nonneg
    {qs : List ℚ} (hqs : ∀ q ∈ qs, 0 < q) :
    0 < (continuedFractionMobius qs).a ∧
      0 ≤ (continuedFractionMobius qs).b ∧
      0 ≤ (continuedFractionMobius qs).c ∧
      0 ≤ (continuedFractionMobius qs).d := by
  induction qs with
  | nil => norm_num [continuedFractionMobius]
  | cons q qs ih =>
      have hq : 0 < q := hqs q (by simp)
      have htail : ∀ r ∈ qs, 0 < r := by
        intro r hr
        exact hqs r (by simp [hr])
      rcases ih htail with ⟨ha, hb, hc, hd⟩
      simp only [continuedFractionMobius, CFMobius.prepend]
      constructor
      · positivity
      constructor
      · positivity
      constructor <;> positivity

theorem mobius_c_pos
    {q : ℚ} {qs : List ℚ} (hqs : ∀ r ∈ q :: qs, 0 < r) :
    0 < (continuedFractionMobius (q :: qs)).c := by
  simp only [continuedFractionMobius, CFMobius.prepend]
  exact (mobius_coeffs_nonneg
    (fun r hr ↦ hqs r (by simp [hr]))).1

theorem continued_mobius_den
    {qs : List ℚ} (hqs : ∀ q ∈ qs, 0 < q) {x : ℝ} (hx : 0 < x) :
    0 < ((continuedFractionMobius qs).c : ℝ) * x +
      (continuedFractionMobius qs).d := by
  rcases mobius_coeffs_nonneg hqs with ⟨ha, hb, hc, hd⟩
  cases qs with
  | nil => norm_num [continuedFractionMobius]
  | cons q qs =>
      have hcpos : 0 < (continuedFractionMobius (q :: qs)).c :=
        mobius_c_pos hqs
      positivity

theorem continued_mobius_num
    {qs : List ℚ} (hqs : ∀ q ∈ qs, 0 < q) {x : ℝ} (hx : 0 < x) :
    0 < ((continuedFractionMobius qs).a : ℝ) * x +
      (continuedFractionMobius qs).b := by
  rcases mobius_coeffs_nonneg hqs with ⟨ha, hb, hc, hd⟩
  positivity

/-- A positive finite continued fraction is the linear fractional transformation given by its
continuant matrix. -/
theorem continued_fraction_mobius
    {qs : List ℚ} (hqs : ∀ q ∈ qs, 0 < q) {x : ℝ} (hx : 0 < x) :
    finiteContinuedFraction qs x =
      (((continuedFractionMobius qs).a : ℝ) * x +
          (continuedFractionMobius qs).b) /
        (((continuedFractionMobius qs).c : ℝ) * x +
          (continuedFractionMobius qs).d) := by
  induction qs with
  | nil => simp [finiteContinuedFraction, continuedFractionMobius]
  | cons q qs ih =>
      have hq : 0 < q := hqs q (by simp)
      have htail : ∀ r ∈ qs, 0 < r := by
        intro r hr
        exact hqs r (by simp [hr])
      rw [finiteContinuedFraction, ih htail]
      have hden := continued_mobius_den htail hx
      have hnum := continued_mobius_num htail hx
      simp only [continuedFractionMobius, CFMobius.prepend]
      push_cast
      field_simp
      ring

/-- The algebraic direction of Lagrange's theorem for a purely periodic block: a positive
irrational fixed by a nonempty positive rational continued-fraction block has degree two over
`ℚ`. -/
theorem quadratic_irrational_continued
    {q : ℚ} {qs : List ℚ} (hqs : ∀ r ∈ q :: qs, 0 < r)
    {x : ℝ} (hx : 0 < x) (hirr : Irrational x)
    (hfix : finiteContinuedFraction (q :: qs) x = x) :
    IQIrrati x := by
  let M := continuedFractionMobius (q :: qs)
  have hc : 0 < M.c := mobius_c_pos hqs
  have hden : 0 < (M.c : ℝ) * x + M.d := continued_mobius_den hqs hx
  have heval := continued_fraction_mobius hqs hx
  have hfrac : x = ((M.a : ℝ) * x + M.b) / ((M.c : ℝ) * x + M.d) := by
    simpa [M] using hfix.symm.trans heval
  have hquad :
      x ^ 2 + (((M.d - M.a) / M.c : ℚ) : ℝ) * x - (M.b / M.c : ℚ) = 0 := by
    have hcR : (M.c : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hc
    rw [eq_div_iff (ne_of_gt hden)] at hfrac
    push_cast
    field_simp
    nlinarith
  let p : ℚ[X] := X ^ 2 + C ((M.d - M.a) / M.c) * X - C (M.b / M.c)
  have hpmonic : p.Monic := by
    dsimp [p]
    monicity <;> norm_num
  have hpdeg : p.natDegree = 2 := by
    dsimp [p]
    compute_degree
    all_goals norm_num
  have hproot : Polynomial.aeval x p = 0 := by
    simpa [p] using hquad
  have hint : IsIntegral ℚ x := ⟨p, hpmonic, hproot⟩
  refine ⟨hint, le_antisymm ?_ ?_⟩
  · have hdiv : minpoly ℚ x ∣ p := minpoly.dvd ℚ x hproot
    exact (Polynomial.natDegree_le_of_dvd hdiv hpmonic.ne_zero).trans_eq hpdeg
  · rw [minpoly.two_le_natDegree_iff hint]
    simpa [Irrational] using hirr

/-- Inversion preserves degree-two algebraicity. -/
theorem IQIrrati.inv {x : ℝ} (hx : IQIrrati x) :
    IQIrrati x⁻¹ := by
  rcases hx with ⟨hint, hdeg⟩
  have hintInv : IsIntegral ℚ x⁻¹ := hint.inv
  refine ⟨hintInv, ?_⟩
  have hadjoin : IntermediateField.adjoin ℚ ({x⁻¹} : Set ℝ) =
      IntermediateField.adjoin ℚ ({x} : Set ℝ) := by
    apply le_antisymm
    · rw [IntermediateField.adjoin_simple_le_iff]
      exact (IntermediateField.adjoin ℚ ({x} : Set ℝ)).inv_mem
        (IntermediateField.mem_adjoin_simple_self ℚ x)
    · rw [IntermediateField.adjoin_simple_le_iff]
      have hmem : x⁻¹ ∈ IntermediateField.adjoin ℚ ({x⁻¹} : Set ℝ) :=
        IntermediateField.mem_adjoin_simple_self ℚ x⁻¹
      simpa only [inv_inv] using
        (IntermediateField.adjoin ℚ ({x⁻¹} : Set ℝ)).inv_mem hmem
  calc
    (minpoly ℚ x⁻¹).natDegree =
        Module.finrank ℚ (IntermediateField.adjoin ℚ ({x⁻¹} : Set ℝ)) :=
      (IntermediateField.adjoin.finrank hintInv).symm
    _ = Module.finrank ℚ (IntermediateField.adjoin ℚ ({x} : Set ℝ)) := by rw [hadjoin]
    _ = (minpoly ℚ x).natDegree := IntermediateField.adjoin.finrank hint
    _ = 2 := hdeg

/-- Adding a rational number preserves degree-two algebraicity. -/
theorem IQIrrati.add_rat {x : ℝ} (hx : IQIrrati x) (q : ℚ) :
    IQIrrati ((q : ℝ) + x) := by
  rcases hx with ⟨hint, hdeg⟩
  have hq : IsIntegral ℚ (q : ℝ) := isIntegral_algebraMap
  refine ⟨hq.add hint, ?_⟩
  rw [add_comm]
  change (minpoly ℚ (x + algebraMap ℚ ℝ q)).natDegree = 2
  rw [minpoly.add_algebraMap]
  rw [Polynomial.natDegree_comp, hdeg]
  norm_num

/-- Every finite rational continued-fraction prefix preserves quadratic irrationality of its
tail. -/
theorem IQIrrati.finiteContinuedFraction {x : ℝ}
    (hx : IQIrrati x) (qs : List ℚ) :
    IQIrrati (finiteContinuedFraction qs x) := by
  induction qs with
  | nil => simpa [finiteContinuedFraction] using hx
  | cons q qs ih =>
      simpa [finiteContinuedFraction] using (ih.inv.add_rat q)

/-- A real quadratic irrational is irrational in the ordinary sense. -/
theorem IQIrrati.irrational
    {x : ℝ} (hx : IQIrrati x) : Irrational x := by
  rcases hx with ⟨hint, hdeg⟩
  have htwo : 2 ≤ (minpoly ℚ x).natDegree := hdeg.ge
  rw [minpoly.two_le_natDegree_iff hint] at htwo
  simpa [Irrational] using htwo

/-- Clearing the two rational denominators in the monic minimal polynomial gives an integral
quadratic equation with positive leading coefficient. -/
theorem IQIrrati.exists_int_quadr
    {x : ℝ} (hx : IQIrrati x) :
    ∃ A B C : ℤ, 0 < A ∧
      (A : ℝ) * x ^ 2 + (B : ℝ) * x + C = 0 := by
  rcases hx with ⟨hint, hdeg⟩
  let p := minpoly ℚ x
  let b := p.coeff 1
  let c := p.coeff 0
  have hpform : p = C 1 * X ^ 2 + C b * X + C c := by
    have hp := Polynomial.eq_quadratic_of_degree_le_two
      (p := p) (Polynomial.natDegree_le_iff_degree_le.mp hdeg.le)
    have hpcoeff : p.coeff 2 = 1 := by
      rw [← hdeg, ← Polynomial.leadingCoeff]
      exact (minpoly.monic hint).leadingCoeff
    simpa only [b, c, hpcoeff] using hp
  have heval : x ^ 2 + (b : ℝ) * x + (c : ℝ) = 0 := by
    have hpzero := minpoly.aeval ℚ x
    rw [show minpoly ℚ x = p from rfl, hpform] at hpzero
    simpa using hpzero
  refine ⟨(b.den * c.den : ℕ), b.num * c.den, c.num * b.den, ?_, ?_⟩
  · exact_mod_cast Nat.mul_pos b.pos c.pos
  · rw [Rat.cast_def, Rat.cast_def] at heval
    push_cast
    field_simp at heval ⊢
    nlinarith

open GenContFract

/-- The canonical continued fraction determines the real number from which it was constructed. -/
theorem cont_fract_injective : Function.Injective (GenContFract.of : ℝ → GenContFract ℝ) := by
  intro x y hxy
  have hconv : (GenContFract.of x).convs = (GenContFract.of y).convs :=
    congrArg GenContFract.convs hxy
  exact tendsto_nhds_unique (hconv ▸ GenContFract.of_convergence x)
    (GenContFract.of_convergence y)

theorem cont_fract_get?_eq_of_partDens_get?_eq (x : ℝ) {m n : ℕ}
    (h : (GenContFract.of x).partDens.get? m =
      (GenContFract.of x).partDens.get? n) :
    (GenContFract.of x).s.get? m = (GenContFract.of x).s.get? n := by
  cases hm : (GenContFract.of x).s.get? m with
  | none =>
      have hpm : (GenContFract.of x).partDens.get? m = none :=
        GenContFract.partDen_none_iff_s_none.mpr hm
      have hpn : (GenContFract.of x).partDens.get? n = none := by rw [← h, hpm]
      exact (GenContFract.partDen_none_iff_s_none.mp hpn).symm
  | some pm =>
      cases hn : (GenContFract.of x).s.get? n with
      | none =>
          have hpn : (GenContFract.of x).partDens.get? n = none :=
            GenContFract.partDen_none_iff_s_none.mpr hn
          have hpm' : (GenContFract.of x).partDens.get? m = none := by rw [h, hpn]
          have hsm := GenContFract.partDen_none_iff_s_none.mp hpm'
          rw [hm] at hsm
          contradiction
      | some pn =>
          have hbm := GenContFract.partDen_eq_s_b hm
          have hbn := GenContFract.partDen_eq_s_b hn
          have hb : pm.b = pn.b := by
            rw [hbm, hbn] at h
            exact Option.some.inj h
          have ham := (GenContFract.of_partNum_eq_one_and_exists_int_partDen_eq hm).1
          have han := (GenContFract.of_partNum_eq_one_and_exists_int_partDen_eq hn).1
          congr 1
          cases pm
          cases pn
          simp_all

/-- The `n`th complete quotient in the ordinary continued-fraction algorithm. -/
noncomputable def completeQuotient : ℕ → ℝ → ℝ
  | 0, x => x
  | n + 1, x => (Int.fract (completeQuotient n x))⁻¹

/-- The consecutive integer parts of a finite run of complete quotients. -/
noncomputable def completeQuotientBlock (x : ℝ) (n : ℕ) : ℕ → List ℚ
  | 0 => []
  | k + 1 => (⌊completeQuotient n x⌋ : ℚ) :: completeQuotientBlock x (n + 1) k

/-- Unwinding a finite run of the continued-fraction algorithm recovers its initial complete
quotient. -/
theorem continued_fraction_complete (x : ℝ) (n k : ℕ) :
    finiteContinuedFraction (completeQuotientBlock x n k) (completeQuotient (n + k) x) =
      completeQuotient n x := by
  induction k generalizing n with
  | zero => simp [completeQuotientBlock, finiteContinuedFraction]
  | succ k ih =>
      rw [completeQuotientBlock, finiteContinuedFraction]
      have htail : finiteContinuedFraction (completeQuotientBlock x (n + 1) k)
          (completeQuotient (n + (k + 1)) x) = completeQuotient (n + 1) x := by
        simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih (n + 1)
      rw [htail, completeQuotient, inv_inv]
      norm_cast
      exact Int.floor_add_fract (completeQuotient n x)

theorem gen_cont_fract (x : ℝ) (n : ℕ) :
    (GenContFract.of (completeQuotient n x)).s = (GenContFract.of x).s.drop n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [completeQuotient, ← GenContFract.of_s_tail, ih]
      rfl

/-- Periodic partial denominators give equal tails of the canonical continued fraction. -/
theorem part_dens_drop {x : ℝ} {N p : ℕ}
    (hper : Function.Periodic
      (fun n ↦ (GenContFract.of x).partDens.get? (N + n)) p) :
    (GenContFract.of x).s.drop N = (GenContFract.of x).s.drop (N + p) := by
  apply Stream'.Seq.ext
  intro n
  rw [Stream'.Seq.drop_get?, Stream'.Seq.drop_get?]
  apply cont_fract_get?_eq_of_partDens_get?_eq x
  simpa only [Function.Periodic, add_assoc, add_left_comm, add_comm] using (hper n).symm

theorem part_dens_head {x : ℝ}
    (hnot : ¬(GenContFract.of x).Terminates) (n : ℕ) :
    (GenContFract.of x).partDens.get? n =
      some (GenContFract.of (completeQuotient (n + 1) x)).h := by
  have hnt : ¬(GenContFract.of x).TerminatedAt n := by
    intro hn
    exact hnot ⟨n, hn⟩
  obtain ⟨gp, hgp⟩ := Option.ne_none_iff_exists'.mp hnt
  rw [GenContFract.partDen_eq_s_b hgp]
  have hcqHead : (GenContFract.of (completeQuotient n x)).s.head = some gp := by
    rw [gen_cont_fract, Stream'.Seq.head_dropn, hgp]
  have hfract : Int.fract (completeQuotient n x) ≠ 0 := by
    intro hf
    have hy : completeQuotient n x = (⌊completeQuotient n x⌋ : ℝ) := by
      rw [Int.fract] at hf
      exact sub_eq_zero.mp hf
    have hsNil : (GenContFract.of (completeQuotient n x)).s = Stream'.Seq.nil := by
      rw [hy]
      exact GenContFract.of_s_of_int ℝ _
    rw [hsNil] at hcqHead
    simp at hcqHead
  have hhead := GenContFract.of_s_head hfract
  rw [hcqHead] at hhead
  have hb : gp.b =
      (↑⌊(Int.fract (completeQuotient n x))⁻¹⌋ : ℝ) := by
    exact congrArg GenContFract.Pair.b (Option.some.inj hhead)
  exact congrArg some (hb.trans (by rw [completeQuotient, GenContFract.of_h_eq_floor]))

/-- Every complete quotient of an irrational number is irrational. -/
theorem irrational_completeQuotient {x : ℝ} (hx : Irrational x) (n : ℕ) :
    Irrational (completeQuotient n x) := by
  induction n with
  | zero => exact hx
  | succ n ih =>
      rw [completeQuotient, irrational_inv_iff, Int.fract]
      exact irrational_sub_intCast_iff.mpr ih

/-- The finite block read from a nonterminating canonical continued fraction has positive rational
coefficients. -/
theorem complete_block_pos {x : ℝ} (hnot : ¬(GenContFract.of x).Terminates)
    (N k : ℕ) : ∀ q ∈ completeQuotientBlock x (N + 1) k, 0 < q := by
  induction k generalizing N with
  | zero => simp [completeQuotientBlock]
  | succ k ih =>
      intro q hq
      simp only [completeQuotientBlock, List.mem_cons] at hq
      rcases hq with rfl | hq
      · have hpd := part_dens_head hnot N
        rw [GenContFract.of_h_eq_floor] at hpd
        have hone : (1 : ℝ) ≤ (⌊completeQuotient (N + 1) x⌋ : ℝ) :=
          GenContFract.of_one_le_get?_partDen hpd
        exact_mod_cast (zero_lt_one.trans_le hone)
      · simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          ih (N + 1) q hq

/-- A period in the canonical partial denominators makes the corresponding complete quotient
repeat. -/
theorem complete_dens_periodic {x : ℝ} {N p : ℕ}
    (hnot : ¬(GenContFract.of x).Terminates)
    (hper : Function.Periodic
      (fun n ↦ (GenContFract.of x).partDens.get? (N + n)) p) :
    completeQuotient (N + 1) x = completeQuotient (N + p + 1) x := by
  have hperShift : Function.Periodic
      (fun n ↦ (GenContFract.of x).partDens.get? (N + 1 + n)) p := by
    intro n
    simpa only [Function.Periodic, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      hper (n + 1)
  have hs : (GenContFract.of (completeQuotient (N + 1) x)).s =
      (GenContFract.of (completeQuotient (N + p + 1) x)).s := by
    rw [gen_cont_fract, gen_cont_fract]
    simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      part_dens_drop hperShift
  have hh : (GenContFract.of (completeQuotient (N + 1) x)).h =
      (GenContFract.of (completeQuotient (N + p + 1) x)).h := by
    have hN := part_dens_head hnot N
    have hNp := part_dens_head hnot (N + p)
    apply Option.some.inj
    rw [← hN, ← hNp]
    simpa only [Function.Periodic, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      (hper 0).symm
  apply cont_fract_injective
  apply GenContFract.ext
  · exact hh
  · exact hs

/-- The complete quotient at the start of a positive period is a quadratic irrational. -/
theorem quadratic_irrational_periodic {x : ℝ} {N p : ℕ}
    (hx : Irrational x) (hp : 0 < p)
    (hper : Function.Periodic
      (fun n ↦ (GenContFract.of x).partDens.get? (N + n)) p) :
    IQIrrati (completeQuotient (N + 1) x) := by
  have hnot : ¬(GenContFract.of x).Terminates := by
    rw [continued_terminates_irrational]
    simpa [Irrational, eq_comm] using hx
  have hrepeat := complete_dens_periodic hnot hper
  have hfix : finiteContinuedFraction (completeQuotientBlock x (N + 1) p)
      (completeQuotient (N + 1) x) = completeQuotient (N + 1) x := by
    nth_rewrite 1 [hrepeat]
    simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      continued_fraction_complete x (N + 1) p
  have hyirr : Irrational (completeQuotient (N + 1) x) :=
    irrational_completeQuotient hx (N + 1)
  have hypos : 0 < completeQuotient (N + 1) x := by
    rw [completeQuotient]
    exact inv_pos.mpr (Int.fract_pos.mpr
      ((irrational_completeQuotient hx N).ne_int ⌊completeQuotient N x⌋))
  cases p with
  | zero => omega
  | succ p =>
      apply quadratic_irrational_continued
        (q := (⌊completeQuotient (N + 1) x⌋ : ℚ))
        (qs := completeQuotientBlock x (N + 1 + 1) p)
      · simpa only [completeQuotientBlock] using complete_block_pos hnot N (p + 1)
      · exact hypos
      · exact hyirr
      · simpa only [completeQuotientBlock] using hfix

/-- The algebraic direction of Lagrange's theorem: an irrational real number with eventually
periodic canonical continued fraction is quadratic. -/
theorem irrational_continued_periodic {x : ℝ}
    (hx : Irrational x) (hperiodic : ContinuedEventuallyPeriodic x) :
    IQIrrati x := by
  rcases hperiodic with ⟨N, p, hp, hper⟩
  have htail := quadratic_irrational_periodic hx hp hper
  have hprefix := htail.finiteContinuedFraction (completeQuotientBlock x 0 (N + 1))
  have hreconstruct := continued_fraction_complete x 0 (N + 1)
  have hreconstruct' : finiteContinuedFraction (completeQuotientBlock x 0 (N + 1))
      (completeQuotient (N + 1) x) = completeQuotient 0 x := by
    simpa only [Nat.zero_add] using hreconstruct
  change finiteContinuedFraction (completeQuotientBlock x 0 (N + 1))
      (completeQuotient (N + 1) x) = x at hreconstruct'
  rw [hreconstruct'] at hprefix
  exact hprefix

theorem completeQuotient_add (x : ℝ) (m n : ℕ) :
    completeQuotient (m + n) x = completeQuotient n (completeQuotient m x) := by
  induction n with
  | zero => simp [completeQuotient]
  | succ n ih =>
      rw [Nat.add_succ, completeQuotient, completeQuotient, ih]

/-- Once two complete quotients agree, determinism makes the following tail periodic. -/
theorem complete_quotient_periodic (x : ℝ) {m n : ℕ} (hmn : m < n)
    (h : completeQuotient m x = completeQuotient n x) :
    Function.Periodic (fun k ↦ completeQuotient (m + k) x) (n - m) := by
  intro k
  have hn : n = m + (n - m) := (Nat.add_sub_of_le hmn.le).symm
  dsimp only
  rw [show m + (k + (n - m)) = (m + (n - m)) + k by omega,
    completeQuotient_add, ← hn, ← h, ← completeQuotient_add]

/-- A sequence of complete quotients with finite range is eventually periodic. -/
theorem complete_eventually_periodic (x : ℝ)
    (hfinite : (Set.range fun n ↦ completeQuotient n x).Finite) :
    EventuallyPeriodic (fun n ↦ completeQuotient n x) := by
  obtain ⟨m, -, n, -, hne, heq⟩ :=
    Set.Infinite.exists_ne_map_eq_of_mapsTo (f := fun n ↦ completeQuotient n x)
      Set.infinite_univ
      (fun n _ ↦ show completeQuotient n x ∈
        Set.range (fun n ↦ completeQuotient n x) from ⟨n, rfl⟩) hfinite
  rcases Nat.lt_or_gt_of_ne hne with hmn | hnm
  · refine ⟨m, n - m, Nat.sub_pos_of_lt hmn, ?_⟩
    exact complete_quotient_periodic x hmn heq
  · refine ⟨n, m - n, Nat.sub_pos_of_lt hnm, ?_⟩
    exact complete_quotient_periodic x hnm heq.symm

/-- Finite range of the complete quotients is the precise bounded-state input needed for the
forward direction of Lagrange's theorem. -/
theorem continued_eventually_periodic
    {x : ℝ} (hnot : ¬(GenContFract.of x).Terminates)
    (hfinite : (Set.range fun n ↦ completeQuotient n x).Finite) :
    ContinuedEventuallyPeriodic x := by
  rcases complete_eventually_periodic x hfinite with
    ⟨N, p, hp, hper⟩
  refine ⟨N, p, hp, ?_⟩
  intro n
  dsimp only
  rw [part_dens_head hnot,
    part_dens_head hnot]
  exact congrArg (fun y : ℝ ↦ some (GenContFract.of y).h)
    (by simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hper (n + 1))

/-- Subtracting an integer and inverting transports an integral quadratic equation to another
integral quadratic equation with the same discriminant. -/
theorem quadratic_equation_sub
    {y : ℝ} {A B C a : ℤ}
    (hroot : (A : ℝ) * y ^ 2 + (B : ℝ) * y + C = 0)
    (hne : y ≠ a) :
    (((A * a ^ 2 + B * a + C : ℤ) : ℝ) * (y - a)⁻¹ ^ 2 +
        ((2 * A * a + B : ℤ) : ℝ) * (y - a)⁻¹ + A = 0) ∧
      (2 * A * a + B) ^ 2 - 4 * (A * a ^ 2 + B * a + C) * A =
        B ^ 2 - 4 * A * C := by
  constructor
  · have hsub : y - (a : ℝ) ≠ 0 := sub_ne_zero.mpr hne
    field_simp
    push_cast
    nlinarith
  · ring

/-- One complete-quotient step applies the integral quadratic-state recurrence, preserving its
discriminant. -/
theorem complete_quadratic_equation
    {x : ℝ} {n : ℕ} {A B C : ℤ}
    (hroot : (A : ℝ) * completeQuotient n x ^ 2 +
      (B : ℝ) * completeQuotient n x + C = 0)
    (hirr : Irrational (completeQuotient n x)) :
    let a := ⌊completeQuotient n x⌋
    (((A * a ^ 2 + B * a + C : ℤ) : ℝ) * completeQuotient (n + 1) x ^ 2 +
        ((2 * A * a + B : ℤ) : ℝ) * completeQuotient (n + 1) x + A = 0) ∧
      (2 * A * a + B) ^ 2 - 4 * (A * a ^ 2 + B * a + C) * A =
        B ^ 2 - 4 * A * C := by
  dsimp only
  rw [completeQuotient, Int.fract]
  exact quadratic_equation_sub hroot (hirr.ne_int _)

/-- Starting from one integral quadratic equation for an irrational, every complete quotient
satisfies an integral quadratic equation with the same discriminant. -/
theorem quadratic_equation_complete
    {x : ℝ} (hx : Irrational x) {A B C : ℤ}
    (hroot : (A : ℝ) * x ^ 2 + (B : ℝ) * x + C = 0) :
    ∀ n : ℕ, ∃ A' B' C' : ℤ,
      B' ^ 2 - 4 * A' * C' = B ^ 2 - 4 * A * C ∧
        (A' : ℝ) * completeQuotient n x ^ 2 +
          (B' : ℝ) * completeQuotient n x + C' = 0 := by
  intro n
  induction n with
  | zero => exact ⟨A, B, C, rfl, hroot⟩
  | succ n ih =>
      obtain ⟨A', B', C', hdisc, hroot'⟩ := ih
      obtain ⟨hnext, hdiscNext⟩ :=
        complete_quadratic_equation hroot'
          (irrational_completeQuotient hx n)
      let a := ⌊completeQuotient n x⌋
      refine ⟨A' * a ^ 2 + B' * a + C', 2 * A' * a + B', A', ?_, ?_⟩
      · exact hdiscNext.trans hdisc
      · simpa only [Nat.succ_eq_add_one] using hnext

/-- An irrational real root of an integral quadratic with positive leading coefficient has
strictly positive discriminant. -/
theorem quadratic_discriminant_pos
    {x : ℝ} (hx : Irrational x) {A B C : ℤ} (hA : 0 < A)
    (hroot : (A : ℝ) * x ^ 2 + (B : ℝ) * x + C = 0) :
    0 < B ^ 2 - 4 * A * C := by
  have hA0 : (A : ℝ) ≠ 0 := by exact_mod_cast hA.ne'
  have hlin : 2 * (A : ℝ) * x + B ≠ 0 := by
    intro hzero
    apply hx.ne_rat (-B / (2 * A))
    push_cast
    field_simp
    nlinarith
  have hdisc :
      (((B ^ 2 - 4 * A * C : ℤ) : ℝ)) = (2 * (A : ℝ) * x + B) ^ 2 := by
    push_cast
    calc
      (B : ℝ) ^ 2 - 4 * A * C =
          (2 * A * x + B) ^ 2 - 4 * A * (A * x ^ 2 + B * x + C) := by ring
      _ = (2 * A * x + B) ^ 2 := by rw [hroot]; ring
  exact_mod_cast (hdisc.symm ▸ sq_pos_of_ne_zero hlin)

/-- The complete quotients of a quadratic irrational all satisfy integral quadratic equations with
one fixed discriminant. -/
theorem IQIrrati.exists_fixed_discstates
    {x : ℝ} (hx : IQIrrati x) :
    ∃ D : ℤ, ∀ n : ℕ, ∃ A B C : ℤ,
      B ^ 2 - 4 * A * C = D ∧
        (A : ℝ) * completeQuotient n x ^ 2 +
          (B : ℝ) * completeQuotient n x + C = 0 := by
  obtain ⟨A, B, C, -, hroot⟩ := hx.exists_int_quadr
  exact ⟨B ^ 2 - 4 * A * C,
    quadratic_equation_complete hx.irrational hroot⟩

/-- The fixed discriminant of the complete-quotient states can be chosen positive. -/
theorem IQIrrati.exists_posfi_discs
    {x : ℝ} (hx : IQIrrati x) :
    ∃ D : ℤ, 0 < D ∧ ∀ n : ℕ, ∃ A B C : ℤ,
      B ^ 2 - 4 * A * C = D ∧
        (A : ℝ) * completeQuotient n x ^ 2 +
          (B : ℝ) * completeQuotient n x + C = 0 := by
  obtain ⟨A, B, C, hA, hroot⟩ := hx.exists_int_quadr
  exact ⟨B ^ 2 - 4 * A * C, quadratic_discriminant_pos hx.irrational hA hroot,
    quadratic_equation_complete hx.irrational hroot⟩

/-- Fixed-discriminant reduced quadratic states form a finite set.  This is the bounded-state
step in the classical proof of the forward direction of Lagrange's theorem. -/
theorem complete_reduced_states
    (x : ℝ) (D : ℤ)
    (hstate : ∀ n : ℕ, ∃ A B C : ℤ,
      0 < A ∧ C < 0 ∧ B ^ 2 - 4 * A * C = D ∧
        (A : ℝ) * completeQuotient n x ^ 2 +
          (B : ℝ) * completeQuotient n x + C = 0) :
    (Set.range fun n ↦ completeQuotient n x).Finite := by
  have hD : 0 < D := by
    obtain ⟨A, B, C, hA, hC, hdisc, -⟩ := hstate 0
    nlinarith [sq_nonneg B]
  let U : Set ℤ := Set.Icc (-D) D
  let roots : Set ℝ := ⋃ (f : ℤ[X])
      (_ : f.natDegree ≤ 2 ∧ ∀ i, f.coeff i ∈ U),
      (((f.map (Int.castRingHom ℝ)).roots.toFinset : Finset ℝ) : Set ℝ)
  have hroots : roots.Finite := by
    exact Polynomial.bUnion_roots_finite (Int.castRingHom ℝ) 2
      (Set.finite_Icc (-D) D)
  apply hroots.subset
  rintro y ⟨n, rfl⟩
  obtain ⟨A, B, C, hA, hC, hdisc, hroot⟩ := hstate n
  have hA_le : A ≤ D := by nlinarith [sq_nonneg B]
  have hC_le : -C ≤ D := by nlinarith [sq_nonneg B]
  have hB_sq : B ^ 2 ≤ D := by nlinarith
  have hB_lower : -D ≤ B := by
    by_contra h
    have : B < -D := lt_of_not_ge h
    nlinarith [sq_nonneg (B + D)]
  have hB_upper : B ≤ D := by
    by_contra h
    have : D < B := lt_of_not_ge h
    nlinarith [sq_nonneg (B - D)]
  let f : ℤ[X] := Polynomial.monomial 2 A +
    Polynomial.monomial 1 B + Polynomial.monomial 0 C
  have hfdeg : f.natDegree ≤ 2 := by
    dsimp [f]
    rw [← Polynomial.C_mul_X_pow_eq_monomial,
      ← Polynomial.C_mul_X_pow_eq_monomial]
    simpa only [pow_one, pow_zero, mul_one] using
      (Polynomial.natDegree_quadratic_le (a := A) (b := B) (c := C))
  have hfcoeff : ∀ i, f.coeff i ∈ U := by
    intro i
    have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ 3 ≤ i := by omega
    rcases hi with rfl | rfl | rfl | hi
    · simp only [f, Polynomial.coeff_add, Polynomial.coeff_monomial]
      norm_num [U]
      constructor <;> omega
    · simp only [f, Polynomial.coeff_add, Polynomial.coeff_monomial]
      norm_num [U]
      exact ⟨hB_lower, hB_upper⟩
    · simp only [f, Polynomial.coeff_add, Polynomial.coeff_monomial]
      norm_num [U]
      constructor <;> omega
    · have : f.coeff i = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt
        (hfdeg.trans_lt hi)
      rw [this]
      simp [U, hD.le]
  have hfne : f.map (Int.castRingHom ℝ) ≠ 0 := by
    intro hf
    have := congrArg (fun p : ℝ[X] ↦ p.coeff 2) hf
    simp only [f, Polynomial.map_add, Polynomial.map_monomial,
      Polynomial.coeff_add, Polynomial.coeff_monomial] at this
    norm_num at this
    exact_mod_cast hA.ne' this
  apply Set.mem_iUnion_of_mem f
  apply Set.mem_iUnion_of_mem ⟨hfdeg, hfcoeff⟩
  change completeQuotient n x ∈ (f.map (Int.castRingHom ℝ)).roots.toFinset
  rw [Multiset.mem_toFinset, Polynomial.mem_roots hfne]
  change Polynomial.eval (completeQuotient n x) (f.map (Int.castRingHom ℝ)) = 0
  rw [Polynomial.eval_map]
  simp only [f, Polynomial.eval₂_add, Polynomial.eval₂_monomial]
  norm_num
  exact hroot

/-- A finite preperiod does not affect the bounded-state argument: it is enough that the complete
quotients are reduced quadratic states from some index onward. -/
theorem eventually_reduced_states
    (x : ℝ) (D : ℤ) (N : ℕ)
    (hstate : ∀ n : ℕ, N ≤ n → ∃ A B C : ℤ,
      0 < A ∧ C < 0 ∧ B ^ 2 - 4 * A * C = D ∧
        (A : ℝ) * completeQuotient n x ^ 2 +
          (B : ℝ) * completeQuotient n x + C = 0) :
    (Set.range fun n ↦ completeQuotient n x).Finite := by
  have htail : (Set.range fun n ↦ completeQuotient n (completeQuotient N x)).Finite := by
    refine complete_reduced_states
      (completeQuotient N x) D ?_
    intro n
    obtain ⟨A, B, C, hA, hC, hdisc, hroot⟩ := hstate (N + n) (Nat.le_add_right N n)
    refine ⟨A, B, C, hA, hC, hdisc, ?_⟩
    simpa only [completeQuotient_add] using hroot
  have hprefix : ((fun n ↦ completeQuotient n x) '' Set.Iio N).Finite :=
    (Set.finite_Iio N).image _
  apply (hprefix.union htail).subset
  rintro y ⟨n, rfl⟩
  by_cases hn : n < N
  · exact Or.inl ⟨n, hn, rfl⟩
  · right
    refine ⟨n - N, ?_⟩
    change completeQuotient (n - N) (completeQuotient N x) = completeQuotient n x
    rw [← completeQuotient_add]
    congr
    omega

/-- Eventual reducedness of the fixed-discriminant quadratic states gives the forward
periodicity conclusion directly. -/
theorem continued_periodic_states
    {x : ℝ} (hnot : ¬(GenContFract.of x).Terminates) (D : ℤ) (N : ℕ)
    (hstate : ∀ n : ℕ, N ≤ n → ∃ A B C : ℤ,
      0 < A ∧ C < 0 ∧ B ^ 2 - 4 * A * C = D ∧
        (A : ℝ) * completeQuotient n x ^ 2 +
          (B : ℝ) * completeQuotient n x + C = 0) :
    ContinuedEventuallyPeriodic x :=
  continued_eventually_periodic hnot
    (eventually_reduced_states x D N hstate)

end Submission.NumberTheory.Milne
