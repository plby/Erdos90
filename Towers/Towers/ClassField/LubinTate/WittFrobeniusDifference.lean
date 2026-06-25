import Mathlib.RingTheory.WittVector.FrobeniusFractionField
import Mathlib.RingTheory.WittVector.Complete
import Towers.ClassField.LubinTate.ResidueFieldBase

/-!
# The Artin--Schreier map on Witt vectors

For an algebraically closed field `k` of characteristic `p`, Frobenius minus
the identity is onto on `W(k)`.  The proof lifts solutions of
`z ^ p - z = b` one `p`-adic digit at a time and uses the existing
`p`-adic completeness and separatedness of the Witt ring.

This is the additive arithmetic input in Lemma I.3.11 and Proposition
I.3.10 for the completed maximal-unramified coefficient ring.
-/

namespace WittVector

noncomputable section

variable (p : ℕ) [Fact p.Prime]
variable {k : Type*} [Field k] [CharP k p] [IsAlgClosed k]

set_option maxHeartbeats 2000000 in
-- The one-step correction unfolds Witt coefficients and ideal divisibility.
private theorem frobenius_approximation_succ
    (a x : WittVector p k) (n : ℕ)
    (hx : frobenius x - x - a ∈ Ideal.span {(p : WittVector p k) ^ n}) :
    ∃ y : WittVector p k,
      frobenius y - y - a ∈ Ideal.span {(p : WittVector p k) ^ (n + 1)} ∧
      y - x ∈ Ideal.span {(p : WittVector p k) ^ n} := by
  rw [Ideal.mem_span_singleton] at hx
  obtain ⟨d, hd⟩ := hx
  obtain ⟨z, hz⟩ :=
    Towers.CField.LTate.frobenius_pow_surjective
      k p 1 (by omega) (-d.coeff 0)
  let c : WittVector p k := teichmuller p z
  refine ⟨x + (p : WittVector p k) ^ n * c, ?_, ?_⟩
  · rw [Ideal.mem_span_singleton]
    have hcoeff : (d + frobenius c - c).coeff 0 = 0 := by
      change constantCoeff (d + frobenius c - c) = 0
      simp only [map_sub, map_add, coeff_frobenius_charP,
        teichmuller_coeff_zero, c, constantCoeff_apply]
      change z ^ (p ^ 1) - z = -d.coeff 0 at hz
      rw [pow_one] at hz
      linear_combination hz
    have hbmem := (mem_span_p_iff_coeff_zero_eq_zero
      (d + frobenius c - c)).2 hcoeff
    rw [Ideal.mem_span_singleton] at hbmem
    obtain ⟨e, he⟩ := hbmem
    refine ⟨e, ?_⟩
    have hfixp : frobenius (p : WittVector p k) = p := by simp
    have hcalc :
        frobenius (x + (p : WittVector p k) ^ n * c) -
            (x + (p : WittVector p k) ^ n * c) - a =
          (p : WittVector p k) ^ (n + 1) * e := by
      calc
        frobenius (x + (p : WittVector p k) ^ n * c) -
            (x + (p : WittVector p k) ^ n * c) - a =
            (frobenius x - x - a) +
              (p : WittVector p k) ^ n * (frobenius c - c) := by
          rw [map_add, map_mul, map_pow, hfixp]
          ring
        _ = (p : WittVector p k) ^ n * d +
              (p : WittVector p k) ^ n * (frobenius c - c) := by rw [hd]
        _ = (p : WittVector p k) ^ n * (d + frobenius c - c) := by ring
        _ = (p : WittVector p k) ^ (n + 1) * e := by
          rw [he]
          rw [pow_succ]
          ring
    exact hcalc
  · rw [Ideal.mem_span_singleton]
    exact ⟨c, by ring⟩

private noncomputable def frobeniusSubApproximation
    (a : WittVector p k) :
    (n : ℕ) → {x : WittVector p k //
      frobenius x - x - a ∈ Ideal.span {(p : WittVector p k) ^ n}}
  | 0 => ⟨0, by
      rw [pow_zero]
      rw [Ideal.mem_span_singleton]
      exact ⟨-a, by simp⟩⟩
  | n + 1 => by
      let xn := frobeniusSubApproximation a n
      let h := frobenius_approximation_succ p a xn n xn.property
      exact ⟨Classical.choose h, (Classical.choose_spec h).1⟩

private theorem frobenius_sub_approximation
    (a : WittVector p k) (n : ℕ) :
    (frobeniusSubApproximation p a (n + 1)).1 -
        (frobeniusSubApproximation p a n).1 ∈
      Ideal.span {(p : WittVector p k) ^ n} := by
  rw [frobeniusSubApproximation]
  exact (Classical.choose_spec
    (frobenius_approximation_succ p a
      (frobeniusSubApproximation p a n) n
      (frobeniusSubApproximation p a n).property)).2

private theorem frobenius_approximation_smod
    (a : WittVector p k) (n : ℕ) :
    (frobeniusSubApproximation p a n).1 ≡
      (frobeniusSubApproximation p a (n + 1)).1
        [SMOD ((Ideal.span {(p : WittVector p k)}) ^ n • ⊤ :
          Submodule (WittVector p k) (WittVector p k))] := by
  apply SModEq.symm
  rw [SModEq.sub_mem]
  simpa only [Ideal.span_singleton_pow, smul_eq_mul, Ideal.mul_top] using
    frobenius_sub_approximation p a n

set_option maxHeartbeats 2000000 in
-- The limit argument unfolds the adic Cauchy and separatedness interfaces.
theorem frobenius_sub_surjective :
    Function.Surjective
      (fun x : WittVector p k ↦ frobenius x - x) := by
  intro a
  let I : Ideal (WittVector p k) := Ideal.span {(p : WittVector p k)}
  let f : ℕ → WittVector p k := fun n ↦
    (frobeniusSubApproximation p a n).1
  have hf : AdicCompletion.IsAdicCauchy I (WittVector p k) f :=
    (AdicCompletion.isAdicCauchy_iff I (WittVector p k) f).2 fun n ↦ by
      exact frobenius_approximation_smod p a n
  obtain ⟨x, hx⟩ := IsPrecomplete.prec
    (WittVector.isAdicCompleteIdealSpanP.toIsPrecomplete)
    (f := f) hf
  refine ⟨x, ?_⟩
  rw [← sub_eq_zero]
  apply IsHausdorff.haus
    WittVector.isAdicCompleteIdealSpanP.toIsHausdorff
  intro n
  change frobenius x - x - a ≡ 0
    [SMOD ((Ideal.span {(p : WittVector p k)}) ^ n • ⊤ :
      Submodule (WittVector p k) (WittVector p k))]
  apply SModEq.zero.mpr
  have hxn := hx n
  have happ := (frobeniusSubApproximation p a n).property
  change f n ≡ x [SMOD _] at hxn
  change frobenius x - x - a ∈
    (Ideal.span {(p : WittVector p k)}) ^ n •
      (⊤ : Submodule (WittVector p k) (WittVector p k))
  have hxn' : f n - x ∈ Ideal.span {(p : WittVector p k) ^ n} := by
    have hxn0 := SModEq.sub_mem.mp hxn
    simpa only [SModEq, Ideal.span_singleton_pow, smul_eq_mul,
      Ideal.mul_top] using hxn0
  have hdiff : x - f n ∈ Ideal.span {(p : WittVector p k) ^ n} := by
    simpa only [neg_sub] using
      (Ideal.span {(p : WittVector p k) ^ n}).neg_mem hxn'
  have hfrob : frobenius (x - f n) ∈
      Ideal.span {(p : WittVector p k) ^ n} := by
    rw [Ideal.mem_span_singleton] at hdiff ⊢
    obtain ⟨d, hd⟩ := hdiff
    refine ⟨frobenius d, ?_⟩
    have hfixp : frobenius (p : WittVector p k) = p := by simp
    calc
      frobenius (x - f n) = frobenius ((p : WittVector p k) ^ n * d) :=
        congrArg frobenius hd
      _ = (p : WittVector p k) ^ n * frobenius d := by
        rw [map_mul, map_pow, hfixp]
  simp only [Ideal.span_singleton_pow, smul_eq_mul, Ideal.mul_top]
  rw [show frobenius x - x - a =
      (frobenius (f n) - f n - a) +
        (frobenius (x - f n) - (x - f n)) by
    rw [map_sub]
    ring]
  exact (Ideal.span {(p : WittVector p k) ^ n}).add_mem happ
    ((Ideal.span {(p : WittVector p k) ^ n}).sub_mem hfrob hdiff)

end

end WittVector
