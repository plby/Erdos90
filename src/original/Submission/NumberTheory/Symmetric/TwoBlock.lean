import Mathlib

namespace Submission.NumberTheory

open MvPolynomial

namespace TBSymmet

/-- Evaluation at the first `n` elementary symmetric polynomials. -/
noncomputable def elementaryEval (σ R : Type*) [CommRing R] [Fintype σ] (n : ℕ) :
    MvPolynomial (Fin n) R →ₐ[R] MvPolynomial σ R :=
  (symmetricSubalgebra σ R).val.comp (esymmAlgHom σ R n)

theorem elementaryEval_apply
    {σ R : Type*} [CommRing R] [Fintype σ] (n : ℕ)
    (q : MvPolynomial (Fin n) R) :
    elementaryEval σ R n q = aeval (fun i : Fin n => esymm σ R (i + 1)) q := by
  exact esymmAlgHom_apply q

theorem elementaryEval_injective
    {σ R : Type*} [CommRing R] [Fintype σ] {n : ℕ}
    (hcard : n ≤ Fintype.card σ) :
    Function.Injective (elementaryEval σ R n) := by
  intro p q hpq
  apply esymmAlgHom_injective R hcard
  apply Subtype.ext
  exact hpq

theorem elementary_eval_symmetric
    {σ R : Type*} [CommRing R] [Fintype σ] {n : ℕ}
    (hcard : Fintype.card σ ≤ n) {p : MvPolynomial σ R}
    (hp : p.IsSymmetric) :
    ∃ q : MvPolynomial (Fin n) R, elementaryEval σ R n q = p := by
  obtain ⟨q, hq⟩ := esymmAlgHom_surjective R hcard ⟨p, hp⟩
  exact ⟨q, congrArg Subtype.val hq⟩

/-- Substitute the elementary symmetric polynomials separately in two blocks of variables.
The outer variables form the first block; the coefficient polynomials form the second. -/
noncomputable def blockElementaryEval (R : Type*) [CommRing R] (m n : ℕ)
    (q : MvPolynomial (Fin m) (MvPolynomial (Fin n) R)) :
    MvPolynomial (Fin m) (MvPolynomial (Fin n) R) :=
  elementaryEval (Fin m) (MvPolynomial (Fin n) R) m
    (MvPolynomial.map (elementaryEval (Fin n) R n).toRingHom q)

private theorem map_elementaryEval
    {R : Type*} [CommRing R] {m n : ℕ} (e : Equiv.Perm (Fin n))
    (q : MvPolynomial (Fin m) (MvPolynomial (Fin n) R)) :
    MvPolynomial.map (MvPolynomial.rename e).toRingHom
        (elementaryEval (Fin m) (MvPolynomial (Fin n) R) m q) =
      elementaryEval (Fin m) (MvPolynomial (Fin n) R) m
        (MvPolynomial.map (MvPolynomial.rename e).toRingHom q) := by
  rw [elementaryEval_apply, elementaryEval_apply]
  induction q using MvPolynomial.induction_on with
  | C r => simp
  | add p q hp hq =>
      simp only [map_add, hp, hq]
  | mul_X p i hp =>
      simp only [map_mul, map_X, aeval_X, hp, MvPolynomial.map_esymm]

/-- Lemma 8: a polynomial symmetric separately in two finite blocks of variables is a
polynomial in the elementary symmetric polynomials of the two blocks. This iterated-polynomial
form is identified with a polynomial in `Fin m ⊕ Fin n` variables by `MvPolynomial.sumAlgEquiv`. -/
theorem block_elementary_eval
    {R : Type*} [CommRing R] {m n : ℕ}
    {p : MvPolynomial (Fin m) (MvPolynomial (Fin n) R)}
    (hx : p.IsSymmetric)
    (hy : ∀ e : Equiv.Perm (Fin n),
      MvPolynomial.map (MvPolynomial.rename e).toRingHom p = p) :
    ∃ q : MvPolynomial (Fin m) (MvPolynomial (Fin n) R),
      blockElementaryEval R m n q = p := by
  obtain ⟨qx, hqx⟩ :=
    elementary_eval_symmetric (R := MvPolynomial (Fin n) R)
      (σ := Fin m) (n := m) (by simp) hx
  have hcoeffSymmetric : ∀ d : Fin m →₀ ℕ, (qx.coeff d).IsSymmetric := by
    intro d e
    have hmapQx : MvPolynomial.map (MvPolynomial.rename e).toRingHom qx = qx := by
      apply elementaryEval_injective (R := MvPolynomial (Fin n) R)
        (σ := Fin m) (n := m) (by simp)
      calc
        elementaryEval (Fin m) (MvPolynomial (Fin n) R) m
            (MvPolynomial.map (MvPolynomial.rename e).toRingHom qx) =
            MvPolynomial.map (MvPolynomial.rename e).toRingHom
              (elementaryEval (Fin m) (MvPolynomial (Fin n) R) m qx) :=
          (map_elementaryEval e qx).symm
        _ = MvPolynomial.map (MvPolynomial.rename e).toRingHom p := congrArg _ hqx
        _ = p := hy e
        _ = elementaryEval (Fin m) (MvPolynomial (Fin n) R) m qx := hqx.symm
    have := congrArg (MvPolynomial.coeff d) hmapQx
    simpa [MvPolynomial.coeff_map] using this
  have hpreimage : ∀ c : MvPolynomial (Fin n) R,
      c.IsSymmetric → ∃ r, elementaryEval (Fin n) R n r = c := by
    intro c hc
    exact elementary_eval_symmetric (R := R) (σ := Fin n)
      (n := n) (by simp) hc
  classical
  let liftCoeff : MvPolynomial (Fin n) R → MvPolynomial (Fin n) R := fun c =>
    if hzero : c = 0 then 0
    else if hc : c.IsSymmetric then Classical.choose (hpreimage c hc) else 0
  have hliftCoeff_zero : liftCoeff 0 = 0 := by simp [liftCoeff]
  have hliftCoeff (c : MvPolynomial (Fin n) R) (hc : c.IsSymmetric) :
      elementaryEval (Fin n) R n (liftCoeff c) = c := by
    by_cases hzero : c = 0
    · simp [liftCoeff, hzero]
    · simp only [liftCoeff, hzero, ↓reduceDIte, hc]
      exact Classical.choose_spec (hpreimage c hc)
  let q := qx.mapRange liftCoeff hliftCoeff_zero
  have hmapQ : MvPolynomial.map (elementaryEval (Fin n) R n).toRingHom q = qx := by
    apply MvPolynomial.ext
    intro d
    rw [MvPolynomial.coeff_map]
    change elementaryEval (Fin n) R n (liftCoeff (MvPolynomial.coeff d qx)) = _
    exact hliftCoeff _ (hcoeffSymmetric d)
  refine ⟨q, ?_⟩
  rw [blockElementaryEval, hmapQ, hqx]

end TBSymmet

end Submission.NumberTheory
