import Mathlib.RingTheory.AdicCompletion.Algebra
import Mathlib.RingTheory.AdicCompletion.Completeness

/-!
# Quotients of an adic completion

This file records the algebraic form of Milne's Lemma 7.25.  The ideal in the
completion that plays the role of the `n`th power of the completed maximal
ideal is canonically the kernel of reduction modulo `I ^ n`.
-/

namespace Towers.NumberTheory.Milne

open AdicCompletion

noncomputable section

variable (R : Type*) [CommRing R] (I : Ideal R)

/-- Milne, Lemma 7.25, in the canonical `I`-adic-completion formulation:
reducing the completion modulo the kernel of reduction mod `I ^ n` recovers
`R / I ^ n`. -/
noncomputable def adicCompletionQuotient (n : ℕ) :
    (AdicCompletion I R ⧸ RingHom.ker (evalₐ I n).toRingHom) ≃+* R ⧸ I ^ n :=
  RingHom.quotientKerEquivOfSurjective (surjective_evalₐ I n)

/-- The quotient equivalence sends the class of a completed element to its
reduction modulo `I ^ n`. -/
@[simp]
theorem adic_equiv_mk (n : ℕ) (x : AdicCompletion I R) :
    adicCompletionQuotient R I n
        (Ideal.Quotient.mk (RingHom.ker (evalₐ I n).toRingHom) x) =
      evalₐ I n x :=
  rfl

/-- On elements coming from `R`, the quotient comparison is the ordinary
reduction map `R → R / I ^ n`. -/
@[simp]
theorem adic_completion_quotient (n : ℕ) (x : R) :
    adicCompletionQuotient R I n
        (Ideal.Quotient.mk (RingHom.ker (evalₐ I n).toRingHom) (of I R x)) =
      Ideal.Quotient.mk (I ^ n) x := by
  rw [adic_equiv_mk, evalₐ_of]

/-- For a finitely generated ideal, the kernel of reduction modulo `I ^ n`
is literally the `n`th power of the extension of `I` to its completion. -/
theorem ker_evalₐ_eq_map_pow (hI : I.FG) (n : ℕ) :
    RingHom.ker (evalₐ I n).toRingHom =
      (I.map (algebraMap R (AdicCompletion I R))) ^ n := by
  ext x
  rw [← Ideal.map_pow]
  change evalₐ I n x = 0 ↔
    x ∈ (Ideal.map (algebraMap R (AdicCompletion I R)) (I ^ n)).restrictScalars R
  rw [← Ideal.smul_top_eq_map]
  rw [AdicCompletion.pow_smul_top_eq_ker_eval hI]
  change evalₐ I n x = 0 ↔ eval I R n x = 0
  let heq : (I ^ n • ⊤ : Ideal R) = I ^ n := by ext y; simp
  let e : (R ⧸ (I ^ n • ⊤ : Ideal R)) ≃ₐ[R] R ⧸ I ^ n :=
    Ideal.quotientEquivAlgOfEq R heq
  change e (eval I R n x) = 0 ↔ eval I R n x = 0
  constructor
  · intro hx
    apply e.injective
    simpa using hx
  · intro hx
    rw [hx]
    exact e.map_zero

/-- Milne, Lemma 7.25, with the completed ideal written literally as the
extension of `I`: reduction identifies the quotient of the completion by its
`n`th power with `R / I ^ n`. -/
noncomputable def adicPowEquiv
    (hI : I.FG) (n : ℕ) :
    (AdicCompletion I R ⧸
        (I.map (algebraMap R (AdicCompletion I R))) ^ n) ≃+*
      R ⧸ I ^ n :=
  (Ideal.quotEquivOfEq (ker_evalₐ_eq_map_pow R I hI n).symm).trans
    (adicCompletionQuotient R I n)

/-- The equivalence with the literal extended-ideal power is still the
ordinary reduction map on completed elements. -/
@[simp]
theorem adic_completion_mk
    (hI : I.FG) (n : ℕ) (x : AdicCompletion I R) :
    adicPowEquiv R I hI n
        (Ideal.Quotient.mk
          ((I.map (algebraMap R (AdicCompletion I R))) ^ n) x) =
      evalₐ I n x := by
  rw [adicPowEquiv, RingEquiv.trans_apply,
    Ideal.quotEquivOfEq_mk, adic_equiv_mk]

/-- The source-oriented form of Milne's map
`R / I ^ n → R̂ / (I R̂) ^ n`. -/
noncomputable def adicBaseCompletion
    (hI : I.FG) (n : ℕ) :
    R ⧸ I ^ n ≃+*
      AdicCompletion I R ⧸
        (I.map (algebraMap R (AdicCompletion I R))) ^ n :=
  (adicPowEquiv R I hI n).symm

/-- Milne's source-oriented equivalence sends the class of `x` to the class
of its image in the completion. -/
@[simp]
theorem adic_base_mk
    (hI : I.FG) (n : ℕ) (x : R) :
    adicBaseCompletion R I hI n
        (Ideal.Quotient.mk (I ^ n) x) =
      Ideal.Quotient.mk
        ((I.map (algebraMap R (AdicCompletion I R))) ^ n) (of I R x) := by
  apply (adicPowEquiv R I hI n).injective
  change (adicPowEquiv R I hI n)
      ((adicPowEquiv R I hI n).symm
        (Ideal.Quotient.mk (I ^ n) x)) =
    (adicPowEquiv R I hI n)
      (Ideal.Quotient.mk
        ((I.map (algebraMap R (AdicCompletion I R))) ^ n) (of I R x))
  rw [RingEquiv.apply_symm_apply, adic_completion_mk,
    evalₐ_of]

end

end Towers.NumberTheory.Milne
