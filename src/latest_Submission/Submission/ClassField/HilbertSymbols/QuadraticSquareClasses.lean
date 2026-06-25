import Submission.ClassField.HilbertSymbols.QuadraticHilbert

/-!
# Milne, Class Field Theory, Section III.4: quadratic square classes

Milne observes that the quadratic conic indicator depends only on its two
arguments modulo nonzero squares.  This file makes that assertion literal by
descending the indicator to the quotient of `Kˣ` by its subgroup of squares.
-/

namespace Submission.CField.HSymbol

variable {K : Type*} [Field K]

/-- The group of nonzero square classes of a field. -/
abbrev QuadraticSquareClass (K : Type*) [Field K] :=
  Kˣ ⧸ Subgroup.square Kˣ

private theorem units_sq_rel {a b : Kˣ}
    (h : QuotientGroup.leftRel (Subgroup.square Kˣ) a b) :
    ∃ u : Kˣ, b = a * u ^ 2 := by
  have hsquare : IsSquare (a⁻¹ * b) :=
    Subgroup.mem_square.mp (QuotientGroup.leftRel_apply.mp h)
  rcases hsquare with ⟨u, hu⟩
  refine ⟨u, ?_⟩
  rw [pow_two, ← hu]
  simp

/-- Descend the second argument of the quadratic indicator to square
classes. -/
private noncomputable def hilbertSignRight (a : Kˣ) :
    QuadraticSquareClass K → ℤˣ :=
  fun q ↦ Quotient.liftOn' q
    (fun b : Kˣ ↦ quadraticHilbertSign (a : K) (b : K)) (by
      intro b c hbc
      obtain ⟨u, rfl⟩ := units_sq_rel hbc
      simpa using
        (hilbert_sign_sq
          (a : K) (b : K) (u : K) u.ne_zero).symm)

/-- The quadratic conic indicator as a function of two nonzero square
classes. -/
noncomputable def hilbertSignSquare :
    QuadraticSquareClass K → QuadraticSquareClass K → ℤˣ :=
  fun q ↦ Quotient.liftOn' q hilbertSignRight (by
    intro a c hac
    funext qb
    induction qb using QuotientGroup.induction_on with
    | _ b =>
        obtain ⟨u, rfl⟩ := units_sq_rel hac
        simpa [hilbertSignRight] using
          (quadratic_sign_sq
            (a : K) (b : K) (u : K) u.ne_zero).symm)

@[simp]
theorem hilbert_sign_mk (a b : Kˣ) :
    hilbertSignSquare
        (QuotientGroup.mk a) (QuotientGroup.mk b) =
      quadraticHilbertSign (a : K) (b : K) :=
  rfl

/-- The descended quadratic indicator remains symmetric. -/
theorem hilbert_sign_comm
    (a b : QuadraticSquareClass K) :
    hilbertSignSquare a b =
      hilbertSignSquare b a := by
  induction a using QuotientGroup.induction_on with
  | _ a =>
      induction b using QuotientGroup.induction_on with
      | _ b =>
          simp only [hilbert_sign_mk]
          exact quadratic_sign_comm (a : K) (b : K)

end Submission.CField.HSymbol
