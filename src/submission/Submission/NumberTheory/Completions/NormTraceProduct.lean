import Mathlib


/-!
# Milne, Chapter 8, Corollary 8.4

Norm and trace split as a product and a sum when a finite algebra decomposes
as a product.  This is the algebraic statement applied to the completion
decomposition in Proposition 8.2.
-/

namespace Submission.NumberTheory.Milne

noncomputable section

universe u v

variable {R S T L : Type*} [CommRing R] [CommRing S] [CommRing T] [CommRing L]
  [Algebra R S] [Algebra R T] [Algebra R L]
  [Module.Free R S] [Module.Free R T] [Module.Free R L]
  [Module.Finite R S] [Module.Finite R T] [Module.Finite R L]

/-- The norm of an element of a product algebra is the product of its norms. -/
theorem algebraNorm_prod (x : S × T) :
    Algebra.norm R x = Algebra.norm R x.1 * Algebra.norm R x.2 := by
  rw [Algebra.norm_apply, Algebra.norm_apply, Algebra.norm_apply]
  rw [← LinearMap.det_prodMap]
  congr 1

/-- The trace of an element of a product algebra is the sum of its traces. -/
theorem algebraTrace_prod (x : S × T) :
    Algebra.trace R (S × T) x =
      Algebra.trace R S x.1 + Algebra.trace R T x.2 :=
  Algebra.trace_prod_apply x

omit [Module.Free R L] [Module.Finite R L] in
/-- Milne's Corollary 8.4, transported across a two-factor algebra
decomposition.  Iterating this statement gives the formula for any finite
product of completions. -/
theorem norm_alg_prod (e : L ≃ₐ[R] S × T) (x : L) :
    Algebra.norm R x = Algebra.norm R (e x).1 * Algebra.norm R (e x).2 ∧
      Algebra.trace R L x =
        Algebra.trace R S (e x).1 + Algebra.trace R T (e x).2 := by
  constructor
  · rw [← Algebra.norm_eq_of_algEquiv e x, algebraNorm_prod]
  · rw [← Algebra.trace_eq_of_algEquiv e x, algebraTrace_prod]

section FiniteProduct

variable {I : Type u} [Fintype I]
variable (A : I → Type v) [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)]
  [∀ i, Module.Free R (A i)] [∀ i, Module.Finite R (A i)]

/-- Splitting an `Option`-indexed product into its distinguished factor and
the product of the remaining factors, as an algebra equivalence. -/
private def piOptionProd {J : Type u} (B : Option J → Type v)
    [∀ j, CommRing (B j)] [∀ j, Algebra R (B j)] :
    (∀ j, B j) ≃ₐ[R] B none × (∀ j, B (some j)) where
  __ := RingEquiv.piOptionEquivProd
  commutes' _ := rfl

/-- The norm and trace on a finite dependent product of finite free algebras
are respectively the product and sum of the component norms and traces. -/
theorem norm_trace_pi (x : ∀ i, A i) :
    Algebra.norm R x = ∏ i, Algebra.norm R (x i) ∧
      Algebra.trace R (∀ i, A i) x = ∑ i, Algebra.trace R (A i) (x i) := by
  classical
  revert A
  refine Fintype.induction_empty_option (P := fun I _ ↦
    ∀ (A : I → Type v) [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)]
      [∀ i, Module.Free R (A i)] [∀ i, Module.Finite R (A i)] (x : ∀ i, A i),
      Algebra.norm R x = ∏ i, Algebra.norm R (x i) ∧
        Algebra.trace R (∀ i, A i) x = ∑ i, Algebra.trace R (A i) (x i)) ?_ ?_ ?_ I
  · intro α β _ e h A _ _ _ _ x
    letI : Fintype α := Fintype.ofEquiv β e.symm
    let E : (∀ i : α, A (e i)) ≃ₐ[R] (∀ i : β, A i) := AlgEquiv.piCongrLeft R A e
    let y : ∀ i : α, A (e i) := E.symm x
    have hEy : E y = x := E.apply_symm_apply x
    have hycomp (i : α) : y i = x (e i) := by
      rw [← hEy]
      simp [E]
    have hy := h (fun i ↦ A (e i)) y
    constructor
    · calc
        Algebra.norm R x = Algebra.norm R (E y) := congr_arg (Algebra.norm R) hEy.symm
        _ = Algebra.norm R y := Algebra.norm_eq_of_algEquiv E y
        _ = ∏ i, Algebra.norm R (y i) := hy.1
        _ = ∏ i, Algebra.norm R (x i) :=
          Fintype.prod_equiv e _ _ (fun i ↦ congr_arg (Algebra.norm R) (hycomp i))
    · calc
        Algebra.trace R (∀ i, A i) x = Algebra.trace R (∀ i, A i) (E y) :=
          congr_arg (Algebra.trace R (∀ i, A i)) hEy.symm
        _ = Algebra.trace R (∀ i, A (e i)) y := Algebra.trace_eq_of_algEquiv E y
        _ = ∑ i, Algebra.trace R (A (e i)) (y i) := hy.2
        _ = ∑ i, Algebra.trace R (A i) (x i) :=
          Fintype.sum_equiv e _ _ (fun i ↦
            congr_arg (Algebra.trace R (A (e i))) (hycomp i))
  · intro A _ _ _ _ x
    constructor
    · rw [Algebra.norm_apply]
      have hmul : Algebra.lmul R (∀ i, A i) x = LinearMap.id := Subsingleton.elim _ _
      rw [hmul, LinearMap.det_id]
      simp
    · rw [Algebra.trace_apply]
      have hmul : Algebra.lmul R (∀ i, A i) x = 0 := Subsingleton.elim _ _
      rw [hmul, map_zero]
      simp
  · intro α _ h A _ _ _ _ x
    let E : (∀ i, A i) ≃ₐ[R] A none × (∀ i, A (some i)) := piOptionProd A
    have htail := h (fun i ↦ A (some i)) (fun i ↦ x (some i))
    constructor
    · calc
        Algebra.norm R x = Algebra.norm R (E x) := (Algebra.norm_eq_of_algEquiv E x).symm
        _ = Algebra.norm R (x none) * Algebra.norm R (fun i ↦ x (some i)) := algebraNorm_prod _
        _ = Algebra.norm R (x none) * ∏ i, Algebra.norm R (x (some i)) :=
          congrArg (Algebra.norm R (x none) * ·) htail.1
        _ = ∏ i, Algebra.norm R (x i) := by simp
    · calc
        Algebra.trace R (∀ i, A i) x = Algebra.trace R _ (E x) :=
          (Algebra.trace_eq_of_algEquiv E x).symm
        _ = Algebra.trace R (A none) (x none) +
            Algebra.trace R (∀ i, A (some i)) (fun i ↦ x (some i)) := algebraTrace_prod _
        _ = Algebra.trace R (A none) (x none) +
            ∑ i, Algebra.trace R (A (some i)) (x (some i)) :=
          congrArg (Algebra.trace R (A none) (x none) + ·) htail.2
        _ = ∑ i, Algebra.trace R (A i) (x i) := by simp

/-- Finite-product norm formula. -/
theorem algebraNorm_pi (x : ∀ i, A i) :
    Algebra.norm R x = ∏ i, Algebra.norm R (x i) :=
  (norm_trace_pi A x).1

/-- Finite-product trace formula. -/
theorem algebraTrace_pi (x : ∀ i, A i) :
    Algebra.trace R (∀ i, A i) x = ∑ i, Algebra.trace R (A i) (x i) :=
  (norm_trace_pi A x).2

omit [Module.Free R L] [Module.Finite R L] in
/-- Milne's Corollary 8.4 in finite-product form, transported across the
algebra decomposition supplied by Proposition 8.2. -/
theorem norm_alg_pi (e : L ≃ₐ[R] (∀ i, A i)) (x : L) :
    Algebra.norm R x = ∏ i, Algebra.norm R (e x i) ∧
      Algebra.trace R L x = ∑ i, Algebra.trace R (A i) (e x i) := by
  constructor
  · rw [← Algebra.norm_eq_of_algEquiv e x, algebraNorm_pi]
  · rw [← Algebra.trace_eq_of_algEquiv e x, algebraTrace_pi]

end FiniteProduct

end

end Submission.NumberTheory.Milne
