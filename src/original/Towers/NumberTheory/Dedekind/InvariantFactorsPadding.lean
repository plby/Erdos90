import Towers.NumberTheory.Dedekind.InvariantFactorsCRT

/-!
# Milne, Algebraic Number Theory, padding prime-power cyclic decompositions

An exponent zero contributes the zero module `A / P ^ 0 = A / ⊤`.  We use this observation to
pad finite prime-primary cyclic decompositions to a common length before applying the CRT packing
of invariant factors.
-/

namespace Towers.NumberTheory.Milne

open scoped DirectSum

/-- Append one zero exponent to a tuple.  The indexing is chosen to agree with `finSuccEquiv`. -/
noncomputable def padExponentOne {n : ℕ} (e : Fin n → ℕ) : Fin (n + 1) → ℕ :=
  fun i => Option.rec 0 e (finSuccEquiv n i)

/-- Appending an exponent zero does not change a direct sum of prime-power quotient modules. -/
noncomputable def padDirectLinear
    (A : Type*) [CommRing A] (P : Ideal A)
    (n : ℕ) (e : Fin n → ℕ) :
    (⨁ j, A ⧸ P ^ e j) ≃ₗ[A]
      ⨁ j, A ⧸ P ^ padExponentOne e j := by
  classical
  let KIdeal : Option (Fin n) → Ideal A := fun
    | none => ⊤
    | some j => P ^ e j
  let EIdeal : Fin (n + 1) → Ideal A := fun j => P ^ padExponentOne e j
  have hIdeal : ∀ o, EIdeal ((finSuccEquiv n).symm o) = KIdeal o := by
    intro o
    cases o <;> simp [EIdeal, KIdeal, padExponentOne]
  let eReindex :
      (⨁ j, A ⧸ EIdeal j) ≃ₗ[A]
        ⨁ o, A ⧸ EIdeal ((finSuccEquiv n).symm o) :=
    DirectSum.lequivCongrLeft A (finSuccEquiv n)
  let eNormalize :
      (⨁ o, A ⧸ EIdeal ((finSuccEquiv n).symm o)) ≃ₗ[A]
        ⨁ o, A ⧸ KIdeal o :=
    DFinsupp.mapRange.linearEquiv fun o =>
      Submodule.quotEquivOfEq _ _ (hIdeal o)
  let eSplit :
      (⨁ o, A ⧸ KIdeal o) ≃ₗ[A]
        ((A ⧸ KIdeal none) × (⨁ j, A ⧸ KIdeal (some j))) :=
    DirectSum.lequivProdDirectSum (R := A)
  letI : Unique (A ⧸ KIdeal none) := Unique.mk' _
  let eSome :
      (⨁ j, A ⧸ KIdeal (some j)) ≃ₗ[A]
        ⨁ j, A ⧸ P ^ e j :=
    DFinsupp.mapRange.linearEquiv fun j =>
      Submodule.quotEquivOfEq _ _ (by simp [KIdeal])
  let eDrop :
      ((A ⧸ KIdeal none) × (⨁ j, A ⧸ KIdeal (some j))) ≃ₗ[A]
        ⨁ j, A ⧸ P ^ e j := by
    exact ((LinearEquiv.refl A (A ⧸ KIdeal none)).prodCongr eSome).trans
      (LinearEquiv.uniqueProd (R := A)
        (M := ⨁ j, A ⧸ P ^ e j) (M₂ := A ⧸ KIdeal none))
  exact (eReindex.trans eNormalize |>.trans eSplit |>.trans eDrop).symm

/-- Pad a tuple of exponents by any prescribed number of zeros. -/
theorem pad_direct_sum
    (A : Type*) [CommRing A] (P : Ideal A)
    (d k : ℕ) (e : Fin d → ℕ) :
    ∃ e' : Fin (d + k) → ℕ,
      Nonempty ((⨁ j, A ⧸ P ^ e j) ≃ₗ[A]
        ⨁ j, A ⧸ P ^ e' j) := by
  induction k with
  | zero =>
      simpa using ⟨e, Nonempty.intro (LinearEquiv.refl A _)⟩
  | succ k ih =>
      obtain ⟨e', ⟨h⟩⟩ := ih
      let e'' : Fin (d + (k + 1)) → ℕ := fun i =>
        padExponentOne e' (Fin.cast (by omega) i)
      refine ⟨e'', ⟨h ≪≫ₗ ?_⟩⟩
      exact (padDirectLinear A P (d + k) e') ≪≫ₗ
        DirectSum.lequivCongrLeft A (finCongr (by omega))

/-- Pad a prime-primary cyclic decomposition to any larger prescribed length. -/
theorem pad_direct_linear
    (A : Type*) [CommRing A] (P : Ideal A)
    (d n : ℕ) (hdn : d ≤ n) (e : Fin d → ℕ) :
    ∃ e' : Fin n → ℕ,
      Nonempty ((⨁ j, A ⧸ P ^ e j) ≃ₗ[A]
        ⨁ j, A ⧸ P ^ e' j) := by
  obtain ⟨e', ⟨h⟩⟩ :=
    pad_direct_sum A P d (n - d) e
  have hdn' : d + (n - d) = n := Nat.add_sub_of_le hdn
  let e'' : Fin n → ℕ := fun i => e' (Fin.cast hdn'.symm i)
  refine ⟨e'', ⟨h ≪≫ₗ ?_⟩⟩
  exact DirectSum.lequivCongrLeft A (finCongr hdn')

/-- A finite family of prime-primary cyclic decompositions can be padded to one common
rectangular length. -/
theorem rectangular_prime_columns
    (A : Type*) [CommRing A]
    (ι : Type*) [Finite ι]
    (P : ι → Ideal A) (d : ι → ℕ)
    (e : ∀ i, Fin (d i) → ℕ) :
    ∃ (n : ℕ) (e' : ι → Fin n → ℕ),
      Nonempty
        ((⨁ i, ⨁ j, A ⧸ P i ^ e i j) ≃ₗ[A]
          ⨁ i, ⨁ j, A ⧸ P i ^ e' i j) := by
  classical
  letI := Fintype.ofFinite ι
  let n := Finset.univ.sup d
  have hdn : ∀ i, d i ≤ n := by
    intro i
    exact Finset.le_sup (f := d) (Finset.mem_univ i)
  choose e' he' using fun i =>
    pad_direct_linear A (P i) (d i) n (hdn i) (e i)
  refine ⟨n, e', ⟨DFinsupp.mapRange.linearEquiv fun i => (he' i).some⟩⟩

end Towers.NumberTheory.Milne
