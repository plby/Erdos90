import Towers.NumberTheory.Dedekind.InvariantFactorsPadding
import Mathlib.Data.Fin.SuccPred
import Mathlib.LinearAlgebra.Prod

/-!
# Rank padding for invariant-factor decompositions

An invariant-factor decomposition may be enlarged by putting copies of the unit ideal at the
left. These contribute zero cyclic summands and preserve the descending chain of ideals.
-/

namespace Towers.NumberTheory.Milne

open scoped DirectSum

/-- Add the unit ideal at the beginning of a finite family of ideals. -/
def prependTopFactor
    (A : Type*) [CommRing A] {n : ℕ} (b : Fin n → Ideal A) :
    Fin (n + 1) → Ideal A :=
  fun i ↦ Option.rec ⊤ b (finSuccEquiv n i)

@[simp]
theorem prepend_top_invariant
    (A : Type*) [CommRing A] {n : ℕ} (b : Fin n → Ideal A) :
    prependTopFactor A b 0 = ⊤ := by
  simp [prependTopFactor]

@[simp]
theorem prepend_top_succ
    (A : Type*) [CommRing A] {n : ℕ} (b : Fin n → Ideal A) (i : Fin n) :
    prependTopFactor A b i.succ = b i := by
  simp [prependTopFactor]

/-- Adding the unit ideal at the beginning preserves the invariant-factor ordering. -/
theorem prepend_top_antitone
    (A : Type*) [CommRing A] {n : ℕ} (b : Fin n → Ideal A)
    (hb : Antitone b) :
    Antitone (prependTopFactor A b) := by
  intro i j hij
  by_cases hi : i = 0
  · subst i
    exact le_top
  obtain ⟨i, rfl⟩ := Fin.exists_succ_eq_of_ne_zero hi
  have hj : j ≠ 0 := by
    intro hj
    subst j
    simp at hij
  obtain ⟨j, rfl⟩ := Fin.exists_succ_eq_of_ne_zero hj
  exact hb (Fin.succ_le_succ_iff.mp hij)

/-- The cyclic direct sum is unchanged when a unit ideal is prepended. -/
noncomputable def prependTopDirect
    (A : Type*) [CommRing A] {n : ℕ} (b : Fin n → Ideal A) :
    (⨁ i : Fin (n + 1), A ⧸ prependTopFactor A b i) ≃ₗ[A]
      ⨁ i : Fin n, A ⧸ b i := by
  letI : Unique (A ⧸ (⊤ : Ideal A)) :=
    Classical.choice (Submodule.unique_quotient_iff_eq_top.mpr rfl)
  let K : Option (Fin n) → Ideal A := fun
    | none => ⊤
    | some i => b i
  let E : Fin (n + 1) → Ideal A := prependTopFactor A b
  have hIdeal : ∀ o, E ((finSuccEquiv n).symm o) = K o := by
    intro o
    cases o <;> simp [E, K]
  let reindex :
      (⨁ i : Fin (n + 1), A ⧸ prependTopFactor A b i) ≃ₗ[A]
        ⨁ o : Option (Fin n), A ⧸ E ((finSuccEquiv n).symm o) :=
    DirectSum.lequivCongrLeft A (finSuccEquiv n)
  let normalize :
      (⨁ o : Option (Fin n), A ⧸ E ((finSuccEquiv n).symm o)) ≃ₗ[A]
        ⨁ o : Option (Fin n), A ⧸ K o :=
    DFinsupp.mapRange.linearEquiv fun o =>
      Submodule.quotEquivOfEq _ _ (hIdeal o)
  let split :
      (⨁ o : Option (Fin n), A ⧸ K o) ≃ₗ[A]
        (A ⧸ (⊤ : Ideal A)) × (⨁ i : Fin n, A ⧸ b i) :=
    DirectSum.lequivProdDirectSum (R := A)
  exact reindex ≪≫ₗ normalize ≪≫ₗ split ≪≫ₗ LinearEquiv.uniqueProd

/-- One may prepend any number of zero cyclic summands to an invariant-factor decomposition. -/
theorem invariant_decomposition_pad
    (A T : Type*) [CommRing A]
    [AddCommGroup T] [Module A T]
    {n : ℕ} (b : Fin n → Ideal A)
    (hb : Antitone b)
    (hT : Nonempty (T ≃ₗ[A] ⨁ i : Fin n, A ⧸ b i))
    (k : ℕ) :
    ∃ b' : Fin (n + k) → Ideal A,
      Antitone b' ∧ Nonempty (T ≃ₗ[A] ⨁ i : Fin (n + k), A ⧸ b' i) := by
  induction k with
  | zero =>
      exact ⟨b, hb, hT⟩
  | succ k ih =>
      obtain ⟨b', hb', ⟨e⟩⟩ := ih
      let b'' : Fin ((n + k) + 1) → Ideal A := prependTopFactor A b'
      have hb'' : Antitone b'' := prepend_top_antitone A b' hb'
      have he'' : Nonempty (T ≃ₗ[A] ⨁ i : Fin ((n + k) + 1), A ⧸ b'' i) :=
        ⟨e ≪≫ₗ (prependTopDirect A b').symm⟩
      exact ⟨b'', hb'', he''⟩

/-- Once the number of cyclic factors is bounded by `r`, padding produces exactly `r`
invariant-factor slots. -/
theorem invariant_decomposition_resize
    (A T : Type*) [CommRing A]
    [AddCommGroup T] [Module A T]
    {n r : ℕ} (b : Fin n → Ideal A)
    (hb : Antitone b)
    (hT : Nonempty (T ≃ₗ[A] ⨁ i : Fin n, A ⧸ b i))
    (hnr : n ≤ r) :
    ∃ b' : Fin r → Ideal A,
      Antitone b' ∧ Nonempty (T ≃ₗ[A] ⨁ i : Fin r, A ⧸ b' i) := by
  obtain ⟨b', hb', he'⟩ :=
    invariant_decomposition_pad A T b hb hT (r - n)
  rw [← Nat.add_sub_of_le hnr]
  exact ⟨b', hb', he'⟩

end Towers.NumberTheory.Milne
