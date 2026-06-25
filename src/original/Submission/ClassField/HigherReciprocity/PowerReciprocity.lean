import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Chapter VIII, Section 5, Theorem 5.11: power reciprocity

The local Hilbert symbol for general `n` has not yet been constructed in the
project.  The proof of Theorem 5.11, however, uses only three precise facts:
skew-symmetry (5.7), the unramified residue-symbol formula (5.8), and the
global product formula (5.10).  `PRData` isolates exactly those
facts and the theorems below formalize Milne's finite-product argument.
-/

namespace Submission.CField.HRecip

open scoped BigOperators

variable {A V μ : Type*} [CommGroup A] [CommGroup μ] [DecidableEq V]

/-- The exact Hilbert-symbol data used by the proof of the Power Recip
Law.  `exceptionalSupport a` is `S(a) \ S`; thus disjointness of two such
supports is precisely the source hypothesis `S(a) ∩ S(b) = S`.

The values are abstract only because the general local Hilbert symbol is not
yet available.  No conclusion of Theorem 5.11 is included as a field. -/
structure PRData (A V μ : Type*)
    [CommGroup A] [CommGroup μ] [DecidableEq V] where
  distinguishedPlaces : Finset V
  exceptionalSupport : A → Finset V
  localHilbert : V → A → A → μ
  residueSymbol : A → A → μ
  localHilbert_skew : ∀ v a b,
    localHilbert v b a = (localHilbert v a b)⁻¹
  residue_symbol_product : ∀ a b,
    residueSymbol a b =
      ∏ v ∈ exceptionalSupport b, localHilbert v a b
  product_formula : ∀ a b,
    (∏ v ∈ exceptionalSupport a ∪ exceptionalSupport b,
        localHilbert v a b) *
      (∏ v ∈ distinguishedPlaces, localHilbert v a b) = 1

namespace PRData

variable (D : PRData A V μ)

/-- **Theorem VIII.5.11 (Power Recip Law).** -/
theorem powerReciprocity : (∀ a b : A, Disjoint (D.exceptionalSupport a) (D.exceptionalSupport b) →
      D.residueSymbol a b * (D.residueSymbol b a)⁻¹ =
        ∏ v ∈ D.distinguishedPlaces, D.localHilbert v b a) := by
  intro a b hdisjoint
  have houtside :
      D.residueSymbol a b * (D.residueSymbol b a)⁻¹ =
        ∏ v ∈ D.exceptionalSupport a ∪ D.exceptionalSupport b,
          D.localHilbert v a b := by
    rw [D.residue_symbol_product, D.residue_symbol_product]
    have hskewProduct :
        (∏ v ∈ D.exceptionalSupport a, D.localHilbert v b a) =
          (∏ v ∈ D.exceptionalSupport a, D.localHilbert v a b)⁻¹ := by
      calc
        (∏ v ∈ D.exceptionalSupport a, D.localHilbert v b a) =
            ∏ v ∈ D.exceptionalSupport a, (D.localHilbert v a b)⁻¹ :=
          Finset.prod_congr rfl fun v _ ↦ D.localHilbert_skew v a b
        _ = (∏ v ∈ D.exceptionalSupport a, D.localHilbert v a b)⁻¹ :=
          Finset.prod_inv_distrib _
    rw [hskewProduct, inv_inv, Finset.prod_union hdisjoint]
    ac_rfl
  rw [houtside]
  have hproduct := D.product_formula a b
  have hinverse :
      (∏ v ∈ D.exceptionalSupport a ∪ D.exceptionalSupport b,
          D.localHilbert v a b) =
        (∏ v ∈ D.distinguishedPlaces, D.localHilbert v a b)⁻¹ := by
    calc
      ∏ v ∈ D.exceptionalSupport a ∪ D.exceptionalSupport b,
          D.localHilbert v a b =
          (∏ v ∈ D.exceptionalSupport a ∪ D.exceptionalSupport b,
              D.localHilbert v a b) *
            ((∏ v ∈ D.distinguishedPlaces, D.localHilbert v a b) *
              (∏ v ∈ D.distinguishedPlaces, D.localHilbert v a b)⁻¹) := by
                simp
      _ = ((∏ v ∈ D.exceptionalSupport a ∪ D.exceptionalSupport b,
              D.localHilbert v a b) *
            (∏ v ∈ D.distinguishedPlaces, D.localHilbert v a b)) *
          (∏ v ∈ D.distinguishedPlaces, D.localHilbert v a b)⁻¹ := by
            ac_rfl
      _ = (∏ v ∈ D.distinguishedPlaces, D.localHilbert v a b)⁻¹ := by
            rw [hproduct, one_mul]
  rw [hinverse]
  calc
    (∏ v ∈ D.distinguishedPlaces, D.localHilbert v a b)⁻¹ =
        ∏ v ∈ D.distinguishedPlaces, (D.localHilbert v a b)⁻¹ :=
      (Finset.prod_inv_distrib _).symm
    _ = ∏ v ∈ D.distinguishedPlaces, D.localHilbert v b a :=
      Finset.prod_congr rfl fun v _ ↦ (D.localHilbert_skew v a b).symm

/-- The “moreover” clause of Theorem 5.11.  The source hypothesis `S(c)=S`
is expressed as the vanishing of `S(c) \ S`. -/
theorem moreover
    {b c : A} (hc : D.exceptionalSupport c = ∅) :
    D.residueSymbol c b =
      ∏ v ∈ D.distinguishedPlaces, D.localHilbert v b c := by
  have hdisjoint :
      Disjoint (D.exceptionalSupport c) (D.exceptionalSupport b) := by
    simp [hc]
  have h := D.powerReciprocity c b hdisjoint
  rw [D.residue_symbol_product b c, hc] at h
  simpa using h

/-- **Theorem VIII.5.11, complete source statement.** This packages both the
reciprocity identity and the source's “moreover” clause. The first identity
is proved separately by `powerReciprocity`. -/
def CompleteReciprocityLaw : Prop :=
  (∀ a b : A, Disjoint (D.exceptionalSupport a) (D.exceptionalSupport b) →
        D.residueSymbol a b * (D.residueSymbol b a)⁻¹ =
          ∏ v ∈ D.distinguishedPlaces, D.localHilbert v b a) ∧
    ∀ b c : A, D.exceptionalSupport c = ∅ →
      D.residueSymbol c b =
        ∏ v ∈ D.distinguishedPlaces, D.localHilbert v b c

theorem completeReciprocityLaw :
    D.CompleteReciprocityLaw := by
  refine ⟨D.powerReciprocity, ?_⟩
  intro b c hc
  exact D.moreover hc

end PRData

end Submission.CField.HRecip
