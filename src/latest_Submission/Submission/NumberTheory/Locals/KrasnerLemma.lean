import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.Galois.GaloisClosure
import Mathlib.Algebra.Order.AbsoluteValue.Basic
import Mathlib.Algebra.Order.Ring.IsNonarchimedean
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Normed.Field.Krasner
import Mathlib.Analysis.Normed.Unbundled.SpectralNorm

/-!
# Krasner's lemma

This file proves the finite-Galois form of Milne's Proposition 7.60.  In the
usual application, the ambient field is a finite Galois subextension of an
algebraic closure containing the two elements.  Invariance of the absolute
value under base-field automorphisms follows from uniqueness of its extension.
-/

namespace Submission.NumberTheory.Milne

open IntermediateField

section

variable {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω]
  [FiniteDimensional K Ω] [IsGalois K Ω]

/-- Milne, Proposition 7.60 (Krasner's lemma), in a finite Galois ambient
extension.  If `α` is closer to `β` than to every distinct `K`-conjugate of
`α`, then adjoining `α` gives a subfield of the field obtained by adjoining
`β`.

The hypothesis `hinv` records the standard fact that the uniquely extended
absolute value is invariant under every `K`-automorphism of the ambient Galois
extension. -/
theorem krasner_le_adjoin
    (v : AbsoluteValue Ω ℝ) (hv : IsNonarchimedean v)
    (hinv : ∀ (σ : Ω ≃ₐ[K] Ω) (x : Ω), v (σ x) = v x)
    {α β : Ω}
    (hclose : ∀ σ : Ω ≃ₐ[K] Ω, σ α ≠ α → v (α - β) < v (σ α - α)) :
    K⟮α⟯ ≤ K⟮β⟯ := by
  rw [adjoin_simple_le_iff]
  rw [← IsGalois.fixedField_fixingSubgroup K⟮β⟯]
  rw [mem_fixedField_iff]
  intro σ hσ
  by_contra hne
  have hβ : σ β = β := by
    exact hσ ⟨β, mem_adjoin_simple_self K β⟩
  have hfirst : v (σ α - β) = v (α - β) := by
    calc
      v (σ α - β) = v (σ α - σ β) := by rw [hβ]
      _ = v (σ (α - β)) := by rw [map_sub σ]
      _ = v (α - β) := hinv σ (α - β)
  have hsecond : v (β - α) = v (α - β) := by
    rw [show β - α = -(α - β) by ring, v.map_neg]
  have hle : v (σ α - α) ≤ v (α - β) := by
    calc
      v (σ α - α) = v ((σ α - β) + (β - α)) := by ring_nf
      _ ≤ max (v (σ α - β)) (v (β - α)) := hv _ _
      _ = v (α - β) := by rw [hfirst, hsecond, max_self]
  exact (not_lt_of_ge hle) (hclose σ hne)

end

section CompleteAlgebraic

variable {K L : Type*} [NontriviallyNormedField K] [CompleteSpace K]
  [IsUltrametricDist K] [NormedField L] [NormedAlgebra K L]
  [Algebra.IsAlgebraic K L]

/-- Milne, Proposition 7.60, in Mathlib's classical complete-field form.
The splitting hypothesis says that all `K`-conjugates of `α` under
consideration lie in `L`.  This is a direct intermediate-field wrapper around
`IsKrasner.krasner`. -/
theorem krasner_complete
    {α β : L} (hαsep : (minpoly K α).Separable)
    (hsplits : ((minpoly K α).map (algebraMap K L)).Splits)
    (hβint : IsIntegral K β)
    (hclose : ∀ α' : L, IsConjRoot K α α' → α ≠ α' →
      ‖α - β‖ < ‖α - α'‖) :
    K⟮α⟯ ≤ K⟮β⟯ := by
  rw [adjoin_simple_le_iff]
  exact IsKrasner.krasner hαsep hsplits hβint hclose

/-- Milne, Proposition 7.60, with the separability hypothesis stated over
`K⟨β⟩` as in the book.  This is the spectral-norm proof of Krasner's lemma,
run with conjugacy over `K⟨β⟩`; those conjugates are also `K`-conjugates,
which lets us use the original closeness inequality. -/
theorem krasner_adjoin_complete
    {α β : L} [Normal K⟮β⟯ L]
    (hαsep : (minpoly K⟮β⟯ α).Separable)
    (hclose : ∀ α' : L, IsConjRoot K α α' → α ≠ α' →
      ‖α - β‖ < ‖α - α'‖) :
    K⟮α⟯ ≤ K⟮β⟯ := by
  have hβint : IsIntegral K β := Algebra.IsIntegral.isIntegral β
  letI : FiniteDimensional K K⟮β⟯ :=
    IntermediateField.adjoin.finiteDimensional hβint
  have : IsUltrametricDist L := IsUltrametricDist.of_normedAlgebra K
  have hβmem : β ∈ K⟮β⟯ := mem_adjoin_simple_self K β
  let β' : K⟮β⟯ := ⟨β, hβmem⟩
  let z := α - β
  have hzsep : IsSeparable K⟮β⟯ z :=
    Field.isSeparable_sub hαsep (isSeparable_algebraMap β')
  rw [adjoin_simple_le_iff]
  suffices z ∈ K⟮β⟯ by simpa [z, β'] using add_mem this β'.2
  have hzmem : z ∈ K⟮β⟯ ↔ z ∈ (⊥ : Subalgebra K⟮β⟯ L) := by
    simp [Algebra.mem_bot]
  rw [hzmem]
  by_contra hz
  obtain ⟨z', hne, hconj⟩ := (notMem_iff_exists_ne_and_isConjRoot hzsep
      (minpoly_sub_algebraMap_splits β'
        (IsIntegral.minpoly_splits_tower_top
          (Algebra.IsIntegral.isIntegral α)
          ((inferInstance : Normal K⟮β⟯ L).splits α)))).mp hz
  obtain ⟨σ, hσ⟩ := isConjRoot_iff_exists_algEquiv.mp hconj
  apply_fun σ.symm at hσ
  simp only [AlgEquiv.symm_apply_apply] at hσ
  have hlt : ‖z - z'‖ < ‖z - z'‖ :=
    calc
      _ ≤ max ‖z‖ ‖z'‖ := by
        simpa [norm_neg, sub_eq_add_neg] using
          (IsUltrametricDist.norm_add_le_max z (-z'))
      _ ≤ ‖α - β‖ := by
        simp only [NormedAlgebra.norm_eq_spectralNorm K, hσ, sup_le_iff]
        rw [← AlgEquiv.restrictScalars_apply K,
          ← spectralNorm_eq_of_equiv (σ.symm.restrictScalars K)]
        simp [z]
      _ < ‖α - (z' + β)‖ := by
        apply hclose (z' + β)
        · apply IsConjRoot.of_isScalarTower (L := K⟮β⟯)
            (Algebra.IsIntegral.isIntegral α)
          simpa [z, β'] using IsConjRoot.add_algebraMap β' hconj
        · simpa [z, sub_eq_iff_eq_add] using hne
      _ = ‖z - z'‖ := by congr 1; ring
  exact (lt_self_iff_false ‖z - z'‖).mp hlt

/-- Milne, Proposition 7.60, in the book's algebraic-closure setting.

Normality of `L` over `K⟮β⟯`, needed by the spectral-norm proof above, is
automatic because `L` is algebraically closed; it is therefore constructed
internally rather than exported as an additional hypothesis. -/
theorem krasner_complete_closed
    [IsAlgClosed L] {α β : L}
    (hαsep : (minpoly K⟮β⟯ α).Separable)
    (hclose : ∀ α' : L, IsConjRoot K α α' → α ≠ α' →
      ‖α - β‖ < ‖α - α'‖) :
    K⟮α⟯ ≤ K⟮β⟯ := by
  letI : Normal K⟮β⟯ L := normal_iff.mpr fun x ↦
    ⟨Algebra.IsAlgebraic.isIntegral.isIntegral x, IsAlgClosed.splits _⟩
  exact krasner_adjoin_complete hαsep hclose

end CompleteAlgebraic

section AlgebraicGalois

variable {K Ω : Type*} [NontriviallyNormedField K] [CompleteSpace K]
  [IsUltrametricDist K]
  [NormedField Ω] [NormedAlgebra K Ω] [Algebra.IsAlgebraic K Ω]
  [IsGalois K Ω]

/-- Milne, Proposition 7.60, in an algebraic Galois ambient extension of a
complete normed field.

The two elements lie in a finite Galois normal closure `E`.  On `E`, every
base-field automorphism preserves the norm because the latter is the spectral
norm; the finite-Galois form `krasner_le_adjoin` therefore applies.  Mapping
the resulting inclusion of intermediate fields back to `Ω` gives the claimed
inclusion.  In particular, this version applies directly to a separable
algebraic closure of a characteristic-zero complete field. -/
theorem krasner_adjoin_galois
    (hna : IsNonarchimedean (norm : Ω → ℝ))
    {α β : Ω}
    (hclose : ∀ σ : Ω ≃ₐ[K] Ω, σ α ≠ α → ‖α - β‖ < ‖σ α - α‖) :
    K⟮α⟯ ≤ K⟮β⟯ := by
  let E : FiniteGaloisIntermediateField K Ω :=
    FiniteGaloisIntermediateField.adjoin K ({α, β} : Set Ω)
  letI : NormedField E := SubfieldClass.toNormedField E.toIntermediateField
  have hαE : α ∈ E.toIntermediateField :=
    FiniteGaloisIntermediateField.subset_adjoin K ({α, β} : Set Ω)
      (Set.mem_insert α {β})
  have hβE : β ∈ E.toIntermediateField :=
    FiniteGaloisIntermediateField.subset_adjoin K ({α, β} : Set Ω)
      (Set.mem_insert_of_mem α (Set.mem_singleton β))
  let αE : E := ⟨α, hαE⟩
  let βE : E := ⟨β, hβE⟩
  have hnaE : IsNonarchimedean (norm : E → ℝ) := by
    intro x y
    exact hna x y
  have hinvE : ∀ (σ : E ≃ₐ[K] E) (x : E), ‖σ x‖ = ‖x‖ := by
    intro σ x
    calc
      ‖σ x‖ = ‖(algebraMap E Ω) (σ x)‖ := rfl
      _ = ‖(σ.liftNormal Ω) ((algebraMap E Ω) x)‖ := by
        rw [σ.liftNormal_commutes Ω x]
      _ = ‖(algebraMap E Ω) x‖ := by
        rw [NormedAlgebra.norm_eq_spectralNorm K,
          NormedAlgebra.norm_eq_spectralNorm K]
        exact (spectralNorm_eq_of_equiv (σ.liftNormal Ω) _).symm
      _ = ‖x‖ := rfl
  have hcloseE : ∀ σ : E ≃ₐ[K] E, σ αE ≠ αE →
      ‖αE - βE‖ < ‖σ αE - αE‖ := by
    intro σ hσ
    let σΩ : Ω ≃ₐ[K] Ω := σ.liftNormal Ω
    have hσα : σΩ α ≠ α := by
      intro h
      apply hσ
      apply Subtype.ext
      have hcomm := σ.liftNormal_commutes Ω αE
      exact hcomm.symm.trans (by simpa [σΩ, αE] using h)
    have hc := hclose σΩ hσα
    have hcomm := σ.liftNormal_commutes Ω αE
    have hσΩα : σΩ α = (σ αE : Ω) := by
      simpa [σΩ, αE] using hcomm
    rw [hσΩα] at hc
    simpa [αE, βE] using hc
  have hleE : K⟮αE⟯ ≤ K⟮βE⟯ :=
    krasner_le_adjoin (NormedField.toAbsoluteValue E) hnaE hinvE hcloseE
  have hlift := IntermediateField.map_mono E.toIntermediateField.val hleE
  change IntermediateField.lift K⟮αE⟯ ≤ IntermediateField.lift K⟮βE⟯ at hlift
  simpa [αE, βE, IntermediateField.lift_adjoin_simple] using hlift

end AlgebraicGalois

end Submission.NumberTheory.Milne
