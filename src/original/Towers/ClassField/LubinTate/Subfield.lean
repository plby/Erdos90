import Mathlib.Topology.Algebra.Field
import Mathlib.Dynamics.FixedPoints.Topology
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.NumberTheory.Padics.Complex

/-!
# Class Field Theory, Chapter I, Lemma 3.12

Milne proves that an intermediate field of an algebraic closure of a local
field is closed by expressing it as the common fixed field of its Galois
group.  The theorem below isolates that topological fixed-point argument.
Applying it to the algebraic closure requires a compatible topology on the
algebraic closure together with the infinite Galois fixed-field theorem and
continuity of its automorphisms; that combined interface is not yet packaged
in Mathlib.
-/

namespace Towers.CField.LTate

noncomputable section

/-- A subfield characterized as the common fixed field of a family of
continuous endomorphisms of a Hausdorff topological field is closed. -/
theorem Subfield.closed_forall_fixed
    {L : Type*} [Field L] [TopologicalSpace L] [T2Space L]
    (E : Subfield L) (G : Set (L →+* L))
    (hcontinuous : ∀ σ ∈ G, Continuous σ)
    (hfixed : ∀ x : L, x ∈ E ↔ ∀ σ ∈ G, σ x = x) :
    IsClosed (E : Set L) := by
  have hcarrier :
      (E : Set L) = ⋂ σ : {σ // σ ∈ G}, {x : L | σ.1 x = x} := by
    ext x
    simp only [Set.mem_iInter, Set.mem_setOf_eq]
    constructor
    · intro hx σ
      exact (hfixed x).mp hx σ.1 σ.2
    · intro hx
      exact (hfixed x).mpr fun σ hσ ↦ hx ⟨σ, hσ⟩
  rw [hcarrier]
  exact isClosed_iInter fun σ ↦
    isClosed_eq (hcontinuous σ.1 σ.2) continuous_id

/-- The fixed-field argument in the form used by Milne: an intermediate field
of a Galois extension is closed when all algebra automorphisms are continuous.
-/
theorem intermediate_closed_continuous
    {K L : Type*} [Field K] [Field L] [Algebra K L] [IsGalois K L]
    [TopologicalSpace L] [T2Space L]
    (hcontinuous : ∀ σ : L ≃ₐ[K] L, Continuous σ)
    (E : IntermediateField K L) :
    IsClosed (E : Set L) := by
  have hfixed :
      (IntermediateField.fixedField E.fixingSubgroup : Set L) =
        ⋂ σ : E.fixingSubgroup,
          Function.fixedPoints (σ.1 : L → L) := by
    ext x
    simp only [SetLike.mem_coe, IntermediateField.mem_fixedField_iff,
      Set.mem_iInter, Function.mem_fixedPoints]
    constructor
    · intro hx σ
      exact hx σ.1 σ.2
    · intro hx σ hσ
      exact hx ⟨σ, hσ⟩
  rw [← InfiniteGalois.fixedField_fixingSubgroup E, hfixed]
  exact isClosed_iInter fun σ ↦
    isClosed_fixedPoints (hcontinuous σ.1)

/-- Lemma 3.12 for the fixed algebraic closure of `ℚ_p`: every intermediate
field is closed in the topology induced by the spectral norm. -/
theorem cl_intermediate_closed
    (p : ℕ) [Fact p.Prime]
    (E : IntermediateField ℚ_[p] (PadicAlgCl p)) :
    IsClosed (E : Set (PadicAlgCl p)) := by
  apply intermediate_closed_continuous
  intro σ
  apply Isometry.continuous
  rw [isometry_iff_dist_eq]
  intro x y
  rw [dist_eq_norm, dist_eq_norm, ← map_sub]
  change spectralNorm ℚ_[p] (PadicAlgCl p) (σ (x - y)) =
    spectralNorm ℚ_[p] (PadicAlgCl p) (x - y)
  exact (spectralNorm_eq_of_equiv σ (x - y)).symm

end

end Towers.CField.LTate
