import Submission.ClassField.NormCorrespondence.SubgroupOpenClosed
import Submission.ClassField.NormCorrespondence.LocalStatement

/-!
# Chapter I, Local Existence: established consequences

This file records the portion of Theorem 1.4 and Corollary 1.5 supplied by
Lemma 1.3 before the existence construction itself is available.
-/

namespace Submission.CField.LFTheory

noncomputable section

universe u

/-- Open finite-index subgroups are upward closed.  This is the subgroup-side
content of Corollary I.1.5(e). -/
theorem OFSubgro.mono
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {H I : Subgroup G} (hH : OFSubgro H) (hHI : H ≤ I) :
    OFSubgro I := by
  rcases hH with ⟨hHopen, hHfinite⟩
  letI : H.FiniteIndex := hHfinite
  exact ⟨Subgroup.isOpen_mono hHI hHopen, Subgroup.finiteIndex_of_le hHI⟩

section Recip

variable (K : Type u) [NontriviallyNormedField K]
  [IsUltrametricDist K] [ValuativeRel K] [IsNonarchimedeanLocalField K]

/-- The finite-level norm-residue isomorphism in Theorem I.1.1 makes every
norm group of a finite abelian subextension have finite index. -/
theorem FASubext.normgr_finin_local
    (hrec : LocalReciprocityLaw K) (L : FASubext K) :
    L.normGroup.FiniteIndex := by
  rcases hrec with ⟨φ, hφ, _⟩
  rcases hφ.2 L with ⟨e, _⟩
  letI : Finite Gal(L.finiteIntermediateField/K) := inferInstance
  letI : Finite (Kˣ ⧸ L.normGroup) :=
    Finite.of_equiv Gal(L.finiteIntermediateField/K) e.symm.toEquiv
  exact Subgroup.finiteIndex_of_finite_quotient

end Recip

variable (K : Type u) [NontriviallyNormedField K]
  [IsUltrametricDist K] [ValuativeRel K] [IsNonarchimedeanLocalField K]
  [Valuation.Compatible (NormedField.valuation (K := K))]

/-- The openness half of the forward implication in the Local Existence
Theorem.  Lemma I.1.3 supplies it for every local norm group once its finite
index is known. -/
theorem LGroup.open_fin_index
    {H : Subgroup Kˣ} [H.FiniteIndex]
    (hH : LGroup K H) : IsOpen (H : Set Kˣ) := by
  rcases hH with ⟨L, hL⟩
  letI : L.normGroup.FiniteIndex := by
    exact hL.symm ▸ (inferInstance : H.FiniteIndex)
  letI : (normSubgroup K L.1).FiniteIndex := by
    change L.normGroup.FiniteIndex
    infer_instance
  rw [← hL]
  exact norm_subgroup K L.1

omit [Valuation.Compatible (NormedField.valuation (K := K))] in
/-- Theorem I.1.1 implies that every local norm group has finite index. -/
theorem LGroup.fin_index_localrecipro
    {H : Subgroup Kˣ} (hrec : LocalReciprocityLaw K)
    (hH : LGroup K H) : H.FiniteIndex := by
  rcases hH with ⟨L, hL⟩
  rw [← hL]
  exact L.normgr_finin_local K hrec

/-- If finite index has been established for all local norm groups, Lemma
I.1.3 proves the full forward implication of Theorem I.1.4. -/
theorem existence_forward_index
    (hfinite : ∀ H : Subgroup Kˣ,
      LGroup K H → H.FiniteIndex) :
    ∀ H : Subgroup Kˣ,
      LGroup K H → OFSubgro H := by
  intro H hH
  letI : H.FiniteIndex := hfinite H hH
  exact ⟨hH.open_fin_index K, inferInstance⟩

/-- The full forward implication of Theorem I.1.4 follows from the Local
Recip Law and Lemma I.1.3. -/
theorem local_existence_reciprocity
    (hrec : LocalReciprocityLaw K) :
    ∀ H : Subgroup Kˣ,
      LGroup K H → OFSubgro H := by
  apply existence_forward_index K
  intro H hH
  exact hH.fin_index_localrecipro K hrec

/-- Combining Theorem I.1.1 with Lemma I.1.3, the norm group of every finite
abelian subextension is open and of finite index. -/
theorem FASubext.normgr_openf_indel
    (hrec : LocalReciprocityLaw K) (L : FASubext K) :
    OFSubgro L.normGroup := by
  letI : L.normGroup.FiniteIndex :=
    L.normgr_finin_local K hrec
  letI : (normSubgroup K L.1).FiniteIndex := by
    change L.normGroup.FiniteIndex
    infer_instance
  exact ⟨norm_subgroup K L.1, inferInstance⟩

end


end Submission.CField.LFTheory
