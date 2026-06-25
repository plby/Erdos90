import Submission.ClassField.NormCorrespondence.Main
import Submission.ClassField.NormCorrespondence.StandardOpenSubgroups

/-!
# Class Field Theory, Theorem I.1.15: the finite-level argument

This file formalizes the two finite-level steps in the proof of the local
Kronecker--Weber theorem.  First, a standard subgroup contained in a norm
group is equal to that norm group when the index calculation in the text
shows that their indices agree.  Second, every finite abelian extension lies
in one of the resulting Lubin--Tate--unramified composita.
-/

namespace Submission.CField.NCorr

open Submission.CField.LFTheory

noncomputable section

universe u

variable {K : Type u} [NontriviallyNormedField K]

/-- The norm-residue isomorphism identifies the index of a norm group with
the degree of the corresponding finite abelian extension. -/
theorem finrank_induces_reciprocity
    (phi : Kˣ →* AbsoluteAbelianGalois K)
    (L : FASubext K)
    (hphi : InducesLocalReciprocity K phi L) :
    L.normGroup.index = Module.finrank K L.finiteIntermediateField := by
  obtain ⟨e, _⟩ := hphi
  rw [Subgroup.index_eq_card]
  exact (Nat.card_congr e.toEquiv).trans
    (IsGalois.card_aut_eq_finrank K L.finiteIntermediateField)

/-- A finite-index subgroup cannot be properly contained in a subgroup with
the same index. -/
theorem subgroup_index
    {G : Type*} [Group G] {H I : Subgroup G} [H.FiniteIndex]
    (hHI : H ≤ I) (hindex : H.index = I.index) : H = I := by
  apply le_antisymm hHI
  by_contra hIH
  have hstrict : H < I := lt_of_le_of_ne hHI (fun h ↦ hIH h.ge)
  have := Subgroup.index_strictAnti hstrict
  omega

section LocalField

variable (K : Type u) [NontriviallyNormedField K]
  [IsUltrametricDist K] [ValuativeRel K]
  [IsNonarchimedeanLocalField K]
  [Valuation.Compatible (NormedField.valuation (K := K))]

omit [IsUltrametricDist K]
  [Valuation.Compatible (NormedField.valuation (K := K))] in
/-- The index comparison in the first paragraph of the proof of Theorem
I.1.15.  Containment is condition (d) of the constructed Artin map, while
`hdegree` is the displayed degree/index calculation. -/
theorem standard_open_degree
    (phi : Kˣ →* AbsoluteAbelianGalois K)
    (hphi : ∀ L : FASubext K,
      InducesLocalReciprocity K phi L)
    (pi : Kˣ) (n m : ℕ) (L : FASubext K)
    (hcontain : standardOpenSubgroup K pi n m ≤ L.normGroup)
    (hdegree : (standardOpenSubgroup K pi n m).index =
      Module.finrank K L.finiteIntermediateField) :
    standardOpenSubgroup K pi n m = L.normGroup := by
  let H := standardOpenSubgroup K pi n m
  have hHne : H.index ≠ 0 := by
    rw [hdegree]
    exact (Module.finrank_pos (R := K)
      (M := L.finiteIntermediateField)).ne'
  letI : H.FiniteIndex := (Subgroup.finiteIndex_iff).2 hHne
  apply subgroup_index hcontain
  exact hdegree.trans
    (finrank_induces_reciprocity
      phi L (hphi L)).symm

/-- Every finite abelian extension occurs inside one of the finite
Lubin--Tate--unramified levels once condition (d) and the degree computation
have been established for those levels. -/
theorem standard_norm_level
    (phi : Kˣ →* AbsoluteAbelianGalois K)
    (hphi : ∀ L : FASubext K,
      InducesLocalReciprocity K phi L)
    (pi : Kˣ)
    (Knm : ℕ → ℕ → FASubext K)
    (hcontain : ∀ n m,
      standardOpenSubgroup K pi n m ≤ (Knm n m).normGroup)
    (hdegree : ∀ n m, (standardOpenSubgroup K pi n m).index =
      Module.finrank K (Knm n m).finiteIntermediateField)
    (L : FASubext K) :
    ∃ n, L.intermediateField ≤
      (Knm n L.normGroup.index).intermediateField := by
  have hfinite : L.normGroup.FiniteIndex := by
    obtain ⟨e, _⟩ := hphi L
    letI : Finite Gal(L.finiteIntermediateField/K) := inferInstance
    letI : Finite (Kˣ ⧸ L.normGroup) :=
      Finite.of_equiv Gal(L.finiteIntermediateField/K) e.symm.toEquiv
    exact Subgroup.finiteIndex_of_finite_quotient
  letI : L.normGroup.FiniteIndex := hfinite
  letI : (normSubgroup K L.finiteIntermediateField).FiniteIndex := by
    change L.normGroup.FiniteIndex
    infer_instance
  have hopen : IsOpen (L.normGroup : Set Kˣ) := by
    change IsOpen (normSubgroup K L.finiteIntermediateField : Set Kˣ)
    exact norm_subgroup K L.finiteIntermediateField
  obtain ⟨n, hn⟩ := standard_open_subgroup
    K L.normGroup hopen pi
  refine ⟨n, (intermediate_norm_group
    phi hphi L (Knm n L.normGroup.index)).2 ?_⟩
  rw [← standard_open_degree
    K phi hphi pi n L.normGroup.index (Knm n L.normGroup.index)
      (hcontain n L.normGroup.index) (hdegree n L.normGroup.index)]
  exact hn

end LocalField

end

end Submission.CField.NCorr
