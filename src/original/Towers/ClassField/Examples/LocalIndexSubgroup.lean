import Towers.ClassField.NormCorrespondence.OpenIndexSubgroup
import Towers.ClassField.NormCorrespondence.FiniteIndexOpen

/-!
# Class Field Theory, Introduction, Theorem 0.9

Milne's introductory local class field theorem classifies finite abelian
extensions of a p-adic field by the finite-index subgroups of its
multiplicative group.  Chapter I phrases the correspondence using *open*
finite-index subgroups.  For characteristic-zero local fields this is no
restriction: every finite-index subgroup is open.
-/

namespace Towers.CField.Examples

open Towers.CField.LFTheory

noncomputable section

universe u

variable (K : Type u) [NontriviallyNormedField K]
  [IsUltrametricDist K] [ValuativeRel K] [IsNonarchimedeanLocalField K]
  [CharZero K]

/-- The subgroups occurring literally in Theorem 0.9: no separate openness
assumption is included. -/
abbrev LocalFiniteSubgroup :=
  {H : Subgroup Kˣ // H.FiniteIndex}

/-- **Theorem 0.9, exact statement.** Norm groups have finite index, and the
norm-group assignment is an inclusion-reversing bijection from finite
abelian subextensions of a fixed separable closure to finite-index
subgroups of the multiplicative group of K. -/
structure LocalIndexStatement : Prop where
  norm_group_index (L : FASubext K) :
    L.normGroup.FiniteIndex
  normGroup_bijective :
    Function.Bijective fun L : FASubext K ↦
      (⟨L.normGroup, norm_group_index L⟩ :
        LocalFiniteSubgroup K)
  inclusion_iff (L M : FASubext K) :
    L.intermediateField ≤ M.intermediateField ↔
      M.normGroup ≤ L.normGroup

/-- In a p-adic field the source's finite-index subgroup type agrees with
the open finite-index subgroup type used in Chapter I. -/
noncomputable def localIndexOpen :
    LocalFiniteSubgroup K ≃ LocalOpenSubgroup K where
  toFun H :=
    ⟨H.1, open_char_zero H.1 H.2, H.2⟩
  invFun H := ⟨H.1, H.2.2⟩
  left_inv H := by cases H; rfl
  right_inv H := by cases H; rfl

omit [IsUltrametricDist K] in
/-- Corollary I.1.5 gives exactly the introductory Theorem 0.9 after
removing the redundant word “open” from the subgroup side. -/
theorem of_localExistence
    (h15 : localOpenEquivalence K) :
    LocalIndexStatement K := by
  let e := localIndexOpen K
  let fOpen : FASubext K →
      LocalOpenSubgroup K :=
    fun L ↦ ⟨L.normGroup, h15.norm_group_open L⟩
  let fFinite : FASubext K →
      LocalFiniteSubgroup K :=
    fun L ↦ ⟨L.normGroup, (h15.norm_group_open L).2⟩
  have hcomm : e ∘ fFinite = fOpen := by
    funext L
    rfl
  refine {
    norm_group_index := fun L ↦ (h15.norm_group_open L).2
    normGroup_bijective := ?_
    inclusion_iff := h15.inclusion_iff }
  change Function.Bijective fFinite
  have hbij : Function.Bijective (e.symm ∘ fOpen) :=
    e.symm.bijective.comp h15.normGroup_bijective
  have hback : e.symm ∘ fOpen = fFinite := by
    funext L
    apply e.injective
    simpa only [Equiv.apply_symm_apply, Function.comp_apply] using
      congrFun hcomm L
  rwa [hback] at hbij

omit [IsUltrametricDist K] in
/-- The Chapter I norm correspondence and local existence theorem imply
the exact introductory classification. -/
theorem local_correspondence_existence
    (hNorm : LocalNormCorrespondence K)
    (hExistence : LocalExistenceTheorem K) :
    LocalIndexStatement K :=
  of_localExistence K
    (open_correspondence_existence K hNorm hExistence)

end

end Towers.CField.Examples
