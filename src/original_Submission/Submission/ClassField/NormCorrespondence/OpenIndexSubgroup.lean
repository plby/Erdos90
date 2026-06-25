import Submission.ClassField.NormCorrespondence.Statement
import Submission.ClassField.NormCorrespondence.ExistenceConsequences

/-!
# Chapter I, Corollary 1.5

This file states the open-subgroup form of the local class field
correspondence and proves formally that it follows from Corollary 1.2 and the
Local Existence Theorem.
-/

namespace Submission.CField.LFTheory

noncomputable section

universe u

variable (K : Type u) [NontriviallyNormedField K]
  [IsUltrametricDist K] [ValuativeRel K] [IsNonarchimedeanLocalField K]

/-- Open finite-index subgroups of `Kˣ`. -/
abbrev LocalOpenSubgroup :=
  {H : Subgroup Kˣ // OFSubgro H}

/-- The conclusions of Corollary I.1.5, with the correspondence realized by
the actual norm-group map. -/
structure LocalOpenCorrespondence : Prop where
  /-- Norm groups of finite abelian extensions are open and of finite
  index. -/
  norm_group_open (L : FASubext K) :
    OFSubgro L.normGroup
  /-- (a) Finite abelian extensions correspond bijectively to open
  finite-index subgroups. -/
  normGroup_bijective : Function.Bijective fun L : FASubext K ↦
    (⟨L.normGroup, norm_group_open L⟩ :
      LocalOpenSubgroup K)
  /-- (b) The correspondence reverses inclusions. -/
  inclusion_iff (L L' : FASubext K) :
    L.intermediateField ≤ L'.intermediateField ↔
      L'.normGroup ≤ L.normGroup
  /-- (c) Composita correspond to intersections. -/
  norm_compositum (L L' : FASubext K) :
    ∃ M : FASubext K,
      FASubext.IsCompositum K M L L' ∧
        M.normGroup = L.normGroup ⊓ L'.normGroup
  /-- (d) Intersections correspond to generated products, represented by
  subgroup suprema. -/
  norm_intersection (L L' : FASubext K) :
    ∃ M : FASubext K,
      FASubext.IsIntersection K M L L' ∧
        M.normGroup = L.normGroup ⊔ L'.normGroup
  /-- (e) Every subgroup containing an open finite-index subgroup is again
  open and of finite index. -/
  supergroup_openFinite (H I : Subgroup Kˣ) :
    OFSubgro H → H ≤ I →
      OFSubgro I

/-- **Corollary I.1.5, statement.** Finite abelian extensions of `K`
correspond contravariantly to the open finite-index subgroups of `Kˣ`. -/
def localOpenEquivalence : Prop :=
  LocalOpenCorrespondence K

omit [IsUltrametricDist K] in
/-- Corollary I.1.2 and the Local Existence Theorem imply the complete
open-subgroup correspondence of Corollary I.1.5. -/
theorem open_correspondence_existence
    (hNorm : LocalNormCorrespondence K)
    (hExist : LocalExistenceTheorem K) :
    localOpenEquivalence K := by
  let hopen : ∀ L : FASubext K,
      OFSubgro L.normGroup := fun L ↦
    (hExist L.normGroup).1
      ((subextension_norm_local K L.normGroup).1
        ⟨L, rfl⟩)
  refine
    { norm_group_open := hopen
      normGroup_bijective := ?_
      inclusion_iff := hNorm.inclusion_iff
      norm_compositum := hNorm.norm_compositum
      norm_intersection := hNorm.norm_intersection
      supergroup_openFinite := fun _ _ hH hHI ↦ hH.mono hHI }
  constructor
  · intro L L' hLL'
    have hval : L.normGroup = L'.normGroup :=
      congrArg (fun H : LocalOpenSubgroup K => (H : Subgroup Kˣ)) hLL'
    exact hNorm.normGroup_bijective.1 (Subtype.ext hval)
  · intro H
    have hLocal : LGroup K H.1 :=
      (hExist H.1).2 H.2
    obtain ⟨L, hL⟩ :=
      (subextension_norm_local K H.1).2 hLocal
    refine ⟨L, Subtype.ext ?_⟩
    exact hL

omit [IsUltrametricDist K] [ValuativeRel K]
  [IsNonarchimedeanLocalField K] in
/-- Conversely, the open-subgroup correspondence contains the Local
Existence Theorem (for extensions in the same universe as `K`). -/
theorem localExistence
    (h15 : localOpenEquivalence K) : LocalExistenceTheorem K := by
  intro H
  constructor
  · intro hH
    have hSub : SubextensionNormGroup K H :=
      (subextension_norm_local K H).2 hH
    rcases hSub with ⟨L, rfl⟩
    exact h15.norm_group_open L
  · intro hH
    rcases h15.normGroup_bijective.2 ⟨H, hH⟩ with ⟨L, hL⟩
    apply (subextension_norm_local K H).1
    refine ⟨L, ?_⟩
    exact congrArg Subtype.val hL

end

end Submission.CField.LFTheory
