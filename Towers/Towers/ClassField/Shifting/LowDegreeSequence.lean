import Towers.ClassField.Shifting.SplittingModule

/-!
# Milne, Class Field Theory, Theorem II.3.11: the low-degree exact-sequence step

This file isolates the formal long-exact-sequence argument in Tate's proof.
For a short exact sequence `0 -> C -> E -> I -> 0`, if `H¹(C) = 0`,
`H²(I) = 0`, and the boundary `H¹(I) -> H²(C)` is an isomorphism,
then `H¹(E) = H²(E) = 0`.
-/

namespace Towers.CField.Shifting

open CategoryTheory CategoryTheory.Limits Rep

noncomputable section

universe u

variable {k G : Type u} [CommRing k] [Group G]

/-- The exact-sequence step used in Theorem II.3.11 to prove that a splitting
module has vanishing first and second cohomology. -/
theorem middle_boundary_iso
    {X : ShortComplex (Rep.{u} k G)} (hX : X.ShortExact)
    (hC1 : IsZero (groupCohomology X.X₁ 1))
    (hI2 : IsZero (groupCohomology X.X₃ 2))
    [IsIso (groupCohomology.δ hX 1 2 rfl)] :
    IsZero (groupCohomology X.X₂ 1) ∧
      IsZero (groupCohomology X.X₂ 2) := by
  let S11 := groupCohomology.mapShortComplex₂ X 1
  let S12 := groupCohomology.mapShortComplex₃ hX (i := 1) (j := 2) rfl
  have hS11 : S11.Exact := groupCohomology.mapShortComplex₂_exact hX 1
  have hS12 : S12.Exact := groupCohomology.mapShortComplex₃_exact hX rfl
  haveI hmono1 : Mono S11.g := hS11.mono_g (hC1.eq_of_src _ _)
  haveI hmonoBoundary : Mono S12.g := by
    change Mono (groupCohomology.δ hX 1 2 rfl)
    infer_instance
  have hzero1 : S11.g = 0 := by
    change S12.f = 0
    exact hS12.mono_g_iff.mp inferInstance
  have hE1 : IsZero (groupCohomology X.X₂ 1) := by
    haveI : Mono (0 : groupCohomology X.X₂ 1 ⟶ groupCohomology X.X₃ 1) :=
      hzero1 ▸ hmono1
    exact IsZero.of_mono_zero (groupCohomology X.X₂ 1)
      (groupCohomology X.X₃ 1)
  let S21 := groupCohomology.mapShortComplex₁ hX (i := 1) (j := 2) rfl
  let S22 := groupCohomology.mapShortComplex₂ X 2
  have hS21 : S21.Exact := groupCohomology.mapShortComplex₁_exact hX rfl
  have hS22 : S22.Exact := groupCohomology.mapShortComplex₂_exact hX 2
  haveI hepiBoundary : Epi S21.f := by
    change Epi (groupCohomology.δ hX 1 2 rfl)
    infer_instance
  have hzero2 : S22.f = 0 := by
    change S21.g = 0
    exact hS21.epi_f_iff.mp inferInstance
  haveI hmono2 : Mono S22.g := hS22.mono_g hzero2
  have htargetZero : S22.g = 0 := hI2.eq_of_tgt _ _
  have hE2 : IsZero (groupCohomology X.X₂ 2) := by
    haveI : Mono (0 : groupCohomology X.X₂ 2 ⟶ groupCohomology X.X₃ 2) :=
      htargetZero ▸ hmono2
    exact IsZero.of_mono_zero (groupCohomology X.X₂ 2)
      (groupCohomology X.X₃ 2)
  exact ⟨hE1, hE2⟩

/-- Subgroupwise specialization of the preceding exact-sequence lemma to
Tate's splitting module.  The remaining arithmetic input in Milne's proof is
precisely that each displayed boundary map is an isomorphism. -/
theorem splitting_12_restricted
    [Finite G] (C : Rep.{u} k G)
    (X : ShortComplex (Rep.{u} k G)) (hX : X.ShortExact)
    (hX1 : X.X₁ = C)
    (hC1 : ∀ H : Subgroup G,
      IsZero (groupCohomology (Rep.res H.subtype C) 1))
    (hI2 : ∀ H : Subgroup G,
      IsZero (groupCohomology (Rep.res H.subtype X.X₃) 2))
    (hboundary : ∀ H : Subgroup G,
      IsIso (groupCohomology.δ
        (hX.map_of_exact (Rep.resFunctor H.subtype)) 1 2 rfl)) :
    ∀ H : Subgroup G,
      IsZero (groupCohomology (Rep.res H.subtype X.X₂) 1) ∧
        IsZero (groupCohomology (Rep.res H.subtype X.X₂) 2) := by
  subst hX1
  intro H
  let hXH := hX.map_of_exact (Rep.resFunctor H.subtype)
  letI : IsIso (groupCohomology.δ hXH 1 2 rfl) := hboundary H
  exact middle_boundary_iso hXH (hC1 H) (hI2 H)

/-- The preceding criterion for the concrete splitting-module sequence
constructed from a normalized cocycle. -/
theorem splitting_12_iso
    {G : Type} [Group G] [Finite G]
    (C : Rep ℤ G) (φ : groupCohomology.cocycles₂ C)
    (hφ : φ (1, 1) = 0)
    (hC1 : ∀ H : Subgroup G,
      IsZero (groupCohomology (Rep.res H.subtype C) 1))
    (hI2 : ∀ H : Subgroup G,
      IsZero (groupCohomology
        (Rep.res H.subtype (augmentationIdealRep (G := G))) 2))
    (hboundary : ∀ H : Subgroup G,
      IsIso (groupCohomology.δ
        ((splitting_sequence_short C φ hφ).map_of_exact
          (Rep.resFunctor H.subtype)) 1 2 rfl)) :
    ∀ H : Subgroup G,
      IsZero (groupCohomology
          (Rep.res H.subtype (splittingModule C φ hφ)) 1) ∧
        IsZero (groupCohomology
          (Rep.res H.subtype (splittingModule C φ hφ)) 2) := by
  intro H
  let hXH := (splitting_sequence_short C φ hφ).map_of_exact
    (Rep.resFunctor H.subtype)
  letI : IsIso (groupCohomology.δ hXH 1 2 rfl) := hboundary H
  exact middle_boundary_iso hXH (hC1 H) (hI2 H)

end

end Towers.CField.Shifting
