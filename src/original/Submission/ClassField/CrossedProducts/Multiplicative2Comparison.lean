import Submission.ClassField.CohomologyOps.NormalizedRepresentation
import Submission.ClassField.CrossedProducts.CohomologyClass

/-!
# Comparing the two presentations of degree-two cohomology

The crossed-product chapters use normalized multiplicative cocycles, while
the Tate-cohomology chapters use Mathlib's additive categorical
`groupCohomology.H2`.  This file identifies the two presentations.
-/

namespace Submission.CField.CProduca

open groupCohomology

variable {G M : Type}
  [Group G] [CommGroup M] [MulDistribMulAction G M]

private noncomputable abbrev additiveH2 :=
  groupCohomology.H2 (Rep.ofMulDistribMulAction G M)

/-- A normalized multiplicative cocycle determines an ordinary additive
degree-two cohomology class. -/
noncomputable def NMCocycl₂.toAdditiveH2
    (c : NMCocycl₂ (G := G) (M := M)) : additiveH2 (G := G) (M := M) :=
  H2π (Rep.ofMulDistribMulAction G M)
    (cocyclesOfIsMulCocycle₂ c.isMulCocycle₂)

private theorem NMCocycl₂.toAdditiveH2_eq_of_isCohomologous
    {c d : NMCocycl₂ (G := G) (M := M)}
    (h : MHTwo.IsCohomologous c d) :
    c.toAdditiveH2 = d.toAdditiveH2 := by
  rw [NMCocycl₂.toAdditiveH2,
    NMCocycl₂.toAdditiveH2, H2π_eq_iff]
  have hb := (coboundariesOfIsMulCoboundary₂ h).property
  convert hb using 1

/-- The comparison map from normalized multiplicative `H²` to Mathlib's
categorical `H²`. -/
noncomputable def multiplicative2Additive
    (x : MHTwo G M) : additiveH2 (G := G) (M := M) :=
  Quotient.lift NMCocycl₂.toAdditiveH2
    (fun _ _ h ↦ NMCocycl₂.toAdditiveH2_eq_of_isCohomologous h) x

@[simp]
theorem multiplicative_2_mk
    (c : NMCocycl₂ (G := G) (M := M)) :
    multiplicative2Additive (MHTwo.mk c) = c.toAdditiveH2 :=
  rfl

/-- The comparison map is additive after translating the multiplicative
group law on normalized cocycles. -/
theorem multiplicative_additive_mul
    (x y : MHTwo G M) :
    multiplicative2Additive (x * y) =
      multiplicative2Additive x + multiplicative2Additive y := by
  induction x, y using Quotient.inductionOn₂ with
  | _ c d =>
      change H2π _ (cocyclesOfIsMulCocycle₂ (c * d).isMulCocycle₂) =
        H2π _ (cocyclesOfIsMulCocycle₂ c.isMulCocycle₂) +
          H2π _ (cocyclesOfIsMulCocycle₂ d.isMulCocycle₂)
      rw [← map_add]
      apply congrArg (H2π (Rep.ofMulDistribMulAction G M))
      apply Subtype.ext
      rfl

@[simp]
theorem multiplicative_2_additive :
    multiplicative2Additive (1 : MHTwo G M) = 0 := by
  have h := multiplicative_additive_mul
    (1 : MHTwo G M) (1 : MHTwo G M)
  rw [one_mul] at h
  let a := multiplicative2Additive (1 : MHTwo G M)
  have ha : a = a + a := h
  have hz : 0 = a := by
    have hsub := congrArg (fun z ↦ z - a) ha
    simpa [add_assoc] using hsub
  exact hz.symm

/-- The comparison as a homomorphism into the multiplicative wrapper of
ordinary `H²`. -/
noncomputable def multiplicativeHHom :
    MHTwo G M →* Multiplicative (additiveH2 (G := G) (M := M)) where
  toFun x := Multiplicative.ofAdd (multiplicative2Additive x)
  map_one' := congrArg Multiplicative.ofAdd multiplicative_2_additive
  map_mul' x y := congrArg Multiplicative.ofAdd
    (multiplicative_additive_mul x y)

private theorem multiplicative_2_injective :
    Function.Injective
      (multiplicative2Additive (G := G) (M := M)) := by
  intro x y hxy
  obtain ⟨c, rfl⟩ := MHTwo.exists_mk_eq x
  obtain ⟨d, rfl⟩ := MHTwo.exists_mk_eq y
  rw [multiplicative_2_mk,
    multiplicative_2_mk] at hxy
  rw [MHTwo.mk_eq_iff]
  have hb := (H2π_eq_iff
    (cocyclesOfIsMulCocycle₂ c.isMulCocycle₂)
    (cocyclesOfIsMulCocycle₂ d.isMulCocycle₂)).1 hxy
  have hmul := isMulCoboundary₂_of_mem_coboundaries₂
    (G := G) (M := M)
    ((Additive.ofMul ∘ c) - (Additive.ofMul ∘ d)) hb
  convert hmul using 1

private theorem multiplicative_h_surjective :
    Function.Surjective
      (multiplicative2Additive (G := G) (M := M)) := by
  intro z
  obtain ⟨c, hc, hc0⟩ :=
    COps.normalized_cocycle_representation
      (Rep.ofMulDistribMulAction G M) z
  let f : G × G → M := Additive.toMul ∘ c
  have hf : IsMulCocycle₂ f :=
    isMulCocycle₂_of_mem_cocycles₂ (G := G) (M := M) c c.property
  have hf0 : f (1, 1) = 1 := congrArg Additive.toMul hc0
  let cn : NMCocycl₂ (G := G) (M := M) := {
    toFun := f
    isMulCocycle₂ := hf
    map_one_fst := fun g ↦ by
      rw [map_one_fst_of_isMulCocycle₂ hf]
      exact hf0
    map_one_snd := fun g ↦ by
      rw [map_one_snd_of_isMulCocycle₂ hf, hf0]
      simp
  }
  refine ⟨MHTwo.mk cn, ?_⟩
  rw [multiplicative_2_mk,
    NMCocycl₂.toAdditiveH2, ← hc]
  apply congrArg (H2π (Rep.ofMulDistribMulAction G M))
  apply Subtype.ext
  rfl

/-- Normalized multiplicative `H²` is canonically the multiplicative form
of Mathlib's categorical degree-two group cohomology. -/
noncomputable def multiplicativeHCohomology :
    MHTwo G M ≃* Multiplicative (additiveH2 (G := G) (M := M)) :=
  MulEquiv.ofBijective multiplicativeHHom
    ⟨fun _ _ h ↦ multiplicative_2_injective
        (congrArg Multiplicative.toAdd h),
      fun z ↦ by
        obtain ⟨x, hx⟩ := multiplicative_h_surjective
          (G := G) (M := M) z.toAdd
        exact ⟨x, congrArg Multiplicative.ofAdd hx⟩⟩

end Submission.CField.CProduca
