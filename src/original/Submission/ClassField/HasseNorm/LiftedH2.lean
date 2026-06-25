import Submission.ClassField.HasseNorm.GlobalComparison
import Submission.ClassField.CohomologyOps.NormalizedRepresentation
import Submission.ClassField.CrossedProducts.CohomologyClass
import Submission.ClassField.LocalBrauer.CohomologyTransport

/-!
# Multiplicative `H²` and universe-resized group cohomology

The existing crossed-product comparison uses the ordinary integral
representation and is consequently universe-zero.  This file proves the same
comparison for `uliftMulRepresentation`, allowing the universe-polymorphic
local-unit acyclicity theorems to feed the idèle decomposition.
-/

namespace Submission.CField.HNorm

open groupCohomology
open Submission.CField.COps
open Submission.CField.CProduca
open Submission.CField.LBrauer

noncomputable section

universe u

variable {G M : Type u} [Group G] [CommGroup M]
  [MulDistribMulAction G M]

private abbrev uliftAdditive2 :=
  H2 (uliftMulRepresentation (G := G) (M := M))

/-- A multiplicative two-cocycle, written additively in the resized
representation. -/
private def uliftCocyclesCocycle₂
    {f : G × G → M} (hf : IsMulCocycle₂ f) :
    cocycles₂ (uliftMulRepresentation (G := G) (M := M)) :=
  ⟨Additive.ofMul ∘ f,
    (mem_cocycles₂_iff
      (A := uliftMulRepresentation (G := G) (M := M)) _).2 hf⟩

/-- A multiplicative two-coboundary, written additively in the resized
representation. -/
private def uliftCoboundariesCoboundary₂
    {f : G × G → M} (hf : IsMulCoboundary₂ f) :
    coboundaries₂ (uliftMulRepresentation (G := G) (M := M)) :=
  ⟨Additive.ofMul ∘ f, Additive.ofMul ∘ hf.choose,
    funext fun p => congrArg Additive.ofMul (hf.choose_spec p.1 p.2)⟩

/-- Membership in resized additive coboundaries gives the corresponding
multiplicative coboundary. -/
private theorem isMulCoboundary₂_of_mem_uliftCoboundaries₂
    (f : G × G → Additive M)
    (hf : f ∈ coboundaries₂
      (uliftMulRepresentation (G := G) (M := M))) :
    IsMulCoboundary₂ (Additive.toMul ∘ f) := by
  rcases hf with ⟨x, rfl⟩
  exact ⟨Additive.toMul ∘ x, fun _ _ => rfl⟩

/-- A normalized multiplicative cocycle determines resized additive `H²`. -/
noncomputable def normalizedCocycleU
    (c : NMCocycl₂ (G := G) (M := M)) :
    uliftAdditive2 (G := G) (M := M) :=
  H2π (uliftMulRepresentation (G := G) (M := M))
    (uliftCocyclesCocycle₂ c.isMulCocycle₂)

private theorem normalized_cocycle_cohomologous
    {c d : NMCocycl₂ (G := G) (M := M)}
    (h : MHTwo.IsCohomologous c d) :
    normalizedCocycleU c =
      normalizedCocycleU d := by
  rw [normalizedCocycleU,
    normalizedCocycleU, H2π_eq_iff]
  have hb := (uliftCoboundariesCoboundary₂ h).property
  convert hb using 1

/-- The comparison map from multiplicative `H²` to resized ordinary
degree-two cohomology. -/
noncomputable def multiplicativeLiftAdditive
    (x : MHTwo G M) : uliftAdditive2 (G := G) (M := M) :=
  Quotient.lift normalizedCocycleU
    (fun _ _ h =>
      normalized_cocycle_cohomologous h) x

@[simp]
theorem multiplicative_additive_mk
    (c : NMCocycl₂ (G := G) (M := M)) :
    multiplicativeLiftAdditive (MHTwo.mk c) =
      normalizedCocycleU c :=
  rfl

theorem multiplicative_lift_additive
    (x y : MHTwo G M) :
    multiplicativeLiftAdditive (x * y) =
      multiplicativeLiftAdditive x +
        multiplicativeLiftAdditive y := by
  induction x, y using Quotient.inductionOn₂ with
  | _ c d =>
      change H2π _ (uliftCocyclesCocycle₂
          (c * d).isMulCocycle₂) =
        H2π _ (uliftCocyclesCocycle₂ c.isMulCocycle₂) +
          H2π _ (uliftCocyclesCocycle₂ d.isMulCocycle₂)
      rw [← map_add]
      apply congrArg (H2π (uliftMulRepresentation (G := G) (M := M)))
      apply Subtype.ext
      rfl

@[simp]
theorem multiplicative_u_additive :
    multiplicativeLiftAdditive
      (1 : MHTwo G M) = 0 := by
  have h := multiplicative_lift_additive
    (1 : MHTwo G M) (1 : MHTwo G M)
  rw [one_mul] at h
  let a := multiplicativeLiftAdditive (1 : MHTwo G M)
  have ha : a = a + a := h
  have hz : 0 = a := by
    have hsub := congrArg (fun z => z - a) ha
    simpa [add_assoc] using hsub
  exact hz.symm

/-- The comparison as a multiplicative homomorphism. -/
noncomputable def multiplicativeCohomologyHom :
    MHTwo G M →*
      Multiplicative (uliftAdditive2 (G := G) (M := M)) where
  toFun x := Multiplicative.ofAdd (multiplicativeLiftAdditive x)
  map_one' := congrArg Multiplicative.ofAdd
    multiplicative_u_additive
  map_mul' x y := congrArg Multiplicative.ofAdd
    (multiplicative_lift_additive x y)

private theorem multiplicative_additive_injective :
    Function.Injective
      (multiplicativeLiftAdditive (G := G) (M := M)) := by
  intro x y hxy
  obtain ⟨c, rfl⟩ := MHTwo.exists_mk_eq x
  obtain ⟨d, rfl⟩ := MHTwo.exists_mk_eq y
  rw [multiplicative_additive_mk,
    multiplicative_additive_mk] at hxy
  rw [MHTwo.mk_eq_iff]
  have hb := (H2π_eq_iff
    (uliftCocyclesCocycle₂ c.isMulCocycle₂)
    (uliftCocyclesCocycle₂ d.isMulCocycle₂)).1 hxy
  have hmul := isMulCoboundary₂_of_mem_uliftCoboundaries₂
    ((Additive.ofMul ∘ c) - (Additive.ofMul ∘ d)) hb
  convert hmul using 1

private theorem multiplicative_additive_surjective :
    Function.Surjective
      (multiplicativeLiftAdditive (G := G) (M := M)) := by
  intro z
  obtain ⟨c, hc, hc0⟩ :=
    normalized_cocycle_representation
      (uliftMulRepresentation (G := G) (M := M)) z
  let f : G × G → M := Additive.toMul ∘ c
  have hf : IsMulCocycle₂ f :=
    (mem_cocycles₂_iff
      (A := uliftMulRepresentation (G := G) (M := M)) c).1 c.property
  have hf0 : f (1, 1) = 1 := congrArg Additive.toMul hc0
  let cn : NMCocycl₂ (G := G) (M := M) :=
    { toFun := f
      isMulCocycle₂ := hf
      map_one_fst := fun g => by
        rw [map_one_fst_of_isMulCocycle₂ hf]
        exact hf0
      map_one_snd := fun g => by
        rw [map_one_snd_of_isMulCocycle₂ hf, hf0]
        simp }
  refine ⟨MHTwo.mk cn, ?_⟩
  rw [multiplicative_additive_mk,
    normalizedCocycleU, ← hc]
  apply congrArg (H2π (uliftMulRepresentation (G := G) (M := M)))
  apply Subtype.ext
  rfl

/-- Universe-polymorphic multiplicative `H²` is canonically the
multiplicative form of ordinary `H²` for `uliftMulRepresentation`. -/
noncomputable def multiplicativeUCohomology :
    MHTwo G M ≃*
      Multiplicative (uliftAdditive2 (G := G) (M := M)) :=
  MulEquiv.ofBijective multiplicativeCohomologyHom
    ⟨fun _ _ h => multiplicative_additive_injective
        (congrArg Multiplicative.toAdd h),
      fun z => by
        obtain ⟨x, hx⟩ := multiplicative_additive_surjective
          (G := G) (M := M) z.toAdd
        exact ⟨x, congrArg Multiplicative.ofAdd hx⟩⟩

/-- Multiplicative `H²` vanishing transfers to the universe-resized ordinary
group cohomology used by the idèle decomposition. -/
theorem ulift_subsingleton_multiplicative
    [Subsingleton (MHTwo G M)] :
    Subsingleton (H2 (uliftMulRepresentation (G := G) (M := M))) := by
  let e := multiplicativeUCohomology
    (G := G) (M := M)
  have hmul : Subsingleton
      (Multiplicative
        (H2 (uliftMulRepresentation (G := G) (M := M)))) :=
    e.symm.injective.subsingleton
  constructor
  intro x y
  exact congrArg Multiplicative.toAdd
    (@Subsingleton.elim _ hmul (Multiplicative.ofAdd x) (Multiplicative.ofAdd y))

/-- For a nontrivial finite cyclic action, surjectivity of the action norm
implies vanishing of resized ordinary `H²`. -/
theorem ulift_cohomology_subsingleton
    [Fintype G] {n : ℕ} [NeZero n] (hn : 1 < n)
    (e : Multiplicative (ZMod n) ≃* G)
    (hN : Function.Surjective (FMAct.norm G M)) :
    Subsingleton (H2 (uliftMulRepresentation (G := G) (M := M))) := by
  let eH2 : MHTwo G M ≃*
      FMAct.invariantsModNorm G M :=
    GroupH2.mulInvariantsMod (M := M) e hn
  have hrange : (FMAct.norm G M).range = ⊤ :=
    MonoidHom.range_eq_top.mpr hN
  have hquot : Subsingleton (FMAct.invariantsModNorm G M) := by
    change Subsingleton
      (FMAct.invariants G M ⧸ (FMAct.norm G M).range)
    rw [hrange]
    exact QuotientGroup.subsingleton_quotient_top
  letI : Subsingleton (MHTwo G M) :=
    ⟨fun x y => eH2.injective (@Subsingleton.elim _ hquot _ _)⟩
  exact ulift_subsingleton_multiplicative

end

end Submission.CField.HNorm
