import Submission.ClassField.Shifting.CyclicTateShape
import Submission.ClassField.NormIndex.RestrictedQuotient
import Submission.ClassField.HasseNorm.ClassH1

/-!
# Herbrand multiplicativity in Theorem VII.4.3

The Chapter II Herbrand-quotient theorem requires its coefficient ring and
group in one universe.  We apply it after rescaling the integral
representations to `ULift ℤ`; the existing explicit Tate-degree comparison
then transports the resulting cardinal identity back to the integral
representations in the source statement.
-/

namespace Submission.CField.BLoc

open CategoryTheory CategoryTheory.Limits
open IsDedekindDomain NumberField Representation
open Submission.CField.Shifting
open Submission.CField.Ideles
open Submission.CField.ICohomo
open Submission.CField.HQuotie
open Submission.CField.NIndex
open Submission.CField.HNorm
open groupCohomology

noncomputable section

universe u

/-- Rescale every term and map of an integral short complex to `ULift ℤ`.
The underlying additive groups and functions are unchanged. -/
noncomputable def uliftShortComplex
    {G : Type u} [Group G]
    (X : ShortComplex (Rep.{u, 0, u} ℤ G)) :
    ShortComplex (Rep (ULift.{u} ℤ) G) :=
  ShortComplex.mk
    (uliftIntegralHom X.f)
    (uliftIntegralHom X.g) (by
      apply Rep.hom_ext
      apply Representation.IntertwiningMap.ext
      apply LinearMap.ext
      intro x
      change X.g (X.f x) = 0
      exact congrArg (fun f ↦ f x) X.zero)

/-- Rescaling an integral short complex preserves short exactness. -/
theorem ulift_short_exact
    {G : Type u} [Group G]
    (X : ShortComplex (Rep.{u, 0, u} ℤ G))
    (hX : X.ShortExact) :
    (uliftShortComplex X).ShortExact := by
  letI intRepModule (A : Rep.{u, 0, u} ℤ G) : Module ℤ A := A.hV2
  letI uliftRepModule
      (A : Rep.{u, u, u} (ULift.{u} ℤ) G) :
      Module (ULift.{u} ℤ) A := A.hV2
  let F : (Rep.{u, 0, u} ℤ G) ⥤ ModuleCat.{u} ℤ :=
    forget₂ (Rep.{u, 0, u} ℤ G) (ModuleCat.{u} ℤ)
  have hXF : (X.map F).ShortExact := hX.map_of_exact F
  apply ShortComplex.ShortExact.mk'
  · exact (forget₂ (Rep.{u, u, u} (ULift.{u} ℤ) G)
      (ModuleCat.{u} (ULift.{u} ℤ))).reflects_exact_of_faithful _ <|
      (ShortComplex.moduleCat_exact_iff _).2 (fun x hx ↦ by
        have hx' : X.g x = 0 := hx
        obtain ⟨y, hy⟩ :=
          (ShortComplex.moduleCat_exact_iff (X.map F)).1
            hXF.exact x hx'
        exact ⟨y, hy⟩)
  · rw [Rep.mono_iff_injective]
    exact (Rep.mono_iff_injective X.f).1 hX.mono_f
  · rw [Rep.epi_iff_surjective]
    exact (Rep.epi_iff_surjective X.g).1 hX.epi_g

private noncomputable def integralUlift2
    {G : Type u} [CommGroup G] [Fintype G]
    (A : Rep.{u, 0, u} ℤ G) (g : G)
    (hg : ∀ x, x ∈ Subgroup.zpowers g) :
    tateZero A ≃+
      groupCohomology (uliftIntegralRepresentation A) 2 :=
  (tateIntLift A).trans
    (tateCohomologyTwo
      (uliftIntegralRepresentation A) g hg).toAddEquiv

private noncomputable def integralUlift1
    {G : Type u} [CommGroup G] [Fintype G]
    (A : Rep.{u, 0, u} ℤ G) (g : G)
    (hg : ∀ x, x ∈ Subgroup.zpowers g) :
    tateNegOne A ≃+
      groupCohomology (uliftIntegralRepresentation A) 1 :=
  (tateULift A).trans
    (tateCohomologyNeg
      (uliftIntegralRepresentation A) g hg).toAddEquiv

set_option maxHeartbeats 5000000 in
-- The proof elaborates six dependent Tate/cohomology equivalences at once.
/-- The universe-polymorphic exact-quotient bridge in Theorem VII.4.3. -/
theorem herbrandExactBridge :
    HerbrandExactBridge.{u} := by
  intro K L _ _ _ _ _ _ _ _
  letI : Fintype Gal(L/K) := Fintype.ofFinite Gal(L/K)
  letI : CommGroup Gal(L/K) := IsCyclic.commGroup
  intro S e qU qI hU hI
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Gal(L/K))
  let U : Rep ℤ Gal(L/K) :=
    unitsPlacesRepresentation (K := K) (L := L) S
  let I : Rep ℤ Gal(L/K) :=
    idelesRepresentation (K := K) (L := L) S
  let C : Rep ℤ Gal(L/K) :=
    classCokernelRepresentation (K := K) (L := L)
  let f : U ⟶ I := restrictedPrincipalHom (K := K) (L := L) S
  let X₀ : ShortComplex (Rep ℤ Gal(L/K)) :=
    ShortComplex.mk f (cokernel.π f) (cokernel.condition f)
  have hX₀ : X₀.ShortExact := by
    apply ShortComplex.ShortExact.mk'
    · exact ShortComplex.exact_cokernel f
    · exact (Rep.mono_iff_injective f).2
        (restricted_principal_injective (K := K) (L := L) S)
    · infer_instance
  let X₁ : ShortComplex (Rep ℤ Gal(L/K)) :=
    ShortComplex.mk f (cokernel.π f ≫ e.hom) (by
      rw [← Category.assoc, cokernel.condition, zero_comp])
  let eX : X₀ ≅ X₁ :=
    ShortComplex.isoMk (Iso.refl _) (Iso.refl _) e
      (by simp [X₀, X₁])
      (by simp [X₀, X₁])
  have hX₁ : X₁.ShortExact :=
    ShortComplex.shortExact_of_iso eX hX₀
  let X := uliftShortComplex X₁
  have hX : X.ShortExact :=
    ulift_short_exact X₁ hX₁
  let AU := uliftIntegralRepresentation U
  let AI := uliftIntegralRepresentation I
  let AC := uliftIntegralRepresentation C
  let eU₂ := integralUlift2 U g hg
  let eU₁ := integralUlift1 U g hg
  let eI₂ := integralUlift2 I g hg
  let eI₁ := integralUlift1 I g hg
  let eC₂ := integralUlift2 C g hg
  let eC₁ := integralUlift1 C g hg
  letI : Finite (tateZero U) := hU.1
  letI : Finite (tateNegOne U) := hU.2.1
  letI : Finite (tateZero I) := hI.1
  letI : Finite (tateNegOne I) := hI.2.1
  letI : Finite (groupCohomology AU 2) :=
    Finite.of_equiv (tateZero U) eU₂.toEquiv
  letI : Finite (groupCohomology AU 1) :=
    Finite.of_equiv (tateNegOne U) eU₁.toEquiv
  letI : Finite (groupCohomology AI 2) :=
    Finite.of_equiv (tateZero I) eI₂.toEquiv
  letI : Finite (groupCohomology AI 1) :=
    Finite.of_equiv (tateNegOne I) eI₁.toEquiv
  have hUvalue : (herbrandQuotient AU : ℚ) = qU := by
    change (Nat.card (groupCohomology AU 2) : ℚ) /
      Nat.card (groupCohomology AU 1) = qU
    rw [← Nat.card_congr eU₂.toEquiv,
      ← Nat.card_congr eU₁.toEquiv]
    exact hU.2.2
  have hIvalue : (herbrandQuotient AI : ℚ) = qI := by
    change (Nat.card (groupCohomology AI 2) : ℚ) /
      Nat.card (groupCohomology AI 1) = qI
    rw [← Nat.card_congr eI₂.toEquiv,
      ← Nat.card_congr eI₁.toEquiv]
    exact hI.2.2
  letI : Finite (groupCohomology X.X₁ 1) := by
    change Finite (groupCohomology AU 1)
    infer_instance
  letI : Finite (groupCohomology X.X₁ 2) := by
    change Finite (groupCohomology AU 2)
    infer_instance
  letI : Finite (groupCohomology X.X₂ 1) := by
    change Finite (groupCohomology AI 1)
    infer_instance
  letI : Finite (groupCohomology X.X₂ 2) := by
    change Finite (groupCohomology AI 2)
    infer_instance
  have hfiniteC := herbrand_quotient_right hX g hg
  letI : Finite (groupCohomology X.X₃ 1) := hfiniteC.1
  letI : Finite (groupCohomology X.X₃ 2) := hfiniteC.2
  letI : Finite (groupCohomology AC 1) := by
    change Finite (groupCohomology X.X₃ 1)
    infer_instance
  letI : Finite (groupCohomology AC 2) := by
    change Finite (groupCohomology X.X₃ 2)
    infer_instance
  letI : Finite (tateZero C) :=
    Finite.of_equiv (groupCohomology AC 2) eC₂.symm.toEquiv
  letI : Finite (tateNegOne C) :=
    Finite.of_equiv (groupCohomology AC 1) eC₁.symm.toEquiv
  let qC : ℚ := (Nat.card (tateZero C) : ℚ) /
    Nat.card (tateNegOne C)
  have hC : HerbrandQuotientValue C qC :=
    ⟨inferInstance, inferInstance, rfl⟩
  have hCvalue : (herbrandQuotient AC : ℚ) = qC := by
    change (Nat.card (groupCohomology AC 2) : ℚ) /
      Nat.card (groupCohomology AC 1) = qC
    rw [← Nat.card_congr eC₂.toEquiv,
      ← Nat.card_congr eC₁.toEquiv]
  refine ⟨qC, hC, ?_⟩
  have hmul := herbrandQuotient_mul hX g hg
  have hmulQ := congrArg (fun z : ℚˣ ↦ (z : ℚ)) hmul
  change (herbrandQuotient AI : ℚ) =
    (herbrandQuotient AU : ℚ) * (herbrandQuotient AC : ℚ) at hmulQ
  simpa only [hIvalue, hUvalue, hCvalue] using hmulQ

end

end Submission.CField.BLoc
