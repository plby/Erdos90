import Towers.ClassField.Shifting.NormTransitivity
import Mathlib.Algebra.Category.ModuleCat.Kernels
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import Mathlib.Algebra.Homology.ShortComplex.SnakeLemma

/-!
# Milne, Class Field Theory, Theorem II.3.10: exceptional dimension shift

The norm is natural from coinvariants to invariants.  Applying the snake lemma
to this natural transformation and a short exact sequence whose middle norm is
an isomorphism identifies degree-minus-one Tate cohomology of the quotient with
degree-zero Tate cohomology of the kernel.
-/

namespace Towers.CField.Shifting

open CategoryTheory CategoryTheory.Limits Rep

noncomputable section

universe u

variable {k G : Type u} [CommRing k] [Group G] [Fintype G]

/-- The norm maps form a natural transformation from coinvariants to
invariants. -/
noncomputable def normNatTrans :
    Rep.coinvariantsFunctor.{u} k G ⟶ Rep.invariantsFunctor.{u} k G where
  app A := ModuleCat.ofHom (normCoinvariantsInvariants A)
  naturality A B f := by
    apply Rep.coinvariantsFunctor_hom_ext
    apply ModuleCat.hom_ext
    ext x
    apply Subtype.ext
    change B.ρ.norm (f.hom x) = f.hom (A.ρ.norm x)
    exact congrArg (fun q : A ⟶ B => q.hom x) (Rep.norm_comm f)

/-- The snake diagram obtained by applying coinvariants, invariants, and the
norm natural transformation to a short exact sequence. -/
noncomputable def normSnakeInput
    (X : ShortComplex (Rep.{u} k G)) (hX : X.ShortExact) :
    ShortComplex.SnakeInput (ModuleCat.{u} k) := by
  let L₁ := X.map (Rep.coinvariantsFunctor k G)
  let L₂ := X.map (Rep.invariantsFunctor k G)
  let v₁₂ := X.mapNatTrans (normNatTrans (k := k) (G := G))
  have h₁ := (Functor.preservesFiniteColimits_iff_forall_exact_map_and_epi
    (F := Rep.coinvariantsFunctor k G)).mp inferInstance X hX
  have h₂ := (Functor.preservesFiniteLimits_iff_forall_exact_map_and_mono
    (F := Rep.invariantsFunctor k G)).mp inferInstance X hX
  exact {
    L₀ := {
      f := kernel.map v₁₂.τ₁ v₁₂.τ₂ L₁.f L₂.f v₁₂.comm₁₂
      g := kernel.map v₁₂.τ₂ v₁₂.τ₃ L₁.g L₂.g v₁₂.comm₂₃
      zero := by
        rw [← cancel_mono (kernel.ι v₁₂.τ₃)]
        simp only [ShortComplex.map_X₁, ShortComplex.map_X₃,
          ShortComplex.map_X₂, Category.assoc, kernel.lift_ι,
          kernel.lift_ι_assoc]
        calc
          (kernel.ι v₁₂.τ₁ ≫ L₁.f) ≫ L₁.g =
              kernel.ι v₁₂.τ₁ ≫ (L₁.f ≫ L₁.g) :=
            Category.assoc _ _ _
          _ = 0 := by rw [L₁.zero, comp_zero]
          _ = 0 ≫ kernel.ι v₁₂.τ₃ := zero_comp.symm }
    L₁ := L₁
    L₂ := L₂
    L₃ := {
      f := cokernel.map v₁₂.τ₁ v₁₂.τ₂ L₁.f L₂.f v₁₂.comm₁₂
      g := cokernel.map v₁₂.τ₂ v₁₂.τ₃ L₁.g L₂.g v₁₂.comm₂₃
      zero := by
        rw [← cancel_epi (cokernel.π v₁₂.τ₁)]
        simp only [ShortComplex.map_X₁, ShortComplex.map_X₃,
          ShortComplex.map_X₂, cokernel.π_desc_assoc, Category.assoc,
          cokernel.π_desc]
        calc
          L₂.f ≫ (L₂.g ≫ cokernel.π v₁₂.τ₃) =
              (L₂.f ≫ L₂.g) ≫ cokernel.π v₁₂.τ₃ :=
            (Category.assoc _ _ _).symm
          _ = 0 := by rw [L₂.zero, zero_comp]
          _ = cokernel.π v₁₂.τ₁ ≫ 0 := comp_zero.symm }
    v₀₁ := {
      τ₁ := kernel.ι v₁₂.τ₁
      τ₂ := kernel.ι v₁₂.τ₂
      τ₃ := kernel.ι v₁₂.τ₃ }
    v₁₂ := v₁₂
    v₂₃ := {
      τ₁ := cokernel.π v₁₂.τ₁
      τ₂ := cokernel.π v₁₂.τ₂
      τ₃ := cokernel.π v₁₂.τ₃ }
    h₀ := by
      apply ShortComplex.isLimitOfIsLimitπ <;>
        exact (KernelFork.isLimitMapConeEquiv _ _).2 (kernelIsKernel _)
    h₃ := by
      apply ShortComplex.isColimitOfIsColimitπ <;>
        exact (CokernelCofork.isColimitMapCoconeEquiv _ _).2 (cokernelIsCokernel _)
    L₁_exact := h₁.1
    epi_L₁_g := h₁.2
    L₂_exact := h₂.1
    mono_L₂_f := h₂.2 }

set_option maxHeartbeats 500000 in
-- Composing the componentwise snake kernels and cokernels needs extra elaboration.
/-- The exceptional Tate dimension shift attached to a short exact sequence
whose middle term has vanishing Tate cohomology in degrees `-1` and `0`. -/
noncomputable def isoShortExact
    (X : ShortComplex (Rep.{u} k G)) (hX : X.ShortExact)
    (hneg : Subsingleton (tateCohomologyOne X.X₂))
    (hzero : Subsingleton (tateCohomologyZero X.X₂)) :
    tateCohomologyOne X.X₃ ≃ₗ[k] tateCohomologyZero X.X₁ := by
  let S := normSnakeInput X hX
  letI : Subsingleton (tateCohomologyOne X.X₂) := hneg
  letI : Subsingleton (tateCohomologyZero X.X₂) := hzero
  have h₀ : IsZero S.L₀.X₂ :=
    (ModuleCat.isZero_of_subsingleton
      (ModuleCat.of k (tateCohomologyOne X.X₂))).of_iso
        (ModuleCat.kernelIsoKer S.v₁₂.τ₂)
  have h₃ : IsZero S.L₃.X₂ :=
    (ModuleCat.isZero_of_subsingleton
      (ModuleCat.of k (tateCohomologyZero X.X₂))).of_iso
        (ModuleCat.cokernelIsoRangeQuotient S.v₁₂.τ₂)
  let e : ModuleCat.of k (tateCohomologyOne X.X₃) ≅
      ModuleCat.of k (tateCohomologyZero X.X₁) :=
    (ModuleCat.kernelIsoKer S.v₁₂.τ₃).symm ≪≫
      S.δIso h₀ h₃ ≪≫
      ModuleCat.cokernelIsoRangeQuotient S.v₁₂.τ₁
  exact e.toLinearEquiv

end

end Towers.CField.Shifting
