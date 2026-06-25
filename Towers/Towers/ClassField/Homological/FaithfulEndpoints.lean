import Towers.ClassField.Homological.ExtendedSnakeLemma

/-!
# Milne, Class Field Theory, Lemma II.A.1: source-faithful endpoints

This file extends Mathlib's six-object snake sequence by the two endpoint
objects which occur explicitly in Milne's statement.
-/

namespace Towers.CField.Homological

open CategoryTheory CategoryTheory.Limits Category

universe u v

variable {C : Type u} [Category.{v} C] [Abelian C]

namespace ESnake

variable (S : ShortComplex.SnakeInput C)

lemma kernel_condition_vertical :
    kernel.ι S.L₁.f ≫ S.v₁₂.τ₁ = 0 := by
  rw [← cancel_mono S.L₂.f, assoc, S.v₁₂.comm₁₂]
  simp

/-- The map `Ker(L₁.f) ⟶ Ker(v₁₂.τ₁)` at the left end of Milne's
extended snake sequence. -/
noncomputable def leftMap : kernel S.L₁.f ⟶ S.L₀.X₁ :=
  S.h₀τ₁.lift (KernelFork.ofι (kernel.ι S.L₁.f) (kernel_condition_vertical S))

@[reassoc (attr := simp)]
lemma left_comp_vertical :
    leftMap S ≫ S.v₀₁.τ₁ = kernel.ι S.L₁.f :=
  S.h₀τ₁.fac _ WalkingParallelPair.zero

instance leftMap_mono : Mono (leftMap S) :=
  mono_of_mono_fac (left_comp_vertical S)

@[reassoc (attr := simp)]
lemma leftMap_comp : leftMap S ≫ S.L₀.f = 0 := by
  rw [← cancel_mono S.v₀₁.τ₂, assoc, ← S.v₀₁.comm₁₂]
  simp

/-- The new left-hand map is a kernel of the first map in the ordinary
snake sequence. -/
noncomputable def leftKernel :
    IsLimit (KernelFork.ofι (leftMap S) (leftMap_comp S)) :=
  KernelFork.IsLimit.ofι' _ _ fun {A} k hk ↦ by
    let l : A ⟶ kernel S.L₁.f := kernel.lift S.L₁.f (k ≫ S.v₀₁.τ₁) (by
      rw [assoc, S.v₀₁.comm₁₂, reassoc_of% hk, zero_comp])
    refine ⟨l, ?_⟩
    rw [← cancel_mono S.v₀₁.τ₁, assoc, left_comp_vertical]
    exact kernel.lift_ι _ _ _

/-- Exactness at `Ker(a)` in the extended sequence, including Milne's
explicit `Ker(f)` term. -/
lemma leftEndpointExact :
    (ShortComplex.mk (leftMap S) S.L₀.f (leftMap_comp S)).Exact :=
  ShortComplex.exact_of_f_is_kernel _ (leftKernel S)

lemma vertic_coker_condi :
    S.v₁₂.τ₃ ≫ cokernel.π S.L₂.g = 0 := by
  rw [← cancel_epi S.L₁.g, ← S.v₁₂.comm₂₃_assoc]
  simp

/-- The map `Coker(v₁₂.τ₃) ⟶ Coker(L₂.g)` at the right end of
Milne's extended snake sequence. -/
noncomputable def rightMap : S.L₃.X₃ ⟶ cokernel S.L₂.g :=
  S.h₃τ₃.desc
    (CokernelCofork.ofπ (cokernel.π S.L₂.g) (vertic_coker_condi S))

@[reassoc (attr := simp)]
lemma vertical_comp_right :
    S.v₂₃.τ₃ ≫ rightMap S = cokernel.π S.L₂.g :=
  S.h₃τ₃.fac _ WalkingParallelPair.one

instance rightMap_epi : Epi (rightMap S) :=
  epi_of_epi_fac (vertical_comp_right S)

@[reassoc (attr := simp)]
lemma comp_rightMap : S.L₃.g ≫ rightMap S = 0 := by
  rw [← cancel_epi S.v₂₃.τ₂, S.v₂₃.comm₂₃_assoc]
  simp

/-- The new right-hand map is a cokernel of the last map in the ordinary
snake sequence. -/
noncomputable def rightCokernel :
    IsColimit (CokernelCofork.ofπ (rightMap S) (comp_rightMap S)) :=
  CokernelCofork.IsColimit.ofπ' _ _ fun {A} k hk ↦ by
    let l : cokernel S.L₂.g ⟶ A := cokernel.desc S.L₂.g (S.v₂₃.τ₃ ≫ k) (by
      rw [← S.v₂₃.comm₂₃_assoc, hk, comp_zero])
    refine ⟨l, ?_⟩
    rw [← cancel_epi S.v₂₃.τ₃, ← assoc, vertical_comp_right]
    exact cokernel.π_desc _ _ _

/-- Exactness at `Coker(c)` in the extended sequence, including Milne's
explicit `Coker(g')` term. -/
lemma rightEndpointExact :
    (ShortComplex.mk S.L₃.g (rightMap S) (comp_rightMap S)).Exact :=
  ShortComplex.exact_of_g_is_cokernel _ (rightCokernel S)

/-- The eight nonzero objects of Milne's extended snake sequence:
`Ker(f) ⟶ Ker(a) ⟶ Ker(b) ⟶ Ker(c) ⟶ Coker(a) ⟶ Coker(b) ⟶
Coker(c) ⟶ Coker(g')`. -/
noncomputable abbrev composableArrows : ComposableArrows C 7 :=
  ((((((ComposableArrows.mk₁ (rightMap S)).precomp S.L₃.g).precomp S.L₃.f).precomp S.δ).precomp
      S.L₀.g).precomp S.L₀.f).precomp (leftMap S)

/-- **Lemma II.A.1 (the extended snake lemma), source-faithful form.**
The eight nonzero terms in Milne's displayed sequence are exact. -/
theorem exact : (composableArrows S).Exact :=
  ComposableArrows.exact_of_δ₀ (leftEndpointExact S).exact_toComposableArrows
    (ComposableArrows.exact_of_δ₀ S.L₀_exact.exact_toComposableArrows
      (ComposableArrows.exact_of_δ₀ S.L₁'_exact.exact_toComposableArrows
        (ComposableArrows.exact_of_δ₀ S.L₂'_exact.exact_toComposableArrows
          (ComposableArrows.exact_of_δ₀ S.L₃_exact.exact_toComposableArrows
            (rightEndpointExact S).exact_toComposableArrows))))

/-- The first arrow in the source-faithful sequence is monic, which supplies
the initial zero in Milne's display. -/
theorem mono_left : Mono (leftMap S) := inferInstance

/-- The last arrow in the source-faithful sequence is epic, which supplies
the terminal zero in Milne's display. -/
theorem epi_right : Epi (rightMap S) := inferInstance

end ESnake

end Towers.CField.Homological
