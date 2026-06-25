import Submission.ClassField.Shifting.GeneratorSub

/-!
# Milne, Class Field Theory, Corollary II.3.9

A homomorphism of cyclic-group modules with finite kernel and cokernel
preserves the Herbrand quotient.  The proof factors the homomorphism through
its image and applies Propositions II.3.6 and II.3.8 to the resulting two
short exact sequences.
-/

namespace Submission.CField.Shifting

open CategoryTheory CategoryTheory.Limits Representation

noncomputable section

universe u

variable {k G : Type u} [CommRing k] [CommGroup G] [Fintype G]

variable {M N : Rep k G}

/-- The canonical short complex `ker α → M → im α`. -/
private noncomputable abbrev imageShortComplex (α : M ⟶ N) :
    ShortComplex (Rep k G) :=
  ShortComplex.mk (kernel.ι α) (Abelian.factorThruImage α) <| by
    rw [← cancel_mono (Abelian.image.ι α)]
    simp

omit [Fintype G] in
/-- The canonical complex `ker α → M → im α` is short exact. -/
private theorem image_short_exact (α : M ⟶ N) :
    (imageShortComplex α).ShortExact := by
  let S : ShortComplex (Rep k G) :=
    ShortComplex.mk (kernel.ι α) (Abelian.coimage.π α) (cokernel.condition _)
  have hS : S.ShortExact := by
    apply ShortComplex.ShortExact.mk'
    · exact ShortComplex.exact_of_g_is_cokernel _
        (cokernelIsCokernel (kernel.ι α))
    · infer_instance
    · infer_instance
  let e : S ≅ imageShortComplex α :=
    ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Abelian.coimageIsoImage α)
      (by simp [S, imageShortComplex])
      (by
        dsimp [S, imageShortComplex]
        rw [← cancel_mono (Abelian.image.ι α)]
        simp [Category.assoc])
  exact ShortComplex.shortExact_of_iso e hS

/-- The canonical short complex `im α → N → coker α`. -/
private noncomputable abbrev imageCokernelComplex (α : M ⟶ N) :
    ShortComplex (Rep k G) :=
  ShortComplex.mk (Abelian.image.ι α) (cokernel.π α) (kernel.condition _)

omit [Fintype G] in
/-- The canonical complex `im α → N → coker α` is short exact. -/
private theorem cokernel_short_exact (α : M ⟶ N) :
    (imageCokernelComplex α).ShortExact := by
  apply ShortComplex.ShortExact.mk'
  · exact ShortComplex.exact_of_f_is_kernel _
      (kernelIsKernel (cokernel.π α))
  · dsimp [imageCokernelComplex]
    infer_instance
  · dsimp [imageCokernelComplex]
    infer_instance

set_option linter.unusedFintypeInType false in
/-- If the Herbrand quotient of the domain is defined, then so is that of
the codomain, provided the kernel and cokernel are finite. -/
theorem herbrand_codomain_cokernel
    (α : M ⟶ N) [Finite ↑(kernel α : Rep k G)] [Finite ↑(cokernel α : Rep k G)]
    (g : G) (hg : ∀ x, x ∈ Subgroup.zpowers g)
    [Finite (groupCohomology M 1)] [Finite (groupCohomology M 2)] :
    Finite (groupCohomology N 1) ∧ Finite (groupCohomology N 2) := by
  letI : Finite (groupCohomology (kernel α) 1) :=
    group_cohomology_module (kernel α) g hg
  letI : Finite (groupCohomology (kernel α) 2) :=
    cohomology_two_module (kernel α) g hg
  let X₁ := imageShortComplex α
  have hX₁ := image_short_exact α
  obtain ⟨hI₁, hI₂⟩ := herbrand_quotient_right hX₁ g hg
  letI : Finite (groupCohomology (Abelian.image α) 1) := hI₁
  letI : Finite (groupCohomology (Abelian.image α) 2) := hI₂
  letI : Finite (groupCohomology (cokernel α) 1) :=
    group_cohomology_module (cokernel α) g hg
  letI : Finite (groupCohomology (cokernel α) 2) :=
    cohomology_two_module (cokernel α) g hg
  exact herbrand_quotient_middle
    (cokernel_short_exact α) g hg

set_option linter.unusedFintypeInType false in
/-- If the Herbrand quotient of the codomain is defined, then so is that of
the domain, provided the kernel and cokernel are finite. -/
theorem herbrand_domain_cokernel
    (α : M ⟶ N) [Finite ↑(kernel α : Rep k G)] [Finite ↑(cokernel α : Rep k G)]
    (g : G) (hg : ∀ x, x ∈ Subgroup.zpowers g)
    [Finite (groupCohomology N 1)] [Finite (groupCohomology N 2)] :
    Finite (groupCohomology M 1) ∧ Finite (groupCohomology M 2) := by
  letI : Finite (groupCohomology (cokernel α) 1) :=
    group_cohomology_module (cokernel α) g hg
  letI : Finite (groupCohomology (cokernel α) 2) :=
    cohomology_two_module (cokernel α) g hg
  let X₂ := imageCokernelComplex α
  have hX₂ := cokernel_short_exact α
  obtain ⟨hI₁, hI₂⟩ := herbrand_quotient_left hX₂ g hg
  letI : Finite (groupCohomology (Abelian.image α) 1) := hI₁
  letI : Finite (groupCohomology (Abelian.image α) 2) := hI₂
  letI : Finite (groupCohomology (kernel α) 1) :=
    group_cohomology_module (kernel α) g hg
  letI : Finite (groupCohomology (kernel α) 2) :=
    cohomology_two_module (kernel α) g hg
  exact herbrand_quotient_middle
    (image_short_exact α) g hg

set_option linter.unusedFintypeInType false in
/-- A morphism with finite kernel and cokernel preserves the Herbrand
quotient whenever both quotients are defined. -/
theorem herbrand_quotient_cokernel
    (α : M ⟶ N) [Finite ↑(kernel α : Rep k G)] [Finite ↑(cokernel α : Rep k G)]
    (g : G) (hg : ∀ x, x ∈ Subgroup.zpowers g)
    [Finite (groupCohomology M 1)] [Finite (groupCohomology M 2)]
    [Finite (groupCohomology N 1)] [Finite (groupCohomology N 2)] :
    herbrandQuotient M = herbrandQuotient N := by
  letI : Finite (groupCohomology (kernel α) 1) :=
    group_cohomology_module (kernel α) g hg
  letI : Finite (groupCohomology (kernel α) 2) :=
    cohomology_two_module (kernel α) g hg
  obtain ⟨hI₁, hI₂⟩ := herbrand_quotient_right
    (image_short_exact α) g hg
  letI : Finite (groupCohomology (Abelian.image α) 1) := hI₁
  letI : Finite (groupCohomology (Abelian.image α) 2) := hI₂
  letI : Finite (groupCohomology (cokernel α) 1) :=
    group_cohomology_module (cokernel α) g hg
  letI : Finite (groupCohomology (cokernel α) 2) :=
    cohomology_two_module (cokernel α) g hg
  have h₁ := herbrandQuotient_mul
    (image_short_exact α) g hg
  have h₂ := herbrandQuotient_mul
    (cokernel_short_exact α) g hg
  have hK := herbrand_quotient_module (kernel α) g hg
  have hC := herbrand_quotient_module (cokernel α) g hg
  calc
    herbrandQuotient M =
        herbrandQuotient (kernel α) * herbrandQuotient (Abelian.image α) := h₁
    _ = herbrandQuotient (Abelian.image α) := by rw [hK, one_mul]
    _ = herbrandQuotient (Abelian.image α) * herbrandQuotient (cokernel α) := by
      rw [hC, mul_one]
    _ = herbrandQuotient N := h₂.symm

set_option linter.unusedFintypeInType false in
/-- **Corollary II.3.9, domain-to-codomain form.** If the domain quotient is
defined and the kernel and cokernel are finite, the codomain quotient is
defined and equal to it. -/
theorem codomain_kernel_cokernel
    (α : M ⟶ N) [Finite ↑(kernel α : Rep k G)] [Finite ↑(cokernel α : Rep k G)]
    (g : G) (hg : ∀ x, x ∈ Subgroup.zpowers g)
    [Finite (groupCohomology M 1)] [Finite (groupCohomology M 2)] :
    letI : Finite (groupCohomology N 1) :=
      (herbrand_codomain_cokernel α g hg).1
    letI : Finite (groupCohomology N 2) :=
      (herbrand_codomain_cokernel α g hg).2
    herbrandQuotient M = herbrandQuotient N := by
  obtain ⟨hN₁, hN₂⟩ :=
    herbrand_codomain_cokernel α g hg
  letI : Finite (groupCohomology N 1) := hN₁
  letI : Finite (groupCohomology N 2) := hN₂
  exact herbrand_quotient_cokernel α g hg

set_option linter.unusedFintypeInType false in
/-- **Corollary II.3.9, codomain-to-domain form.** If the codomain quotient
is defined and the kernel and cokernel are finite, the domain quotient is
defined and equal to it. -/
theorem herbrand_kernel_cokernel
    (α : M ⟶ N) [Finite ↑(kernel α : Rep k G)] [Finite ↑(cokernel α : Rep k G)]
    (g : G) (hg : ∀ x, x ∈ Subgroup.zpowers g)
    [Finite (groupCohomology N 1)] [Finite (groupCohomology N 2)] :
    letI : Finite (groupCohomology M 1) :=
      (herbrand_domain_cokernel α g hg).1
    letI : Finite (groupCohomology M 2) :=
      (herbrand_domain_cokernel α g hg).2
    herbrandQuotient M = herbrandQuotient N := by
  obtain ⟨hM₁, hM₂⟩ :=
    herbrand_domain_cokernel α g hg
  letI : Finite (groupCohomology M 1) := hM₁
  letI : Finite (groupCohomology M 2) := hM₂
  exact herbrand_quotient_cokernel α g hg

end

end Submission.CField.Shifting
