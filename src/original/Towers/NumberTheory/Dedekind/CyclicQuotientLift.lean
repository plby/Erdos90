import Towers.NumberTheory.Dedekind.DedekindModules
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Milne, Algebraic Number Theory, lifting a cyclic quotient

The induction behind the invariant-factor theorem starts with a cyclic quotient `A / I`.
Projectivity of the ambient lattice lifts the quotient map to an `A`-valued functional.  Its
image ideal is coprime to `I`, and the original kernel is the inverse image of `I`.
-/

namespace Towers.NumberTheory.Milne

/-- The explicit splitting associated to a right inverse of the range-restricted map. -/
noncomputable def kerRangeSection
    {A M : Type*} [Ring A]
    [AddCommGroup M] [Module A M]
    (f : M →ₗ[A] A) (r : LinearMap.range f →ₗ[A] M)
    (hr : f.rangeRestrict.comp r = LinearMap.id) :
    M ≃ₗ[A] LinearMap.ker f × LinearMap.range f where
  toFun x :=
    (⟨x - r (f.rangeRestrict x), by
      rw [LinearMap.mem_ker, map_sub]
      have hsec : f (r (f.rangeRestrict x)) = f x := by
        have h := congrArg Subtype.val (DFunLike.congr_fun hr (f.rangeRestrict x))
        change f (r (f.rangeRestrict x)) = f x at h
        exact h
      exact sub_eq_zero.mpr hsec.symm⟩,
      f.rangeRestrict x)
  invFun x := x.1.1 + r x.2
  map_add' x y := by
    apply Prod.ext
    · apply Subtype.ext
      change x + y - r (f.rangeRestrict (x + y)) =
        (x - r (f.rangeRestrict x)) + (y - r (f.rangeRestrict y))
      rw [map_add, map_add]
      abel
    · apply Subtype.ext
      simp
  map_smul' a x := by
    apply Prod.ext
    · apply Subtype.ext
      change a • x - r (f.rangeRestrict (a • x)) =
        a • (x - r (f.rangeRestrict x))
      rw [map_smul, map_smul, smul_sub]
    · apply Subtype.ext
      simp
  left_inv x := by
    change (x - r (f.rangeRestrict x)) + r (f.rangeRestrict x) = x
    abel_nf
  right_inv x := by
    have hker : f x.1.1 = 0 := LinearMap.mem_ker.mp x.1.2
    have hsec : f (r x.2) = x.2.1 := by
      have h := congrArg Subtype.val (DFunLike.congr_fun hr x.2)
      change f (r x.2) = x.2.1 at h
      exact h
    have hrange : f.rangeRestrict (x.1.1 + r x.2) = x.2 := by
      apply Subtype.ext
      change f (x.1.1 + r x.2) = x.2.1
      rw [map_add, hker, hsec, zero_add]
    apply Prod.ext
    · apply Subtype.ext
      change x.1.1 + r x.2 - r (f.rangeRestrict (x.1.1 + r x.2)) = x.1.1
      rw [hrange]
      abel
    · apply Subtype.ext
      exact congrArg Subtype.val hrange

@[simp]
theorem ker_section_fst
    {A M : Type*} [Ring A]
    [AddCommGroup M] [Module A M]
    (f : M →ₗ[A] A) (r : LinearMap.range f →ₗ[A] M)
    (hr : f.rangeRestrict.comp r = LinearMap.id) (x : M) :
    (kerRangeSection f r hr x).1.1 =
      x - r (f.rangeRestrict x) :=
  rfl

@[simp]
theorem ker_section_snd
    {A M : Type*} [Ring A]
    [AddCommGroup M] [Module A M]
    (f : M →ₗ[A] A) (r : LinearMap.range f →ₗ[A] M)
    (hr : f.rangeRestrict.comp r = LinearMap.id) (x : M) :
    (kerRangeSection f r hr x).2 = f.rangeRestrict x :=
  rfl

@[simp]
theorem ker_section_symm
    {A M : Type*} [Ring A]
    [AddCommGroup M] [Module A M]
    (f : M →ₗ[A] A) (r : LinearMap.range f →ₗ[A] M)
    (hr : f.rangeRestrict.comp r = LinearMap.id)
    (x : LinearMap.ker f × LinearMap.range f) :
    (kerRangeSection f r hr).symm x = x.1.1 + r x.2 :=
  rfl

/-- A surjection from a projective module to `A / I` lifts to an `A`-valued functional whose
range is coprime to `I`; the kernel of the quotient map is the pullback of `I`. -/
theorem lift_cyclic_quotient
    (A M : Type*) [CommRing A]
    [AddCommGroup M] [Module A M] [Module.Projective A M]
    (I : Ideal A) (q : M →ₗ[A] A ⧸ I) (hq : Function.Surjective q) :
    ∃ f : M →ₗ[A] A,
      (Submodule.mkQ I).comp f = q ∧
        LinearMap.range f ⊔ I = ⊤ ∧
        LinearMap.ker q = Submodule.comap f (I : Submodule A A) := by
  obtain ⟨f, hf⟩ :=
    Module.projective_lifting_property (Submodule.mkQ I) q I.mkQ_surjective
  refine ⟨f, hf, ?_, ?_⟩
  · rw [eq_top_iff]
    intro x _
    obtain ⟨m, hm⟩ := hq (Ideal.Quotient.mk I x)
    have hmem : f m - x ∈ I := by
      apply (Submodule.Quotient.eq I).mp
      calc
        Submodule.Quotient.mk (f m) = q m := by
          rw [← hf]
          rfl
        _ = Submodule.Quotient.mk x := hm
    rw [Submodule.mem_sup]
    refine ⟨f m, ⟨m, rfl⟩, x - f m, ?_, ?_⟩
    · have hneg := I.neg_mem hmem
      rwa [neg_sub] at hneg
    · abel
  · ext m
    rw [LinearMap.mem_ker, Submodule.mem_comap]
    change q m = 0 ↔ f m ∈ I
    rw [← hf]
    exact Ideal.Quotient.eq_zero_iff_mem

/-- The range ideal in a lifted cyclic quotient meets the defining ideal in their product. -/
theorem range_inf_lift
    (A M : Type*) [CommRing A]
    [AddCommGroup M] [Module A M] [Module.Projective A M]
    (I : Ideal A) (q : M →ₗ[A] A ⧸ I) (hq : Function.Surjective q) :
    ∃ f : M →ₗ[A] A,
      (Submodule.mkQ I).comp f = q ∧
        LinearMap.ker q = Submodule.comap f (I : Submodule A A) ∧
        LinearMap.range f ⊓ I = LinearMap.range f * I := by
  obtain ⟨f, hf, hcop, hker⟩ := lift_cyclic_quotient A M I q hq
  exact ⟨f, hf, hker,
    (Ideal.mul_eq_inf_of_coprime hcop).symm⟩

/-- Over a Dedekind domain, the lifted range ideal is projective, so the ambient lattice splits
as the kernel of the lift times its range ideal. -/
theorem split_lift_cyclic
    (A M : Type*) [CommRing A] [IsDomain A] [IsDedekindDomain A]
    [AddCommGroup M] [Module A M] [Module.Finite A M]
    [Module.IsTorsionFree A M]
    (I : Ideal A) (q : M →ₗ[A] A ⧸ I) (hq : Function.Surjective q) :
    ∃ f : M →ₗ[A] A,
      (Submodule.mkQ I).comp f = q ∧
        LinearMap.range f ⊔ I = ⊤ ∧
        LinearMap.ker q = Submodule.comap f (I : Submodule A A) ∧
        Nonempty (M ≃ₗ[A] LinearMap.ker f × LinearMap.range f) := by
  letI : Module.Projective A M := torsion_module_projective A M
  obtain ⟨f, hf, hcop, hker⟩ := lift_cyclic_quotient A M I q hq
  letI : Module.Finite A (LinearMap.range f) :=
    Module.Finite.of_fg (IsNoetherian.noetherian _)
  letI : Module.Projective A (LinearMap.range f) :=
    torsion_module_projective A (LinearMap.range f)
  obtain ⟨r, hr⟩ := Module.projective_lifting_property
    f.rangeRestrict LinearMap.id f.surjective_rangeRestrict
  let split : M ≃ₗ[A] LinearMap.ker f × LinearMap.range f :=
    (lequivProdOfRightSplitExact
      (j := (LinearMap.ker f).subtype) (g := f.rangeRestrict) (f := r)
      (LinearMap.ker f).injective_subtype (by
        rw [Submodule.range_subtype, LinearMap.ker_rangeRestrict]) hr).symm
  exact ⟨f, hf, hcop, hker, ⟨split⟩⟩

end Towers.NumberTheory.Milne
