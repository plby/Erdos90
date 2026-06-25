import Towers.NumberTheory.Dedekind.CyclicQuotientLift

/-!
# Coordinates for a lifted cyclic quotient

Under the splitting associated to a section of the range-restricted map, the inverse image of an
ideal is the product of the full kernel with the corresponding submodule of the range ideal.
-/

namespace Towers.NumberTheory.Milne

/-- The cyclic lifting construction with the section of the range-restricted map retained. -/
theorem lift_cyclic_section
    (A M : Type*) [CommRing A] [IsDomain A] [IsDedekindDomain A]
    [AddCommGroup M] [Module A M] [Module.Finite A M]
    [Module.IsTorsionFree A M]
    (I : Ideal A) (q : M →ₗ[A] A ⧸ I) (hq : Function.Surjective q) :
    ∃ (f : M →ₗ[A] A) (r : LinearMap.range f →ₗ[A] M),
      (Submodule.mkQ I).comp f = q ∧
        LinearMap.range f ⊔ I = ⊤ ∧
        LinearMap.ker q = Submodule.comap f (I : Submodule A A) ∧
        f.rangeRestrict.comp r = LinearMap.id := by
  letI : Module.Projective A M := torsion_module_projective A M
  obtain ⟨f, hf, hcop, hker⟩ := lift_cyclic_quotient A M I q hq
  letI : Module.Finite A (LinearMap.range f) :=
    Module.Finite.of_fg (IsNoetherian.noetherian _)
  letI : Module.Projective A (LinearMap.range f) :=
    torsion_module_projective A (LinearMap.range f)
  obtain ⟨r, hr⟩ := Module.projective_lifting_property
    f.rangeRestrict LinearMap.id f.surjective_rangeRestrict
  exact ⟨f, r, hf, hcop, hker, hr⟩

/-- In the explicit kernel-range splitting, `f⁻¹(I)` is the product of the full kernel with
the part of the range ideal lying in `I`. -/
theorem comap_top_subtype
    {A M : Type*} [CommRing A]
    [AddCommGroup M] [Module A M]
    (f : M →ₗ[A] A) (r : LinearMap.range f →ₗ[A] M)
    (hr : f.rangeRestrict.comp r = LinearMap.id) (I : Ideal A) :
    (Submodule.comap f (I : Submodule A A)).map
        (kerRangeSection f r hr).toLinearMap =
      (Submodule.prod (⊤ : Submodule A (LinearMap.ker f))
        (Submodule.comap (LinearMap.range f).subtype (I : Submodule A A))) := by
  ext x
  constructor
  · rintro ⟨m, hm, rfl⟩
    rw [Submodule.mem_prod]
    refine ⟨Submodule.mem_top, ?_⟩
    exact hm
  · intro hx
    rw [Submodule.mem_prod] at hx
    let e := kerRangeSection f r hr
    refine ⟨e.symm x, ?_, e.apply_symm_apply x⟩
    change f (e.symm x) ∈ I
    rw [ker_section_symm, map_add,
      LinearMap.mem_ker.mp x.1.2]
    have hsec : f (r x.2) = x.2.1 := by
      have h := congrArg Subtype.val (DFunLike.congr_fun hr x.2)
      change f (r x.2) = x.2.1 at h
      exact h
    rw [hsec, zero_add]
    exact hx.2

/-- A section of the range-restricted map sends the part of the range lying in a coprime ideal
into the submodule obtained by multiplying the ambient module by that ideal. -/
theorem section_comap_subtype
    {A M : Type*} [CommRing A]
    [AddCommGroup M] [Module A M]
    (f : M →ₗ[A] A) (r : LinearMap.range f →ₗ[A] M)
    (I : Ideal A) (hcop : LinearMap.range f ⊔ I = ⊤)
    (y : LinearMap.range f)
    (hy : y ∈ Submodule.comap (LinearMap.range f).subtype (I : Submodule A A)) :
    r y ∈ I • (⊤ : Submodule A M) := by
  have hyprod : y.1 ∈ LinearMap.range f * I := by
    rw [Ideal.mul_eq_inf_of_coprime hcop]
    exact ⟨y.2, hy⟩
  have hysmul : y.1 ∈ I • LinearMap.range f := by
    rw [Ideal.smul_eq_mul, mul_comm]
    exact hyprod
  have hytop : y ∈ I • (⊤ : Submodule A (LinearMap.range f)) :=
    (Submodule.mem_smul_top_iff (I := I) (N := LinearMap.range f) y).2 hysmul
  have hry : r y ∈ (I • (⊤ : Submodule A (LinearMap.range f))).map r :=
    Submodule.mem_map_of_mem hytop
  rw [Submodule.map_smul'', Submodule.map_top] at hry
  have hle : I • LinearMap.range r ≤ I • (⊤ : Submodule A M) :=
    smul_mono_right I le_top
  exact hle hry

/-- If the submodule lies in the inverse image of the ideal and contains the ideal times the
ambient module, then the kernel-range splitting carries it to the corresponding product. -/
theorem submodule_comap_subtype
    {A M : Type*} [CommRing A]
    [AddCommGroup M] [Module A M]
    (f : M →ₗ[A] A) (r : LinearMap.range f →ₗ[A] M)
    (hr : f.rangeRestrict.comp r = LinearMap.id)
    (I : Ideal A) (hcop : LinearMap.range f ⊔ I = ⊤)
    (N : Submodule A M)
    (hIM : I • (⊤ : Submodule A M) ≤ N)
    (hN : N ≤ Submodule.comap f (I : Submodule A A)) :
    N.map (kerRangeSection f r hr).toLinearMap =
      Submodule.prod
        (Submodule.comap (LinearMap.ker f).subtype N)
        (Submodule.comap (LinearMap.range f).subtype (I : Submodule A A)) := by
  let e := kerRangeSection f r hr
  ext x
  constructor
  · rintro ⟨m, hm, rfl⟩
    rw [Submodule.mem_prod]
    have hy :
        f.rangeRestrict m ∈
          Submodule.comap (LinearMap.range f).subtype (I : Submodule A A) :=
      hN hm
    have hry : r (f.rangeRestrict m) ∈ N :=
      hIM (section_comap_subtype
        f r I hcop (f.rangeRestrict m) hy)
    exact ⟨N.sub_mem hm hry, hy⟩
  · intro hx
    rw [Submodule.mem_prod] at hx
    refine ⟨e.symm x, ?_, e.apply_symm_apply x⟩
    rw [ker_section_symm]
    exact N.add_mem hx.1
      (hIM (section_comap_subtype
        f r I hcop x.2 hx.2))

end Towers.NumberTheory.Milne
