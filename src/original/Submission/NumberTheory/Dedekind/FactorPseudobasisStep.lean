import Submission.NumberTheory.Dedekind.FactorPseudobasisInduction


/-!
# The nondegenerate induction step for invariant-factor pseudobases

When the final invariant ideal is proper, projection to the final cyclic quotient lifts to an
`A`-valued functional.  Its range is a nonzero ideal, and the explicit kernel-range coordinates
split both the ambient lattice and the sublattice.  The remaining kernel quotient carries the
prefix invariant-factor presentation.
-/

namespace Submission.NumberTheory.Milne

open scoped DirectSum

universe u

/-- Peel off the final proper invariant factor while preserving the prefix quotient. -/
theorem invariant_pseudobasis_step
    (A M : Type u) [CommRing A] [IsDomain A] [IsDedekindDomain A]
    [AddCommGroup M] [Module A M] [Module.Finite A M]
    [Module.IsTorsionFree A M]
    (N : Submodule A M)
    (n : ℕ) (b : Fin (n + 1) → Ideal A) (hb : Antitone b)
    (e : (M ⧸ N) ≃ₗ[A]
      DirectSum (Fin (n + 1)) (fun i ↦ idealQuotientModule A (b i)))
    (hlast : b (Fin.last n) ≠ ⊤) :
    ∃ (f : M →ₗ[A] A) (r : LinearMap.range f →ₗ[A] M)
      (_hr : f.rangeRestrict.comp r = LinearMap.id),
      LinearMap.range f ≠ ⊥ ∧
      ∃ (eM : M ≃ₗ[A] LinearMap.ker f × LinearMap.range f)
        (eN : N ≃ₗ[A]
          (Submodule.comap (LinearMap.ker f).subtype N) ×
            (LinearMap.range f * b (Fin.last n) : Ideal A))
        (_ePrefix :
          (LinearMap.ker f ⧸ Submodule.comap (LinearMap.ker f).subtype N) ≃ₗ[A]
            DirectSum (Fin n)
              (fun i ↦ idealQuotientModule A (b i.castSucc))),
        ∀ x : N,
          eM x.1 = ((eN x).1.1,
            Submodule.inclusion Ideal.mul_le_right (eN x).2) := by
  classical
  let split := invariantSplitLast A n b
  let total : M →ₗ[A]
      (DirectSum (Fin n) (fun i ↦ idealQuotientModule A (b i.castSucc))) ×
        idealQuotientModule A (b (Fin.last n)) :=
    split.toLinearMap.comp (e.toLinearMap.comp N.mkQ)
  let q : M →ₗ[A] idealQuotientModule A (b (Fin.last n)) :=
    (LinearMap.snd A _ _).comp total
  have hq : Function.Surjective q := by
    intro y
    let z := split.symm (0, y)
    obtain ⟨m, hm⟩ := N.mkQ_surjective (e.symm z)
    refine ⟨m, ?_⟩
    simp [q, total, z, hm]
  letI : Module.Projective A M := torsion_module_projective A M
  obtain ⟨f, hf, hcop, hker⟩ := lift_cyclic_quotient A M _ q hq
  have hrange_ne : LinearMap.range f ≠ ⊥ := by
    intro hrange
    apply hlast
    simpa [hrange] using hcop
  letI : Module.Finite A (LinearMap.range f) :=
    Module.Finite.of_fg (IsNoetherian.noetherian _)
  letI : Module.Projective A (LinearMap.range f) :=
    torsion_module_projective A (LinearMap.range f)
  obtain ⟨r, hr⟩ := Module.projective_lifting_property
    f.rangeRestrict LinearMap.id f.surjective_rangeRestrict
  let eM := kerRangeSection f r hr
  have hIM : b (Fin.last n) • (⊤ : Submodule A M) ≤ N :=
    invariant_smul_submodule A M N n b hb e
  have hN : N ≤ Submodule.comap f (b (Fin.last n) : Submodule A A) := by
    rw [← hker]
    intro x hx
    rw [LinearMap.mem_ker]
    simp [q, total, (Submodule.Quotient.mk_eq_zero N).mpr hx]
  let eN := submodule_range_mul f r hr _ hcop N hIM hN
  let K := LinearMap.ker f
  let J := LinearMap.range f
  let P := Submodule.comap K.subtype N
  let kEmbed : K →ₗ[A] M :=
    eM.symm.toLinearMap.comp (LinearMap.inl A K J)
  have hkEmbed (x : K) : kEmbed x = x.1 := by
    simp [kEmbed, eM, K, J]
  let prefixMap : K →ₗ[A]
      DirectSum (Fin n) (fun i ↦ idealQuotientModule A (b i.castSucc)) :=
    (LinearMap.fst A _ _).comp (total.comp kEmbed)
  have hq_kEmbed (x : K) : q (kEmbed x) = 0 := by
    rw [← hf]
    simp [kEmbed, eM, K, J]
  have hprefix_ker : LinearMap.ker prefixMap = P := by
    ext x
    constructor
    · intro hx
      have hfst : (total (kEmbed x)).1 = 0 := by
        simpa [prefixMap] using LinearMap.mem_ker.mp hx
      have hsnd : (total (kEmbed x)).2 = 0 := by
        exact hq_kEmbed x
      have htotal : total (kEmbed x) = 0 := Prod.ext hfst hsnd
      have hquot : N.mkQ (kEmbed x) = 0 := by
        apply e.injective
        apply split.injective
        simpa [total] using htotal
      change x.1 ∈ N
      rw [← hkEmbed x]
      exact (Submodule.Quotient.mk_eq_zero N).mp hquot
    · intro hx
      rw [LinearMap.mem_ker]
      have hxN : kEmbed x ∈ N := by
        rw [hkEmbed]
        exact hx
      have hquot : N.mkQ (kEmbed x) = 0 :=
        (Submodule.Quotient.mk_eq_zero N).mpr hxN
      simp [prefixMap, total, hquot]
  have hprefix_surjective : Function.Surjective prefixMap := by
    intro y
    let z := split.symm (y, 0)
    obtain ⟨m, hm⟩ := N.mkQ_surjective (e.symm z)
    have htotal : total m = (y, 0) := by
      simp [total, z, hm]
    let sx := eM m
    have hsx_mem : sx.2 ∈
        Submodule.comap J.subtype (b (Fin.last n) : Submodule A A) := by
      change sx.2.1 ∈ b (Fin.last n)
      have hqm : q m = 0 := by simpa [q] using congrArg Prod.snd htotal
      have hfm : f m ∈ b (Fin.last n) := by
        rw [← Ideal.Quotient.eq_zero_iff_mem]
        have hfmq := DFunLike.congr_fun hf m
        change Ideal.Quotient.mk (b (Fin.last n)) (f m) = q m at hfmq
        rw [hfmq, hqm]
      simpa [sx, eM] using hfm
    have hrN : r sx.2 ∈ N :=
      hIM (section_comap_subtype
        f r _ hcop sx.2 hsx_mem)
    let x : K := sx.1
    refine ⟨x, ?_⟩
    have hmdecomp : m = x.1 + r sx.2 := by
      have hs := eM.symm_apply_apply m
      simp [eM, sx, x]
    have htotal_r : total (r sx.2) = 0 := by
      have hquot : N.mkQ (r sx.2) = 0 :=
        (Submodule.Quotient.mk_eq_zero N).mpr hrN
      simp [total, hquot]
    have htotal_k : total (kEmbed x) = (y, 0) := by
      rw [hkEmbed]
      apply eq_of_sub_eq_zero
      rw [← htotal, hmdecomp, map_add, htotal_r, add_zero, sub_self]
    simpa [prefixMap] using congrArg Prod.fst htotal_k
  let induced : (K ⧸ P) →ₗ[A]
      DirectSum (Fin n) (fun i ↦ idealQuotientModule A (b i.castSucc)) :=
    P.liftQ prefixMap (by rw [← hprefix_ker])
  have hinduced : Function.Bijective induced := by
    constructor
    · rw [← LinearMap.ker_eq_bot]
      exact Submodule.ker_liftQ_eq_bot' P prefixMap hprefix_ker.symm
    · intro y
      obtain ⟨x, hx⟩ := hprefix_surjective y
      exact ⟨Submodule.Quotient.mk x, by simpa [induced] using hx⟩
  let ePrefix := LinearEquiv.ofBijective induced hinduced
  refine ⟨f, r, hr, hrange_ne, eM, eN, ePrefix, ?_⟩
  intro x
  rfl

end Submission.NumberTheory.Milne
