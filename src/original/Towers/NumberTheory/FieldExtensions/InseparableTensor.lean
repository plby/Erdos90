import Mathlib

/-!
# Milne, Algebraic Number Theory, the inseparable tensor-product obstruction

At the end of Chapter 1, Milne explains why separability is necessary in the tensor-product
decomposition theorem. If `x ^ p` belongs to the base field but `x` does not, then
`x ⊗ 1 - 1 ⊗ x` is a nonzero element whose `p`-th power is zero.
-/

open scoped TensorProduct

namespace Towers.NumberTheory.Milne

variable (k K : Type*) [Field k] [Field K] [Algebra k K]
variable (p : ℕ) [Fact p.Prime] [CharP k p]

/-- If the `p`-th power of `x` belongs to the base field, then
`x ⊗ 1 - 1 ⊗ x` has `p`-th power zero in `K ⊗[k] K`. -/
theorem include_sub_range (x : K)
    (hx : x ^ p ∈ Set.range (algebraMap k K)) :
    (Algebra.TensorProduct.includeLeftSubRight k K x) ^ p = 0 := by
  letI : CharP (K ⊗[k] K) p := charP_of_injective_algebraMap
    (FaithfulSMul.algebraMap_injective k (K ⊗[k] K)) p
  obtain ⟨a, ha⟩ := hx
  rw [Algebra.TensorProduct.includeLeftSubRight_apply, sub_pow_char,
    Algebra.TensorProduct.tmul_pow, Algebra.TensorProduct.tmul_pow, ← ha]
  exact sub_eq_zero.mpr (by
    simpa using (Algebra.TensorProduct.tmul_one_eq_one_tmul (A := K) (B := K) a))

/-- An element outside the base field gives a nonzero difference
`x ⊗ 1 - 1 ⊗ x`. -/
theorem include_ne_range (x : K)
    (hx : x ∉ Set.range (algebraMap k K)) :
    Algebra.TensorProduct.includeLeftSubRight k K x ≠ 0 := by
  intro hzero
  exact hx ((Algebra.IsEffective.of_faithfullyFlat k K x).mp hzero)

/-- Milne's obstruction to dropping separability: if `x ^ p` is in the base field while `x`
is not, then `K ⊗[k] K` contains a nonzero nilpotent element. -/
theorem nonzero_nilpotent_range (x : K)
    (hxp : x ^ p ∈ Set.range (algebraMap k K))
    (hx : x ∉ Set.range (algebraMap k K)) :
    ∃ y : K ⊗[k] K, y ≠ 0 ∧ IsNilpotent y := by
  refine ⟨Algebra.TensorProduct.includeLeftSubRight k K x,
    include_ne_range k K x hx, ?_⟩
  exact ⟨p, include_sub_range k K p x hxp⟩

/-- Under the same hypotheses, `K ⊗[k] K` is not reduced. In particular it cannot be a product
of fields, which is the conclusion drawn in Milne's discussion after Example 1.19. -/
theorem tensor_reduced_range (x : K)
    (hxp : x ^ p ∈ Set.range (algebraMap k K))
    (hx : x ∉ Set.range (algebraMap k K)) :
    ¬IsReduced (K ⊗[k] K) := by
  intro hred
  letI : IsReduced (K ⊗[k] K) := hred
  obtain ⟨y, hy, hnil⟩ :=
    nonzero_nilpotent_range k K p x hxp hx
  exact hy (isNilpotent_iff_eq_zero.mp hnil)

end Towers.NumberTheory.Milne

namespace Towers.NumberTheory.Milne

open Polynomial

variable (k K : Type*) [Field k] [Field K] [Algebra k K]

/-- A finite inseparable extension has nonreduced self-tensor product.

The frequently used special case where `x ^ p` belongs to the base field does not cover every
inseparable extension: an inseparable simple extension can have a nontrivial separable part.  For
the general statement, choose an inseparable element `x`, base-change its minimal polynomial to
`K`, and use its repeated root `x` to construct a nonzero square-zero element. -/
theorem tensor_reduced_separable
    [FiniteDimensional k K] (hsep : ¬Algebra.IsSeparable k K) :
    ¬IsReduced (K ⊗[k] K) := by
  classical
  have hnotall : ¬∀ x : K, IsSeparable k x := by
    intro hall
    exact hsep ⟨hall⟩
  obtain ⟨x, hxsep⟩ := not_forall.mp hnotall
  have hxint : IsIntegral k x := Algebra.IsIntegral.isIntegral x
  let f0 : k[X] := minpoly k x
  let f : K[X] := f0.map (algebraMap k K)
  have hf0monic : f0.Monic := minpoly.monic hxint
  have hfmonic : f.Monic := hf0monic.map (algebraMap k K)
  have hf0deriv : f0.derivative = 0 := by
    by_contra hne
    exact hxsep ((separable_iff_derivative_ne_zero (minpoly.irreducible hxint)).2 hne)
  have hfderiv : f.derivative = 0 := by
    simp [f, derivative_map, hf0deriv]
  have hfx : f.eval x = 0 := by
    unfold f f0
    rw [eval_map]
    exact minpoly.aeval k x
  let h : K[X] := X - C x
  let q : K[X] := f /ₘ h
  have hfactor : h * q = f := by
    change (X - C x) * (f /ₘ (X - C x)) = f
    rw [X_sub_C_mul_divByMonic_eq_sub_modByMonic]
    simp [modByMonic_X_sub_C_eq_C_eval, hfx]
  have hqroot : q.eval x = 0 := by
    have hd := congrArg (fun g : K[X] => g.eval x)
      (divByMonic_add_X_sub_C_mul_derivative_divByMonic_eq_derivative f x)
    simpa [q, h, hfderiv] using hd
  have hhdvdq : h ∣ q := by
    change X - C x ∣ q
    rw [dvd_iff_isRoot]
    exact hqroot
  obtain ⟨r, hr⟩ := hhdvdq
  have hqne : q ≠ 0 := by
    intro hq
    apply hfmonic.ne_zero
    rw [← hfactor, hq, mul_zero]
  have hqdegree : q.natDegree < f.natDegree := by
    have hdegree := (monic_X_sub_C x).natDegree_mul' hqne
    rw [show X - C x = h by rfl, hfactor, natDegree_X_sub_C] at hdegree
    omega
  have hqsquare : f ∣ q ^ 2 := by
    refine ⟨r, ?_⟩
    calc
      q ^ 2 = q * q := pow_two q
      _ = (h * r) * q := by rw [← hr]
      _ = (h * q) * r := by ring
      _ = f * r := by rw [hfactor]
  let y : AdjoinRoot f := AdjoinRoot.mk f q
  have hyne : y ≠ 0 := by
    exact AdjoinRoot.mk_ne_zero_of_natDegree_lt hfmonic hqne hqdegree
  have hysquare : y ^ 2 = 0 := by
    change AdjoinRoot.mk f (q ^ 2) = 0
    exact AdjoinRoot.mk_eq_zero.mpr hqsquare
  let L : Type _ := IntermediateField.adjoin k ({x} : Set K)
  let xL : L := ⟨x, IntermediateField.subset_adjoin k ({x} : Set K) (Set.mem_singleton x)⟩
  have hLgen : Algebra.adjoin k ({xL} : Set L) = ⊤ := by
    simpa [L, xL] using (IntermediateField.adjoin.powerBasis hxint).adjoin_gen_eq_top
  have hxLroot : Polynomial.aeval xL f0 = 0 := by
    apply Subtype.ext
    change ((Polynomial.aeval xL f0 : L) : K) = 0
    calc
      ((Polynomial.aeval xL f0 : L) : K) =
          Polynomial.aeval ((IntermediateField.val _) xL) f0 :=
        (Polynomial.aeval_algHom_apply (IntermediateField.val _) xL f0).symm
      _ = Polynomial.aeval x f0 := by rfl
      _ = 0 := by
        unfold f0
        exact minpoly.aeval k x
  let T : Type _ := K ⊗[k] L
  let t : T := (1 : K) ⊗ₜ[k] xL
  have ht : Polynomial.aeval t f = 0 := by
    unfold f
    rw [Polynomial.aeval_map_algebraMap]
    change Polynomial.aeval
      ((Algebra.TensorProduct.includeRight : L →ₐ[k] T) xL) f0 = 0
    rw [Polynomial.aeval_algHom_apply, hxLroot, map_zero]
  let φ : AdjoinRoot f →ₐ[K] T :=
    AdjoinRoot.liftAlgHom f (Algebra.ofId K T) t (by
      simpa [Polynomial.aeval_def] using ht)
  have hTgen : Algebra.adjoin K ({t} : Set T) = ⊤ := by
    simpa [T, t] using
      Algebra.TensorProduct.adjoin_one_tmul_image_eq_top (A := K) ({xL} : Set L) hLgen
  have hφsurj : Function.Surjective φ := by
    apply (AlgHom.range_eq_top φ).mp
    apply top_unique
    rw [← hTgen]
    apply Algebra.adjoin_le
    rintro _ rfl
    refine ⟨AdjoinRoot.root f, ?_⟩
    exact AdjoinRoot.liftAlgHom_root f (Algebra.ofId K T) t _
  letI : Module.Free K (AdjoinRoot f) := hfmonic.free_adjoinRoot
  letI : Module.Finite K (AdjoinRoot f) := hfmonic.finite_adjoinRoot
  have hdim : Module.finrank K (AdjoinRoot f) = Module.finrank K T := by
    calc
      Module.finrank K (AdjoinRoot f) = f.natDegree :=
        (AdjoinRoot.powerBasis' hfmonic).finrank
      _ = f0.natDegree := by simp [f, hf0monic.natDegree_map]
      _ = Module.finrank k L := (IntermediateField.adjoin.finrank hxint).symm
      _ = Module.finrank K T := Module.finrank_baseChange.symm
  have hφinj : Function.Injective φ :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (f := φ.toLinearMap) hdim).mpr hφsurj
  let ψ : T →ₐ[k] (K ⊗[k] K) :=
    Algebra.TensorProduct.map (AlgHom.id k K) (IntermediateField.val _)
  have hψinj : Function.Injective ψ :=
    Module.Flat.lTensor_preserves_injective_linearMap _ Subtype.val_injective
  let z : K ⊗[k] K := ψ (φ y)
  have hzne : z ≠ 0 := by
    intro hz
    apply hyne
    apply hφinj
    apply hψinj
    simpa [z] using hz
  have hzsquare : z ^ 2 = 0 := by
    change (ψ (φ y)) ^ 2 = 0
    rw [← map_pow, ← map_pow, hysquare, map_zero, map_zero]
  intro hred
  letI : IsReduced (K ⊗[k] K) := hred
  exact hzne (isNilpotent_iff_eq_zero.mp ⟨2, hzsquare⟩)

end Towers.NumberTheory.Milne
