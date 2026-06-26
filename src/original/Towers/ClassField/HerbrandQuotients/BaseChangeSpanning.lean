import Towers.ClassField.HerbrandQuotients.Representation
import Mathlib.LinearAlgebra.TensorProduct.Finiteness
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.TensorProduct.IsBaseChangeHom

/-!
# Chapter VII, Section 3, Lemma 3.2: base-change spanning

Equivariant linear maps are the kernel of the finite family of linear
equivariance equations.  Extension of scalars along a field extension is
flat, so it preserves that kernel.  The resulting tensor expression gives
the spanning bridge used by the determinant-polynomial proof of Lemma 3.2.
-/

namespace Towers.CField.HQuotie

open scoped BigOperators TensorProduct

noncomputable section

universe u v w x y

/-- The linear map whose kernel consists of the intertwiners from `ρ` to
`σ`.  Its value records the equivariance defect at every group element. -/
private def equivarianceDefect
    (k G M N : Type*) [Field k] [Group G]
    [AddCommGroup M] [Module k M] [AddCommGroup N] [Module k N]
    (ρ : Representation k G M) (σ : Representation k G N) :
    (M →ₗ[k] N) →ₗ[k] (G → (M →ₗ[k] N)) where
  toFun f g := f ∘ₗ ρ g - σ g ∘ₗ f
  map_add' f h := by
    ext g m
    simp only [Pi.add_apply, LinearMap.add_apply, LinearMap.sub_apply,
      LinearMap.comp_apply, map_add]
    abel
  map_smul' a f := by
    ext g m
    simp only [Pi.smul_apply, LinearMap.smul_apply, LinearMap.sub_apply,
      LinearMap.comp_apply, map_smul]
    exact (smul_sub a _ _).symm

/-- Mathlib's base-change equivalence on spaces of linear maps agrees with
the canonical tensor-product base change of an individual linear map. -/
private theorem linear_base_change
    (k : Type u) (Ω : Type v) (G : Type w) (M : Type x) (N : Type y)
    [Field k] [Field Ω] [Algebra k Ω] [Group G]
    [AddCommGroup M] [Module k M] [Module.Finite k M]
    [AddCommGroup N] [Module k N]
    (f : M →ₗ[k] N) :
    let iM : M →ₗ[k] Ω ⊗[k] M := TensorProduct.mk k Ω M 1
    let iN : N →ₗ[k] Ω ⊗[k] N := TensorProduct.mk k Ω N 1
    let jM : IsBaseChange Ω iM := TensorProduct.isBaseChange k M Ω
    IsBaseChange.linearMapLeftRightHom jM iN f = f.baseChange Ω := by
  dsimp only
  let iM : M →ₗ[k] Ω ⊗[k] M := TensorProduct.mk k Ω M 1
  let iN : N →ₗ[k] Ω ⊗[k] N := TensorProduct.mk k Ω N 1
  let jM : IsBaseChange Ω iM := TensorProduct.isBaseChange k M Ω
  apply jM.algHom_ext
  intro m
  rw [IsBaseChange.linearMapLeftRightHom_comp_apply]
  change (1 : Ω) ⊗ₜ[k] f m = f.baseChange Ω ((1 : Ω) ⊗ₜ[k] m)
  rw [LinearMap.baseChange_tmul]

/-- The equivariant maps after scalar extension are spanned by scalar
extensions of equivariant maps over the ground field. -/
theorem intertwiningSpanningBridge :
    IntertwiningSpanningBridge.{u, v, w, x, y} := by
  intro k Ω G M N _ _ _ _ _ _ _ _ _ _ _ ρ σ f
  let iM : M →ₗ[k] Ω ⊗[k] M := TensorProduct.mk k Ω M 1
  let iN : N →ₗ[k] Ω ⊗[k] N := TensorProduct.mk k Ω N 1
  let jM : IsBaseChange Ω iM := TensorProduct.isBaseChange k M Ω
  let jN : IsBaseChange Ω iN := TensorProduct.isBaseChange k N Ω
  let H := M →ₗ[k] N
  let HΩ := (Ω ⊗[k] M) →ₗ[Ω] (Ω ⊗[k] N)
  let iH : H →ₗ[k] Ω ⊗[k] H := TensorProduct.mk k Ω H 1
  let jH : IsBaseChange Ω iH := TensorProduct.isBaseChange k H Ω
  let D : H →ₗ[k] (G → H) := equivarianceDefect k G M N ρ σ
  let DΩ : HΩ →ₗ[Ω] (G → HΩ) :=
    equivarianceDefect Ω G (Ω ⊗[k] M) (Ω ⊗[k] N)
      (Representation.baseChange k Ω G M ρ)
      (Representation.baseChange k Ω G N σ)
  let b : H →ₗ[k] HΩ := IsBaseChange.linearMapLeftRightHom jM iN
  have hb : IsBaseChange Ω b := jM.linearMapLeftRight jN
  let bG : (G → H) →ₗ[k] (G → HΩ) := b.compLeft G
  have hbG : IsBaseChange Ω bG := hb.finitePow G
  have hb_apply (l : H) : b l = l.baseChange Ω := by
    exact linear_base_change k Ω G M N l
  have hcomm (l : H) : DΩ (b l) = bG (D l) := by
    ext g m
    simp [DΩ, D, equivarianceDefect, bG, hb_apply,
      Representation.baseChange_apply, LinearMap.baseChange_comp]
  have hsquare :
      DΩ ∘ₗ hb.equiv.toLinearMap =
        hbG.equiv.toLinearMap ∘ₗ D.baseChange Ω := by
    apply jH.algHom_ext
    intro l
    change DΩ (hb.equiv ((1 : Ω) ⊗ₜ[k] l)) =
      hbG.equiv (D.baseChange Ω ((1 : Ω) ⊗ₜ[k] l))
    simpa only [IsBaseChange.equiv_tmul, LinearMap.baseChange_tmul, one_smul]
      using hcomm l
  let K : Submodule k H := LinearMap.ker D
  let yΩ : HΩ := f.toLinearMap
  have hyΩ : DΩ yΩ = 0 := by
    apply funext
    intro g
    change f.toLinearMap ∘ₗ (Representation.baseChange k Ω G M ρ) g -
      (Representation.baseChange k Ω G N σ) g ∘ₗ f.toLinearMap = 0
    exact sub_eq_zero.mpr (f.isIntertwining' g)
  let zΩ : Ω ⊗[k] H := hb.equiv.symm yΩ
  have hzD : D.baseChange Ω zΩ = 0 := by
    apply hbG.equiv.injective
    rw [map_zero]
    have hs := LinearMap.congr_fun hsquare zΩ
    rw [LinearMap.comp_apply, LinearMap.comp_apply] at hs
    calc
      hbG.equiv (D.baseChange Ω zΩ) = DΩ (hb.equiv zΩ) := hs.symm
      _ = DΩ yΩ := by rw [hb.equiv.apply_symm_apply]
      _ = 0 := hyΩ
  have hexact : Function.Exact (K.subtype.baseChange Ω) (D.baseChange Ω) := by
    simpa only [LinearMap.baseChange_eq_ltensor] using
      Module.Flat.lTensor_exact Ω D.exact_subtype_ker_map
  have hzrange : zΩ ∈ LinearMap.range (K.subtype.baseChange Ω) := by
    rw [LinearMap.exact_iff] at hexact
    rw [← hexact]
    exact hzD
  obtain ⟨z, hz⟩ := hzrange
  obtain ⟨n, a, q, hq⟩ := TensorProduct.exists_sum_tmul_eq z
  let maps : Fin n → ρ.IntertwiningMap σ := fun i =>
    { toLinearMap := (q i).1
      isIntertwining' := fun g => by
        have hzero : D (q i).1 = 0 := (q i).2
        exact sub_eq_zero.mp (congrFun hzero g) }
  refine ⟨n, a, maps, ?_⟩
  have hy : hb.equiv zΩ = yΩ := hb.equiv.apply_symm_apply yΩ
  change yΩ = _
  rw [← hy, ← hz, hq]
  simp only [map_sum, LinearMap.baseChange_tmul, IsBaseChange.equiv_tmul,
    K, maps, hb_apply, Representation.IntertwiningMap.ba_c_l,
    Submodule.subtype_apply]

/-- **Lemma VII.3.2.** Isomorphism after extending scalars descends over an
infinite ground field. -/
theorem changeSpanningStatement :
    ∀ (k : Type u) (Ω : Type v) (G : Type w) (M : Type x) (N : Type y)
      [Field k] [Infinite k] [Field Ω] [Algebra k Ω]
      [Group G] [Finite G]
      [AddCommGroup M] [Module k M] [Module.Finite k M]
      [AddCommGroup N] [Module k N] [Module.Finite k N]
      (ρ : Representation k G M) (σ : Representation k G N),
      Nonempty ((Representation.baseChange k Ω G M ρ).Equiv
        (Representation.baseChange k Ω G N σ)) → Nonempty (ρ.Equiv σ) :=
  representation_statement_bridge intertwiningSpanningBridge

end

end Towers.CField.HQuotie
