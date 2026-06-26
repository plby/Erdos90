import Mathlib.GroupTheory.Complement
import Mathlib.RepresentationTheory.FiniteIndex
import Mathlib.RepresentationTheory.Rep.Iso

/-!
# Milne, Class Field Theory, Remark II.1.3(a,b)

This file records the concrete representation isomorphisms underlying
Milne's description of induced modules.  For a finite group, coinduction
from the trivial subgroup is the regular representation tensored with the
underlying module.  After restriction to a subgroup, the regular basis is
regrouped according to a right transversal.
-/

namespace Submission.CField.COps

open CategoryTheory MonoidalCategory Rep
open scoped TensorProduct

universe u

variable {k G : Type u} [CommRing k] [Group G]

section PartA

variable [Finite G] (V : Type u) [AddCommGroup V] [Module k V]

noncomputable local instance : DecidableEq G := Classical.decEq G

/-- Coinduction from the trivial subgroup has no equivariance condition on
its underlying functions. -/
noncomputable def coindBotFun :
    Rep.coind (⊥ : Subgroup G).subtype (Rep.trivial k (⊥ : Subgroup G) V) ≃ₗ[k]
      (G → V) where
  toFun f := f.1
  invFun f := ⟨f, by
    intro h g
    have hh : h = (1 : (⊥ : Subgroup G)) :=
      Subtype.ext (Subgroup.mem_bot.mp h.2)
    subst hh
    simp⟩
  left_inv f := Subtype.ext rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The underlying linear equivalence in Remark II.1.3(a).  In coordinates
it sends `φ` to `∑ g, g ⊗ φ(g⁻¹)`. -/
noncomputable def coindBotRegular :
    Rep.coind (⊥ : Subgroup G).subtype (Rep.trivial k (⊥ : Subgroup G) V) ≃ₗ[k]
      TensorProduct k (G →₀ k) V :=
  by
    classical
    exact (coindBotFun V).trans <|
      (LinearEquiv.funCongrLeft k V (Equiv.inv G)).trans <|
        (Finsupp.linearEquivFunOnFinite k V G).symm.trans
          (TensorProduct.finsuppScalarLeft k V G).symm

@[simp]
lemma coind_bot_regular
    (f : Rep.coind (⊥ : Subgroup G).subtype (Rep.trivial k (⊥ : Subgroup G) V))
    (g : G) :
    TensorProduct.finsuppScalarLeft k V G
        (coindBotRegular V f) g = f.1 g⁻¹ := by
  simp only [coindBotRegular, LinearEquiv.trans_apply]
  calc
    _ = ((Finsupp.linearEquivFunOnFinite k V G).symm
          ((LinearEquiv.funCongrLeft k V (Equiv.inv G))
            (coindBotFun V f))) g :=
      DFunLike.congr_fun
        ((TensorProduct.finsuppScalarLeft k V G).apply_symm_apply _) g
    _ = f.1 g⁻¹ := by
      simp [coindBotFun, LinearEquiv.funCongrLeft_apply, LinearMap.funLeft]

lemma coind_regular_finsupp
    (f : G →₀ V) :
    coindBotRegular V
        ((coindBotFun V).symm fun g ↦ f g⁻¹) =
      (TensorProduct.finsuppScalarLeft k V G).symm f := by
  classical
  apply (TensorProduct.finsuppScalarLeft k V G).injective
  ext g
  rw [coind_bot_regular]
  simp [coindBotFun]

omit [Finite G] in
lemma finsupp_scalar_regular
    (h g : G) (x : TensorProduct k (G →₀ k) V) :
    TensorProduct.finsuppScalarLeft k V G
        (TensorProduct.map ((Rep.leftRegular k G).ρ h) LinearMap.id x) g =
      TensorProduct.finsuppScalarLeft k V G x (h⁻¹ * g) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul p v => simp [TensorProduct.finsuppScalarLeft_apply_tmul_apply]
  | add x y hx hy => simp [hx, hy]

/-- **Remark II.1.3(a).** For finite `G`, Milne's function-valued induced
module is isomorphic to the left regular representation tensored with its
underlying coefficient module. -/
noncomputable def coindRegularTensor :
    Rep.coind (⊥ : Subgroup G).subtype (Rep.trivial k (⊥ : Subgroup G) V) ≅
      (Rep.leftRegular k G ⊗ Rep.trivial k G V) := by
  classical
  exact Rep.mkIso {
    toLinearEquiv := coindBotRegular V
    isIntertwining' := fun h ↦ by
      apply LinearMap.ext
      intro f
      apply (TensorProduct.finsuppScalarLeft k V G).injective
      ext g
      change TensorProduct.finsuppScalarLeft k V G
          (coindBotRegular V
            ((Representation.coind (⊥ : Subgroup G).subtype
              (Rep.trivial k (⊥ : Subgroup G) V).ρ) h f)) g =
        TensorProduct.finsuppScalarLeft k V G
          (TensorProduct.map ((Rep.leftRegular k G).ρ h)
            ((Rep.trivial k G V).ρ h)
            (coindBotRegular V f)) g
      rw [show (Rep.trivial k G V).ρ h = LinearMap.id by ext; simp]
      rw [finsupp_scalar_regular]
      rw [coind_bot_regular,
        coind_bot_regular]
      simp [Representation.coind_apply] }

end PartA

section PartB

variable (H : Subgroup G) (T : H.RightTransversal)
variable (V : Type u) [AddCommGroup V] [Module k V]

/-- Multiplication gives the unique decomposition `g = h * t` associated to
a chosen right transversal. -/
noncomputable def rightTransversalEquiv : H × ↥(T : Set G) ≃ G :=
  Equiv.ofBijective (fun p ↦ (p.1 : G) * (p.2 : G)) T.2

/-- Regroup finitely supported coefficients on `G` first by `H` and then by
the chosen right transversal. -/
noncomputable def rightTransversalFinsupp :
    (G →₀ V) ≃ₗ[k] H →₀ ↥(T : Set G) →₀ V := by
  classical
  exact (Finsupp.domLCongr (rightTransversalEquiv H T).symm).trans
    (Finsupp.curryLinearEquiv k)

@[simp]
theorem transversal_finsupp_single
    (h : H) (t : ↥(T : Set G)) (v : V) :
    rightTransversalFinsupp (k := k) H T V
        (Finsupp.single ((h : G) * (t : G)) v) =
      Finsupp.single h (Finsupp.single t v) := by
  classical
  have hinv : (rightTransversalEquiv H T).symm ((h : G) * (t : G)) = (h, t) := by
    exact (rightTransversalEquiv H T).symm_apply_apply (h, t)
  simp only [rightTransversalFinsupp, LinearEquiv.trans_apply,
    Finsupp.domLCongr_single]
  rw [hinv]
  simp

/-- The underlying linear equivalence which regroups the regular tensor
according to the right-coset decomposition `G = ⋃ₜ Ht`. -/
noncomputable def restrictRegularTensor :
    TensorProduct k (G →₀ k) V ≃ₗ[k]
      TensorProduct k (H →₀ k) (↥(T : Set G) →₀ V) := by
  classical
  exact (TensorProduct.finsuppScalarLeft k V G).trans <|
    (rightTransversalFinsupp H T V).trans
      (TensorProduct.finsuppScalarLeft k (↥(T : Set G) →₀ V) H).symm

@[simp]
theorem restrict_regular_tensor
    (h : H) (t : ↥(T : Set G)) (r : k) (v : V) :
    restrictRegularTensor H T V
        (Finsupp.single ((h : G) * (t : G)) r ⊗ₜ[k] v) =
      Finsupp.single h r ⊗ₜ[k] Finsupp.single t v := by
  classical
  simp only [restrictRegularTensor, LinearEquiv.trans_apply]
  rw [TensorProduct.finsuppScalarLeft_apply_tmul]
  have hs : (Finsupp.single ((h : G) * (t : G)) r).sum
      (fun i a ↦ Finsupp.single i (a • v)) =
        Finsupp.single ((h : G) * (t : G)) (r • v) := by simp
  rw [hs, transversal_finsupp_single (k := k),
    TensorProduct.finsuppScalarLeft_symm_apply_single]
  rw [show Finsupp.single t (r • v) = r • Finsupp.single t v by simp]
  rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul']
  simp

theorem restrict_regular_single
    (h₀ h : H) (t : ↥(T : Set G)) (r : k) (v : V) :
    restrictRegularTensor H T V
        (Finsupp.single ((h₀ : G) * ((h : G) * (t : G))) r ⊗ₜ[k] v) =
      Finsupp.single (h₀ * h) r ⊗ₜ[k] Finsupp.single t v := by
  classical
  rw [show (h₀ : G) * ((h : G) * (t : G)) =
    ((h₀ * h : H) : G) * (t : G) by simp [mul_assoc]]
  rw [restrict_regular_tensor]

/-- **Remark II.1.3(b).** Restricting a regular tensor representation to
`H` is again a regular tensor representation.  Its coefficient module is
the direct sum of one copy of `V` for every chosen right-coset
representative, exactly Milne's module `M₁ = ⊕ₛ {}^s M₀`. -/
noncomputable def restrictRegularIso :
    Rep.res H.subtype (Rep.leftRegular k G ⊗ Rep.trivial k G V) ≅
      (Rep.leftRegular k H ⊗ Rep.trivial k H (↥(T : Set G) →₀ V)) :=
  Rep.mkIso {
    toLinearEquiv := restrictRegularTensor H T V
    isIntertwining' := fun h₀ ↦ by
      apply LinearMap.ext
      intro x
      change restrictRegularTensor H T V
          (TensorProduct.map ((Rep.leftRegular k G).ρ (h₀ : G)) LinearMap.id x) =
        TensorProduct.map ((Rep.leftRegular k H).ρ h₀) LinearMap.id
          (restrictRegularTensor H T V x)
      induction x using TensorProduct.induction_on with
      | zero => simp
      | add x y hx hy =>
          simpa only [map_add, LinearMap.comp_apply] using congrArg₂ (· + ·) hx hy
      | tmul p v =>
          induction p using Finsupp.induction_linear with
          | zero => simp
          | add p q hp hq =>
              simpa only [TensorProduct.add_tmul, map_add, LinearMap.comp_apply] using
                congrArg₂ (· + ·) hp hq
          | single g r =>
              obtain ⟨⟨h, t⟩, rfl⟩ := (rightTransversalEquiv H T).surjective g
              simpa [rightTransversalEquiv] using
                restrict_regular_single H T V h₀ h t r v }

end PartB

end Submission.CField.COps
