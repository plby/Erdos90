import Submission.Group.ExponentVector
import Submission.Group.Frattini
import Submission.Group.FrattiniFunctor
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Exponent vectors kill the mod-`p` Frattini subgroup of a free group

This is the easy direction of the familiar identification of the degree-one quotient
of a free group with the free `ZMod p`-module on its generators.
-/

open scoped commutatorElement

namespace Submission

noncomputable section

variable (p : ℕ) (α : Type*)

/-- The exponent-vector hom kills all `p`th powers in the free group. -/
theorem p_vector_ker :
    pPowerSubgroup p (FreeGroup α) ≤ MonoidHom.ker (exponentVectorHom p α) := by
  refine Subgroup.normalClosure_le_normal ?_
  intro x hx
  rcases hx with ⟨w, rfl⟩
  change exponentVectorHom p α (w ^ p) = 1
  apply Multiplicative.toAdd.injective
  change exponentVector p α (w ^ p) = 0
  rw [exponentVector_pow]
  rw [← Nat.cast_smul_eq_nsmul (R := ZMod p)]
  simp

/-- The exponent-vector hom kills the commutator subgroup of the free group. -/
theorem exponent_vector_ker :
    _root_.commutator (FreeGroup α) ≤ MonoidHom.ker (exponentVectorHom p α) := by
  rw [_root_.commutator_def]
  rw [Subgroup.commutator_le]
  intro u _ v _
  change exponentVectorHom p α ⁅u, v⁆ = 1
  apply Multiplicative.toAdd.injective
  change exponentVector p α ⁅u, v⁆ = 0
  exact exponentVector_commutator p α u v

/-- Consequently, the mod-`p` Frattini subgroup of a free group lies in the kernel of
its exponent-vector hom. -/
theorem mod_vector_ker :
    modPFrattini p (FreeGroup α) ≤ MonoidHom.ker (exponentVectorHom p α) := by
  dsimp [modPFrattini]
  apply sup_le
  · exact p_vector_ker p α
  · exact exponent_vector_ker p α

end
end Submission

namespace Submission

noncomputable section

variable (p : ℕ) (α : Type*)

/-- The canonical linear map from exponent vectors to the mod-`p` Frattini quotient
of a free group. -/
def freeLinear :
    eModule p α →ₗ[ZMod p] mFAdditi p (FreeGroup α) :=
  Finsupp.linearCombination (ZMod p)
    (fun x : α => Additive.ofMul (mFQuot.mk p (FreeGroup α) (FreeGroup.of x)))

/-- The free exponent-to-quotient map on a single basis vector. -/
@[simp] theorem free_linear_single (x : α) (a : ZMod p) :
    freeLinear p α (Finsupp.single x a) =
      a • Additive.ofMul (mFQuot.mk p (FreeGroup α) (FreeGroup.of x)) := by
  simp [freeLinear]

/-- The free exponent-to-quotient map on a basis vector with coefficient one. -/
@[simp] theorem free_exponent_single (x : α) :
    freeLinear p α (Finsupp.single x (1 : ZMod p)) =
      Additive.ofMul (mFQuot.mk p (FreeGroup α) (FreeGroup.of x)) := by
  simp

/-- Evaluating the free linear map on a word's exponent vector recovers its quotient class. -/
theorem free_exponent_vector (w : FreeGroup α) :
    freeLinear p α (exponentVector p α w) =
      Additive.ofMul (mFQuot.mk p (FreeGroup α) w) := by
  induction w using FreeGroup.induction_on with
  | C1 => simp [freeLinear]
  | of x => simp [freeLinear]
  | inv_of x hx =>
      simp [freeLinear]
  | mul u v hu hv =>
      simp only [exponentVector_mul, map_add, map_mul, ofMul_mul]
      rw [hu, hv]

end
end Submission

namespace Submission

noncomputable section

variable (p : ℕ) (α : Type*)

/-- The kernel of the free exponent-vector hom is contained in the mod-`p`
Frattini subgroup. -/
theorem vector_p_frattini :
    MonoidHom.ker (exponentVectorHom p α) ≤ modPFrattini p (FreeGroup α) := by
  intro w hw
  have hv : exponentVector p α w = 0 := by
    change exponentVectorHom p α w = 1 at hw
    apply Multiplicative.toAdd.injective
    simpa [exponentVector] using hw
  have hqAdd : Additive.ofMul (mFQuot.mk p (FreeGroup α) w) = 0 := by
    rw [← free_exponent_vector (p := p) (α := α) w, hv]
    simp [freeLinear]
  have hq : mFQuot.mk p (FreeGroup α) w = 1 := by
    exact Additive.ofMul.injective hqAdd
  exact (QuotientGroup.eq_one_iff (N := modPFrattini p (FreeGroup α)) w).1 hq

/-- The kernel of the exponent-vector hom on a free group is the mod-`p` Frattini subgroup. -/
theorem exponent_vector_frattini :
    MonoidHom.ker (exponentVectorHom p α) = modPFrattini p (FreeGroup α) := by
  apply le_antisymm
  · exact vector_p_frattini p α
  · exact mod_vector_ker p α

/-- Membership in the free mod-`p` Frattini subgroup is exactly vanishing of the
mod-`p` exponent vector. -/
@[simp] theorem mod_frattini_free (w : FreeGroup α) :
    w ∈ modPFrattini p (FreeGroup α) ↔ exponentVector p α w = 0 := by
  rw [← exponent_vector_frattini (p := p) (α := α)]
  exact vector_hom_ker p α w

/-- Two free words differ by the free Frattini subgroup iff they have the same exponent vector. -/
@[simp] theorem div_frattini_free (u v : FreeGroup α) :
    u / v ∈ modPFrattini p (FreeGroup α) ↔
      exponentVector p α u = exponentVector p α v := by
  rw [mod_frattini_free]
  rw [exponentVector_div]
  exact sub_eq_zero

end
end Submission

namespace Submission

noncomputable section

variable (p : ℕ) (α : Type*)

/-- The quotient map induced by exponent vectors, landing in the multiplicative
tag of the module. -/
def freeExponentHom :
    mFQuot p (FreeGroup α) →* Multiplicative (eModule p α) :=
  QuotientGroup.lift (modPFrattini p (FreeGroup α)) (exponentVectorHom p α) (by
    intro w hw
    have hker := (mod_vector_ker p α) hw
    simpa [MonoidHom.mem_ker] using hker)

/-- Additive/linear form of the quotient-to-exponent-vector map. -/
def freeExponentAdd :
    mFAdditi p (FreeGroup α) →+ eModule p α where
  toFun q := Multiplicative.toAdd (freeExponentHom p α (Additive.toMul q))
  map_zero' := by rfl
  map_add' x y := by
    change Multiplicative.toAdd
        ((freeExponentHom p α) (Additive.toMul x * Additive.toMul y)) = _
    rw [map_mul]
    rfl

/-- The induced `ZMod p`-linear map from the free mod-`p` Frattini quotient to exponent vectors. -/
def freeExponentLinear :
    mFAdditi p (FreeGroup α) →ₗ[ZMod p] eModule p α :=
  (freeExponentAdd p α).toZModLinearMap p

@[simp] theorem free_exponent_mk (w : FreeGroup α) :
    freeExponentLinear p α
      (Additive.ofMul (mFQuot.mk p (FreeGroup α) w)) =
    exponentVector p α w := by
  rfl

end
end Submission

namespace Submission

noncomputable section

variable (p : ℕ) (α : Type*)

@[simp] theorem free_linear_inverse
    (q : mFAdditi p (FreeGroup α)) :
    freeLinear p α (freeExponentLinear p α q) = q := by
  induction q using Additive.rec with
  | ofMul q0 =>
    refine QuotientGroup.induction_on q0 ?_
    intro w
    change freeLinear p α (exponentVector p α w) =
      Additive.ofMul (mFQuot.mk p (FreeGroup α) w)
    exact free_exponent_vector p α w

end
end Submission

namespace Submission

noncomputable section

variable (p : ℕ) (α : Type*)

@[simp] theorem free_exponent_inverse
    (v : eModule p α) :
    freeExponentLinear p α (freeLinear p α v) = v := by
  -- prove by finsupp induction
  classical
  induction v using Finsupp.induction_linear with
  | zero => simp [freeLinear]
  | add f g hf hg => simp [map_add, hf, hg]
  | single a r =>
      simp [freeLinear]

end
end Submission

namespace Submission

noncomputable section

variable (p : ℕ) (α : Type*)

/-- The mod-`p` Frattini quotient of a free group is linearly equivalent to the free
`ZMod p`-module of exponent vectors. -/
def freeFrattiniExponent :
    mFAdditi p (FreeGroup α) ≃ₗ[ZMod p] eModule p α where
  toFun := freeExponentLinear p α
  invFun := freeLinear p α
  left_inv := free_linear_inverse p α
  right_inv := free_exponent_inverse p α
  map_add' := by intro x y; exact (freeExponentLinear p α).map_add x y
  map_smul' := by intro a x; exact (freeExponentLinear p α).map_smul a x

@[simp] theorem free_frattini_mk (w : FreeGroup α) :
    freeFrattiniExponent p α
      (Additive.ofMul (mFQuot.mk p (FreeGroup α) w)) =
    exponentVector p α w := by
  rfl

end
end Submission

namespace Submission

noncomputable section

variable (p : ℕ) (α : Type*)

@[simp] theorem free_linear_exponent :
    (freeFrattiniExponent p α).toLinearMap =
      freeExponentLinear p α := rfl

@[simp] theorem free_frattini_symm :
    (freeFrattiniExponent p α).symm.toLinearMap =
      freeLinear p α := rfl

/-- The inverse equivalence sends a single basis vector to the corresponding quotient generator. -/
@[simp] theorem free_frattini_single (x : α) (a : ZMod p) :
    (freeFrattiniExponent p α).symm (Finsupp.single x a) =
      a • Additive.ofMul (mFQuot.mk p (FreeGroup α) (FreeGroup.of x)) := by
  change freeLinear p α (Finsupp.single x a) = _
  simp

/-- The quotient-to-exponent equivalence sends a quotient generator to its basis vector. -/
@[simp] theorem frattini_linear_exponent (x : α) :
    freeFrattiniExponent p α
      (Additive.ofMul (mFQuot.mk p (FreeGroup α) (FreeGroup.of x))) =
      Finsupp.single x (1 : ZMod p) := by
  simp

@[simp] theorem frattini_exponent_symm
    (q : mFAdditi p (FreeGroup α)) :
    (freeFrattiniExponent p α).symm
        (freeExponentLinear p α q) = q := by
  exact (freeFrattiniExponent p α).left_inv q

@[simp] theorem free_linear_symm
    (v : eModule p α) :
    freeExponentLinear p α
        ((freeFrattiniExponent p α).symm v) = v := by
  exact (freeFrattiniExponent p α).right_inv v

/-- Equality to the free quotient-to-exponent map, rewritten through the inverse equivalence. -/
theorem free_exponent_symm
    (q : mFAdditi p (FreeGroup α)) (v : eModule p α) :
    freeExponentLinear p α q = v ↔
      q = (freeFrattiniExponent p α).symm v := by
  constructor
  · intro h
    rw [← h]
    exact (frattini_exponent_symm p α q).symm
  · intro h
    rw [h]
    exact free_linear_symm p α v

@[simp] theorem free_frattini_exponent
    (v : eModule p α) :
    (freeFrattiniExponent p α)
        (freeLinear p α v) = v := by
  exact (freeFrattiniExponent p α).right_inv v

@[simp] theorem free_linear_equiv
    (q : mFAdditi p (FreeGroup α)) :
    freeLinear p α
        ((freeFrattiniExponent p α) q) = q := by
  exact (freeFrattiniExponent p α).left_inv q

/-- Equality to the exponent-to-quotient map, rewritten through the forward equivalence. -/
theorem free_exponent_equiv
    (v : eModule p α) (q : mFAdditi p (FreeGroup α)) :
    freeLinear p α v = q ↔
      v = (freeFrattiniExponent p α) q := by
  constructor
  · intro h
    rw [← h]
    exact (free_frattini_exponent p α v).symm
  · intro h
    rw [h]
    exact free_linear_equiv p α q

/-- Naturality of the free quotient-to-exponent map under relabeling generators. -/
theorem free_linear_naturality {β : Type*} (f : α → β)
    (q : mFAdditi p (FreeGroup α)) :
    freeExponentLinear p β
      (mFAdditi.mapLinear (p := p) (FreeGroup.map f) q) =
    exponentModuleMap p α f (freeExponentLinear p α q) := by
  induction q using Additive.rec with
  | ofMul q0 =>
    refine QuotientGroup.induction_on q0 ?_
    intro w
    change exponentVector p β ((FreeGroup.map f) w) =
      exponentModuleMap p α f (exponentVector p α w)
    simp

/-- Coordinate form of quotient-to-exponent naturality for generator equivalences. -/
@[simp] theorem free_exponent_naturality {β : Type*}
    (e : α ≃ β) (q : mFAdditi p (FreeGroup α)) (y : β) :
    freeExponentLinear p β
        (mFAdditi.mapLinear (p := p) (FreeGroup.map e) q) y =
      freeExponentLinear p α q (e.symm y) := by
  rw [free_linear_naturality]
  exact exponent_module p α e (freeExponentLinear p α q) y

/-- Naturality of the inverse exponent-to-quotient map under relabeling generators. -/
theorem exponent_linear_naturality {β : Type*} (f : α → β)
    (v : eModule p α) :
    freeLinear p β (exponentModuleMap p α f v) =
      mFAdditi.mapLinear (p := p) (FreeGroup.map f)
        (freeLinear p α v) := by
  apply (freeFrattiniExponent p β).injective
  change freeExponentLinear p β
      (freeLinear p β (exponentModuleMap p α f v)) =
    freeExponentLinear p β
      (mFAdditi.mapLinear (p := p) (FreeGroup.map f)
        (freeLinear p α v))
  rw [free_linear_naturality]
  simp

/-- The free Frattini relabeling map for the identity generator map is the identity. -/
@[simp] theorem free_frattini_id :
    (mFAdditi.mapLinear (p := p)
      (FreeGroup.map (fun x : α => x)) :
        mFAdditi p (FreeGroup α) →ₗ[ZMod p]
          mFAdditi p (FreeGroup α)) = LinearMap.id := by
  ext q
  apply (freeFrattiniExponent p α).injective
  change freeExponentLinear p α
      (mFAdditi.mapLinear (p := p) (FreeGroup.map (fun x : α => x)) q) =
    freeExponentLinear p α q
  rw [free_linear_naturality]
  simp

/-- Free Frattini relabeling maps compose functorially on generator maps. -/
@[simp] theorem free_frattini_comp {β γ : Type*} (f : α → β) (g : β → γ) :
    (mFAdditi.mapLinear (p := p) (FreeGroup.map g)).comp
        (mFAdditi.mapLinear (p := p) (FreeGroup.map f)) =
      (mFAdditi.mapLinear (p := p) (FreeGroup.map (g ∘ f)) :
        mFAdditi p (FreeGroup α) →ₗ[ZMod p]
          mFAdditi p (FreeGroup γ)) := by
  ext q
  apply (freeFrattiniExponent p γ).injective
  change freeExponentLinear p γ
      ((mFAdditi.mapLinear (p := p) (FreeGroup.map g))
        ((mFAdditi.mapLinear (p := p) (FreeGroup.map f)) q)) =
    freeExponentLinear p γ
      ((mFAdditi.mapLinear (p := p) (FreeGroup.map (g ∘ f))) q)
  rw [free_linear_naturality]
  rw [free_linear_naturality]
  rw [free_linear_naturality]
  exact congrFun (congrArg DFunLike.coe (exponent_module_comp (p := p) (α := α) f g))
    (freeExponentLinear p α q)

/-- An injective relabeling of generators induces an injective map on free Frattini quotients. -/
theorem free_injective_generators {β : Type*}
    (f : α → β) (hf : Function.Injective f) :
    Function.Injective (mFAdditi.mapLinear (p := p) (FreeGroup.map f) :
      mFAdditi p (FreeGroup α) →ₗ[ZMod p]
        mFAdditi p (FreeGroup β)) := by
  intro q₁ q₂ h
  apply (freeFrattiniExponent p α).injective
  change freeExponentLinear p α q₁ = freeExponentLinear p α q₂
  apply exponent_module_injective p α f hf
  calc
    exponentModuleMap p α f (freeExponentLinear p α q₁) =
        freeExponentLinear p β
          (mFAdditi.mapLinear (p := p) (FreeGroup.map f) q₁) := by
      rw [free_linear_naturality]
    _ = freeExponentLinear p β
          (mFAdditi.mapLinear (p := p) (FreeGroup.map f) q₂) := by
      rw [h]
    _ = exponentModuleMap p α f (freeExponentLinear p α q₂) := by
      rw [free_linear_naturality]

/-- A surjective relabeling of generators induces a surjective map on free Frattini quotients. -/
theorem free_surjective_generators {β : Type*}
    (f : α → β) (hf : Function.Surjective f) :
    Function.Surjective (mFAdditi.mapLinear (p := p) (FreeGroup.map f) :
      mFAdditi p (FreeGroup α) →ₗ[ZMod p]
        mFAdditi p (FreeGroup β)) := by
  intro q
  obtain ⟨v, hv⟩ := module_surjective p α f hf
    (freeExponentLinear p β q)
  refine ⟨freeLinear p α v, ?_⟩
  apply (freeFrattiniExponent p β).injective
  change freeExponentLinear p β
      (mFAdditi.mapLinear (p := p) (FreeGroup.map f)
        (freeLinear p α v)) = freeExponentLinear p β q
  rw [free_linear_naturality]
  rw [← hv]
  simp

/-- Kernel form for the free Frattini map induced by an injective generator relabeling. -/
theorem free_bot_generators {β : Type*}
    (f : α → β) (hf : Function.Injective f) :
    LinearMap.ker (mFAdditi.mapLinear (p := p) (FreeGroup.map f) :
      mFAdditi p (FreeGroup α) →ₗ[ZMod p]
        mFAdditi p (FreeGroup β)) = ⊥ := by
  exact LinearMap.ker_eq_bot_of_injective
    (free_injective_generators p α f hf)

/-- Range form for the free Frattini map induced by a surjective generator relabeling. -/
theorem free_frattini_generators {β : Type*}
    (f : α → β) (hf : Function.Surjective f) :
    LinearMap.range (mFAdditi.mapLinear (p := p) (FreeGroup.map f) :
      mFAdditi p (FreeGroup α) →ₗ[ZMod p]
        mFAdditi p (FreeGroup β)) = ⊤ := by
  exact LinearMap.range_eq_top_of_surjective _
    (free_surjective_generators p α f hf)

/-- The linear equivalence on free Frattini quotients induced by an equivalence of generators. -/
def freeFrattiniRelabel {β : Type*} (e : α ≃ β) :
    mFAdditi p (FreeGroup α) ≃ₗ[ZMod p]
      mFAdditi p (FreeGroup β) :=
  (freeFrattiniExponent p α).trans
    ((exponentModuleEquiv p α e).trans
      (freeFrattiniExponent p β).symm)

@[simp] theorem frattini_relabel_equiv {β : Type*} (e : α ≃ β)
    (q : mFAdditi p (FreeGroup α)) :
    freeFrattiniRelabel p α e q =
      mFAdditi.mapLinear (p := p) (FreeGroup.map e) q := by
  apply (freeFrattiniExponent p β).injective
  change freeExponentLinear p β
      (freeFrattiniRelabel p α e q) =
    freeExponentLinear p β
      (mFAdditi.mapLinear (p := p) (FreeGroup.map e) q)
  rw [show freeFrattiniRelabel p α e q =
      (freeFrattiniExponent p β).symm
        ((exponentModuleEquiv p α e) ((freeFrattiniExponent p α) q)) by rfl]
  change (freeFrattiniExponent p β)
      ((freeFrattiniExponent p β).symm
        ((exponentModuleEquiv p α e) ((freeFrattiniExponent p α) q))) =
    freeExponentLinear p β
      (mFAdditi.mapLinear (p := p) (FreeGroup.map e) q)
  rw [(freeFrattiniExponent p β).apply_symm_apply]
  change (exponentModuleMap p α e) (freeExponentLinear p α q) =
    freeExponentLinear p β
      (mFAdditi.mapLinear (p := p) (FreeGroup.map e) q)
  rw [free_linear_naturality]

/-- Representative formula for the free Frattini relabeling equivalence. -/
@[simp] theorem free_relabel_mk {β : Type*} (e : α ≃ β)
    (w : FreeGroup α) :
    freeFrattiniRelabel p α e
        (Additive.ofMul (mFQuot.mk p (FreeGroup α) w)) =
      Additive.ofMul (mFQuot.mk p (FreeGroup β) (FreeGroup.map e w)) := by
  rw [frattini_relabel_equiv]
  rfl

/-- Coordinate form of the free Frattini relabeling equivalence after identifying with exponents. -/
@[simp] theorem frattini_relabel_exponent {β : Type*}
    (e : α ≃ β) (q : mFAdditi p (FreeGroup α)) (y : β) :
    freeExponentLinear p β (freeFrattiniRelabel p α e q) y =
      freeExponentLinear p α q (e.symm y) := by
  rw [frattini_relabel_equiv]
  exact free_exponent_naturality p α e q y

@[simp] theorem frattini_relabel_linear {β : Type*} (e : α ≃ β) :
    (freeFrattiniRelabel p α e).toLinearMap =
      mFAdditi.mapLinear (p := p) (FreeGroup.map e) := by
  ext q
  exact frattini_relabel_equiv p α e q

@[simp] theorem relabel_linear_symm {β : Type*} (e : α ≃ β)
    (q : mFAdditi p (FreeGroup β)) :
    (freeFrattiniRelabel p α e).symm q =
      mFAdditi.mapLinear (p := p) (FreeGroup.map e.symm) q := by
  apply (freeFrattiniRelabel p α e).injective
  rw [LinearEquiv.apply_symm_apply]
  rw [frattini_relabel_equiv]
  symm
  change ((mFAdditi.mapLinear (p := p) (FreeGroup.map e))
      ((mFAdditi.mapLinear (p := p) (FreeGroup.map e.symm)) q)) = q
  rw [← LinearMap.comp_apply]
  have hcomp : (FreeGroup.map e).comp (FreeGroup.map e.symm) =
      MonoidHom.id (FreeGroup β) := by
    apply MonoidHom.ext
    intro w
    change (FreeGroup.map e) ((FreeGroup.map e.symm) w) = w
    rw [FreeGroup.map.comp]
    change (FreeGroup.map (fun x : β => e (e.symm x))) w = w
    simp
  rw [← mFAdditi.mapLinear_comp (p := p)
    (FreeGroup.map e.symm) (FreeGroup.map e)]
  rw [hcomp, mFAdditi.mapLinear_id]
  rfl

/-- Representative formula for the inverse free Frattini relabeling equivalence. -/
@[simp] theorem frattini_relabel_mk {β : Type*} (e : α ≃ β)
    (w : FreeGroup β) :
    (freeFrattiniRelabel p α e).symm
        (Additive.ofMul (mFQuot.mk p (FreeGroup β) w)) =
      Additive.ofMul (mFQuot.mk p (FreeGroup α) (FreeGroup.map e.symm w)) := by
  rw [relabel_linear_symm]
  rfl

@[simp] theorem frattini_relabel_symm {β : Type*} (e : α ≃ β) :
    (freeFrattiniRelabel p α e).symm.toLinearMap =
      mFAdditi.mapLinear (p := p) (FreeGroup.map e.symm) := by
  ext q
  exact relabel_linear_symm p α e q

/-- The inverse free Frattini relabeling equivalence uses the inverse generators. -/
@[simp] theorem free_relabel_linear {β : Type*} (e : α ≃ β) :
    (freeFrattiniRelabel p α e).symm =
      freeFrattiniRelabel p β e.symm := by
  ext q
  rw [relabel_linear_symm]
  rw [frattini_relabel_equiv]

/-- The identity generator equivalence induces the identity free Frattini equivalence. -/
@[simp] theorem frattini_relabel_refl :
    freeFrattiniRelabel p α (Equiv.refl α) =
      LinearEquiv.refl (ZMod p) (mFAdditi p (FreeGroup α)) := by
  ext q
  rw [frattini_relabel_equiv]
  change (mFAdditi.mapLinear (p := p)
      (FreeGroup.map (fun x : α => x)) q) = q
  rw [free_frattini_id]
  rfl

/-- Free Frattini relabeling equivalences compose functorially. -/
@[simp] theorem frattini_relabel_trans {β γ : Type*}
    (e : α ≃ β) (f : β ≃ γ) :
    (freeFrattiniRelabel p α e).trans
        (freeFrattiniRelabel p β f) =
      freeFrattiniRelabel p α (e.trans f) := by
  ext q
  rw [LinearEquiv.trans_apply]
  repeat rw [frattini_relabel_equiv]
  change ((mFAdditi.mapLinear (p := p) (FreeGroup.map f)).comp
      (mFAdditi.mapLinear (p := p) (FreeGroup.map e))) q =
    (mFAdditi.mapLinear (p := p) (FreeGroup.map (f ∘ e))) q
  rw [free_frattini_comp]

/-- Applying the inverse relabeling equivalence cancels the forward free Frattini map. -/
@[simp] theorem free_frattini_relabel {β : Type*} (e : α ≃ β)
    (q : mFAdditi p (FreeGroup α)) :
    (freeFrattiniRelabel p α e).symm
        (mFAdditi.mapLinear (p := p) (FreeGroup.map e) q) = q := by
  rw [← frattini_relabel_equiv (p := p) (α := α) e q]
  exact (freeFrattiniRelabel p α e).left_inv q

/-- The forward free Frattini map cancels the inverse relabeling equivalence. -/
@[simp] theorem linear_relabel_symm {β : Type*} (e : α ≃ β)
    (q : mFAdditi p (FreeGroup β)) :
    mFAdditi.mapLinear (p := p) (FreeGroup.map e)
        ((freeFrattiniRelabel p α e).symm q) = q := by
  rw [← frattini_relabel_equiv (p := p) (α := α) e]
  exact (freeFrattiniRelabel p α e).right_inv q

/-- Characterize equality to an equivalence-induced free Frattini relabeling map via its inverse. -/
theorem free_relabel_symm {β : Type*} (e : α ≃ β)
    (q : mFAdditi p (FreeGroup α))
    (r : mFAdditi p (FreeGroup β)) :
    mFAdditi.mapLinear (p := p) (FreeGroup.map e) q = r ↔
      q = (freeFrattiniRelabel p α e).symm r := by
  constructor
  · intro h
    rw [← h]
    exact (free_frattini_relabel p α e q).symm
  · intro h
    rw [h]
    exact linear_relabel_symm p α e r

/-- Equivalence-induced free Frattini relabeling maps have trivial kernel. -/
theorem free_frattini_bot {β : Type*} (e : α ≃ β) :
    LinearMap.ker (mFAdditi.mapLinear (p := p) (FreeGroup.map e) :
      mFAdditi p (FreeGroup α) →ₗ[ZMod p]
        mFAdditi p (FreeGroup β)) = ⊥ := by
  rw [← frattini_relabel_linear (p := p) (α := α) e]
  exact LinearMap.ker_eq_bot_of_injective (freeFrattiniRelabel p α e).injective

/-- Equivalence-induced free Frattini relabeling maps have full range. -/
theorem free_frattini_top {β : Type*} (e : α ≃ β) :
    LinearMap.range (mFAdditi.mapLinear (p := p) (FreeGroup.map e) :
      mFAdditi p (FreeGroup α) →ₗ[ZMod p]
        mFAdditi p (FreeGroup β)) = ⊤ := by
  rw [← frattini_relabel_linear (p := p) (α := α) e]
  exact LinearMap.range_eq_top_of_surjective _ (freeFrattiniRelabel p α e).surjective

end
end Submission

namespace Submission

noncomputable section

variable (p : ℕ) (α : Type*)

/-- The quotient-to-exponent linear map for a free group has trivial kernel. -/
theorem free_exponent_bot :
    LinearMap.ker (freeExponentLinear p α) = ⊥ := by
  rw [← free_linear_exponent (p := p) (α := α)]
  exact LinearMap.ker_eq_bot_of_injective
    (freeFrattiniExponent p α).injective

/-- The quotient-to-exponent linear map for a free group has full range. -/
theorem free_exponent_top :
    LinearMap.range (freeExponentLinear p α) = ⊤ := by
  rw [← free_linear_exponent (p := p) (α := α)]
  exact LinearMap.range_eq_top_of_surjective _
    (freeFrattiniExponent p α).surjective

/-- The exponent-to-quotient linear map for a free group has trivial kernel. -/
theorem free_ker_bot :
    LinearMap.ker (freeLinear p α) = ⊥ := by
  rw [← free_frattini_symm (p := p) (α := α)]
  exact LinearMap.ker_eq_bot_of_injective
    (freeFrattiniExponent p α).symm.injective

/-- The exponent-to-quotient linear map for a free group has full range. -/
theorem free_linear_top :
    LinearMap.range (freeLinear p α) = ⊤ := by
  rw [← free_frattini_symm (p := p) (α := α)]
  exact LinearMap.range_eq_top_of_surjective _
    (freeFrattiniExponent p α).symm.surjective

/-- The quotient-to-exponent map is injective. -/
theorem free_exponent_injective :
    Function.Injective (freeExponentLinear p α) := by
  exact (freeFrattiniExponent p α).injective

/-- The quotient-to-exponent map is surjective. -/
theorem free_exponent_surjective :
    Function.Surjective (freeExponentLinear p α) := by
  exact (freeFrattiniExponent p α).surjective

/-- The exponent-to-quotient map is injective. -/
theorem free_linear_injective :
    Function.Injective (freeLinear p α) := by
  exact (freeFrattiniExponent p α).symm.injective

/-- The exponent-to-quotient map is surjective. -/
theorem free_linear_surjective :
    Function.Surjective (freeLinear p α) := by
  exact (freeFrattiniExponent p α).symm.surjective

@[simp] theorem free_exponent_linear
    (q : mFAdditi p (FreeGroup α)) :
    freeExponentLinear p α q = 0 ↔ q = 0 := by
  constructor
  · intro h
    exact (free_exponent_injective p α) (by simpa using h)
  · intro h
    simp [h]

@[simp] theorem free_exponent_zero (v : eModule p α) :
    freeLinear p α v = 0 ↔ v = 0 := by
  constructor
  · intro h
    exact (free_linear_injective p α) (by simpa using h)
  · intro h
    simp [h]

end
end Submission

namespace Submission

noncomputable section

variable (p : ℕ) (α : Type*)

/-- The canonical basis of the free mod-`p` Frattini quotient, indexed by generators. -/
def freeFrattiniBasis : Module.Basis α (ZMod p)
    (mFAdditi p (FreeGroup α)) :=
  (Finsupp.basisSingleOne : Module.Basis α (ZMod p) (eModule p α)).map
    (freeFrattiniExponent p α).symm

/-- A basis vector is the quotient class of the corresponding free generator. -/
@[simp] theorem frattini_basis (x : α) :
    freeFrattiniBasis p α x =
      Additive.ofMul (mFQuot.mk p (FreeGroup α) (FreeGroup.of x)) := by
  simp [freeFrattiniBasis]

/-- Coordinates in the canonical free-Frattini basis are exactly exponent vectors. -/
@[simp] theorem frattini_basis_repr :
    (freeFrattiniBasis p α).repr = freeExponentLinear p α := by
  rfl

/-- Pointwise version of `frattini_basis_repr`. -/
@[simp] theorem free_frattini_repr
    (q : mFAdditi p (FreeGroup α)) :
    (freeFrattiniBasis p α).repr q = freeExponentLinear p α q := by
  rfl

/-- Representative formula for coordinates of a word in the canonical free-Frattini basis. -/
@[simp] theorem frattini_repr_mk (w : FreeGroup α) :
    (freeFrattiniBasis p α).repr
        (Additive.ofMul (mFQuot.mk p (FreeGroup α) w)) =
      exponentVector p α w := by
  rfl

/-- Coordinate formula for a word at a single generator. -/
@[simp] theorem free_repr_mk (w : FreeGroup α) (x : α) :
    (freeFrattiniBasis p α).repr
        (Additive.ofMul (mFQuot.mk p (FreeGroup α) w)) x =
      exponentVector p α w x := by
  rfl

/-- Relabeling generators sends canonical basis vectors to canonical basis vectors. -/
@[simp] theorem free_frattini_basis {β : Type*} (f : α → β) (x : α) :
    mFAdditi.mapLinear (p := p) (FreeGroup.map f)
        (freeFrattiniBasis p α x) = freeFrattiniBasis p β (f x) := by
  simp [freeFrattiniBasis]

/-- Equivalence-induced relabeling sends canonical basis vectors along the equivalence. -/
@[simp] theorem free_relabel_basis {β : Type*}
    (e : α ≃ β) (x : α) :
    freeFrattiniRelabel p α e (freeFrattiniBasis p α x) =
      freeFrattiniBasis p β (e x) := by
  rw [frattini_relabel_equiv]
  simp

/-- The inverse relabeling equivalence sends canonical basis vectors along the inverse. -/
@[simp] theorem frattini_relabel_basis {β : Type*}
    (e : α ≃ β) (y : β) :
    (freeFrattiniRelabel p α e).symm (freeFrattiniBasis p β y) =
      freeFrattiniBasis p α (e.symm y) := by
  rw [relabel_linear_symm]
  simp

/-- Extensionality for free Frattini quotient elements via exponent coordinates. -/
theorem freeFrattini_ext
    {q r : mFAdditi p (FreeGroup α)}
    (h : ∀ x : α,
      freeExponentLinear p α q x = freeExponentLinear p α r x) :
    q = r := by
  apply free_exponent_injective p α
  ext x
  exact h x

/-- Equality of additive quotient representatives is equality of exponent vectors. -/
@[simp] theorem frattini_additive_mk (u v : FreeGroup α) :
    Additive.ofMul (mFQuot.mk p (FreeGroup α) u) =
      Additive.ofMul (mFQuot.mk p (FreeGroup α) v) ↔
    exponentVector p α u = exponentVector p α v := by
  constructor
  · intro h
    simpa using congrArg (freeExponentLinear p α) h
  · intro h
    apply free_exponent_injective p α
    simpa using h

/-- Equality of multiplicative quotient representatives is equality of exponent vectors. -/
@[simp] theorem frattini_quotient_mk (u v : FreeGroup α) :
    mFQuot.mk p (FreeGroup α) u =
      mFQuot.mk p (FreeGroup α) v ↔
    exponentVector p α u = exponentVector p α v := by
  constructor
  · intro h
    have ha : Additive.ofMul (mFQuot.mk p (FreeGroup α) u) =
        Additive.ofMul (mFQuot.mk p (FreeGroup α) v) :=
      congrArg Additive.ofMul h
    simpa using congrArg (freeExponentLinear p α) ha
  · intro h
    apply Additive.ofMul.injective
    apply free_exponent_injective p α
    simpa using h

/-- A word is trivial in the free Frattini quotient exactly when its exponent vector vanishes. -/
@[simp] theorem free_mk_one (w : FreeGroup α) :
    mFQuot.mk p (FreeGroup α) w = 1 ↔
      exponentVector p α w = 0 := by
  simpa using (frattini_quotient_mk (p := p) (α := α) w 1)

end
end Submission


namespace Submission

noncomputable section

variable (p : ℕ) (α : Type*)

/-- The exponent module on a finite generator type is finite-dimensional over `ZMod p`.
This is the free-module side of the free Frattini quotient identification. -/
theorem module_finite_exponent [Fact p.Prime] [Finite α] :
    Module.Finite (ZMod p) (eModule p α) := by
  infer_instance

/-- The free mod-`p` Frattini quotient on finitely many generators is finite-dimensional. -/
theorem module_free_frattini [Fact p.Prime] [Finite α] :
    Module.Finite (ZMod p) (mFAdditi p (FreeGroup α)) := by
  exact Module.Finite.equiv (freeFrattiniExponent p α).symm

/-- The finrank of the exponent module is the number of generators. -/
@[simp] theorem finrank_exponentModule [Fact p.Prime] [Fintype α] :
    Module.finrank (ZMod p) (eModule p α) = Fintype.card α := by
  simp [eModule]

/-- The free mod-`p` Frattini quotient has finrank equal to the number of generators. -/
@[simp] theorem finrank_free_frattini [Fact p.Prime] [Fintype α] :
    Module.finrank (ZMod p) (mFAdditi p (FreeGroup α)) = Fintype.card α := by
  rw [(freeFrattiniExponent p α).finrank_eq]
  simp [eModule]

/-- A finrank form phrased through the quotient-to-exponent equivalence. -/
theorem finrank_frattini_exponent [Fact p.Prime] :
    Module.finrank (ZMod p) (mFAdditi p (FreeGroup α)) =
      Module.finrank (ZMod p) (eModule p α) := by
  exact (freeFrattiniExponent p α).finrank_eq

end
end Submission

namespace Submission

noncomputable section
variable (p : ℕ) (α : Type*)

noncomputable instance eModule.fintype [Fact p.Prime] [Fintype α] :
    Fintype (eModule p α) := by
  classical
  exact Fintype.ofEquiv (α → ZMod p) (Finsupp.equivFunOnFinite.symm)

noncomputable instance fFAdditi.fintype [Fact p.Prime] [Fintype α] :
    Fintype (mFAdditi p (FreeGroup α)) := by
  classical
  exact Fintype.ofEquiv (eModule p α)
    (freeFrattiniExponent p α).toEquiv.symm

noncomputable instance fFQuot.fintype [Fact p.Prime] [Fintype α] :
    Fintype (mFQuot p (FreeGroup α)) := by
  classical
  exact Fintype.ofEquiv (mFAdditi p (FreeGroup α)) Additive.ofMul.symm

@[simp] theorem card_exponentModule [Fact p.Prime] [Fintype α] :
    Fintype.card (eModule p α) = p ^ Fintype.card α := by
  classical
  calc
    Fintype.card (eModule p α) = Fintype.card (α → ZMod p) :=
      Fintype.card_congr Finsupp.equivFunOnFinite
    _ = Fintype.card (ZMod p) ^ Fintype.card α := by rw [Fintype.card_fun]
    _ = p ^ Fintype.card α := by rw [ZMod.card]

@[simp] theorem card_free_additive [Fact p.Prime] [Fintype α] :
    Fintype.card (mFAdditi p (FreeGroup α)) = p ^ Fintype.card α := by
  classical
  calc
    Fintype.card (mFAdditi p (FreeGroup α)) =
        Fintype.card (eModule p α) :=
      Fintype.card_congr (freeFrattiniExponent p α).toEquiv
    _ = p ^ Fintype.card α := card_exponentModule p α

@[simp] theorem card_free_frattini [Fact p.Prime] [Fintype α] :
    Fintype.card (mFQuot p (FreeGroup α)) = p ^ Fintype.card α := by
  classical
  calc
    Fintype.card (mFQuot p (FreeGroup α)) =
        Fintype.card (mFAdditi p (FreeGroup α)) :=
      Fintype.card_congr Additive.ofMul
    _ = p ^ Fintype.card α := card_free_additive p α
end
end Submission

namespace Submission

noncomputable section

variable (p : ℕ) (α : Type*) [Fact p.Prime] [Finite α]

/-- `Nat.card` of the finite exponent module on a finite generator type. -/
@[simp] theorem nat_exponent_module :
    Nat.card (eModule p α) = p ^ Nat.card α := by
  classical
  letI := Fintype.ofFinite α
  rw [Nat.card_eq_fintype_card]
  rw [card_exponentModule]
  rw [Nat.card_eq_fintype_card]

/-- `Nat.card` of the additive free Frattini quotient on finitely many generators. -/
@[simp] theorem card_frattini_additive :
    Nat.card (mFAdditi p (FreeGroup α)) = p ^ Nat.card α := by
  classical
  letI := Fintype.ofFinite α
  rw [Nat.card_eq_fintype_card]
  rw [card_free_additive]
  rw [Nat.card_eq_fintype_card]

/-- `Nat.card` of the multiplicative free Frattini quotient on finitely many generators. -/
@[simp] theorem nat_free_frattini :
    Nat.card (mFQuot p (FreeGroup α)) = p ^ Nat.card α := by
  classical
  letI := Fintype.ofFinite α
  rw [Nat.card_eq_fintype_card]
  rw [card_free_frattini]
  rw [Nat.card_eq_fintype_card]

/-- The finite exponent module has positive cardinality. -/
theorem nat_module_pos :
    0 < Nat.card (eModule p α) := by
  rw [nat_exponent_module]
  exact pow_pos (Fact.out : Nat.Prime p).pos (Nat.card α)

/-- The additive free Frattini quotient has positive cardinality. -/
theorem frattini_additive_pos :
    0 < Nat.card (mFAdditi p (FreeGroup α)) := by
  rw [card_frattini_additive]
  exact pow_pos (Fact.out : Nat.Prime p).pos (Nat.card α)

/-- The multiplicative free Frattini quotient has positive cardinality. -/
theorem nat_frattini_pos :
    0 < Nat.card (mFQuot p (FreeGroup α)) := by
  rw [nat_free_frattini]
  exact pow_pos (Fact.out : Nat.Prime p).pos (Nat.card α)

end
end Submission

namespace Submission

noncomputable section

variable (p : ℕ) (α : Type*) [Fact p.Prime] [Finite α]

/-- Finiteness of the exponent module as a type for finite generator sets. -/
theorem finite_exponent_module : Finite (eModule p α) := by
  classical
  letI := Fintype.ofFinite α
  letI : Fintype (eModule p α) := eModule.fintype p α
  infer_instance

/-- Finiteness of the additive free Frattini quotient as a type for finite generator sets. -/
theorem free_frattini_additive :
    Finite (mFAdditi p (FreeGroup α)) := by
  classical
  letI := Fintype.ofFinite α
  letI : Fintype (mFAdditi p (FreeGroup α)) :=
    fFAdditi.fintype p α
  infer_instance

/-- Finiteness of the multiplicative free Frattini quotient as a type for finite generator sets. -/
theorem free_frattini_quotient :
    Finite (mFQuot p (FreeGroup α)) := by
  classical
  letI := Fintype.ofFinite α
  letI : Fintype (mFQuot p (FreeGroup α)) :=
    fFQuot.fintype p α
  infer_instance

end
end Submission

namespace Submission

noncomputable section

variable (p : ℕ) (α : Type*) [Fact p.Prime] [Finite α]

/-- `Nat.card = p^finrank` for the finite exponent module. -/
theorem nat_module_finrank :
    Nat.card (eModule p α) =
      p ^ Module.finrank (ZMod p) (eModule p α) := by
  classical
  letI := Fintype.ofFinite α
  rw [nat_exponent_module]
  rw [finrank_exponentModule]
  rw [Nat.card_eq_fintype_card]

/-- `Nat.card = p^finrank` for the additive free Frattini quotient. -/
theorem free_frattini_finrank :
    Nat.card (mFAdditi p (FreeGroup α)) =
      p ^ Module.finrank (ZMod p) (mFAdditi p (FreeGroup α)) := by
  classical
  letI := Fintype.ofFinite α
  rw [card_frattini_additive]
  rw [finrank_free_frattini]
  rw [Nat.card_eq_fintype_card]

/-- Multiplicative free quotient version, with the exponent written using the additive
linear structure. -/
theorem nat_free_finrank :
    Nat.card (mFQuot p (FreeGroup α)) =
      p ^ Module.finrank (ZMod p) (mFAdditi p (FreeGroup α)) := by
  classical
  letI := Fintype.ofFinite α
  rw [nat_free_frattini]
  rw [finrank_free_frattini]
  rw [Nat.card_eq_fintype_card]

end
end Submission
