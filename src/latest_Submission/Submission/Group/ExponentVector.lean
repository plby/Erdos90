import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Data.ZMod.Basic

/-!
# Mod-`p` exponent vectors for free-group words

This is the degree-one abelianization of a free group, with coefficients in `ZMod p`.
It records the exponent sum of each generator.  The construction is via the universal
property of `FreeGroup` into the multiplicative type-tag of the free module.
-/

namespace Submission

noncomputable section

variable (p : ℕ) (α : Type*)

/-- The target free `ZMod p`-module for exponent vectors. -/
abbrev eModule : Type _ := α →₀ ZMod p

/-- The multiplicative hom underlying the exponent-vector map. -/
def exponentVectorHom : FreeGroup α →* Multiplicative (eModule p α) :=
  FreeGroup.lift fun x : α => Multiplicative.ofAdd (Finsupp.single x (1 : ZMod p))

/-- The mod-`p` exponent vector of a free-group word. -/
def exponentVector (w : FreeGroup α) : eModule p α :=
  Multiplicative.toAdd (exponentVectorHom p α w)

@[simp] theorem exponentVector_one : exponentVector p α 1 = 0 := by
  simp [exponentVector, exponentVectorHom]

@[simp] theorem exponentVector_of (x : α) :
    exponentVector p α (FreeGroup.of x) = Finsupp.single x (1 : ZMod p) := by
  simp [exponentVector, exponentVectorHom]

@[simp] theorem exponentVector_mul (u v : FreeGroup α) :
    exponentVector p α (u * v) = exponentVector p α u + exponentVector p α v := by
  simp [exponentVector, exponentVectorHom]

@[simp] theorem exponentVector_inv (u : FreeGroup α) :
    exponentVector p α u⁻¹ = - exponentVector p α u := by
  simp [exponentVector, exponentVectorHom]

@[simp] theorem exponentVector_div (u v : FreeGroup α) :
    exponentVector p α (u / v) = exponentVector p α u - exponentVector p α v := by
  simp [div_eq_mul_inv, sub_eq_add_neg]

@[simp] theorem vector_of_apply [DecidableEq α] (x y : α) :
    exponentVector p α (FreeGroup.of x) y = if x = y then (1 : ZMod p) else 0 := by
  simp [exponentVector_of, Finsupp.single_apply]

@[simp] theorem exponent_vector (u v : FreeGroup α) (x : α) :
    exponentVector p α (u * v) x = exponentVector p α u x + exponentVector p α v x := by
  simp

@[simp] theorem vector_inv (u : FreeGroup α) (x : α) :
    exponentVector p α u⁻¹ x = - exponentVector p α u x := by
  simp

@[simp] theorem vector_div (u v : FreeGroup α) (x : α) :
    exponentVector p α (u / v) x = exponentVector p α u x - exponentVector p α v x := by
  simp

@[simp] theorem exponentVector_pow (u : FreeGroup α) (n : ℕ) :
    exponentVector p α (u ^ n) = n • exponentVector p α u := by
  induction n with
  | zero => simp
  | succ n ih => simp [pow_succ, ih, succ_nsmul]

@[simp] theorem exponentVector_zpow (u : FreeGroup α) (n : ℤ) :
    exponentVector p α (u ^ n) = n • exponentVector p α u := by
  induction n using Int.induction_on with
  | zero => simp
  | succ n ih =>
    change exponentVector p α (u ^ ((n : ℤ) + 1)) =
      ((n : ℤ) + 1) • exponentVector p α u
    calc
      exponentVector p α (u ^ ((n : ℤ) + 1)) =
          exponentVector p α (u ^ (n : ℤ) * u) := by rw [zpow_add_one]
      _ = exponentVector p α (u ^ (n : ℤ)) + exponentVector p α u := by simp
      _ = (n : ℤ) • exponentVector p α u + exponentVector p α u := by rw [ih]
      _ = ((n : ℤ) + 1) • exponentVector p α u := by
        rw [add_zsmul, one_zsmul]
  | pred n ih =>
    change exponentVector p α (u ^ (-(n : ℤ) - 1)) =
      (-(n : ℤ) - 1) • exponentVector p α u
    calc
      exponentVector p α (u ^ (-(n : ℤ) - 1)) =
          exponentVector p α (u ^ (-(n : ℤ)) * u⁻¹) := by rw [zpow_sub_one]
      _ = exponentVector p α (u ^ (-(n : ℤ))) + exponentVector p α u⁻¹ := by simp
      _ = (-(n : ℤ)) • exponentVector p α u - exponentVector p α u := by
        rw [ih]
        simp [sub_eq_add_neg]
      _ = (-(n : ℤ) - 1) • exponentVector p α u := by
        rw [sub_zsmul, one_zsmul]
        simp [sub_eq_add_neg]

/-- Exponent vectors turn a finite product into the corresponding finite sum. -/
@[simp] theorem vector_list_prod (ws : List (FreeGroup α)) :
    exponentVector p α ws.prod = (ws.map (exponentVector p α)).sum := by
  induction ws with
  | nil => simp
  | cons w ws ih => simp [ih]

/-- Coordinate form of the exponent-vector formula for a list product. -/
@[simp] theorem exponent_vector_list (ws : List (FreeGroup α)) (x : α) :
    exponentVector p α ws.prod x = (ws.map (fun w => exponentVector p α w x)).sum := by
  induction ws with
  | nil => simp
  | cons w ws ih =>
      calc
        exponentVector p α (List.prod (w :: ws)) x =
            (exponentVector p α w + exponentVector p α ws.prod) x := by simp
        _ = exponentVector p α w x + exponentVector p α ws.prod x := rfl
        _ = exponentVector p α w x + (ws.map (fun w => exponentVector p α w x)).sum := by
            rw [ih]
        _ = (List.map (fun w => exponentVector p α w x) (w :: ws)).sum := by simp

/-- A product of exponent-zero words has exponent vector zero. -/
theorem exponent_vector_zero (ws : List (FreeGroup α))
    (h : ∀ w ∈ ws, exponentVector p α w = 0) :
    exponentVector p α ws.prod = 0 := by
  induction ws with
  | nil => simp
  | cons w ws ih =>
      have hw : exponentVector p α w = 0 := h w (by simp)
      have hws : ∀ u ∈ ws, exponentVector p α u = 0 := by
        intro u hu
        exact h u (by simp [hu])
      simp [hw, ih hws]

/-- Conjugation does not change an exponent vector. -/
@[simp] theorem exponentVector_conj (g w : FreeGroup α) :
    exponentVector p α (g * w * g⁻¹) = exponentVector p α w := by
  simp [add_left_comm, add_comm]

/-- A quotient-form variant of conjugation invariance. -/
@[simp] theorem vector_conj_div (g w : FreeGroup α) :
    exponentVector p α (g * w / g) = exponentVector p α w := by
  simp [div_eq_mul_inv, add_left_comm, add_comm]

/-- The inverse-conjugation convention also leaves exponent vectors unchanged. -/
@[simp] theorem exponent_inv (g w : FreeGroup α) :
    exponentVector p α (g⁻¹ * w * g) = exponentVector p α w := by
  simp

/-- Quotient-form inverse-conjugation invariance. -/
@[simp] theorem vector_inv_div (g w : FreeGroup α) :
    exponentVector p α (g⁻¹ * w / g⁻¹) = exponentVector p α w := by
  simp [div_eq_mul_inv]

/-- Kernel membership for the multiplicative exponent-vector hom is exactly vanishing
of the additive exponent vector. -/
theorem exponent_vector_hom (w : FreeGroup α) :
    exponentVectorHom p α w = 1 ↔ exponentVector p α w = 0 := by
  change exponentVectorHom p α w = 1 ↔
    Multiplicative.toAdd (exponentVectorHom p α w) = 0
  simp

@[simp] theorem vector_hom_ker (w : FreeGroup α) :
    w ∈ MonoidHom.ker (exponentVectorHom p α) ↔ exponentVector p α w = 0 := by
  simp [MonoidHom.mem_ker, exponent_vector_hom]

variable {β : Type*}

/-- Relabel basis vectors in an exponent module along a function of generators. -/
def exponentModuleMap (f : α → β) :
    eModule p α →ₗ[ZMod p] eModule p β :=
  Finsupp.lmapDomain (ZMod p) (ZMod p) f

@[simp] theorem exponent_module_single (f : α → β) (x : α) (a : ZMod p) :
    exponentModuleMap p α f (Finsupp.single x a) = Finsupp.single (f x) a := by
  simp [exponentModuleMap, Finsupp.lmapDomain]

/-- Exponent vectors are natural for relabeling free-group generators. -/
@[simp] theorem exponentVector_map (f : α → β) (w : FreeGroup α) :
    exponentModuleMap p α f (exponentVector p α w) =
      exponentVector p β (FreeGroup.map f w) := by
  induction w using FreeGroup.induction_on with
  | C1 => simp [exponentModuleMap]
  | of x => simp [exponent_module_single, FreeGroup.map.of]
  | inv_of x hx => simp [exponent_module_single, FreeGroup.map.of]
  | mul u v hu hv => simp [map_mul, hu, hv]

@[simp] theorem exponent_module_id :
    exponentModuleMap p α (fun x : α => x) = LinearMap.id := by
  ext v x
  simp [exponentModuleMap, Finsupp.lmapDomain]

@[simp] theorem exponent_module_comp {γ : Type*} (f : α → β) (g : β → γ) :
    (exponentModuleMap p β g).comp (exponentModuleMap p α f) =
      exponentModuleMap p α (g ∘ f) := by
  ext v x
  simp [exponentModuleMap, Finsupp.lmapDomain]

theorem exponent_module_domain (f : α → β)
    (v : eModule p α) :
    exponentModuleMap p α f v = Finsupp.mapDomain f v := rfl

/-- Coordinate formula for relabeling along an equivalence of generators. -/
@[simp] theorem exponent_module (e : α ≃ β)
    (v : eModule p α) (y : β) :
    exponentModuleMap p α e v y = v (e.symm y) := by
  classical
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add v w hv hw => simp [map_add, hv, hw]
  | single x a =>
      by_cases h : e x = y
      · subst y
        simp [exponent_module_single]
      · have hne : x ≠ e.symm y := by
          intro hx
          apply h
          rw [hx]
          simp
        simp [exponent_module_single, h, hne]

/-- Coordinate form of exponent-vector naturality for generator equivalences. -/
@[simp] theorem exponent_vector_equiv (e : α ≃ β)
    (w : FreeGroup α) (y : β) :
    exponentVector p β (FreeGroup.map e w) y =
      exponentVector p α w (e.symm y) := by
  have h := exponentVector_map (p := p) (α := α) e w
  rw [← h]
  exact exponent_module p α e (exponentVector p α w) y

/-- Injective relabelings induce injective maps on exponent modules. -/
theorem exponent_module_injective (f : α → β)
    (hf : Function.Injective f) : Function.Injective (exponentModuleMap p α f) := by
  intro v w h
  apply Finsupp.mapDomain_injective hf
  simpa using h

/-- Surjective relabelings induce surjective maps on exponent modules. -/
theorem module_surjective (f : α → β)
    (hf : Function.Surjective f) : Function.Surjective (exponentModuleMap p α f) := by
  intro w
  rcases Finsupp.mapDomain_surjective (M := ZMod p) hf w with ⟨v, hv⟩
  refine ⟨v, ?_⟩
  simpa using hv

/-- Kernel form for an injective relabeling of exponent modules. -/
theorem exponent_bot_injective (f : α → β)
    (hf : Function.Injective f) :
    LinearMap.ker (exponentModuleMap p α f) = ⊥ := by
  exact LinearMap.ker_eq_bot_of_injective
    (exponent_module_injective p α f hf)

/-- Range form for a surjective relabeling of exponent modules. -/
theorem exponent_module_surjective (f : α → β)
    (hf : Function.Surjective f) :
    LinearMap.range (exponentModuleMap p α f) = ⊤ := by
  exact LinearMap.range_eq_top_of_surjective _
    (module_surjective p α f hf)

/-- Relabeling by an equivalence of generators gives a linear equivalence of exponent modules. -/
def exponentModuleEquiv (e : α ≃ β) :
    eModule p α ≃ₗ[ZMod p] eModule p β where
  toFun := exponentModuleMap p α e
  invFun := exponentModuleMap p β e.symm
  left_inv := by
    intro v
    change ((exponentModuleMap p β e.symm).comp (exponentModuleMap p α e)) v = v
    rw [exponent_module_comp]
    have h : (e.symm ∘ e : α → α) = fun x => x := by
      funext x
      simp
    rw [h, exponent_module_id]
    rfl
  right_inv := by
    intro v
    change ((exponentModuleMap p α e).comp (exponentModuleMap p β e.symm)) v = v
    rw [exponent_module_comp]
    have h : (e ∘ e.symm : β → β) = fun x => x := by
      funext x
      simp
    rw [h, exponent_module_id]
    rfl
  map_add' := by intro x y; exact (exponentModuleMap p α e).map_add x y
  map_smul' := by intro a x; exact (exponentModuleMap p α e).map_smul a x

@[simp] theorem module_equiv (e : α ≃ β) (v : eModule p α) :
    exponentModuleEquiv p α e v = exponentModuleMap p α e v := rfl

@[simp] theorem module_equiv_linear (e : α ≃ β) :
    (exponentModuleEquiv p α e).toLinearMap = exponentModuleMap p α e := rfl

@[simp] theorem exponent_module_linear (e : α ≃ β) :
    (exponentModuleEquiv p α e).symm.toLinearMap = exponentModuleMap p β e.symm := rfl

@[simp] theorem exponent_module_equiv (e : α ≃ β) (v : eModule p β) :
    (exponentModuleEquiv p α e).symm v = exponentModuleMap p β e.symm v := rfl

/-- Coordinate formula for an exponent-module equivalence. -/
@[simp] theorem module_equiv_coord (e : α ≃ β)
    (v : eModule p α) (y : β) :
    exponentModuleEquiv p α e v y = v (e.symm y) := by
  simp [module_equiv]

/-- Coordinate formula for the inverse exponent-module equivalence. -/
@[simp] theorem exponent_module_coord (e : α ≃ β)
    (v : eModule p β) (x : α) :
    (exponentModuleEquiv p α e).symm v x = v (e x) := by
  simp [exponent_module_equiv]

@[simp] theorem exponent_module_vector (e : α ≃ β) (w : FreeGroup α) :
    exponentModuleEquiv p α e (exponentVector p α w) =
      exponentVector p β (FreeGroup.map e w) := by
  simp

@[simp] theorem module_equiv_symm (e : α ≃ β)
    (v : eModule p α) :
    (exponentModuleEquiv p α e).symm (exponentModuleMap p α e v) = v := by
  exact (exponentModuleEquiv p α e).left_inv v

@[simp] theorem exponent_equiv_symm (e : α ≃ β)
    (v : eModule p β) :
    exponentModuleMap p α e ((exponentModuleEquiv p α e).symm v) = v := by
  change exponentModuleEquiv p α e ((exponentModuleEquiv p α e).symm v) = v
  exact (exponentModuleEquiv p α e).right_inv v

/-- The inverse relabeling equivalence is relabeling by the inverse equivalence. -/
@[simp] theorem exponent_symm (e : α ≃ β) :
    (exponentModuleEquiv p α e).symm = exponentModuleEquiv p β e.symm := by
  ext v x
  rfl

/-- The identity generator equivalence induces the identity exponent-module equivalence. -/
@[simp] theorem exponent_module_refl :
    exponentModuleEquiv p α (Equiv.refl α) =
      LinearEquiv.refl (ZMod p) (eModule p α) := by
  ext v x
  simp [exponentModuleEquiv, exponentModuleMap, Finsupp.lmapDomain]

/-- Exponent-module relabeling equivalences compose functorially. -/
@[simp] theorem exponent_module_trans {γ : Type*} (e : α ≃ β) (f : β ≃ γ) :
    (exponentModuleEquiv p α e).trans (exponentModuleEquiv p β f) =
      exponentModuleEquiv p α (e.trans f) := by
  ext v x
  have h := congrArg
    (fun (L : eModule p α →ₗ[ZMod p] eModule p γ) => L v)
    (exponent_module_comp (p := p) (α := α) e f)
  exact congrArg (fun w : eModule p γ => w x) h

/-- Characterize equality to an equivalence-induced relabeling map via its inverse. -/
theorem exponent_module_symm (e : α ≃ β)
    (v : eModule p α) (w : eModule p β) :
    exponentModuleMap p α e v = w ↔ v = (exponentModuleEquiv p α e).symm w := by
  constructor
  · intro h
    rw [← h]
    exact (module_equiv_symm p α e v).symm
  · intro h
    rw [h]
    exact exponent_equiv_symm p α e w

/-- The relabeling map induced by an equivalence has trivial kernel. -/
theorem exponent_module_bot (e : α ≃ β) :
    LinearMap.ker (exponentModuleMap p α e) = ⊥ := by
  rw [← module_equiv_linear (p := p) (α := α) e]
  exact LinearMap.ker_eq_bot_of_injective (exponentModuleEquiv p α e).injective

/-- The relabeling map induced by an equivalence has full range. -/
theorem exponent_module_top (e : α ≃ β) :
    LinearMap.range (exponentModuleMap p α e) = ⊤ := by
  rw [← module_equiv_linear (p := p) (α := α) e]
  exact LinearMap.range_eq_top_of_surjective _ (exponentModuleEquiv p α e).surjective

end
end Submission

namespace Submission

open scoped commutatorElement

noncomputable section

variable (p : ℕ) (α : Type*)

@[simp] theorem vector_pth_power (w : FreeGroup α) :
    exponentVector p α (w ^ p) = 0 := by
  rw [exponentVector_pow]
  -- `p`-fold addition is zero in a `ZMod p`-module.
  rw [← Nat.cast_smul_eq_nsmul (R := ZMod p)]
  simp

@[simp] theorem exponentVector_commutator (u v : FreeGroup α) :
    exponentVector p α ⁅u, v⁆ = 0 := by
  simp [commutatorElement_def, add_comm, add_left_comm]


/-- Products of exponent-zero words have exponent zero. -/
theorem vector_zero_mul {u v : FreeGroup α}
    (hu : exponentVector p α u = 0) (hv : exponentVector p α v = 0) :
    exponentVector p α (u * v) = 0 := by
  simp [hu, hv]

/-- Inverses of exponent-zero words have exponent zero. -/
theorem vector_zero_inv {u : FreeGroup α}
    (hu : exponentVector p α u = 0) : exponentVector p α u⁻¹ = 0 := by
  simp [hu]

/-- Conjugates of exponent-zero words have exponent zero. -/
theorem vector_zero_conj {g u : FreeGroup α}
    (hu : exponentVector p α u = 0) :
    exponentVector p α (g * u * g⁻¹) = 0 := by
  simp [hu]

/-- Inverse-conjugates of exponent-zero words have exponent zero. -/
theorem exponent_conj_inv {g u : FreeGroup α}
    (hu : exponentVector p α u = 0) :
    exponentVector p α (g⁻¹ * u * g) = 0 := by
  simpa using (vector_zero_conj (p := p) (α := α) (g := g⁻¹) hu)

/-- Divisions of exponent-zero words have exponent zero. -/
theorem vector_zero_div {u v : FreeGroup α}
    (hu : exponentVector p α u = 0) (hv : exponentVector p α v = 0) :
    exponentVector p α (u / v) = 0 := by
  simp [div_eq_mul_inv, hu, hv]

/-- Natural powers of an exponent-zero word have exponent zero. -/
theorem vector_zero_pow {u : FreeGroup α}
    (hu : exponentVector p α u = 0) (n : ℕ) :
    exponentVector p α (u ^ n) = 0 := by
  rw [exponentVector_pow]
  simp [hu]

/-- Integer powers of an exponent-zero word have exponent zero. -/
theorem vector_zero_zpow {u : FreeGroup α}
    (hu : exponentVector p α u = 0) (n : ℤ) :
    exponentVector p α (u ^ n) = 0 := by
  rw [exponentVector_zpow]
  simp [hu]

/-- The exponent-vector hom sends every `p`th power to the identity. -/
@[simp] theorem exponent_vector_pth (w : FreeGroup α) :
    exponentVectorHom p α (w ^ p) = 1 := by
  apply Multiplicative.toAdd.injective
  change exponentVector p α (w ^ p) = 0
  exact vector_pth_power p α w

/-- The exponent-vector hom sends every commutator to the identity. -/
@[simp] theorem exponent_vector_commutator (u v : FreeGroup α) :
    exponentVectorHom p α ⁅u, v⁆ = 1 := by
  apply Multiplicative.toAdd.injective
  change exponentVector p α ⁅u, v⁆ = 0
  exact exponentVector_commutator p α u v

/-- The exponent-vector kernel is closed under products (named wrapper). -/
theorem exponent_vector_mul {u v : FreeGroup α}
    (hu : u ∈ MonoidHom.ker (exponentVectorHom p α))
    (hv : v ∈ MonoidHom.ker (exponentVectorHom p α)) :
    u * v ∈ MonoidHom.ker (exponentVectorHom p α) :=
  (MonoidHom.ker (exponentVectorHom p α)).mul_mem hu hv

/-- The exponent-vector kernel is closed under inverses (named wrapper). -/
theorem vector_ker_inv {u : FreeGroup α}
    (hu : u ∈ MonoidHom.ker (exponentVectorHom p α)) :
    u⁻¹ ∈ MonoidHom.ker (exponentVectorHom p α) :=
  (MonoidHom.ker (exponentVectorHom p α)).inv_mem hu

/-- The exponent-vector kernel is closed under division (named wrapper). -/
theorem vector_ker_div {u v : FreeGroup α}
    (hu : u ∈ MonoidHom.ker (exponentVectorHom p α))
    (hv : v ∈ MonoidHom.ker (exponentVectorHom p α)) :
    u / v ∈ MonoidHom.ker (exponentVectorHom p α) := by
  exact (MonoidHom.ker (exponentVectorHom p α)).div_mem hu hv

/-- The exponent-vector kernel is closed under natural powers (named wrapper). -/
theorem exponent_vector_pow {u : FreeGroup α}
    (hu : u ∈ MonoidHom.ker (exponentVectorHom p α)) (n : ℕ) :
    u ^ n ∈ MonoidHom.ker (exponentVectorHom p α) :=
  (MonoidHom.ker (exponentVectorHom p α)).pow_mem hu n

/-- The exponent-vector kernel is closed under integer powers (named wrapper). -/
theorem exponent_vector_zpow {u : FreeGroup α}
    (hu : u ∈ MonoidHom.ker (exponentVectorHom p α)) (n : ℤ) :
    u ^ n ∈ MonoidHom.ker (exponentVectorHom p α) :=
  (MonoidHom.ker (exponentVectorHom p α)).zpow_mem hu n

/-- A list product of kernel elements remains in the exponent-vector kernel. -/
theorem exponent_vector_prod (ws : List (FreeGroup α))
    (h : ∀ w ∈ ws, w ∈ MonoidHom.ker (exponentVectorHom p α)) :
    ws.prod ∈ MonoidHom.ker (exponentVectorHom p α) := by
  rw [vector_hom_ker]
  apply exponent_vector_zero
  intro w hw
  exact (vector_hom_ker (p := p) (α := α) w).1 (h w hw)

/-- Conjugating a kernel element stays in the exponent-vector kernel. -/
theorem vector_ker_conj {g u : FreeGroup α}
    (hu : u ∈ MonoidHom.ker (exponentVectorHom p α)) :
    g * u * g⁻¹ ∈ MonoidHom.ker (exponentVectorHom p α) := by
  change exponentVectorHom p α (g * u * g⁻¹) = 1
  have huv : exponentVector p α u = 0 := by
    change exponentVectorHom p α u = 1 at hu
    -- convert multiplicative kernel equality back to additive exponent-vector equality
    simpa [exponentVectorHom] using congrArg Multiplicative.toAdd hu
  apply Multiplicative.toAdd.injective
  change exponentVector p α (g * u * g⁻¹) = 0
  exact vector_zero_conj p α huv

/-- The inverse-conjugation convention preserves membership in the exponent-vector kernel. -/
theorem vector_conj_inv {g u : FreeGroup α}
    (hu : u ∈ MonoidHom.ker (exponentVectorHom p α)) :
    g⁻¹ * u * g ∈ MonoidHom.ker (exponentVectorHom p α) := by
  simpa using (vector_ker_conj (p := p) (α := α) (g := g⁻¹) hu)

/-- Conjugation does not change membership in the exponent-vector kernel. -/
@[simp] theorem exponent_vector_conj (g u : FreeGroup α) :
    g * u * g⁻¹ ∈ MonoidHom.ker (exponentVectorHom p α) ↔
      u ∈ MonoidHom.ker (exponentVectorHom p α) := by
  simp

/-- Inverse-conjugation does not change membership in the exponent-vector kernel. -/
@[simp] theorem exponent_vector_inv (g u : FreeGroup α) :
    g⁻¹ * u * g ∈ MonoidHom.ker (exponentVectorHom p α) ↔
      u ∈ MonoidHom.ker (exponentVectorHom p α) := by
  simp

/-- Quotient-form conjugation does not change membership in the exponent-vector kernel. -/
@[simp] theorem exponent_vector_div (g u : FreeGroup α) :
    g * u / g ∈ MonoidHom.ker (exponentVectorHom p α) ↔
      u ∈ MonoidHom.ker (exponentVectorHom p α) := by
  simp [div_eq_mul_inv]

/-- Kernel-membership form for `p`th powers. -/
@[simp] theorem pth_vector_ker (w : FreeGroup α) :
    w ^ p ∈ MonoidHom.ker (exponentVectorHom p α) := by
  change exponentVectorHom p α (w ^ p) = 1
  exact exponent_vector_pth p α w

/-- Kernel-membership form for commutators. -/
@[simp] theorem commutator_vector_ker (u v : FreeGroup α) :
    ⁅u, v⁆ ∈ MonoidHom.ker (exponentVectorHom p α) := by
  change exponentVectorHom p α ⁅u, v⁆ = 1
  exact exponent_vector_commutator p α u v

end
end Submission
