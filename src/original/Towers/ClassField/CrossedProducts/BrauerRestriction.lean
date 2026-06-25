import Towers.ClassField.BrauerGroups.BaseChangeTower
import Towers.ClassField.CrossedProducts.BrauerBimoduleCriterion
import Towers.ClassField.CrossedProducts.GaloisRestriction
import Towers.ClassField.CrossedProducts.Cohomology


/-!
# Brauer-theoretic restriction in finite Galois cohomology

Scalar extension through `K → L` sends classes split by `E` over `K` to
classes split by `E` over `L`.  Transporting this map through the crossed
product classification gives the Brauer-theoretic restriction map in `H²`.
An explicit Mackey--Morita bimodule proves that this map agrees with cochain
restriction, giving the restriction square used in the local invariant
theorem.
-/

namespace Towers.CField.CProduca

noncomputable section

universe u

open scoped TensorProduct

open BGroups

attribute [local instance] Units.mulDistribMulActionRight
attribute [local instance low] Algebra.TensorProduct.rightAlgebra

variable (K L E : Type u) [Field K] [Field L] [Field E]
  [Algebra K L] [Algebra K E] [Algebra L E] [IsScalarTower K L E]

/-- Scalar extension on relative Brauer groups in a field tower. -/
def relativeBrauerChange :
    relativeBrauerGroup K E →* relativeBrauerGroup L E where
  toFun x := ⟨brauerBaseChange K L x.1, by
    rw [relative_brauer_group, base_change_tower]
    exact (relative_brauer_group K E x.1).1 x.2⟩
  map_one' := by
    apply Subtype.ext
    exact map_one (brauerBaseChange K L)
  map_mul' x y := by
    apply Subtype.ext
    exact map_mul (brauerBaseChange K L) x.1 y.1

@[simp]
theorem relative_change_coe (x : relativeBrauerGroup K E) :
    ((relativeBrauerChange K L E x : relativeBrauerGroup L E) :
        BrauerGroup L) = brauerBaseChange K L (x : BrauerGroup K) :=
  rfl

/-- Relative Brauer-group base change is transitive through an intermediate
field. -/
theorem relative_change_trans
    (M : Type u) [Field M]
    [Algebra K M] [Algebra L M] [Algebra M E]
    [IsScalarTower K L M] [IsScalarTower K M E]
    [IsScalarTower L M E]
    (x : relativeBrauerGroup K E) :
    relativeBrauerChange L M E (relativeBrauerChange K L E x) =
      relativeBrauerChange K M E x := by
  apply Subtype.ext
  exact base_change_tower K L M x.1

variable [FiniteDimensional K E] [IsGalois K E]
  [FiniteDimensional L E] [IsGalois L E]

private abbrev restrictedCocycle
    (c : NMCocycl₂ (G := Gal(E/K)) (M := Eˣ)) :
    NMCocycl₂ (G := Gal(E/L)) (M := Eˣ) :=
  NMCocycl₂.restrict (galoisTowerInclusion K L E)
    (by intro sigma x; rfl) c

private noncomputable def restrictedCrossedFn
    (c : NMCocycl₂ (G := Gal(E/K)) (M := Eˣ))
    (x : CProduc (restrictedCocycle K L E c)) : CProduc c :=
  CProduc.sum (restrictedCocycle K L E c) x fun sigma a =>
    CProduc.single c (galoisTowerInclusion K L E sigma) a

omit [FiniteDimensional K E] [IsGalois K E] [FiniteDimensional L E] [IsGalois L E] in
@[simp]
private theorem restricted_fn_single
    (c : NMCocycl₂ (G := Gal(E/K)) (M := Eˣ))
    (sigma : Gal(E/L)) (a : E) :
    restrictedCrossedFn K L E c
        (CProduc.single (restrictedCocycle K L E c) sigma a) =
      CProduc.single c (galoisTowerInclusion K L E sigma) a := by
  rw [restrictedCrossedFn, CProduc.sum_single_index]
  simp

omit [FiniteDimensional K E] [IsGalois K E] [FiniteDimensional L E] [IsGalois L E] in
@[simp]
private theorem restricted_embedding_fn
    (c : NMCocycl₂ (G := Gal(E/K)) (M := Eˣ)) :
    restrictedCrossedFn K L E c 0 = 0 := by
  exact CProduc.sum_zero_index (restrictedCocycle K L E c)

omit [FiniteDimensional K E] [IsGalois K E] [FiniteDimensional L E] [IsGalois L E] in
private theorem crossed_embedding_fn
    (c : NMCocycl₂ (G := Gal(E/K)) (M := Eˣ))
    (x y : CProduc (restrictedCocycle K L E c)) :
    restrictedCrossedFn K L E c (x + y) =
      restrictedCrossedFn K L E c x +
        restrictedCrossedFn K L E c y := by
  apply CProduc.sum_add_index'
  · intro sigma
    simp
  · intro sigma a b
    simp

omit [FiniteDimensional K E] [IsGalois K E] [FiniteDimensional L E] [IsGalois L E] in
@[simp]
private theorem restricted_crossed_embedding
    (c : NMCocycl₂ (G := Gal(E/K)) (M := Eˣ)) :
    restrictedCrossedFn K L E c 1 = 1 := by
  rw [CProduc.one_def,
    restricted_fn_single, CProduc.one_def]
  rfl

omit [FiniteDimensional K E] [IsGalois K E] [FiniteDimensional L E] [IsGalois L E] in
private theorem restricted_crossed_fn
    (c : NMCocycl₂ (G := Gal(E/K)) (M := Eˣ))
    (sigma tau : Gal(E/L)) (a b : E) :
    restrictedCrossedFn K L E c
        (CProduc.single (restrictedCocycle K L E c) sigma a *
          CProduc.single (restrictedCocycle K L E c) tau b) =
      restrictedCrossedFn K L E c
          (CProduc.single (restrictedCocycle K L E c) sigma a) *
        restrictedCrossedFn K L E c
          (CProduc.single (restrictedCocycle K L E c) tau b) := by
  rw [CProduc.single_mul_single,
    restricted_fn_single,
    restricted_fn_single,
    restricted_fn_single,
    CProduc.single_mul_single]
  rfl

omit [FiniteDimensional K E] [IsGalois K E]
  [FiniteDimensional L E] [IsGalois L E] in
private theorem restricted_fn_mul
    (c : NMCocycl₂ (G := Gal(E/K)) (M := Eˣ))
    (x y : CProduc (restrictedCocycle K L E c)) :
    restrictedCrossedFn K L E c (x * y) =
      restrictedCrossedFn K L E c x *
        restrictedCrossedFn K L E c y := by
  induction x using CProduc.induction_on (restrictedCocycle K L E c) with
  | zero => simp
  | hadd x₁ x₂ hx₁ hx₂ =>
      rw [add_mul, crossed_embedding_fn,
        crossed_embedding_fn, add_mul, hx₁, hx₂]
  | hsingle sigma a =>
      induction y using CProduc.induction_on (restrictedCocycle K L E c) with
      | zero => simp
      | hadd y₁ y₂ hy₁ hy₂ =>
          rw [mul_add, crossed_embedding_fn,
            crossed_embedding_fn, mul_add, hy₁, hy₂]
      | hsingle tau b =>
          exact restricted_crossed_fn
            K L E c sigma tau a b

/-- The crossed product of the restricted cocycle embeds into the original
crossed product by retaining precisely the basis vectors indexed by
`Gal(E/L)`. -/
private noncomputable def restrictedCrossedEmbedding
    (c : NMCocycl₂ (G := Gal(E/K)) (M := Eˣ)) :
    CProduc (restrictedCocycle K L E c) →+* CProduc c where
  toFun := restrictedCrossedFn K L E c
  map_zero' := restricted_embedding_fn K L E c
  map_one' := restricted_crossed_embedding K L E c
  map_add' := crossed_embedding_fn K L E c
  map_mul' := restricted_fn_mul K L E c

omit [FiniteDimensional K E] [IsGalois K E]
  [FiniteDimensional L E] [IsGalois L E] in
@[simp]
private theorem restricted_crossed_single
    (c : NMCocycl₂ (G := Gal(E/K)) (M := Eˣ))
    (sigma : Gal(E/L)) (a : E) :
    restrictedCrossedEmbedding K L E c
        (CProduc.single (restrictedCocycle K L E c) sigma a) =
      CProduc.single c (galoisTowerInclusion K L E sigma) a := by
  exact restricted_fn_single K L E c sigma a

private noncomputable def intermediateCoefficientEmbedding
    (c : NMCocycl₂ (G := Gal(E/K)) (M := Eˣ)) :
    L →+* CProduc c :=
  (CProduc.fieldEmbedding K E c).toRingHom.comp (algebraMap L E)

omit [FiniteDimensional K E] [IsGalois K E]
  [FiniteDimensional L E] [IsGalois L E] in
@[simp]
private theorem restricted_crossed_algebra
    (c : NMCocycl₂ (G := Gal(E/K)) (M := Eˣ)) (l : L) :
    restrictedCrossedEmbedding K L E c
        (algebraMap L (CProduc (restrictedCocycle K L E c)) l) =
      intermediateCoefficientEmbedding K L E c l := by
  rw [CProduc.algebraMap_apply,
    restricted_crossed_single]
  rfl

omit [FiniteDimensional K E] [IsGalois K E]
  [FiniteDimensional L E] [IsGalois L E] in
private theorem intermediate_commutes_restricted
    (c : NMCocycl₂ (G := Gal(E/K)) (M := Eˣ))
    (l : L) (b : CProduc (restrictedCocycle K L E c)) :
    intermediateCoefficientEmbedding K L E c l *
        restrictedCrossedEmbedding K L E c b =
      restrictedCrossedEmbedding K L E c b *
        intermediateCoefficientEmbedding K L E c l := by
  induction b using CProduc.induction_on (restrictedCocycle K L E c) with
  | zero => simp
  | hadd x y hx hy =>
      rw [map_add, mul_add, add_mul, hx, hy]
  | hsingle sigma a =>
      rw [restricted_crossed_single]
      change CProduc.single c 1 (algebraMap L E l) *
          CProduc.single c (galoisTowerInclusion K L E sigma) a =
        CProduc.single c (galoisTowerInclusion K L E sigma) a *
          CProduc.single c 1 (algebraMap L E l)
      rw [CProduc.single_mul_single, CProduc.single_mul_single]
      apply congrArg (CProduc.single c
        (galoisTowerInclusion K L E sigma))
      simp only [one_smul, NMCocycl₂.apply_one_fst,
        Units.val_one, mul_one, NMCocycl₂.apply_one_snd]
      change (algebraMap L E) l * a =
        a * (galoisTowerInclusion K L E sigma) ((algebraMap L E) l)
      rw [galois_tower_inclusion, sigma.commutes]
      exact mul_comm _ _

private noncomputable def restrictionScalarHom
    (c : NMCocycl₂ (G := Gal(E/K)) (M := Eˣ)) :
    L →+* (CProduc c)ᵐᵒᵖ where
  toFun l := MulOpposite.op (intermediateCoefficientEmbedding K L E c l)
  map_zero' := by simp [intermediateCoefficientEmbedding]
  map_one' := by simp [intermediateCoefficientEmbedding]
  map_add' l m := by simp [intermediateCoefficientEmbedding]
  map_mul' l m := by
    apply MulOpposite.unop_injective
    change intermediateCoefficientEmbedding K L E c (l * m) =
      intermediateCoefficientEmbedding K L E c m *
        intermediateCoefficientEmbedding K L E c l
    rw [← map_mul, mul_comm]

@[reducible] private noncomputable def restrictionRightModule
    (c : NMCocycl₂ (G := Gal(E/K)) (M := Eˣ)) :
    Module L (CProduc c) :=
  Module.compHom (CProduc c) (restrictionScalarHom K L E c)

private noncomputable instance (priority := low) restrictionSMul
    (c : NMCocycl₂ (G := Gal(E/K)) (M := Eˣ)) :
    SMul L (CProduc c) :=
  (restrictionRightModule K L E c).toSMul

private noncomputable instance (priority := low) restrictionModule
    (c : NMCocycl₂ (G := Gal(E/K)) (M := Eˣ)) :
    Module L (CProduc c) :=
  restrictionRightModule K L E c

omit [Algebra K L] [IsScalarTower K L E] [FiniteDimensional K E] [IsGalois K E]
  [FiniteDimensional L E] [IsGalois L E] in
@[simp]
private theorem restriction_smul_apply
    (c : NMCocycl₂ (G := Gal(E/K)) (M := Eˣ))
    (l : L) (x : CProduc c) :
    l • x = x * intermediateCoefficientEmbedding K L E c l := by
  rfl

private noncomputable instance (priority := low) restrictionIsScalarTower
    (c : NMCocycl₂ (G := Gal(E/K)) (M := Eˣ)) :
    IsScalarTower K L (CProduc c) := by
  constructor
  intro r l x
  have hbase : intermediateCoefficientEmbedding K L E c (algebraMap K L r) =
      algebraMap K (CProduc c) r := by
    change CProduc.single c 1
        (algebraMap L E (algebraMap K L r)) =
      CProduc.single c 1 (algebraMap K E r)
    rw [IsScalarTower.algebraMap_apply K L E]
  calc
    (r • l) • x =
        x * intermediateCoefficientEmbedding K L E c (r • l) :=
      restriction_smul_apply K L E c (r • l) x
    _ = x * intermediateCoefficientEmbedding K L E c
        (algebraMap K L r * l) := by rw [Algebra.smul_def]
    _ = x * (intermediateCoefficientEmbedding K L E c (algebraMap K L r) *
        intermediateCoefficientEmbedding K L E c l) := by rw [map_mul]
    _ = (x * algebraMap K (CProduc c) r) *
        intermediateCoefficientEmbedding K L E c l := by rw [hbase, mul_assoc]
    _ = (algebraMap K (CProduc c) r * x) *
        intermediateCoefficientEmbedding K L E c l := by rw [Algebra.commutes]
    _ = algebraMap K (CProduc c) r *
        (x * intermediateCoefficientEmbedding K L E c l) := mul_assoc _ _ _
    _ = r • (l • x) := by
      rw [Algebra.smul_def, restriction_smul_apply]

private noncomputable instance (priority := low) restrictionSMulCommClassLeft
    (c : NMCocycl₂ (G := Gal(E/K)) (M := Eˣ)) :
    SMulCommClass (CProduc c) L (CProduc c) := by
  constructor
  intro a l x
  rw [restriction_smul_apply, restriction_smul_apply]
  exact (mul_assoc _ _ _).symm

private noncomputable instance (priority := low) restrictionSMulCommClassScalars
    (c : NMCocycl₂ (G := Gal(E/K)) (M := Eˣ)) :
    SMulCommClass L L (CProduc c) := by
  constructor
  intro l m x
  change (x * intermediateCoefficientEmbedding K L E c m) *
      intermediateCoefficientEmbedding K L E c l =
    (x * intermediateCoefficientEmbedding K L E c l) *
      intermediateCoefficientEmbedding K L E c m
  rw [mul_assoc, mul_assoc]
  have hcomm : intermediateCoefficientEmbedding K L E c m *
      intermediateCoefficientEmbedding K L E c l =
    intermediateCoefficientEmbedding K L E c l *
      intermediateCoefficientEmbedding K L E c m := by
    rw [← map_mul, ← map_mul, mul_comm]
  exact congrArg (x * ·) hcomm

private noncomputable instance (priority := low) restrictionIsScalarTowerScalars
    (c : NMCocycl₂ (G := Gal(E/K)) (M := Eˣ)) :
    IsScalarTower L L (CProduc c) := by
  constructor
  intro l m x
  rw [restriction_smul_apply, restriction_smul_apply]
  change x * intermediateCoefficientEmbedding K L E c (l * m) =
    (x * intermediateCoefficientEmbedding K L E c m) *
      intermediateCoefficientEmbedding K L E c l
  rw [map_mul, mul_assoc]
  have hcomm : intermediateCoefficientEmbedding K L E c l *
      intermediateCoefficientEmbedding K L E c m =
    intermediateCoefficientEmbedding K L E c m *
      intermediateCoefficientEmbedding K L E c l := by
    rw [← map_mul, ← map_mul, mul_comm]
  exact congrArg (x * ·) hcomm

private noncomputable instance (priority := low) restrictionModuleFinite
    (c : NMCocycl₂ (G := Gal(E/K)) (M := Eˣ)) :
    Module.Finite L (CProduc c) :=
  Module.Finite.of_restrictScalars_finite K L (CProduc c)

private noncomputable def restrictionLeftMul
    (c : NMCocycl₂ (G := Gal(E/K)) (M := Eˣ))
    (a : CProduc c) : Module.End L (CProduc c) where
  toFun x := a * x
  map_add' x y := mul_add a x y
  map_smul' l x := by
    change a * (x * intermediateCoefficientEmbedding K L E c l) =
      (a * x) * intermediateCoefficientEmbedding K L E c l
    exact (mul_assoc a x (intermediateCoefficientEmbedding K L E c l)).symm

omit [FiniteDimensional K E] [IsGalois K E] [FiniteDimensional L E] [IsGalois L E] in
private theorem intermediate_embedding_algebra
    (c : NMCocycl₂ (G := Gal(E/K)) (M := Eˣ)) (r : K) :
    intermediateCoefficientEmbedding K L E c (algebraMap K L r) =
      algebraMap K (CProduc c) r := by
  change CProduc.single c 1
      (algebraMap L E (algebraMap K L r)) =
    CProduc.single c 1 (algebraMap K E r)
  rw [IsScalarTower.algebraMap_apply K L E]

private noncomputable def restrictionAlgHom
    (c : NMCocycl₂ (G := Gal(E/K)) (M := Eˣ)) :
    CProduc c →ₐ[K] Module.End L (CProduc c) where
  toFun := restrictionLeftMul K L E c
  map_zero' := by
    apply LinearMap.ext
    intro x
    exact zero_mul x
  map_one' := by
    apply LinearMap.ext
    intro x
    exact one_mul x
  map_add' a b := by
    apply LinearMap.ext
    intro x
    exact add_mul a b x
  map_mul' a b := by
    apply LinearMap.ext
    intro x
    exact mul_assoc a b x
  commutes' r := by
    apply LinearMap.ext
    intro x
    change algebraMap K (CProduc c) r * x =
      (algebraMap K (Module.End L (CProduc c)) r) x
    rw [Module.algebraMap_end_apply, Algebra.smul_def]

/-- The scalar extension of the original crossed product acts on it by left
multiplication and by the chosen right `L`-module structure. -/
private noncomputable def restrictionLeftAction
    (c : NMCocycl₂ (G := Gal(E/K)) (M := Eˣ)) :
    L ⊗[K] CProduc c →ₐ[L] Module.End L (CProduc c) :=
  (AlgHom.liftEquiv K L (CProduc c)
    (Module.End L (CProduc c))) (restrictionAlgHom K L E c)

omit [FiniteDimensional K E] [IsGalois K E] [FiniteDimensional L E] [IsGalois L E] in
@[simp]
private theorem restriction_action_tmul
    (c : NMCocycl₂ (G := Gal(E/K)) (M := Eˣ))
    (l : L) (a x : CProduc c) :
    restrictionLeftAction K L E c (l ⊗ₜ[K] a) x =
      (a * x) * intermediateCoefficientEmbedding K L E c l := by
  rw [restrictionLeftAction, AlgHom.liftEquiv_tmul]
  rfl

private noncomputable def restrictionRightAction
    (c : NMCocycl₂ (G := Gal(E/K)) (M := Eˣ))
    (b : CProduc (restrictedCocycle K L E c)) :
    Module.End L (CProduc c) where
  toFun x := x * restrictedCrossedEmbedding K L E c b
  map_add' x y := add_mul x y _
  map_smul' l x := by
    rw [restriction_smul_apply, restriction_smul_apply]
    calc
      (x * intermediateCoefficientEmbedding K L E c l) *
          restrictedCrossedEmbedding K L E c b =
        x * (intermediateCoefficientEmbedding K L E c l *
          restrictedCrossedEmbedding K L E c b) := mul_assoc _ _ _
      _ = x * (restrictedCrossedEmbedding K L E c b *
          intermediateCoefficientEmbedding K L E c l) := by
        rw [intermediate_commutes_restricted]
      _ = (x * restrictedCrossedEmbedding K L E c b) *
          intermediateCoefficientEmbedding K L E c l := (mul_assoc _ _ _).symm

private noncomputable def restrictionActionAlg
    (c : NMCocycl₂ (G := Gal(E/K)) (M := Eˣ)) :
    (CProduc (restrictedCocycle K L E c))ᵐᵒᵖ →ₐ[L]
      Module.End L (CProduc c) where
  toFun b := restrictionRightAction K L E c b.unop
  map_zero' := by
    apply LinearMap.ext
    intro x
    change x * restrictedCrossedEmbedding K L E c 0 = 0
    rw [map_zero, mul_zero]
  map_one' := by
    apply LinearMap.ext
    intro x
    change x * restrictedCrossedEmbedding K L E c 1 = x
    rw [map_one, mul_one]
  map_add' b d := by
    apply LinearMap.ext
    intro x
    change x * restrictedCrossedEmbedding K L E c (b.unop + d.unop) =
      x * restrictedCrossedEmbedding K L E c b.unop +
        x * restrictedCrossedEmbedding K L E c d.unop
    rw [map_add, mul_add]
  map_mul' b d := by
    apply LinearMap.ext
    intro x
    change x * restrictedCrossedEmbedding K L E c (d.unop * b.unop) =
      (x * restrictedCrossedEmbedding K L E c d.unop) *
        restrictedCrossedEmbedding K L E c b.unop
    rw [map_mul, mul_assoc]
  commutes' l := by
    apply LinearMap.ext
    intro x
    change x * restrictedCrossedEmbedding K L E c
        ((algebraMap L
          (CProduc (restrictedCocycle K L E c))ᵐᵒᵖ l).unop) = l • x
    rw [MulOpposite.algebraMap_apply, MulOpposite.unop_op,
      restricted_crossed_algebra,
      restriction_smul_apply]

omit [FiniteDimensional K E] [IsGalois K E]
  [FiniteDimensional L E] [IsGalois L E] in
private theorem restrictionActions_commute
    (c : NMCocycl₂ (G := Gal(E/K)) (M := Eˣ))
    (z : L ⊗[K] CProduc c)
    (b : (CProduc (restrictedCocycle K L E c))ᵐᵒᵖ) :
    restrictionLeftAction K L E c z *
        restrictionActionAlg K L E c b =
      restrictionActionAlg K L E c b *
        restrictionLeftAction K L E c z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add z w hz hw =>
      rw [map_add, add_mul, mul_add, hz, hw]
  | tmul l a =>
      apply LinearMap.ext
      intro x
      simp only [Module.End.mul_apply]
      change
        (a * (x * restrictedCrossedEmbedding K L E c b.unop)) *
            intermediateCoefficientEmbedding K L E c l =
          ((a * x) * intermediateCoefficientEmbedding K L E c l) *
            restrictedCrossedEmbedding K L E c b.unop
      calc
        (a * (x * restrictedCrossedEmbedding K L E c b.unop)) *
            intermediateCoefficientEmbedding K L E c l =
          (a * x) * (restrictedCrossedEmbedding K L E c b.unop *
            intermediateCoefficientEmbedding K L E c l) := by
              simp only [mul_assoc]
        _ = (a * x) * (intermediateCoefficientEmbedding K L E c l *
            restrictedCrossedEmbedding K L E c b.unop) := by
          rw [intermediate_commutes_restricted]
        _ = ((a * x) * intermediateCoefficientEmbedding K L E c l) *
            restrictedCrossedEmbedding K L E c b.unop :=
          (mul_assoc _ _ _).symm

private noncomputable def restrictionCombinedAction
    (c : NMCocycl₂ (G := Gal(E/K)) (M := Eˣ)) :
    (L ⊗[K] CProduc c) ⊗[L]
        (CProduc (restrictedCocycle K L E c))ᵐᵒᵖ →ₐ[L]
      Module.End L (CProduc c) :=
  Algebra.TensorProduct.lift (restrictionLeftAction K L E c)
    (restrictionActionAlg K L E c)
    (restrictionActions_commute K L E c)

omit [IsGalois L E] in
private theorem original_crossed_intermediate
    (c : NMCocycl₂ (G := Gal(E/K)) (M := Eˣ)) :
    Module.finrank L (CProduc c) =
      Module.finrank K L * (Module.finrank L E) ^ 2 := by
  letI : FiniteDimensional K L :=
    FiniteDimensional.of_injective
      ((Algebra.linearMap L E).restrictScalars K) (algebraMap L E).injective
  apply Nat.eq_of_mul_eq_mul_left (Module.finrank_pos (R := K) (M := L))
  calc
    Module.finrank K L * Module.finrank L (CProduc c) =
        Module.finrank K (CProduc c) :=
      Module.finrank_mul_finrank K L (CProduc c)
    _ = (Module.finrank K E) ^ 2 := CProduc.finrank_over_base K E c
    _ = (Module.finrank K L * Module.finrank L E) ^ 2 := by
      rw [Module.finrank_mul_finrank K L E]
    _ = Module.finrank K L *
        (Module.finrank K L * (Module.finrank L E) ^ 2) := by ring

private theorem restriction_combined_end
    (c : NMCocycl₂ (G := Gal(E/K)) (M := Eˣ)) :
    Module.finrank L
        ((L ⊗[K] CProduc c) ⊗[L]
          (CProduc (restrictedCocycle K L E c))ᵐᵒᵖ) =
      Module.finrank L (Module.End L (CProduc c)) := by
  letI : FiniteDimensional K L :=
    FiniteDimensional.of_injective
      ((Algebra.linearMap L E).restrictScalars K) (algebraMap L E).injective
  rw [Module.finrank_tensorProduct, MulOpposite.finrank,
    Module.finrank_baseChange, CProduc.finrank_over_base,
    CProduc.finrank_over_base, Module.finrank_linearMap,
    original_crossed_intermediate K L E c,
    ← Module.finrank_mul_finrank K L E]
  ring

private theorem restriction_combined_bijective
    (c : NMCocycl₂ (G := Gal(E/K)) (M := Eˣ)) :
    Function.Bijective (restrictionCombinedAction K L E c) := by
  let A := CProduc c
  let B := CProduc (restrictedCocycle K L E c)
  let C := L ⊗[K] A
  let hScalarCentral : Algebra.IsCentral L (A ⊗[K] L) :=
    BGroups.scalar_extension_central K L A
  letI : Algebra.IsCentral L (A ⊗[K] L) := hScalarCentral
  let eComm : C ≃ₐ[L] A ⊗[K] L :=
    Algebra.TensorProduct.commRight K L A
  letI : Algebra.IsCentral L C :=
    Algebra.IsCentral.of_algEquiv L (A ⊗[K] L) C eComm.symm
  letI : IsSimpleRing C :=
    BGroups.tensor_simple_right
      (k := K) (A := L) (B := A)
  letI : IsSimpleRing (C ⊗[L] Bᵐᵒᵖ) :=
    BGroups.tensor_simple_ring L C Bᵐᵒᵖ
  have hinjRing : Function.Injective
      (restrictionCombinedAction K L E c).toRingHom :=
    @RingHom.injective
      ((L ⊗[K] CProduc c) ⊗[L]
        (CProduc (restrictedCocycle K L E c))ᵐᵒᵖ)
      (Module.End L (CProduc c)) _ _ _ _
      (restrictionCombinedAction K L E c).toRingHom
  have hinj : Function.Injective (restrictionCombinedAction K L E c) := by
    intro x y hxy
    exact hinjRing hxy
  have hinjLinear : Function.Injective
      (restrictionCombinedAction K L E c).toLinearMap := by
    intro x y hxy
    exact hinj hxy
  have hsurj : Function.Surjective
      (restrictionCombinedAction K L E c).toLinearMap := by
    let e := LinearMap.linearEquivOfInjective
      (K := L)
      (V := (L ⊗[K] CProduc c) ⊗[L]
        (CProduc (restrictedCocycle K L E c))ᵐᵒᵖ)
      (V₂ := Module.End L (CProduc c))
      (restrictionCombinedAction K L E c).toLinearMap hinjLinear
      (restriction_combined_end K L E c)
    exact e.surjective
  exact ⟨hinj, hsurj⟩

private noncomputable def restrictionCombinedEnd
    (c : NMCocycl₂ (G := Gal(E/K)) (M := Eˣ)) :
    (L ⊗[K] CProduc c) ⊗[L]
        (CProduc (restrictedCocycle K L E c))ᵐᵒᵖ ≃ₐ[L]
      Module.End L (CProduc c) :=
  AlgEquiv.ofBijective (restrictionCombinedAction K L E c)
    (restriction_combined_bijective K L E c)

private theorem brauer_equivalent_restricted
    (c : NMCocycl₂ (G := Gal(E/K)) (M := Eˣ)) :
    IsBrauerEquivalent
      (scalarExtensionCSA K L (CProduc.centralSimpleCSA K E c))
      (CProduc.centralSimpleCSA L E
        (restrictedCocycle K L E c)) := by
  let A := CProduc c
  let B := CProduc (restrictedCocycle K L E c)
  let C := L ⊗[K] A
  let hScalarCSA := BGroups.scalar_extension_simple K L A
  letI : IsSimpleRing (A ⊗[K] L) := hScalarCSA.1
  letI : Algebra.IsCentral L (A ⊗[K] L) := hScalarCSA.2
  let eComm : C ≃ₐ[L] A ⊗[K] L :=
    Algebra.TensorProduct.commRight K L A
  letI : Algebra.IsCentral L C :=
    Algebra.IsCentral.of_algEquiv L (A ⊗[K] L) C eComm.symm
  letI : IsSimpleRing C :=
    BGroups.tensor_simple_right
      (k := K) (A := L) (B := A)
  letI : Module.Finite L C := Module.Finite.base_change K L A
  have hMorita : IsBrauerEquivalent
      (centralSimpleCSA L C) (centralSimpleCSA L B) :=
    equivalent_op_end L C B A
      (restrictionCombinedEnd K L E c)
  have hComm : IsBrauerEquivalent
      (scalarExtensionCSA K L (centralSimpleCSA K A))
      (centralSimpleCSA L C) :=
    brauer_equivalent_alg L _ _ eComm.symm
  exact hComm.trans hMorita

/-- Scalar extension of a crossed product represents the same Brauer class as
the crossed product of the restricted factor set.  This is the cocycle-level
form of compatibility between Brauer localization and restriction in `H²`. -/
theorem restricted_crossed_brauer
    (c : NMCocycl₂ (G := Gal(E/K)) (M := Eˣ)) :
    brauerClass L
        (CProduc.centralSimpleCSA L E
          (restrictedCocycle K L E c)) =
      brauerBaseChange K L
        (brauerClass K (CProduc.centralSimpleCSA K E c)) := by
  rw [brauer_change_class]
  exact (brauer_class L _ _).2
    (brauer_equivalent_restricted K L E c).symm

/-- Restriction in finite Galois `H²`, defined by transporting scalar
extension of relative Brauer classes through Theorem IV.3.14. -/
def brauerHRestriction :
    MHTwo Gal(E/K) Eˣ →* MHTwo Gal(E/L) Eˣ :=
  (CProduc.hRelativeBrauer L E).symm.toMonoidHom.comp
    ((relativeBrauerChange K L E).comp
      (CProduc.hRelativeBrauer K E).toMonoidHom)

/-- The defining commutative square for Brauer-theoretic restriction. -/
theorem h_brauer_restriction
    (x : MHTwo Gal(E/K) Eˣ) :
    CProduc.hRelativeBrauer L E
        (brauerHRestriction K L E x) =
      relativeBrauerChange K L E
        (CProduc.hRelativeBrauer K E x) := by
  simp [brauerHRestriction]

/-- Brauer-theoretic `H²` restriction is transitive through an intermediate
field. -/
theorem brauer_restriction_trans
    (M : Type u) [Field M]
    [Algebra K M] [Algebra L M] [Algebra M E]
    [IsScalarTower K L M] [IsScalarTower K M E]
    [IsScalarTower L M E]
    [FiniteDimensional M E] [IsGalois M E]
    (x : MHTwo Gal(E/K) Eˣ) :
    brauerHRestriction L M E (brauerHRestriction K L E x) =
      brauerHRestriction K M E x := by
  apply (CProduc.hRelativeBrauer M E).injective
  rw [h_brauer_restriction,
    h_brauer_restriction,
    h_brauer_restriction,
    relative_change_trans]

/-- Cochain restriction agrees with scalar extension of crossed products.
The proof is the Mackey--Morita calculation for the restriction square. -/
theorem GaloisRestrictionCompatibility :
    galoisHRestriction K L E = brauerHRestriction K L E := by
  apply MonoidHom.ext
  intro x
  induction x using Quotient.inductionOn with
  | _ c =>
      apply (CProduc.hRelativeBrauer L E).injective
      rw [h_brauer_restriction]
      change CProduc.relativeBrauerClass L E
          (restrictedCocycle K L E c) =
        relativeBrauerChange K L E
          (CProduc.relativeBrauerClass K E c)
      apply Subtype.ext
      exact restricted_crossed_brauer K L E c

/-- Brauer localization agrees with restriction of factor sets under the
crossed-product classification. -/
theorem brauerRestrictionStatement :
    (CProduc.hRelativeBrauer L E).toMonoidHom.comp
        (galoisHRestriction K L E) =
      (relativeBrauerChange K L E).comp
        (CProduc.hRelativeBrauer K E).toMonoidHom := by
  rw [GaloisRestrictionCompatibility]
  apply MonoidHom.ext
  exact h_brauer_restriction K L E

end

end Towers.CField.CProduca
