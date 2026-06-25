import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Algebra.MonoidAlgebra.Lift
import Mathlib.GroupTheory.Abelianization.Defs
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.Tactic.Module
import Mathlib.Tactic.NoncommRing

/-!
# Milne, Class Field Theory, Lemma II.2.6

For a group `G`, let `I_G` be the augmentation ideal in the integral group ring.  The map

`g ↦ (g - 1) mod I_G²`

induces an isomorphism from the abelianization of `G` to `I_G / I_G²`.
-/

namespace Towers.CField.TCohomo

open Finsupp

universe u

variable (G : Type u) [Group G]

/-- The integral group ring of `G`. -/
abbrev IntegralGroupRing := MonoidAlgebra ℤ G

/-- The augmentation homomorphism `ℤ[G] →+* ℤ`, summing the coefficients. -/
noncomputable def augmentationRingHom : IntegralGroupRing G →+* ℤ :=
  MonoidAlgebra.liftNCRingHom (RingHom.id ℤ) (1 : G →* ℤ) fun _ _ => by simp

/-- The augmentation as an integral linear map. -/
noncomputable def augmentation : IntegralGroupRing G →ₗ[ℤ] ℤ :=
  (augmentationRingHom G).toIntAlgHom.toLinearMap

@[simp]
lemma augmentation_single (g : G) (n : ℤ) :
    augmentation G (single g n) = n := by
  simp [augmentation, augmentationRingHom]

@[simp]
lemma augmentation_one : augmentation G (single 1 1) = 1 := by
  simp

@[simp]
lemma augmentation_mul (x y : IntegralGroupRing G) :
    augmentation G (x * y) = augmentation G x * augmentation G y := by
  exact map_mul (augmentationRingHom G) x y

/-- The augmentation ideal `I_G`. -/
noncomputable def augmentationIdeal : Submodule ℤ (IntegralGroupRing G) :=
  LinearMap.ker (augmentation G)

/-- The standard element `g - 1` of the augmentation ideal. -/
noncomputable def augmentationClass (g : G) : augmentationIdeal G :=
  ⟨single g 1 - single 1 1, by
    rw [augmentationIdeal, LinearMap.mem_ker]
    change augmentationRingHom G (single g 1 - single 1 1) = 0
    calc
      augmentationRingHom G (single g 1 - single 1 1) =
          augmentationRingHom G (single g 1) -
            augmentationRingHom G (single 1 1) :=
        map_sub (augmentationRingHom G) _ _
      _ = 0 := by simp [augmentationRingHom]⟩

@[simp]
lemma augmentationClass_coe (g : G) :
    (augmentationClass G g : IntegralGroupRing G) = single g 1 - single 1 1 :=
  rfl

@[simp]
lemma augmentationClass_one : augmentationClass G 1 = 0 := by
  apply Subtype.ext
  change single 1 (1 : ℤ) - single 1 1 = 0
  abel

/-- The product of two elements of the augmentation ideal, again in the augmentation ideal. -/
noncomputable def augmentationProduct (x y : augmentationIdeal G) : augmentationIdeal G :=
  ⟨x.1 * y.1, by
    change augmentation G (x.1 * y.1) = 0
    rw [augmentation_mul]
    rw [LinearMap.mem_ker.mp x.2, LinearMap.mem_ker.mp y.2, zero_mul]⟩

@[simp]
lemma augmentationProduct_coe (x y : augmentationIdeal G) :
    (augmentationProduct G x y : IntegralGroupRing G) = x.1 * y.1 :=
  rfl

/-- The square `I_G²`, as the subgroup of `I_G` spanned by products of two elements of `I_G`. -/
noncomputable def augmentationIdealSquare : Submodule ℤ (augmentationIdeal G) :=
  Submodule.span ℤ (Set.range fun p : augmentationIdeal G × augmentationIdeal G =>
    augmentationProduct G p.1 p.2)

/-- The additive group `I_G / I_G²`. -/
noncomputable abbrev AugmentationCotangent :=
  augmentationIdeal G ⧸ augmentationIdealSquare G

/-- The class of `g - 1` in `I_G / I_G²`. -/
noncomputable def augmentationCotangentClass (g : G) : AugmentationCotangent G :=
  (augmentationIdealSquare G).mkQ (augmentationClass G g)

@[simp]
lemma augmentation_cotangent_class : augmentationCotangentClass G 1 = 0 := by
  simp [augmentationCotangentClass]

lemma augmentation_cotangent_mul (g h : G) :
    augmentationCotangentClass G (g * h) =
      augmentationCotangentClass G g + augmentationCotangentClass G h := by
  rw [augmentationCotangentClass, augmentationCotangentClass, augmentationCotangentClass,
    ← map_add]
  apply (Submodule.Quotient.eq _).2
  apply Submodule.subset_span
  refine ⟨(augmentationClass G g, augmentationClass G h), ?_⟩
  apply Subtype.ext
  simp only [augmentationProduct_coe, augmentationClass_coe, Submodule.coe_sub,
    Submodule.coe_add]
  let sg : IntegralGroupRing G := single g 1
  let sh : IntegralGroupRing G := single h 1
  let se : IntegralGroupRing G := single 1 1
  let sgh : IntegralGroupRing G := single (g * h) 1
  change (sg - se) * (sh - se) = (sgh - se) - ((sg - se) + (sh - se))
  calc
    _ = sg * sh - sg * se - se * sh + se * se := by
        noncomm_ring
    _ = _ := by
      simp [sg, sh, se, sgh, MonoidAlgebra.single_mul_single]
      abel

/-- The homomorphism `G → I_G / I_G²`, written multiplicatively on the codomain. -/
noncomputable def cotangentMonoidHom :
    G →* Multiplicative (AugmentationCotangent G) where
  toFun g := Multiplicative.ofAdd (augmentationCotangentClass G g)
  map_one' := by simp
  map_mul' g h := by
    apply Multiplicative.toAdd.injective
    exact augmentation_cotangent_mul G g h

/-- The canonical map `Gᵃᵇ → I_G / I_G²`. -/
noncomputable def abelianizationCotangent :
    Additive (Abelianization G) →ₗ[ℤ] AugmentationCotangent G :=
  AddMonoidHom.toIntLinearMap <|
    AddMonoidHom.toMultiplicativeRight.symm <|
      Abelianization.lift (cotangentMonoidHom G)

@[simp]
lemma abelianization_cotangent (g : G) :
    abelianizationCotangent G
        (Additive.ofMul (Abelianization.of g)) =
      augmentationCotangentClass G g := by
  rfl

/-- The coefficient-weighted sum of the classes of group elements in `Gᵃᵇ`. -/
noncomputable def abelianizationSum :
    IntegralGroupRing G →ₗ[ℤ] Additive (Abelianization G) :=
  AddMonoidHom.toIntLinearMap <|
    Finsupp.liftAddHom fun g : G =>
      zmultiplesHom _ (Additive.ofMul (Abelianization.of g))

@[simp]
lemma abelianizationSum_single (g : G) (n : ℤ) :
    abelianizationSum G (single g n) =
      n • Additive.ofMul (Abelianization.of g) := by
  change
    (Finsupp.liftAddHom fun g : G =>
      zmultiplesHom _ (Additive.ofMul (Abelianization.of g))) (single g n) = _
  rw [Finsupp.liftAddHom_apply_single]
  rfl

lemma abelianizationSum_mul (x y : IntegralGroupRing G) :
    abelianizationSum G (x * y) =
      augmentation G y • abelianizationSum G x +
        augmentation G x • abelianizationSum G y := by
  induction x using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x x' hx hx' =>
      simp only [add_mul, map_add, hx, hx', add_zsmul]
      module
  | single g a =>
      induction y using MonoidAlgebra.induction_linear with
      | zero => simp
      | add y y' hy hy' =>
          simp only [mul_add, map_add, hy, hy', add_zsmul]
          module
      | single h b =>
          simp [MonoidAlgebra.single_mul_single, mul_zsmul]
          module

/-- The map `I_G → Gᵃᵇ` sending `∑ n_g g` to `∑ n_g [g]`. -/
noncomputable def augmentationIdealAbelianization :
    augmentationIdeal G →ₗ[ℤ] Additive (Abelianization G) :=
  (abelianizationSum G).comp (augmentationIdeal G).subtype

lemma augmentation_abelianization_product
    (x y : augmentationIdeal G) :
    augmentationIdealAbelianization G (augmentationProduct G x y) = 0 := by
  change abelianizationSum G (x.1 * y.1) = 0
  rw [abelianizationSum_mul]
  rw [LinearMap.mem_ker.mp x.2, LinearMap.mem_ker.mp y.2]
  simp

lemma augmentation_square_ker :
    augmentationIdealSquare G ≤ LinearMap.ker (augmentationIdealAbelianization G) := by
  rw [augmentationIdealSquare, Submodule.span_le]
  rintro z ⟨⟨x, y⟩, rfl⟩
  exact LinearMap.mem_ker.mpr (augmentation_abelianization_product G x y)

/-- The inverse map `I_G / I_G² → Gᵃᵇ`. -/
noncomputable def augmentationCotangentAbelianization :
    AugmentationCotangent G →ₗ[ℤ] Additive (Abelianization G) :=
  (augmentationIdealSquare G).liftQ (augmentationIdealAbelianization G)
    (augmentation_square_ker G)

@[simp]
lemma cotangent_abelianization_class (g : G) :
    augmentationCotangentAbelianization G (augmentationCotangentClass G g) =
      Additive.ofMul (Abelianization.of g) := by
  change augmentationIdealAbelianization G (augmentationClass G g) = _
  change abelianizationSum G (single g 1 - single 1 1) = _
  calc
    abelianizationSum G (single g 1 - single 1 1) =
        abelianizationSum G (single g 1) -
          abelianizationSum G (single 1 1) :=
      map_sub (abelianizationSum G) _ _
    _ = _ := by
      rw [abelianizationSum_single, abelianizationSum_single]
      simp

/-- The coefficient expansion `∑ n_g (g - 1)`, valued in the augmentation ideal. -/
noncomputable def centeredSum : IntegralGroupRing G →ₗ[ℤ] augmentationIdeal G :=
  AddMonoidHom.toIntLinearMap <|
    Finsupp.liftAddHom fun g : G => zmultiplesHom _ (augmentationClass G g)

@[simp]
lemma centeredSum_single (g : G) (n : ℤ) :
    centeredSum G (single g n) = n • augmentationClass G g := by
  change
    (Finsupp.liftAddHom fun g : G => zmultiplesHom _ (augmentationClass G g))
      (single g n) = _
  rw [Finsupp.liftAddHom_apply_single]
  rfl

lemma centeredSum_coe (x : IntegralGroupRing G) :
    (centeredSum G x : IntegralGroupRing G) =
      x - MonoidAlgebra.single 1 (augmentation G x) := by
  induction x using MonoidAlgebra.induction_linear with
  | zero =>
      change (0 : IntegralGroupRing G) = 0 - MonoidAlgebra.single 1 0
      rw [MonoidAlgebra.single_zero, sub_zero]
  | add x y hx hy =>
      change ((centeredSum G (x + y) : augmentationIdeal G) : IntegralGroupRing G) = _
      rw [map_add]
      change
        (centeredSum G x : IntegralGroupRing G) + (centeredSum G y : IntegralGroupRing G) = _
      rw [hx, hy, map_add]
      rw [MonoidAlgebra.single_add]
      abel
  | single g n =>
      rw [centeredSum_single, augmentation_single]
      change
        n • (single g (1 : ℤ) - single 1 1 : IntegralGroupRing G) =
          ((single g n : IntegralGroupRing G) - single 1 n : IntegralGroupRing G)
      calc
        n • (single g (1 : ℤ) - single 1 1 : IntegralGroupRing G) =
            n • (single g (1 : ℤ) : IntegralGroupRing G) -
              n • (single 1 1 : IntegralGroupRing G) :=
          smul_sub n _ _
        _ = _ := by
          rw [Finsupp.smul_single_one, Finsupp.smul_single_one]
          rfl

@[simp]
lemma centered_sum_ideal (x : augmentationIdeal G) :
    centeredSum G x.1 = x := by
  apply Subtype.ext
  rw [centeredSum_coe]
  rw [LinearMap.mem_ker.mp x.2]
  rw [MonoidAlgebra.single_zero, sub_zero]

lemma abelianization_cotangent_sum (x : IntegralGroupRing G) :
    abelianizationCotangent G (abelianizationSum G x) =
      (augmentationIdealSquare G).mkQ (centeredSum G x) := by
  induction x using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => simpa using congrArg₂ (· + ·) hx hy
  | single g n =>
      simp [abelianization_cotangent, augmentationCotangentClass,
        centeredSum_single]

/-- The canonical isomorphism `Gᵃᵇ ≃ I_G / I_G²` of Lemma II.2.6. -/
noncomputable def abelianizationAugmentationCotangent :
    Additive (Abelianization G) ≃+ AugmentationCotangent G :=
  LinearEquiv.toAddEquiv <|
    LinearEquiv.ofLinear
      (abelianizationCotangent G)
      (augmentationCotangentAbelianization G)
      (by
        apply LinearMap.ext
        intro q
        induction q using Submodule.Quotient.induction_on with
        | _ x =>
            change
              abelianizationCotangent G
                  (abelianizationSum G x.1) =
                Submodule.Quotient.mk x
            rw [abelianization_cotangent_sum]
            simp)
      (by
        apply LinearMap.ext
        intro x
        change
          augmentationCotangentAbelianization G
              (abelianizationCotangent G
                (Additive.ofMul x.toMul)) =
            Additive.ofMul x.toMul
        refine QuotientGroup.induction_on x.toMul ?_
        intro g
        change
          augmentationCotangentAbelianization G
              (abelianizationCotangent G
                (Additive.ofMul (Abelianization.of g))) =
            Additive.ofMul (Abelianization.of g)
        rw [abelianization_cotangent,
          cotangent_abelianization_class])

@[simp]
theorem abelianization_equiv_cotangent (g : G) :
    abelianizationAugmentationCotangent G
        (Additive.ofMul (Abelianization.of g)) =
      augmentationCotangentClass G g := by
  rfl

end Towers.CField.TCohomo
