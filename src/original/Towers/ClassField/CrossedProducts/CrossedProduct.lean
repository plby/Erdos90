import Mathlib.Algebra.SkewMonoidAlgebra.Basic
import Mathlib.Algebra.Group.Action.Units
import Mathlib.Algebra.Ring.TransferInstance
import Towers.ClassField.CrossedProducts.NormalizedCocycle

/-!
# Chapter IV, Section 3: crossed-product algebras

This file constructs the twisted skew group algebra attached to a normalized
multiplicative `2`-cocycle.  Its underlying module is the free module with
basis indexed by the acting group, while multiplication is

`(a e_g) (b e_h) = a (g • b) phi(g,h) e_(gh)`.
-/

namespace Towers.CField.CProduca

noncomputable section

universe u v

attribute [local instance] Units.mulDistribMulActionRight

/-- The crossed product attached to a normalized `2`-cocycle.  The wrapper
keeps the cocycle as part of the type, so distinct twists have distinct ring
structures. -/
structure CProduc {G : Type u} {L : Type v} [Group G] [CommRing L]
    [MulSemiringAction G L]
    (c : NMCocycl₂ (G := G) (M := Lˣ)) where
  skewMonoid : SkewMonoidAlgebra L G

namespace CProduc

variable {G : Type u} {L : Type v} [Group G] [CommRing L] [MulSemiringAction G L]
  (c : NMCocycl₂ (G := G) (M := Lˣ))

/-- The additive equivalence with the ordinary skew group algebra.  Only the
multiplication is changed by the cocycle. -/
def toSkewEquiv : CProduc c ≃ SkewMonoidAlgebra L G where
  toFun := CProduc.skewMonoid
  invFun := CProduc.mk
  left_inv x := by cases x; rfl
  right_inv _ := rfl

instance : AddCommGroup (CProduc c) := (toSkewEquiv c).addCommGroup

instance : AddGroupWithOne (CProduc c) := (toSkewEquiv c).addGroupWithOne

/-- The transported additive equivalence. -/
def skewAddEquiv : CProduc c ≃+ SkewMonoidAlgebra L G :=
  Equiv.addEquiv (toSkewEquiv c)

instance : Module L (CProduc c) := (skewAddEquiv c).module L

/-- The transported `L`-linear equivalence. -/
def skewLinearEquiv : CProduc c ≃ₗ[L] SkewMonoidAlgebra L G :=
  { skewAddEquiv c with map_smul' := fun _ _ ↦ rfl }

@[ext]
theorem ext {x y : CProduc c}
    (h : x.skewMonoid = y.skewMonoid) : x = y := by
  cases x
  cases y
  simpa using h

@[simp]
theorem toSkew_zero : (0 : CProduc c).skewMonoid = 0 := rfl

@[simp]
theorem toSkew_add (x y : CProduc c) :
    (x + y).skewMonoid =
      x.skewMonoid + y.skewMonoid := rfl

@[simp]
theorem toSkew_neg (x : CProduc c) :
    (-x).skewMonoid = -x.skewMonoid := rfl

@[simp]
theorem toSkew_smul (a : L) (x : CProduc c) :
    (a • x).skewMonoid = a • x.skewMonoid := rfl

/-- A single basis term `a e_g`. -/
def single (g : G) (a : L) : CProduc c :=
  ⟨SkewMonoidAlgebra.single g a⟩

@[simp]
theorem toSkew_single (g : G) (a : L) :
    (single c g a).skewMonoid = SkewMonoidAlgebra.single g a := rfl

@[simp]
theorem single_zero (g : G) : single c g 0 = 0 := by
  ext
  simp [single]

@[simp]
theorem single_add (g : G) (a b : L) :
    single c g (a + b) = single c g a + single c g b := by
  ext
  simp [single]

@[simp]
theorem smul_single (a b : L) (g : G) :
    a • single c g b = single c g (a * b) := by
  apply ext
  exact SkewMonoidAlgebra.smul_single a g b

/-- Sum over the finite support of a crossed-product element. -/
def sum {N : Type*} [AddCommMonoid N] (x : CProduc c)
    (f : G → L → N) : N :=
  x.skewMonoid.sum f

@[simp]
theorem sum_single_index {N : Type*} [AddCommMonoid N]
    {g : G} {a : L} {f : G → L → N} (hzero : f g 0 = 0) :
    sum c (single c g a) f = f g a :=
  SkewMonoidAlgebra.sum_single_index hzero

theorem sum_add_index' {N : Type*} [AddCommMonoid N]
    {x y : CProduc c} {f : G → L → N}
    (hzero : ∀ g, f g 0 = 0)
    (hadd : ∀ g a b, f g (a + b) = f g a + f g b) :
    sum c (x + y) f = sum c x f + sum c y f :=
  SkewMonoidAlgebra.sum_add_index' hzero hadd

@[simp]
theorem sum_add {N : Type*} [AddCommMonoid N] (x : CProduc c)
    (f g : G → L → N) :
    sum c x (fun i a ↦ f i a + g i a) = sum c x f + sum c x g :=
  SkewMonoidAlgebra.sum_add _ _ _

@[simp]
theorem sum_zero {N : Type*} [AddCommMonoid N] (x : CProduc c) :
    sum c x (fun _ _ ↦ (0 : N)) = 0 :=
  SkewMonoidAlgebra.sum_zero

@[simp]
theorem sum_zero_index {N : Type*} [AddCommMonoid N] {f : G → L → N} :
    sum c (0 : CProduc c) f = 0 :=
  SkewMonoidAlgebra.sum_zero_index

@[elab_as_elim]
theorem induction_on {p : CProduc c → Prop} (x : CProduc c)
    (zero : p 0) (hsingle : ∀ g a, p (single c g a))
    (hadd : ∀ x y, p x → p y → p (x + y)) : p x := by
  let q : SkewMonoidAlgebra L G → Prop := fun f ↦ p ⟨f⟩
  have hq : q x.skewMonoid := by
    refine SkewMonoidAlgebra.induction_on (p := q) x.skewMonoid ?_ ?_ ?_
    · exact zero
    · exact hsingle
    · intro f g hf hg
      exact hadd ⟨f⟩ ⟨g⟩ hf hg
  simpa [q] using hq

/-- Twisted convolution multiplication. -/
instance : Mul (CProduc c) :=
  ⟨fun x y ↦ sum c x fun g a ↦
    sum c y fun h b ↦ single c (g * h) (a * (g • b) * (c (g, h) : L))⟩

theorem mul_def (x y : CProduc c) :
    x * y = sum c x fun g a ↦
      sum c y fun h b ↦ single c (g * h) (a * (g • b) * (c (g, h) : L)) :=
  rfl

@[simp]
theorem single_mul_single (g h : G) (a b : L) :
    single c g a * single c h b =
      single c (g * h) (a * (g • b) * (c (g, h) : L)) := by
  rw [mul_def, sum_single_index, sum_single_index]
  · simp
  · simp

@[simp]
theorem one_def : (1 : CProduc c) = single c 1 1 := rfl

instance : NonUnitalNonAssocRing (CProduc c) where
  left_distrib x y z := by
    classical
    simp only [mul_def]
    have hinner (g : G) (a : L) :
        sum c (y + z) (fun h b ↦
            single c (g * h) (a * (g • b) * (c (g, h) : L))) =
          sum c y (fun h b ↦
            single c (g * h) (a * (g • b) * (c (g, h) : L))) +
          sum c z (fun h b ↦
            single c (g * h) (a * (g • b) * (c (g, h) : L))) := by
      apply sum_add_index' c
      · intro h
        simp
      · intro h b d
        simp only [smul_add, mul_add, add_mul, single_add]
    simp_rw [hinner]
    exact sum_add c x _ _
  right_distrib x y z := by
    classical
    simp only [mul_def]
    apply sum_add_index' c
    · intro g
      simp
    · intro g a b
      simpa only [add_mul, single_add] using
        (sum_add c z
          (fun h d ↦ single c (g * h) (a * (g • d) * (c (g, h) : L)))
          (fun h d ↦ single c (g * h) (b * (g • d) * (c (g, h) : L))))
  zero_mul x := by simp [mul_def]
  mul_zero x := by simp [mul_def]

private theorem single_mul_assoc (g h j : G) (a b d : L) :
    (single c g a * single c h b) * single c j d =
      single c g a * (single c h b * single c j d) := by
  rw [single_mul_single, single_mul_single, single_mul_single, single_mul_single]
  rw [show (g * h) * j = g * (h * j) by simp only [mul_assoc]]
  apply congrArg (single c (g * (h * j)))
  have hc := congrArg Units.val (c.isMulCocycle₂ g h j)
  change (c (g * h, j) : L) * (c (g, h) : L) =
    (g • (c (h, j) : L)) * (c (g, h * j) : L) at hc
  calc
    (a * (g • b) * (c (g, h) : L)) * ((g * h) • d) * (c (g * h, j) : L) =
        a * (g • b) * ((g * h) • d) *
          ((c (g * h, j) : L) * (c (g, h) : L)) := by ring
    _ = a * (g • b) * ((g * h) • d) *
          ((g • (c (h, j) : L)) * (c (g, h * j) : L)) := by rw [hc]
    _ = a * (g • (b * (h • d) * (c (h, j) : L))) *
          (c (g, h * j) : L) := by
      simp only [smul_mul', mul_smul]
      ring

instance : NonAssocRing (CProduc c) where
  __ := (inferInstance : NonUnitalNonAssocRing (CProduc c))
  __ := (inferInstance : AddGroupWithOne (CProduc c))
  one_mul x := by
    induction x using induction_on c with
    | zero => simp
    | hsingle g a => simp [single_mul_single]
    | hadd x y hx hy => simpa [mul_add] using congrArg₂ (· + ·) hx hy
  mul_one x := by
    induction x using induction_on c with
    | zero => simp
    | hsingle g a => simp [single_mul_single]
    | hadd x y hx hy => simpa [add_mul] using congrArg₂ (· + ·) hx hy

instance : Ring (CProduc c) where
  __ := (inferInstance : NonAssocRing (CProduc c))
  mul_assoc x y z := by
    induction x using induction_on c with
    | zero => simp
    | hsingle g a =>
      induction y using induction_on c with
      | zero => simp
      | hsingle h b =>
        induction z using induction_on c with
        | zero => simp
        | hsingle j d => exact single_mul_assoc c g h j a b d
        | hadd z w hz hw => simp_all [mul_add]
      | hadd y z hy hz => simp_all [add_mul, mul_add]
    | hadd x y hx hy => simp_all [add_mul]

/-- The standard basis `e_g`. -/
def basis : Module.Basis G L (CProduc c) :=
  SkewMonoidAlgebra.basisSingleOne.map (skewLinearEquiv c).symm

@[simp]
theorem basis_apply (g : G) : basis c g = single c g 1 := by
  apply ext
  rfl

/-- The coefficient of the standard basis vector indexed by `g`. -/
def coeff (x : CProduc c) (g : G) : L :=
  x.skewMonoid.coeff g

@[simp]
theorem coeff_zero (g : G) : coeff c 0 g = 0 :=
  SkewMonoidAlgebra.coeff_zero g

@[simp]
theorem coeff_add (x y : CProduc c) (g : G) :
    coeff c (x + y) g = coeff c x g + coeff c y g :=
  SkewMonoidAlgebra.coeff_add _ _ _

@[simp]
theorem coeff_smul (a : L) (x : CProduc c) (g : G) :
    coeff c (a • x) g = a * coeff c x g := by
  rfl

theorem coeff_single (g h : G) (a : L) [Decidable (g = h)] :
    coeff c (single c g a) h = if g = h then a else 0 :=
  SkewMonoidAlgebra.coeff_single_apply

theorem ext_coeff {x y : CProduc c}
    (h : ∀ g, coeff c x g = coeff c y g) : x = y := by
  apply ext
  exact SkewMonoidAlgebra.ext h

/-- The canonical copy of the coefficient ring, `a ↦ a e_1`. -/
def coefficientRingHom : L →+* CProduc c where
  toFun a := single c 1 a
  map_zero' := single_zero c 1
  map_one' := one_def c
  map_add' a b := single_add c 1 a b
  map_mul' a b := by simp [single_mul_single]

@[simp]
theorem coefficient_ring_hom (a : L) :
    coefficientRingHom c a = single c 1 a := rfl

theorem coefficient_ring_injective : Function.Injective (coefficientRingHom c) := by
  intro a b h
  have h' := congrArg (fun x : CProduc c ↦ x.skewMonoid) h
  exact SkewMonoidAlgebra.single_injective (1 : G) h'

@[simp]
theorem coefficient_mul_single (a b : L) (g : G) :
    coefficientRingHom c a * single c g b = single c g (a * b) := by
  simp [coefficientRingHom, single_mul_single]

@[simp]
theorem single_mul_coefficient (g : G) (a b : L) :
    single c g a * coefficientRingHom c b = single c g (a * (g • b)) := by
  simp [coefficientRingHom, single_mul_single]

/-- Left multiplication by a coefficient is the transported `L`-module
structure on the crossed product. -/
theorem coefficient_mul (a : L) (x : CProduc c) :
    coefficientRingHom c a * x = a • x := by
  induction x using induction_on c with
  | zero => simp
  | hsingle g b => simp
  | hadd x y hx hy => rw [mul_add, hx, hy, smul_add]

end CProduc

end

end Towers.CField.CProduca
