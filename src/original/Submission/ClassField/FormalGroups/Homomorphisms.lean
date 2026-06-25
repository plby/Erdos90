import Submission.ClassField.FormalGroups.FormalGroupLaw

/-!
# Class Field Theory, Chapter I, Section 2: homomorphisms of formal groups

This file formalizes Definition 2.6, Example 2.7, and the elementary
identity/composition part of Lemma 2.8.
-/

namespace Submission.CField.FGroups

open MvPowerSeries

noncomputable section

namespace FGLaw

variable {R : Type*} [CommRing R]

private theorem hasSubst_unary {σ : Type} (x : MvPowerSeries σ R)
    (hx : constantCoeff x = 0) : HasSubst (fun _ : Fin 1 ↦ x) :=
  hasSubst_of_constantCoeff_zero (fun _ ↦ hx)

private theorem hasSubst_binary {σ : Type} (x y : MvPowerSeries σ R)
    (hx : constantCoeff x = 0) (hy : constantCoeff y = 0) :
    HasSubst (Fin.cases x (fun _ : Fin 1 ↦ y) : Fin 2 → MvPowerSeries σ R) := by
  apply hasSubst_of_constantCoeff_zero
  intro i
  exact Fin.cases hx (fun _ ↦ hy) i

private theorem constant_coeff_subst
    {ι σ : Type} [Finite ι] (a : ι → MvPowerSeries σ R)
    (ha : ∀ i, constantCoeff (a i) = 0) (f : MvPowerSeries ι R) :
    constantCoeff (subst a f) = constantCoeff f := by
  rw [constantCoeff_subst (hasSubst_of_constantCoeff_zero ha)]
  rw [finsum_eq_single _ 0]
  · simp
  · intro d hd
    obtain ⟨i, hi⟩ : ∃ i : ι, d i ≠ 0 := by
      by_contra! h
      exact hd (Finsupp.ext h)
    have hprod : constantCoeff (d.prod fun s e ↦ a s ^ e) = 0 := by
      simpa [map_finsuppProd, ha] using
        Finset.prod_eq_zero (i := i) (by simp [hi]) (by simp [zero_pow hi])
    rw [hprod, smul_zero]

@[simp]
theorem compose_unaryX {σ : Type} (x : MvPowerSeries σ R)
    (hx : constantCoeff x = 0) : compose unaryX x = x := by
  exact subst_X (hasSubst_unary x hx) 0

theorem constant_coeff_compose (f : UnarySeries R)
    (hf : constantCoeff f = 0) {σ : Type} (x : MvPowerSeries σ R)
    (hx : constantCoeff x = 0) : constantCoeff (compose f x) = 0 := by
  exact constantCoeff_subst_eq_zero (hasSubst_unary x hx) (fun _ ↦ hx) hf

theorem compose_assoc (h g : UnarySeries R)
    (hg : constantCoeff g = 0) {σ : Type} (x : MvPowerSeries σ R)
    (hx : constantCoeff x = 0) :
    compose (compose h g) x = compose h (compose g x) := by
  exact subst_comp_subst_apply (hasSubst_unary g hg) (hasSubst_unary x hx) h

theorem law_constant_coeff (F : FGLaw R) :
    constantCoeff F.law = 0 := by
  have h := congrArg constantCoeff F.left_identity
  change constantCoeff
      (subst (Fin.cases (0 : UnarySeries R) (fun _ : Fin 1 ↦ unaryX)) F.law) =
    constantCoeff unaryX at h
  rw [constant_coeff_subst _
    (by intro i; exact Fin.cases (by simp) (fun _ ↦ by simp [unaryX]) i)] at h
  simpa [unaryX] using h

theorem compose_unary_x (f : UnarySeries R) : compose f unaryX = f := by
  have hfamily : (fun _ : Fin 1 ↦ unaryX) =
      (MvPowerSeries.X : Fin 1 → UnarySeries R) := by
    funext i
    exact Fin.cases rfl (fun j ↦ Fin.elim0 j) i
  rw [compose, hfamily]
  exact congrFun (subst_self (R := R)) f

/-- Definition 2.6. A homomorphism from `F` to `G` is a series with zero
constant coefficient which respects the two formal group laws.

The law equation is stated after arbitrary zero-constant substitutions.  Its
specialization to `binaryX` and `binaryY` is exactly Milne's displayed
identity `h(F(X,Y)) = G(h(X),h(Y))`; the substitution-stable form is more
convenient for composing homomorphisms. -/
structure Hom (F G : FGLaw R) where
  toSeries : UnarySeries R
  constant_coeff_zero : constantCoeff toSeries = 0
  map_law : ∀ {σ : Type} (x y : MvPowerSeries σ R),
    constantCoeff x = 0 → constantCoeff y = 0 →
      compose toSeries (substitute F.law x y) =
        substitute G.law (compose toSeries x) (compose toSeries y)

namespace Hom

variable {F G H : FGLaw R}

@[ext]
theorem ext {f g : Hom F G} (h : f.toSeries = g.toSeries) : f = g := by
  cases f
  cases g
  cases h
  rfl

/-- The defining law equation in the literal two-variable form used by
Definition 2.6. -/
theorem map_law_binary (f : Hom F G) :
    compose f.toSeries (substitute F.law binaryX binaryY) =
      substitute G.law (compose f.toSeries binaryX) (compose f.toSeries binaryY) := by
  apply f.map_law (σ := Fin 2)
  · simp [binaryX]
  · simp [binaryY]

/-- The identity homomorphism of a formal group law. -/
def id (F : FGLaw R) : Hom F F where
  toSeries := unaryX
  constant_coeff_zero := by simp [unaryX]
  map_law x y hx hy := by
    rw [compose_unaryX _]
    · rw [compose_unaryX x hx, compose_unaryX y hy]
    · exact constantCoeff_subst_eq_zero (hasSubst_binary x y hx hy)
        (by intro i; exact Fin.cases hx (fun _ ↦ hy) i)
        (law_constant_coeff F)

/-- Composition of homomorphisms is composition of their power series. -/
def comp (g : Hom G H) (f : Hom F G) : Hom F H where
  toSeries := compose g.toSeries f.toSeries
  constant_coeff_zero :=
    constant_coeff_compose g.toSeries g.constant_coeff_zero
      f.toSeries f.constant_coeff_zero
  map_law x y hx hy := by
    have hFxy : constantCoeff (substitute F.law x y) = 0 := by
      change constantCoeff
          (subst (Fin.cases x (fun _ : Fin 1 ↦ y)) F.law) = 0
      rw [constant_coeff_subst _
        (by intro i; exact Fin.cases hx (fun _ ↦ hy) i)]
      exact law_constant_coeff F
    rw [compose_assoc g.toSeries f.toSeries f.constant_coeff_zero
      (substitute F.law x y) hFxy]
    rw [f.map_law x y hx hy]
    rw [g.map_law (compose f.toSeries x) (compose f.toSeries y)]
    · rw [← compose_assoc g.toSeries f.toSeries f.constant_coeff_zero x hx]
      rw [← compose_assoc g.toSeries f.toSeries f.constant_coeff_zero y hy]
    · exact constant_coeff_compose f.toSeries f.constant_coeff_zero x hx
    · exact constant_coeff_compose f.toSeries f.constant_coeff_zero y hy

@[simp]
theorem id_toSeries : (id F).toSeries = unaryX := rfl

@[simp]
theorem comp_toSeries (g : Hom G H) (f : Hom F G) :
    (comp g f).toSeries = compose g.toSeries f.toSeries := rfl

@[simp]
theorem id_comp (f : Hom F G) : comp (id G) f = f := by
  apply ext
  exact compose_unaryX f.toSeries f.constant_coeff_zero

@[simp]
theorem comp_id (f : Hom F G) : comp f (id F) = f := by
  apply ext
  exact compose_unary_x f.toSeries

theorem comp_assoc {K : FGLaw R} (h : Hom H K) (g : Hom G H)
    (f : Hom F G) : comp h (comp g f) = comp (comp h g) f := by
  apply ext
  exact (compose_assoc h.toSeries g.toSeries g.constant_coeff_zero
    f.toSeries f.constant_coeff_zero).symm

end Hom

/-- An isomorphism of formal group laws is a homomorphism with a two-sided
inverse. -/
structure Iso (F G : FGLaw R) where
  hom : Hom F G
  inv : Hom G F
  inv_hom_id : Hom.comp inv hom = Hom.id F
  hom_inv_id : Hom.comp hom inv = Hom.id G

namespace Iso

variable {F G : FGLaw R}

/-- The identity isomorphism. -/
def refl (F : FGLaw R) : Iso F F where
  hom := Hom.id F
  inv := Hom.id F
  inv_hom_id := Hom.id_comp _
  hom_inv_id := Hom.id_comp _

/-- The inverse isomorphism. -/
def symm (e : Iso F G) : Iso G F where
  hom := e.inv
  inv := e.hom
  inv_hom_id := e.hom_inv_id
  hom_inv_id := e.inv_hom_id

end Iso

/-- Example 2.7. The endomorphism `[n](T) = (1+T)^n-1` of the
multiplicative formal group. -/
def multiplicativeNatEndomorphism (n : ℕ) :
    Hom (multiplicative (R := R)) (multiplicative (R := R)) where
  toSeries := (1 + unaryX) ^ n - 1
  constant_coeff_zero := by simp [unaryX]
  map_law {σ} x y hx hy := by
    have hEval (z : MvPowerSeries σ R) (hz : constantCoeff z = 0) :
        compose ((1 + unaryX) ^ n - 1) z = (1 + z) ^ n - 1 := by
      have hzSub := hasSubst_unary z hz
      change subst (fun _ : Fin 1 ↦ z) ((1 + unaryX) ^ n - 1) = _
      rw [subst_sub hzSub, subst_pow hzSub, subst_add hzSub]
      change (subst (fun _ : Fin 1 ↦ z) 1 + compose unaryX z) ^ n -
          subst (fun _ : Fin 1 ↦ z) 1 = _
      rw [compose_unaryX z hz]
      have hone : subst (fun _ : Fin 1 ↦ z) (1 : UnarySeries R) = 1 := by
        rw [← substAlgHom_apply hzSub]
        exact map_one _
      rw [hone]
    change compose ((1 + unaryX) ^ n - 1)
        (substitute (multiplicativeLaw (R := R)) x y) =
      substitute (multiplicativeLaw (R := R))
        (compose ((1 + unaryX) ^ n - 1) x)
        (compose ((1 + unaryX) ^ n - 1) y)
    rw [substitute_multiplicativeLaw]
    have hxy : constantCoeff (x + y + x * y) = 0 := by simp [hx, hy]
    rw [hEval (x + y + x * y) hxy]
    rw [substitute_multiplicativeLaw]
    rw [hEval x hx, hEval y hy]
    rw [show 1 + (x + y + x * y) = (1 + x) * (1 + y) by ring, mul_pow]
    ring

end FGLaw

end

end Submission.CField.FGroups
