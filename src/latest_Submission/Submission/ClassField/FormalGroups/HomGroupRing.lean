import Submission.ClassField.FormalGroups.Homomorphisms

/-!
# Class Field Theory, Chapter I, Section 2: algebra on formal-group homomorphisms

This file formalizes Lemma 2.8.  Homomorphisms from `F` to `G` form an
additive commutative group, where addition is computed using the target law
`G`.  Endomorphisms form a ring, with multiplication given by composition.
-/

namespace Submission.CField.FGroups

open MvPowerSeries

noncomputable section

namespace FGLaw

variable {R : Type*} [CommRing R]

private theorem subst_zero_coeff {ι σ : Type} [Finite ι]
    (a : ι → MvPowerSeries σ R) (ha : ∀ i, constantCoeff (a i) = 0) :
    HasSubst a :=
  hasSubst_of_constantCoeff_zero ha

private theorem hasSubst_binary {σ : Type} (x y : MvPowerSeries σ R)
    (hx : constantCoeff x = 0) (hy : constantCoeff y = 0) :
    HasSubst (Fin.cases x (fun _ : Fin 1 ↦ y) : Fin 2 → MvPowerSeries σ R) :=
  subst_zero_coeff _ (by intro i; exact Fin.cases hx (fun _ ↦ hy) i)

private theorem hasSubst_unary {σ : Type} (x : MvPowerSeries σ R)
    (hx : constantCoeff x = 0) : HasSubst (fun _ : Fin 1 ↦ x) :=
  subst_zero_coeff _ (fun _ ↦ hx)

private theorem substitute_constant_zero (F : FGLaw R)
    {σ : Type} (x y : MvPowerSeries σ R)
    (hx : constantCoeff x = 0) (hy : constantCoeff y = 0) :
    constantCoeff (substitute F.law x y) = 0 := by
  exact constantCoeff_subst_eq_zero (hasSubst_binary x y hx hy)
    (by intro i; exact Fin.cases hx (fun _ ↦ hy) i)
    (law_constant_coeff F)

private theorem compose_substitute (F : FGLaw R)
    (f g : UnarySeries R) (hf : constantCoeff f = 0)
    (hg : constantCoeff g = 0) {σ : Type} (x : MvPowerSeries σ R)
    (hx : constantCoeff x = 0) :
    compose (substitute F.law f g) x =
      substitute F.law (compose f x) (compose g x) := by
  change subst (fun _ : Fin 1 ↦ x)
      (subst (Fin.cases f (fun _ : Fin 1 ↦ g)) F.law) = _
  rw [subst_comp_subst_apply (hasSubst_binary f g hf hg)
    (hasSubst_unary x hx)]
  congr 1
  funext i
  fin_cases i <;> rfl

private theorem compose_zero {σ : Type} (x : MvPowerSeries σ R)
    (hx : constantCoeff x = 0) : compose 0 x = 0 := by
  change subst (fun _ : Fin 1 ↦ x) 0 = 0
  rw [← substAlgHom_apply (hasSubst_unary x hx)]
  exact map_zero _

private theorem compose_zero_right (f : UnarySeries R)
    (hf : constantCoeff f = 0) : compose f (0 : UnarySeries R) = 0 := by
  have h := rescale_zero_apply f
  rw [rescale_eq_subst] at h
  change subst (fun _ : Fin 1 ↦ (0 : UnarySeries R)) f = 0
  simpa [hf] using h

private theorem substitute_zero_left (F : FGLaw R)
    {σ : Type} (x : MvPowerSeries σ R) (hx : constantCoeff x = 0) :
    substitute F.law 0 x = x := by
  calc
    substitute F.law 0 x =
        substitute F.law (compose (0 : UnarySeries R) x) (compose unaryX x) := by
          rw [compose_zero (R := R) x hx, compose_unaryX x hx]
    _ = compose (substitute F.law 0 unaryX) x :=
      (compose_substitute F 0 unaryX (by simp) (by simp [unaryX]) x hx).symm
    _ = compose unaryX x := by rw [F.left_identity]
    _ = x := compose_unaryX x hx

private theorem substitute_zero_right (F : FGLaw R)
    {σ : Type} (x : MvPowerSeries σ R) (hx : constantCoeff x = 0) :
    substitute F.law x 0 = x := by
  calc
    substitute F.law x 0 =
        substitute F.law (compose unaryX x) (compose (0 : UnarySeries R) x) := by
          rw [compose_zero (R := R) x hx, compose_unaryX x hx]
    _ = compose (substitute F.law unaryX 0) x :=
      (compose_substitute F unaryX 0 (by simp [unaryX]) (by simp) x hx).symm
    _ = compose unaryX x := by rw [F.right_identity]
    _ = x := compose_unaryX x hx

private theorem substitute_substitute (P a b : BinarySeries R)
    (ha : constantCoeff a = 0) (hb : constantCoeff b = 0)
    {σ : Type} (x y : MvPowerSeries σ R)
    (hx : constantCoeff x = 0) (hy : constantCoeff y = 0) :
    substitute (substitute P a b) x y =
      substitute P (substitute a x y) (substitute b x y) := by
  change subst (Fin.cases x (fun _ : Fin 1 ↦ y))
      (subst (Fin.cases a (fun _ : Fin 1 ↦ b)) P) = _
  rw [subst_comp_subst_apply (hasSubst_binary a b ha hb)
    (hasSubst_binary x y hx hy)]
  congr 1
  funext i
  fin_cases i <;> rfl

private theorem substitute_binaryX {σ : Type} (x y : MvPowerSeries σ R)
    (hx : constantCoeff x = 0) (hy : constantCoeff y = 0) :
    substitute binaryX x y = x := by
  change subst (Fin.cases x (fun _ : Fin 1 ↦ y)) (X 0) = x
  rw [subst_X (hasSubst_binary x y hx hy)]
  rfl

private theorem substitute_binaryY {σ : Type} (x y : MvPowerSeries σ R)
    (hx : constantCoeff x = 0) (hy : constantCoeff y = 0) :
    substitute binaryY x y = y := by
  change subst (Fin.cases x (fun _ : Fin 1 ↦ y)) (X 1) = y
  rw [subst_X (hasSubst_binary x y hx hy)]
  rw [show (1 : Fin 2) = Fin.succ 0 by rfl]
  rfl

private theorem substitute_comm (F : FGLaw R)
    {σ : Type} (x y : MvPowerSeries σ R)
    (hx : constantCoeff x = 0) (hy : constantCoeff y = 0) :
    substitute F.law x y = substitute F.law y x := by
  have h := congrArg (fun P : BinarySeries R ↦ substitute P x y) F.commutativity
  change substitute (substitute F.law binaryX binaryY) x y =
    substitute (substitute F.law binaryY binaryX) x y at h
  rw [substitute_substitute F.law binaryX binaryY
      (by simp [binaryX]) (by simp [binaryY]) x y hx hy,
    substitute_substitute F.law binaryY binaryX
      (by simp [binaryY]) (by simp [binaryX]) x y hx hy] at h
  rw [substitute_binaryX x y hx hy, substitute_binaryY x y hx hy] at h
  exact h

private theorem substitute_assoc (F : FGLaw R)
    {σ : Type} (x y z : MvPowerSeries σ R)
    (hx : constantCoeff x = 0) (hy : constantCoeff y = 0)
    (hz : constantCoeff z = 0) :
    substitute F.law x (substitute F.law y z) =
      substitute F.law (substitute F.law x y) z := by
  let b : Fin 3 → MvPowerSeries σ R := ![x, y, z]
  have hb : HasSubst b := subst_zero_coeff b (by
    intro i
    fin_cases i <;> simp [b, hx, hy, hz])
  let aL : Fin 2 → TernarySeries R :=
    Fin.cases ternaryX (fun _ ↦ substitute F.law ternaryY ternaryZ)
  let aR : Fin 2 → TernarySeries R :=
    Fin.cases (substitute F.law ternaryX ternaryY) (fun _ ↦ ternaryZ)
  have haL : HasSubst aL := subst_zero_coeff aL (by
    intro i
    exact Fin.cases (by simp [aL, ternaryX])
      (fun _ ↦ substitute_constant_zero F _ _
        (by simp [ternaryY]) (by simp [ternaryZ])) i)
  have haR : HasSubst aR := subst_zero_coeff aR (by
    intro i
    exact Fin.cases
      (substitute_constant_zero F _ _
        (by simp [ternaryX]) (by simp [ternaryY]))
      (fun _ ↦ by exact constantCoeff_X _) i)
  have hyz : subst b (substitute F.law ternaryY ternaryZ) =
      substitute F.law y z := by
    change subst b (subst (Fin.cases ternaryY (fun _ : Fin 1 ↦ ternaryZ)) F.law) = _
    rw [subst_comp_subst_apply
      (hasSubst_binary ternaryY ternaryZ (by simp [ternaryY]) (by simp [ternaryZ])) hb]
    congr 1
    funext i
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · simp only [Fin.cases_zero, ternaryY, subst_X hb]
      simp [b]
    · simp only [Fin.cases_succ, ternaryZ, subst_X hb]
      simp [b]
  have hxy : subst b (substitute F.law ternaryX ternaryY) =
      substitute F.law x y := by
    change subst b (subst (Fin.cases ternaryX (fun _ : Fin 1 ↦ ternaryY)) F.law) = _
    rw [subst_comp_subst_apply
      (hasSubst_binary ternaryX ternaryY (by simp [ternaryX]) (by simp [ternaryY])) hb]
    congr 1
    funext i
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · simp only [Fin.cases_zero, ternaryX, subst_X hb]
      simp [b]
    · simp only [Fin.cases_succ, ternaryY, subst_X hb]
      simp [b]
  have h := congrArg (substAlgHom hb) F.associativity
  rw [substAlgHom_apply, substAlgHom_apply] at h
  change subst b (subst aL F.law) = subst b (subst aR F.law) at h
  rw [subst_comp_subst_apply haL hb, subst_comp_subst_apply haR hb] at h
  change subst (fun i ↦ subst b (aL i)) F.law =
    subst (fun i ↦ subst b (aR i)) F.law at h
  have hL : (fun i ↦ subst b (aL i)) =
      Fin.cases x (fun _ : Fin 1 ↦ substitute F.law y z) := by
    funext i
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · simp only [Fin.cases_zero, aL, ternaryX, subst_X hb]
      simp [b]
    · simpa only [Fin.cases_succ, aL] using hyz
  have hR : (fun i ↦ subst b (aR i)) =
      Fin.cases (substitute F.law x y) (fun _ : Fin 1 ↦ z) := by
    funext i
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · simpa only [Fin.cases_zero, aR] using hxy
    · simp only [Fin.cases_succ, aR, ternaryZ, subst_X hb]
      simp [b]
  rw [hL, hR] at h
  exact h

private theorem substitute_inverse_right (F : FGLaw R)
    {σ : Type} (x : MvPowerSeries σ R) (hx : constantCoeff x = 0) :
    substitute F.law x (compose F.inverse x) = 0 := by
  calc
    substitute F.law x (compose F.inverse x) =
        substitute F.law (compose unaryX x) (compose F.inverse x) := by
          rw [compose_unaryX x hx]
    _ = compose (substitute F.law unaryX F.inverse) x :=
      (compose_substitute F unaryX F.inverse (by simp [unaryX])
        F.inverse_constantCoeff x hx).symm
    _ = 0 := by rw [F.inverse_law, compose_zero (R := R) x hx]

private theorem substitute_inverse_left (F : FGLaw R)
    {σ : Type} (x : MvPowerSeries σ R) (hx : constantCoeff x = 0) :
    substitute F.law (compose F.inverse x) x = 0 := by
  rw [substitute_comm F]
  · exact substitute_inverse_right F x hx
  · exact constant_coeff_compose F.inverse F.inverse_constantCoeff x hx
  · exact hx

private theorem substitute_inverse_unique (F : FGLaw R)
    {σ : Type} (x i : MvPowerSeries σ R)
    (hx : constantCoeff x = 0) (hi : constantCoeff i = 0)
    (hxi : substitute F.law x i = 0) :
    i = compose F.inverse x := by
  have hinvx := constant_coeff_compose F.inverse
    F.inverse_constantCoeff x hx
  calc
    i = substitute F.law 0 i := (substitute_zero_left F i hi).symm
    _ = substitute F.law (substitute F.law (compose F.inverse x) x) i := by
      rw [substitute_inverse_left F x hx]
    _ = substitute F.law (compose F.inverse x) (substitute F.law x i) :=
      (substitute_assoc F (compose F.inverse x) x i hinvx hx hi).symm
    _ = substitute F.law (compose F.inverse x) 0 := by rw [hxi]
    _ = compose F.inverse x := substitute_zero_right F _ hinvx

namespace Hom

variable {F G H : FGLaw R}

/-- The zero homomorphism, represented by the zero power series. -/
def zero (F G : FGLaw R) : Hom F G where
  toSeries := 0
  constant_coeff_zero := by simp
  map_law x y hx hy := by
    rw [compose_zero (R := R) _ (substitute_constant_zero F x y hx hy)]
    rw [compose_zero (R := R) x hx, compose_zero (R := R) y hy]
    exact (substitute_zero_left G 0 (by simp)).symm

/-- Milne's sum `f +_G g`, computed using the target formal group law. -/
def add (f g : Hom F G) : Hom F G where
  toSeries := substitute G.law f.toSeries g.toSeries
  constant_coeff_zero := substitute_constant_zero G _ _
    f.constant_coeff_zero g.constant_coeff_zero
  map_law x y hx hy := by
    rw [compose_substitute G f.toSeries g.toSeries
      f.constant_coeff_zero g.constant_coeff_zero
      (substitute F.law x y)
      (substitute_constant_zero F x y hx hy)]
    rw [f.map_law x y hx hy, g.map_law x y hx hy]
    rw [compose_substitute G f.toSeries g.toSeries
      f.constant_coeff_zero g.constant_coeff_zero x hx]
    rw [compose_substitute G f.toSeries g.toSeries
      f.constant_coeff_zero g.constant_coeff_zero y hy]
    let fx := compose f.toSeries x
    let fy := compose f.toSeries y
    let gx := compose g.toSeries x
    let gy := compose g.toSeries y
    have hfx : constantCoeff fx = 0 :=
      constant_coeff_compose _ f.constant_coeff_zero _ hx
    have hfy : constantCoeff fy = 0 :=
      constant_coeff_compose _ f.constant_coeff_zero _ hy
    have hgx : constantCoeff gx = 0 :=
      constant_coeff_compose _ g.constant_coeff_zero _ hx
    have hgy : constantCoeff gy = 0 :=
      constant_coeff_compose _ g.constant_coeff_zero _ hy
    change substitute G.law (substitute G.law fx fy) (substitute G.law gx gy) =
      substitute G.law (substitute G.law fx gx) (substitute G.law fy gy)
    rw [substitute_assoc G (substitute G.law fx fy) gx gy
      (substitute_constant_zero G fx fy hfx hfy) hgx hgy]
    rw [← substitute_assoc G fx fy gx hfx hfy hgx]
    rw [substitute_comm G fy gx hfy hgx]
    rw [substitute_assoc G fx gx fy hfx hgx hfy]
    rw [← substitute_assoc G (substitute G.law fx gx) fy gy
      (substitute_constant_zero G fx gx hfx hgx) hfy hgy]

/-- Additive inverse, obtained by applying the target formal inverse. -/
def neg (f : Hom F G) : Hom F G where
  toSeries := compose G.inverse f.toSeries
  constant_coeff_zero := constant_coeff_compose G.inverse
    G.inverse_constantCoeff f.toSeries f.constant_coeff_zero
  map_law x y hx hy := by
    rw [compose_assoc G.inverse f.toSeries f.constant_coeff_zero
      (substitute F.law x y)
      (substitute_constant_zero F x y hx hy)]
    rw [f.map_law x y hx hy]
    rw [compose_assoc G.inverse f.toSeries f.constant_coeff_zero x hx]
    rw [compose_assoc G.inverse f.toSeries f.constant_coeff_zero y hy]
    let fx := compose f.toSeries x
    let fy := compose f.toSeries y
    have hfx : constantCoeff fx = 0 :=
      constant_coeff_compose _ f.constant_coeff_zero _ hx
    have hfy : constantCoeff fy = 0 :=
      constant_coeff_compose _ f.constant_coeff_zero _ hy
    have hix : constantCoeff (compose G.inverse fx) = 0 :=
      constant_coeff_compose _ G.inverse_constantCoeff _ hfx
    have hiy : constantCoeff (compose G.inverse fy) = 0 :=
      constant_coeff_compose _ G.inverse_constantCoeff _ hfy
    have hsum : constantCoeff (substitute G.law fx fy) = 0 :=
      substitute_constant_zero G fx fy hfx hfy
    symm
    apply substitute_inverse_unique G (substitute G.law fx fy)
      (substitute G.law (compose G.inverse fx) (compose G.inverse fy))
      hsum (substitute_constant_zero G _ _ hix hiy)
    rw [substitute_assoc G (substitute G.law fx fy)
      (compose G.inverse fx) (compose G.inverse fy) hsum hix hiy]
    rw [← substitute_assoc G fx fy (compose G.inverse fx) hfx hfy hix]
    rw [substitute_comm G fy (compose G.inverse fx) hfy hix]
    rw [substitute_assoc G fx (compose G.inverse fx) fy hfx hix hfy]
    rw [substitute_inverse_right G fx hfx]
    rw [substitute_zero_left G fy hfy]
    exact substitute_inverse_right G fy hfy

@[simp] theorem zero_toSeries : (zero F G).toSeries = 0 := rfl

@[simp] theorem add_toSeries (f g : Hom F G) :
    (add f g).toSeries = substitute G.law f.toSeries g.toSeries := rfl

@[simp] theorem neg_toSeries (f : Hom F G) :
    (neg f).toSeries = compose G.inverse f.toSeries := rfl

instance : Zero (Hom F G) := ⟨zero F G⟩
instance : Add (Hom F G) := ⟨add⟩
instance : Neg (Hom F G) := ⟨neg⟩

@[simp] theorem zero_toSeries' : (0 : Hom F G).toSeries = 0 := rfl

@[simp] theorem add_toSeries' (f g : Hom F G) :
    (f + g).toSeries = substitute G.law f.toSeries g.toSeries := rfl

@[simp] theorem neg_toSeries' (f : Hom F G) :
    (-f).toSeries = compose G.inverse f.toSeries := rfl

instance : AddCommGroup (Hom F G) where
  add_assoc f g h := by
    apply ext
    exact (substitute_assoc G f.toSeries g.toSeries h.toSeries
      f.constant_coeff_zero g.constant_coeff_zero h.constant_coeff_zero).symm
  zero_add f := by
    apply ext
    exact substitute_zero_left G f.toSeries f.constant_coeff_zero
  add_zero f := by
    apply ext
    exact substitute_zero_right G f.toSeries f.constant_coeff_zero
  neg_add_cancel f := by
    apply ext
    rw [add_toSeries', neg_toSeries']
    rw [substitute_comm G (compose G.inverse f.toSeries) f.toSeries
      (constant_coeff_compose G.inverse G.inverse_constantCoeff
        f.toSeries f.constant_coeff_zero) f.constant_coeff_zero]
    exact substitute_inverse_right G f.toSeries f.constant_coeff_zero
  add_comm f g := by
    apply ext
    exact substitute_comm G f.toSeries g.toSeries
      f.constant_coeff_zero g.constant_coeff_zero
  nsmul := nsmulRec
  zsmul := zsmulRec

/-- Multiplication of endomorphisms is composition: `f * g = f ∘ g`. -/
def mul (f g : Hom F F) : Hom F F := comp f g

instance : One (Hom F F) := ⟨id F⟩
instance : Mul (Hom F F) := ⟨mul⟩

@[simp] theorem one_toSeries : (1 : Hom F F).toSeries = unaryX := rfl

@[simp] theorem mul_toSeries (f g : Hom F F) :
    (f * g).toSeries = compose f.toSeries g.toSeries := rfl

instance : Ring (Hom F F) where
  mul_assoc f g h := by
    exact (comp_assoc f g h).symm
  one_mul f := id_comp f
  mul_one f := comp_id f
  left_distrib f g h := by
    apply ext
    exact f.map_law g.toSeries h.toSeries
      g.constant_coeff_zero h.constant_coeff_zero
  right_distrib f g h := by
    apply ext
    exact compose_substitute F f.toSeries g.toSeries
      f.constant_coeff_zero g.constant_coeff_zero h.toSeries
      h.constant_coeff_zero
  zero_mul f := by
    apply ext
    exact compose_zero (R := R) f.toSeries f.constant_coeff_zero
  mul_zero f := by
    apply ext
    exact compose_zero_right f.toSeries f.constant_coeff_zero

end Hom

end FGLaw

end

end Submission.CField.FGroups
