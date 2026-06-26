import Towers.ClassField.CrossedProducts.MulApply

/-!
# Chapter IV, Section 3: normalized multiplicative `H²`

This file presents degree-two cohomology by normalized multiplicative
cocycles modulo multiplicative coboundaries.  This presentation is universe
polymorphic and is the one used by Milne's crossed-product construction.
-/

namespace Towers.CField.CProduca

open groupCohomology

universe u v

variable {G : Type u} {M : Type v}
  [Group G] [CommGroup M] [MulDistribMulAction G M]

namespace NMCocycl₂

/-- The constant normalized cocycle. -/
def one : NMCocycl₂ (G := G) (M := M) where
  toFun _ := 1
  isMulCocycle₂ _ _ _ := by simp
  map_one_fst _ := rfl
  map_one_snd _ := rfl

/-- Pointwise inversion of a normalized cocycle. -/
def inv (c : NMCocycl₂ (G := G) (M := M)) :
    NMCocycl₂ (G := G) (M := M) where
  toFun p := (c p)⁻¹
  isMulCocycle₂ g h j := by
    rw [smul_inv']
    have hc := congrArg Inv.inv (c.isMulCocycle₂ g h j)
    simp only [mul_inv_rev] at hc
    calc
      (c (g * h, j))⁻¹ * (c (g, h))⁻¹ =
          (c (g, h))⁻¹ * (c (g * h, j))⁻¹ := mul_comm _ _
      _ = (c (g, h * j))⁻¹ * (g • c (h, j))⁻¹ := hc
      _ = (g • c (h, j))⁻¹ * (c (g, h * j))⁻¹ := mul_comm _ _
  map_one_fst g := by simp
  map_one_snd g := by simp

@[ext]
theorem ext {c d : NMCocycl₂ (G := G) (M := M)}
    (h : ∀ p, c p = d p) : c = d := by
  cases c with
  | mk c hc c1 c2 =>
      cases d with
      | mk d hd d1 d2 =>
          have : c = d := funext h
          subst d
          rfl

/-- Normalized multiplicative cocycles form an abelian group under pointwise
multiplication. -/
instance : CommGroup (NMCocycl₂ (G := G) (M := M)) where
  mul := mul
  one := one
  inv := inv
  mul_assoc a b c := by ext p; exact mul_assoc _ _ _
  one_mul a := by ext p; exact one_mul _
  mul_one a := by ext p; exact mul_one _
  inv_mul_cancel a := by ext p; exact inv_mul_cancel _
  mul_comm a b := by ext p; exact mul_comm _ _

@[simp]
theorem instMul_apply
    (c d : NMCocycl₂ (G := G) (M := M)) (p : G × G) :
    (c * d) p = c p * d p :=
  rfl

@[simp]
theorem one_apply (p : G × G) :
    (1 : NMCocycl₂ (G := G) (M := M)) p = 1 :=
  rfl

@[simp]
theorem inv_apply (c : NMCocycl₂ (G := G) (M := M))
    (p : G × G) : c⁻¹ p = (c p)⁻¹ :=
  rfl

@[simp]
theorem pow_apply (c : NMCocycl₂ (G := G) (M := M))
    (n : ℕ) (p : G × G) : (c ^ n) p = (c p) ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, one_apply]
  | succ n ih => rw [pow_succ, pow_succ, instMul_apply, ih]

end NMCocycl₂

namespace MHTwo

/-- Two normalized cocycles are cohomologous when their quotient is a
multiplicative two-coboundary. -/
def IsCohomologous
    (c d : NMCocycl₂ (G := G) (M := M)) : Prop :=
  IsMulCoboundary₂ (fun p ↦ c p / d p)

theorem isCohomologous_refl
    (c : NMCocycl₂ (G := G) (M := M)) :
    IsCohomologous c c := by
  refine ⟨fun _ ↦ 1, ?_⟩
  intro g h
  simp

theorem isCohomologous_symm
    {c d : NMCocycl₂ (G := G) (M := M)}
    (hcd : IsCohomologous c d) : IsCohomologous d c := by
  obtain ⟨x, hx⟩ := hcd
  refine ⟨fun g ↦ (x g)⁻¹, ?_⟩
  intro g h
  have hi := congrArg Inv.inv (hx g h)
  simp only [smul_inv', div_eq_mul_inv, mul_inv_rev, inv_inv] at hi ⊢
  calc
    (g • x h)⁻¹ * x (g * h) * (x g)⁻¹ =
        (x g)⁻¹ * x (g * h) * (g • x h)⁻¹ := by ac_rfl
    _ = d (g, h) * (c (g, h))⁻¹ := by
      simpa only [mul_assoc] using hi

theorem isCohomologous_trans
    {c d e : NMCocycl₂ (G := G) (M := M)}
    (hcd : IsCohomologous c d) (hde : IsCohomologous d e) :
    IsCohomologous c e := by
  obtain ⟨x, hx⟩ := hcd
  obtain ⟨y, hy⟩ := hde
  refine ⟨fun g ↦ x g * y g, ?_⟩
  intro g h
  have hx' := hx g h
  have hy' := hy g h
  simp only [div_eq_mul_inv] at hx' hy'
  simp only [smul_mul', div_eq_mul_inv, mul_inv_rev]
  calc
    _ =
        ((g • x h) * (x (g * h))⁻¹ * x g) *
          ((g • y h) * (y (g * h))⁻¹ * y g) := by ac_rfl
    _ = (c (g, h) * (d (g, h))⁻¹) *
          (d (g, h) * (e (g, h))⁻¹) := by rw [hx', hy']
    _ = c (g, h) * (e (g, h))⁻¹ := by simp [mul_assoc]

theorem isCohomologous_mul
    {c c' d d' : NMCocycl₂ (G := G) (M := M)}
    (hc : IsCohomologous c c') (hd : IsCohomologous d d') :
    IsCohomologous (c * d) (c' * d') := by
  obtain ⟨x, hx⟩ := hc
  obtain ⟨y, hy⟩ := hd
  refine ⟨fun g ↦ x g * y g, ?_⟩
  intro g h
  have hx' := hx g h
  have hy' := hy g h
  simp only [div_eq_mul_inv] at hx' hy'
  simp only [smul_mul', div_eq_mul_inv, mul_inv_rev]
  calc
    _ =
        ((g • x h) * (x (g * h))⁻¹ * x g) *
          ((g • y h) * (y (g * h))⁻¹ * y g) := by ac_rfl
    _ = (c (g, h) * (c' (g, h))⁻¹) *
          (d (g, h) * (d' (g, h))⁻¹) := by rw [hx', hy']
    _ = c (g, h) * d (g, h) *
          (c' (g, h) * d' (g, h))⁻¹ := by
      simp only [mul_inv_rev]
      ac_rfl

theorem isCohomologous_inv
    {c d : NMCocycl₂ (G := G) (M := M)}
    (hcd : IsCohomologous c d) : IsCohomologous c⁻¹ d⁻¹ :=
  by
    simpa [IsCohomologous, div_eq_mul_inv, mul_comm] using
      isCohomologous_symm hcd

/-- The equivalence relation defining multiplicative `H²`. -/
def setoid : Setoid (NMCocycl₂ (G := G) (M := M)) where
  r := IsCohomologous
  iseqv := ⟨isCohomologous_refl, isCohomologous_symm, isCohomologous_trans⟩

end MHTwo

/-- Degree-two cohomology of a multiplicative action, presented by normalized
cocycles modulo multiplicative coboundaries. -/
def MHTwo (G : Type u) (M : Type v) [Group G] [CommGroup M]
    [MulDistribMulAction G M] :=
  Quotient (MHTwo.setoid (G := G) (M := M))

namespace MHTwo

/-- The cohomology class of a normalized cocycle. -/
def mk (c : NMCocycl₂ (G := G) (M := M)) : MHTwo G M :=
  Quotient.mk'' c

private def mul (x y : MHTwo G M) : MHTwo G M :=
  Quotient.map₂ (fun c d ↦ c * d)
    (fun _ _ hc _ _ hd ↦ isCohomologous_mul hc hd) x y

private def inv (x : MHTwo G M) : MHTwo G M :=
  Quotient.map Inv.inv (fun _ _ h ↦ isCohomologous_inv h) x

/-- The usual abelian-group structure on multiplicative `H²`. -/
instance : CommGroup (MHTwo G M) where
  mul := mul
  one := mk 1
  inv := inv
  mul_assoc := by
    intro x y z
    induction x, y, z using Quotient.inductionOn₃ with
    | _ a b c => exact congrArg mk (mul_assoc a b c)
  one_mul := by
    intro x
    induction x using Quotient.inductionOn with
    | _ a => exact congrArg mk (one_mul a)
  mul_one := by
    intro x
    induction x using Quotient.inductionOn with
    | _ a => exact congrArg mk (mul_one a)
  inv_mul_cancel := by
    intro x
    induction x using Quotient.inductionOn with
    | _ a => exact congrArg mk (inv_mul_cancel a)
  mul_comm := by
    intro x y
    induction x, y using Quotient.inductionOn₂ with
    | _ a b => exact congrArg mk (mul_comm a b)

@[simp]
theorem mk_mul (c d : NMCocycl₂ (G := G) (M := M)) :
    mk (c * d) = mk c * mk d :=
  rfl

@[simp]
theorem mk_pow (c : NMCocycl₂ (G := G) (M := M)) (n : ℕ) :
    mk (c ^ n) = mk c ^ n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pow_succ, pow_succ, mk_mul, ih]

/-- Equality in multiplicative `H²` is precisely cohomology by a
two-coboundary. -/
theorem mk_eq_iff (c d : NMCocycl₂ (G := G) (M := M)) :
    mk c = mk d ↔ IsCohomologous c d :=
  Quotient.eq''

/-- Every class has a normalized multiplicative representative. -/
theorem exists_mk_eq (x : MHTwo G M) :
    ∃ c : NMCocycl₂ (G := G) (M := M), mk c = x := by
  induction x using Quotient.inductionOn with
  | _ c => exact ⟨c, rfl⟩

end MHTwo

end Towers.CField.CProduca
