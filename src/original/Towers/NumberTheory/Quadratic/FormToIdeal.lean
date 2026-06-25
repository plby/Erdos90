import Towers.NumberTheory.Quadratic.ProperPrimitiveClasses
import Towers.NumberTheory.Quadratic.PrimeDecomposition
import Mathlib.LinearAlgebra.Basis.Basic

/-!
# Milne, Algebraic Number Theory, Theorem 4.29: forms to ideals

This file gives the concrete inverse construction underlying the form--ideal correspondence.
For a form `(a, b, c)` with `b = B + 2r` and discriminant `B^2 + 4A`, the associated ideal in
the quadratic order `Z[omega]`, `omega^2 = A + B omega`, is the lattice

`Z a + Z (omega + r)`.

We define it intrinsically by the congruence `a | re(z) - r im(z)`, prove that the discriminant
identity makes this lattice an ideal, and verify that its normalized norm form is the original
binary quadratic form.
-/

namespace Towers.NumberTheory.Milne

open scoped QuadraticAlgebra

noncomputable section

namespace BQForm

variable (A B a r c : ℤ)

/-- The lattice `Z a + Z (omega + r)` as an ideal of the quadratic order.  The relation
`r^2 + Br - A = ac` is precisely what makes the lattice stable under multiplication by
`omega`. -/
def latticeIdeal (hrel : r ^ 2 + B * r - A = a * c) :
    Ideal (QOrd A B) where
  carrier := {z | a ∣ z.re - r * z.im}
  zero_mem' := by simp
  add_mem' := by
    rintro x y ⟨u, hu⟩ ⟨v, hv⟩
    refine ⟨u + v, ?_⟩
    simp only [QuadraticAlgebra.re_add, QuadraticAlgebra.im_add]
    calc
      x.re + y.re - r * (x.im + y.im) =
          (x.re - r * x.im) + (y.re - r * y.im) := by ring
      _ = a * u + a * v := by rw [hu, hv]
      _ = a * (u + v) := by ring
  smul_mem' := by
    rintro z x ⟨u, hu⟩
    refine ⟨(z.re - r * z.im) * u - z.im * c * x.im, ?_⟩
    simp only [smul_eq_mul, QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul]
    calc
      z.re * x.re + A * z.im * x.im -
            r * (z.re * x.im + z.im * x.re + B * z.im * x.im) =
          (z.re - r * z.im) * (x.re - r * x.im) +
            z.im * x.im * (A - r ^ 2 - B * r) := by ring
      _ = (z.re - r * z.im) * (a * u) +
            z.im * x.im * (A - r ^ 2 - B * r) := by rw [hu]
      _ = (z.re - r * z.im) * (a * u) + z.im * x.im * (-(a * c)) := by
        congr 2
        nlinarith [hrel]
      _ = a * ((z.re - r * z.im) * u - z.im * c * x.im) := by ring

@[simp]
theorem mem_lattice_iff (hrel : r ^ 2 + B * r - A = a * c)
    (z : QOrd A B) :
    z ∈ latticeIdeal A B a r c hrel ↔ a ∣ z.re - r * z.im :=
  Iff.rfl

/-- The first evident lattice generator belongs to the form ideal. -/
theorem int_cast_lattice (hrel : r ^ 2 + B * r - A = a * c) :
    (a : QOrd A B) ∈ latticeIdeal A B a r c hrel := by
  simp [latticeIdeal]

/-- The second evident lattice generator belongs to the form ideal. -/
theorem omega_lattice_ideal (hrel : r ^ 2 + B * r - A = a * c) :
    (ω + (r : QOrd A B)) ∈ latticeIdeal A B a r c hrel := by
  simp [latticeIdeal]

/-- Membership in the form ideal is exactly membership in the `Z`-span of the two evident
generators. -/
theorem lattice_ideal (hrel : r ^ 2 + B * r - A = a * c)
    (z : QOrd A B) :
    z ∈ latticeIdeal A B a r c hrel ↔
      ∃ x y : ℤ,
        z = x • (a : QOrd A B) + y • (ω + (r : QOrd A B)) := by
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨x, z.im, ?_⟩
    apply QuadraticAlgebra.ext
    · simp only [QuadraticAlgebra.re_add, QuadraticAlgebra.re_smul,
        QuadraticAlgebra.re_intCast, QuadraticAlgebra.omega_re]
      dsimp
      linarith [hx]
    · simp
  · rintro ⟨x, y, rfl⟩
    refine ⟨x, ?_⟩
    simp
    ring

/-- If the leading coefficient is nonzero, so is the associated ideal. -/
theorem lattice_ne_bot (hrel : r ^ 2 + B * r - A = a * c) (ha : a ≠ 0) :
    latticeIdeal A B a r c hrel ≠ ⊥ := by
  intro hbot
  have hmem : (a : QOrd A B) ∈ (⊥ : Ideal (QOrd A B)) := by
    rw [← hbot]
    exact int_cast_lattice A B a r c hrel
  have hz : (a : QOrd A B) = 0 := (Submodule.mem_bot _).mp hmem
  exact ha (by
    simpa only [QuadraticAlgebra.re_intCast, QuadraticAlgebra.re_zero] using
      congrArg QuadraticAlgebra.re hz)

/-- Coordinate synthesis for the evident ordered generators of the form ideal. -/
def latticeSynthesis (hrel : r ^ 2 + B * r - A = a * c) :
    (Fin 2 → ℤ) →ₗ[ℤ] latticeIdeal A B a r c hrel where
  toFun x :=
    ⟨x 0 • (a : QOrd A B) +
        x 1 • (ω + (r : QOrd A B)),
      (lattice_ideal A B a r c hrel _).mpr ⟨x 0, x 1, rfl⟩⟩
  map_add' x y := by
    apply Subtype.ext
    change
      (x 0 + y 0) • (a : QOrd A B) +
          (x 1 + y 1) • (ω + (r : QOrd A B)) =
        (x 0 • (a : QOrd A B) + x 1 • (ω + (r : QOrd A B))) +
          (y 0 • (a : QOrd A B) + y 1 • (ω + (r : QOrd A B)))
    module
  map_smul' z x := by
    apply Subtype.ext
    change
      (z * x 0) • (a : QOrd A B) +
          (z * x 1) • (ω + (r : QOrd A B)) =
        z • (x 0 • (a : QOrd A B) + x 1 • (ω + (r : QOrd A B)))
    module

/-- The evident generators give an actual ordered `Z`-basis of the form ideal. -/
noncomputable def latticeBasis (hrel : r ^ 2 + B * r - A = a * c) (ha : a ≠ 0) :
    Module.Basis (Fin 2) ℤ (latticeIdeal A B a r c hrel) := by
  let f := latticeSynthesis A B a r c hrel
  have hf_inj : Function.Injective f := by
    intro x y hxy
    have him := congrArg (fun z : latticeIdeal A B a r c hrel ↦ (z : QOrd A B).im) hxy
    have hre := congrArg (fun z : latticeIdeal A B a r c hrel ↦ (z : QOrd A B).re) hxy
    simp only [f, latticeSynthesis, LinearMap.coe_mk, AddHom.coe_mk, QuadraticAlgebra.im_add,
      QuadraticAlgebra.im_smul, QuadraticAlgebra.im_intCast, QuadraticAlgebra.omega_im,
      zero_add, smul_eq_mul, mul_zero] at him
    simp only [f, latticeSynthesis, LinearMap.coe_mk, AddHom.coe_mk, QuadraticAlgebra.re_add,
      QuadraticAlgebra.re_smul, QuadraticAlgebra.re_intCast, QuadraticAlgebra.omega_re,
      zero_add, smul_eq_mul] at hre
    norm_num at him hre
    funext i
    fin_cases i
    · change x 0 = y 0
      rw [him] at hre
      exact mul_right_cancel₀ ha (add_right_cancel hre)
    · change x 1 = y 1
      exact him
  have hf_surj : Function.Surjective f := by
    intro z
    obtain ⟨x, y, hxy⟩ :=
      (lattice_ideal A B a r c hrel (z : QOrd A B)).mp z.property
    refine ⟨![x, y], ?_⟩
    apply Subtype.ext
    simpa [f, latticeSynthesis] using hxy.symm
  exact Module.Basis.ofEquivFun (LinearEquiv.ofBijective f ⟨hf_inj, hf_surj⟩).symm

@[simp]
theorem lattice_basis_coe (hrel : r ^ 2 + B * r - A = a * c) (ha : a ≠ 0) :
    ((latticeBasis A B a r c hrel ha 0 : latticeIdeal A B a r c hrel) :
        QOrd A B) = (a : QOrd A B) := by
  simp [latticeBasis, latticeSynthesis]

@[simp]
theorem lattice_one_coe (hrel : r ^ 2 + B * r - A = a * c) (ha : a ≠ 0) :
    ((latticeBasis A B a r c hrel ha 1 : latticeIdeal A B a r c hrel) :
        QOrd A B) = ω + (r : QOrd A B) := by
  simp [latticeBasis, latticeSynthesis]

variable {A B : ℤ} (Q : BQForm) (r : ℤ)

/-- The coefficient relation needed to construct the form ideal follows from the middle
coefficient and discriminant identities. -/
theorem lattice_relation (hb : Q.b = B + 2 * r)
    (hdisc : Q.discriminant = B ^ 2 + 4 * A) :
    r ^ 2 + B * r - A = Q.a * Q.c := by
  simp only [discriminant] at hdisc
  rw [hb] at hdisc
  nlinarith

/-- The ideal attached to a binary quadratic form after choosing the integer `r` with
`b = B + 2r`. -/
def toIdeal (hb : Q.b = B + 2 * r) (hdisc : Q.discriminant = B ^ 2 + 4 * A) :
    Ideal (QOrd A B) :=
  latticeIdeal A B Q.a r Q.c (Q.lattice_relation r hb hdisc)

/-- The evident ordered basis of the ideal attached to a form. -/
noncomputable def toIdealBasis (hb : Q.b = B + 2 * r)
    (hdisc : Q.discriminant = B ^ 2 + 4 * A) (ha : Q.a ≠ 0) :
    Module.Basis (Fin 2) ℤ (Q.toIdeal r hb hdisc) :=
  latticeBasis A B Q.a r Q.c (Q.lattice_relation r hb hdisc) ha

@[simp]
theorem mem_to_iff (hb : Q.b = B + 2 * r)
    (hdisc : Q.discriminant = B ^ 2 + 4 * A) (z : QOrd A B) :
    z ∈ Q.toIdeal r hb hdisc ↔ Q.a ∣ z.re - r * z.im :=
  Iff.rfl

/-- The associated ideal is nonzero for every form with nonzero leading coefficient. -/
theorem ideal_ne (hb : Q.b = B + 2 * r)
    (hdisc : Q.discriminant = B ^ 2 + 4 * A) (ha : Q.a ≠ 0) :
    Q.toIdeal r hb hdisc ≠ ⊥ :=
  lattice_ne_bot A B Q.a r Q.c (Q.lattice_relation r hb hdisc) ha

/-- The norm on the evident ordered lattice generators is the leading coefficient times the
given binary quadratic form. -/
theorem norm_evident_generators (hb : Q.b = B + 2 * r)
    (hdisc : Q.discriminant = B ^ 2 + 4 * A) (x y : ℤ) :
    QuadraticAlgebra.norm
        (x • (Q.a : QOrd A B) +
          y • (ω + (r : QOrd A B))) =
      Q.a * Q.eval x y := by
  have hrel := Q.lattice_relation r hb hdisc
  simp only [smul_eq_mul, QuadraticAlgebra.norm_def, QuadraticAlgebra.re_add,
    QuadraticAlgebra.re_smul, QuadraticAlgebra.re_intCast, QuadraticAlgebra.omega_re,
    QuadraticAlgebra.im_add, QuadraticAlgebra.im_smul, QuadraticAlgebra.im_intCast,
    QuadraticAlgebra.omega_im, zero_add, add_zero]
  simp only [eval]
  rw [hb]
  norm_num
  nlinarith

/-- Dividing the norm by the leading coefficient recovers the original form exactly. -/
theorem normal_evide_gener (hb : Q.b = B + 2 * r)
    (hdisc : Q.discriminant = B ^ 2 + 4 * A) (ha : Q.a ≠ 0) (x y : ℤ) :
    QuadraticAlgebra.norm
          (x • (Q.a : QOrd A B) +
            y • (ω + (r : QOrd A B))) /
        Q.a =
      Q.eval x y := by
  rw [Q.norm_evident_generators r hb hdisc x y]
  exact Int.mul_ediv_cancel_left _ ha

/-- In terms of the actual ordered basis of `toIdeal`, its normalized norm form is `Q`. -/
theorem normalized_ideal_basis (hb : Q.b = B + 2 * r)
    (hdisc : Q.discriminant = B ^ 2 + 4 * A) (ha : Q.a ≠ 0) (x y : ℤ) :
    QuadraticAlgebra.norm
          (x • ((Q.toIdealBasis r hb hdisc ha 0 : Q.toIdeal r hb hdisc) :
              QOrd A B) +
            y • ((Q.toIdealBasis r hb hdisc ha 1 : Q.toIdeal r hb hdisc) :
              QOrd A B)) /
        Q.a =
      Q.eval x y := by
  have h0 :
      ((Q.toIdealBasis r hb hdisc ha 0 : Q.toIdeal r hb hdisc) : QOrd A B) =
        (Q.a : QOrd A B) := by
    exact lattice_basis_coe A B Q.a r Q.c (Q.lattice_relation r hb hdisc) ha
  have h1 :
      ((Q.toIdealBasis r hb hdisc ha 1 : Q.toIdeal r hb hdisc) : QOrd A B) =
        ω + (r : QOrd A B) := by
    exact lattice_one_coe A B Q.a r Q.c (Q.lattice_relation r hb hdisc) ha
  rw [h0, h1]
  exact Q.normal_evide_gener r hb hdisc ha x y

end BQForm

end

end Towers.NumberTheory.Milne
