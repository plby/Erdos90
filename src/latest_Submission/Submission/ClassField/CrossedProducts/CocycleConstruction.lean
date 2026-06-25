import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree


/-!
# Chapter IV, Section 3: factor sets and 2-cocycles

This file formalizes the associativity calculation following Corollary IV.3.10.
If representatives `e_g` commute past scalars according to the action of `g`
and their products are measured by a factor set `φ`, then `φ` satisfies the
multiplicative 2-cocycle identity.
-/

namespace Submission.CField.CProduca

open groupCohomology

variable {G M U : Type*} [Group G] [CommGroup M] [Group U]
  [MulAction G M]

/-- The abstract form of equations (39) and (40) in Milne.  The injective map
`q` regards the coefficient group as scalar units in the ambient algebra. -/
structure FSData where
  q : M →* U
  q_injective : Function.Injective q
  representative : G → U
  factorSet : G × G → M
  commute_scalar : ∀ (g : G) (a : M),
    representative g * q a = q (g • a) * representative g
  mul_representative : ∀ g h : G,
    representative g * representative h =
      q (factorSet (g, h)) * representative (g * h)

namespace FSData

/-- Associativity of the ambient group gives the factor-set identity

`phi(gh,j) * phi(g,h) = g • phi(h,j) * phi(g,hj)`.

Thus the factors attached to representatives form a multiplicative
2-cocycle. -/
theorem isMulCocycle₂ (d : FSData (G := G) (M := M) (U := U)) :
    IsMulCocycle₂ d.factorSet := by
  intro g h j
  apply d.q_injective
  simp only [map_mul]
  have hleft :
      (d.representative g * d.representative h) * d.representative j =
        (d.q (d.factorSet (g, h)) * d.q (d.factorSet (g * h, j))) *
          d.representative (g * h * j) := by
    calc
      (d.representative g * d.representative h) * d.representative j =
          (d.q (d.factorSet (g, h)) * d.representative (g * h)) *
            d.representative j := by rw [d.mul_representative]
      _ = d.q (d.factorSet (g, h)) *
            (d.representative (g * h) * d.representative j) := by
              rw [mul_assoc]
      _ = d.q (d.factorSet (g, h)) *
            (d.q (d.factorSet (g * h, j)) * d.representative ((g * h) * j)) := by
              rw [d.mul_representative]
      _ = (d.q (d.factorSet (g, h)) * d.q (d.factorSet (g * h, j))) *
            d.representative (g * h * j) := by rw [← mul_assoc]
  have hright :
      d.representative g * (d.representative h * d.representative j) =
        (d.q (g • d.factorSet (h, j)) * d.q (d.factorSet (g, h * j))) *
          d.representative (g * (h * j)) := by
    calc
      d.representative g * (d.representative h * d.representative j) =
          d.representative g *
            (d.q (d.factorSet (h, j)) * d.representative (h * j)) := by
              rw [d.mul_representative]
      _ = (d.representative g * d.q (d.factorSet (h, j))) *
            d.representative (h * j) := by rw [mul_assoc]
      _ = (d.q (g • d.factorSet (h, j)) * d.representative g) *
            d.representative (h * j) := by rw [d.commute_scalar]
      _ = d.q (g • d.factorSet (h, j)) *
            (d.representative g * d.representative (h * j)) := by rw [mul_assoc]
      _ = d.q (g • d.factorSet (h, j)) *
            (d.q (d.factorSet (g, h * j)) * d.representative (g * (h * j))) := by
              rw [d.mul_representative]
      _ = (d.q (g • d.factorSet (h, j)) * d.q (d.factorSet (g, h * j))) *
            d.representative (g * (h * j)) := by rw [mul_assoc]
  have hcoeff :
      d.q (d.factorSet (g, h)) * d.q (d.factorSet (g * h, j)) =
        d.q (g • d.factorSet (h, j)) * d.q (d.factorSet (g, h * j)) := by
    apply mul_right_cancel
    rw [← hleft, mul_assoc, hright]
    simp only [mul_assoc]
  calc
    d.q (d.factorSet (g * h, j)) * d.q (d.factorSet (g, h)) =
        d.q (d.factorSet (g, h)) * d.q (d.factorSet (g * h, j)) := by
          rw [← map_mul, ← map_mul, mul_comm]
    _ = d.q (g • d.factorSet (h, j)) * d.q (d.factorSet (g, h * j)) := hcoeff

/-- The factor set obtained after replacing `e_g` by `c_g e_g`. -/
def rescaledFactorSet (d : FSData (G := G) (M := M) (U := U))
    (c : G → M) (p : G × G) : M :=
  (p.1 • c p.2 / c (p.1 * p.2) * c p.1) * d.factorSet p

/-- Rescaling representatives by coefficient-group elements preserves the
factor-set equations. -/
def rescale (d : FSData (G := G) (M := M) (U := U)) (c : G → M) :
    FSData (G := G) (M := M) (U := U) where
  q := d.q
  q_injective := d.q_injective
  representative g := d.q (c g) * d.representative g
  factorSet := d.rescaledFactorSet c
  commute_scalar g a := by
    calc
      (d.q (c g) * d.representative g) * d.q a =
          d.q (c g) * (d.representative g * d.q a) := by rw [mul_assoc]
      _ = d.q (c g) * (d.q (g • a) * d.representative g) := by
        rw [d.commute_scalar]
      _ = (d.q (c g) * d.q (g • a)) * d.representative g := by
        rw [← mul_assoc]
      _ = (d.q (g • a) * d.q (c g)) * d.representative g := by
        rw [← map_mul, ← map_mul, mul_comm]
      _ = d.q (g • a) * (d.q (c g) * d.representative g) := by rw [mul_assoc]
  mul_representative g h := by
    have hcoeff :
        (d.q (c g) * d.q (g • c h)) * d.q (d.factorSet (g, h)) =
          d.q (d.rescaledFactorSet c (g, h)) * d.q (c (g * h)) := by
      rw [← map_mul, ← map_mul, ← map_mul]
      congr 1
      simp only [rescaledFactorSet]
      simp only [mul_assoc, div_eq_mul_inv, mul_comm, mul_left_comm, mul_right_inj]
      symm
      calc
        c (g * h) *
            (g • c h * ((c (g * h))⁻¹ * d.factorSet (g, h))) =
            g • c h *
              (c (g * h) * ((c (g * h))⁻¹ * d.factorSet (g, h))) := by
                ac_rfl
        _ = g • c h * d.factorSet (g, h) := by simp [← mul_assoc]
    calc
      (d.q (c g) * d.representative g) *
          (d.q (c h) * d.representative h) =
        d.q (c g) *
          ((d.representative g * d.q (c h)) * d.representative h) := by
            simp only [mul_assoc]
      _ = d.q (c g) *
          ((d.q (g • c h) * d.representative g) * d.representative h) := by
            rw [d.commute_scalar]
      _ = (d.q (c g) * d.q (g • c h)) *
          (d.representative g * d.representative h) := by
            simp only [mul_assoc]
      _ = (d.q (c g) * d.q (g • c h)) *
          (d.q (d.factorSet (g, h)) * d.representative (g * h)) := by
            rw [d.mul_representative]
      _ = ((d.q (c g) * d.q (g • c h)) * d.q (d.factorSet (g, h))) *
          d.representative (g * h) := by rw [← mul_assoc]
      _ = (d.q (d.rescaledFactorSet c (g, h)) * d.q (c (g * h))) *
          d.representative (g * h) := by rw [hcoeff]
      _ = d.q (d.rescaledFactorSet c (g, h)) *
          (d.q (c (g * h)) * d.representative (g * h)) := by rw [mul_assoc]

/-- Consequently, changing representatives changes the factor set by a
multiplicative 2-coboundary. -/
theorem rescaled_div_coboundary₂
    (d : FSData (G := G) (M := M) (U := U)) (c : G → M) :
    IsMulCoboundary₂ (fun p ↦ d.rescaledFactorSet c p / d.factorSet p) := by
  refine ⟨c, ?_⟩
  intro g h
  simp only [rescaledFactorSet]
  simp [div_eq_mul_inv, mul_assoc, mul_comm]

end FSData

end Submission.CField.CProduca
