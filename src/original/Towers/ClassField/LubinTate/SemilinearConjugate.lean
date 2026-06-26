import Towers.ClassField.LubinTate.SemilinearIntertwiningError

/-!
# Class Field Theory, Chapter I, Proposition 3.10, Step 2

This file records the unconditional formal-series algebra in Step 2.  The
conjugated series is `sigma(theta) ∘ f ∘ theta⁻¹`; its constant and linear
coefficients are computed exactly, and the semilinear equation identifies the
extra factor which appears after applying `sigma` to the inverse series.
-/

namespace Towers.CField.LTate

open PowerSeries

noncomputable section

/-- The series called `h = sigma(theta) ∘ f ∘ theta⁻¹` in Step 2 of the
proof of Proposition 3.10. -/
def semilinearConjugate
    {R : Type*} [CommRing R] (sigma : R →+* R)
    (theta inverseTheta f : PowerSeries R) : PowerSeries R :=
  subst (subst inverseTheta f) (PowerSeries.map sigma theta)

theorem semilinear_constant_coeff
    {R : Type*} [CommRing R] (sigma : R →+* R)
    {theta inverseTheta f : PowerSeries R}
    (htheta0 : constantCoeff theta = 0)
    (hinverse0 : constantCoeff inverseTheta = 0)
    (hf0 : constantCoeff f = 0) :
    constantCoeff (semilinearConjugate sigma theta inverseTheta f) = 0 := by
  have hinner : constantCoeff (subst inverseTheta f) = 0 :=
    constantCoeff_subst_eq_zero hinverse0 f hf0
  apply constantCoeff_subst_eq_zero hinner
  rw [← coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
    coeff_zero_eq_constantCoeff_apply, htheta0, map_zero]

/-- The linear coefficient of `sigma(theta) ∘ f ∘ theta⁻¹` is the product
of the three linear coefficients. -/
theorem semilinear_conjugate_one
    {R : Type*} [CommRing R] (sigma : R →+* R)
    {theta inverseTheta f : PowerSeries R}
    (hinverse0 : constantCoeff inverseTheta = 0)
    (hf0 : constantCoeff f = 0) :
    coeff 1 (semilinearConjugate sigma theta inverseTheta f) =
      sigma (coeff 1 theta) * (coeff 1 f * coeff 1 inverseTheta) := by
  rw [semilinearConjugate,
    Towers.CField.FGroups.coeff_one_subst
      (constantCoeff_subst_eq_zero hinverse0 f hf0),
    PowerSeries.coeff_map,
    Towers.CField.FGroups.coeff_one_subst hinverse0]

/-- The linear coefficient of a compositional inverse is the inverse of the
original linear coefficient. -/
theorem coeff_subst_x
    {R : Type*} [CommRing R] {theta inverseTheta : PowerSeries R}
    (epsilon : Rˣ) (htheta1 : coeff 1 theta = (epsilon : R))
    (hinverse0 : constantCoeff inverseTheta = 0)
    (hinverse : subst inverseTheta theta = X) :
    coeff 1 inverseTheta = ((epsilon⁻¹ : Rˣ) : R) := by
  have hlinear := congrArg (coeff (R := R) 1) hinverse
  rw [Towers.CField.FGroups.coeff_one_subst hinverse0,
    coeff_one_X, htheta1] at hlinear
  calc
    coeff 1 inverseTheta =
        ((epsilon⁻¹ : Rˣ) : R) *
          ((epsilon : R) * coeff 1 inverseTheta) := by
            rw [← mul_assoc, epsilon.inv_mul, one_mul]
    _ = ((epsilon⁻¹ : Rˣ) : R) := by rw [hlinear, mul_one]

/-- Milne's linear-term calculation
`sigma(epsilon) * pi * epsilon⁻¹ = pi * u`. -/
theorem semilinear_conjugate_coeff
    {R : Type*} [CommRing R] (sigma : R →+* R)
    {theta inverseTheta f : PowerSeries R} (epsilon w : Rˣ) (pi : R)
    (htheta1 : coeff 1 theta = (epsilon : R))
    (hinverse0 : constantCoeff inverseTheta = 0)
    (hinverse : subst inverseTheta theta = X)
    (hf0 : constantCoeff f = 0) (hf1 : coeff 1 f = pi)
    (hepsilon : sigma (epsilon : R) = ((epsilon * w : Rˣ) : R)) :
    coeff 1 (semilinearConjugate sigma theta inverseTheta f) =
      pi * (w : R) := by
  rw [semilinear_conjugate_one sigma hinverse0 hf0, htheta1, hf1,
    coeff_subst_x epsilon htheta1 hinverse0 hinverse,
    hepsilon]
  change ((epsilon : R) * (w : R)) *
      (pi * ((epsilon⁻¹ : Rˣ) : R)) = pi * (w : R)
  calc
    ((epsilon : R) * (w : R)) *
          (pi * ((epsilon⁻¹ : Rˣ) : R)) =
        ((epsilon : R) * ((epsilon⁻¹ : Rˣ) : R)) *
          (pi * (w : R)) := by ac_rfl
    _ = pi * (w : R) := by rw [epsilon.mul_inv, one_mul]

/-- Applying `sigma` to a compositional inverse and then composing with the
semilinear factor `u` recovers the original inverse.  This is the middle
identity used in Milne's proof that `sigma(h) = h`. -/
theorem subst_semilinear_factor
    {R : Type*} [CommRing R] (sigma : R →+* R)
    {theta inverseTheta u : PowerSeries R}
    (hinverse0 : constantCoeff inverseTheta = 0)
    (hu0 : constantCoeff u = 0)
    (hinverse : subst inverseTheta theta = X)
    (hsemilinear : PowerSeries.map sigma theta = subst u theta) :
    subst (PowerSeries.map sigma inverseTheta) u = inverseTheta := by
  have hmapInverse0 :
      constantCoeff (PowerSeries.map sigma inverseTheta) = 0 := by
    rw [← coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
      coeff_zero_eq_constantCoeff_apply, hinverse0, map_zero]
  have hmappedInverse :
      subst (PowerSeries.map sigma inverseTheta)
          (PowerSeries.map sigma theta) = X := by
    calc
      subst (PowerSeries.map sigma inverseTheta)
          (PowerSeries.map sigma theta) =
        PowerSeries.map sigma (subst inverseTheta theta) :=
          (PowerSeries.map_subst (h := sigma)
            (PowerSeries.HasSubst.of_constantCoeff_zero' hinverse0) theta).symm
      _ = PowerSeries.map sigma X := by rw [hinverse]
      _ = X := PowerSeries.map_X sigma
  have hcandidate0 :
      constantCoeff (subst (PowerSeries.map sigma inverseTheta) u) = 0 :=
    constantCoeff_subst_eq_zero hmapInverse0 u hu0
  apply Eq.symm
  apply Towers.CField.FGroups.subst_inverse_unique
    hinverse0 hcandidate0 hinverse
  calc
    subst (subst (PowerSeries.map sigma inverseTheta) u) theta =
        subst (PowerSeries.map sigma inverseTheta) (subst u theta) :=
      (subst_comp_subst_apply
        (PowerSeries.HasSubst.of_constantCoeff_zero' hu0)
        (PowerSeries.HasSubst.of_constantCoeff_zero' hmapInverse0) theta).symm
    _ = subst (PowerSeries.map sigma inverseTheta)
        (PowerSeries.map sigma theta) := by rw [← hsemilinear]
    _ = X := hmappedInverse

/-- The two parenthesizations of the threefold conjugating composition agree. -/
theorem semilinear_conjugate_nested
    {R : Type*} [CommRing R] (sigma : R →+* R)
    {theta inverseTheta f : PowerSeries R}
    (hinverse0 : constantCoeff inverseTheta = 0)
    (hf0 : constantCoeff f = 0) :
    semilinearConjugate sigma theta inverseTheta f =
      subst inverseTheta (subst f (PowerSeries.map sigma theta)) := by
  exact (subst_comp_subst_apply
    (PowerSeries.HasSubst.of_constantCoeff_zero' hf0)
    (PowerSeries.HasSubst.of_constantCoeff_zero' hinverse0)
    (PowerSeries.map sigma theta)).symm

/-- The formal-series fixedness calculation in Step 2: the conjugated series
`h = sigma(theta) ∘ f ∘ theta⁻¹` is fixed by `sigma`.  Descent of its
coefficients from the completed unramified valuation ring to the base ring is
the separate arithmetic input in Milne's proof. -/
theorem semilinear_conjugate_self
    {R : Type*} [CommRing R] (sigma : R →+* R)
    {theta inverseTheta f u : PowerSeries R}
    (hinverse0 : constantCoeff inverseTheta = 0)
    (hf0 : constantCoeff f = 0)
    (hu0 : constantCoeff u = 0)
    (hinverse : subst inverseTheta theta = X)
    (hsemilinear : PowerSeries.map sigma theta = subst u theta)
    (hfixf : PowerSeries.map sigma f = f)
    (hfixu : PowerSeries.map sigma u = u)
    (hcomm : subst f u = subst u f) :
    PowerSeries.map sigma
        (semilinearConjugate sigma theta inverseTheta f) =
      semilinearConjugate sigma theta inverseTheta f := by
  have hmapInverse0 :
      constantCoeff (PowerSeries.map sigma inverseTheta) = 0 := by
    rw [← coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
      coeff_zero_eq_constantCoeff_apply, hinverse0, map_zero]
  have htwisted : subst (PowerSeries.map sigma inverseTheta) u = inverseTheta :=
    subst_semilinear_factor
      sigma hinverse0 hu0 hinverse hsemilinear
  have hsigma2 :
      PowerSeries.map sigma (PowerSeries.map sigma theta) =
        subst u (PowerSeries.map sigma theta) := by
    calc
      PowerSeries.map sigma (PowerSeries.map sigma theta) =
          PowerSeries.map sigma (subst u theta) := by rw [hsemilinear]
      _ = subst (PowerSeries.map sigma u)
          (PowerSeries.map sigma theta) := by
        simpa using PowerSeries.map_subst (h := sigma)
          (PowerSeries.HasSubst.of_constantCoeff_zero' hu0) theta
      _ = subst u (PowerSeries.map sigma theta) := by rw [hfixu]
  have hmapInner :
      PowerSeries.map sigma
          (subst f (PowerSeries.map sigma theta)) =
        subst f (subst u (PowerSeries.map sigma theta)) := by
    calc
      PowerSeries.map sigma
          (subst f (PowerSeries.map sigma theta)) =
          subst (PowerSeries.map sigma f)
            (PowerSeries.map sigma (PowerSeries.map sigma theta)) := by
        simpa using PowerSeries.map_subst (h := sigma)
          (PowerSeries.HasSubst.of_constantCoeff_zero' hf0)
          (PowerSeries.map sigma theta)
      _ = subst f (subst u (PowerSeries.map sigma theta)) := by
        rw [hfixf, hsigma2]
  rw [semilinear_conjugate_nested sigma hinverse0 hf0]
  calc
    PowerSeries.map sigma
        (subst inverseTheta
          (subst f (PowerSeries.map sigma theta))) =
        subst (PowerSeries.map sigma inverseTheta)
          (PowerSeries.map sigma
            (subst f (PowerSeries.map sigma theta))) := by
      simpa using PowerSeries.map_subst (h := sigma)
        (PowerSeries.HasSubst.of_constantCoeff_zero' hinverse0)
        (subst f (PowerSeries.map sigma theta))
    _ = subst (PowerSeries.map sigma inverseTheta)
          (subst f (subst u (PowerSeries.map sigma theta))) := by
      rw [hmapInner]
    _ = subst (PowerSeries.map sigma inverseTheta)
          (subst u (subst f (PowerSeries.map sigma theta))) := by
      congr 1
      rw [subst_comp_subst_apply
        (PowerSeries.HasSubst.of_constantCoeff_zero' hu0)
        (PowerSeries.HasSubst.of_constantCoeff_zero' hf0)]
      rw [subst_comp_subst_apply
        (PowerSeries.HasSubst.of_constantCoeff_zero' hf0)
        (PowerSeries.HasSubst.of_constantCoeff_zero' hu0)]
      rw [hcomm]
    _ = subst (subst (PowerSeries.map sigma inverseTheta) u)
          (subst f (PowerSeries.map sigma theta)) := by
      rw [subst_comp_subst_apply
        (PowerSeries.HasSubst.of_constantCoeff_zero' hu0)
        (PowerSeries.HasSubst.of_constantCoeff_zero' hmapInverse0)]
    _ = subst inverseTheta
          (subst f (PowerSeries.map sigma theta)) := by rw [htwisted]

/-- Postcomposition by a Frobenius-fixed series preserves the semilinear
functional equation.  This is the first property of Milne's replacement
`theta' = [1]_{g,h} ∘ theta`. -/
theorem subst_semilinear_fixed
    {R : Type*} [CommRing R] (sigma : R →+* R)
    {i theta u : PowerSeries R}
    (htheta0 : constantCoeff theta = 0)
    (hu0 : constantCoeff u = 0)
    (hsemilinear : PowerSeries.map sigma theta = subst u theta)
    (hfixi : PowerSeries.map sigma i = i) :
    PowerSeries.map sigma (subst theta i) = subst u (subst theta i) := by
  calc
    PowerSeries.map sigma (subst theta i) =
        subst (PowerSeries.map sigma theta) (PowerSeries.map sigma i) := by
      simpa using PowerSeries.map_subst (h := sigma)
        (PowerSeries.HasSubst.of_constantCoeff_zero' htheta0) i
    _ = subst (subst u theta) i := by rw [hsemilinear, hfixi]
    _ = subst u (subst theta i) :=
      (subst_comp_subst_apply
        (PowerSeries.HasSubst.of_constantCoeff_zero' htheta0)
        (PowerSeries.HasSubst.of_constantCoeff_zero' hu0) i).symm

/-- Postcomposition by a series with linear coefficient one preserves the
linear coefficient of `theta`. -/
theorem one_subst
    {R : Type*} [CommRing R] {i theta : PowerSeries R}
    (htheta0 : constantCoeff theta = 0)
    (hi1 : coeff 1 i = 1) :
    coeff 1 (subst theta i) = coeff 1 theta := by
  rw [Towers.CField.FGroups.coeff_one_subst htheta0,
    hi1, one_mul]

/-- The expected inverse of `i ∘ theta` is `theta⁻¹ ∘ j`. -/
theorem subst_adjusted_theta
    {R : Type*} [CommRing R]
    {i j theta inverseTheta : PowerSeries R}
    (htheta0 : constantCoeff theta = 0)
    (hinverse0 : constantCoeff inverseTheta = 0)
    (hj0 : constantCoeff j = 0)
    (hthetaInverse : subst inverseTheta theta = X)
    (hij : subst j i = X) :
    subst (subst j inverseTheta) (subst theta i) = X := by
  calc
    subst (subst j inverseTheta) (subst theta i) =
        subst j (subst inverseTheta (subst theta i)) :=
      (subst_comp_subst_apply
        (PowerSeries.HasSubst.of_constantCoeff_zero' hinverse0)
        (PowerSeries.HasSubst.of_constantCoeff_zero' hj0)
        (subst theta i)).symm
    _ = subst j (subst (subst inverseTheta theta) i) := by
      rw [subst_comp_subst_apply
        (PowerSeries.HasSubst.of_constantCoeff_zero' htheta0)
        (PowerSeries.HasSubst.of_constantCoeff_zero' hinverse0)]
    _ = subst j i := by
      rw [hthetaInverse]
      have hX : subst X i = i := by
        rw [← PowerSeries.map_algebraMap_eq_subst_X (R := R) (S := R) i]
        change PowerSeries.map (RingHom.id R) i = i
        rw [PowerSeries.map_id]
        rfl
      rw [hX]
    _ = X := hij

/-- Conjugating after replacing `theta` by `i ∘ theta` replaces the old
conjugate `h` by `i ∘ h ∘ j`, where `j` is the chosen inverse of `i`. -/
theorem semilinear_conjugate_subst
    {R : Type*} [CommRing R] (sigma : R →+* R)
    {i j theta inverseTheta f : PowerSeries R}
    (htheta0 : constantCoeff theta = 0)
    (hinverse0 : constantCoeff inverseTheta = 0)
    (hj0 : constantCoeff j = 0)
    (hf0 : constantCoeff f = 0)
    (hfixi : PowerSeries.map sigma i = i) :
    semilinearConjugate sigma (subst theta i) (subst j inverseTheta) f =
      subst j (subst (semilinearConjugate sigma theta inverseTheta f) i) := by
  have hadjustedInverse0 : constantCoeff (subst j inverseTheta) = 0 :=
    constantCoeff_subst_eq_zero hj0 inverseTheta hinverse0
  have hmapAdjusted :
      PowerSeries.map sigma (subst theta i) =
        subst (PowerSeries.map sigma theta) i := by
    calc
      PowerSeries.map sigma (subst theta i) =
          subst (PowerSeries.map sigma theta) (PowerSeries.map sigma i) := by
        simpa using PowerSeries.map_subst (h := sigma)
          (PowerSeries.HasSubst.of_constantCoeff_zero' htheta0) i
      _ = subst (PowerSeries.map sigma theta) i := by rw [hfixi]
  rw [semilinear_conjugate_nested sigma hadjustedInverse0 hf0,
    hmapAdjusted]
  calc
    subst (subst j inverseTheta)
        (subst f (subst (PowerSeries.map sigma theta) i)) =
      subst (subst j inverseTheta)
        (subst (subst f (PowerSeries.map sigma theta)) i) := by
          rw [subst_comp_subst_apply
            (PowerSeries.HasSubst.of_constantCoeff_zero'
              (by
                rw [← coeff_zero_eq_constantCoeff_apply,
                  PowerSeries.coeff_map, coeff_zero_eq_constantCoeff_apply,
                  htheta0, map_zero]))
            (PowerSeries.HasSubst.of_constantCoeff_zero' hf0)]
    _ = subst j
        (subst inverseTheta
          (subst (subst f (PowerSeries.map sigma theta)) i)) :=
      (subst_comp_subst_apply
        (PowerSeries.HasSubst.of_constantCoeff_zero' hinverse0)
        (PowerSeries.HasSubst.of_constantCoeff_zero' hj0)
        (subst (subst f (PowerSeries.map sigma theta)) i)).symm
    _ = subst j
        (subst (subst inverseTheta
          (subst f (PowerSeries.map sigma theta))) i) := by
      congr 1
      rw [subst_comp_subst_apply
        (PowerSeries.HasSubst.of_constantCoeff_zero'
          (constantCoeff_subst_eq_zero hf0
            (PowerSeries.map sigma theta)
            (by
              rw [← coeff_zero_eq_constantCoeff_apply,
                PowerSeries.coeff_map, coeff_zero_eq_constantCoeff_apply,
                htheta0, map_zero])))
        (PowerSeries.HasSubst.of_constantCoeff_zero' hinverse0)]
    _ = subst j
        (subst (semilinearConjugate sigma theta inverseTheta f) i) := by
      rw [semilinear_conjugate_nested sigma hinverse0 hf0]

/-- The abstract final adjustment in Step 2.  If `i` intertwines the old
conjugate `h` with `g`, and `j` is its right compositional inverse, then the
adjusted `theta` has conjugate exactly `g`. -/
theorem semilinear_subst_intertwines
    {R : Type*} [CommRing R] (sigma : R →+* R)
    {i j theta inverseTheta f g : PowerSeries R}
    (hi0 : constantCoeff i = 0)
    (hj0 : constantCoeff j = 0)
    (htheta0 : constantCoeff theta = 0)
    (hinverse0 : constantCoeff inverseTheta = 0)
    (hf0 : constantCoeff f = 0)
    (hfixi : PowerSeries.map sigma i = i)
    (hij : subst j i = X)
    (hintertwines :
      subst i g = subst (semilinearConjugate sigma theta inverseTheta f) i) :
    semilinearConjugate sigma (subst theta i) (subst j inverseTheta) f = g := by
  rw [semilinear_conjugate_subst sigma htheta0 hinverse0 hj0 hf0 hfixi,
    ← hintertwines]
  rw [subst_comp_subst_apply
    (PowerSeries.HasSubst.of_constantCoeff_zero' hi0)
    (PowerSeries.HasSubst.of_constantCoeff_zero' hj0)]
  rw [hij]
  exact (PowerSeries.map_algebraMap_eq_subst_X
    (R := R) (S := R) g).symm

/-- The subring of coefficients fixed by a ring endomorphism.  In Milne's
application this is the base valuation ring inside the completed maximal
unramified extension. -/
def ringFixedSubring {R : Type*} [CommRing R]
    (sigma : R →+* R) : Subring R where
  carrier := {x | sigma x = x}
  zero_mem' := map_zero sigma
  one_mem' := map_one sigma
  add_mem' := by
    intro x y hx hy
    change sigma x = x at hx
    change sigma y = y at hy
    change sigma (x + y) = x + y
    rw [map_add, hx, hy]
  mul_mem' := by
    intro x y hx hy
    change sigma x = x at hx
    change sigma y = y at hy
    change sigma (x * y) = x * y
    rw [map_mul, hx, hy]
  neg_mem' := by
    intro x hx
    change sigma x = x at hx
    change sigma (-x) = -x
    rw [map_neg, hx]

@[simp]
theorem ring_fixed_subring
    {R : Type*} [CommRing R] (sigma : R →+* R) (x : R) :
    x ∈ ringFixedSubring sigma ↔ sigma x = x :=
  Iff.rfl

/-- A power series is fixed coefficientwise exactly when all of its
coefficients belong to the fixed subring. -/
theorem self_coeff_subring
    {R : Type*} [CommRing R] (sigma : R →+* R) (f : PowerSeries R) :
    PowerSeries.map sigma f = f ↔
      ∀ n, coeff n f ∈ ringFixedSubring sigma := by
  constructor
  · intro h n
    have hn := congrArg (coeff (R := R) n) h
    simpa only [PowerSeries.coeff_map] using hn
  · intro h
    apply PowerSeries.ext
    intro n
    rw [PowerSeries.coeff_map]
    exact h n

/-- Consequently every coefficient of Milne's Step 2 conjugate lies in the
Frobenius-fixed coefficient subring. -/
theorem semilinear_conjugate_subring
    {R : Type*} [CommRing R] (sigma : R →+* R)
    {theta inverseTheta f u : PowerSeries R}
    (hinverse0 : constantCoeff inverseTheta = 0)
    (hf0 : constantCoeff f = 0)
    (hu0 : constantCoeff u = 0)
    (hinverse : subst inverseTheta theta = X)
    (hsemilinear : PowerSeries.map sigma theta = subst u theta)
    (hfixf : PowerSeries.map sigma f = f)
    (hfixu : PowerSeries.map sigma u = u)
    (hcomm : subst f u = subst u f) :
    ∀ n, coeff n (semilinearConjugate sigma theta inverseTheta f) ∈
      ringFixedSubring sigma :=
  (self_coeff_subring sigma _).mp
    (semilinear_conjugate_self sigma hinverse0 hf0 hu0 hinverse
      hsemilinear hfixf hfixu hcomm)

end

end Towers.CField.LTate
