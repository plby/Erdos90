import Towers.NumberTheory.ClassGroup.NarrowClassGroup
import Towers.NumberTheory.Quadratic.IdealFormMap

/-!
# Signs and total positivity in a quadratic field

If an element of a quadratic field has positive norm, its values at the two real embeddings
have the same sign.  Thus either the element or its negative is totally positive.  This is the
sign fact needed to upgrade the principal scaling relation in Theorem 4.29 from the ordinary
class group to the narrow class group.
-/

namespace Towers.NumberTheory.Milne

open Towers.NumberTheory

noncomputable section

namespace QTPositi

variable {d : ℤ}

private theorem map_apply (x : QFModel d)
    (phi : QFModel d →+* ℝ) :
    phi x = (x.re : ℝ) + (x.im : ℝ) * phi QuadraticAlgebra.omega := by
  rcases x with ⟨xr, xi⟩
  simp [QuadraticAlgebra.mk_eq_add_smul_omega, Algebra.smul_def]

private theorem map_omega_sq (phi : QFModel d →+* ℝ) :
    (phi QuadraticAlgebra.omega) ^ 2 = (d : ℝ) := by
  have homega :
      (QuadraticAlgebra.omega : QFModel d) ^ 2 = (d : QFModel d) := by
    apply QuadraticAlgebra.ext <;>
      norm_num [pow_two, QuadraticAlgebra.omega_mul_omega_eq_mk]
  calc
    (phi QuadraticAlgebra.omega) ^ 2 = phi (QuadraticAlgebra.omega ^ 2) := by rw [map_pow]
    _ = phi (d : QFModel d) := by rw [homega]
    _ = (d : ℝ) := by simp

private theorem values_mul_pos
    [Fact (∀ r : ℚ, r ^ 2 ≠ (d : ℚ) + 0 * r)]
    (x : QFModel d) (hx : x ≠ 0)
    (hnorm : 0 < Algebra.norm ℚ x)
    (phi psi : QFModel d →+* ℝ) :
    0 < phi x * psi x := by
  have homega := eq_or_eq_neg_of_sq_eq_sq
    (phi QuadraticAlgebra.omega) (psi QuadraticAlgebra.omega)
    ((map_omega_sq phi).trans (map_omega_sq psi).symm)
  rcases homega with homega | homega
  · have hvalues : phi x = psi x := by
      rw [map_apply x phi, map_apply x psi, homega]
    rw [← hvalues]
    simpa [pow_two] using sq_pos_of_ne_zero (show phi x ≠ 0 by
      intro hzero
      apply hx
      apply phi.injective
      simpa using hzero)
  · have hprod :
        phi x * psi x = (Algebra.norm ℚ x : ℝ) := by
      have hroot := map_omega_sq phi
      have hnormformula :
          (Algebra.norm ℚ x : ℝ) =
            (x.re : ℝ) ^ 2 - (d : ℝ) * (x.im : ℝ) ^ 2 := by
        let canonical : Algebra ℚ (QFModel d) :=
          @DivisionRing.toRatAlgebra (QFModel d) inferInstance inferInstance
        change ((@Algebra.norm ℚ (QFModel d) inferInstance inferInstance
          canonical x : ℚ) : ℝ) = _
        have hRing :
            (QuadraticAlgebra.instField : Field (QFModel d)).toDivisionRing.toRing =
              (QuadraticAlgebra.instCommRing : CommRing (QFModel d)).toRing := by
          rfl
        cases hRing
        have hAlgebra : canonical = QuadraticAlgebra.instAlgebra := Subsingleton.elim _ _
        rw [hAlgebra, QIMap.norm_quadratic_model]
        push_cast
        ring
      have hpsi : psi QuadraticAlgebra.omega = -phi QuadraticAlgebra.omega := by
        linarith
      rw [map_apply x phi, map_apply x psi, hpsi]
      calc
        ((x.re : ℝ) + (x.im : ℝ) * phi QuadraticAlgebra.omega) *
              ((x.re : ℝ) + (x.im : ℝ) * -phi QuadraticAlgebra.omega) =
            (x.re : ℝ) ^ 2 - (x.im : ℝ) ^ 2 *
              (phi QuadraticAlgebra.omega) ^ 2 := by ring
        _ = (x.re : ℝ) ^ 2 - (d : ℝ) * (x.im : ℝ) ^ 2 := by
          rw [hroot]
          ring
        _ = (Algebra.norm ℚ x : ℝ) := hnormformula.symm
    rw [hprod]
    exact_mod_cast hnorm

/-- An element of positive norm in a quadratic field has one global sign at all real
embeddings: either it or its negative is totally positive.  If there are no real embeddings,
the first alternative holds vacuously. -/
theorem totally_or_neg
    [Fact (∀ r : ℚ, r ^ 2 ≠ (d : ℚ) + 0 * r)]
    [Module.Finite ℚ (QFModel d)]
    [NumberField (QFModel d)]
    (x : QFModel d) (hx : x ≠ 0)
    (hnorm : 0 < Algebra.norm ℚ x) :
    ITPos (QFModel d) x ∨
      ITPos (QFModel d) (-x) := by
  classical
  cases isEmpty_or_nonempty (QFModel d →+* ℝ) with
  | inl hempty =>
      left
      intro phi
      exact isEmptyElim phi
  | inr hnonempty =>
      let phi0 : QFModel d →+* ℝ := Classical.choice hnonempty
      have hphi0 : phi0 x ≠ 0 := by
        intro hzero
        apply hx
        apply phi0.injective
        simpa using hzero
      rcases lt_or_gt_of_ne hphi0 with hphi0neg | hphi0pos
      · right
        intro psi
        have hmul := values_mul_pos x hx hnorm phi0 psi
        have hpsineg : psi x < 0 := by
          by_contra h
          push Not at h
          nlinarith
        simpa using neg_pos.mpr hpsineg
      · left
        intro psi
        have hmul := values_mul_pos x hx hnorm phi0 psi
        by_contra h
        push Not at h
        nlinarith

/-- Explicit sign version of `totally_or_neg`. -/
theorem sign_totally_positive
    [Fact (∀ r : ℚ, r ^ 2 ≠ (d : ℚ) + 0 * r)]
    [Module.Finite ℚ (QFModel d)]
    [NumberField (QFModel d)]
    (x : QFModel d) (hx : x ≠ 0)
    (hnorm : 0 < Algebra.norm ℚ x) :
    ∃ epsilon : ℤ, (epsilon = 1 ∨ epsilon = -1) ∧
      ITPos (QFModel d) ((epsilon : QFModel d) * x) := by
  rcases totally_or_neg x hx hnorm with hxpos | hxneg
  · exact ⟨1, Or.inl rfl, by simpa using hxpos⟩
  · exact ⟨-1, Or.inr rfl, by simpa using hxneg⟩

/-- A nonzero totally positive element of a quadratic field has positive field norm.  For a
negative radicand this follows directly from the quadratic norm formula; for a positive radicand
the norm is the product of the values at the two real embeddings. -/
theorem pos_totally_positive
    [Fact (∀ r : ℚ, r ^ 2 ≠ (d : ℚ) + 0 * r)]
    [Module.Finite ℚ (QFModel d)]
    [NumberField (QFModel d)]
    (x : QFModel d) (hx : x ≠ 0)
    (htotal : ITPos (QFModel d) x) :
    0 < Algebra.norm ℚ x := by
  let canonical : Algebra ℚ (QFModel d) :=
    @DivisionRing.toRatAlgebra (QFModel d) inferInstance inferInstance
  change 0 < @Algebra.norm ℚ (QFModel d) inferInstance inferInstance canonical x
  have hRing :
      (QuadraticAlgebra.instField : Field (QFModel d)).toDivisionRing.toRing =
        (QuadraticAlgebra.instCommRing : CommRing (QFModel d)).toRing := by
    rfl
  cases hRing
  have hAlgebra : canonical = QuadraticAlgebra.instAlgebra := Subsingleton.elim _ _
  rw [hAlgebra]
  clear hAlgebra canonical
  by_cases hdneg : d < 0
  · rw [QIMap.norm_quadratic_model]
    have hcoords : x.re ≠ 0 ∨ x.im ≠ 0 := by
      by_contra h
      push Not at h
      apply hx
      apply QuadraticAlgebra.ext <;> simp [h.1, h.2]
    rcases hcoords with hre | him
    · have hreSq : 0 < x.re ^ 2 := sq_pos_of_ne_zero hre
      have himSq : 0 ≤ x.im ^ 2 := sq_nonneg _
      have hdnegQ : (d : ℚ) < 0 := by exact_mod_cast hdneg
      have hterm : 0 ≤ -(d : ℚ) * x.im ^ 2 :=
        mul_nonneg (neg_nonneg.mpr hdnegQ.le) himSq
      nlinarith
    · have hreSq : 0 ≤ x.re ^ 2 := sq_nonneg _
      have himSq : 0 < x.im ^ 2 := sq_pos_of_ne_zero him
      have hdnegQ : (d : ℚ) < 0 := by exact_mod_cast hdneg
      have hterm : 0 < -(d : ℚ) * x.im ^ 2 :=
        mul_pos (neg_pos.mpr hdnegQ) himSq
      nlinarith
  · have hd0 : d ≠ 0 := by
      intro hd
      have h := (Fact.out : ∀ r : ℚ, r ^ 2 ≠ (d : ℚ) + 0 * r) 0
      simp [hd] at h
    have hdpos : 0 < d := lt_of_le_of_ne (le_of_not_gt hdneg) (Ne.symm hd0)
    let sqrtD : ℝ := Real.sqrt (d : ℝ)
    have hsqrt : sqrtD ^ 2 = (d : ℝ) := by
      rw [Real.sq_sqrt]
      exact_mod_cast le_of_lt hdpos
    let phiPos : QFModel d →+* ℝ :=
      (QuadraticAlgebra.lift (R := ℚ) (A := ℝ)
        ⟨sqrtD, by
          simpa [pow_two] using hsqrt⟩).toRingHom
    let phiNeg : QFModel d →+* ℝ :=
      (QuadraticAlgebra.lift (R := ℚ) (A := ℝ)
        ⟨-sqrtD, by
          simpa [pow_two] using hsqrt⟩).toRingHom
    have hphiPos : phiPos QuadraticAlgebra.omega = sqrtD := by
      simp [phiPos]
    have hphiNeg : phiNeg QuadraticAlgebra.omega = -sqrtD := by
      simp [phiNeg]
    have hprod :
        ((@Algebra.norm ℚ (QFModel d) inferInstance inferInstance
          QuadraticAlgebra.instAlgebra x : ℚ) : ℝ) = phiPos x * phiNeg x := by
      rw [QIMap.norm_quadratic_model]
      push_cast
      rw [map_apply x phiPos, map_apply x phiNeg, hphiPos, hphiNeg]
      nlinarith [hsqrt]
    have hprodpos : 0 < phiPos x * phiNeg x :=
      mul_pos (htotal phiPos) (htotal phiNeg)
    rw [← hprod] at hprodpos
    exact_mod_cast hprodpos

/-- Squarefree-radicand specialization with the canonical quadratic number-field instances
used throughout the formalization of Theorem 4.29. -/
theorem sign_totally_squarefree
    {d : ℤ} (hd : Squarefree d) (hd1 : d ≠ 1) :
    letI : Fact (∀ r : ℚ, r ^ 2 ≠ (d : ℚ) + 0 * r) :=
      quadraticNonsquareFact hd hd1
    letI : Module.Finite ℚ (QFModel d) := quadraticModuleFinite hd hd1
    letI : NumberField (QFModel d) := quadraticFieldNumber hd hd1
    ∀ (x : QFModel d), x ≠ 0 → 0 < Algebra.norm ℚ x →
      ∃ epsilon : ℤ, (epsilon = 1 ∨ epsilon = -1) ∧
        ITPos (QFModel d)
          ((epsilon : QFModel d) * x) := by
  letI : Fact (∀ r : ℚ, r ^ 2 ≠ (d : ℚ) + 0 * r) :=
    quadraticNonsquareFact hd hd1
  letI : Module.Finite ℚ (QFModel d) := quadraticModuleFinite hd hd1
  letI : NumberField (QFModel d) := quadraticFieldNumber hd hd1
  intro x hx hnorm
  exact sign_totally_positive x hx hnorm

end QTPositi

end

end Towers.NumberTheory.Milne
