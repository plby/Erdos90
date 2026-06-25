import Towers.NumberTheory.Locals.RamificationGroups


/-!
# Milne, Exercise 8-2

For positive lower ramification index, the coefficient of a Galois
automorphism on a uniformizer is additive modulo the maximal ideal.

The converse at index zero is not a formal consequence of the ideal-theoretic
definition alone: it also uses that the tame character on `G₀ / G₁` is
nontrivial.  The theorem below isolates and proves the exact positive-index
calculation.
-/

namespace Towers.NumberTheory.Milne

open scoped Pointwise

section HigherRamificationCoefficient

variable {B G : Type*} [CommRing B] [IsDomain B] [Group G]
  [MulSemiringAction G B]

private theorem ramification_mod_uniformizer
    (Pi : B) (hPi : Pi ≠ 0) (i : Nat) (hi : 0 < i)
    (a : idealRamificationGroup (Ideal.span ({Pi} : Set B)) G i → B)
    (ha : ∀ sigma,
      sigma.1 • Pi = Pi + a sigma * Pi ^ (i + 1))
    (sigma tau : idealRamificationGroup (Ideal.span ({Pi} : Set B)) G i) :
    Ideal.Quotient.mk (Ideal.span ({Pi} : Set B)) (a (sigma * tau)) =
      Ideal.Quotient.mk (Ideal.span ({Pi} : Set B)) (a sigma) +
        Ideal.Quotient.mk (Ideal.span ({Pi} : Set B)) (a tau) := by
  let P : Ideal B := Ideal.span ({Pi} : Set B)
  let q : B →+* B ⧸ P := Ideal.Quotient.mk P
  let u : B := 1 + a sigma * Pi ^ i
  have hfactor : sigma.1 • Pi = Pi * u := by
    rw [ha sigma]
    dsimp [u]
    rw [pow_succ]
    ring
  have heq :
      Pi + a (sigma * tau) * Pi ^ (i + 1) =
        (Pi + a sigma * Pi ^ (i + 1)) +
          (sigma.1 • a tau) * (sigma.1 • Pi) ^ (i + 1) := by
    calc
      Pi + a (sigma * tau) * Pi ^ (i + 1) = (sigma * tau).1 • Pi :=
        (ha (sigma * tau)).symm
      _ = sigma.1 • (tau.1 • Pi) := by simp [mul_smul]
      _ = sigma.1 • (Pi + a tau * Pi ^ (i + 1)) := by rw [ha tau]
      _ = (Pi + a sigma * Pi ^ (i + 1)) +
          (sigma.1 • a tau) * (sigma.1 • Pi) ^ (i + 1) := by
        simp only [smul_add, smul_mul', smul_pow', ha sigma]
  have hcancelPi :
      a (sigma * tau) * Pi ^ (i + 1) =
        a sigma * Pi ^ (i + 1) +
          (sigma.1 • a tau) * (sigma.1 • Pi) ^ (i + 1) := by
    apply add_left_cancel (a := Pi)
    simpa [add_assoc] using heq
  have hcoeff :
      a (sigma * tau) =
        a sigma + (sigma.1 • a tau) * u ^ (i + 1) := by
    refine mul_right_cancel₀ (b := Pi ^ (i + 1)) (pow_ne_zero _ hPi) ?_
    rw [hfactor, mul_pow] at hcancelPi
    calc
      a (sigma * tau) * Pi ^ (i + 1) =
          a sigma * Pi ^ (i + 1) +
            (sigma.1 • a tau) *
              (Pi ^ (i + 1) * u ^ (i + 1)) := hcancelPi
      _ = (a sigma + (sigma.1 • a tau) * u ^ (i + 1)) *
          Pi ^ (i + 1) := by ring
  have haction : q (sigma.1 • a tau) = q (a tau) := by
    apply Ideal.Quotient.eq.mpr
    exact Ideal.pow_le_self (Nat.succ_ne_zero i) (sigma.2 (a tau))
  have hqPi : q Pi = 0 := by
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    exact Ideal.mem_span_singleton_self Pi
  have hqu : q u = 1 := by
    dsimp [u]
    simp [map_add, map_mul, map_pow, hqPi, zero_pow hi.ne']
  change q (a (sigma * tau)) = q (a sigma) + q (a tau)
  rw [hcoeff, map_add, map_mul, map_pow, haction, hqu]
  simp

/-- At ramification level zero the coefficient law has one extra quadratic
term.  This is the precise obstruction to additivity omitted by the phrase
"if and only if `i > 0`" in the exercise. -/
theorem ramification_coefficient_formula
    (Pi : B) (hPi : Pi ≠ 0)
    (a : idealRamificationGroup (Ideal.span ({Pi} : Set B)) G 0 → B)
    (ha : ∀ sigma, sigma.1 • Pi = Pi + a sigma * Pi)
    (sigma tau : idealRamificationGroup (Ideal.span ({Pi} : Set B)) G 0) :
    Ideal.Quotient.mk (Ideal.span ({Pi} : Set B)) (a (sigma * tau)) =
      Ideal.Quotient.mk (Ideal.span ({Pi} : Set B)) (a sigma) +
        Ideal.Quotient.mk (Ideal.span ({Pi} : Set B)) (a tau) +
          Ideal.Quotient.mk (Ideal.span ({Pi} : Set B)) (a sigma * a tau) := by
  let P : Ideal B := Ideal.span ({Pi} : Set B)
  let q : B →+* B ⧸ P := Ideal.Quotient.mk P
  let u : B := 1 + a sigma
  have hfactor : sigma.1 • Pi = Pi * u := by
    rw [ha sigma]
    dsimp [u]
    ring
  have heq :
      Pi + a (sigma * tau) * Pi =
        (Pi + a sigma * Pi) +
          (sigma.1 • a tau) * (sigma.1 • Pi) := by
    calc
      Pi + a (sigma * tau) * Pi = (sigma * tau).1 • Pi :=
        (ha (sigma * tau)).symm
      _ = sigma.1 • (tau.1 • Pi) := by simp [mul_smul]
      _ = sigma.1 • (Pi + a tau * Pi) := by rw [ha tau]
      _ = (Pi + a sigma * Pi) +
          (sigma.1 • a tau) * (sigma.1 • Pi) := by
        simp only [smul_add, smul_mul', ha sigma]
  have hcancelPi :
      a (sigma * tau) * Pi =
        a sigma * Pi + (sigma.1 • a tau) * (sigma.1 • Pi) := by
    apply add_left_cancel (a := Pi)
    simpa [add_assoc] using heq
  have hcoeff :
      a (sigma * tau) = a sigma + (sigma.1 • a tau) * u := by
    apply mul_right_cancel₀ hPi
    rw [hfactor] at hcancelPi
    calc
      a (sigma * tau) * Pi =
          a sigma * Pi + (sigma.1 • a tau) * (Pi * u) := hcancelPi
      _ = (a sigma + (sigma.1 • a tau) * u) * Pi := by ring
  have haction : q (sigma.1 • a tau) = q (a tau) := by
    apply Ideal.Quotient.eq.mpr
    exact Ideal.pow_le_self (Nat.succ_ne_zero 0) (sigma.2 (a tau))
  change q (a (sigma * tau)) =
    q (a sigma) + q (a tau) + q (a sigma * a tau)
  rw [hcoeff, map_add, map_mul, haction]
  dsimp [u]
  simp only [map_add, map_one]
  rw [map_mul]
  ring

/-- The level-zero coefficient map is additive exactly when all of its
quadratic cross-terms vanish in the residue ring.  In the usual nontrivial
tame situation this condition fails. -/
theorem ramification_coefficient_additive
    (Pi : B) (hPi : Pi ≠ 0)
    (a : idealRamificationGroup (Ideal.span ({Pi} : Set B)) G 0 → B)
    (ha : ∀ sigma, sigma.1 • Pi = Pi + a sigma * Pi) :
    (∀ sigma tau,
      Ideal.Quotient.mk (Ideal.span ({Pi} : Set B)) (a (sigma * tau)) =
        Ideal.Quotient.mk (Ideal.span ({Pi} : Set B)) (a sigma) +
          Ideal.Quotient.mk (Ideal.span ({Pi} : Set B)) (a tau)) ↔
      ∀ sigma tau,
        Ideal.Quotient.mk (Ideal.span ({Pi} : Set B)) (a sigma * a tau) = 0 := by
  constructor
  · intro hadd sigma tau
    have hformula := ramification_coefficient_formula
      Pi hPi a ha sigma tau
    rw [hadd sigma tau] at hformula
    apply add_left_cancel
      (a := Ideal.Quotient.mk (Ideal.span ({Pi} : Set B)) (a sigma) +
        Ideal.Quotient.mk (Ideal.span ({Pi} : Set B)) (a tau))
    simpa using hformula
  · intro hzero sigma tau
    simpa only [hzero sigma tau, add_zero] using
      ramification_coefficient_formula Pi hPi a ha sigma tau

/-- When `(Pi)` is maximal, the level-zero coefficient map is additive exactly
when it vanishes identically.  Equivalently, the missing converse in the
printed exercise requires the tame character `sigma |-> 1 + a(sigma)` to be
nontrivial. -/
theorem ramifi_addit_coeff
    (Pi : B) (hPi : Pi ≠ 0)
    (a : idealRamificationGroup (Ideal.span ({Pi} : Set B)) G 0 → B)
    (ha : ∀ sigma, sigma.1 • Pi = Pi + a sigma * Pi)
    [hmax : (Ideal.span ({Pi} : Set B)).IsMaximal] :
    (∀ sigma tau,
      Ideal.Quotient.mk (Ideal.span ({Pi} : Set B)) (a (sigma * tau)) =
        Ideal.Quotient.mk (Ideal.span ({Pi} : Set B)) (a sigma) +
          Ideal.Quotient.mk (Ideal.span ({Pi} : Set B)) (a tau)) ↔
      ∀ sigma,
        Ideal.Quotient.mk (Ideal.span ({Pi} : Set B)) (a sigma) = 0 := by
  let P : Ideal B := Ideal.span ({Pi} : Set B)
  letI : Field (B ⧸ P) := Ideal.Quotient.field P
  rw [ramification_coefficient_additive Pi hPi a ha]
  constructor
  · intro hcross sigma
    have hsquare := hcross sigma sigma
    change Ideal.Quotient.mk P (a sigma * a sigma) = 0 at hsquare
    rw [map_mul] at hsquare
    exact (mul_self_eq_zero.mp hsquare)
  · intro hzero sigma tau
    change Ideal.Quotient.mk P (a sigma * a tau) = 0
    rw [map_mul, hzero sigma, hzero tau, zero_mul]

/-- In the nontrivial tame case the level-zero coefficient map is not
additive.  This is the valid form of the reverse implication in Exercise 8-2. -/
theorem ramification_not_additive
    (Pi : B) (hPi : Pi ≠ 0)
    (a : idealRamificationGroup (Ideal.span ({Pi} : Set B)) G 0 → B)
    (ha : ∀ sigma, sigma.1 • Pi = Pi + a sigma * Pi)
    [hmax : (Ideal.span ({Pi} : Set B)).IsMaximal]
    (hnontrivial : ∃ sigma,
      Ideal.Quotient.mk (Ideal.span ({Pi} : Set B)) (a sigma) ≠ 0) :
    ¬ ∀ sigma tau,
      Ideal.Quotient.mk (Ideal.span ({Pi} : Set B)) (a (sigma * tau)) =
        Ideal.Quotient.mk (Ideal.span ({Pi} : Set B)) (a sigma) +
          Ideal.Quotient.mk (Ideal.span ({Pi} : Set B)) (a tau) := by
  rw [ramifi_addit_coeff
    Pi hPi a ha]
  rcases hnontrivial with ⟨sigma, hsigma⟩
  intro hzero
  exact hsigma (hzero sigma)

/-- For the canonical uniformizer coefficients, level-zero additivity is
equivalent to the tame ramification quotient being trivial (`G₀ = G₁`). -/
theorem principal_ramification_top
    {A : Type*} [CommRing A] [Algebra A B] [SMulCommClass G A B]
    (Pi : B) (hPi : Pi ≠ 0)
    (hgen : Algebra.adjoin A ({Pi} : Set B) = ⊤)
    [hmax : (Ideal.span ({Pi} : Set B)).IsMaximal] :
    (∀ sigma tau :
        idealRamificationGroup (Ideal.span ({Pi} : Set B)) G 0,
      Ideal.Quotient.mk (Ideal.span ({Pi} : Set B))
          (principalRamificationCoefficient Pi 0 (sigma * tau)) =
        Ideal.Quotient.mk (Ideal.span ({Pi} : Set B))
            (principalRamificationCoefficient Pi 0 sigma) +
          Ideal.Quotient.mk (Ideal.span ({Pi} : Set B))
            (principalRamificationCoefficient Pi 0 tau)) ↔
      idealRamificationStep (G := G) Pi 0 = ⊤ := by
  have hspec : ∀ sigma :
      idealRamificationGroup (Ideal.span ({Pi} : Set B)) G 0,
      sigma.1 • Pi =
        Pi + principalRamificationCoefficient Pi 0 sigma * Pi := by
    intro sigma
    simpa using principal_ramification_spec (G := G) Pi 0 sigma
  rw [ramifi_addit_coeff
    Pi hPi (principalRamificationCoefficient Pi 0)
      hspec]
  constructor
  · intro hzero
    apply top_unique
    intro sigma _
    apply (principal_ramification_step
      (A := A) (G := G) Pi hPi 0 hgen sigma).1
    exact Ideal.Quotient.eq_zero_iff_mem.mp (hzero sigma)
  · intro htop sigma
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    apply (principal_ramification_step
      (A := A) (G := G) Pi hPi 0 hgen sigma).2
    rw [htop]
    trivial

/-- Corrected full form of Exercise 8-2.  The printed equivalence holds
provided the tame quotient `G₀ / G₁` is nontrivial.  Without this hypothesis
the level-zero coefficient can also be additive. -/
theorem principal_ramification_pos
    {A : Type*} [CommRing A] [Algebra A B] [SMulCommClass G A B]
    (Pi : B) (hPi : Pi ≠ 0)
    (hgen : Algebra.adjoin A ({Pi} : Set B) = ⊤)
    [hmax : (Ideal.span ({Pi} : Set B)).IsMaximal]
    (htame : idealRamificationStep (G := G) Pi 0 ≠ ⊤)
    (i : Nat) :
    (∀ sigma tau :
        idealRamificationGroup (Ideal.span ({Pi} : Set B)) G i,
      Ideal.Quotient.mk (Ideal.span ({Pi} : Set B))
          (principalRamificationCoefficient Pi i (sigma * tau)) =
        Ideal.Quotient.mk (Ideal.span ({Pi} : Set B))
            (principalRamificationCoefficient Pi i sigma) +
          Ideal.Quotient.mk (Ideal.span ({Pi} : Set B))
            (principalRamificationCoefficient Pi i tau)) ↔
      0 < i := by
  constructor
  · intro hadd
    by_contra hi
    have hi0 : i = 0 := Nat.eq_zero_of_not_pos hi
    subst i
    exact htame
      ((principal_ramification_top
        (A := A) (G := G) Pi hPi hgen).1 hadd)
  · intro hi sigma tau
    exact ramification_mod_uniformizer
      Pi hPi i hi (principalRamificationCoefficient Pi i)
        (principal_ramification_spec (G := G) Pi i) sigma tau

/-- Exercise 8-2, positive-index direction.  If
`sigma Pi = Pi + a(sigma) Pi^(i+1)`, then `a(sigma) mod Pi` is an additive
homomorphism on the `i`th ramification group for `i > 0`. -/
noncomputable def higherRamificationHom
    (Pi : B) (hPi : Pi ≠ 0) (i : Nat) (hi : 0 < i)
    (a : idealRamificationGroup (Ideal.span ({Pi} : Set B)) G i → B)
    (ha : ∀ sigma,
      sigma.1 • Pi = Pi + a sigma * Pi ^ (i + 1)) :
    Additive (idealRamificationGroup (Ideal.span ({Pi} : Set B)) G i) →+
      B ⧸ Ideal.span ({Pi} : Set B) where
  toFun sigma := Ideal.Quotient.mk (Ideal.span ({Pi} : Set B)) (a sigma.toMul)
  map_zero' := by
    change Ideal.Quotient.mk (Ideal.span ({Pi} : Set B)) (a 1) = 0
    have hzero : a 1 = 0 := by
      have h := ha (1 : idealRamificationGroup
        (Ideal.span ({Pi} : Set B)) G i)
      have h' : Pi = Pi + a 1 * Pi ^ (i + 1) := by simpa using h
      have hprod : a 1 * Pi ^ (i + 1) = 0 := add_eq_left.mp h'.symm
      exact (mul_eq_zero.mp hprod).resolve_right (pow_ne_zero _ hPi)
    simp [hzero]
  map_add' sigma tau :=
    ramification_mod_uniformizer Pi hPi i hi a ha sigma.toMul tau.toMul

@[simp]
theorem higher_ramification_coefficient
    (Pi : B) (hPi : Pi ≠ 0) (i : Nat) (hi : 0 < i)
    (a : idealRamificationGroup (Ideal.span ({Pi} : Set B)) G i → B)
    (ha : ∀ sigma,
      sigma.1 • Pi = Pi + a sigma * Pi ^ (i + 1))
    (sigma : Additive
      (idealRamificationGroup (Ideal.span ({Pi} : Set B)) G i)) :
    higherRamificationHom Pi hPi i hi a ha sigma =
      Ideal.Quotient.mk (Ideal.span ({Pi} : Set B)) (a sigma.toMul) :=
  rfl

end HigherRamificationCoefficient

section NumberFieldHigherRamificationCoefficient

open NumberField

/-- Exercise 8-2 for the higher ramification groups at an actual prime of a
number field.  For every positive level, the coefficient map induces an
injection from `G_i / G_(i+1)` into the additive group of the residue field.

This is the arithmetic specialization of the abstract coefficient law above;
the construction of the quotient map and the identification of its kernel
are supplied by `RamificationGroups`. -/
theorem exercise_eight_injective
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    {q : ℕ} (hq : Nat.Prime q)
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)]
    (i : ℕ) (hi : 0 < i) :
    ∃ φ : Towers.number_ramification_step (L := L) P i →*
        Multiplicative P.ResidueField,
      Function.Injective φ := by
  exact
    number_higher_additive
      L hq P i hi

end NumberFieldHigherRamificationCoefficient

end Towers.NumberTheory.Milne
