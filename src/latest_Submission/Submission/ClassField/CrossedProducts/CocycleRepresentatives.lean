import Mathlib.FieldTheory.Galois.Basic
import Submission.ClassField.BrauerGroups.SimpleSubalgebraInner
import Submission.ClassField.CrossedProducts.CocycleConstruction
import Submission.ClassField.CrossedProducts.IsMaximalCommutative


/-!
# Chapter IV, Section 3: representatives and factor sets

This file constructs the representatives and factor set in equations
(38)--(40) from a finite Galois subfield of a central simple algebra.
-/

namespace Submission.CField.CProduca

open groupCohomology

noncomputable section

universe u

variable (k L A : Type u) [Field k] [Field L] [Algebra k L]
  [FiniteDimensional k L] [IsGalois k L]
  [Ring A] [Algebra k A] [IsSimpleRing A] [Algebra.IsCentral k A]
  [Module.Finite k A]

variable (i : L →ₐ[k] A)

omit [IsGalois k L] in
/-- Skolem--Noether supplies a unit implementing every Galois automorphism
of an embedded finite Galois field. -/
theorem exists_galois_conjugator (sigma : Gal(L/k)) :
    ∃ e : Aˣ, ∀ a : L,
      i (sigma a) = (e : A) * i a * (e⁻¹ : Aˣ) := by
  exact BGroups.skolemNoether k L A (i.comp sigma.toAlgHom) i

/-- A normalized choice of the Skolem--Noether conjugators. -/
def galoisConjugator (i : L →ₐ[k] A) (sigma : Gal(L/k)) : Aˣ := by
  classical
  exact if h : sigma = 1 then 1
    else Classical.choose (exists_galois_conjugator k L A i sigma)

omit [IsGalois k L] in
@[simp]
theorem galoisConjugator_one : galoisConjugator k L A i 1 = 1 := by
  simp [galoisConjugator]

omit [IsGalois k L] in
/-- Equation (38) for the normalized choice of conjugators. -/
theorem galoisConjugator_spec (sigma : Gal(L/k)) (a : L) :
    i (sigma a) = (galoisConjugator k L A i sigma : A) * i a *
      ((galoisConjugator k L A i sigma)⁻¹ : Aˣ) := by
  by_cases h : sigma = 1
  · subst sigma
    simp
  · simpa [galoisConjugator, h] using
      Classical.choose_spec (exists_galois_conjugator k L A i sigma) a

omit [IsGalois k L] in
/-- Equation (39), the commuting form of the conjugation identity. -/
theorem conjugator_mul_scalar (sigma : Gal(L/k)) (a : L) :
    (galoisConjugator k L A i sigma : A) * i a =
      i (sigma a) * (galoisConjugator k L A i sigma : A) := by
  have h := galoisConjugator_spec k L A i sigma a
  calc
    (galoisConjugator k L A i sigma : A) * i a =
        ((galoisConjugator k L A i sigma : A) * i a *
          ((galoisConjugator k L A i sigma)⁻¹ : Aˣ)) *
            (galoisConjugator k L A i sigma : A) := by simp [mul_assoc]
    _ = i (sigma a) * (galoisConjugator k L A i sigma : A) := by rw [← h]

/-- The embedding of scalar units into the unit group of the ambient
algebra. -/
def scalarUnits : Lˣ →* Aˣ := Units.map i.toRingHom.toMonoidHom

omit [FiniteDimensional k L] [IsGalois k L] [Algebra.IsCentral k A] [Module.Finite k A] in
theorem scalarUnits_injective :
    Function.Injective (scalarUnits k L A i) := by
  exact Units.map_injective i.injective

omit [FiniteDimensional k L] [IsGalois k L] [IsSimpleRing A] [Algebra.IsCentral k A]
  [Module.Finite k A] in
private theorem range_commutative :
    ∀ x y : i.range, x * y = y * x := by
  intro x y
  obtain ⟨a, ha⟩ := x.2
  obtain ⟨b, hb⟩ := y.2
  apply Subtype.ext
  change (x : A) * (y : A) = (y : A) * (x : A)
  rw [← ha, ← hb]
  rw [← map_mul, ← map_mul, mul_comm]

private noncomputable def rangeEquiv : L ≃ₐ[k] i.range :=
  AlgEquiv.ofInjective i i.injective

omit [FiniteDimensional k L] [IsGalois k L] in
private theorem range_centralizer_eq
    (hdim : Module.finrank k A = (Module.finrank k L) ^ 2) :
    Subalgebra.centralizer k (i.range : Set A) = i.range := by
  let e := rangeEquiv k L A i
  letI : IsSimpleRing i.range :=
    IsSimpleRing.of_ringEquiv e.toRingEquiv inferInstance
  have hrank : Module.finrank k i.range = Module.finrank k L :=
    e.toLinearEquiv.finrank_eq.symm
  apply (centralizer_finrank_sq k A i.range
    (range_commutative k L A i)).2
  simpa [hrank] using hdim

omit [FiniteDimensional k L] [IsGalois k L] in
/-- Two units implementing the same Galois automorphism differ, on the left,
by a unique scalar unit. -/
theorem unique_scalar_units
    (hdim : Module.finrank k A = (Module.finrank k L) ^ 2)
    (sigma : Gal(L/k)) (u v : Aˣ)
    (hu : ∀ a : L, (u : A) * i a = i (sigma a) * (u : A))
    (hv : ∀ a : L, (v : A) * i a = i (sigma a) * (v : A)) :
    ∃! c : Lˣ, u = scalarUnits k L A i c * v := by
  let w : Aˣ := u * v⁻¹
  have hwcentral : (w : A) ∈ Subalgebra.centralizer k (i.range : Set A) := by
    rw [Subalgebra.mem_centralizer_iff]
    intro b hb
    obtain ⟨a, rfl⟩ := hb
    let x : L := sigma⁻¹ a
    have hsx : sigma x = a := by simp [x]
    have hv_inv : ((v⁻¹ : Aˣ) : A) * i (sigma x) = i x * ((v⁻¹ : Aˣ) : A) := by
      have hh := congrArg
        (fun z : A => ((v⁻¹ : Aˣ) : A) * z * ((v⁻¹ : Aˣ) : A)) (hv x)
      simpa [mul_assoc] using hh.symm
    change i a * ((u * v⁻¹ : Aˣ) : A) =
      ((u * v⁻¹ : Aˣ) : A) * i a
    simp only [Units.val_mul]
    calc
      i a * ((u : A) * ((v⁻¹ : Aˣ) : A)) =
          i (sigma x) * ((u : A) * ((v⁻¹ : Aˣ) : A)) := by rw [hsx]
      _ = (i (sigma x) * (u : A)) * ((v⁻¹ : Aˣ) : A) := by rw [mul_assoc]
      _ = ((u : A) * i x) * ((v⁻¹ : Aˣ) : A) := by rw [hu]
      _ = (u : A) * (i x * ((v⁻¹ : Aˣ) : A)) := by rw [mul_assoc]
      _ = (u : A) * (((v⁻¹ : Aˣ) : A) * i (sigma x)) := by rw [hv_inv]
      _ = ((u : A) * ((v⁻¹ : Aˣ) : A)) * i (sigma x) := by rw [← mul_assoc]
      _ = ((u : A) * ((v⁻¹ : Aˣ) : A)) * i a := by rw [hsx]
  rw [range_centralizer_eq k L A i hdim] at hwcentral
  obtain ⟨c, hc⟩ := hwcentral
  have hc0 : c ≠ 0 := by
    intro hc0
    have hw0 : (w : A) = 0 := by simpa [hc0] using hc.symm
    exact Units.ne_zero w hw0
  let cu : Lˣ := Units.mk0 c hc0
  have hcu : u = scalarUnits k L A i cu * v := by
    apply Units.ext
    change (u : A) = i c * (v : A)
    have hw : (u : A) * (v⁻¹ : Aˣ) = i c := hc.symm
    calc
      (u : A) = ((u : A) * (v⁻¹ : Aˣ)) * (v : A) := by simp
      _ = i c * (v : A) := by rw [hw]
  refine ⟨cu, hcu, ?_⟩
  intro d hd
  apply scalarUnits_injective k L A i
  apply mul_right_cancel (b := v)
  rw [← hcu, ← hd]

omit [IsGalois k L] in
/-- The product of the representatives for `sigma` and `tau` implements
their product. -/
theorem galois_conjugator_scalar (sigma tau : Gal(L/k)) (a : L) :
    ((galoisConjugator k L A i sigma * galoisConjugator k L A i tau : Aˣ) : A) * i a =
      i ((sigma * tau) a) *
        ((galoisConjugator k L A i sigma * galoisConjugator k L A i tau : Aˣ) : A) := by
  simp only [Units.val_mul]
  calc
    (galoisConjugator k L A i sigma : A) *
          (galoisConjugator k L A i tau : A) * i a =
        (galoisConjugator k L A i sigma : A) *
          ((galoisConjugator k L A i tau : A) * i a) := by rw [mul_assoc]
    _ = (galoisConjugator k L A i sigma : A) *
          (i (tau a) * (galoisConjugator k L A i tau : A)) := by
            rw [conjugator_mul_scalar]
    _ = ((galoisConjugator k L A i sigma : A) * i (tau a)) *
          (galoisConjugator k L A i tau : A) := by rw [← mul_assoc]
    _ = (i (sigma (tau a)) * (galoisConjugator k L A i sigma : A)) *
          (galoisConjugator k L A i tau : A) := by
            rw [conjugator_mul_scalar]
    _ = i ((sigma * tau) a) *
          ((galoisConjugator k L A i sigma : A) *
            (galoisConjugator k L A i tau : A)) := by
            simp [mul_assoc]

/-- The factor in equation (40), chosen using scalar uniqueness. -/
def galoisFactor (i : L →ₐ[k] A)
    (hdim : Module.finrank k A = (Module.finrank k L) ^ 2)
    (p : Gal(L/k) × Gal(L/k)) : Lˣ :=
  Classical.choose <| unique_scalar_units k L A i hdim (p.1 * p.2)
    (galoisConjugator k L A i p.1 * galoisConjugator k L A i p.2)
    (galoisConjugator k L A i (p.1 * p.2))
    (galois_conjugator_scalar k L A i p.1 p.2)
    (conjugator_mul_scalar k L A i (p.1 * p.2))

omit [IsGalois k L] in
/-- Equation (40) for the chosen factor. -/
theorem galoisConjugator_mul (hdim : Module.finrank k A = (Module.finrank k L) ^ 2)
    (sigma tau : Gal(L/k)) :
    galoisConjugator k L A i sigma * galoisConjugator k L A i tau =
      scalarUnits k L A i (galoisFactor k L A i hdim (sigma, tau)) *
        galoisConjugator k L A i (sigma * tau) := by
  exact (Classical.choose_spec <| unique_scalar_units k L A i hdim
    (sigma * tau)
    (galoisConjugator k L A i sigma * galoisConjugator k L A i tau)
    (galoisConjugator k L A i (sigma * tau))
    (galois_conjugator_scalar k L A i sigma tau)
    (conjugator_mul_scalar k L A i (sigma * tau))).1

omit [IsGalois k L] in
/-- Choosing the identity representative to be `1` normalizes the factor in
the first argument. -/
@[simp]
theorem galois_factor_left
    (hdim : Module.finrank k A = (Module.finrank k L) ^ 2)
    (sigma : Gal(L/k)) :
    galoisFactor k L A i hdim (1, sigma) = 1 := by
  apply scalarUnits_injective k L A i
  apply mul_right_cancel (b := galoisConjugator k L A i sigma)
  simpa using (galoisConjugator_mul k L A i hdim 1 sigma).symm

omit [IsGalois k L] in
/-- Choosing the identity representative to be `1` normalizes the factor in
the second argument. -/
@[simp]
theorem galois_factor_right
    (hdim : Module.finrank k A = (Module.finrank k L) ^ 2)
    (sigma : Gal(L/k)) :
    galoisFactor k L A i hdim (sigma, 1) = 1 := by
  apply scalarUnits_injective k L A i
  apply mul_right_cancel (b := galoisConjugator k L A i sigma)
  simpa using (galoisConjugator_mul k L A i hdim sigma 1).symm

omit [IsGalois k L] in
/-- The chosen factor set is normalized. -/
theorem galoisFactor_normalized
    (hdim : Module.finrank k A = (Module.finrank k L) ^ 2) :
    (∀ sigma : Gal(L/k), galoisFactor k L A i hdim (1, sigma) = 1) ∧
      (∀ sigma : Gal(L/k), galoisFactor k L A i hdim (sigma, 1) = 1) :=
  ⟨galois_factor_left k L A i hdim,
    galois_factor_right k L A i hdim⟩

/-- The actual factor-set data attached to an embedded finite Galois field in
a central simple algebra of the required square dimension. -/
def galoisSetData (i : L →ₐ[k] A)
    (hdim : Module.finrank k A = (Module.finrank k L) ^ 2) :
    FSData (G := Gal(L/k)) (M := Lˣ) (U := Aˣ) where
  q := scalarUnits k L A i
  q_injective := scalarUnits_injective k L A i
  representative := galoisConjugator k L A i
  factorSet := galoisFactor k L A i hdim
  commute_scalar sigma a := by
    apply Units.ext
    exact conjugator_mul_scalar k L A i sigma (a : L)
  mul_representative := galoisConjugator_mul k L A i hdim

omit [IsGalois k L] in
/-- The factors arising from the normalized representatives form a
multiplicative 2-cocycle. -/
theorem galois_factor_cocycle₂
    (hdim : Module.finrank k A = (Module.finrank k L) ^ 2) :
    IsMulCocycle₂ (galoisFactor k L A i hdim) :=
  (galoisSetData k L A i hdim).isMulCocycle₂

end

end Submission.CField.CProduca
