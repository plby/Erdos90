import Towers.ClassField.Ideles.Ideles
import Towers.NumberTheory.Ideals.FractionalFreeAbelian

/-!
# Chapter V, Section 4, Statement 4.1

The finite coordinate of an idèle has a discrete valuation at every finite
prime and valuation zero at all but finitely many primes.  These valuations
therefore form the exponent vector of a unique nonzero fractional ideal.
This file constructs Milne's canonical map, proves that it is onto, and
identifies its kernel with the idèles which are units at every finite place.
-/

namespace Towers.CField.Ideles

open Filter IsDedekindDomain
open Towers.NumberTheory.Milne
open scoped RestrictedProduct nonZeroDivisors WithZero

noncomputable section

variable (R K : Type*) [CommRing R] [IsDomain R] [IsDedekindDomain R]
  [Field K] [Algebra R K] [IsFractionRing R K]

private abbrev finiteIdeleAt (x : FiniteIdeles R K)
    (v : HeightOneSpectrum R) : (v.adicCompletion K)ˣ :=
  (show Πʳ v : HeightOneSpectrum R,
      [(v.adicCompletion K)ˣ, IdeleUnitSubgroup R K v] from x) v

/-- The additive order of a nonzero element of the completion at `v`.
Mathlib's multiplicative valuation sends a uniformizer to `exp (-1)`, hence
the minus sign. -/
private def localIdeleOrder (v : HeightOneSpectrum R)
    (x : (v.adicCompletion K)ˣ) : ℤ :=
  -WithZero.log (Valued.v (x : v.adicCompletion K))

omit [IsDomain R] in
private theorem local_idele_mul (v : HeightOneSpectrum R)
    (x y : (v.adicCompletion K)ˣ) :
    localIdeleOrder R K v (x * y) =
      localIdeleOrder R K v x + localIdeleOrder R K v y := by
  have hx : Valued.v (x : v.adicCompletion K) ≠ 0 := by simp
  have hy : Valued.v (y : v.adicCompletion K) ≠ 0 := by simp
  simp only [localIdeleOrder, Units.val_mul, map_mul,
    WithZero.log_mul hx hy]
  omega

omit [IsDomain R] in
private theorem local_idele_order (v : HeightOneSpectrum R)
    (x : (v.adicCompletion K)ˣ) :
    localIdeleOrder R K v x = 0 ↔
      x ∈ IdeleUnitSubgroup R K v := by
  change localIdeleOrder R K v x = 0 ↔
    x ∈ (v.adicCompletionIntegers K).units
  rw [IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one]
  have hx : Valued.v (x : v.adicCompletion K) ≠ 0 := by simp
  constructor
  · intro h
    have hlog : WithZero.log (Valued.v (x : v.adicCompletion K)) = 0 := by
      change -WithZero.log (Valued.v (x : v.adicCompletion K)) = 0 at h
      exact neg_eq_zero.mp h
    calc
      Valued.v (x : v.adicCompletion K) =
          WithZero.exp (WithZero.log (Valued.v (x : v.adicCompletion K))) :=
        (WithZero.exp_log hx).symm
      _ = 1 := by simp [hlog]
  · intro h
    simp [localIdeleOrder, h]

omit [IsDomain R] in
private theorem idele_order_support
    (x : FiniteIdeles R K) :
    {v : HeightOneSpectrum R |
      localIdeleOrder R K v (finiteIdeleAt R K x v) ≠ 0}.Finite := by
  let x' : Πʳ v : HeightOneSpectrum R,
      [(v.adicCompletion K)ˣ, IdeleUnitSubgroup R K v] := x
  apply (Filter.eventually_cofinite.mp x'.2).subset
  intro v hv
  simp only [Set.mem_setOf_eq] at hv ⊢
  exact fun hunit ↦ hv
    ((local_idele_order R K v (finiteIdeleAt R K x v)).2 hunit)

/-- The finitely supported prime-exponent vector of a finite idèle. -/
private def finiteIdeleExponents (x : FiniteIdeles R K) :
    HeightOneSpectrum R →₀ ℤ :=
  Finsupp.mk
    (idele_order_support R K x).toFinset
    (fun v ↦ localIdeleOrder R K v (finiteIdeleAt R K x v))
    (by
      intro v
      simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq])

omit [IsDomain R] in
private theorem finite_idele_exponents
    (x : FiniteIdeles R K) (v : HeightOneSpectrum R) :
    finiteIdeleExponents R K x v =
      localIdeleOrder R K v (finiteIdeleAt R K x v) :=
  rfl

/-- The exponent-vector homomorphism underlying Statement V.4.1. -/
noncomputable def ideleExponentHom :
    FiniteIdeles R K →* Multiplicative (HeightOneSpectrum R →₀ ℤ) where
  toFun x := Multiplicative.ofAdd (finiteIdeleExponents R K x)
  map_one' := by
    apply Multiplicative.toAdd.injective
    change finiteIdeleExponents R K 1 = 0
    apply Finsupp.ext
    intro v
    rw [finite_idele_exponents]
    change localIdeleOrder R K v (1 : (v.adicCompletion K)ˣ) = 0
    simp [localIdeleOrder]
  map_mul' x y := by
    apply Multiplicative.toAdd.injective
    change finiteIdeleExponents R K (x * y) =
      finiteIdeleExponents R K x + finiteIdeleExponents R K y
    apply Finsupp.ext
    intro v
    rw [Finsupp.add_apply, finite_idele_exponents,
      finite_idele_exponents, finite_idele_exponents]
    exact local_idele_mul R K v
      (finiteIdeleAt R K x v) (finiteIdeleAt R K y v)

omit [IsDomain R] in
/-- Coordinate formula for the exponent-vector homomorphism.  This public
form is useful for subsequent statements involving normalized finite-place
absolute values. -/
theorem idele_exponent_hom
    (x : FiniteIdeles R K) (v : HeightOneSpectrum R) :
    (ideleExponentHom R K x).toAdd v =
      -WithZero.log (Valued.v
        ((x.1 v : (v.adicCompletion K)ˣ) : v.adicCompletion K)) := by
  rfl

/-- The canonical homomorphism from finite idèles to nonzero fractional
ideals, `x ↦ ∏_v p_v ^ ord_v(x_v)`. -/
noncomputable def finiteIdeleIdeal :
    FiniteIdeles R K →* (FractionalIdeal R⁰ K)ˣ :=
  (fractionalIdealFactorization R K).toMonoidHom.comp
    (ideleExponentHom R K)

omit [IsDomain R] in
private theorem local_unit_order (v : HeightOneSpectrum R)
    (n : ℤ) : ∃ x : (v.adicCompletion K)ˣ,
      localIdeleOrder R K v x = n := by
  obtain ⟨x, hx⟩ :=
    IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_surjective
      (K := K) v (WithZero.exp (-n))
  have hx0 : x ≠ 0 := by
    intro hzero
    subst x
    have hzeroexp : (0 : ℤᵐ⁰) = WithZero.exp (-n) := by
      simpa using hx
    exact (WithZero.exp_ne_zero (a := -n)) hzeroexp.symm
  refine ⟨Units.mk0 x hx0, ?_⟩
  simp only [localIdeleOrder, Units.val_mk0, hx, WithZero.log_exp]
  omega

omit [IsDomain R] in
private theorem idele_exponent_surjective :
    Function.Surjective (ideleExponentHom R K) := by
  intro e
  classical
  choose x hx using fun v : HeightOneSpectrum R ↦
    local_unit_order R K v (e.toAdd v)
  have hrestricted : ∀ᶠ v in Filter.cofinite,
      x v ∈ IdeleUnitSubgroup R K v := by
    filter_upwards [show {v : HeightOneSpectrum R | v ∈ e.toAdd.support}ᶜ ∈
        Filter.cofinite from e.toAdd.support.finite_toSet.compl_mem_cofinite] with v hv
    have hev : e.toAdd v = 0 := by simpa using hv
    apply (local_idele_order R K v (x v)).1
    rw [hx v, hev]
  let a : FiniteIdeles R K := RestrictedProduct.mk x hrestricted
  refine ⟨a, ?_⟩
  apply Multiplicative.toAdd.injective
  apply Finsupp.ext
  intro v
  simpa [a, ideleExponentHom, finite_idele_exponents] using hx v

omit [IsDomain R] in
/-- The finite idèle-to-ideal map is onto. -/
theorem idele_ideal_surjective :
    Function.Surjective (finiteIdeleIdeal R K) :=
  (fractionalIdealFactorization R K).surjective.comp
    (idele_exponent_surjective R K)

set_option maxHeartbeats 800000 in
-- Unfolding the dependent restricted product needs extra elaboration time.
/-- Finite idèles which are units at every finite place. -/
def everywhereUnitIdeles : Subgroup (FiniteIdeles R K) where
  carrier := {x | ∀ v, finiteIdeleAt R K x v ∈ IdeleUnitSubgroup R K v}
  one_mem' v := (IdeleUnitSubgroup R K v).one_mem
  mul_mem' hx hy v := (IdeleUnitSubgroup R K v).mul_mem (hx v) (hy v)
  inv_mem' hx v := (IdeleUnitSubgroup R K v).inv_mem (hx v)

omit [IsDomain R] in
/-- The kernel of the finite idèle-to-ideal map is precisely the product of
the local unit groups. -/
theorem idele_ideal_ker :
    (finiteIdeleIdeal R K).ker = everywhereUnitIdeles R K := by
  ext x
  rw [MonoidHom.mem_ker]
  change (fractionalIdealFactorization R K)
      (ideleExponentHom R K x) = 1 ↔ _
  rw [← map_one (fractionalIdealFactorization R K)]
  rw [(fractionalIdealFactorization R K).injective.eq_iff]
  change finiteIdeleExponents R K x = 0 ↔ ∀ v,
    finiteIdeleAt R K x v ∈ IdeleUnitSubgroup R K v
  constructor
  · intro h v
    apply (local_idele_order R K v (finiteIdeleAt R K x v)).1
    rw [← finite_idele_exponents R K x v, h]
    rfl
  · intro h
    apply Finsupp.ext
    intro v
    rw [finite_idele_exponents,
      (local_idele_order R K v (finiteIdeleAt R K x v)).2 (h v)]
    rfl

/-- Milne's ideal map on the full idèle group; the infinite coordinates
are ignored. -/
noncomputable def ideleIdealMap :
    IdeleGroup R K →* (FractionalIdeal R⁰ K)ˣ :=
  (finiteIdeleIdeal R K).comp
    { toFun := Prod.snd
      map_one' := rfl
      map_mul' := fun _ _ ↦ rfl }

omit [IsDomain R] in
/-- **Statement V.4.1, surjectivity.** -/
theorem idele_surjective :
    Function.Surjective (ideleIdealMap R K) := by
  intro I
  obtain ⟨x, rfl⟩ := idele_ideal_surjective R K I
  exact ⟨(1, x), rfl⟩

/-- The subgroup `ℐ_{S_∞}`: arbitrary infinite coordinates and units at
every finite coordinate. -/
def idelesEveryPlace : Subgroup (IdeleGroup R K) :=
  (everywhereUnitIdeles R K).comap
    { toFun := Prod.snd
      map_one' := rfl
      map_mul' := fun _ _ ↦ rfl }

omit [IsDomain R] in
/-- **Statement V.4.1, kernel.** -/
theorem idele_ker :
    (ideleIdealMap R K).ker = idelesEveryPlace R K := by
  ext x
  change finiteIdeleIdeal R K x.2 = 1 ↔
    x.2 ∈ everywhereUnitIdeles R K
  rw [← MonoidHom.mem_ker, idele_ideal_ker]

end

end Towers.CField.Ideles
