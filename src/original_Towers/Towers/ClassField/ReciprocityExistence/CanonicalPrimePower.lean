import Towers.ClassField.ReciprocityExistence.CanonicalComparison
import Towers.ClassField.ReciprocityExistence.PadicNormalization
import Towers.ClassField.ReciprocityExistence.ActualLocalProduct
import Towers.ClassField.ReciprocityExistence.FiniteLayerAbsolute

open scoped IsMulCommutative

/-!
# The canonical prime-power product in Example VII.8.2

This file is the final product-packaging step in the prime-power case of
Example VII.8.2.  Its input records the canonical local calculations in their
natural, placewise form: complex conjugation at infinity, the explicit
`p`-adic factor at the conductor prime, arithmetic Frobenius at an away
prime, and the identity at every other finite place.

The main theorem evaluates the actual finite `finprod` and the product over
infinite places and packages the result as
`PAData`.  The already-proved explicit
cyclotomic cancellations then give principal-idèle reciprocity.
-/

namespace Towers.CField.RExist

open Polynomial
open NumberField IsDedekindDomain
open Towers.CField.LTate
open Towers.CField.Ideles
open Towers.CField.Recip
open Towers.CField.ICohomo

noncomputable section

private theorem finprod_single_off
    {ι A : Type*} [CommMonoid A] (f : ι → A) (i : ι)
    (h : ∀ j, j ≠ i → f j = 1) :
    (∏ᶠ j, f j) = f i := by
  classical
  exact finprod_eq_single f i h

private theorem finprod_off_two
    {ι A : Type*} [CommMonoid A] (f : ι → A) (i j : ι) (hij : i ≠ j)
    (h : ∀ k, k ≠ i → k ≠ j → f k = 1) :
    (∏ᶠ k, f k) = f i * f j := by
  classical
  rw [finprod_eq_finsetProd_of_mulSupport_subset f (s := {i, j})]
  · simp [hij]
  · intro k hk
    by_cases hki : k = i
    · simp [hki]
    by_cases hkj : k = j
    · simp [hkj]
    exact (hk (h k hki hkj)).elim

/-- A product of local factors on the idèles of `ℚ`, using `ℤ` as the
chosen integral model.  This is the rational specialization of
`FAProduc`; spelling it with `ℤ` keeps its source definitionally
equal to the idèle group used throughout Example VII.8.2. -/
structure RAProduc
    (A : Type*) [Group A] where
  commutative : IsMulCommutative A
  finiteLocalHom : ∀ P : HeightOneSpectrum ℤ,
    (P.adicCompletion ℚ)ˣ →* A
  eventually_units :
    ∀ᶠ P in Filter.cofinite, ∀ x : (P.adicCompletion ℚ)ˣ,
      x ∈ IdeleUnitSubgroup ℤ ℚ P → finiteLocalHom P x = 1
  infinite : ∀ v : InfinitePlace ℚ, v.1.Completionˣ →* A

namespace RAProduc

variable {A : Type*} [Group A]

private theorem finite_mulSupport (D : RAProduc A)
    (x : FiniteIdeles ℤ ℚ) :
    Function.HasFiniteMulSupport (fun P => D.finiteLocalHom P (x.1 P)) := by
  change {P | D.finiteLocalHom P (x.1 P) ≠ 1}.Finite
  rw [← Filter.eventually_cofinite]
  filter_upwards [x.2, D.eventually_units] with P hxP hD
  simpa using hD (x.1 P) hxP

noncomputable def finiteHom (D : RAProduc A) :
    FiniteIdeles ℤ ℚ →* A := by
  letI : IsMulCommutative A := D.commutative
  letI : CommGroup A := inferInstance
  exact
    { toFun := fun x => ∏ᶠ P, D.finiteLocalHom P (x.1 P)
      map_one' := by
        apply finprod_eq_one_of_forall_eq_one
        intro P
        exact map_one (D.finiteLocalHom P)
      map_mul' := fun x y => by
        rw [show (∏ᶠ P, D.finiteLocalHom P ((x * y).1 P)) =
            ∏ᶠ P, D.finiteLocalHom P (x.1 P) *
              D.finiteLocalHom P (y.1 P) by
          apply finprod_congr
          intro P
          exact map_mul (D.finiteLocalHom P) (x.1 P) (y.1 P)]
        exact finprod_mul_distrib (D.finite_mulSupport x)
          (D.finite_mulSupport y) }

noncomputable def infiniteHom (D : RAProduc A) :
    (InfiniteAdeleRing ℚ)ˣ →* A := by
  letI : IsMulCommutative A := D.commutative
  letI : CommGroup A := inferInstance
  exact
    { toFun := fun x =>
        ∏ v : InfinitePlace ℚ, D.infinite v (MulEquiv.piUnits x v)
      map_one' := by
        apply Finset.prod_eq_one
        intro v _
        rw [show MulEquiv.piUnits (1 : (InfiniteAdeleRing ℚ)ˣ) v = 1 by
          exact congrFun (map_one (MulEquiv.piUnits :
            (InfiniteAdeleRing ℚ)ˣ ≃*
              ((v : InfinitePlace ℚ) → v.1.Completionˣ))) v]
        exact map_one (D.infinite v)
      map_mul' := fun x y => by
        rw [← Finset.prod_mul_distrib]
        apply Finset.prod_congr rfl
        intro v _
        rw [show MulEquiv.piUnits (x * y) v =
            MulEquiv.piUnits x v * MulEquiv.piUnits y v by
          exact congrFun (map_mul (MulEquiv.piUnits :
            (InfiniteAdeleRing ℚ)ˣ ≃*
              ((v : InfinitePlace ℚ) → v.1.Completionˣ)) x y) v]
        exact map_mul (D.infinite v) _ _ }

/-- The actual product of the rational local factors. -/
noncomputable def artin (D : RAProduc A) :
    IdeleGroup ℤ ℚ →* A := by
  letI : IsMulCommutative A := D.commutative
  letI : CommGroup A := inferInstance
  exact
    { toFun := fun x => D.infiniteHom x.1 * D.finiteHom x.2
      map_one' := by
        change D.infiniteHom 1 * D.finiteHom 1 = 1
        rw [map_one, map_one, one_mul]
      map_mul' := fun x y => by
        change D.infiniteHom (x.1 * y.1) * D.finiteHom (x.2 * y.2) = _
        rw [map_mul D.infiniteHom, map_mul D.finiteHom]
        ac_rfl }

@[simp]
theorem artin_apply (D : RAProduc A) (x : IdeleGroup ℤ ℚ) :
    letI : IsMulCommutative A := D.commutative
    letI : CommGroup A := inferInstance
    D.artin x =
      (∏ v : InfinitePlace ℚ, D.infinite v (MulEquiv.piUnits x.1 v)) *
        (∏ᶠ P : HeightOneSpectrum ℤ, D.finiteLocalHom P (x.2.1 P)) := by
  rfl

end RAProduc

/-- The height-one prime of `ℤ` represented by the rational prime `p`. -/
noncomputable def rationalIntHeight
    (p : ℕ) [Fact p.Prime] : HeightOneSpectrum ℤ :=
  Rat.HeightOneSpectrum.primesEquiv.symm ⟨p, Fact.out⟩

local instance : DecidableEq (HeightOneSpectrum ℤ) := Classical.decEq _

@[simp]
private theorem principal_infinite_int
    (x : ℚˣ) (v : InfinitePlace ℚ) :
    MulEquiv.piUnits (principalIdele ℤ ℚ x).1 v =
      Units.map (algebraMap ℚ v.1.Completion) x := by
  apply Units.ext
  rfl

@[simp]
private theorem principal_idele_int
    (x : ℚˣ) (P : HeightOneSpectrum ℤ) :
    (principalIdele ℤ ℚ x).2.1 P =
      Units.map (algebraMap ℚ (P.adicCompletion ℚ)) x := by
  apply Units.ext
  rfl

set_option synthInstance.maxHeartbeats 500000 in
-- Cyclotomicity synthesizes the finite Galois group used by every local factor.
/-- The genuinely canonical local-factor input for Example VII.8.2.  At the
conductor prime its values are still written using the Proposition III.3.6
local Artin map.  The conversion below applies
`CanonicalPadicNormalization` to replace precisely those values by
the explicit inverse-unit map. -/
structure CFData
    (p r : ℕ) [Fact p.Prime] [NeZero (p ^ r)]
    (L : Type) [Field L] [NumberField L]
    [IsCyclotomicExtension {p ^ r} ℚ L]
    (D : RAProduc Gal(L/ℚ)) where
  conductorPlace : CompletionPlacesAbove (L := L)
    (FinitePlace.mk (rationalHeightOne p)).val
  infinite_neg_one :
    D.infinite Rat.infinitePlace
        (Units.map (algebraMap ℚ Rat.infinitePlace.Completion) (-1 : ℚˣ)) =
      cyclotomicNegAutomorphism (p ^ r) L
  infinite_nat : ∀ (q : ℕ) (hq : q.Prime),
    D.infinite Rat.infinitePlace
        (Units.map (algebraMap ℚ Rat.infinitePlace.Completion)
          (rationalNatUnit q hq.ne_zero)) = 1
  finite_neg_one :
    ∀ P : HeightOneSpectrum ℤ,
      D.finiteLocalHom P
          (Units.map (algebraMap ℚ (P.adicCompletion ℚ)) (-1 : ℚˣ)) =
        if P = rationalIntHeight p then
          canonicalPadicArtin p r L conductorPlace
            (-1 : ℚ_[p]ˣ)
        else 1
  finite_conductor :
    ∀ P : HeightOneSpectrum ℤ,
      D.finiteLocalHom P
          (Units.map (algebraMap ℚ (P.adicCompletion ℚ))
            (rationalNatUnit p (Fact.out : p.Prime).ne_zero)) =
        if P = rationalIntHeight p then
          canonicalPadicArtin p r L conductorPlace
            (padicNatUnit p p (Fact.out : p.Prime).ne_zero)
        else 1
  finite_away : ∀ (q : ℕ) (hq : q.Prime) (hqp : q ≠ p),
    letI : Fact q.Prime := ⟨hq⟩
    let hcopPow : q.Coprime (p ^ r) :=
      ((Nat.coprime_primes hq (Fact.out : p.Prime)).2 hqp).pow_right r
    ∀ P : HeightOneSpectrum ℤ,
      D.finiteLocalHom P
          (Units.map (algebraMap ℚ (P.adicCompletion ℚ))
            (rationalNatUnit q hq.ne_zero)) =
        if P = rationalIntHeight q then
          cyclotomicFrobenius
            (Polynomial.cyclotomic.irreducible_rat (NeZero.pos (p ^ r)))
            hcopPow (L := L)
        else if P = rationalIntHeight p then
          canonicalPadicArtin p r L conductorPlace
            (padicNatUnit p q hq.ne_zero)
        else 1

set_option synthInstance.maxHeartbeats 500000 in
-- The explicit factor record repeatedly synthesizes the cyclotomic Galois group structure.
/-- The canonical local calculations needed by the prime-power case of
Example VII.8.2, stated before multiplying the factors.

The finite formulas deliberately use the actual completed rational
coordinates of a principal idèle.  This makes the conversion below a theorem
about the genuine `finprod`, rather than a restatement of its conclusion. -/
structure CPData
    (p r : ℕ) [Fact p.Prime] [NeZero (p ^ r)]
    (L : Type*) [Field L] [Algebra ℚ L]
    [IsCyclotomicExtension {p ^ r} ℚ L]
    (D : RAProduc Gal(L/ℚ)) where
  infinite_neg_one :
    D.infinite Rat.infinitePlace
        (Units.map (algebraMap ℚ Rat.infinitePlace.Completion) (-1 : ℚˣ)) =
      cyclotomicNegAutomorphism (p ^ r) L
  infinite_nat : ∀ (q : ℕ) (hq : q.Prime),
    D.infinite Rat.infinitePlace
        (Units.map (algebraMap ℚ Rat.infinitePlace.Completion)
          (rationalNatUnit q hq.ne_zero)) = 1
  finite_neg_one :
    ∀ P : HeightOneSpectrum ℤ,
      D.finiteLocalHom P
          (Units.map (algebraMap ℚ (P.adicCompletion ℚ)) (-1 : ℚˣ)) =
        if P = rationalIntHeight p then
          padicCyclotomicArtin p r L (-1 : ℚ_[p]ˣ)
        else 1
  finite_conductor :
    ∀ P : HeightOneSpectrum ℤ,
      D.finiteLocalHom P
          (Units.map (algebraMap ℚ (P.adicCompletion ℚ))
            (rationalNatUnit p (Fact.out : p.Prime).ne_zero)) =
        if P = rationalIntHeight p then
          padicCyclotomicArtin p r L
            (padicNatUnit p p (Fact.out : p.Prime).ne_zero)
        else 1
  finite_away : ∀ (q : ℕ) (hq : q.Prime) (hqp : q ≠ p),
    letI : Fact q.Prime := ⟨hq⟩
    let hcopPow : q.Coprime (p ^ r) :=
      ((Nat.coprime_primes hq (Fact.out : p.Prime)).2 hqp).pow_right r
    ∀ P : HeightOneSpectrum ℤ,
      D.finiteLocalHom P
          (Units.map (algebraMap ℚ (P.adicCompletion ℚ))
            (rationalNatUnit q hq.ne_zero)) =
        if P = rationalIntHeight q then
          cyclotomicFrobenius
            (Polynomial.cyclotomic.irreducible_rat (NeZero.pos (p ^ r)))
            hcopPow (L := L)
        else if P = rationalIntHeight p then
          padicCyclotomicArtin p r L
            (padicNatUnit p q hq.ne_zero)
        else 1

namespace CFData

variable
    (p r : ℕ) [Fact p.Prime] [NeZero (p ^ r)]
    (L : Type) [Field L] [NumberField L]
    [IsCyclotomicExtension {p ^ r} ℚ L]
    (D : RAProduc Gal(L/ℚ))

set_option synthInstance.maxHeartbeats 500000 in
-- Converting canonical factors elaborates the cyclotomic Galois targets at each place.
/-- Applying the canonical/explicit normalization at the conductor prime
turns the canonical local factors into the explicit factor record used by
the prime-power product calculation. -/
theorem primeFactorData
    (C : CFData p r L D) :
    CPData p r L D where
  infinite_neg_one := C.infinite_neg_one
  infinite_nat := C.infinite_nat
  finite_neg_one P := by
    rw [C.finite_neg_one P]
    split_ifs
    · rw [canonicalPadicNormalization p r L C.conductorPlace]
    · rfl
  finite_conductor P := by
    rw [C.finite_conductor P]
    split_ifs
    · rw [canonicalPadicNormalization p r L C.conductorPlace]
    · rfl
  finite_away q hq hqp := by
    letI : Fact q.Prime := ⟨hq⟩
    dsimp only
    intro P
    rw [C.finite_away q hq hqp P]
    split_ifs
    · rfl
    · rw [canonicalPadicNormalization p r L C.conductorPlace]
    · rfl

end CFData

namespace CPData

variable
    (p r : ℕ) [Fact p.Prime] [NeZero (p ^ r)]
    (L : Type*) [Field L] [Algebra ℚ L]
    [IsCyclotomicExtension {p ^ r} ℚ L]
    (D : RAProduc Gal(L/ℚ))

private theorem infinite_rational_place
    [CommGroup Gal(L/ℚ)]
    (a : ℚˣ) :
    (∏ v : InfinitePlace ℚ,
        D.infinite v
          (Units.map (algebraMap ℚ v.1.Completion) a)) =
      D.infinite Rat.infinitePlace
        (Units.map (algebraMap ℚ Rat.infinitePlace.Completion) a) := by
  classical
  apply Fintype.prod_eq_single Rat.infinitePlace
  intro v hv
  exact (hv (Subsingleton.elim v Rat.infinitePlace)).elim

private theorem prime_height_ne
    (q : ℕ) (hq : q.Prime) (hqp : q ≠ p) :
    letI : Fact q.Prime := ⟨hq⟩
    rationalIntHeight q ≠ rationalIntHeight p := by
  letI : Fact q.Prime := ⟨hq⟩
  intro h
  apply hqp
  have h' := congrArg Rat.HeightOneSpectrum.primesEquiv h
  have hq' : Rat.HeightOneSpectrum.primesEquiv
      (rationalIntHeight q) = (⟨q, hq⟩ : Nat.Primes) := by
    exact Rat.HeightOneSpectrum.primesEquiv.apply_symm_apply _
  have hp' : Rat.HeightOneSpectrum.primesEquiv
      (rationalIntHeight p) =
        (⟨p, Fact.out⟩ : Nat.Primes) := by
    exact Rat.HeightOneSpectrum.primesEquiv.apply_symm_apply _
  rw [hq', hp'] at h'
  exact congrArg Subtype.val h'

set_option synthInstance.maxHeartbeats 500000 in
-- The three finprod calculations synthesize the commutative cyclotomic Galois group.
/-- The placewise canonical calculations give exactly the three global
products consumed by the explicit prime-power proof. -/
theorem primeActualData
    (H : CPData p r L D) :
    PAData p r L D.artin where
  neg_one_eq := by
    letI : IsMulCommutative Gal(L/ℚ) := D.commutative
    letI : CommGroup Gal(L/ℚ) := inferInstance
    rw [D.artin_apply]
    simp_rw [principal_infinite_int, principal_idele_int]
    rw [infinite_rational_place (L := L) (D := D) (-1 : ℚˣ),
      H.infinite_neg_one]
    congr 1
    calc
      (∏ᶠ P : HeightOneSpectrum ℤ,
          D.finiteLocalHom P
            (Units.map (algebraMap ℚ (P.adicCompletion ℚ)) (-1 : ℚˣ))) =
          D.finiteLocalHom (rationalIntHeight p)
            (Units.map
              (algebraMap ℚ ((rationalIntHeight p).adicCompletion ℚ))
              (-1 : ℚˣ)) := by
        apply finprod_single_off
        intro P hP
        rw [H.finite_neg_one, if_neg hP]
      _ = padicCyclotomicArtin p r L (-1 : ℚ_[p]ˣ) := by
        rw [H.finite_neg_one, if_pos rfl]
  conductor_eq := by
    letI : IsMulCommutative Gal(L/ℚ) := D.commutative
    letI : CommGroup Gal(L/ℚ) := inferInstance
    rw [D.artin_apply]
    simp_rw [principal_infinite_int, principal_idele_int]
    rw [infinite_rational_place (L := L) (D := D)
        (rationalNatUnit p (Fact.out : p.Prime).ne_zero),
      H.infinite_nat p (Fact.out : p.Prime), one_mul]
    calc
      (∏ᶠ P : HeightOneSpectrum ℤ,
          D.finiteLocalHom P
            (Units.map (algebraMap ℚ (P.adicCompletion ℚ))
              (rationalNatUnit p (Fact.out : p.Prime).ne_zero))) =
          D.finiteLocalHom (rationalIntHeight p)
            (Units.map
              (algebraMap ℚ ((rationalIntHeight p).adicCompletion ℚ))
              (rationalNatUnit p (Fact.out : p.Prime).ne_zero)) := by
        apply finprod_single_off
        intro P hP
        rw [H.finite_conductor, if_neg hP]
      _ = padicCyclotomicArtin p r L
          (padicNatUnit p p (Fact.out : p.Prime).ne_zero) := by
        rw [H.finite_conductor, if_pos rfl]
  away_eq q hq hqp := by
    letI : IsMulCommutative Gal(L/ℚ) := D.commutative
    letI : CommGroup Gal(L/ℚ) := inferInstance
    letI : Fact q.Prime := ⟨hq⟩
    let hcopPow : q.Coprime (p ^ r) :=
      ((Nat.coprime_primes hq (Fact.out : p.Prime)).2 hqp).pow_right r
    dsimp only
    have hpq : rationalIntHeight q ≠ rationalIntHeight p :=
      prime_height_ne p q hq hqp
    rw [D.artin_apply]
    simp_rw [principal_infinite_int, principal_idele_int]
    rw [infinite_rational_place (L := L) (D := D)
        (rationalNatUnit q hq.ne_zero),
      H.infinite_nat q hq, one_mul]
    calc
      (∏ᶠ P : HeightOneSpectrum ℤ,
          D.finiteLocalHom P
            (Units.map (algebraMap ℚ (P.adicCompletion ℚ))
              (rationalNatUnit q hq.ne_zero))) =
          D.finiteLocalHom (rationalIntHeight q)
              (Units.map
                (algebraMap ℚ ((rationalIntHeight q).adicCompletion ℚ))
                (rationalNatUnit q hq.ne_zero)) *
            D.finiteLocalHom (rationalIntHeight p)
              (Units.map
                (algebraMap ℚ ((rationalIntHeight p).adicCompletion ℚ))
                (rationalNatUnit q hq.ne_zero)) := by
        apply finprod_off_two _ _ _ hpq
        intro P hPq hPp
        rw [H.finite_away q hq hqp, if_neg hPq, if_neg hPp]
      _ = cyclotomicFrobenius
            (Polynomial.cyclotomic.irreducible_rat (NeZero.pos (p ^ r)))
            hcopPow (L := L) *
          padicCyclotomicArtin p r L
            (padicNatUnit p q hq.ne_zero) := by
        rw [H.finite_away q hq hqp, if_pos rfl,
          H.finite_away q hq hqp, if_neg hpq.symm, if_pos rfl]

set_option synthInstance.maxHeartbeats 500000 in
-- Applying the actual-factor reciprocity theorem reconstructs the cyclotomic group hierarchy.
/-- **Example VII.8.2, prime-power canonical product.**  Once the canonical
local maps have the standard cyclotomic values recorded above, their actual
global product is trivial on every rational principal idèle. -/
theorem principalReciprocity
    (H : CPData p r L D) :
    ∀ x : ℚˣ, D.artin (principalIdele ℤ ℚ x) = 1 :=
  reciprocity_actual_factors
    p r L D.artin (H.primeActualData p r L D)

end CPData

namespace CFData

set_option synthInstance.maxHeartbeats 500000 in
-- The packaging composition elaborates both canonical and explicit cyclotomic records.
/-- The complete requested packaging map: canonical placewise factors are
normalized at the conductor prime and then assembled into the literal
prime-power data consumed by Example VII.8.2. -/
theorem primeActualData
    (p r : ℕ) [Fact p.Prime] [NeZero (p ^ r)]
    (L : Type) [Field L] [NumberField L]
    [IsCyclotomicExtension {p ^ r} ℚ L]
    (D : RAProduc Gal(L/ℚ))
    (C : CFData p r L D) :
    PAData p r L D.artin :=
  (C.primeFactorData p r L D)
    |>.primeActualData p r L D

end CFData

set_option synthInstance.maxHeartbeats 500000 in
-- The final principal-idèle statement synthesizes the cyclotomic Galois group from its extension.
/-- **Example VII.8.2, canonical prime-power form.**  The canonical
placewise factors imply rational principal-idèle reciprocity; the conductor
normalization is now a theorem rather than an argument. -/
theorem principal_reciprocity_factors
    (p r : ℕ) [Fact p.Prime] [NeZero (p ^ r)]
    (L : Type) [Field L] [NumberField L]
    [IsCyclotomicExtension {p ^ r} ℚ L]
    (D : RAProduc Gal(L/ℚ))
    (C : CFData p r L D) :
    ∀ x : ℚˣ, D.artin (principalIdele ℤ ℚ x) = 1 :=
  reciprocity_actual_factors
    p r L D.artin (C.primeActualData p r L D)

end

end Towers.CField.RExist
