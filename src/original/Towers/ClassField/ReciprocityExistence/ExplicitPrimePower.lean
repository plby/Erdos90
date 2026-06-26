import Towers.ClassField.ReciprocityExistence.CanonicalPrimePower
import Mathlib.Algebra.Algebra.Rat

/-!
# The explicit prime-power product in Example VII.8.2

The cohomological local Artin map and the concrete Lubin--Tate action are
different constructions.  Example VII.8.2 itself uses the latter at the
conductor prime.  This file performs that replacement in the literal local
product: all away and infinite factors are retained, while the conductor
coordinate is the inverse-unit map constructed in Chapter I.

Consequently the three displayed calculations of Example VII.8.2 package
into `PAData` with no canonical/local
normalization hypothesis.
-/

namespace Towers.CField.RExist

open NumberField IsDedekindDomain
open Towers.NumberTheory.Milne
open Towers.CField.LTate
open Towers.CField.Ideles
open Towers.CField.Recip
open Towers.CField.ICohomo

noncomputable section

/-- The explicit Chapter-I local Artin map, transported from `Q_p` to the
prime-adic completion used by rational idèles. -/
noncomputable def explicitConductorAdic
    (p r : ℕ) [Fact p.Prime] [NeZero (p ^ r)]
    (L : Type*) [Field L] [Algebra ℚ L]
    [IsCyclotomicExtension {p ^ r} ℚ L] :
  ((rationalIntHeight p).adicCompletion ℚ)ˣ →* Gal(L/ℚ) :=
  (padicCyclotomicArtin p r L).comp
    (rationalCompletionUnits ⟨p, Fact.out⟩).toMonoidHom

/-- Transporting a diagonal rational unit to `Q_p` is the ordinary scalar
embedding. -/
@[simp]
theorem explicit_conductor_adic
    (p r : ℕ) [Fact p.Prime] [NeZero (p ^ r)]
    (L : Type*) [Field L] [Algebra ℚ L]
    [IsCyclotomicExtension {p ^ r} ℚ L]
    (x : ℚˣ) :
    explicitConductorAdic p r L
        (Units.map
          (algebraMap ℚ ((rationalIntHeight p).adicCompletion ℚ)) x) =
      padicCyclotomicArtin p r L
        (Units.map (algebraMap ℚ ℚ_[p]) x) := by
  apply congrArg (padicCyclotomicArtin p r L)
  apply Units.ext
  exact (rationalFiniteCompletion ⟨p, Fact.out⟩).commutes (x : ℚ)

/-- Replace only the conductor coordinate of a rational local product by
the explicit inverse-unit Lubin--Tate action. -/
noncomputable def RAProduc.withExplicitConductor
    (p r : ℕ) [Fact p.Prime] [NeZero (p ^ r)]
    (L : Type*) [Field L] [Algebra ℚ L]
    [IsCyclotomicExtension {p ^ r} ℚ L]
    (D : RAProduc Gal(L/ℚ)) :
    RAProduc Gal(L/ℚ) := by
  classical
  exact
    { commutative := D.commutative
      finiteLocalHom := fun P ↦
        if h : P = rationalIntHeight p then
          h ▸ explicitConductorAdic p r L
        else D.finiteLocalHom P
      eventually_units := by
        have hp : ∀ᶠ P in Filter.cofinite,
            P ≠ rationalIntHeight p := by
          rw [Filter.eventually_cofinite]
          simp
        filter_upwards [hp, D.eventually_units] with P hP hD
        intro x hx
        rw [dif_neg hP]
        exact hD x hx
      infinite := D.infinite }

namespace RAProduc

variable
    (p r : ℕ) [Fact p.Prime] [NeZero (p ^ r)]
    (L : Type*) [Field L] [Algebra ℚ L]
    [IsCyclotomicExtension {p ^ r} ℚ L]
    (D : RAProduc Gal(L/ℚ))

@[simp]
theorem explicit_conductor_hom :
    (D.withExplicitConductor p r L).finiteLocalHom
        (rationalIntHeight p) =
      explicitConductorAdic p r L := by
  simp [withExplicitConductor]

theorem explicit_conductor_ne
    (P : HeightOneSpectrum ℤ)
    (hP : P ≠ rationalIntHeight p) :
    (D.withExplicitConductor p r L).finiteLocalHom P =
      D.finiteLocalHom P := by
  simp [withExplicitConductor, hP]

@[simp]
theorem explicit_conductor_infinite (v : InfinitePlace ℚ) :
    (D.withExplicitConductor p r L).infinite v = D.infinite v :=
  rfl

end RAProduc

private theorem rational_height_ne
    (p q : ℕ) [Fact p.Prime] (hq : q.Prime) (hqp : q ≠ p) :
    letI : Fact q.Prime := ⟨hq⟩
    rationalIntHeight q ≠ rationalIntHeight p := by
  letI : Fact q.Prime := ⟨hq⟩
  intro h
  apply hqp
  have h' := congrArg Rat.HeightOneSpectrum.primesEquiv h
  simpa [rationalIntHeight] using congrArg Subtype.val h'

private theorem rational_padic_neg
    (p : ℕ) [Fact p.Prime] :
    Units.map (algebraMap ℚ ℚ_[p]) (-1 : ℚˣ) = (-1 : ℚ_[p]ˣ) := by
  apply Units.ext
  simp

private theorem rationalNatPadic
    (p q : ℕ) [Fact p.Prime] (hq : q ≠ 0) :
    Units.map (algebraMap ℚ ℚ_[p]) (rationalNatUnit q hq) =
      padicNatUnit p q hq := by
  apply Units.ext
  rfl

/-! ### Fully explicit away-prime and infinite maps -/

private def trivialUnitAction
    {U G : Type*} [Group U] [Group G] : U →* G where
  toFun := fun _ ↦ 1
  map_one' := rfl
  map_mul' := fun _ _ ↦ (one_mul 1).symm

/-- At a prime `q` away from the conductor, local reciprocity is trivial on
units and sends the uniformizer to arithmetic Frobenius. -/
noncomputable def explicitAwayArtin
    (p r q : ℕ) [Fact p.Prime] [Fact q.Prime] [NeZero (p ^ r)]
    (hqp : q ≠ p)
    (L : Type*) [Field L] [Algebra ℚ L]
    [IsCyclotomicExtension {p ^ r} ℚ L] :
    ℚ_[q]ˣ →* Gal(L/ℚ) :=
  let hcopPow : q.Coprime (p ^ r) :=
    ((Nat.coprime_primes (Fact.out : q.Prime) (Fact.out : p.Prime)).2 hqp)
      |>.pow_right r
  let frob := cyclotomicFrobenius
    (Polynomial.cyclotomic.irreducible_rat (NeZero.pos (p ^ r)))
    hcopPow (L := L)
  artinCommutingActions
    (Padic.mulValuation (p := q)) (q : ℚ_[q])
    (padic_prime_uniformizer q)
    (trivialUnitAction (U :=
      (Padic.mulValuation (p := q)).valuationSubring.unitGroup)
      (G := Gal(L/ℚ))) frob (fun _ ↦ Commute.one_left frob)

@[simp]
theorem explicit_away_unit
    (p r q : ℕ) [Fact p.Prime] [Fact q.Prime] [NeZero (p ^ r)]
    (hqp : q ≠ p)
    (L : Type*) [Field L] [Algebra ℚ L]
    [IsCyclotomicExtension {p ^ r} ℚ L]
    (u : (Padic.mulValuation (p := q)).valuationSubring.unitGroup) :
    explicitAwayArtin p r q hqp L (u : ℚ_[q]ˣ) = 1 := by
  let hcopPow : q.Coprime (p ^ r) :=
    ((Nat.coprime_primes (Fact.out : q.Prime) (Fact.out : p.Prime)).2 hqp)
      |>.pow_right r
  let frob := cyclotomicFrobenius
    (Polynomial.cyclotomic.irreducible_rat (NeZero.pos (p ^ r)))
    hcopPow (L := L)
  simpa [explicitAwayArtin, frob, trivialUnitAction] using
    (commuting_actions_decomposition
      (Padic.mulValuation (p := q)) (q : ℚ_[q])
      (padic_prime_uniformizer q)
      (trivialUnitAction (U :=
        (Padic.mulValuation (p := q)).valuationSubring.unitGroup)
        (G := Gal(L/ℚ))) frob (fun _ ↦ Commute.one_left frob) u 0)

@[simp]
theorem away_artin_uniformizer
    (p r q : ℕ) [Fact p.Prime] [Fact q.Prime] [NeZero (p ^ r)]
    (hqp : q ≠ p)
    (L : Type*) [Field L] [Algebra ℚ L]
    [IsCyclotomicExtension {p ^ r} ℚ L] :
    explicitAwayArtin p r q hqp L
        (padicNatUnit q q (Fact.out : q.Prime).ne_zero) =
      cyclotomicFrobenius
        (Polynomial.cyclotomic.irreducible_rat (NeZero.pos (p ^ r)))
        (((Nat.coprime_primes (Fact.out : q.Prime)
          (Fact.out : p.Prime)).2 hqp).pow_right r) (L := L) := by
  let u : (Padic.mulValuation (p := q)).valuationSubring.unitGroup := 1
  have hq : padicNatUnit q q (Fact.out : q.Prime).ne_zero =
      (u : ℚ_[q]ˣ) *
        (Units.mk0 (q : ℚ_[q]) (padic_prime_uniformizer q).ne_zero) ^
          (1 : ℤ) := by
    apply Units.ext
    simp [u, padicNatUnit]
  rw [hq]
  simpa [explicitAwayArtin, trivialUnitAction] using
    (commuting_actions_decomposition
      (Padic.mulValuation (p := q)) (q : ℚ_[q])
      (padic_prime_uniformizer q)
      (trivialUnitAction (U :=
        (Padic.mulValuation (p := q)).valuationSubring.unitGroup)
        (G := Gal(L/ℚ)))
      (cyclotomicFrobenius
        (Polynomial.cyclotomic.irreducible_rat (NeZero.pos (p ^ r)))
        (((Nat.coprime_primes (Fact.out : q.Prime)
          (Fact.out : p.Prime)).2 hqp).pow_right r) (L := L))
      (fun _ ↦ Commute.one_left _) u 1)

/-- The uniformizer formula with the rational prime supplied through an
equality.  Keeping the local index fixed avoids dependent casts between
different `Q_q` types. -/
theorem explicit_away_uniformizer
    (p r s q : ℕ) [Fact p.Prime] [Fact s.Prime] [NeZero (p ^ r)]
    (hqs : q = s) (hq : q.Prime) (hqp : q ≠ p)
    (L : Type*) [Field L] [Algebra ℚ L]
    [IsCyclotomicExtension {p ^ r} ℚ L] :
    explicitAwayArtin p r s
        (hqs ▸ hqp) L (padicNatUnit s q hq.ne_zero) =
      cyclotomicFrobenius
        (Polynomial.cyclotomic.irreducible_rat (NeZero.pos (p ^ r)))
        (((Nat.coprime_primes hq (Fact.out : p.Prime)).2 hqp).pow_right r)
        (L := L) := by
  subst q
  exact away_artin_uniformizer p r s hqp L

/-- An away-prime local map kills every integral unit coming from `Z_q`. -/
@[simp]
theorem explicit_away_artin
    (p r q : ℕ) [Fact p.Prime] [Fact q.Prime] [NeZero (p ^ r)]
    (hqp : q ≠ p)
    (L : Type*) [Field L] [Algebra ℚ L]
    [IsCyclotomicExtension {p ^ r} ℚ L]
    (u : ℤ_[q]ˣ) :
    explicitAwayArtin p r q hqp L
        (padicIntUnit q u) = 1 := by
  let v := (padicValuationInt q).symm u
  have hv : (v : ℚ_[q]ˣ) = padicIntUnit q u := rfl
  rw [← hv]
  exact explicit_away_unit p r q hqp L v

/-- Therefore a rational prime different from both the local prime and the
conductor has trivial local symbol. -/
theorem explicit_away_other
    (p r q s : ℕ) [Fact p.Prime] [Fact q.Prime] [NeZero (p ^ r)]
    (hqp : q ≠ p)
    (L : Type*) [Field L] [Algebra ℚ L]
    [IsCyclotomicExtension {p ^ r} ℚ L]
    (hs : s.Prime) (hsq : s ≠ q) :
    explicitAwayArtin p r q hqp L
        (padicNatUnit q s hs.ne_zero) = 1 := by
  let hcop : q.Coprime s :=
    (Nat.coprime_primes (Fact.out : q.Prime) hs).2 hsq.symm
  rw [← padic_int_away q s hs hsq]
  exact explicit_away_artin p r q hqp L
    (awayPadicUnit q s hcop)

/-- The prime represented by an arbitrary height-one prime of `Z`. -/
private abbrev rationalPrimeAt (P : HeightOneSpectrum ℤ) : ℕ :=
  (Rat.HeightOneSpectrum.primesEquiv P).1

private instance rational_prime_fact (P : HeightOneSpectrum ℤ) :
    Fact (rationalPrimeAt P).Prime :=
  ⟨(Rat.HeightOneSpectrum.primesEquiv P).2⟩

/-- The canonical prime-adic completion equivalence, on unit groups. -/
noncomputable def rationalAdicPadic
    (P : HeightOneSpectrum ℤ) :
    (P.adicCompletion ℚ)ˣ ≃* ℚ_[rationalPrimeAt P]ˣ :=
  Units.mapEquiv
    (Rat.HeightOneSpectrum.adicCompletion.padicEquiv P).toMulEquiv

private theorem rational_ne_height
    (p : ℕ) [Fact p.Prime] (P : HeightOneSpectrum ℤ)
    (hP : P ≠ rationalIntHeight p) :
    rationalPrimeAt P ≠ p := by
  intro h
  apply hP
  apply Rat.HeightOneSpectrum.primesEquiv.injective
  apply Subtype.ext
  change rationalPrimeAt P =
    (Rat.HeightOneSpectrum.primesEquiv (rationalIntHeight p)).1
  rw [h]
  exact congrArg Subtype.val
    (Rat.HeightOneSpectrum.primesEquiv.apply_symm_apply
      (⟨p, Fact.out⟩ : Nat.Primes)).symm

/-- The explicit unramified local map at an arbitrary rational prime away
from the conductor. -/
noncomputable def explicitAwayAdic
    (p r : ℕ) [Fact p.Prime] [NeZero (p ^ r)]
    (L : Type*) [Field L] [Algebra ℚ L]
    [IsCyclotomicExtension {p ^ r} ℚ L]
    (P : HeightOneSpectrum ℤ)
    (hP : P ≠ rationalIntHeight p) :
    (P.adicCompletion ℚ)ˣ →* Gal(L/ℚ) :=
  (explicitAwayArtin p r (rationalPrimeAt P)
      (rational_ne_height p P hP) L).comp
    (rationalAdicPadic P).toMonoidHom

@[simp]
theorem explicit_away_adic
    (p r : ℕ) [Fact p.Prime] [NeZero (p ^ r)]
    (L : Type*) [Field L] [Algebra ℚ L]
    [IsCyclotomicExtension {p ^ r} ℚ L]
    (P : HeightOneSpectrum ℤ)
    (hP : P ≠ rationalIntHeight p) (x : ℚˣ) :
    explicitAwayAdic p r L P hP
        (Units.map (algebraMap ℚ (P.adicCompletion ℚ)) x) =
      explicitAwayArtin p r (rationalPrimeAt P)
        (rational_ne_height p P hP) L
        (Units.map (algebraMap ℚ ℚ_[rationalPrimeAt P]) x) := by
  apply congrArg (explicitAwayArtin p r (rationalPrimeAt P)
    (rational_ne_height p P hP) L)
  apply Units.ext
  exact (Rat.HeightOneSpectrum.adicCompletion.padicEquiv P).commutes (x : ℚ)

/-- Away-prime maps kill the distinguished integral unit subgroup of the
rational restricted product. -/
theorem explicit_away_units
    (p r : ℕ) [Fact p.Prime] [NeZero (p ^ r)]
    (L : Type*) [Field L] [Algebra ℚ L]
    [IsCyclotomicExtension {p ^ r} ℚ L]
    (P : HeightOneSpectrum ℤ)
    (hP : P ≠ rationalIntHeight p)
    (x : (P.adicCompletion ℚ)ˣ)
    (hx : x ∈ IdeleUnitSubgroup ℤ ℚ P) :
    explicitAwayAdic p r L P hP x = 1 := by
  let e := Rat.HeightOneSpectrum.adicCompletion.padicEquiv P
  let y : ℚ_[rationalPrimeAt P]ˣ := Units.map e.toRingHom x
  have hx' := (Submonoid.mem_units_iff
    (Submonoid.ofClass (P.adicCompletionIntegers ℚ)) x).mp hx
  have hy : (y : ℚ_[rationalPrimeAt P]) ∈ PadicInt.subring (rationalPrimeAt P) := by
    exact (Rat.HeightOneSpectrum.adicCompletion.padicEquiv_bijOn P).mapsTo hx'.1
  have hyinv : ((y⁻¹ : ℚ_[rationalPrimeAt P]ˣ) :
      ℚ_[rationalPrimeAt P]) ∈ PadicInt.subring (rationalPrimeAt P) := by
    have hmap : e ((x⁻¹ : (P.adicCompletion ℚ)ˣ) : P.adicCompletion ℚ) =
        ((y⁻¹ : ℚ_[rationalPrimeAt P]ˣ) : ℚ_[rationalPrimeAt P]) := by
      simp [y]
    rw [← hmap]
    exact (Rat.HeightOneSpectrum.adicCompletion.padicEquiv_bijOn P).mapsTo hx'.2
  let u : ℤ_[rationalPrimeAt P]ˣ :=
    { val := ⟨(y : ℚ_[rationalPrimeAt P]), hy⟩
      inv := ⟨((y⁻¹ : ℚ_[rationalPrimeAt P]ˣ) :
        ℚ_[rationalPrimeAt P]), hyinv⟩
      val_inv := by
        apply Subtype.ext
        simp
      inv_val := by
        apply Subtype.ext
        simp }
  have huy : padicIntUnit (rationalPrimeAt P) u = y := by
    apply Units.ext
    rfl
  change explicitAwayArtin p r (rationalPrimeAt P)
      (rational_ne_height p P hP) L y = 1
  rw [← huy]
  exact explicit_away_artin p r
    (rationalPrimeAt P) (rational_ne_height p P hP) L u

private def realSignArtin
    {G : Type*} [Group G] (c : G) (hc : c * c = 1) : ℝˣ →* G where
  toFun x := if 0 < (x : ℝ) then 1 else c
  map_one' := by simp
  map_mul' x y := by
    by_cases hx : 0 < (x : ℝ)
    · by_cases hy : 0 < (y : ℝ)
      · simp [hx, hy, mul_pos hx hy]
      · have hyneg : (y : ℝ) < 0 :=
          lt_of_le_of_ne (le_of_not_gt hy) y.ne_zero
        have hxyneg : ((x * y : ℝˣ) : ℝ) < 0 :=
          mul_neg_of_pos_of_neg hx hyneg
        simp [hx, hy]
    · have hxneg : (x : ℝ) < 0 :=
        lt_of_le_of_ne (le_of_not_gt hx) x.ne_zero
      by_cases hy : 0 < (y : ℝ)
      · have hxyneg : ((x * y : ℝˣ) : ℝ) < 0 :=
          mul_neg_of_neg_of_pos hxneg hy
        simp [hx, hy]
      · have hyneg : (y : ℝ) < 0 :=
          lt_of_le_of_ne (le_of_not_gt hy) y.ne_zero
        have hxypos : 0 < ((x * y : ℝˣ) : ℝ) :=
          mul_pos_of_neg_of_neg hxneg hyneg
        rw [if_pos hxypos, if_neg hx, if_neg hy, hc]

/-- The real local factor: positive units act trivially and negative units
act by complex conjugation. -/
noncomputable def explicitInfiniteHom
    (p r : ℕ) [Fact p.Prime] [NeZero (p ^ r)]
    (L : Type*) [Field L] [Algebra ℚ L]
    [IsCyclotomicExtension {p ^ r} ℚ L] :
    Rat.infinitePlace.Completionˣ →* Gal(L/ℚ) :=
  (realSignArtin (cyclotomicNegAutomorphism (p ^ r) L)
      (cyclotomic_automorphism_self (p ^ r) L)).comp
    rationalInfiniteUnits.toMonoidHom

@[simp]
theorem explicit_infinite_neg
    (p r : ℕ) [Fact p.Prime] [NeZero (p ^ r)]
    (L : Type*) [Field L] [Algebra ℚ L]
    [IsCyclotomicExtension {p ^ r} ℚ L] :
    explicitInfiniteHom p r L
        (Units.map (algebraMap ℚ Rat.infinitePlace.Completion) (-1 : ℚˣ)) =
      cyclotomicNegAutomorphism (p ^ r) L := by
  change (if 0 <
      ((rationalInfiniteCompletion
        (algebraMap ℚ Rat.infinitePlace.Completion (-1 : ℚ))) : ℝ)
    then 1 else cyclotomicNegAutomorphism (p ^ r) L) = _
  have hmap : rationalInfiniteCompletion
      (algebraMap ℚ Rat.infinitePlace.Completion (-1 : ℚ)) = (-1 : ℝ) := by
    calc
      _ = algebraMap ℚ ℝ (-1 : ℚ) :=
        RingHom.map_rat_algebraMap rationalInfiniteCompletion.toRingHom (-1 : ℚ)
      _ = (-1 : ℝ) := by norm_num
  rw [hmap]
  simp

@[simp]
theorem explicit_infinite_nat
    (p r : ℕ) [Fact p.Prime] [NeZero (p ^ r)]
    (L : Type*) [Field L] [Algebra ℚ L]
    [IsCyclotomicExtension {p ^ r} ℚ L]
    (q : ℕ) (hq : q.Prime) :
    explicitInfiniteHom p r L
        (Units.map (algebraMap ℚ Rat.infinitePlace.Completion)
          (rationalNatUnit q hq.ne_zero)) = 1 := by
  change (if 0 <
      ((rationalInfiniteCompletion
        (algebraMap ℚ Rat.infinitePlace.Completion (q : ℚ))) : ℝ)
    then 1 else cyclotomicNegAutomorphism (p ^ r) L) = 1
  have hmap : rationalInfiniteCompletion
      (algebraMap ℚ Rat.infinitePlace.Completion (q : ℚ)) = (q : ℝ) := by
    calc
      _ = algebraMap ℚ ℝ (q : ℚ) :=
        RingHom.map_rat_algebraMap rationalInfiniteCompletion.toRingHom (q : ℚ)
      _ = (q : ℝ) := by norm_num
  rw [hmap]
  simp [hq.pos]

@[simp]
private theorem rational_int_height
    (q : ℕ) [Fact q.Prime] :
    rationalPrimeAt (rationalIntHeight q) = q := by
  exact congrArg Subtype.val
    (Rat.HeightOneSpectrum.primesEquiv.apply_symm_apply
      (⟨q, Fact.out⟩ : Nat.Primes))

private theorem rational_int_neg
    (q : ℕ) [Fact q.Prime] :
    Units.map (algebraMap ℚ ℚ_[q]) (-1 : ℚˣ) =
      padicIntUnit q (-1 : ℤ_[q]ˣ) := by
  apply Units.ext
  simp

/-- The literal family of local maps used in Example VII.8.2: inverse-unit
Lubin--Tate reciprocity at `p`, valuation--Frobenius reciprocity away from
`p`, and the sign character at infinity. -/
noncomputable def explicitArtinProduct
    (p r : ℕ) [Fact p.Prime] [NeZero (p ^ r)]
    (L : Type*) [Field L] [Algebra ℚ L]
    [IsCyclotomicExtension {p ^ r} ℚ L] :
    RAProduc Gal(L/ℚ) := by
  classical
  exact
    { commutative :=
        IsCyclotomicExtension.isMulCommutative {p ^ r} ℚ L
      finiteLocalHom := fun P ↦
        if hP : P = rationalIntHeight p then
          hP ▸ explicitConductorAdic p r L
        else explicitAwayAdic p r L P hP
      eventually_units := by
        have hp : ∀ᶠ P in Filter.cofinite,
            P ≠ rationalIntHeight p := by
          rw [Filter.eventually_cofinite]
          simp
        filter_upwards [hp] with P hP
        intro x hx
        rw [dif_neg hP]
        exact explicit_away_units p r L P hP x hx
      infinite := fun v ↦
        (Subsingleton.elim v Rat.infinitePlace) ▸
          explicitInfiniteHom p r L }

namespace EAProduc

variable
    (p r : ℕ) [Fact p.Prime] [NeZero (p ^ r)]
    (L : Type*) [Field L] [Algebra ℚ L]
    [IsCyclotomicExtension {p ^ r} ℚ L]

@[simp]
theorem local_hom_conductor :
    (explicitArtinProduct p r L).finiteLocalHom
        (rationalIntHeight p) =
      explicitConductorAdic p r L := by
  simp [explicitArtinProduct]

theorem local_hom_ne
    (P : HeightOneSpectrum ℤ)
    (hP : P ≠ rationalIntHeight p) :
    (explicitArtinProduct p r L).finiteLocalHom P =
      explicitAwayAdic p r L P hP := by
  simp [explicitArtinProduct, hP]

@[simp]
theorem infinite_rational :
    (explicitArtinProduct p r L).infinite
        Rat.infinitePlace = explicitInfiniteHom p r L := by
  rfl

end EAProduc

/-- The fully constructed explicit product satisfies all placewise formulas
consumed by the prime-power calculation. -/
noncomputable def explicitPrimeData
    (p r : ℕ) [Fact p.Prime] [NeZero (p ^ r)]
    (L : Type) [Field L] [NumberField L]
    [IsCyclotomicExtension {p ^ r} ℚ L] :
    CPData p r L
      (explicitArtinProduct p r L) where
  infinite_neg_one := by
    rw [EAProduc.infinite_rational]
    exact explicit_infinite_neg p r L
  infinite_nat q hq := by
    rw [EAProduc.infinite_rational]
    exact explicit_infinite_nat p r L q hq
  finite_neg_one P := by
    by_cases hP : P = rationalIntHeight p
    · subst P
      rw [EAProduc.local_hom_conductor,
        explicit_conductor_adic,
        rational_padic_neg, if_pos rfl]
    · rw [EAProduc.local_hom_ne
          p r L P hP,
        explicit_away_adic,
        rational_int_neg,
        explicit_away_artin]
      simp [hP]
  finite_conductor P := by
    by_cases hP : P = rationalIntHeight p
    · subst P
      rw [EAProduc.local_hom_conductor,
        explicit_conductor_adic,
        rationalNatPadic, if_pos rfl]
    · rw [EAProduc.local_hom_ne
          p r L P hP,
        explicit_away_adic,
        rationalNatPadic]
      have hpq : p ≠ rationalPrimeAt P := by
        intro hpq
        exact rational_ne_height p P hP hpq.symm
      rw [explicit_away_other p r
        (rationalPrimeAt P) p
        (rational_ne_height p P hP) L
        (Fact.out : p.Prime) hpq]
      simp [hP]
  finite_away q hq hqp := by
    letI : Fact q.Prime := ⟨hq⟩
    let hPqp : rationalIntHeight q ≠
        rationalIntHeight p :=
      rational_height_ne p q hq hqp
    dsimp only
    intro P
    by_cases hPq : P = rationalIntHeight q
    · subst P
      rw [EAProduc.local_hom_ne
          p r L (rationalIntHeight q) hPqp,
        explicit_away_adic,
        rationalNatPadic]
      have hlocal := explicit_away_uniformizer
        p r (rationalPrimeAt (rationalIntHeight q)) q
        (rational_int_height q).symm hq hqp L
      rw [hlocal, if_pos rfl]
    · by_cases hPp : P = rationalIntHeight p
      · subst P
        rw [EAProduc.local_hom_conductor,
          explicit_conductor_adic,
          rationalNatPadic, if_neg hPq, if_pos rfl]
      · rw [EAProduc.local_hom_ne
            p r L P hPp,
          explicit_away_adic,
          rationalNatPadic]
        have hqP : q ≠ rationalPrimeAt P := by
          intro hqP
          apply hPq
          apply Rat.HeightOneSpectrum.primesEquiv.injective
          apply Subtype.ext
          change rationalPrimeAt P =
            (Rat.HeightOneSpectrum.primesEquiv
              (rationalIntHeight q)).1
          calc
            rationalPrimeAt P = q := hqP.symm
            _ = (Rat.HeightOneSpectrum.primesEquiv
                (rationalIntHeight q)).1 :=
              congrArg Subtype.val
                (Rat.HeightOneSpectrum.primesEquiv.apply_symm_apply
                  (⟨q, hq⟩ : Nat.Primes)).symm
        rw [explicit_away_other p r
          (rationalPrimeAt P) q
          (rational_ne_height p P hPp) L hq hqP]
        simp [hPq, hPp]

/-- A chosen completion of a rational prime-power cyclotomic field above its
conductor prime.  The canonical local Artin map is independent of this
choice; keeping the choice bundled here makes the resulting local-factor
record completely closed. -/
noncomputable def primeConductorPlace
    (p r : ℕ) [Fact p.Prime] [NeZero (p ^ r)]
    (L : Type) [Field L] [NumberField L]
    [IsCyclotomicExtension {p ^ r} ℚ L] :
    CompletionPlacesAbove (L := L)
      (FinitePlace.mk (rationalHeightOne p)).val := by
  let v := (FinitePlace.mk (rationalHeightOne p)).val
  letI : Fact v.IsNontrivial :=
    ⟨absolute_value_nontrivial (rationalHeightOne p)⟩
  letI : IsUltrametricDist v.Completion :=
    placeUltrametricDist (rationalHeightOne p)
  exact Classical.choice
    (absolute_value_extension (K := ℚ) (L := L) v)

/-- The fully constructed prime-power product also supplies the genuinely
canonical local-factor record.  At the conductor this is exactly the
cohomological Proposition III.3.6 map, by the proved cyclotomic
normalization; the away and infinite coordinates are the unramified
Frobenius and sign factors already calculated above. -/
noncomputable def canonicalFactorData
    (p r : ℕ) [Fact p.Prime] [NeZero (p ^ r)]
    (L : Type) [Field L] [NumberField L]
    [IsCyclotomicExtension {p ^ r} ℚ L] :
    CFData p r L
      (explicitArtinProduct p r L) where
  conductorPlace := primeConductorPlace p r L
  infinite_neg_one :=
    (explicitPrimeData p r L).infinite_neg_one
  infinite_nat :=
    (explicitPrimeData p r L).infinite_nat
  finite_neg_one P := by
    rw [(explicitPrimeData p r L).finite_neg_one P]
    split_ifs
    · rw [canonicalPadicNormalization p r L
        (primeConductorPlace p r L)]
    · rfl
  finite_conductor P := by
    rw [(explicitPrimeData p r L).finite_conductor P]
    split_ifs
    · rw [canonicalPadicNormalization p r L
        (primeConductorPlace p r L)]
    · rfl
  finite_away q hq hqp := by
    letI : Fact q.Prime := ⟨hq⟩
    dsimp only
    intro P
    rw [(explicitPrimeData p r L).finite_away q hq hqp P]
    split_ifs
    · rfl
    · rw [canonicalPadicNormalization p r L
        (primeConductorPlace p r L)]
    · rfl

/-- The constructed explicit product supplies the literal prime-power data
with no record-valued input. -/
noncomputable def explicitActualLocal
    (p r : ℕ) [Fact p.Prime] [NeZero (p ^ r)]
    (L : Type) [Field L] [NumberField L]
    [IsCyclotomicExtension {p ^ r} ℚ L] :
    PAData p r L
      (explicitArtinProduct p r L).artin :=
  (explicitPrimeData p r L).primeActualData
    p r L (explicitArtinProduct p r L)

/-- **Example VII.8.2, completely explicit prime-power product.** -/
theorem principal_reciprocity_explicit
    (p r : ℕ) [Fact p.Prime] [NeZero (p ^ r)]
    (L : Type) [Field L] [NumberField L]
    [IsCyclotomicExtension {p ^ r} ℚ L] :
    ∀ x : ℚˣ,
      (explicitArtinProduct p r L).artin
        (principalIdele ℤ ℚ x) = 1 :=
  reciprocity_actual_factors
    p r L (explicitArtinProduct p r L).artin
      (explicitActualLocal p r L)

namespace CFData

/-- Canonical away/infinite calculations, with the conductor coordinate
replaced by Milne's explicit local map, give the fully explicit factor
record without a cohomological normalization assumption. -/
theorem explicitFactorData
    (p r : ℕ) [Fact p.Prime] [NeZero (p ^ r)]
    (L : Type) [Field L] [NumberField L]
    [IsCyclotomicExtension {p ^ r} ℚ L]
    (D : RAProduc Gal(L/ℚ))
    (C : CFData p r L D) :
    CPData p r L
      (D.withExplicitConductor p r L) where
  infinite_neg_one := by simpa using C.infinite_neg_one
  infinite_nat q hq := by simpa using C.infinite_nat q hq
  finite_neg_one P := by
    by_cases hP : P = rationalIntHeight p
    · subst P
      rw [RAProduc.explicit_conductor_hom,
        explicit_conductor_adic,
        rational_padic_neg, if_pos rfl]
    · rw [RAProduc.explicit_conductor_ne
          p r L D P hP,
        C.finite_neg_one P]
      simp [hP]
  finite_conductor P := by
    by_cases hP : P = rationalIntHeight p
    · subst P
      rw [RAProduc.explicit_conductor_hom,
        explicit_conductor_adic,
        rationalNatPadic, if_pos rfl]
    · rw [RAProduc.explicit_conductor_ne
          p r L D P hP,
        C.finite_conductor P]
      simp [hP]
  finite_away q hq hqp := by
    letI : Fact q.Prime := ⟨hq⟩
    let hpq : rationalIntHeight p ≠
        rationalIntHeight q :=
      (rational_height_ne p q hq hqp).symm
    dsimp only
    intro P
    by_cases hPp : P = rationalIntHeight p
    · subst P
      rw [RAProduc.explicit_conductor_hom,
        explicit_conductor_adic,
        rationalNatPadic, if_neg hpq, if_pos rfl]
    · rw [RAProduc.explicit_conductor_ne
          p r L D P hPp,
        C.finite_away q hq hqp P]
      simp [hPp]

/-- The literal three local products of Example VII.8.2, now with no
`CanonicalPadicNormalization` argument. -/
theorem explicitActualData
    (p r : ℕ) [Fact p.Prime] [NeZero (p ^ r)]
    (L : Type) [Field L] [NumberField L]
    [IsCyclotomicExtension {p ^ r} ℚ L]
    (D : RAProduc Gal(L/ℚ))
    (C : CFData p r L D) :
    PAData p r L
      (D.withExplicitConductor p r L).artin :=
  (C.explicitFactorData p r L D)
    |>.primeActualData p r L (D.withExplicitConductor p r L)

end CFData

/-- **Example VII.8.2, explicit prime-power form.**  The product whose
conductor factor is Milne's inverse-unit Lubin--Tate map is trivial on every
rational principal idèle.  No local-normalization proposition is assumed. -/
theorem prime_reciprocity_explicit
    (p r : ℕ) [Fact p.Prime] [NeZero (p ^ r)]
    (L : Type) [Field L] [NumberField L]
    [IsCyclotomicExtension {p ^ r} ℚ L]
    (D : RAProduc Gal(L/ℚ))
    (C : CFData p r L D) :
    ∀ x : ℚˣ,
      (D.withExplicitConductor p r L).artin
        (principalIdele ℤ ℚ x) = 1 :=
  reciprocity_actual_factors
    p r L (D.withExplicitConductor p r L).artin
      (C.explicitActualData p r L D)

end

end Towers.CField.RExist
