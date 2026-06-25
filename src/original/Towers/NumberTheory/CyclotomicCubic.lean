import Towers.NumberTheory.Ramification
import Towers.Group.CyclicSubgroup


open Filter
open scoped Pointwise EuclideanGeometry Topology

noncomputable section

open NumberField

namespace Towers

section CyclotomicCubicConstruction

variable {r : ℕ}
variable {K : Type*} [Field K] [NumberField K] [Algebra ℚ K]
variable [IsCyclotomicExtension {r} ℚ K]

/--
Inside a prime-conductor cyclotomic field, we call an intermediate field a Galois cubic subfield
if it has degree `3` over `ℚ` and is Galois over `ℚ`.

For a degree-`3` Galois extension of `ℚ`, the Galois group automa has order `3`, hence is
cyclic, so this captures the "cyclic cubic subfield" appearing in `CyclotomicCubicConstruction.tex`.
-/
def GaloisCubicSubfield (E : IntermediateField ℚ K) : Prop :=
  Module.finrank ℚ ↥E = 3 ∧ @IsGalois ℚ _ ↥E _ E.algebra'

/--
If `r` is a rational prime with `r ≡ 1 [MOD 3]`, then any `r`-th cyclotomic extension of `ℚ`
contains a unique Galois cubic intermediate field.
-/
theorem unique_cubic_subfield
    (hrp : Nat.Prime r) (hr3 : r ≡ 1 [MOD 3]) :
    ∃! E : IntermediateField ℚ K, GaloisCubicSubfield E := by
  have h_alg : (DivisionRing.toRatAlgebra : Algebra ℚ K) = ‹Algebra ℚ K› :=
    Subsingleton.elim _ _
  cases h_alg
  haveI : NeZero r := ⟨hrp.ne_zero⟩
  letI : IsGalois ℚ K := IsCyclotomicExtension.isGalois (S := {r}) (K := ℚ) (L := K)
  let e := IsCyclotomicExtension.Rat.galEquivZMod r K
  haveI : IsCyclic (Gal(K/ℚ)) := (e.isCyclic).mpr (ZMod.isCyclic_units_prime hrp)
  letI : CommGroup (Gal(K/ℚ)) := IsCyclic.commGroup
  have hcard_gal : Nat.card (Gal(K/ℚ)) = r - 1 := by
    calc
      Nat.card (Gal(K/ℚ)) = Nat.card ((ZMod r)ˣ) := Nat.card_congr e.toEquiv
      _ = Fintype.card ((ZMod r)ˣ) := Nat.card_eq_fintype_card
      _ = Nat.totient r := ZMod.card_units_eq_totient r
      _ = r - 1 := Nat.totient_prime hrp
  have hdiv3 : 3 ∣ Nat.card (Gal(K/ℚ)) := by
    rw [hcard_gal]
    exact (Nat.modEq_iff_dvd' hrp.one_le).mp hr3.symm
  obtain ⟨H, hHidx, hHuniq⟩ :=
    unique_index_three (G := Gal(K/ℚ)) hdiv3
  refine ⟨IntermediateField.fixedField H, ?_, ?_⟩
  · constructor
    · rw [IntermediateField.finrank_eq_fixingSubgroup_index (L := IntermediateField.fixedField H),
        IntermediateField.fixingSubgroup_fixedField, hHidx]
    · letI : H.Normal := by infer_instance
      infer_instance
  · intro E hE
    rcases hE with ⟨hE_deg, _hE_gal⟩
    have hE_idx : E.fixingSubgroup.index = 3 := by
      rw [← hE_deg, IntermediateField.finrank_eq_fixingSubgroup_index (L := E)]
    have hfix : E.fixingSubgroup = H := hHuniq E.fixingSubgroup hE_idx
    calc
      E = IntermediateField.fixedField E.fixingSubgroup := by
        symm
        exact IsGalois.fixedField_fixingSubgroup E
      _ = IntermediateField.fixedField H := by rw [hfix]

/--
The canonical cubic subfield singled out by `unique_cubic_subfield`.
-/
noncomputable def galoisCubicSubfield
    (hrp : Nat.Prime r) (hr3 : r ≡ 1 [MOD 3]) : IntermediateField ℚ K :=
  Classical.choose (unique_cubic_subfield (K := K) hrp hr3)

/--
The canonical cubic subfield is indeed Galois and cubic over `ℚ`.
-/
theorem galois_subfield_spec
    (hrp : Nat.Prime r) (hr3 : r ≡ 1 [MOD 3]) :
    GaloisCubicSubfield (galoisCubicSubfield (K := K) hrp hr3) := by
  exact (Classical.choose_spec (unique_cubic_subfield (K := K) hrp hr3)).1

/--
Any Galois cubic intermediate field coincides with the canonical one.
-/
theorem galois_cubic_subfield
    (hrp : Nat.Prime r) (hr3 : r ≡ 1 [MOD 3])
    {E : IntermediateField ℚ K} (hE : GaloisCubicSubfield E) :
    E = galoisCubicSubfield (K := K) hrp hr3 := by
  exact (Classical.choose_spec (unique_cubic_subfield (K := K) hrp hr3)).2 E hE

/--
Every prime of the cubic subfield above `(r)` has ramification index exactly `3`.

This is stronger than merely saying the field is tamely ramified at `r`, and it is the most
useful arithmetic input for later arguments.
-/
theorem subfield_ramification_idx
    (hrp : Nat.Prime r) (hr3 : r ≡ 1 [MOD 3]) :
    RationalRamificationIdx
      (S := 𝓞 ↥(galoisCubicSubfield (K := K) hrp hr3)) r 3 := by
  have h_alg : (DivisionRing.toRatAlgebra : Algebra ℚ K) = ‹Algebra ℚ K› :=
    Subsingleton.elim _ _
  cases h_alg
  let E := galoisCubicSubfield (K := K) hrp hr3
  letI : Algebra ℚ ↥E := E.algebra'
  haveI : NeZero r := ⟨hrp.ne_zero⟩
  letI : Fact (Nat.Prime r) := ⟨hrp⟩
  letI : IsCyclotomicExtension {r} ℚ K := ‹IsCyclotomicExtension {r} ℚ K›
  letI : IsGalois ℚ K := IsCyclotomicExtension.isGalois (S := {r}) (K := ℚ) (L := K)
  rcases galois_subfield_spec (K := K) hrp hr3 with ⟨hE_deg, hE_gal⟩
  letI : IsGalois ℚ ↥E := hE_gal
  letI := IsIntegralClosure.MulSemiringAction ℤ ℚ ↥E (𝓞 ↥E)
  letI := IsIntegralClosure.MulSemiringAction ℤ ℚ K (𝓞 K)
  letI := IsIntegralClosure.MulSemiringAction (𝓞 ↥E) ↥E K (𝓞 K)
  letI : IsGaloisGroup Gal(↥E/ℚ) ℤ (𝓞 ↥E) :=
    IsGaloisGroup.of_isFractionRing (G := Gal(↥E/ℚ)) (A := ℤ)
      (B := 𝓞 ↥E) (K := ℚ) (L := ↥E)
  letI : IsGaloisGroup Gal(K/ℚ) ℤ (𝓞 K) :=
    IsGaloisGroup.of_isFractionRing (G := Gal(K/ℚ)) (A := ℤ)
      (B := 𝓞 K) (K := ℚ) (L := K)
  letI : IsGaloisGroup Gal(K / ↥E) (𝓞 ↥E) (𝓞 K) :=
    IsGaloisGroup.of_isFractionRing (G := Gal(K / ↥E)) (A := 𝓞 ↥E)
      (B := 𝓞 K) (K := ↥E) (L := K)
  let rI : Ideal ℤ := Ideal.rationalPrimeIdeal r
  have hrI0 : rI ≠ ⊥ := rational_ne_bot hrp
  letI : rI.IsMaximal := rational_ideal_maximal hrp
  have hcountK : (rI.primesOver (𝓞 K)).ncard = 1 := by
    simpa [rI, Ideal.rationalPrimeIdeal] using
      IsCyclotomicExtension.Rat.ncard_primesOver_of_prime (p := r) (K := K)
  have hinertiaK : rI.inertiaDegIn (𝓞 K) = 1 := by
    simpa [rI, Ideal.rationalPrimeIdeal] using
      IsCyclotomicExtension.Rat.inertiaDegIn_eq_of_prime (p := r) (K := K)
  intro P hP
  letI : P.IsPrime := hP.1
  letI : P.LiesOver rI := hP.2
  letI : P.IsMaximal := Ideal.IsMaximal.of_liesOver_isMaximal (p := rI) (P := P)
  have hcountE : (rI.primesOver (𝓞 ↥E)).ncard = 1 := by
    have hcountTower :=
      Ideal.ncard_primesOver_mul_ncard_primesOver
        (p := rI) P (Gal(↥E/ℚ)) (𝓞 K) (Gal(K/ℚ)) (Gal(K/↥E)) hrI0
    have hcountTower1 :
        (rI.primesOver (𝓞 ↥E)).ncard * (P.primesOver (𝓞 K)).ncard = 1 := by
      rwa [hcountK] at hcountTower
    exact Nat.eq_one_of_mul_eq_one_right hcountTower1
  have hinertiaE : rI.inertiaDegIn (𝓞 ↥E) = 1 := by
    have hmul :=
      Ideal.inertiaDegIn_mul_inertiaDegIn
        (p := rI) P (Gal(↥E/ℚ)) (𝓞 K) (Gal(K/ℚ)) (Gal(K/↥E))
    have hmul1 : rI.inertiaDegIn (𝓞 ↥E) * P.inertiaDegIn (𝓞 K) = 1 := by
      rwa [hinertiaK] at hmul
    exact Nat.eq_one_of_mul_eq_one_right hmul1
  have hcardE : Nat.card Gal(↥E/ℚ) = Module.finrank ℚ ↥E := by
    simpa using IsGaloisGroup.card_eq_finrank (G := Gal(↥E/ℚ)) (K := ℚ) (L := ↥E)
  have hramEIn : rI.ramificationIdxIn (𝓞 ↥E) = 3 := by
    have hfund :=
      Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn
        (p := rI) hrI0 (𝓞 ↥E) (Gal(↥E/ℚ))
    rw [hcardE, hE_deg, hcountE, hinertiaE] at hfund
    simpa using hfund
  calc
    Ideal.ramificationIdx rI P
      = rI.ramificationIdxIn (𝓞 ↥E) := by
          symm
          exact Ideal.ramificationIdxIn_eq_ramificationIdx
            (p := rI) (P := P) (G := Gal(↥E/ℚ))
    _ = 3 := hramEIn

/--
At every prime ideal above `(r)`, the ramification index is coprime to `r`.

This is the usual prime-ideal-level tame ramification conclusion; it follows immediately from the
exact ramification index computation.
-/
theorem subfield_coprime_r
    (hrp : Nat.Prime r) (hr3 : r ≡ 1 [MOD 3]) :
    ∀ P ∈ Ideal.primesOver (Ideal.rationalPrimeIdeal r)
        (𝓞 ↥(galoisCubicSubfield (K := K) hrp hr3)),
      Nat.Coprime r
        (Ideal.ramificationIdx (Ideal.rationalPrimeIdeal r) P) := by
  intro P hP
  have hram :
      Ideal.ramificationIdx (Ideal.rationalPrimeIdeal r) P = 3 :=
    subfield_ramification_idx (K := K) hrp hr3 P hP
  have hcop : Nat.Coprime r 3 := by
    rw [hrp.coprime_iff_not_dvd]
    intro hdiv
    have hr_eq : r = 3 := (Nat.prime_dvd_prime_iff_eq hrp Nat.prime_three).mp hdiv
    have hnot : ¬ 3 ≡ 1 [MOD 3] := by decide
    exact hnot (by simpa [hr_eq] using hr3)
  rw [hram]
  exact hcop

/--
Every rational prime `q ≠ r` is unramified in the cubic subfield.
-/
theorem galois_subfield_away
    (hrp : Nat.Prime r) (hr3 : r ≡ 1 [MOD 3])
    {q : ℕ} (hq : Nat.Prime q) (hqr : q ≠ r) :
    RationalPrimeUnramified
      (S := 𝓞 ↥(galoisCubicSubfield (K := K) hrp hr3)) q := by
  have h_alg : (DivisionRing.toRatAlgebra : Algebra ℚ K) = ‹Algebra ℚ K› :=
    Subsingleton.elim _ _
  cases h_alg
  let E := galoisCubicSubfield (K := K) hrp hr3
  letI : Algebra ℚ ↥E := E.algebra'
  haveI : NeZero r := ⟨hrp.ne_zero⟩
  letI : Fact (Nat.Prime q) := ⟨hq⟩
  letI : IsCyclotomicExtension {r} ℚ K := ‹IsCyclotomicExtension {r} ℚ K›
  letI : IsGalois ℚ K := IsCyclotomicExtension.isGalois (S := {r}) (K := ℚ) (L := K)
  rcases galois_subfield_spec (K := K) hrp hr3 with ⟨_hE_deg, hE_gal⟩
  letI : IsGalois ℚ ↥E := hE_gal
  letI := IsIntegralClosure.MulSemiringAction ℤ ℚ ↥E (𝓞 ↥E)
  letI := IsIntegralClosure.MulSemiringAction ℤ ℚ K (𝓞 K)
  letI := IsIntegralClosure.MulSemiringAction (𝓞 ↥E) ↥E K (𝓞 K)
  letI : IsGaloisGroup Gal(↥E/ℚ) ℤ (𝓞 ↥E) :=
    IsGaloisGroup.of_isFractionRing (G := Gal(↥E/ℚ)) (A := ℤ)
      (B := 𝓞 ↥E) (K := ℚ) (L := ↥E)
  letI : IsGaloisGroup Gal(K/ℚ) ℤ (𝓞 K) :=
    IsGaloisGroup.of_isFractionRing (G := Gal(K/ℚ)) (A := ℤ)
      (B := 𝓞 K) (K := ℚ) (L := K)
  letI : IsGaloisGroup Gal(K / ↥E) (𝓞 ↥E) (𝓞 K) :=
    IsGaloisGroup.of_isFractionRing (G := Gal(K / ↥E)) (A := 𝓞 ↥E)
      (B := 𝓞 K) (K := ↥E) (L := K)
  let qI : Ideal ℤ := Ideal.rationalPrimeIdeal q
  have hqI0 : qI ≠ ⊥ := rational_ne_bot hq
  letI : qI.IsMaximal := rational_ideal_maximal hq
  have hqndvd : ¬ q ∣ r := by
    intro hdiv
    exact hqr ((Nat.prime_dvd_prime_iff_eq hq hrp).mp hdiv)
  have hramK : qI.ramificationIdxIn (𝓞 K) = 1 := by
    simpa [qI, Ideal.rationalPrimeIdeal] using
      IsCyclotomicExtension.Rat.ramificationIdxIn_eq_of_not_dvd
        (m := r) (p := q) (K := K) hqndvd
  intro P hP
  letI : P.IsPrime := hP.1
  letI : P.LiesOver qI := hP.2
  letI : P.IsMaximal := Ideal.IsMaximal.of_liesOver_isMaximal (p := qI) (P := P)
  have hmul :=
    Ideal.ramificationIdxIn_mul_ramificationIdxIn'
      (p := qI) P (Gal(↥E/ℚ)) (𝓞 K) (Gal(K/ℚ)) (Gal(K/↥E))
  have hramEIn : qI.ramificationIdxIn (𝓞 ↥E) = 1 := by
    have hmul1 : qI.ramificationIdxIn (𝓞 ↥E) * P.ramificationIdxIn (𝓞 K) = 1 := by
      rwa [hramK] at hmul
    exact Nat.eq_one_of_mul_eq_one_right hmul1
  calc
    Ideal.ramificationIdx qI P
      = qI.ramificationIdxIn (𝓞 ↥E) := by
          symm
          exact Ideal.ramificationIdxIn_eq_ramificationIdx
            (p := qI) (P := P) (G := Gal(↥E/ℚ))
    _ = 1 := hramEIn

/--
If a rational prime is unramified in a finite Galois extension `K/ℚ`, then it is already
unramified in every finite Galois intermediate field.
-/
theorem rational_unramified_intermediate
    {K : Type*} [Field K] [NumberField K] [Algebra ℚ K] [IsGalois ℚ K]
    (E : IntermediateField ℚ K) [FiniteDimensional ℚ ↥E] [IsGalois ℚ ↥E]
    {q : ℕ} (hq : Nat.Prime q)
    (hK_unram : RationalPrimeUnramified (S := 𝓞 K) q) :
    RationalPrimeUnramified (S := 𝓞 ↥E) q := by
  letI : Algebra ℚ ↥E := E.algebra'
  let qI : Ideal ℤ := Ideal.rationalPrimeIdeal q
  intro P hP
  letI : P.IsPrime := hP.1
  letI : P.LiesOver qI := hP.2
  obtain ⟨⟨Q, hQprime, hQoverP⟩⟩ := P.nonempty_primesOver (S := 𝓞 K)
  letI : Q.IsPrime := hQprime
  letI : Q.LiesOver P := hQoverP
  letI : Q.LiesOver qI := Ideal.LiesOver.trans Q P qI
  have hQ0 : Q ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot
    (rational_ne_bot hq) Q
  letI : Algebra.IsUnramifiedAt ℤ Q := by
    have hramQ :
        Ideal.ramificationIdx (Ideal.under ℤ Q) Q = 1 := by
      rw [← Ideal.LiesOver.over (P := Q) (p := qI)]
      exact hK_unram Q ⟨hQprime, inferInstance⟩
    exact (Algebra.isUnramifiedAt_iff_of_isDedekindDomain
      (R := ℤ) (S := 𝓞 K) (p := Q) hQ0).2 hramQ
  letI : Algebra.IsUnramifiedAt ℤ P :=
    Algebra.IsUnramifiedAt.of_liesOver (R := ℤ) P Q
  have hP0 : P ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot
    (rational_ne_bot hq) P
  have hramP :
      Ideal.ramificationIdx (Ideal.under ℤ P) P = 1 :=
    (Algebra.isUnramifiedAt_iff_of_isDedekindDomain
      (R := ℤ) (S := 𝓞 ↥E) (p := P) hP0).1
        (show Algebra.IsUnramifiedAt ℤ P from inferInstance)
  rw [← Ideal.LiesOver.over (P := P) (p := qI)] at hramP
  exact hramP



/--
The canonical cubic subfield is totally real.
-/
theorem subfield_totally_real
    (hrp : Nat.Prime r) (hr3 : r ≡ 1 [MOD 3]) :
    NumberField.IsTotallyReal ↥(galoisCubicSubfield (K := K) hrp hr3) := by
  let E := galoisCubicSubfield (K := K) hrp hr3
  letI : Algebra ℚ ↥E := E.algebra'
  rcases galois_subfield_spec (K := K) hrp hr3 with ⟨hE_deg, hE_gal⟩
  letI : IsGalois ℚ ↥E := hE_gal
  letI : IsUnramifiedAtInfinitePlaces ℚ ↥E := by
    have hodd : Odd (Module.finrank ℚ ↥E) := by
      rw [hE_deg]
      decide
    exact IsUnramifiedAtInfinitePlaces_of_odd_finrank (k := ℚ) (K := ↥E) hodd
  refine (NumberField.isTotallyReal_iff ↥E).2 ?_
  intro w
  have hw_unram : w.IsUnramified ℚ := NumberField.InfinitePlace.isUnramified (k := ℚ) w
  have hbase_real : (w.comap (algebraMap ℚ ↥E)).IsReal := by
    exact NumberField.IsTotallyReal.isReal _
  exact ((NumberField.InfinitePlace.isUnramified_iff (k := ℚ) (w := w)).1 hw_unram).resolve_right
    ((NumberField.InfinitePlace.not_isComplex_iff_isReal).2 hbase_real)

end CyclotomicCubicConstruction

end Towers
