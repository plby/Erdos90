import Towers.ClassField.RayClassGroups.Frobenius
import Towers.ClassField.KummerNormIndex.GalMLMK
import Towers.ClassField.BrauerLocalization.CokernelAssembly

/-!
# The local completion/restriction step in Lemma VII.6.2

At a prime unramified in `M / K`, the order of Frobenius is the residue
degree.  The exponent-`p` hypothesis therefore bounds the residue degree of
`M / K` by `p`.  A nontrivial Frobenius for `M / L` already has order `p`,
so multiplicativity of residue degrees forces the residue degree of `L / K`
to be one.  The Frobenius tower formula then gives the desired equality.
-/

namespace Towers.CField.KNIndex

open IsDedekindDomain NumberField
open Towers.NumberTheory.Milne
open Towers.CField.RCGroups
open Towers.CField.Ideles
open Towers.CField.NIndex

noncomputable section

universe u

private abbrev OK (F : Type u) [Field F] [NumberField F] :=
  NumberField.RingOfIntegers F

set_option synthInstance.maxHeartbeats 500000 in
-- The proof carries the two integral-closure Galois actions simultaneously.
set_option maxHeartbeats 3000000 in
/-- The local Frobenius equality used in the proof of Lemma VII.6.2. -/
theorem completionRestrictionBridge :
    CompletionRestrictionBridge.{u} := by
  classical
  intro p hp K L M
    _ _ _
    _ _ _
    _ _ _
    _
    _ _
    _ _
    hexponent S hunramified Q hQnotS hFrobNe
  letI : Fact p.Prime := ⟨hp⟩
  letI : MulSemiringAction Gal(M/K) (OK M) :=
    IsIntegralClosure.MulSemiringAction (OK K) K M (OK M)
  letI : IsGaloisGroup Gal(M/K) (OK K) (OK M) :=
    IsGaloisGroup.of_isFractionRing Gal(M/K) (OK K) (OK M) K M
  letI : MulSemiringAction Gal(M/L) (OK M) :=
    IsIntegralClosure.MulSemiringAction (OK L) L M (OK M)
  letI : IsGaloisGroup Gal(M/L) (OK L) (OK M) :=
    IsGaloisGroup.of_isFractionRing Gal(M/L) (OK L) (OK M) L M
  let qL : Ideal (OK L) := Q.asIdeal.under (OK L)
  let qK : Ideal (OK K) := Q.asIdeal.under (OK K)
  letI : Q.asIdeal.LiesOver qL := ⟨rfl⟩
  letI : qL.LiesOver qK := ⟨by
    dsimp only [qK, qL]
    exact (Ideal.under_under Q.asIdeal).symm⟩
  letI : Algebra.IsUnramifiedAt (OK K) Q.asIdeal :=
    hunramified Q hQnotS
  letI : Algebra.IsUnramifiedAt (OK L) Q.asIdeal :=
    Algebra.IsUnramifiedAt.of_restrictScalars (OK K) Q.asIdeal
  let frobK : Gal(M/K) := numberFrobeniusElement (K := K) Q
  let frobL : Gal(M/L) := numberFrobeniusElement (K := L) Q
  have hfrobL_pow : frobL ^ p = 1 :=
    gal_ml_pow (K := K) (L := L) (M := M) p hexponent frobL
  have hfrobL_order : orderOf frobL = p :=
    orderOf_eq_prime hfrobL_pow hFrobNe
  have horderL : orderOf frobL = qL.inertiaDeg Q.asIdeal := by
    simpa only [frobL, qL, numberFrobeniusElement] using
      (frob_inertia_deg
        (R := OK L) (S := OK M) (G := Gal(M/L)) Q.asIdeal)
  have hdegreeL : qL.inertiaDeg Q.asIdeal = p := by
    rw [← horderL, hfrobL_order]
  have hfrobK_pow : frobK ^ p = 1 := hexponent frobK
  have horderK : orderOf frobK = qK.inertiaDeg Q.asIdeal := by
    simpa only [frobK, qK, numberFrobeniusElement] using
      (frob_inertia_deg
        (R := OK K) (S := OK M) (G := Gal(M/K)) Q.asIdeal)
  have hdegreeK_dvd : qK.inertiaDeg Q.asIdeal ∣ p := by
    rw [← horderK]
    exact orderOf_dvd_of_pow_eq_one hfrobK_pow
  have htower : qK.inertiaDeg Q.asIdeal =
      qK.inertiaDeg qL * qL.inertiaDeg Q.asIdeal :=
    Ideal.inertiaDeg_algebra_tower qK qL Q.asIdeal
  have hproduct_dvd : qK.inertiaDeg qL * p ∣ p := by
    have hproduct_eq : qK.inertiaDeg qL * p =
        qK.inertiaDeg Q.asIdeal := by
      calc
        qK.inertiaDeg qL * p =
            qK.inertiaDeg qL * qL.inertiaDeg Q.asIdeal := by
          rw [hdegreeL]
        _ = qK.inertiaDeg Q.asIdeal := htower.symm
    rw [hproduct_eq]
    exact hdegreeK_dvd
  have hdegreeMiddle : qK.inertiaDeg qL = 1 := by
    have hle : qK.inertiaDeg qL * p ≤ p :=
      Nat.le_of_dvd hp.pos hproduct_dvd
    have hpos : 0 < qK.inertiaDeg qL := Ideal.inertiaDeg_pos qK qL
    have hp_pos : 0 < p := hp.pos
    have hle_one : qK.inertiaDeg qL ≤ 1 :=
      Nat.le_of_mul_le_mul_right (by simpa only [one_mul] using hle) hp_pos
    omega
  have htowerFrobenius := frobenius_tower_degree
    (R := OK K) (S := OK M) (G := Gal(M/K))
    (T := OK L) (H := Gal(M/L)) Q.asIdeal
    (galMLMK (K := K) (L := L) (M := M))
    (by
      intro sigma x
      rfl)
  simpa only [frobK, frobL, qK, qL, numberFrobeniusElement,
    hdegreeMiddle, pow_one] using htowerFrobenius.symm

set_option synthInstance.maxHeartbeats 500000 in
-- Three integral-closure Galois actions are synthesized in the splitting criterion.
set_option maxHeartbeats 3000000 in
/-- A nontrivial `M / L` Frobenius selected in Lemma VII.6.2 lies over a
base prime which splits completely in `L / K`.

The point is numerical.  Its order in `Gal(M / L)` is `p`, while the order
of the `M / K` Frobenius divides `p`; multiplicativity of inertia degrees
therefore forces the intermediate inertia degree to be one.  Unramifiedness
descends from `M / K`, so the Galois splitting criterion applies. -/
theorem splits_completely_ne
    (p : ℕ) (hp : p.Prime)
    (K L M : Type u)
    [Field K] [Field L] [Field M]
    [NumberField K] [NumberField L] [NumberField M]
    [Algebra K L] [Algebra L M] [Algebra K M]
    [IsScalarTower K L M]
    [FiniteDimensional K L] [FiniteDimensional L M]
    [IsGalois K L] [IsGalois L M] [IsAbelianGalois K M]
    (hexponent : ∀ sigma : Gal(M/K), sigma ^ p = 1)
    (S : Finset (NumberFieldPlace K))
    (hunramified : ∀ Q : FinitePrime M,
      (Sum.inl (Q.under (OK K)) : NumberFieldPlace K) ∉ S →
        Algebra.IsUnramifiedAt (OK K) Q.asIdeal)
    (Q : FinitePrime M)
    (hQnotS : (Sum.inl (Q.under (OK K)) : NumberFieldPlace K) ∉ S)
    (hFrobNe : numberFrobeniusElement (K := L) Q ≠ 1) :
    SplitsCompletelyAt K L (Q.under (OK K)) := by
  letI : Fact p.Prime := ⟨hp⟩
  letI : MulSemiringAction Gal(M/K) (OK M) :=
    IsIntegralClosure.MulSemiringAction (OK K) K M (OK M)
  letI : IsGaloisGroup Gal(M/K) (OK K) (OK M) :=
    IsGaloisGroup.of_isFractionRing Gal(M/K) (OK K) (OK M) K M
  letI : MulSemiringAction Gal(M/L) (OK M) :=
    IsIntegralClosure.MulSemiringAction (OK L) L M (OK M)
  letI : IsGaloisGroup Gal(M/L) (OK L) (OK M) :=
    IsGaloisGroup.of_isFractionRing Gal(M/L) (OK L) (OK M) L M
  let qL : Ideal (OK L) := Q.asIdeal.under (OK L)
  let qK : Ideal (OK K) := Q.asIdeal.under (OK K)
  letI : Q.asIdeal.LiesOver qL := ⟨rfl⟩
  letI : qL.LiesOver qK := ⟨by
    dsimp only [qK, qL]
    exact (Ideal.under_under Q.asIdeal).symm⟩
  letI : Algebra.IsUnramifiedAt (OK K) Q.asIdeal :=
    hunramified Q hQnotS
  letI : Algebra.IsUnramifiedAt (OK L) Q.asIdeal :=
    Algebra.IsUnramifiedAt.of_restrictScalars (OK K) Q.asIdeal
  let frobK : Gal(M/K) := numberFrobeniusElement (K := K) Q
  let frobL : Gal(M/L) := numberFrobeniusElement (K := L) Q
  have hfrobL_pow : frobL ^ p = 1 :=
    gal_ml_pow (K := K) (L := L) (M := M) p hexponent frobL
  have hfrobL_order : orderOf frobL = p :=
    orderOf_eq_prime hfrobL_pow hFrobNe
  have horderL : orderOf frobL = qL.inertiaDeg Q.asIdeal := by
    simpa only [frobL, qL, numberFrobeniusElement] using
      (frob_inertia_deg
        (R := OK L) (S := OK M) (G := Gal(M/L)) Q.asIdeal)
  have hdegreeL : qL.inertiaDeg Q.asIdeal = p := by
    rw [← horderL, hfrobL_order]
  have hfrobK_pow : frobK ^ p = 1 := hexponent frobK
  have horderK : orderOf frobK = qK.inertiaDeg Q.asIdeal := by
    simpa only [frobK, qK, numberFrobeniusElement] using
      (frob_inertia_deg
        (R := OK K) (S := OK M) (G := Gal(M/K)) Q.asIdeal)
  have hdegreeK_dvd : qK.inertiaDeg Q.asIdeal ∣ p := by
    rw [← horderK]
    exact orderOf_dvd_of_pow_eq_one hfrobK_pow
  have htower : qK.inertiaDeg Q.asIdeal =
      qK.inertiaDeg qL * qL.inertiaDeg Q.asIdeal :=
    Ideal.inertiaDeg_algebra_tower qK qL Q.asIdeal
  have hproduct_dvd : qK.inertiaDeg qL * p ∣ p := by
    have hproduct_eq : qK.inertiaDeg qL * p =
        qK.inertiaDeg Q.asIdeal := by
      calc
        qK.inertiaDeg qL * p =
            qK.inertiaDeg qL * qL.inertiaDeg Q.asIdeal := by
          rw [hdegreeL]
        _ = qK.inertiaDeg Q.asIdeal := htower.symm
    rw [hproduct_eq]
    exact hdegreeK_dvd
  have hdegreeMiddle : qK.inertiaDeg qL = 1 := by
    have hle : qK.inertiaDeg qL * p ≤ p :=
      Nat.le_of_dvd hp.pos hproduct_dvd
    have hpos : 0 < qK.inertiaDeg qL := Ideal.inertiaDeg_pos qK qL
    have hp_pos : 0 < p := hp.pos
    have hle_one : qK.inertiaDeg qL ≤ 1 :=
      Nat.le_of_mul_le_mul_right (by simpa only [one_mul] using hle) hp_pos
    omega
  letI : Algebra.IsUnramifiedAt (OK K) qL :=
    Algebra.IsUnramifiedAt.of_liesOver (OK K) qL Q.asIdeal
  have hqLmem : qL ∈ Ideal.primesOver qK (OK L) :=
    ⟨inferInstance, inferInstance⟩
  have hqLmem' : qL ∈
      Ideal.primesOver (Q.under (OK K)).asIdeal (OK L) := by
    simpa only [qK] using hqLmem
  have hqKne : qK ≠ ⊥ := by
    simpa only [qK] using (Q.under (OK K)).ne_bot
  have hramification : qK.ramificationIdx qL = 1 :=
    (unramified_ramification_idx qK qL
      (Ideal.ne_bot_of_liesOver_of_ne_bot hqKne qL)).mp inferInstance
  exact splits_completely_prime K L (Q.under (OK K)) qL
    hqLmem' hramification hdegreeMiddle

/-- **Lemma VII.6.2.**  There is a finite set of primes away from `S` whose
`M / L` Frobenius elements form an `𝔽_p`-basis, and their inclusions into
`Gal(M / K)` are the corresponding `M / K` Frobenius elements. -/
theorem completionRestrictionStatement : (∀ (p : ℕ) (_hp : Nat.Prime p)
      (K L M : Type u)
      [Field K] [Field L] [Field M]
      [NumberField K] [NumberField L] [NumberField M]
      [Algebra K L] [Algebra L M] [Algebra K M]
      [IsScalarTower K L M]
      [FiniteDimensional K L] [FiniteDimensional L M]
      [IsGalois L M] [IsAbelianGalois K M],
      (primitiveRoots p K).Nonempty →
        ∀ (hexponent : ∀ sigma : Gal(M/K), sigma ^ p = 1)
          (S : Finset (NumberFieldPlace K)),
          (∀ Q : FinitePrime M,
            (Sum.inl (Q.under (OK K)) : NumberFieldPlace K) ∉ S →
              Algebra.IsUnramifiedAt (OK K) Q.asIdeal) →
          HasFrobeniusBasis (K := K) (L := L) (M := M)
            p hexponent S) :=
  galMLStatement
    (number_statement_only
      Towers.CField.BLoc.cyclicSubextensionDegree)
    completionRestrictionBridge

end

end Towers.CField.KNIndex
