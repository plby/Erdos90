import Towers.NumberTheory.Completions.CompletedValuationExtension
import Towers.NumberTheory.Completions.AdicLocalRing

/-!
# Descending ideal bounds from a completed local ring

The canonical map from a Dedekind local ring to its completed valuation
integer ring is faithfully flat.  This file packages the map computation
and ideal-divisibility descent used after identifying a completed different.
-/

namespace Towers.NumberTheory.Milne

open Ideal IsDedekindDomain

noncomputable section

universe u

variable {R K : Type u} [CommRing R] [IsDedekindDomain R]
  [Field K] [Algebra R K] [IsFractionRing R K]

/-- Extending an ideal first to the local ring and then to the completed
valuation ring agrees with extending it directly. -/
theorem prime_adic_integers
    (v : HeightOneSpectrum R) [Finite (R ⧸ v.asIdeal)] (D : Ideal R) :
    (D.map (algebraMap R (Localization.AtPrime v.asIdeal))).map
        (primeAdicIntegers (K := K) v) =
      D.map (algebraMap R (v.adicCompletionIntegers K)) := by
  rw [Ideal.map_map]
  congr 1
  ext x
  exact congrArg Subtype.val
    (adic_integers_algebra (K := K) v x)

set_option synthInstance.maxHeartbeats 200000 in
-- Inferring the completed valuation ring's flatness unfolds its DVR structure.
/-- A bound for the direct image of a global ideal in the completed
valuation ring descends to the corresponding localized ideal. -/
theorem localized_dvd_maximal
    (v : HeightOneSpectrum R) [Finite (R ⧸ v.asIdeal)]
    (D : Ideal R) (Dhat : Ideal (v.adicCompletionIntegers K)) (n : ℕ)
    (hD : D.map (algebraMap R (v.adicCompletionIntegers K)) = Dhat)
    (hbound : Dhat ∣
      IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ n) :
    D.map (algebraMap R (Localization.AtPrime v.asIdeal)) ∣
      IsLocalRing.maximalIdeal (Localization.AtPrime v.asIdeal) ^ n := by
  let A := Localization.AtPrime v.asIdeal
  let B := v.adicCompletionIntegers K
  let f : A →+* B := primeAdicIntegers (K := K) v
  letI : Algebra A B := f.toAlgebra
  letI : Module.FaithfullyFlat A B :=
    integers_faithfully_flat (K := K) v
  apply ideal_faithfully_flat
    (D.map (algebraMap R A)) (IsLocalRing.maximalIdeal A)
    Dhat (IsLocalRing.maximalIdeal B) n
  · change (D.map (algebraMap R A)).map f = Dhat
    rw [prime_adic_integers (K := K) v D]
    exact hD
  · change (IsLocalRing.maximalIdeal A).map f =
      IsLocalRing.maximalIdeal B
    exact maximal_completion_integers (K := K) v
  · exact hbound

end

end Towers.NumberTheory.Milne
