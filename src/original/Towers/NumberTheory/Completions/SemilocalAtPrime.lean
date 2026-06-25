import Towers.NumberTheory.Completions.DifferentLocalization
import Mathlib.RingTheory.Localization.LocalizationLocalization
import Mathlib.RingTheory.LocalRing.RingHom.Basic

/-!
# Localizing a semilocal localization at an upper prime

Let `P` lie over `p` in `R → S`, and first localize `S` by the image of
`R \ p`.  The image of `P` is prime in this semilocal ring, its contraction
is `P`, and localizing once more gives the ordinary local ring `S_P`.
This file records the resulting equivalence and its action on maximal
ideals and on localized ideals, including the different.
-/

namespace Towers.NumberTheory.Milne

open Ideal IsLocalization

noncomputable section

universe u

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]

/-- The localization of `S` obtained by inverting the image of the
complement of `p`. -/
abbrev SemilocalizationAtPrime (S : Type u) [CommRing S] [Algebra R S]
    (p : Ideal R) [p.IsPrime] :=
  Localization (Algebra.algebraMapSubmonoid S p.primeCompl)

/-- The prime of the semilocal localization corresponding to an upper
prime `P` lying over `p`. -/
noncomputable def sPrime (p : Ideal R) [p.IsPrime] (P : Ideal S) :
    Ideal (SemilocalizationAtPrime S p) :=
  P.map (algebraMap S (SemilocalizationAtPrime S p))

/-- The image of an upper prime lying over `p` remains prime after
localizing at the image of `R \ p`. -/
theorem semilocal_prime
    (p : Ideal R) [p.IsPrime] (P : Ideal S) [P.IsPrime] [P.LiesOver p] :
    (sPrime p P).IsPrime := by
  exact IsLocalization.AtPrime.isPrime_map_of_liesOver
    S p (SemilocalizationAtPrime S p) P

noncomputable instance sPrime.instIsPrime
    (p : Ideal R) [p.IsPrime] (P : Ideal S) [P.IsPrime] [P.LiesOver p] :
    (sPrime p P).IsPrime :=
  semilocal_prime p P

/-- Contracting the corresponding semilocal prime recovers the original
upper prime. -/
theorem semilocalPrime_comap
    (p : Ideal R) [p.IsPrime] (P : Ideal S) [P.IsPrime] [P.LiesOver p] :
    (sPrime p P).comap
        (algebraMap S (SemilocalizationAtPrime S p)) = P := by
  exact IsLocalization.under_map_of_isPrime_disjoint
    (Algebra.algebraMapSubmonoid S p.primeCompl)
    (SemilocalizationAtPrime S p) inferInstance
    (Ideal.disjoint_primeCompl_of_liesOver P p)

/-- Localizing the semilocal ring at the prime corresponding to `P` gives
the ordinary local ring `S_P`. -/
noncomputable def primeEquivSemilocal
    (p : Ideal R) [p.IsPrime] (P : Ideal S) [P.IsPrime] [P.LiesOver p] :
    Localization.AtPrime P ≃ₐ[S]
      Localization.AtPrime (sPrime p P) := by
  letI : (sPrime p P).IsPrime := semilocal_prime p P
  let q := sPrime p P
  let f : S →+* SemilocalizationAtPrime S p := algebraMap S _
  have hM : P.primeCompl = (q.comap f).primeCompl := by
    congr 1
    exact (semilocalPrime_comap p P).symm
  let hloc : IsLocalization (q.comap f).primeCompl
      (Localization.AtPrime q) := inferInstance
  letI : IsLocalization P.primeCompl (Localization.AtPrime q) :=
    hM ▸ hloc
  exact IsLocalization.algEquiv P.primeCompl _ _

/-- The local-ring equivalence carries maximal ideal to maximal ideal. -/
theorem maximal_ideal_semilocal
    (p : Ideal R) [p.IsPrime] (P : Ideal S) [P.IsPrime] [P.LiesOver p] :
    (IsLocalRing.maximalIdeal (Localization.AtPrime P)).map
        (primeEquivSemilocal p P).toRingEquiv =
      IsLocalRing.maximalIdeal
        (Localization.AtPrime (sPrime p P)) := by
  letI : (sPrime p P).IsPrime := semilocal_prime p P
  exact IsLocalRing.map_ringEquiv_maximalIdeal
    (primeEquivSemilocal p P).toRingEquiv

/-- Extending an ideal of `S` directly to `S_P` and then transporting it
through the equivalence agrees with first extending it to the semilocal
ring and then localizing at the corresponding prime. -/
theorem prime_equiv_semilocal
    (p : Ideal R) [p.IsPrime] (P : Ideal S) [P.IsPrime] [P.LiesOver p]
    (D : Ideal S) :
    (D.map (algebraMap S (Localization.AtPrime P))).map
        (primeEquivSemilocal p P).toRingEquiv =
      (D.map (algebraMap S (SemilocalizationAtPrime S p))).map
        (algebraMap (SemilocalizationAtPrime S p)
          (Localization.AtPrime (sPrime p P))) := by
  letI : (sPrime p P).IsPrime := semilocal_prime p P
  let f : S →+* Localization.AtPrime P := algebraMap S _
  let g : Localization.AtPrime P →+*
      Localization.AtPrime (sPrime p P) :=
    (primeEquivSemilocal p P).toRingEquiv
  let f' : S →+* SemilocalizationAtPrime S p := algebraMap S _
  let g' : SemilocalizationAtPrime S p →+*
      Localization.AtPrime (sPrime p P) := algebraMap _ _
  have hcomp : g.comp f = g'.comp f' := by
    ext x
    calc
      g (f x) = algebraMap S
          (Localization.AtPrime (sPrime p P)) x :=
        (primeEquivSemilocal p P).commutes x
      _ = g' (f' x) :=
        IsScalarTower.algebraMap_apply S (SemilocalizationAtPrime S p)
          (Localization.AtPrime (sPrime p P)) x
  calc
    (D.map f).map g = D.map (g.comp f) := Ideal.map_map f g
    _ = D.map (g'.comp f') := by rw [hcomp]
    _ = (D.map f').map g' := (Ideal.map_map f' g').symm

section Different

attribute [local instance] FractionRing.liftAlgebra
  FractionRing.isScalarTower_liftAlgebra
  Localization.AtPrime.liftAlgebra

variable [IsDomain R] [IsDomain S]
variable [IsDedekindDomain R] [IsDedekindDomain S]
variable [Module.Finite R S] [Module.IsTorsionFree R S]
variable [IsIntegralClosure S R (FractionRing S)]
variable [Algebra.IsSeparable (FractionRing R) (FractionRing S)]

/-- Under the local-ring equivalence, the localization of the global
different at `P` is the localization at the corresponding prime of the
semilocal different over `R_p`. -/
theorem different_ideal_semilocal
    (p : Ideal R) [p.IsPrime] (P : Ideal S) [P.IsPrime] [P.LiesOver p] :
    ((differentIdeal R S).map
        (algebraMap S (Localization.AtPrime P))).map
        (primeEquivSemilocal p P).toRingEquiv =
      (differentIdeal (Localization.AtPrime p)
          (SemilocalizationAtPrime S p)).map
        (algebraMap (SemilocalizationAtPrime S p)
          (Localization.AtPrime (sPrime p P))) := by
  rw [prime_equiv_semilocal p P]
  rw [different_prime_semilocal p]

end Different

end

end Towers.NumberTheory.Milne
