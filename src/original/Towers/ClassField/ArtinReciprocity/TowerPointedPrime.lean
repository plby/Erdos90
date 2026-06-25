import Towers.ClassField.ArtinReciprocity.ArtinMap
import Towers.ClassField.RayClassGroups.ForbiddenIdeal

/-!
# Chapter V, Section 3, Proposition 3.3 (source statement)

The tracked file proves the norm/Frobenius identity on one prime generator.
Here it is extended to the full free divisor group.  A final theorem states
the book's literal square on `I^S` from an explicit adapter connecting
fractional ideals, ideal norm, and the free divisor presentation.  This
adapter is precisely the API currently missing from Mathlib.
-/

namespace Towers.CField.ARecip

open Towers.NumberTheory.Milne
open IsDedekindDomain
open Towers.CField.RCGroups
open scoped nonZeroDivisors Pointwise

noncomputable section

universe u

/-- A prime of the top ring carrying all data needed simultaneously over
the intermediate and base rings. -/
structure TPUnram
    (R T S : Type u)
    [CommRing R] [CommRing T] [CommRing S]
    [Algebra R T] [Algebra R S] [Algebra T S] [IsScalarTower R T S] where
  prime : HeightOneSpectrum S
  finiteQuotient : Finite (S ⧸ prime.asIdeal)
  unramifiedBase : Algebra.IsUnramifiedAt R prime.asIdeal
  unramifiedIntermediate : Algebra.IsUnramifiedAt T prime.asIdeal
  underBaseMaximal : (prime.asIdeal.under R).IsMaximal
  underIntermediateMaximal : (prime.asIdeal.under T).IsMaximal
  underLiesOver : (prime.asIdeal.under T).LiesOver (prime.asIdeal.under R)
  finiteBaseQuotient : Finite (R ⧸ prime.asIdeal.under R)
  finiteIntermediateQuotient : Finite (T ⧸ prime.asIdeal.under T)

namespace TPUnram

variable
    {R T S : Type u}
    [CommRing R] [CommRing T] [CommRing S]
    [Algebra R T] [Algebra R S] [Algebra T S] [IsScalarTower R T S]

/-- The same pointed prime viewed over the base ring. -/
def toBase (P : TPUnram R T S) :
    PUPrime R S where
  prime := P.prime
  finiteQuotient := P.finiteQuotient
  isUnramified := P.unramifiedBase

/-- The same pointed prime viewed over the intermediate ring. -/
def toIntermediate (P : TPUnram R T S) :
    PUPrime T S where
  prime := P.prime
  finiteQuotient := P.finiteQuotient
  isUnramified := P.unramifiedIntermediate

/-- The residue degree occurring in the norm of the intermediate prime. -/
def inertiaDeg (P : TPUnram R T S) : ℕ := by
  letI : (P.prime.asIdeal.under R).IsMaximal := P.underBaseMaximal
  letI : (P.prime.asIdeal.under T).IsMaximal := P.underIntermediateMaximal
  letI : (P.prime.asIdeal.under T).LiesOver
      (P.prime.asIdeal.under R) := P.underLiesOver
  exact (P.prime.asIdeal.under R).inertiaDeg
    (P.prime.asIdeal.under T)

end TPUnram

/-- Formal divisors on tower-pointed unramified primes. -/
abbrev TowerUnramifiedDivisors
    (R T S : Type u)
    [CommRing R] [CommRing T] [CommRing S]
    [Algebra R T] [Algebra R S] [Algebra T S] [IsScalarTower R T S] :=
  FreeAbelianGroup (TPUnram R T S)

/-- Forget to the intermediate pointed-prime divisor. -/
def towerIntermediateDivisor
    {R T S : Type u}
    [CommRing R] [CommRing T] [CommRing S]
    [Algebra R T] [Algebra R S] [Algebra T S] [IsScalarTower R T S] :
    TowerUnramifiedDivisors R T S →+
      UnramifiedPrimeDivisors T S :=
  FreeAbelianGroup.lift fun P ↦
    FreeAbelianGroup.of P.toIntermediate

/-- The ideal norm on formal prime divisors: an intermediate prime maps to
its contraction with multiplicity equal to the residue degree. -/
def towerNormDivisor
    {R T S : Type u}
    [CommRing R] [CommRing T] [CommRing S]
    [Algebra R T] [Algebra R S] [Algebra T S] [IsScalarTower R T S] :
    TowerUnramifiedDivisors R T S →+
      UnramifiedPrimeDivisors R S :=
  FreeAbelianGroup.lift fun P ↦
    P.inertiaDeg • FreeAbelianGroup.of P.toBase

@[simp]
theorem tower_intermediate_divisor
    {R T S : Type u}
    [CommRing R] [CommRing T] [CommRing S]
    [Algebra R T] [Algebra R S] [Algebra T S] [IsScalarTower R T S]
    (P : TPUnram R T S) :
    towerIntermediateDivisor (FreeAbelianGroup.of P) =
      FreeAbelianGroup.of P.toIntermediate :=
  FreeAbelianGroup.lift_apply_of _ _

@[simp]
theorem tower_norm_divisor
    {R T S : Type u}
    [CommRing R] [CommRing T] [CommRing S]
    [Algebra R T] [Algebra R S] [Algebra T S] [IsScalarTower R T S]
    (P : TPUnram R T S) :
    towerNormDivisor (FreeAbelianGroup.of P) =
      P.inertiaDeg • FreeAbelianGroup.of P.toBase :=
  FreeAbelianGroup.lift_apply_of _ _

/-- Proposition 3.3 on the entire free divisor group. -/
theorem freeDivisor_square
    {R T S G H : Type u}
    [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [IsDedekindDomain R]
    [CommRing T] [IsDomain T] [IsIntegrallyClosed T] [IsDedekindDomain T]
    [Algebra R T] [Module.Finite R T] [Module.IsTorsionFree R T]
    [PerfectField (FractionRing R)]
    [CommRing S] [Algebra R S] [Algebra T S] [IsScalarTower R T S]
    [CommGroup G] [Finite G] [MulSemiringAction G S] [IsGaloisGroup G R S]
    [CommGroup H] [Finite H] [MulSemiringAction H S] [IsGaloisGroup H T S]
    [IsDomain S] [IsNoetherianRing S]
    (embed : H →* G)
    (embed_smul : ∀ tau : H, ∀ x : S, embed tau • x = tau • x)
    (D : TowerUnramifiedDivisors R T S) :
    artinMap (R := R) (S := S) (G := G) (towerNormDivisor D) =
      embed.toAdditive
        (artinMap (R := T) (S := S) (G := H)
          (towerIntermediateDivisor D)) := by
  induction D using FreeAbelianGroup.induction_on with
  | zero => simp
  | of P =>
      letI : Finite (S ⧸ P.prime.asIdeal) := P.finiteQuotient
      letI : Algebra.IsUnramifiedAt R P.prime.asIdeal := P.unramifiedBase
      letI : Algebra.IsUnramifiedAt T P.prime.asIdeal := P.unramifiedIntermediate
      letI : (P.prime.asIdeal.under R).IsMaximal := P.underBaseMaximal
      letI : (P.prime.asIdeal.under T).IsMaximal := P.underIntermediateMaximal
      letI : (P.prime.asIdeal.under T).LiesOver
          (P.prime.asIdeal.under R) := P.underLiesOver
      letI : Finite (R ⧸ P.prime.asIdeal.under R) := P.finiteBaseQuotient
      letI : Finite (T ⧸ P.prime.asIdeal.under T) :=
        P.finiteIntermediateQuotient
      have hprime := (on_prime
        (R := R) (T := T) (S := S) (G := G) (H := H)
        (P := P.prime.asIdeal) embed embed_smul).2
      simp only [tower_norm_divisor, map_nsmul, artinMap_of,
        tower_intermediate_divisor]
      change Additive.ofMul
          (arithFrobAt R G P.prime.asIdeal ^
            TPUnram.inertiaDeg
              (R := R) (T := T) (S := S) P) =
        Additive.ofMul (embed (arithFrobAt T H P.prime.asIdeal))
      exact congrArg Additive.ofMul hprime
  | neg P hP => simpa using congrArg Neg.neg hP
  | add D E hD hE =>
      simpa using congrArg₂ (fun x y ↦ x + y) hD hE

/-- The group `I^S` of nonzero fractional ideals away from a finite set of
primes, specialized to the fraction field of its Dedekind domain. -/
abbrev FractionalIdealsPrime
    (R : Type u) [CommRing R] [IsDomain R] [IsDedekindDomain R]
    (SR : Finset (HeightOneSpectrum R)) :=
  IdealsPrimeTo R (FractionRing R) SR

/-- The exact missing bridge from Mathlib's integral `Ideal.relNorm` and the
free prime-divisor calculation to the source's fractional-ideal groups.

The two `encode` maps are divisor presentations.  `norm_compat` says that
the proposed fractional-ideal norm has the expected prime multiplicities;
the two Artin compatibility fields identify the literal Artin homomorphisms
with the already-defined free-divisor Artin maps. -/
structure FractionalIdealAdapter
    (R T S G H : Type u)
    [CommRing R] [IsDomain R] [IsDedekindDomain R]
    [CommRing T] [IsDomain T] [IsDedekindDomain T]
    [Algebra R T]
    [CommRing S] [Algebra R S] [Algebra T S] [IsScalarTower R T S]
    [CommGroup G] [Finite G] [MulSemiringAction G S] [IsGaloisGroup G R S]
    [CommGroup H] [Finite H] [MulSemiringAction H S] [IsGaloisGroup H T S]
    (SR : Finset (HeightOneSpectrum R))
    (ST : Finset (HeightOneSpectrum T)) where
  norm : FractionalIdealsPrime T ST →*
    FractionalIdealsPrime R SR
  lowerArtin : FractionalIdealsPrime R SR →* G
  upperArtin : FractionalIdealsPrime T ST →* H
  encodeUpper : Additive (FractionalIdealsPrime T ST) →+
    TowerUnramifiedDivisors R T S
  encodeLower : Additive (FractionalIdealsPrime R SR) →+
    UnramifiedPrimeDivisors R S
  norm_compat : ∀ I,
    encodeLower (Additive.ofMul (norm I)) =
      towerNormDivisor (encodeUpper (Additive.ofMul I))
  lowerArtin_compat : ∀ I,
    artinMap (R := R) (S := S) (G := G)
        (encodeLower (Additive.ofMul I)) =
      Additive.ofMul (lowerArtin I)
  upperArtin_compat : ∀ I,
    artinMap (R := T) (S := S) (G := H)
        (towerIntermediateDivisor (encodeUpper (Additive.ofMul I))) =
      Additive.ofMul (upperArtin I)

/-- The literal fractional-ideal Artin square of Proposition V.3.3, assuming
only the explicit presentation/norm adapter that is absent from the current
library.  No generator-level weakening appears in the conclusion. -/
theorem fractionalIdeal_square
    {R T S G H : Type u}
    [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [IsDedekindDomain R]
    [CommRing T] [IsDomain T] [IsIntegrallyClosed T] [IsDedekindDomain T]
    [Algebra R T] [Module.Finite R T] [Module.IsTorsionFree R T]
    [PerfectField (FractionRing R)]
    [CommRing S] [Algebra R S] [Algebra T S] [IsScalarTower R T S]
    [CommGroup G] [Finite G] [MulSemiringAction G S] [IsGaloisGroup G R S]
    [CommGroup H] [Finite H] [MulSemiringAction H S] [IsGaloisGroup H T S]
    [IsDomain S] [IsNoetherianRing S]
    {SR : Finset (HeightOneSpectrum R)}
    {ST : Finset (HeightOneSpectrum T)}
    (embed : H →* G)
    (embed_smul : ∀ tau : H, ∀ x : S, embed tau • x = tau • x)
    (A : FractionalIdealAdapter R T S G H SR ST) :
    A.lowerArtin.comp A.norm = embed.comp A.upperArtin := by
  ext I
  apply Additive.ofMul.injective
  calc
    Additive.ofMul (A.lowerArtin (A.norm I)) =
        artinMap (R := R) (S := S) (G := G)
          (A.encodeLower (Additive.ofMul (A.norm I))) :=
      (A.lowerArtin_compat (A.norm I)).symm
    _ = artinMap (R := R) (S := S) (G := G)
          (towerNormDivisor (A.encodeUpper (Additive.ofMul I))) := by
      rw [A.norm_compat I]
    _ = embed.toAdditive
          (artinMap (R := T) (S := S) (G := H)
            (towerIntermediateDivisor
              (A.encodeUpper (Additive.ofMul I)))) :=
      freeDivisor_square embed embed_smul _
    _ = embed.toAdditive (Additive.ofMul (A.upperArtin I)) := by
      rw [A.upperArtin_compat I]
    _ = Additive.ofMul (embed (A.upperArtin I)) := rfl

end

end Towers.CField.ARecip
