import Submission.NumberTheory.Galois.DecompositionGroupTower
import Submission.NumberTheory.Galois.FrobeniusElement

/-!
# Chapter V, Section 1: Frobenius properties 1.9--1.12

The Frobenius review in Chapter V repeats results developed in Chapter 8 of
Milne's *Algebraic Number Theory*.  The Submission ANT development already proves
the conjugacy, tower, restriction, and product-restriction formulas.  This
file records source-numbered wrappers in the class-field-theory namespace.
-/

namespace Submission.CField.RCGroups

open Submission.NumberTheory.Milne
open scoped Pointwise

noncomputable section

/-- Statement 1.9, decomposition-group part: the stabilizer of a conjugate
prime is the conjugate of the original stabilizer. -/
theorem decomposition_smul_conjugate
    {G X : Type*} [Group G] [MulAction G X] (tau : G) (P : X) :
    MulAction.stabilizer G (tau • P) =
      (MulAction.stabilizer G P).map (MulAut.conj tau).toMonoidHom :=
  MulAction.stabilizer_smul_eq_stabilizer_map_conj tau P

/-- Statement 1.9, Frobenius part: Frobenius at a conjugate unramified prime
is the conjugate Frobenius element. -/
theorem frobenius_smul_conjugate
    {R S G : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [Group G] [Finite G] [MulSemiringAction G S] [IsGaloisGroup G R S]
    [IsDomain S] [IsNoetherianRing S]
    (P : Ideal S) [P.IsPrime] [Finite (S ⧸ P)]
    (tau : G) [Finite (S ⧸ tau • P)]
    [Algebra.IsUnramifiedAt R P] :
    arithFrobAt R G (tau • P) = tau * arithFrobAt R G P * tau⁻¹ :=
  arith_frob_conjugate P tau

/-- Statement 1.10: in a tower, Frobenius over the intermediate field is the
residue-degree power of Frobenius over the base. -/
theorem frobenius_tower_degree
    {R S G T H : Type*}
    [CommRing R] [CommRing S] [Algebra R S]
    [Group G] [Finite G] [MulSemiringAction G S] [IsGaloisGroup G R S]
    [CommRing T] [Algebra R T] [Algebra T S] [IsScalarTower R T S]
    [Group H] [Finite H] [MulSemiringAction H S] [IsGaloisGroup H T S]
    [IsDomain S] [IsNoetherianRing S]
    (P : Ideal S) [P.IsPrime] [Finite (S ⧸ P)]
    [(P.under R).IsMaximal] [(P.under T).IsMaximal]
    [(P.under T).LiesOver (P.under R)]
    [Finite (R ⧸ P.under R)] [Finite (T ⧸ P.under T)]
    [Algebra.IsUnramifiedAt R P]
    (embed : H →* G)
    (embed_smul : ∀ tau : H, ∀ x : S, embed tau • x = tau • x) :
    arithFrobAt R G P ^ (P.under R).inertiaDeg (P.under T) =
      embed (arithFrobAt T H P) :=
  arith_frob_tower P embed embed_smul

/-- Statement 1.11: restricting Frobenius to a Galois intermediate extension
gives Frobenius at the contracted prime. -/
theorem frobenius_restrict_contracted
    {R S G T H : Type*}
    [CommRing R] [CommRing S] [Algebra R S]
    [Group G] [Finite G] [MulSemiringAction G S] [IsGaloisGroup G R S]
    [CommRing T] [Algebra R T] [Algebra T S] [IsScalarTower R T S]
    [Group H] [Finite H] [MulSemiringAction H T] [IsGaloisGroup H R T]
    [IsDomain T] [IsNoetherianRing T]
    [Algebra.EssFiniteType R T] [Algebra.EssFiniteType R S]
    [IsDedekindDomain T] [Module.IsTorsionFree T S] [IsDomain S]
    (P : Ideal S) [P.IsPrime] [Finite (S ⧸ P)]
    [Finite (T ⧸ P.under T)] [Algebra.IsUnramifiedAt R P]
    (res : G →* H)
    (res_smul : ∀ sigma : G, ∀ x : T,
      algebraMap T S (res sigma • x) = sigma • algebraMap T S x) :
    res (arithFrobAt R G P) = arithFrobAt R H (P.under T) :=
  arith_restrict_unramified P res res_smul

/-- Statement 1.12: under the two restriction maps from a compositum,
Frobenius maps to the pair of Frobenius elements. -/
theorem frobenius_prod_restrict
    {R S G T₁ T₂ H₁ H₂ : Type*}
    [CommRing R] [CommRing S] [Algebra R S]
    [Group G] [Finite G] [MulSemiringAction G S] [IsGaloisGroup G R S]
    [CommRing T₁] [CommRing T₂]
    [Algebra R T₁] [Algebra T₁ S] [IsScalarTower R T₁ S]
    [Algebra R T₂] [Algebra T₂ S] [IsScalarTower R T₂ S]
    [Group H₁] [Finite H₁] [MulSemiringAction H₁ T₁] [IsGaloisGroup H₁ R T₁]
    [Group H₂] [Finite H₂] [MulSemiringAction H₂ T₂] [IsGaloisGroup H₂ R T₂]
    [IsDomain T₁] [IsDomain T₂]
    [IsNoetherianRing T₁] [IsNoetherianRing T₂]
    [Algebra.EssFiniteType R T₁] [Algebra.EssFiniteType R T₂]
    [Algebra.EssFiniteType R S]
    [IsDedekindDomain T₁] [IsDedekindDomain T₂]
    [Module.IsTorsionFree T₁ S] [Module.IsTorsionFree T₂ S]
    [IsDomain S]
    (P : Ideal S) [P.IsPrime] [Finite (S ⧸ P)]
    [Finite (T₁ ⧸ P.under T₁)] [Finite (T₂ ⧸ P.under T₂)]
    [Algebra.IsUnramifiedAt R P]
    (res₁ : G →* H₁) (res₂ : G →* H₂)
    (res₁_smul : ∀ sigma : G, ∀ x : T₁,
      algebraMap T₁ S (res₁ sigma • x) = sigma • algebraMap T₁ S x)
    (res₂_smul : ∀ sigma : G, ∀ x : T₂,
      algebraMap T₂ S (res₂ sigma • x) = sigma • algebraMap T₂ S x) :
    (res₁.prod res₂) (arithFrobAt R G P) =
      (arithFrobAt R H₁ (P.under T₁), arithFrobAt R H₂ (P.under T₂)) :=
  arith_frob_unramified P res₁ res₂ res₁_smul res₂_smul

end

end Submission.CField.RCGroups
