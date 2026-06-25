import Mathlib.NumberTheory.NumberField.ClassNumber
import Mathlib.RingTheory.ClassGroup
import Mathlib.RingTheory.Ideal.Norm.RelNorm

/-!
# Milne, Proposition 4.1: compatibility of ideal norms

This file records the standard compatibility formulas for the relative norm of ideals in a
finite extension of Dedekind domains.  Mathlib's `Ideal.relNorm` is defined using the integral
norm, so the principal-ideal formula is valid without first choosing a basis.
-/

open Module
open scoped nonZeroDivisors NumberField Pointwise

namespace Towers.NumberTheory.Milne

attribute [local instance] FractionRing.liftAlgebra

variable (A B : Type*) [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
  [IsDedekindDomain A] [CommRing B] [IsDomain B] [IsIntegrallyClosed B]
  [IsDedekindDomain B] [Algebra A B] [Module.Finite A B] [IsTorsionFree A B]

private theorem prod_smul_stabilizer
    {G M : Type*} [Group G] [Fintype G] [CommMonoid M] [MulAction G M]
    (x : M) [Fintype (MulAction.orbit G x)] :
    (∏ g : G, g • x) =
      (∏ y : MulAction.orbit G x, y.1) ^ Nat.card (MulAction.stabilizer G x) := by
  classical
  letI := Fintype.ofFinite (MulAction.stabilizer G x)
  let orbitMap : G → MulAction.orbit G x := fun g ↦ ⟨g • x, ⟨g, rfl⟩⟩
  calc
    (∏ g : G, g • x) = ∏ g : G, (orbitMap g).1 := rfl
    _ = ∏ y : MulAction.orbit G x, ∏ _g : {g // orbitMap g = y}, y.1 := by
      exact (Fintype.prod_fiberwise' orbitMap fun y ↦ y.1).symm
    _ = ∏ y : MulAction.orbit G x, y.1 ^ Nat.card (MulAction.stabilizer G x) := by
      apply Finset.prod_congr rfl
      intro y _
      rw [Finset.prod_const, Finset.card_univ]
      congr 1
      obtain ⟨τ, hτ⟩ := y.2
      let e : MulAction.stabilizer G x ≃ {g // orbitMap g = y} :=
        { toFun := fun h ↦ ⟨τ * h.1, Subtype.ext (by
            change (τ * h.1) • x = y.1
            rw [mul_smul, h.2]
            exact hτ)⟩
          invFun := fun g ↦ ⟨τ⁻¹ * g.1, by
            change (τ⁻¹ * g.1) • x = x
            have hg : g.1 • x = τ • x := by
              simpa [orbitMap, hτ] using congrArg Subtype.val g.2
            rw [mul_smul, hg, inv_smul_smul]⟩
          left_inv := fun h ↦ by ext; simp
          right_inv := fun g ↦ by ext; simp }
      rw [Nat.card_eq_fintype_card]
      exact Fintype.card_congr e.symm
    _ = (∏ y : MulAction.orbit G x, y.1) ^ Nat.card (MulAction.stabilizer G x) := by
      rw [Finset.prod_pow]

/-- Milne 4.1(a): the norm of the extension of an ideal is its power by the field degree. -/
theorem rel_extension_pow (a : Ideal A) :
    Ideal.relNorm A (a.map (algebraMap A B)) =
      a ^ Module.finrank (FractionRing A) (FractionRing B) :=
  Ideal.relNorm_algebraMap B a

/-- Relative ideal norms are transitive in a tower. -/
theorem relNorm_transitive (C : Type*) [CommRing C] [IsDomain C] [IsIntegrallyClosed C]
    [IsDedekindDomain C] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    [Module.Finite B C] [Module.Finite A C] [IsTorsionFree B C] [IsTorsionFree A C]
    (c : Ideal C) :
    Ideal.relNorm A (Ideal.relNorm B c) = Ideal.relNorm A c :=
  Ideal.relNorm_relNorm A B c

/-- The relative norm of a prime is the contraction raised to its inertia degree. -/
theorem rel_contraction_deg [PerfectField (FractionRing A)]
    (P : Ideal B) (p : Ideal A) [P.IsMaximal] [p.IsMaximal] [P.LiesOver p] :
    Ideal.relNorm A P = p ^ p.inertiaDeg P :=
  Ideal.relNorm_eq_pow_of_isMaximal P p

/--
Milne 4.1(b), in the factorized form used in the proof: after extending the norm of a prime
back to `B`, every prime over its contraction occurs with exponent `e * f`.
-/
theorem rel_primes_pow
    [IsGalois (FractionRing A) (FractionRing B)]
    (P : Ideal B) (p : Ideal A) [P.IsMaximal] [p.IsMaximal] [P.LiesOver p]
    (hp : p ≠ ⊥) :
    (Ideal.relNorm A P).map (algebraMap A B) =
      (∏ Q ∈ p.primesOver B, Q) ^ (p.ramificationIdx P * p.inertiaDeg P) := by
  let G := Gal(FractionRing B/FractionRing A)
  letI : MulSemiringAction G B :=
    IsIntegralClosure.MulSemiringAction A (FractionRing A) (FractionRing B) B
  letI : IsGaloisGroup G A B :=
    IsGaloisGroup.of_isFractionRing G A B (FractionRing A) (FractionRing B)
  have hram : ∀ Q ∈ (p.primesOver B).toFinset,
      p.ramificationIdx Q = p.ramificationIdx P := by
    intro Q hQ
    rw [Set.mem_toFinset] at hQ
    letI : Q.IsPrime := hQ.1
    letI : Q.LiesOver p := hQ.2
    exact Ideal.ramificationIdx_eq_of_isGaloisGroup p Q P G
  rw [Ideal.relNorm_eq_pow_of_isPrime_isGalois P p, Ideal.map_pow,
    Ideal.map_algebraMap_eq_finsetProd_pow hp]
  have hprod :
      (∏ Q ∈ (p.primesOver B).toFinset, Q ^ p.ramificationIdx Q) =
        ∏ Q ∈ (p.primesOver B).toFinset, Q ^ p.ramificationIdx P := by
    apply Finset.prod_congr rfl
    intro Q hQ
    rw [hram Q hQ]
  rw [hprod, Finset.prod_pow, pow_mul]

/-- Milne 4.1(b), second equality: the extension of the ideal norm of a prime is the
product of all its Galois conjugates. -/
theorem rel_galois_conjugates
    [IsGalois (FractionRing A) (FractionRing B)]
    (P : Ideal B) (p : Ideal A) [P.IsMaximal] [p.IsMaximal] [P.LiesOver p]
    (hp : p ≠ ⊥) :
    (Ideal.relNorm A P).map (algebraMap A B) =
      ∏ σ : Gal(FractionRing B/FractionRing A),
        P.map (galRestrict A (FractionRing A) (FractionRing B) B σ).toRingHom := by
  letI : MulSemiringAction Gal(FractionRing B/FractionRing A) B :=
    IsIntegralClosure.MulSemiringAction A (FractionRing A) (FractionRing B) B
  letI : IsGaloisGroup Gal(FractionRing B/FractionRing A) A B :=
    IsGaloisGroup.of_isFractionRing Gal(FractionRing B/FractionRing A)
      A B (FractionRing A) (FractionRing B)
  letI := (Finite.finite_mulAction_orbit
    (M := Gal(FractionRing B/FractionRing A)) P).fintype
  have horbit : MulAction.orbit Gal(FractionRing B/FractionRing A) P = p.primesOver B :=
    Algebra.IsInvariant.orbit_eq_primesOver A B Gal(FractionRing B/FractionRing A) p P
  have hprod : (∏ Q : MulAction.orbit Gal(FractionRing B/FractionRing A) P, Q.1) =
      ∏ Q ∈ (p.primesOver B).toFinset, Q := by
    calc
      (∏ Q : MulAction.orbit Gal(FractionRing B/FractionRing A) P, Q.1) =
          ∏ Q : p.primesOver B, Q.1 := by
        simpa using
          (Equiv.setCongr horbit).prod_comp (fun Q : p.primesOver B ↦ Q.1)
      _ = ∏ Q ∈ (p.primesOver B).toFinset, Q := by
        simpa using
          (Finset.prod_set_coe (s := p.primesOver B) (f := fun Q : Ideal B ↦ Q))
  have hcard : Nat.card
      (MulAction.stabilizer Gal(FractionRing B/FractionRing A) P) =
      p.ramificationIdx P * p.inertiaDeg P := by
    have horbitStabilizer :
        (p.primesOver B).ncard *
            Nat.card (MulAction.stabilizer Gal(FractionRing B/FractionRing A) P) =
          Nat.card Gal(FractionRing B/FractionRing A) := by
      rw [← horbit, ← Nat.card_coe_set_eq]
      simpa only [Nat.card_prod] using Nat.card_congr
        (MulAction.orbitProdStabilizerEquivGroup
          Gal(FractionRing B/FractionRing A) P)
    have hfundamental :=
      Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn
        hp B Gal(FractionRing B/FractionRing A)
    have hcardIn : Nat.card
        (MulAction.stabilizer Gal(FractionRing B/FractionRing A) P) =
        p.ramificationIdxIn B * p.inertiaDegIn B := by
      apply mul_left_cancel₀ (IsDedekindDomain.primesOver_ncard_ne_zero p B)
      exact horbitStabilizer.trans hfundamental.symm
    rw [hcardIn,
      Ideal.ramificationIdxIn_eq_ramificationIdx p P
        Gal(FractionRing B/FractionRing A),
      Ideal.inertiaDegIn_eq_inertiaDeg p P Gal(FractionRing B/FractionRing A)]
  calc
    (Ideal.relNorm A P).map (algebraMap A B) =
        (∏ Q ∈ p.primesOver B, Q) ^
          (p.ramificationIdx P * p.inertiaDeg P) :=
      rel_primes_pow A B P p hp
    _ = (∏ Q : MulAction.orbit Gal(FractionRing B/FractionRing A) P, Q.1) ^
        Nat.card (MulAction.stabilizer Gal(FractionRing B/FractionRing A) P) := by
      rw [hprod, hcard]
    _ = ∏ σ : Gal(FractionRing B/FractionRing A), σ • P :=
      (prod_smul_stabilizer P).symm
    _ = ∏ σ : Gal(FractionRing B/FractionRing A),
        P.map (galRestrict A (FractionRing A) (FractionRing B) B σ).toRingHom := rfl

/-- Milne 4.1(c), stated with the integral norm available for every such extension. -/
theorem rel_principal_int (b : B) :
    Ideal.relNorm A (Ideal.span ({b} : Set B)) =
      Ideal.span ({Algebra.intNorm A B b} : Set A) :=
  Ideal.relNorm_singleton A b

/-- Milne 4.1(c), in the usual algebra-norm notation when `B` is free over `A`. -/
theorem rel_norm_principal [Module.Free A B] (b : B) :
    Ideal.relNorm A (Ideal.span ({b} : Set B)) =
      Ideal.span ({Algebra.norm A b} : Set A) := by
  rw [Ideal.relNorm_singleton, Algebra.intNorm_eq_norm]

/-- The class-group norm argument used in Milne's conductor-`23` example.
If the degree of the fraction-field extension is coprime to the order of the
base class group, a nontrivial base class group prevents the extension ring
from being a principal ideal ring. -/
theorem coprime_fraction_card
    [Fintype (ClassGroup A)]
    (hcard : Fintype.card (ClassGroup A) ≠ 1)
    (hcoprime : Nat.Coprime
      (Module.finrank A B)
      (Fintype.card (ClassGroup A))) :
    ¬IsPrincipalIdealRing B := by
  intro hprincipalB
  letI : IsPrincipalIdealRing B := hprincipalB
  apply hcard
  rw [card_classGroup_eq_one_iff]
  constructor
  intro I
  by_cases hI : I = ⊥
  · simpa [hI] using (bot_isPrincipal : (⊥ : Ideal A).IsPrincipal)
  let I0 : (Ideal A)⁰ :=
    ⟨I, mem_nonZeroDivisors_iff_ne_zero.mpr hI⟩
  let d := Module.finrank A B
  have hmapPrincipal : (I.map (algebraMap A B)).IsPrincipal :=
    IsPrincipalIdealRing.principal _
  have hnormPrincipal : (Ideal.relNorm A
      (I.map (algebraMap A B))).IsPrincipal := by
    obtain ⟨b, hb⟩ := hmapPrincipal
    refine ⟨Algebra.intNorm A B b, ?_⟩
    rw [hb]
    change Ideal.relNorm A (Ideal.span {b}) =
      Ideal.span {Algebra.intNorm A B b}
    exact Ideal.relNorm_singleton A b
  have hpowPrincipal : (I ^ d).IsPrincipal := by
    change (I ^ Module.finrank A B).IsPrincipal
    rw [← Algebra.IsAlgebraic.finrank_of_isFractionRing A (FractionRing A) B
      (FractionRing B), ← Ideal.relNorm_algebraMap B I]
    exact hnormPrincipal
  let c : ClassGroup A := ClassGroup.mk0 I0
  have hcd : c ^ d = 1 := by
    change (ClassGroup.mk0 I0) ^ d = 1
    rw [← map_pow]
    apply (ClassGroup.mk0_eq_one_iff (I0 ^ d).property).2
    simpa [I0] using hpowPrincipal
  have hordD : orderOf c ∣ d := orderOf_dvd_of_pow_eq_one hcd
  have hordCard : orderOf c ∣ Fintype.card (ClassGroup A) :=
    orderOf_dvd_card
  have hord : orderOf c = 1 :=
    Nat.eq_one_of_dvd_coprimes hcoprime hordD hordCard
  apply (ClassGroup.mk0_eq_one_iff I0.property).1
  exact orderOf_eq_one_iff.mp hord

/-- Number-field form of the class-group norm obstruction: if `[L : K]` is
coprime to the class number of `K`, class number one cannot first appear in
`L`. -/
theorem number_coprime_finrank
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    (hclass : NumberField.classNumber K ≠ 1)
    (hcoprime : Nat.Coprime (Module.finrank K L)
      (NumberField.classNumber K)) :
    NumberField.classNumber L ≠ 1 := by
  letI : Module.Finite (𝓞 K) (𝓞 L) :=
    Module.Finite.of_restrictScalars_finite ℤ (𝓞 K) (𝓞 L)
  have hdegree : Module.finrank (𝓞 K) (𝓞 L) = Module.finrank K L := by
    symm
    exact Algebra.IsAlgebraic.finrank_of_isFractionRing
      (𝓞 K) K (𝓞 L) L
  have hcard : Fintype.card (ClassGroup (𝓞 K)) ≠ 1 := by
    simpa [NumberField.classNumber] using hclass
  have hcoprime' : Nat.Coprime (Module.finrank (𝓞 K) (𝓞 L))
      (Fintype.card (ClassGroup (𝓞 K))) := by
    simpa [hdegree, NumberField.classNumber] using hcoprime
  intro hL
  apply coprime_fraction_card
    (𝓞 K) (𝓞 L) hcard hcoprime'
  exact NumberField.classNumber_eq_one_iff.mp hL

/--
In a Galois extension, the extension of the norm of a principal ideal is the product of all
Galois conjugates of that principal ideal.
-/
theorem rel_principal_conjugates
    [IsGalois (FractionRing A) (FractionRing B)] (b : B) :
    (Ideal.relNorm A (Ideal.span ({b} : Set B))).map (algebraMap A B) =
      ∏ σ : B ≃ₐ[A] B, Ideal.span ({σ b} : Set B) := by
  rw [Ideal.relNorm_singleton, Ideal.map_span, Set.image_singleton,
    Algebra.algebraMap_intNorm_of_isGalois, ← Ideal.prod_span_singleton]

end Towers.NumberTheory.Milne
