import Towers.ClassField.DirichletDensity.SecondInequality
import Towers.ClassField.RayClassGroups.GroupFiniteness

/-!
# Algebraic prerequisites for Theorem VI.4.9

This file discharges the finiteness and split-prime ideal-norm inputs used
by the density proof of the second inequality.
-/

namespace Towers.CField.DDensit

open IsDedekindDomain NumberField Set
open Towers.NumberTheory.Milne
open Towers.CField.RCGroups
open Towers.CField.ARecip
open Towers.CField.EProduc
open Towers.CField.PDensit

noncomputable section

universe u

/-- A finite Galois extension, viewed with its identity self-embedding, is
its own Galois closure. -/
private theorem galois_closure_self
    (K L : Type u) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] :
    IsGaloisClosure K L L := by
  rw [IsGaloisClosure]
  have hrange : Set.range (algebraMap L L) = Set.univ := by
    ext x
    simp
  rw [hrange, IntermediateField.adjoin_univ]
  exact top_unique (IntermediateField.le_normalClosure
    (K := (⊤ : IntermediateField K L)))

/-- The Galois density input needed by Theorem 4.9 is exactly the Galois
specialization of the preceding Theorem 3.4. -/
theorem polarDensityBridge
    (h34 : (∀ (K L M : Type u)
          [Field K] [NumberField K]
          [Field L] [NumberField L]
          [Field M] [NumberField M]
          [Algebra K L] [Algebra K M] [Algebra L M] [IsScalarTower K L M]
          [FiniteDimensional K L] [FiniteDimensional K M] [IsGalois K M],
          GaloisClosureConclusion K L M)) :
    PolarDensityBridge.{u} := by
  intro K L _ _ _ _ _ _ _
  exact h34 K L L (galois_closure_self K L)

/-- Every congruence quotient is a quotient of the ray class group.  Thus
ray-class finiteness supplies the finiteness input used in Theorems 4.8 and
4.9, without a separate cardinality assumption on each subgroup. -/
theorem congruence_finiteness_ray
    (hRay : ∀ (K : Type u) [Field K] [NumberField K],
      RayClassFiniteness K) :
    CongruenceFinitenessBridge.{u} := by
  intro K _ _ m H hRayLe
  let R := rayPrincipalSubgroup K m
  letI : Finite (RayClassGroup K m) := hRay K m
  let f : RayClassGroup K m →* CongruenceClassQuotient K m H :=
    QuotientGroup.map R H (MonoidHom.id _) hRayLe
  apply Finite.of_surjective f
  intro C
  obtain ⟨I, rfl⟩ := QuotientGroup.mk'_surjective H C
  exact ⟨QuotientGroup.mk' R I, rfl⟩

/-- Congruence quotients are finite, using the unconditional finiteness of
the ray class group. -/
theorem congruenceFinitenessBridge :
    CongruenceFinitenessBridge.{u} :=
  congruence_finiteness_ray
    (fun K _ _ ↦ ray_class_group K)

/-- A completely split prime away from the modulus is the norm of any
prime above it, so it belongs to the ray-principal-times-norm subgroup. -/
theorem splittingRayBridge :
    SplittingRayBridge.{u} := by
  intro K _ _ L m hGalois
  letI : IsGalois K L.carrier := hGalois
  intro p hp
  rcases hp with ⟨hpSplit, hpAway⟩
  refine ⟨hpAway, ?_⟩
  apply (show L.idealNormSubgroup m.finiteSupport ≤
      extensionRaySubgroup L m from le_sup_right)
  change (awayIntegralIdeal K ⟨p, hpAway⟩).idealsPrime.1 ∈
    L.totalIdealSubgroup
  obtain ⟨Q, hQprime, hQover⟩ :=
    Classical.choice
      (p.asIdeal.nonempty_primesOver (S := NumberField.RingOfIntegers L.carrier))
  let q : HeightOneSpectrum (NumberField.RingOfIntegers L.carrier) :=
    ⟨Q, hQprime, Ideal.ne_bot_of_mem_primesOver p.ne_bot ⟨hQprime, hQover⟩⟩
  have hQmem : Q ∈ Ideal.primesOver p.asIdeal
      (NumberField.RingOfIntegers L.carrier) := ⟨hQprime, hQover⟩
  let P : L.PAbove := ⟨p, q, hQover⟩
  apply Subgroup.subset_closure
  refine ⟨P, ?_⟩
  have hinertia : p.asIdeal.inertiaDeg Q = 1 := (hpSplit.2 Q hQmem).2
  change ANExt.primeFractionalIdeal p ^
      p.asIdeal.inertiaDeg q.asIdeal =
    (awayIntegralIdeal K ⟨p, hpAway⟩).idealsPrime.1
  rw [show p.asIdeal.inertiaDeg q.asIdeal = 1 by simpa [q] using hinertia, pow_one]
  apply Units.ext
  simp [ANExt.primeFractionalIdeal,
    awayIntegralIdeal, IIPrime.idealsPrime]

/-- **Theorem VI.4.9**, assembled from the named results preceding it.
Ray-class and congruence-quotient finiteness and the split-prime norm input
are discharged above. -/
theorem prerequisites_statement_previous
    (h34 : (∀ (K L M : Type u)
          [Field K] [NumberField K]
          [Field L] [NumberField L]
          [Field M] [NumberField M]
          [Algebra K L] [Algebra K M] [Algebra L M] [IsScalarTower K L M]
          [FiniteDimensional K L] [FiniteDimensional K M] [IsGalois K M],
          GaloisClosureConclusion K L M))
    (h41a : PolarImpliesDirichlet.{u})
    (h48 : CongruenceDensityFormula.{u}) :
    (∀ (K : Type u) [Field K] [NumberField K]
          (L : NFExt K) (m : Modulus K),
          IsGalois K L.carrier →
            Finite (IdealsPrimeTo (NumberField.RingOfIntegers K) K m.finiteSupport ⧸
              extensionRaySubgroup L m) ∧
            (extensionRaySubgroup L m).index ≤
              Module.finrank K L.carrier) :=
  second_inequality_density
    (polarDensityBridge h34)
    h41a
    h48
    congruenceFinitenessBridge
    splittingRayBridge

end

end Towers.CField.DDensit
