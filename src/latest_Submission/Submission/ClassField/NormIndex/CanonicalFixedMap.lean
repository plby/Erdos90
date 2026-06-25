import Submission.ClassField.CohomologyOps.HilbertNinetyCoboundary
import Submission.ClassField.NormIndex.InfiniteIdeleCompatibility

/-!
# The canonical fixed-class map

This file proves the two concrete ingredients in Lemma VII.4.1 for the
coordinatewise idèle-extension map.  The first part establishes injectivity
of that map from the injectivity of every completed-field embedding, and
uses it to descend a principal extended idèle back to the base field.
-/

namespace Submission.CField.NIndex

open AbsoluteValue Ideal IsDedekindDomain NumberField
open Submission.NumberTheory.Milne
open Submission.CField.Ideles
open Submission.CField.ICohomo
open groupCohomology

noncomputable section

universe u

variable {K L : Type u} [Field K] [Field L]
  [NumberField K] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

set_option maxRecDepth 100000 in
omit [FiniteDimensional K L] [IsGalois K L] in
/-- Coordinate extension between two finite completed fields is injective. -/
theorem extension_monoid_injective
    (Q : HeightOneSpectrum (NumberField.RingOfIntegers L)) :
    Function.Injective
      (extensionMonoidHom (K := K) (L := L) Q) := by
  intro x y hxy
  apply Units.ext
  apply (coordinateExtensionHom (K := K) (L := L) Q).injective
  have hxy' := congrArg Units.val hxy
  rw [extension_monoid_val,
    extension_monoid_val] at hxy'
  exact hxy'

/-- A prime factor above a given finite base prime. -/
private noncomputable def chosenUpperExtension
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    UpperPrimeFactors (K := K) (L := L) P := by
  let q : P.asIdeal.primesOver (NumberField.RingOfIntegers L) :=
    Classical.choice inferInstance
  exact ⟨q.1,
    (IsDedekindDomain.mem_primesOverFinset_iff
      (B := NumberField.RingOfIntegers L) P.ne_bot).2 q.2⟩

set_option maxRecDepth 100000 in
omit [FiniteDimensional K L] [IsGalois K L] in
/-- Coordinate extension of finite idèles is injective. -/
theorem idele_monoid_injective :
    Function.Injective
      (ideleMonoidHom (K := K) (L := L)) := by
  intro x y hxy
  apply RestrictedProduct.ext
  intro P
  let q : UpperPrimeFactors (K := K) (L := L) P :=
    chosenUpperExtension (K := K) (L := L) P
  let Q : HeightOneSpectrum (NumberField.RingOfIntegers L) :=
    upperPrime (K := K) (L := L) P q
  have hQ : Q.under (NumberField.RingOfIntegers K) = P :=
    upperPrime_under (K := K) (L := L) P q
  have hcoord := congrArg (fun z => z.1 Q) hxy
  change extensionMonoidHom (K := K) (L := L) Q
      (x.1 (Q.under (NumberField.RingOfIntegers K))) =
    extensionMonoidHom (K := K) (L := L) Q
      (y.1 (Q.under (NumberField.RingOfIntegers K))) at hcoord
  have hbase := extension_monoid_injective
    (K := K) (L := L) Q hcoord
  rw [hQ] at hbase
  exact hbase

omit [NumberField K] [NumberField L] [FiniteDimensional K L] in
/-- Coordinate extension of the infinite adele ring is injective. -/
theorem infinite_adele_injective :
    Function.Injective
      (infiniteAdeleHom (K := K) (L := L)) := by
  intro x y hxy
  funext v
  let w : InfinitePlace L :=
    Classical.choose (InfinitePlace.comap_surjective (K := L) v)
  have hw : w.comap (algebraMap K L) = v :=
    Classical.choose_spec (InfinitePlace.comap_surjective (K := L) v)
  have hcoord := congrFun hxy w
  change completionLies
      (w.comap (algebraMap K L)).1 w.1
      (infinite_lies_comap
        (w.comap (algebraMap K L)) w rfl)
      (x (w.comap (algebraMap K L))) =
    completionLies
      (w.comap (algebraMap K L)).1 w.1
      (infinite_lies_comap
        (w.comap (algebraMap K L)) w rfl)
      (y (w.comap (algebraMap K L))) at hcoord
  have hbase := (completion_lies_isometry
    (w.comap (algebraMap K L)).1 w.1
    (infinite_lies_comap
      (w.comap (algebraMap K L)) w rfl)).injective hcoord
  rw [hw] at hbase
  exact hbase

set_option maxRecDepth 100000 in
omit [NumberField K] [NumberField L] [FiniteDimensional K L] in
/-- Coordinate extension of infinite idèles is injective. -/
theorem infinite_monoid_injective :
    Function.Injective
      (infiniteMonoidHom (K := K) (L := L)) := by
  intro x y hxy
  apply Units.ext
  apply infinite_adele_injective (K := K) (L := L)
  exact congrArg Units.val hxy

set_option maxRecDepth 100000 in
omit [FiniteDimensional K L] in
/-- The full coordinatewise idèle-extension map is injective. -/
theorem idele_extension_monoid :
    Function.Injective (ideleExtensionMonoid (K := K) (L := L)) := by
  intro x y hxy
  apply Prod.ext
  · exact infinite_monoid_injective (K := K) (L := L)
      (congrArg Prod.fst hxy)
  · exact idele_monoid_injective (K := K) (L := L)
      (congrArg Prod.snd hxy)

set_option maxRecDepth 100000 in
/-- If the canonical extension of an idèle is principal, the original idèle
was already principal over the base field. -/
theorem canonical_principal_descent :
    (principalIdeles (NumberField.RingOfIntegers L) L).comap
        (canonicalExtensionData (K := K) (L := L)).toMonoidHom =
      principalIdeles (NumberField.RingOfIntegers K) K := by
  apply le_antisymm
  · intro x hx
    obtain ⟨b, hb⟩ := hx
    let D := concreteActionData (K := K) (L := L)
    have hb_fixed (sigma : Gal(L/K)) :
        Units.map sigma.toRingEquiv.toRingHom b = b := by
      apply principalIdele_injective (NumberField.RingOfIntegers L) L
      calc
        principalIdele (NumberField.RingOfIntegers L) L
            (Units.map sigma.toRingEquiv.toRingHom b) =
            D.action.smul sigma
              (principalIdele (NumberField.RingOfIntegers L) L b) :=
          (D.smul_principalIdele sigma b).symm
        _ = D.action.smul sigma
              (ideleExtensionMonoid (K := K) (L := L) x) :=
          congrArg (D.action.smul sigma) hb
        _ = ideleExtensionMonoid (K := K) (L := L) x :=
          idele_monoid_fixed (K := K) (L := L) sigma x
        _ = principalIdele (NumberField.RingOfIntegers L) L b := hb.symm
    have hb_val_fixed (sigma : Gal(L/K)) : sigma (b : L) = (b : L) :=
      congrArg Units.val (hb_fixed sigma)
    obtain ⟨a, ha⟩ :=
      (IsGalois.mem_range_algebraMap_iff_fixed
        (F := K) (E := L) (b : L)).2 hb_val_fixed
    have ha0 : a ≠ 0 := by
      intro ha_zero
      rw [ha_zero, map_zero] at ha
      exact b.ne_zero ha.symm
    let aUnit : Kˣ := Units.mk0 a ha0
    have haUnit : Units.map (algebraMap K L) aUnit = b := by
      apply Units.ext
      exact ha
    refine ⟨aUnit, ?_⟩
    apply idele_extension_monoid (K := K) (L := L)
    calc
      ideleExtensionMonoid (K := K) (L := L)
          (principalIdele (NumberField.RingOfIntegers K) K aUnit) =
        principalIdele (NumberField.RingOfIntegers L) L
          (Units.map (algebraMap K L).toMonoidHom aUnit) :=
        idele_extension_principal (K := K) (L := L) aUnit
      _ = principalIdele (NumberField.RingOfIntegers L) L b :=
        congrArg (principalIdele (NumberField.RingOfIntegers L) L) haUnit
      _ = ideleExtensionMonoid (K := K) (L := L) x := hb
  · exact (canonicalExtensionData (K := K) (L := L)).main_ideles_lecomap

/-- Proposition VII.2.5(a) in the exact form needed for Lemma VII.4.1: every
fixed idèle is the coordinatewise extension of a base idèle. -/
def CanonicalFixedDescent : Prop :=
  ∀ (K L : Type u) [Field K] [Field L]
    [NumberField K] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (z : IdeleGroup (NumberField.RingOfIntegers L) L),
    (∀ sigma : Gal(L/K),
      (idelesGaloisAction (K := K) (L := L)).smul sigma z = z) →
    ∃ y : IdeleGroup (NumberField.RingOfIntegers K) K,
      ideleExtensionMonoid (K := K) (L := L) y = z

set_option maxHeartbeats 1000000 in
-- Quotient representatives, the idèle action, and Hilbert 90 all unfold in
-- the cocycle calculation.
set_option maxRecDepth 100000 in
/-- Hilbert 90 turns fixed-class lifting into fixed-idèle descent. -/
theorem canonical_fixed_lifting
    (hdesc : CanonicalFixedDescent.{u}) :
    ∀ c : fixedIdeleClasses (K := K) (L := L),
      ∃ y : IdeleGroup (NumberField.RingOfIntegers K) K,
        (canonicalExtensionData (K := K) (L := L)).class_map_fixed
          (QuotientGroup.mk'
            (principalIdeles (NumberField.RingOfIntegers K) K) y) = c := by
  letI := idelesGaloisAction (K := K) (L := L)
  letI := ideleDistribAction (K := K) (L := L)
  intro c
  obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective
    (principalIdeles (NumberField.RingOfIntegers L) L) c.1
  have hprincipal (sigma : Gal(L/K)) :
      sigma • x / x ∈ principalIdeles (NumberField.RingOfIntegers L) L := by
    apply QuotientGroup.eq_iff_div_mem.mp
    have hc := c.2 sigma
    change sigma • c.1 = c.1 at hc
    rw [← hx] at hc
    exact hc
  let f : Gal(L/K) → Lˣ := fun sigma => Classical.choose (hprincipal sigma)
  have hf_principal (sigma : Gal(L/K)) :
      principalIdele (NumberField.RingOfIntegers L) L (f sigma) =
        sigma • x / x :=
    Classical.choose_spec (hprincipal sigma)
  have hf : IsMulCocycle₁ f := by
    intro sigma tau
    apply principalIdele_injective (NumberField.RingOfIntegers L) L
    let D := concreteActionData (K := K) (L := L)
    calc
      principalIdele (NumberField.RingOfIntegers L) L (f (sigma * tau)) =
          (sigma * tau) • x / x := hf_principal (sigma * tau)
      _ = sigma • (tau • x) / x := by rw [mul_smul]
      _ = (sigma • (tau • x) / sigma • x) * (sigma • x / x) := by
        simp only [div_eq_mul_inv]
        calc
          sigma • tau • x * x⁻¹ =
              sigma • tau • x * ((sigma • x)⁻¹ * (sigma • x)) * x⁻¹ := by
            simp
          _ = (sigma • tau • x * (sigma • x)⁻¹) *
              (sigma • x * x⁻¹) := by ac_rfl
      _ = sigma • (tau • x / x) * (sigma • x / x) := by
        have hs : sigma • (tau • x / x) =
            sigma • (tau • x) / sigma • x := by
          simp only [div_eq_mul_inv, smul_mul', smul_inv']
        rw [hs]
      _ = sigma • principalIdele (NumberField.RingOfIntegers L) L (f tau) *
          principalIdele (NumberField.RingOfIntegers L) L (f sigma) := by
        rw [hf_principal tau, hf_principal sigma]
      _ = principalIdele (NumberField.RingOfIntegers L) L
          (sigma • f tau) *
          principalIdele (NumberField.RingOfIntegers L) L (f sigma) := by
        have hs : sigma • principalIdele (NumberField.RingOfIntegers L) L
              (f tau) =
            principalIdele (NumberField.RingOfIntegers L) L
              (sigma • f tau) := by
          change D.action.smul sigma
              (principalIdele (NumberField.RingOfIntegers L) L (f tau)) = _
          simpa using D.smul_principalIdele sigma (f tau)
        rw [hs]
      _ = principalIdele (NumberField.RingOfIntegers L) L
          (sigma • f tau * f sigma) := by rw [map_mul]
  obtain ⟨b, hb⟩ :=
    Submission.CField.COps.isMulCoboundary
      f hf
  let z := x / principalIdele (NumberField.RingOfIntegers L) L b
  have hz_fixed (sigma : Gal(L/K)) : sigma • z = z := by
    let D := concreteActionData (K := K) (L := L)
    have hσb : sigma • b = f sigma * b := eq_mul_of_div_eq (hb sigma)
    have hσx : sigma • x =
        principalIdele (NumberField.RingOfIntegers L) L (f sigma) * x :=
      eq_mul_of_div_eq (hf_principal sigma).symm
    dsimp only [z]
    have hsdiv : sigma •
        (x / principalIdele (NumberField.RingOfIntegers L) L b) =
        sigma • x /
          (sigma • principalIdele (NumberField.RingOfIntegers L) L b) := by
      simp only [div_eq_mul_inv, smul_mul', smul_inv']
    rw [hsdiv]
    have hsp : sigma • principalIdele (NumberField.RingOfIntegers L) L b =
        principalIdele (NumberField.RingOfIntegers L) L (sigma • b) := by
      change D.action.smul sigma
          (principalIdele (NumberField.RingOfIntegers L) L b) = _
      simpa using D.smul_principalIdele sigma b
    rw [hsp, hσb, map_mul, hσx]
    simp only [div_eq_mul_inv]
    calc
      (principalIdele (NumberField.RingOfIntegers L) L (f sigma) * x) *
          ((principalIdele (NumberField.RingOfIntegers L) L b)⁻¹ *
            (principalIdele (NumberField.RingOfIntegers L) L (f sigma))⁻¹) =
          (principalIdele (NumberField.RingOfIntegers L) L (f sigma) *
            (principalIdele (NumberField.RingOfIntegers L) L (f sigma))⁻¹) *
            (x * (principalIdele (NumberField.RingOfIntegers L) L b)⁻¹) := by
        ac_rfl
      _ = x * (principalIdele (NumberField.RingOfIntegers L) L b)⁻¹ := by
        simp
  obtain ⟨y, hy⟩ := hdesc K L z hz_fixed
  refine ⟨y, ?_⟩
  apply Subtype.ext
  change QuotientGroup.mk'
      (principalIdeles (NumberField.RingOfIntegers L) L)
      (ideleExtensionMonoid (K := K) (L := L) y) = c.1
  rw [hy, ← hx]
  dsimp only [z]
  rw [map_div]
  have hbq : QuotientGroup.mk'
      (principalIdeles (NumberField.RingOfIntegers L) L)
      (principalIdele (NumberField.RingOfIntegers L) L b) = 1 :=
    (QuotientGroup.eq_one_iff _).2 ⟨b, rfl⟩
  rw [hbq, div_one]

end

end Submission.CField.NIndex
