import Mathlib.RingTheory.DedekindDomain.Different
import Mathlib.RingTheory.DedekindDomain.Instances
import Mathlib.Algebra.Module.LocalizedModule.Int
import Mathlib.RingTheory.Localization.Finiteness


/-!
# Localization of the different

The trace dual commutes with localization for a finite integral module.
Taking inverses then shows that the different ideal commutes with
localization.  This supplies the local-to-global compatibility used in
Milne, Theorem 8.42.
-/

namespace Towers.NumberTheory.Milne

open Module
open scoped Pointwise

universe u

variable {A Aₘ B Bₘ K L : Type u}
variable [CommRing A] [CommRing Aₘ] [CommRing B] [CommRing Bₘ]
variable [Field K] [Field L]
variable [Algebra A Aₘ] [Algebra A B] [Algebra A K] [Algebra A L]
variable [Algebra A Bₘ] [Algebra Aₘ Bₘ] [Algebra Aₘ K] [Algebra Aₘ L]
variable [Algebra B Bₘ] [Algebra B L] [Algebra Bₘ L] [Algebra K L]
variable [IsScalarTower A Aₘ Bₘ] [IsScalarTower A B Bₘ]
variable [IsScalarTower A Aₘ K] [IsScalarTower A K L]
variable [IsScalarTower Aₘ K L] [IsScalarTower Aₘ Bₘ L]
variable [IsScalarTower B Bₘ L] [IsScalarTower A B L]

omit [Algebra A Bₘ] [IsScalarTower A Aₘ Bₘ] [IsScalarTower A B Bₘ] in
theorem localized_dual_one (M : Submonoid A)
    [IsLocalization M Aₘ] [IsLocalization (M.map (algebraMap A B)) Bₘ]
    [IsLocalizedModule (M.map (algebraMap A B))
      (LinearMap.id (R := B) (M := L))]
    [Module.Finite A B] :
    (Submodule.traceDual A K (1 : Submodule B L)).localized' Bₘ
        (M.map (algebraMap A B)) (LinearMap.id (R := B) (M := L)) =
      Submodule.traceDual Aₘ K (1 : Submodule Bₘ L) := by
  have traceForm_smul_left (a : A) (u v : L) :
      Algebra.traceForm K L (a • u) v =
        algebraMap A K a * Algebra.traceForm K L u v := by
    rw [Algebra.traceForm_apply, Algebra.traceForm_apply]
    calc
      Algebra.trace K L ((a • u) * v) =
          Algebra.trace K L ((algebraMap A K a) • (u * v)) := by
        congr 1
        simp [Algebra.smul_def, IsScalarTower.algebraMap_apply A K L, mul_assoc]
      _ = (algebraMap A K a) • Algebra.trace K L (u * v) := by rw [map_smul]
      _ = algebraMap A K a * Algebra.trace K L (u * v) := by rw [smul_eq_mul]
  have traceForm_smul_right (a : A) (u v : L) :
      Algebra.traceForm K L u (a • v) =
        algebraMap A K a * Algebra.traceForm K L u v := by
    rw [Algebra.traceForm_apply, Algebra.traceForm_apply]
    calc
      Algebra.trace K L (u * (a • v)) =
          Algebra.trace K L ((algebraMap A K a) • (u * v)) := by
        congr 1
        simp [Algebra.smul_def, IsScalarTower.algebraMap_apply A K L,
          mul_comm, mul_assoc]
      _ = (algebraMap A K a) • Algebra.trace K L (u * v) := by rw [map_smul]
      _ = algebraMap A K a * Algebra.trace K L (u * v) := by rw [smul_eq_mul]
  ext x
  constructor
  · intro hxloc
    rw [Submodule.localized'_eq_span] at hxloc
    apply (Submodule.span_le.mpr ?_) hxloc
    rintro y ⟨y, hy, rfl⟩
    change y ∈ Submodule.traceDual A K (1 : Submodule B L) at hy
    change y ∈ Submodule.traceDual Aₘ K (1 : Submodule Bₘ L)
    rw [Submodule.mem_traceDual] at hy ⊢
    intro z hz
    rcases hz with ⟨c, rfl⟩
    rw [LinearMap.toSpanSingleton_apply]
    obtain ⟨⟨b, t⟩, ht⟩ := IsLocalization.surj (M.map (algebraMap A B)) c
    rcases t.property with ⟨a, ha, hat⟩
    rw [show c • (1 : L) = algebraMap Bₘ L c by simp [Algebra.smul_def]]
    have hden : a • algebraMap Bₘ L c = algebraMap B L b := by
      have h := congrArg (algebraMap Bₘ L) ht
      simp only [map_mul] at h
      calc
        a • algebraMap Bₘ L c =
            algebraMap Bₘ L c * algebraMap Bₘ L (algebraMap B Bₘ t) := by
          rw [Algebra.smul_def, IsScalarTower.algebraMap_apply A B L, ← hat,
            IsScalarTower.algebraMap_apply B Bₘ L]
          ring
        _ = algebraMap Bₘ L (algebraMap B Bₘ b) := h
        _ = algebraMap B L b := by rw [← IsScalarTower.algebraMap_apply B Bₘ L]
    obtain ⟨q, hq⟩ := hy (algebraMap B L b) ⟨b, by
      rw [LinearMap.toSpanSingleton_apply]
      simp [Algebra.smul_def]⟩
    have htrace : algebraMap A K a *
        Algebra.traceForm K L y (algebraMap Bₘ L c) =
          Algebra.traceForm K L y (algebraMap B L b) := by
      calc
        algebraMap A K a * Algebra.traceForm K L y (algebraMap Bₘ L c) =
            Algebra.traceForm K L y (a • algebraMap Bₘ L c) :=
          (traceForm_smul_right a y (algebraMap Bₘ L c)).symm
        _ = Algebra.traceForm K L y (algebraMap B L b) := congrArg _ hden
    let ma : M := ⟨a, ha⟩
    let w : Aₘ := IsLocalization.mk' Aₘ q ma
    refine ⟨w, ?_⟩
    have hunit : IsUnit (algebraMap A K a) := by
      rw [IsScalarTower.algebraMap_apply A Aₘ K]
      exact (IsLocalization.map_units Aₘ ma).map (algebraMap Aₘ K)
    apply hunit.mul_left_cancel
    calc
      algebraMap A K a * algebraMap Aₘ K w =
          algebraMap Aₘ K (algebraMap A Aₘ a * w) := by
        rw [map_mul, ← IsScalarTower.algebraMap_apply A Aₘ K]
      _ = algebraMap Aₘ K (algebraMap A Aₘ q) := by
        dsimp only [w]
        have hspec : algebraMap A Aₘ a * IsLocalization.mk' Aₘ q ma =
            algebraMap A Aₘ q := by
          simp [ma]
        rw [hspec]
      _ = algebraMap A K q := by rw [← IsScalarTower.algebraMap_apply A Aₘ K]
      _ = Algebra.traceForm K L y (algebraMap B L b) := hq
      _ = algebraMap A K a * Algebra.traceForm K L y (algebraMap Bₘ L c) :=
        htrace.symm
  · intro hx
    rw [Submodule.mem_traceDual] at hx
    obtain ⟨n, g, hg⟩ := Module.Finite.exists_fin (R := A) (M := B)
    have hgen : ∀ i, ∃ z : Aₘ,
        algebraMap Aₘ K z = Algebra.traceForm K L x (algebraMap B L (g i)) := by
      intro i
      obtain ⟨z, hz⟩ := hx (algebraMap B L (g i))
        ⟨algebraMap B Bₘ (g i),
          by
            rw [LinearMap.toSpanSingleton_apply]
            rw [Algebra.smul_def]
            rw [mul_one, ← IsScalarTower.algebraMap_apply B Bₘ L]⟩
      exact ⟨z, hz⟩
    choose z hz using hgen
    obtain ⟨s, hs⟩ := IsLocalization.exist_integer_multiples_of_finite M z
    let t : M.map (algebraMap A B) :=
      ⟨algebraMap A B s, ⟨(s : A), s.property, rfl⟩⟩
    rw [Submodule.mem_localized']
    refine ⟨(s : A) • x, ?_, t, ?_⟩
    · rw [Submodule.mem_traceDual]
      intro b hb
      rcases hb with ⟨b, rfl⟩
      rw [LinearMap.toSpanSingleton_apply,
        show b • (1 : L) = algebraMap B L b by simp [Algebra.smul_def]]
      have hbspan : b ∈ Submodule.span A (Set.range g) := by
        rw [hg]
        exact Submodule.mem_top
      refine Submodule.span_induction (p := fun b _ ↦
        Algebra.traceForm K L ((s : A) • x) (algebraMap B L b) ∈
          (algebraMap A K).range) ?_ ?_ ?_ ?_ hbspan
      · intro b hb
        rcases hb with ⟨i, rfl⟩
        rcases hs i with ⟨a, ha⟩
        refine ⟨a, ?_⟩
        calc
          algebraMap A K a = algebraMap Aₘ K (algebraMap A Aₘ a) := by
            rw [IsScalarTower.algebraMap_apply A Aₘ K]
          _ = algebraMap Aₘ K ((s : A) • z i) := congrArg (algebraMap Aₘ K) ha
          _ = algebraMap A K s * algebraMap Aₘ K (z i) := by
            simp [Algebra.smul_def, IsScalarTower.algebraMap_apply A Aₘ K]
          _ = algebraMap A K s *
              Algebra.traceForm K L x (algebraMap B L (g i)) := by rw [hz i]
          _ = Algebra.traceForm K L ((s : A) • x) (algebraMap B L (g i)) :=
            (traceForm_smul_left (s : A) x (algebraMap B L (g i))).symm
      · exact ⟨0, by simp⟩
      · rintro b c _ _ ⟨a, ha⟩ ⟨d, hd⟩
        refine ⟨a + d, ?_⟩
        simp only [map_add, ha, hd, map_add]
      · rintro a b _ ⟨d, hd⟩
        refine ⟨a * d, ?_⟩
        rw [map_mul, hd]
        calc
          algebraMap A K a *
              Algebra.traceForm K L ((s : A) • x) (algebraMap B L b) =
              Algebra.traceForm K L ((s : A) • x)
                (a • algebraMap B L b) :=
            (traceForm_smul_right a ((s : A) • x) (algebraMap B L b)).symm
          _ = Algebra.traceForm K L ((s : A) • x)
                (algebraMap B L (a • b)) := by
            have hab : algebraMap B L (a • b) = a • algebraMap B L b := by
              simp [Algebra.smul_def, IsScalarTower.algebraMap_apply A B L]
            rw [hab]
    · simpa [t, Submonoid.smul_def, IsScalarTower.algebraMap_apply A B L] using
        (IsLocalizedModule.mk'_cancel (f := LinearMap.id (R := B) (M := L)) x
          t)

omit [Algebra A Bₘ] [IsScalarTower A Aₘ Bₘ] [IsScalarTower A B Bₘ] in
theorem different_ideal_localization
    [IsDomain A] [IsDomain Aₘ] [IsDomain B] [IsDomain Bₘ]
    [IsIntegrallyClosed A] [IsIntegrallyClosed Aₘ]
    [IsDedekindDomain B] [IsDedekindDomain Bₘ]
    [IsTorsionFree A B] [IsTorsionFree Aₘ Bₘ] [IsTorsionFree B Bₘ]
    [IsFractionRing A K] [IsFractionRing Aₘ K]
    [IsFractionRing B L] [IsFractionRing Bₘ L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    [IsIntegralClosure B A L] [IsIntegralClosure Bₘ Aₘ L]
    (M : Submonoid A) [IsLocalization M Aₘ]
    [IsLocalization (M.map (algebraMap A B)) Bₘ]
    [IsLocalizedModule (M.map (algebraMap A B))
      (LinearMap.id (R := B) (M := L))]
    [Module.Finite A B] :
    (differentIdeal A B).map (algebraMap B Bₘ) = differentIdeal Aₘ Bₘ := by
  rw [← FractionalIdeal.coeIdeal_inj (K := L)]
  rw [← FractionalIdeal.extendedHom_coeIdeal_eq_map (K := L) L Bₘ]
  rw [coeIdeal_differentIdeal A K L B, coeIdeal_differentIdeal Aₘ K L Bₘ]
  rw [map_inv₀]
  congr 1
  apply FractionalIdeal.coeToSubmodule_injective
  change ((FractionalIdeal.extendedHom L Bₘ (FractionalIdeal.dual A K 1)) :
      Submodule Bₘ L) =
    ((FractionalIdeal.dual Aₘ K 1 :
      FractionalIdeal (nonZeroDivisors Bₘ) L) : Submodule Bₘ L)
  rw [FractionalIdeal.extendedHom'_apply, FractionalIdeal.coe_extended_eq_span]
  rw [FractionalIdeal.coe_dual_one]
  let hf : nonZeroDivisors B ≤
      Submonoid.comap (algebraMap B Bₘ) (nonZeroDivisors Bₘ) :=
    nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
      (FaithfulSMul.algebraMap_injective B Bₘ)
  let fL : L →+* L := IsLocalization.map (S := L) L (algebraMap B Bₘ) hf
  change Submodule.span Bₘ
      (fL '' (↑(FractionalIdeal.dual A K
        (1 : FractionalIdeal (nonZeroDivisors B) L)) : Set L)) =
    Submodule.traceDual Aₘ K (1 : Submodule Bₘ L)
  have hmap : fL = RingHom.id L := by
    apply IsLocalization.ringHom_ext (nonZeroDivisors B)
    ext b
    simp [fL, ← IsScalarTower.algebraMap_apply B Bₘ L]
  rw [hmap]
  simp only [RingHom.id_apply]
  have hdual : (↑(FractionalIdeal.dual A K
      (1 : FractionalIdeal (nonZeroDivisors B) L)) : Set L) =
      ↑(Submodule.traceDual A K (1 : Submodule B L)) :=
    congrArg SetLike.coe (FractionalIdeal.coe_dual_one
      (A := A) (K := K) (L := L) (B := B))
  rw [hdual]
  simpa [Submodule.localized'_eq_span] using
    localized_dual_one (A := A) (Aₘ := Aₘ) (B := B) (Bₘ := Bₘ)
      (K := K) (L := L) M

end Towers.NumberTheory.Milne

namespace Towers.NumberTheory.Milne

open Module

noncomputable section

universe v

attribute [local instance] FractionRing.liftAlgebra
  FractionRing.isScalarTower_liftAlgebra
  Localization.AtPrime.liftAlgebra

variable {R S : Type v} [CommRing R] [CommRing S]
variable [IsDomain R] [IsDomain S]
variable [IsDedekindDomain R] [IsDedekindDomain S]
variable [Algebra R S] [Module.Finite R S] [Module.IsTorsionFree R S]
variable [IsIntegralClosure S R (FractionRing S)]
variable [Algebra.IsSeparable (FractionRing R) (FractionRing S)]

omit [IsDomain R] [IsDomain S] [IsDedekindDomain R] [IsDedekindDomain S] [IsTorsionFree R S]
  [IsIntegralClosure S R (FractionRing S)]
  [Algebra.IsSeparable (FractionRing R) (FractionRing S)] in
/-- If `P` is the unique prime above `p`, then localizing `S` at `P` is
also the localization obtained by inverting the image of `R \ p`. -/
theorem localization_primes_singleton
    (p : Ideal R) [p.IsPrime] (P : Ideal S) [P.IsPrime]
    (hP : p.primesOver S = {P}) :
    IsLocalization (p.primeCompl.map (algebraMap R S))
      (Localization.AtPrime P) := by
  letI : P.LiesOver p := (hP.ge rfl).2
  have hle : p.primeCompl.map (algebraMap R S) ≤ P.primeCompl := by
    rintro _ ⟨a, ha, rfl⟩
    exact (P.mem_of_liesOver p a).not.mp ha
  have hdiv : ∀ x ∈ P.primeCompl,
      ∃ y ∈ p.primeCompl.map (algebraMap R S), x ∣ y := by
    intro x hx
    obtain ⟨a, ha, hxa⟩ :=
      Ideal.exists_notMem_dvd_algebraMap_of_primesOver_eq_singleton hP x hx
    exact ⟨algebraMap R S a, ⟨a, ha, rfl⟩, hxa⟩
  exact (IsLocalization.iff_of_le_of_exists_dvd
    (M := p.primeCompl.map (algebraMap R S))
    (S := Localization.AtPrime P) P.primeCompl hle hdiv).mpr inferInstance

omit [IsDedekindDomain R] [IsDedekindDomain S] [IsIntegralClosure S R (FractionRing S)]
  [Algebra.IsSeparable (FractionRing R) (FractionRing S)] in
/-- The unique-prime localization above is torsion-free over the localized
base ring. -/
theorem torsion_primes_singleton
    (p : Ideal R) [p.IsPrime] (P : Ideal S) [P.IsPrime] [P.LiesOver p]
    (hP : p.primesOver S = {P}) :
    letI := Localization.AtPrime.algebraOfLiesOver p P
    Module.IsTorsionFree (Localization.AtPrime p) (Localization.AtPrime P) := by
  letI := Localization.AtPrime.algebraOfLiesOver p P
  letI : IsLocalization (p.primeCompl.map (algebraMap R S))
      (Localization.AtPrime P) :=
    localization_primes_singleton p P hP
  letI : IsLocalization (Algebra.algebraMapSubmonoid S p.primeCompl)
      (Localization.AtPrime P) := by
    simpa only [Algebra.algebraMapSubmonoid] using
      (inferInstance : IsLocalization (p.primeCompl.map (algebraMap R S))
        (Localization.AtPrime P))
  exact Module.IsTorsionFree.of_isLocalization R S p.primeCompl_le_nonZeroDivisors

/-- The different commutes with localization at a base prime.  The upper
ring here is the generally semilocal localization obtained by inverting the
image of the complement of `p`. -/
theorem different_prime_semilocal
    (p : Ideal R) [p.IsPrime] :
    (differentIdeal R S).map
        (algebraMap S
          (Localization (Algebra.algebraMapSubmonoid S p.primeCompl))) =
      differentIdeal (Localization.AtPrime p)
        (Localization (Algebra.algebraMapSubmonoid S p.primeCompl)) := by
  letI : IsLocalization (p.primeCompl.map (algebraMap R S))
      (Localization (Algebra.algebraMapSubmonoid S p.primeCompl)) := by
    simpa only [Algebra.algebraMapSubmonoid] using
      (Localization.isLocalization :
        IsLocalization (Algebra.algebraMapSubmonoid S p.primeCompl)
          (Localization (Algebra.algebraMapSubmonoid S p.primeCompl)))
  letI : IsLocalizedModule (p.primeCompl.map (algebraMap R S))
      (LinearMap.id (R := S) (M := FractionRing S)) :=
    isLocalizedModule_id (p.primeCompl.map (algebraMap R S))
      (FractionRing S)
      (Localization (Algebra.algebraMapSubmonoid S p.primeCompl))
  exact different_ideal_localization
    (A := R) (Aₘ := Localization.AtPrime p)
    (B := S)
    (Bₘ := Localization (Algebra.algebraMapSubmonoid S p.primeCompl))
    (K := FractionRing R) (L := FractionRing S) p.primeCompl

/-- If `P` is the unique prime above `p`, the semilocal localization is the
ordinary local ring `S_P`, so the relative different commutes with this
localization as well. -/
theorem different_ideal_singleton
    (p : Ideal R) [p.IsPrime] (P : Ideal S) [P.IsPrime] [P.LiesOver p]
    [Algebra (Localization.AtPrime p) (Localization.AtPrime P)]
    [Localization.AtPrime.IsLiesOverAlgebra p P]
    [Module.IsTorsionFree (Localization.AtPrime p) (Localization.AtPrime P)]
    (hP : p.primesOver S = {P}) :
    (differentIdeal R S).map
        (algebraMap S (Localization.AtPrime P)) =
      differentIdeal (Localization.AtPrime p) (Localization.AtPrime P) := by
  letI : IsLocalization (p.primeCompl.map (algebraMap R S))
      (Localization.AtPrime P) :=
    localization_primes_singleton p P hP
  letI : IsScalarTower (Localization.AtPrime p) (Localization.AtPrime P)
      (FractionRing S) := by
    apply IsScalarTower.of_algebraMap_eq'
    apply IsLocalization.ringHom_ext p.primeCompl
    ext a
    calc
      algebraMap (Localization.AtPrime p) (FractionRing S)
          (algebraMap R (Localization.AtPrime p) a) =
          algebraMap (FractionRing R) (FractionRing S)
            (algebraMap (Localization.AtPrime p) (FractionRing R)
              (algebraMap R (Localization.AtPrime p) a)) :=
        IsScalarTower.algebraMap_apply (Localization.AtPrime p)
          (FractionRing R) (FractionRing S) _
      _ = algebraMap (FractionRing R) (FractionRing S)
          (algebraMap R (FractionRing R) a) := by
        rw [← IsScalarTower.algebraMap_apply R (Localization.AtPrime p)
          (FractionRing R)]
      _ = algebraMap R (FractionRing S) a :=
        (IsScalarTower.algebraMap_apply R (FractionRing R)
          (FractionRing S) a).symm
      _ = algebraMap S (FractionRing S) (algebraMap R S a) :=
        IsScalarTower.algebraMap_apply R S (FractionRing S) a
      _ = algebraMap (Localization.AtPrime P) (FractionRing S)
          (algebraMap S (Localization.AtPrime P) (algebraMap R S a)) :=
        IsScalarTower.algebraMap_apply S (Localization.AtPrime P)
          (FractionRing S) (algebraMap R S a)
      _ = algebraMap (Localization.AtPrime P) (FractionRing S)
          (algebraMap R (Localization.AtPrime P) a) := by
        rw [IsScalarTower.algebraMap_apply R S (Localization.AtPrime P)]
      _ = algebraMap (Localization.AtPrime P) (FractionRing S)
          (algebraMap (Localization.AtPrime p) (Localization.AtPrime P)
            (algebraMap R (Localization.AtPrime p) a)) := by
        rw [← IsScalarTower.algebraMap_apply R (Localization.AtPrime p)
          (Localization.AtPrime P)]
  letI : IsLocalization (Algebra.algebraMapSubmonoid S p.primeCompl)
      (Localization.AtPrime P) := by
    simpa only [Algebra.algebraMapSubmonoid] using
      (inferInstance : IsLocalization (p.primeCompl.map (algebraMap R S))
        (Localization.AtPrime P))
  letI : Module.Finite (Localization.AtPrime p) (Localization.AtPrime P) :=
    Module.Finite.of_isLocalization R S p.primeCompl
  letI : IsLocalizedModule (p.primeCompl.map (algebraMap R S))
      (LinearMap.id (R := S) (M := FractionRing S)) :=
    isLocalizedModule_id (p.primeCompl.map (algebraMap R S))
      (FractionRing S) (Localization.AtPrime P)
  exact different_ideal_localization
    (A := R) (Aₘ := Localization.AtPrime p)
    (B := S) (Bₘ := Localization.AtPrime P)
    (K := FractionRing R) (L := FractionRing S) p.primeCompl

/-- The unique-prime localization formula with its torsion-free instance
constructed from the uniqueness hypothesis. -/
theorem different_primes_singleton
    (p : Ideal R) [p.IsPrime] (P : Ideal S) [P.IsPrime] [P.LiesOver p]
    (hP : p.primesOver S = {P}) :
    letI := Localization.AtPrime.algebraOfLiesOver p P
    letI : Module.IsTorsionFree (Localization.AtPrime p)
        (Localization.AtPrime P) :=
      torsion_primes_singleton p P hP
    (differentIdeal R S).map
        (algebraMap S (Localization.AtPrime P)) =
      differentIdeal (Localization.AtPrime p) (Localization.AtPrime P) := by
  letI := Localization.AtPrime.algebraOfLiesOver p P
  letI : Module.IsTorsionFree (Localization.AtPrime p)
      (Localization.AtPrime P) :=
    torsion_primes_singleton p P hP
  exact different_ideal_singleton p P hP

end

end Towers.NumberTheory.Milne
