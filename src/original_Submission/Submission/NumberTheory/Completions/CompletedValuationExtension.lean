import Submission.NumberTheory.Locals.CompleteDVRHenselian
import Submission.NumberTheory.Completions.PlaceFactorCorrespondence
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.DedekindDomain.Ideal.Basic
import Mathlib.RingTheory.Polynomial.Subring
import Mathlib.RingTheory.Valuation.Integral


/-!
# Valuation rings in an extension of completed places

An extension `w` of an absolute value `v` induces an isometric field map
between their completions.  This file restricts that map to the corresponding
valuation integer rings.  It is the ring map used in the completed local
extension occurring in Milne's proof of Theorem 8.42.
-/

namespace Submission.NumberTheory.Milne

open AbsoluteValue Polynomial
open scoped NormedField Valued

noncomputable section

variable {K L : Type*} [Field K] [Field L] [Algebra K L]
variable (v : AbsoluteValue K ℝ) (w : AbsoluteValue L ℝ)
variable [Fact v.IsNontrivial] [Fact w.IsNontrivial]
variable [IsUltrametricDist v.Completion] [IsUltrametricDist w.Completion]

private noncomputable local instance completionBaseNontriviallyNormedField :
    NontriviallyNormedField v.Completion :=
  NontriviallyNormedField.ofNormNeOne <| by
    rcases (Fact.out : v.IsNontrivial) with ⟨x, hx0, hx1⟩
    refine ⟨completionEmbedding v x, ?_, ?_⟩
    · intro hx
      apply hx0
      apply RingHom.injective (completionEmbedding v)
      rw [map_zero]
      exact hx
    · rwa [norm_completionEmbedding]

private noncomputable local instance completionUpperNontriviallyNormedField :
    NontriviallyNormedField w.Completion :=
  NontriviallyNormedField.ofNormNeOne <| by
    rcases (Fact.out : w.IsNontrivial) with ⟨x, hx0, hx1⟩
    refine ⟨completionEmbedding w x, ?_, ?_⟩
    · intro hx
      apply hx0
      apply RingHom.injective (completionEmbedding w)
      rw [map_zero]
      exact hx
    · rwa [norm_completionEmbedding]

/-- The valuation integer ring obtained from the canonical `ℝ≥0`-valued
valuation associated to the norm on an absolute-value completion. -/
abbrev completionIntegerRing : Subring v.Completion :=
  (NormedField.valuation (K := v.Completion)).integer

/-- A completed valuation integer ring which is a DVR is Henselian. -/
theorem integer_henselian_local
    [IsDiscreteValuationRing (completionIntegerRing v)] :
    HenselianLocalRing (completionIntegerRing v) :=
  valued_henselian_ring v.Completion

/-- The map on valuation integer rings induced by an extension of completed
places. -/
def integerLies
    (hwv : AbsoluteValue.LiesOver w v) :
    completionIntegerRing v →+* completionIntegerRing w :=
  ((completionLies v w hwv).comp
    (completionIntegerRing v).subtype).codRestrict
    (completionIntegerRing w) fun x => by
      change completionLies v w hwv (x : v.Completion) ∈
        completionIntegerRing w
      rw [Valuation.mem_integer_iff]
      change ‖completionLies v w hwv (x : v.Completion)‖₊ ≤ 1
      have hx : ‖(x : v.Completion)‖₊ ≤ 1 := by
        simpa only [NormedField.valuation_apply] using x.property
      have hx' : ‖(x : v.Completion)‖ ≤ 1 := by
        exact_mod_cast hx
      have hisom :=
        (completion_lies_isometry v w hwv).dist_eq
          (x : v.Completion) 0
      have hisom' :
          ‖completionLies v w hwv (x : v.Completion)‖ =
            ‖(x : v.Completion)‖ := by
        simpa only [dist_zero_right, map_zero] using hisom
      have hreal :
          ‖completionLies v w hwv (x : v.Completion)‖ ≤ 1 := by
        exact hisom'.le.trans hx'
      exact_mod_cast hreal

omit [Fact v.IsNontrivial] [Fact w.IsNontrivial] in
@[simp]
theorem integer_lies_coe
    (hwv : AbsoluteValue.LiesOver w v)
    (x : completionIntegerRing v) :
    ((integerLies v w hwv x :
      completionIntegerRing w) : w.Completion) =
      completionLies v w hwv (x : v.Completion) := rfl

omit [Fact v.IsNontrivial] [Fact w.IsNontrivial] in
/-- The map of completed valuation rings preserves norms. -/
theorem norm_integer_lies
    (hwv : AbsoluteValue.LiesOver w v)
    (x : completionIntegerRing v) :
    ‖integerLies v w hwv x‖ = ‖x‖ := by
  simpa only [dist_zero_right, map_zero] using
    (completion_lies_isometry v w hwv).dist_eq
      (x : v.Completion) 0

omit [Fact v.IsNontrivial] [Fact w.IsNontrivial] in
/-- The restricted map of completed valuation rings is injective. -/
theorem integer_lies_injective
    (hwv : AbsoluteValue.LiesOver w v) :
    Function.Injective (integerLies v w hwv) := by
  intro x y hxy
  apply Subtype.ext
  apply (completion_lies_isometry v w hwv).injective
  exact congrArg Subtype.val hxy

/-- The induced map between completed valuation rings is local. -/
theorem completion_integer_lies
    (hwv : AbsoluteValue.LiesOver w v) :
    IsLocalHom (integerLies v w hwv) := by
  apply IsLocalHom.mk
  intro x hx
  rw [Valued.integer.isUnit_iff_norm_eq_one] at hx ⊢
  rw [← norm_integer_lies v w hwv]
  exact hx

/-- The upper maximal ideal contracts to the lower maximal ideal. -/
theorem lies_comap_maximal
    (hwv : AbsoluteValue.LiesOver w v) :
    Ideal.comap (integerLies v w hwv)
        (IsLocalRing.maximalIdeal (completionIntegerRing w)) =
      IsLocalRing.maximalIdeal (completionIntegerRing v) := by
  letI : IsLocalHom (integerLies v w hwv) :=
    completion_integer_lies v w hwv
  exact IsLocalRing.maximalIdeal_comap _

/-- The canonical algebra structure on the completed valuation-ring
extension associated to `w | v`. -/
@[reducible] def completionIntegerLies
    (hwv : AbsoluteValue.LiesOver w v) :
    Algebra (completionIntegerRing v) (completionIntegerRing w) :=
  (integerLies v w hwv).toAlgebra

section IntegralClosure

variable (hwv : AbsoluteValue.LiesOver w v)

omit [Fact w.IsNontrivial] [IsUltrametricDist w.Completion] in
/-- The norm on the upper completion is the spectral norm of the completed
field extension. -/
theorem norm_spectral_completion
    (hAlg :
      letI : Algebra v.Completion w.Completion :=
        (completionLies v w hwv).toAlgebra
      Algebra.IsAlgebraic v.Completion w.Completion)
    (x : w.Completion) :
    letI : Algebra v.Completion w.Completion :=
      (completionLies v w hwv).toAlgebra
    ‖x‖ = spectralNorm v.Completion w.Completion x := by
  letI : Algebra v.Completion w.Completion :=
    (completionLies v w hwv).toAlgebra
  letI : Algebra.IsAlgebraic v.Completion w.Completion := hAlg
  let f : AbsoluteValue w.Completion ℝ :=
    NormedField.toAbsoluteValue w.Completion
  have hf : ∀ y : v.Completion,
      f (algebraMap v.Completion w.Completion y) = ‖y‖ := by
    intro y
    change ‖completionLies v w hwv y‖ = ‖y‖
    simpa only [dist_zero_right, map_zero] using
      (completion_lies_isometry v w hwv).dist_eq y 0
  have heq : f = completeAbsoluteValue
      v.Completion w.Completion :=
    complete_absolute_unique v.Completion w.Completion f hf
  change f x = spectralNorm v.Completion w.Completion x
  rw [heq]
  rfl

set_option maxHeartbeats 1000000 in
-- Unfolding the two completion algebras and the lifted minimal polynomial is expensive.
omit [Fact w.IsNontrivial] in
/-- The upper completed valuation integer ring is integral over the lower
one whenever the completed field extension is algebraic. -/
theorem completion_integer_integral
    (hAlg :
      letI : Algebra v.Completion w.Completion :=
        (completionLies v w hwv).toAlgebra
      Algebra.IsAlgebraic v.Completion w.Completion) :
    letI : Algebra (completionIntegerRing v) (completionIntegerRing w) :=
      completionIntegerLies v w hwv
    Algebra.IsIntegral (completionIntegerRing v) (completionIntegerRing w) := by
  letI : Algebra v.Completion w.Completion :=
    (completionLies v w hwv).toAlgebra
  letI : Algebra.IsAlgebraic v.Completion w.Completion := hAlg
  letI : Algebra (completionIntegerRing v) (completionIntegerRing w) :=
    completionIntegerLies v w hwv
  rw [Algebra.isIntegral_def]
  intro x
  let y : w.Completion := x
  let p : Polynomial v.Completion := minpoly v.Completion y
  have hpmonic : p.Monic := minpoly.monic (Algebra.IsIntegral.isIntegral y)
  have hxnorm : ‖y‖ ≤ 1 := by
    have hxnn : ‖y‖₊ ≤ 1 := by
      simpa only [y, NormedField.valuation_apply] using x.property
    exact_mod_cast hxnn
  have hspectral : spectralValue p ≤ 1 := by
    change spectralNorm v.Completion w.Completion y ≤ 1
    rw [← norm_spectral_completion v w hwv hAlg y]
    exact hxnorm
  have hcoeff : ∀ n : ℕ, ‖p.coeff n‖ ≤ 1 :=
    (spectralValue_le_one_iff hpmonic).mp hspectral
  have hpcoeffs : (↑p.coeffs : Set v.Completion) ⊆ completionIntegerRing v := by
    intro c hc
    change (NormedField.valuation (K := v.Completion)) c ≤ 1
    change ‖c‖₊ ≤ 1
    obtain ⟨n, _hn, rfl⟩ := Polynomial.mem_coeffs_iff.mp hc
    exact_mod_cast hcoeff n
  let q : Polynomial (completionIntegerRing v) :=
    p.toSubring (completionIntegerRing v) hpcoeffs
  refine ⟨q, (Polynomial.monic_toSubring p
    (completionIntegerRing v) hpcoeffs).mpr hpmonic, ?_⟩
  apply Subtype.ext
  change (completionIntegerRing w).subtype
      (Polynomial.eval₂
        (algebraMap (completionIntegerRing v) (completionIntegerRing w)) x q) =
    (completionIntegerRing w).subtype 0
  rw [Polynomial.hom_eval₂]
  change Polynomial.eval₂
      ((completionLies v w hwv).comp
        (completionIntegerRing v).subtype) y q = 0
  rw [← Polynomial.eval₂_map]
  rw [Polynomial.map_toSubring]
  change aeval y (minpoly v.Completion y) = 0
  exact minpoly.aeval v.Completion y

set_option synthInstance.maxHeartbeats 100000 in
-- Typeclass search must reconstruct the compatible subring and fraction-field tower.
set_option maxHeartbeats 1000000 in
-- Elaborating the compatible algebra tower through the two subrings is expensive.
omit [Fact w.IsNontrivial] in
/-- The upper completed valuation integer ring is the integral closure of
the lower one in the upper completed field. -/
theorem completion_integer_closure
    (hAlg :
      letI : Algebra v.Completion w.Completion :=
        (completionLies v w hwv).toAlgebra
      Algebra.IsAlgebraic v.Completion w.Completion) :
    letI : Algebra (completionIntegerRing v) (completionIntegerRing w) :=
      completionIntegerLies v w hwv
    letI : Algebra (completionIntegerRing w) w.Completion :=
      (completionIntegerRing w).subtype.toAlgebra
    letI : Algebra (completionIntegerRing v) w.Completion :=
      ((completionLies v w hwv).comp
        (completionIntegerRing v).subtype).toAlgebra
    IsIntegralClosure (completionIntegerRing w)
      (completionIntegerRing v) w.Completion := by
  letI : Algebra v.Completion w.Completion :=
    (completionLies v w hwv).toAlgebra
  letI : Algebra.IsAlgebraic v.Completion w.Completion := hAlg
  letI : Algebra (completionIntegerRing v) (completionIntegerRing w) :=
    completionIntegerLies v w hwv
  letI : Algebra (completionIntegerRing w) w.Completion :=
    (completionIntegerRing w).subtype.toAlgebra
  letI : Algebra (completionIntegerRing v) w.Completion :=
    ((completionLies v w hwv).comp
      (completionIntegerRing v).subtype).toAlgebra
  letI : IsScalarTower (completionIntegerRing v)
      (completionIntegerRing w) w.Completion :=
    IsScalarTower.of_algebraMap_eq' rfl
  letI : Algebra.IsIntegral (completionIntegerRing v)
      (completionIntegerRing w) :=
    completion_integer_integral v w hwv hAlg
  letI : IsFractionRing (completionIntegerRing w) w.Completion :=
    (Valuation.integer.integers
      (NormedField.valuation (K := w.Completion))).isFractionRing
  letI : IsIntegrallyClosed (completionIntegerRing w) :=
    (Valuation.integer.integers
      (NormedField.valuation (K := w.Completion))).isIntegrallyClosed
  exact IsIntegralClosure.of_isIntegrallyClosed
    (completionIntegerRing w) (completionIntegerRing v) w.Completion

set_option synthInstance.maxHeartbeats 100000 in
-- The same compatible completion tower is used twice by `IsIntegralClosure.finite`.
set_option maxHeartbeats 1000000 in
omit [Fact w.IsNontrivial] in
/-- A finite separable extension of completed fields induces a finite
extension of their valuation integer rings, provided the lower ring is a
discrete valuation ring. -/
theorem completion_integer_module
    [IsDiscreteValuationRing (completionIntegerRing v)]
    (hFinite :
      letI : Algebra v.Completion w.Completion :=
        (completionLies v w hwv).toAlgebra
      FiniteDimensional v.Completion w.Completion)
    (hSeparable :
      letI : Algebra v.Completion w.Completion :=
        (completionLies v w hwv).toAlgebra
      Algebra.IsSeparable v.Completion w.Completion) :
    letI : Algebra (completionIntegerRing v) (completionIntegerRing w) :=
      completionIntegerLies v w hwv
    Module.Finite (completionIntegerRing v) (completionIntegerRing w) := by
  letI : Algebra v.Completion w.Completion :=
    (completionLies v w hwv).toAlgebra
  letI : FiniteDimensional v.Completion w.Completion := hFinite
  letI : Algebra.IsSeparable v.Completion w.Completion := hSeparable
  letI : Algebra (completionIntegerRing v) (completionIntegerRing w) :=
    completionIntegerLies v w hwv
  letI : Algebra (completionIntegerRing w) w.Completion :=
    (completionIntegerRing w).subtype.toAlgebra
  letI : Algebra (completionIntegerRing v) w.Completion :=
    ((completionLies v w hwv).comp
      (completionIntegerRing v).subtype).toAlgebra
  letI : IsScalarTower (completionIntegerRing v)
      (completionIntegerRing w) w.Completion :=
    IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower (completionIntegerRing v)
      v.Completion w.Completion :=
    IsScalarTower.of_algebraMap_eq' rfl
  letI : IsFractionRing (completionIntegerRing v) v.Completion :=
    (Valuation.integer.integers
      (NormedField.valuation (K := v.Completion))).isFractionRing
  letI : IsIntegralClosure (completionIntegerRing w)
      (completionIntegerRing v) w.Completion :=
    completion_integer_closure v w hwv
      (Algebra.IsSeparable.isAlgebraic v.Completion w.Completion)
  exact IsIntegralClosure.finite (completionIntegerRing v)
    v.Completion w.Completion (completionIntegerRing w)

end IntegralClosure

/-- Ideal divisibility descends after extending both ideals along a
faithfully flat algebra. -/
theorem dvd_faithfully_flat
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [IsDedekindDomain R] [IsDedekindDomain S]
    [Module.FaithfullyFlat R S]
    (D m : Ideal R)
    (hbound : D.map (algebraMap R S) ∣ m.map (algebraMap R S)) :
    D ∣ m := by
  rw [Ideal.dvd_iff_le] at hbound ⊢
  rw [← Ideal.comap_map_eq_self_of_faithfullyFlat (B := S) m,
    ← Ideal.comap_map_eq_self_of_faithfullyFlat (B := S) D]
  exact Ideal.comap_mono hbound

/-- Divisibility of extended ideals descends along a faithfully flat
algebra.  This is the final formal ideal step after identifying a completed
different and maximal ideal as extensions of their localized counterparts. -/
theorem ideal_faithfully_flat
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [IsDedekindDomain R] [IsDedekindDomain S] [Module.FaithfullyFlat R S]
    (D m : Ideal R) (Dhat mhat : Ideal S) (n : ℕ)
    (hD : Ideal.map (algebraMap R S) D = Dhat)
    (hm : Ideal.map (algebraMap R S) m = mhat)
    (hbound : Dhat ∣ mhat ^ n) :
    D ∣ m ^ n := by
  rw [Ideal.dvd_iff_le] at hbound ⊢
  rw [← Ideal.comap_map_eq_self_of_faithfullyFlat (B := S) (m ^ n),
    ← Ideal.comap_map_eq_self_of_faithfullyFlat (B := S) D]
  apply Ideal.comap_mono
  rw [Ideal.map_pow, hD, hm]
  exact hbound

end

end Submission.NumberTheory.Milne
