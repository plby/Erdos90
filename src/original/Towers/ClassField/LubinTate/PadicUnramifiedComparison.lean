import Towers.ClassField.LubinTate.PadicUniformizerRoot
import Towers.ClassField.LubinTate.RootFieldRamification
import Towers.ClassField.LubinTate.LocalArtinMap
import Towers.ClassField.LocalBrauer.SpectralIntegerClosure
import Towers.NumberTheory.Locals.AbsoluteValueExamples
import Mathlib.RingTheory.Valuation.Discrete.RankOne

/-!
# The unramified comparison behind the cyclotomic unit formula

This file compares the norm valuation on a finite cyclotomic Lubin--Tate
root field with the discrete valuation inherited from the common Witt-root
DVR.  The first step is integral: spectral integers map into the Witt-root
ring itself, not merely into its fraction field.
-/

namespace Towers.CField.LTate

open Towers.NumberTheory.Milne
open Towers.CField.LBrauer
open scoped NNReal NormedField Topology

noncomputable section

variable (p : ℕ) [Fact p.Prime]
variable (k : Type*) [Field k] [CharP k p] [IsAlgClosed k]

private abbrev B (n : ℕ) := PadicWittRing p k n
private abbrev C (n : ℕ) := FractionRing (B p k n)
private abbrev L (n : ℕ) :=
  (cyclotomicLubinDatum p).RootField ℚ_[p] n
private abbrev M (n : ℕ) (u : ℤ_[p]ˣ) :=
  wittComparisonCompositum p k n u
private abbrev F (n : ℕ) (u : ℤ_[p]ˣ) :=
  padicCyclotomicComparison p k n u

/-- The canonical spectral valuation on a finite `Q_p`-algebra, packaged
without exposing a dependent instance telescope in later ring types. -/
@[implicit_reducible]
private noncomputable def qpadicSpectralValuation
    (E : Type*) [Field E] [Algebra ℚ_[p] E] [FiniteDimensional ℚ_[p] E] :
    Valuation E ℝ≥0 := by
  letI : Algebra.IsAlgebraic ℚ_[p] E :=
    Algebra.IsAlgebraic.of_finite ℚ_[p] E
  letI : NormedField E := spectralNorm.normedField ℚ_[p] E
  letI : NormedAlgebra ℚ_[p] E := spectralNorm.normedAlgebra ℚ_[p] E
  letI : IsUltrametricDist E := IsUltrametricDist.of_normedAlgebra ℚ_[p]
  exact NormedField.valuation

local instance padicWittUnramifiedValuativeRel : ValuativeRel ℚ_[p] :=
  ValuativeRel.ofValuation (NormedField.valuation (K := ℚ_[p]))

local instance padicWittUnramifiedCompatible :
    Valuation.Compatible (NormedField.valuation (K := ℚ_[p])) :=
  Valuation.Compatible.ofValuation (NormedField.valuation (K := ℚ_[p]))

local instance padicWittUnramifiedLocalField :
    IsNonarchimedeanLocalField ℚ_[p] := by
  haveI htop : IsValuativeTopology ℚ_[p] := by
    apply IsValuativeTopology.of_zero
    intro s
    rw [show s ∈ 𝓝 (0 : ℚ_[p]) ↔
        ∃ γ : (MonoidWithZeroHom.ValueGroup₀
            (NormedField.valuation (K := ℚ_[p])))ˣ,
          {x | (NormedField.valuation (K := ℚ_[p])).restrict x < γ.1} ⊆ s from
      (NormedField.toValued (K := ℚ_[p])).is_topological_valuation s]
    simpa using
      (NormedField.valuation (K := ℚ_[p]))
        |>.exists_setOf_restrict_le_iff 0 s
  haveI hnontrivial : ValuativeRel.IsNontrivial ℚ_[p] :=
    (ValuativeRel.isNontrivial_iff_isNontrivial
      (NormedField.valuation (K := ℚ_[p]))).mpr inferInstance
  exact
    { toIsValuativeTopology := htop
      toLocallyCompactSpace := inferInstance
      toIsNontrivial := hnontrivial }

/-- The spectral norm is unchanged by changing the algebraic presentation
of a finite extension. -/
private theorem spectral_alg_equiv
    (K : Type*) [NormedField K]
    (E F : Type*) [Field E] [Field F] [Algebra K E] [Algebra K F]
    (e : E ≃ₐ[K] F) (x : E) :
    spectralNorm K E x = spectralNorm K F (e x) := by
  simp only [spectralNorm, minpoly.algEquiv_eq]

/-- The residue field of `Q_p`, in the norm-valuation presentation used by
the canonical unramified tower, has cardinality `p`. -/
theorem padic_local_card :
    Towers.CField.LFTheory.localResidueCardinality ℚ_[p] = p := by
  let A := Valuation.integer (NormedField.valuation (K := ℚ_[p]))
  let D := lubinTateDatum p (1 : ℤ_[p]ˣ)
  have hmax : IsLocalRing.maximalIdeal A = Ideal.span {D.pi} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer D.pi).mp
      D.pi_irreducible
  change Nat.card (A ⧸ IsLocalRing.maximalIdeal A) = p
  rw [hmax]
  exact D.residueCard

set_option maxHeartbeats 5000000 in
-- The Lubin--Tate ramification theorem carries a long dependent spectral
-- local-field instance telescope.
set_option synthInstance.maxHeartbeats 500000 in
/-- Every transported basic `p * u` Lubin--Tate root field is totally
ramified over `Q_p`, hence its residue field also has cardinality `p`. -/
theorem padic_integer_card
    (n : ℕ) (u : ℤ_[p]ˣ) :
    let E := (lubinTateDatum p u).RootField ℚ_[p] n
    letI : Algebra.IsAlgebraic ℚ_[p] E :=
      Algebra.IsAlgebraic.of_finite ℚ_[p] E
    letI : NontriviallyNormedField E :=
      spectralNorm.nontriviallyNormedField ℚ_[p] E
    letI : NormedAlgebra ℚ_[p] E := spectralNorm.normedAlgebra ℚ_[p] E
    letI : IsUltrametricDist E := IsUltrametricDist.of_normedAlgebra ℚ_[p]
    Towers.CField.LFTheory.localResidueCardinality
      E = p := by
  let D := lubinTateDatum p u
  let E := D.RootField ℚ_[p] n
  letI : Algebra.IsAlgebraic ℚ_[p] E :=
    Algebra.IsAlgebraic.of_finite ℚ_[p] E
  letI : NontriviallyNormedField E :=
    spectralNorm.nontriviallyNormedField ℚ_[p] E
  letI : NormedField E :=
    (spectralNorm.nontriviallyNormedField ℚ_[p] E).toNormedField
  letI : NormedAlgebra ℚ_[p] E := spectralNorm.normedAlgebra ℚ_[p] E
  letI : IsUltrametricDist E := IsUltrametricDist.of_normedAlgebra ℚ_[p]
  letI : ValuativeRel E := FLExt.valuativeRel ℚ_[p] E
  letI : IsNonarchimedeanLocalField E :=
    FLExt.nonarchimedeanLocalField ℚ_[p] E
  letI : Valuation.Compatible (NormedField.valuation (K := E)) :=
    Valuation.Compatible.ofValuation (NormedField.valuation (K := E))
  letI : CompleteSpace E := spectralNorm.completeSpace ℚ_[p] E
  letI : ProperSpace E := FiniteDimensional.proper ℚ_[p] E
  letI : (NormedField.valuation (K := ℚ_[p])).HasExtension
      (NormedField.valuation (K := E)) :=
    spectralValuationExtension ℚ_[p] E
  let A := Valuation.integer (NormedField.valuation (K := ℚ_[p]))
  let B₀ := Valuation.integer (NormedField.valuation (K := E))
  letI : IsDiscreteValuationRing
      (Valuation.integer (ValuativeRel.valuation E)) :=
    discrete_valuation_ring E
  letI : IsDiscreteValuationRing B₀ :=
    IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing
      (valuativeIntegerNorm E)
  letI : Algebra B₀ E := B₀.subtype.toAlgebra
  letI : IsFractionRing A ℚ_[p] :=
    (Valuation.integer.integers
      (NormedField.valuation (K := ℚ_[p]))).isFractionRing
  letI : IsFractionRing B₀ E :=
    (Valuation.integer.integers
      (NormedField.valuation (K := E))).isFractionRing
  letI : IsScalarTower A B₀ E := IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower A ℚ_[p] E := IsScalarTower.of_algebraMap_eq' rfl
  letI : IsIntegralClosure B₀ A E :=
    FLExt.spectral_integer_closure ℚ_[p] E
  letI : Module.Finite A B₀ := IsIntegralClosure.finite A ℚ_[p] E B₀
  have htotal : TotallyRamified A B₀
      (IsLocalRing.maximalIdeal A) :=
    D.root_totally_ramified ℚ_[p]
      (padic_integer_field p u) n
  let q := IsLocalRing.maximalIdeal A
  obtain ⟨P, hPprime, hPover, _hmap, hram, hunique⟩ := htotal
  have hq0 : q ≠ ⊥ := IsDiscreteValuationRing.not_a_field A
  have hP0 : P ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot hq0 P
  have hPmax : P = IsLocalRing.maximalIdeal B₀ :=
    IsLocalRing.eq_maximalIdeal (hPprime.isMaximal hP0)
  letI : P.IsPrime := hPprime
  letI : P.IsMaximal := hPprime.isMaximal hP0
  letI : P.LiesOver q := hPover
  have hprimes : IsDedekindDomain.primesOverFinset q B₀ = {P} := by
    ext Q
    rw [Finset.mem_singleton, IsDedekindDomain.mem_primesOverFinset_iff hq0 B₀]
    constructor
    · rintro ⟨hQprime, hQover⟩
      exact hunique Q hQprime hQover
    · rintro rfl
      exact ⟨hPprime, hPover⟩
  have hbij : Function.Bijective (algebraMap (A ⧸ q) (B₀ ⧸ P)) :=
    bijective_full_idx
      A B₀ ℚ_[p] E hq0 hprimes hram
  let e : (A ⧸ q) ≃+* (B₀ ⧸ P) :=
    RingEquiv.ofBijective (algebraMap (A ⧸ q) (B₀ ⧸ P)) hbij
  have hcard : Nat.card (B₀ ⧸ P) = Nat.card (A ⧸ q) :=
    (Nat.card_congr e.toEquiv).symm
  change Nat.card (B₀ ⧸ IsLocalRing.maximalIdeal B₀) = p
  rw [← hPmax]
  calc
    Nat.card (B₀ ⧸ P) = Nat.card (A ⧸ q) := hcard
    _ = Towers.CField.LFTheory.localResidueCardinality ℚ_[p] := rfl
    _ = p := padic_local_card p

set_option maxHeartbeats 3000000 in
-- Both equivalent root-field presentations carry dependent spectral norms.
set_option synthInstance.maxHeartbeats 500000 in
/-- The standard basic `p * u` root-field presentation has residue
cardinality `p`. -/
theorem padic_residue_card
    (n : ℕ) (u : ℤ_[p]ˣ) :
    let E := (padicTateDatum p u).RootField ℚ_[p] n
    letI : Algebra.IsAlgebraic ℚ_[p] E :=
      Algebra.IsAlgebraic.of_finite ℚ_[p] E
    letI : NontriviallyNormedField E :=
      spectralNorm.nontriviallyNormedField ℚ_[p] E
    letI : NormedAlgebra ℚ_[p] E := spectralNorm.normedAlgebra ℚ_[p] E
    letI : IsUltrametricDist E := IsUltrametricDist.of_normedAlgebra ℚ_[p]
    Towers.CField.LFTheory.localResidueCardinality E = p := by
  let E₀ := (lubinTateDatum p u).RootField ℚ_[p] n
  let E := (padicTateDatum p u).RootField ℚ_[p] n
  let e : E₀ ≃ₐ[ℚ_[p]] E :=
    padicIntegerBasic p u n
  letI : Algebra.IsAlgebraic ℚ_[p] E₀ :=
    Algebra.IsAlgebraic.of_finite ℚ_[p] E₀
  letI : NontriviallyNormedField E₀ :=
    spectralNorm.nontriviallyNormedField ℚ_[p] E₀
  letI : NormedField E₀ :=
    (spectralNorm.nontriviallyNormedField ℚ_[p] E₀).toNormedField
  letI : NormedAlgebra ℚ_[p] E₀ := spectralNorm.normedAlgebra ℚ_[p] E₀
  letI : IsUltrametricDist E₀ := IsUltrametricDist.of_normedAlgebra ℚ_[p]
  letI : Algebra.IsAlgebraic ℚ_[p] E :=
    Algebra.IsAlgebraic.of_finite ℚ_[p] E
  letI : NontriviallyNormedField E :=
    spectralNorm.nontriviallyNormedField ℚ_[p] E
  letI : NormedField E :=
    (spectralNorm.nontriviallyNormedField ℚ_[p] E).toNormedField
  letI : NormedAlgebra ℚ_[p] E := spectralNorm.normedAlgebra ℚ_[p] E
  letI : IsUltrametricDist E := IsUltrametricDist.of_normedAlgebra ℚ_[p]
  let O₀ := Valuation.integer (NormedField.valuation (K := E₀))
  let O := Valuation.integer (NormedField.valuation (K := E))
  let eO : O₀ ≃+* O := e.toRingEquiv.restrict O₀ O (by
    intro x
    change spectralNorm ℚ_[p] E₀ x ≤ 1 ↔
      spectralNorm ℚ_[p] E (e x) ≤ 1
    rw [spectral_alg_equiv ℚ_[p] E₀ E e x])
  have hcard : Nat.card (IsLocalRing.ResidueField O₀) =
      Nat.card (IsLocalRing.ResidueField O) :=
    Nat.card_congr (IsLocalRing.ResidueField.mapEquiv eO).toEquiv
  change Nat.card (IsLocalRing.ResidueField O) = p
  calc
    Nat.card (IsLocalRing.ResidueField O) =
        Nat.card (IsLocalRing.ResidueField O₀) := hcard.symm
    _ = p := padic_integer_card p n u

set_option maxHeartbeats 4000000 in
-- The target is an intermediate-field copy whose inherited topology must
-- be replaced by its canonical spectral norm during the comparison.
set_option synthInstance.maxHeartbeats 500000 in
/-- The embedded basic field inside the Witt comparison compositum has
residue cardinality `p`. -/
theorem padic_comparison_card
    (n : ℕ) (u : ℤ_[p]ˣ) :
    let E := F p k n u
    letI : Algebra.IsAlgebraic ℚ_[p] E :=
      Algebra.IsAlgebraic.of_finite ℚ_[p] E
    letI : NontriviallyNormedField E :=
      spectralNorm.nontriviallyNormedField ℚ_[p] E
    letI : NormedAlgebra ℚ_[p] E := spectralNorm.normedAlgebra ℚ_[p] E
    letI : IsUltrametricDist E := IsUltrametricDist.of_normedAlgebra ℚ_[p]
    Towers.CField.LFTheory.localResidueCardinality E = p := by
  let E₀ := (padicTateDatum p u).RootField ℚ_[p] n
  let E := F p k n u
  let e : E₀ ≃ₐ[ℚ_[p]] E :=
    (padicWittBasic p k n u).trans
      (padicCyclotomicWitt p k n u)
  letI : Algebra.IsAlgebraic ℚ_[p] E₀ :=
    Algebra.IsAlgebraic.of_finite ℚ_[p] E₀
  letI : NontriviallyNormedField E₀ :=
    spectralNorm.nontriviallyNormedField ℚ_[p] E₀
  letI : NormedField E₀ :=
    (spectralNorm.nontriviallyNormedField ℚ_[p] E₀).toNormedField
  letI : NormedAlgebra ℚ_[p] E₀ := spectralNorm.normedAlgebra ℚ_[p] E₀
  letI : IsUltrametricDist E₀ := IsUltrametricDist.of_normedAlgebra ℚ_[p]
  letI : Algebra.IsAlgebraic ℚ_[p] E :=
    Algebra.IsAlgebraic.of_finite ℚ_[p] E
  letI : NontriviallyNormedField E :=
    spectralNorm.nontriviallyNormedField ℚ_[p] E
  letI : NormedField E :=
    (spectralNorm.nontriviallyNormedField ℚ_[p] E).toNormedField
  letI : NormedAlgebra ℚ_[p] E := spectralNorm.normedAlgebra ℚ_[p] E
  letI : IsUltrametricDist E := IsUltrametricDist.of_normedAlgebra ℚ_[p]
  let O₀ := Valuation.integer (NormedField.valuation (K := E₀))
  let O := Valuation.integer (NormedField.valuation (K := E))
  let eO : O₀ ≃+* O := e.toRingEquiv.restrict O₀ O (by
    intro x
    change spectralNorm ℚ_[p] E₀ x ≤ 1 ↔
      spectralNorm ℚ_[p] E (e x) ≤ 1
    rw [spectral_alg_equiv ℚ_[p] E₀ E e x])
  have hcard : Nat.card (IsLocalRing.ResidueField O₀) =
      Nat.card (IsLocalRing.ResidueField O) :=
    Nat.card_congr (IsLocalRing.ResidueField.mapEquiv eO).toEquiv
  change Nat.card (IsLocalRing.ResidueField O) = p
  calc
    Nat.card (IsLocalRing.ResidueField O) =
        Nat.card (IsLocalRing.ResidueField O₀) := hcard.symm
    _ = p := padic_residue_card p n u

set_option maxHeartbeats 3000000 in
-- The proof passes through the two equivalent presentations of `ℤ_p`.
set_option synthInstance.maxHeartbeats 500000 in
theorem padic_spectral_integral
    (n : ℕ)
    (z :
      letI : Algebra.IsAlgebraic ℚ_[p] (L p n) :=
        Algebra.IsAlgebraic.of_finite ℚ_[p] (L p n)
      letI : NontriviallyNormedField (L p n) :=
        spectralNorm.nontriviallyNormedField ℚ_[p] (L p n)
      letI : NormedAlgebra ℚ_[p] (L p n) :=
        spectralNorm.normedAlgebra ℚ_[p] (L p n)
      letI : IsUltrametricDist (L p n) :=
        IsUltrametricDist.of_normedAlgebra ℚ_[p]
      Valuation.integer (NormedField.valuation (K := L p n))) :
    IsIntegral (B p k n)
      (padicWittFraction p k n z) := by
  let E := L p n
  letI : Algebra.IsAlgebraic ℚ_[p] E :=
    Algebra.IsAlgebraic.of_finite ℚ_[p] E
  letI : NontriviallyNormedField E :=
    spectralNorm.nontriviallyNormedField ℚ_[p] E
  letI : NormedAlgebra ℚ_[p] E := spectralNorm.normedAlgebra ℚ_[p] E
  letI : IsUltrametricDist E := IsUltrametricDist.of_normedAlgebra ℚ_[p]
  let O := Valuation.integer (NormedField.valuation (K := E))
  let A := Valuation.integer (NormedField.valuation (K := ℚ_[p]))
  let e : A ≃+* ℤ_[p] := padicNormInt p
  let f := padicWittFraction p k n
  let rhoB := padicWittRing p k n
  letI : Algebra ℤ_[p] (B p k n) := rhoB.toAlgebra
  letI : Algebra ℤ_[p] (C p k n) :=
    ((algebraMap (B p k n) (C p k n)).comp rhoB).toAlgebra
  letI : Algebra ℤ_[p] E :=
    ((algebraMap ℚ_[p] E).comp (algebraMap ℤ_[p] ℚ_[p])).toAlgebra
  letI : IsIntegralClosure O A E :=
    FLExt.spectral_integer_closure ℚ_[p] E
  have hzA : IsIntegral A (z : E) :=
    (IsIntegralClosure.isIntegral_iff (R := A) (A := O) (B := E)).2
      ⟨z, rfl⟩
  have he : (algebraMap ℤ_[p] E).comp e.toRingHom = algebraMap A E := by
    ext a
    rfl
  have hzZ : IsIntegral ℤ_[p] (z : E) :=
    (e.isIntegral_iff he (z : E)).mp hzA
  have hcomp :
      (algebraMap (B p k n) (C p k n)).comp rhoB =
        f.toRingHom.comp (algebraMap ℤ_[p] E) := by
    ext a
    change algebraMap (B p k n) (C p k n) (rhoB a) =
      f (algebraMap ℚ_[p] E (algebraMap ℤ_[p] ℚ_[p] a))
    rw [f.commutes]
    exact (root_fraction_algebra p k n a).symm
  exact IsIntegral.map_of_comp_eq rhoB f.toRingHom hcomp hzZ

set_option maxHeartbeats 3000000 in
-- Several compatible integer-ring algebra structures occur simultaneously.
set_option synthInstance.maxHeartbeats 500000 in
/-- A spectral integer in the cyclotomic root field has integral image in
the common Witt-root DVR, hence admits a unique lift to that DVR. -/
noncomputable def padicSpectralRing (n : ℕ) :
    letI : Algebra.IsAlgebraic ℚ_[p] (L p n) :=
      Algebra.IsAlgebraic.of_finite ℚ_[p] (L p n)
    letI : NontriviallyNormedField (L p n) :=
      spectralNorm.nontriviallyNormedField ℚ_[p] (L p n)
    letI : NormedAlgebra ℚ_[p] (L p n) :=
      spectralNorm.normedAlgebra ℚ_[p] (L p n)
    letI : IsUltrametricDist (L p n) :=
      IsUltrametricDist.of_normedAlgebra ℚ_[p]
    Valuation.integer (NormedField.valuation (K := L p n)) →+* B p k n := by
  let E := L p n
  letI : Algebra.IsAlgebraic ℚ_[p] E :=
    Algebra.IsAlgebraic.of_finite ℚ_[p] E
  letI : NontriviallyNormedField E :=
    spectralNorm.nontriviallyNormedField ℚ_[p] E
  letI : NormedAlgebra ℚ_[p] E := spectralNorm.normedAlgebra ℚ_[p] E
  letI : IsUltrametricDist E := IsUltrametricDist.of_normedAlgebra ℚ_[p]
  let O := Valuation.integer (NormedField.valuation (K := E))
  let f := padicWittFraction p k n
  have integralImage (z : O) : IsIntegral (B p k n) (f (z : E)) :=
    padic_spectral_integral p k n z
  exact
    { toFun := fun z ↦
        IsIntegralClosure.mk' (B p k n) (f (z : E)) (integralImage z)
      map_one' := by
        apply IsFractionRing.injective (B p k n) (C p k n)
        simp
      map_zero' := by
        apply IsFractionRing.injective (B p k n) (C p k n)
        simp
      map_add' := fun x y ↦ by
        apply IsFractionRing.injective (B p k n) (C p k n)
        simp
      map_mul' := fun x y ↦ by
        apply IsFractionRing.injective (B p k n) (C p k n)
        simp }

set_option maxHeartbeats 2000000 in
-- Unfolding the spectral norm instances and the integral lift is expensive.
set_option synthInstance.maxHeartbeats 500000 in
@[simp]
theorem padic_spectral_algebra
    (n : ℕ)
    (z :
      letI : Algebra.IsAlgebraic ℚ_[p] (L p n) :=
        Algebra.IsAlgebraic.of_finite ℚ_[p] (L p n)
      letI : NontriviallyNormedField (L p n) :=
        spectralNorm.nontriviallyNormedField ℚ_[p] (L p n)
      letI : NormedAlgebra ℚ_[p] (L p n) :=
        spectralNorm.normedAlgebra ℚ_[p] (L p n)
      letI : IsUltrametricDist (L p n) :=
        IsUltrametricDist.of_normedAlgebra ℚ_[p]
      Valuation.integer (NormedField.valuation (K := L p n))) :
    algebraMap (B p k n) (C p k n)
        (padicSpectralRing p k n z) =
      padicWittFraction p k n z := by
  have hz := padic_spectral_integral p k n z
  unfold padicSpectralRing
  change algebraMap (B p k n) (C p k n)
      (IsIntegralClosure.mk' (B p k n)
        (padicWittFraction p k n z) hz) = _
  exact IsIntegralClosure.algebraMap_mk' _ _ _

/-- The distinguished Witt root is nonzero; it generates the nonzero
maximal ideal of the common root DVR. -/
theorem padic_witt_ne (n : ℕ) :
    cyclotomicWittRoot p k n ≠ 0 := by
  intro hroot
  apply IsDiscreteValuationRing.not_a_field (B p k n)
  rw [padic_witt_maximal p k n, hroot]
  exact Ideal.span_singleton_eq_bot.mpr rfl

/-- The normalized discrete valuation on the fraction field of the common
Witt-root DVR. -/
noncomputable def wittFractionValuation (n : ℕ) :
    Valuation (C p k n) (WithZero (Multiplicative ℤ)) :=
  (IsDiscreteValuationRing.maximalIdeal (B p k n)).valuation (C p k n)

/-- In multiplicative convention the distinguished Witt root has value
`exp (-1)`, i.e. additive order one. -/
theorem witt_fraction_valuation (n : ℕ) :
    wittFractionValuation p k n
        (algebraMap (B p k n) (C p k n)
          (cyclotomicWittRoot p k n)) =
      WithZero.exp (-1 : ℤ) := by
  let P := IsDiscreteValuationRing.maximalIdeal (B p k n)
  change P.valuation (C p k n)
      (algebraMap (B p k n) (C p k n)
        (cyclotomicWittRoot p k n)) = _
  rw [P.valuation_of_algebraMap]
  apply P.intValuation_singleton
  · exact padic_witt_ne p k n
  · exact padic_witt_maximal p k n

set_option maxHeartbeats 4000000 in
-- Both spectral presentations of the root field are present at once.
set_option synthInstance.maxHeartbeats 500000 in
/-- The explicit cyclotomic root is a uniformizer of the spectral integer
ring of the explicit root-field presentation. -/
theorem padic_cyclotomic_uniformizer (n : ℕ) :
    let E := L p n
    letI : Algebra.IsAlgebraic ℚ_[p] E :=
      Algebra.IsAlgebraic.of_finite ℚ_[p] E
    letI : NontriviallyNormedField E :=
      spectralNorm.nontriviallyNormedField ℚ_[p] E
    letI : NormedAlgebra ℚ_[p] E := spectralNorm.normedAlgebra ℚ_[p] E
    letI : IsUltrametricDist E := IsUltrametricDist.of_normedAlgebra ℚ_[p]
    let O := Valuation.integer (NormedField.valuation (K := E))
    ∃ alpha : O,
      O.subtype alpha = (cyclotomicLubinDatum p).root ℚ_[p] n ∧
        IsLocalRing.maximalIdeal O = Ideal.span {alpha} := by
  let E₀ :=
    (padicLubinDatum p).RootField ℚ_[p] n
  let E := L p n
  let e : E₀ ≃ₐ[ℚ_[p]] E :=
    padicIntegerAlg p n
  letI : Algebra.IsAlgebraic ℚ_[p] E₀ :=
    Algebra.IsAlgebraic.of_finite ℚ_[p] E₀
  letI : NontriviallyNormedField E₀ :=
    spectralNorm.nontriviallyNormedField ℚ_[p] E₀
  letI : NormedAlgebra ℚ_[p] E₀ := spectralNorm.normedAlgebra ℚ_[p] E₀
  letI : IsUltrametricDist E₀ := IsUltrametricDist.of_normedAlgebra ℚ_[p]
  letI : Algebra.IsAlgebraic ℚ_[p] E :=
    Algebra.IsAlgebraic.of_finite ℚ_[p] E
  letI : NontriviallyNormedField E :=
    spectralNorm.nontriviallyNormedField ℚ_[p] E
  letI : NormedAlgebra ℚ_[p] E := spectralNorm.normedAlgebra ℚ_[p] E
  letI : IsUltrametricDist E := IsUltrametricDist.of_normedAlgebra ℚ_[p]
  let O₀ := Valuation.integer (NormedField.valuation (K := E₀))
  let O := Valuation.integer (NormedField.valuation (K := E))
  obtain ⟨alpha₀, halpha₀, hmax₀⟩ :=
    (padicLubinDatum p).root_field_uniformizer
      ℚ_[p] (padic_integer_residue p) n
  let eInt : O₀ ≃+* O := e.toRingEquiv.restrict O₀ O (by
    intro x
    change spectralNorm ℚ_[p] E₀ x ≤ 1 ↔
      spectralNorm ℚ_[p] E (e x) ≤ 1
    rw [spectral_alg_equiv ℚ_[p] E₀ E e x])
  have hmax : (IsLocalRing.maximalIdeal O₀).map eInt.toRingHom =
      IsLocalRing.maximalIdeal O :=
    IsLocalRing.eq_maximalIdeal
      ((inferInstance : (IsLocalRing.maximalIdeal O₀).IsMaximal).map_bijective
        eInt.toRingHom eInt.bijective)
  refine ⟨eInt alpha₀, ?_, ?_⟩
  · calc
      e (alpha₀ : E₀) =
          e ((padicLubinDatum p).root ℚ_[p] n) :=
        congrArg e halpha₀
      _ = (cyclotomicLubinDatum p).root ℚ_[p] n :=
        padic_integer_alg p n
  · rw [← hmax, hmax₀, Ideal.map_span, Set.image_singleton]
    rfl

set_option maxHeartbeats 4000000 in
-- The basic root field has the same pair of integer-ring presentations.
set_option synthInstance.maxHeartbeats 500000 in
/-- The explicit basic `p * u` Lubin--Tate root is a uniformizer of its
spectral integer ring. -/
theorem padic_basic_uniformizer (n : ℕ) (u : ℤ_[p]ˣ) :
    let E := (padicTateDatum p u).RootField ℚ_[p] n
    letI : Algebra.IsAlgebraic ℚ_[p] E :=
      Algebra.IsAlgebraic.of_finite ℚ_[p] E
    letI : NontriviallyNormedField E :=
      spectralNorm.nontriviallyNormedField ℚ_[p] E
    letI : NormedAlgebra ℚ_[p] E := spectralNorm.normedAlgebra ℚ_[p] E
    letI : IsUltrametricDist E := IsUltrametricDist.of_normedAlgebra ℚ_[p]
    let O := Valuation.integer (NormedField.valuation (K := E))
    ∃ alpha : O,
      O.subtype alpha = (padicTateDatum p u).root ℚ_[p] n ∧
        IsLocalRing.maximalIdeal O = Ideal.span {alpha} := by
  let E₀ := (lubinTateDatum p u).RootField ℚ_[p] n
  let E := (padicTateDatum p u).RootField ℚ_[p] n
  let e : E₀ ≃ₐ[ℚ_[p]] E :=
    padicIntegerBasic p u n
  letI : Algebra.IsAlgebraic ℚ_[p] E₀ :=
    Algebra.IsAlgebraic.of_finite ℚ_[p] E₀
  letI : NontriviallyNormedField E₀ :=
    spectralNorm.nontriviallyNormedField ℚ_[p] E₀
  letI : NormedAlgebra ℚ_[p] E₀ := spectralNorm.normedAlgebra ℚ_[p] E₀
  letI : IsUltrametricDist E₀ := IsUltrametricDist.of_normedAlgebra ℚ_[p]
  letI : Algebra.IsAlgebraic ℚ_[p] E :=
    Algebra.IsAlgebraic.of_finite ℚ_[p] E
  letI : NontriviallyNormedField E :=
    spectralNorm.nontriviallyNormedField ℚ_[p] E
  letI : NormedAlgebra ℚ_[p] E := spectralNorm.normedAlgebra ℚ_[p] E
  letI : IsUltrametricDist E := IsUltrametricDist.of_normedAlgebra ℚ_[p]
  let O₀ := Valuation.integer (NormedField.valuation (K := E₀))
  let O := Valuation.integer (NormedField.valuation (K := E))
  obtain ⟨alpha₀, halpha₀, hmax₀⟩ :=
    (lubinTateDatum p u).root_field_uniformizer
      ℚ_[p] (padic_integer_field p u) n
  let eInt : O₀ ≃+* O := e.toRingEquiv.restrict O₀ O (by
    intro x
    change spectralNorm ℚ_[p] E₀ x ≤ 1 ↔
      spectralNorm ℚ_[p] E (e x) ≤ 1
    rw [spectral_alg_equiv ℚ_[p] E₀ E e x])
  have hmax : (IsLocalRing.maximalIdeal O₀).map eInt.toRingHom =
      IsLocalRing.maximalIdeal O :=
    IsLocalRing.eq_maximalIdeal
      ((inferInstance : (IsLocalRing.maximalIdeal O₀).IsMaximal).map_bijective
        eInt.toRingHom eInt.bijective)
  refine ⟨eInt alpha₀, ?_, ?_⟩
  · calc
      e (alpha₀ : E₀) =
          e ((lubinTateDatum p u).root ℚ_[p] n) :=
        congrArg e halpha₀
      _ = (padicTateDatum p u).root ℚ_[p] n :=
        padic_integer_basic p u n
  · rw [← hmax, hmax₀, Ideal.map_span, Set.image_singleton]
    rfl

set_option maxHeartbeats 4000000 in
-- Transporting the basic spectral order through the two embedded-field equivalences.
set_option synthInstance.maxHeartbeats 500000 in
/-- The basic root remains a spectral uniformizer in the copy of the basic
field sitting inside the comparison compositum. -/
theorem padic_witt_uniformizer
    (n : ℕ) (u : ℤ_[p]ˣ) :
    let E := F p k n u
    letI : Algebra.IsAlgebraic ℚ_[p] E :=
      Algebra.IsAlgebraic.of_finite ℚ_[p] E
    letI : NontriviallyNormedField E :=
      spectralNorm.nontriviallyNormedField ℚ_[p] E
    letI : NormedAlgebra ℚ_[p] E := spectralNorm.normedAlgebra ℚ_[p] E
    letI : IsUltrametricDist E := IsUltrametricDist.of_normedAlgebra ℚ_[p]
    let O := Valuation.integer (NormedField.valuation (K := E))
    let e := (padicWittBasic p k n u).trans
      (padicCyclotomicWitt p k n u)
    ∃ alpha : O,
      O.subtype alpha =
          e ((padicTateDatum p u).root ℚ_[p] n) ∧
        IsLocalRing.maximalIdeal O = Ideal.span {alpha} := by
  let E₀ := (padicTateDatum p u).RootField ℚ_[p] n
  let E := F p k n u
  let e : E₀ ≃ₐ[ℚ_[p]] E :=
    (padicWittBasic p k n u).trans
      (padicCyclotomicWitt p k n u)
  letI : Algebra.IsAlgebraic ℚ_[p] E₀ :=
    Algebra.IsAlgebraic.of_finite ℚ_[p] E₀
  letI : NontriviallyNormedField E₀ :=
    spectralNorm.nontriviallyNormedField ℚ_[p] E₀
  letI : NormedAlgebra ℚ_[p] E₀ := spectralNorm.normedAlgebra ℚ_[p] E₀
  letI : IsUltrametricDist E₀ := IsUltrametricDist.of_normedAlgebra ℚ_[p]
  letI : Algebra.IsAlgebraic ℚ_[p] E :=
    Algebra.IsAlgebraic.of_finite ℚ_[p] E
  letI : NontriviallyNormedField E :=
    spectralNorm.nontriviallyNormedField ℚ_[p] E
  letI : NormedAlgebra ℚ_[p] E := spectralNorm.normedAlgebra ℚ_[p] E
  letI : IsUltrametricDist E := IsUltrametricDist.of_normedAlgebra ℚ_[p]
  let O₀ := Valuation.integer (NormedField.valuation (K := E₀))
  let O := Valuation.integer (NormedField.valuation (K := E))
  obtain ⟨alpha₀, halpha₀, hmax₀⟩ :=
    padic_basic_uniformizer p n u
  let eInt : O₀ ≃+* O := e.toRingEquiv.restrict O₀ O (by
    intro x
    change spectralNorm ℚ_[p] E₀ x ≤ 1 ↔
      spectralNorm ℚ_[p] E (e x) ≤ 1
    rw [spectral_alg_equiv ℚ_[p] E₀ E e x])
  have hmax : (IsLocalRing.maximalIdeal O₀).map eInt.toRingHom =
      IsLocalRing.maximalIdeal O :=
    IsLocalRing.eq_maximalIdeal
      ((inferInstance : (IsLocalRing.maximalIdeal O₀).IsMaximal).map_bijective
        eInt.toRingHom eInt.bijective)
  refine ⟨eInt alpha₀, ?_, ?_⟩
  · exact congrArg e halpha₀
  · rw [← hmax, hmax₀, Ideal.map_span, Set.image_singleton]
    rfl

set_option maxHeartbeats 2000000 in
-- Unfolding both integral lifts under the fraction-field embedding is costly.
set_option synthInstance.maxHeartbeats 500000 in
/-- The integral lift of the cyclotomic spectral uniformizer is literally
the distinguished uniformizer of the Witt-root DVR. -/
theorem spectralUniformizerWitt
    (n : ℕ)
    (alpha :
      let E := L p n
      letI : Algebra.IsAlgebraic ℚ_[p] E :=
        Algebra.IsAlgebraic.of_finite ℚ_[p] E
      letI : NontriviallyNormedField E :=
        spectralNorm.nontriviallyNormedField ℚ_[p] E
      letI : NormedAlgebra ℚ_[p] E := spectralNorm.normedAlgebra ℚ_[p] E
      letI : IsUltrametricDist E := IsUltrametricDist.of_normedAlgebra ℚ_[p]
      Valuation.integer (NormedField.valuation (K := E)))
    (halpha : (alpha : L p n) =
      (cyclotomicLubinDatum p).root ℚ_[p] n) :
    padicSpectralRing p k n alpha =
      cyclotomicWittRoot p k n := by
  apply IsFractionRing.injective (B p k n) (C p k n)
  rw [padic_spectral_algebra, halpha]
  exact padic_witt_fraction p k n

set_option maxHeartbeats 3000000 in
-- The maximal-ideal criterion is applied in the spectral norm structure.
set_option synthInstance.maxHeartbeats 500000 in
/-- The spectral norm of the cyclotomic Lubin--Tate root is strictly less
than one. -/
theorem padic_cyclotomic_spectral (n : ℕ) :
    spectralNorm ℚ_[p] (L p n)
        ((cyclotomicLubinDatum p).root ℚ_[p] n) < 1 := by
  let E := L p n
  letI : Algebra.IsAlgebraic ℚ_[p] E :=
    Algebra.IsAlgebraic.of_finite ℚ_[p] E
  letI : NontriviallyNormedField E :=
    spectralNorm.nontriviallyNormedField ℚ_[p] E
  letI : NormedAlgebra ℚ_[p] E := spectralNorm.normedAlgebra ℚ_[p] E
  letI : IsUltrametricDist E := IsUltrametricDist.of_normedAlgebra ℚ_[p]
  let O := Valuation.integer (NormedField.valuation (K := E))
  obtain ⟨alpha, halpha, hmax⟩ :=
    padic_cyclotomic_uniformizer p n
  have halpha_mem : alpha ∈ IsLocalRing.maximalIdeal O := by
    rw [hmax]
    exact Ideal.mem_span_singleton_self alpha
  have hval :=
    (NormedField.valuation (K := E)).mem_maximalIdeal_iff.mp halpha_mem
  change ‖(alpha : E)‖₊ < 1 at hval
  change ‖((cyclotomicLubinDatum p).root ℚ_[p] n : E)‖ < 1
  rw [← halpha]
  exact_mod_cast hval

/-- The exponential base which makes the Witt DVR absolute value agree
with the spectral norm on the cyclotomic root field. -/
noncomputable def wittAbsoluteBase (n : ℕ) : ℝ≥0 :=
  (⟨spectralNorm ℚ_[p] (L p n)
      ((cyclotomicLubinDatum p).root ℚ_[p] n),
    spectralNorm_nonneg
      ((cyclotomicLubinDatum p).root ℚ_[p] n)⟩ : ℝ≥0)⁻¹

theorem witt_absolute_base (n : ℕ) :
    1 < wittAbsoluteBase p n := by
  rw [wittAbsoluteBase, one_lt_inv_iff₀]
  constructor
  · exact_mod_cast spectralNorm_zero_lt
      ((cyclotomicLubinDatum p).root_ne_zero ℚ_[p] n)
      (Algebra.IsAlgebraic.isAlgebraic
        ((cyclotomicLubinDatum p).root ℚ_[p] n))
  · exact_mod_cast padic_cyclotomic_spectral p n

/-- The normalized absolute value on the ambient Witt fraction field. -/
noncomputable def wittAbsoluteValue (n : ℕ) :
    AbsoluteValue (C p k n) ℝ :=
  discreteValuationAbsolute
    (wittFractionValuation p k n)
    (wittAbsoluteBase p n)
    (witt_absolute_base p n)

/-- The ambient absolute value has the prescribed spectral value on the
cyclotomic uniformizer. -/
theorem witt_absolute_root (n : ℕ) :
    wittAbsoluteValue p k n
        (padicWittFraction p k n
          ((cyclotomicLubinDatum p).root ℚ_[p] n)) =
      spectralNorm ℚ_[p] (L p n)
        ((cyclotomicLubinDatum p).root ℚ_[p] n) := by
  rw [padic_witt_fraction]
  rw [wittAbsoluteValue,
    discrete_valuation_exp
      (wittFractionValuation p k n)
      (wittAbsoluteBase p n)
      (witt_absolute_base p n)
      (witt_fraction_valuation p k n)]
  simp only [zpow_neg, zpow_one, wittAbsoluteBase,
    NNReal.coe_inv, inv_inv]
  rfl

set_option maxHeartbeats 2000000 in
-- The spectral integer lift turns valuation units into DVR units.
set_option synthInstance.maxHeartbeats 500000 in
/-- A spectral valuation unit in the cyclotomic root field has ambient
absolute value one. -/
theorem padic_witt_absolute
    (n : ℕ) (x : L p n)
    (hx : spectralNorm ℚ_[p] (L p n) x = 1) :
    wittAbsoluteValue p k n
        (padicWittFraction p k n x) = 1 := by
  let E := L p n
  letI : Algebra.IsAlgebraic ℚ_[p] E :=
    Algebra.IsAlgebraic.of_finite ℚ_[p] E
  letI : NontriviallyNormedField E :=
    spectralNorm.nontriviallyNormedField ℚ_[p] E
  letI : NormedAlgebra ℚ_[p] E := spectralNorm.normedAlgebra ℚ_[p] E
  letI : IsUltrametricDist E := IsUltrametricDist.of_normedAlgebra ℚ_[p]
  have hxval : (NormedField.valuation (K := E)) x = 1 := by
    change ‖x‖₊ = 1
    apply NNReal.eq
    change spectralNorm ℚ_[p] E x = 1
    exact hx
  let O := Valuation.integer (NormedField.valuation (K := E))
  let z : O := ⟨x, hxval.le⟩
  have hzunit : IsUnit z :=
    (Valuation.integer.integers
      (NormedField.valuation (K := E))).isUnit_iff_valuation_eq_one.mpr hxval
  let b : B p k n :=
    padicSpectralRing p k n z
  have hbunit : IsUnit b := hzunit.map
    (padicSpectralRing p k n)
  have hvb : wittFractionValuation p k n
      (algebraMap (B p k n) (C p k n) b) = 1 := by
    let P := IsDiscreteValuationRing.maximalIdeal (B p k n)
    change P.valuation (C p k n)
        (algebraMap (B p k n) (C p k n) b) = 1
    rw [P.valuation_of_algebraMap, P.intValuation_eq_one_iff]
    exact IsLocalRing.notMem_maximalIdeal.mpr hbunit
  rw [← padic_spectral_algebra
    (p := p) (k := k) n z]
  change wittAbsoluteValue p k n
      (algebraMap (B p k n) (C p k n) b) = 1
  rw [wittAbsoluteValue,
    discrete_valuation_absolute, hvb]
  rfl

set_option maxHeartbeats 4000000 in
-- The proof uses the discrete spectral valuation and the integral Witt lift.
set_option synthInstance.maxHeartbeats 500000 in
/-- The ambient Witt absolute value restricts to the spectral norm on the
embedded cyclotomic root field. -/
theorem witt_absolute_restrict
    (n : ℕ) (x : L p n) :
    wittAbsoluteValue p k n
        (padicWittFraction p k n x) =
      spectralNorm ℚ_[p] (L p n) x := by
  let E := L p n
  letI : Algebra.IsAlgebraic ℚ_[p] E :=
    Algebra.IsAlgebraic.of_finite ℚ_[p] E
  letI : NontriviallyNormedField E :=
    spectralNorm.nontriviallyNormedField ℚ_[p] E
  letI : NormedAlgebra ℚ_[p] E := spectralNorm.normedAlgebra ℚ_[p] E
  letI : IsUltrametricDist E := IsUltrametricDist.of_normedAlgebra ℚ_[p]
  letI : ValuativeRel E :=
    FLExt.valuativeRel ℚ_[p] E
  letI : IsNonarchimedeanLocalField E :=
    FLExt.nonarchimedeanLocalField ℚ_[p] E
  letI : Valuation.Compatible (NormedField.valuation (K := E)) :=
    Valuation.Compatible.ofValuation (NormedField.valuation (K := E))
  let v := NormedField.valuation (K := E)
  let O := Valuation.integer v
  letI : IsDiscreteValuationRing O := by
    letI : IsDiscreteValuationRing
        (Valuation.integer (ValuativeRel.valuation E)) :=
      discrete_valuation_ring E
    exact IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing
      (valuativeIntegerNorm E)
  letI : IsFractionRing O E :=
    (Valuation.integer.integers v).isFractionRing
  let w := (IsDiscreteValuationRing.maximalIdeal O).valuation E
  let eO : O ≃+* Valuation.integer w :=
    IsDiscreteValuationRing.equivValuationSubring (A := O) (K := E)
  have heOcoe (a : O) : ((eO a : Valuation.integer w) : E) =
      algebraMap O E a := by
    dsimp only [eO]
    change ((IsDiscreteValuationRing.equivValuationSubring
      (A := O) (K := E) a : Valuation.integer w) : E) = _
    calc
      ↑(IsDiscreteValuationRing.equivValuationSubring
          (A := O) (K := E) a) =
          ↑(((⊤ : Subring O).equivMapOfInjective (algebraMap O E)
            (IsFractionRing.injective O E)) (Subring.topEquiv.symm a)) := rfl
      _ = algebraMap O E (Subring.topEquiv.symm a : O) :=
        Subring.coe_equivMapOfInjective_apply _ _ _ _
      _ = algebraMap O E a := rfl
  obtain ⟨alpha, halpha, hmax⟩ :=
    padic_cyclotomic_uniformizer p n
  have halphaE : (alpha : E) =
      (cyclotomicLubinDatum p).root ℚ_[p] n := halpha
  have hmaxmap : (IsLocalRing.maximalIdeal O).map eO.toRingHom =
      IsLocalRing.maximalIdeal (Valuation.integer w) :=
    IsLocalRing.eq_maximalIdeal
      ((inferInstance : (IsLocalRing.maximalIdeal O).IsMaximal).map_bijective
        eO.toRingHom eO.bijective)
  have hmaxW : IsLocalRing.maximalIdeal (Valuation.integer w) =
      Ideal.span {eO alpha} := by
    rw [← hmaxmap, hmax, Ideal.map_span, Set.image_singleton]
    rfl
  have halpha_uniformizerW :
      w.IsUniformizer ((eO alpha : Valuation.integer w) : E) :=
    Valuation.isUniformizer_of_maximalIdeal_eq_span (v := w) hmaxW
  have halpha_uniformizer : w.IsUniformizer (alpha : E) := by
    rw [heOcoe alpha] at halpha_uniformizerW
    exact halpha_uniformizerW
  by_cases hx0 : x = 0
  · subst x
    simp [spectralNorm_zero]
  let xu : Eˣ := Units.mk0 x hx0
  obtain ⟨u, m, hu, hdecomp⟩ :=
    unit_uniformizer_zpow w (alpha : E)
      halpha_uniformizer xu
  have hxdecomp : x = (u : E) * (alpha : E) ^ m := by
    have h := congrArg ((↑) : Eˣ → E) hdecomp
    simpa [xu, Units.val_mul, Units.val_zpow_eq_zpow_val] using h
  let uW : Valuation.integer w := ⟨(u : E), hu.le⟩
  have huWunit : IsUnit uW :=
    (Valuation.integer.integers w).isUnit_iff_valuation_eq_one.mpr hu
  let uO : O := eO.symm uW
  have huOunit : IsUnit uO := huWunit.map eO.symm.toRingHom
  have huOcoe : algebraMap O E uO = (u : E) := by
    have h := congrArg Subtype.val (eO.apply_symm_apply uW)
    simpa [eO, IsDiscreteValuationRing.equivValuationSubring, uO, uW] using h
  have huval : v (u : E) = 1 := by
    rw [← huOcoe]
    exact (Valuation.integer.integers v).one_of_isUnit huOunit
  have hunorm : spectralNorm ℚ_[p] E (u : E) = 1 := by
    change ‖(u : E)‖ = 1
    change ‖(u : E)‖₊ = 1 at huval
    exact congrArg (fun z : ℝ≥0 ↦ (z : ℝ)) huval
  let f := padicWittFraction p k n
  let av := wittAbsoluteValue p k n
  calc
    av (f x) = av (f (u : E)) * av (f (alpha : E)) ^ m := by
      rw [hxdecomp, map_mul, map_zpow₀, map_mul, map_zpow₀]
    _ = 1 * av (f (alpha : E)) ^ m := by
      rw [padic_witt_absolute p k n (u : E) hunorm]
    _ = 1 * (spectralNorm ℚ_[p] E
        ((cyclotomicLubinDatum p).root ℚ_[p] n)) ^ m := by
      rw [halphaE, witt_absolute_root]
    _ = spectralNorm ℚ_[p] E x := by
      rw [hxdecomp]
      rw [← halphaE]
      change 1 * ‖(alpha : E)‖ ^ m = ‖(u : E) * (alpha : E) ^ m‖
      rw [norm_mul, norm_zpow, show ‖(u : E)‖ = 1 by exact hunorm]

/-- The ambient absolute value restricted to the finite comparison
compositum. -/
noncomputable def comparisonAbsoluteValue
    (n : ℕ) (u : ℤ_[p]ˣ) : AbsoluteValue (M p k n u) ℝ :=
  (wittAbsoluteValue p k n).comp
    (f := (M p k n u).val.toRingHom) Subtype.val_injective

set_option maxHeartbeats 3000000 in
-- The uniqueness theorem unfolds the two embedded root-field presentations.
set_option synthInstance.maxHeartbeats 500000 in
/-- By uniqueness over the complete base, the restricted ambient absolute
value is the spectral norm of the comparison compositum. -/
theorem comparison_absolute_spectral
    (n : ℕ) (u : ℤ_[p]ˣ) (x : M p k n u) :
    comparisonAbsoluteValue p k n u x =
      spectralNorm ℚ_[p] (M p k n u) x := by
  apply spectralNorm_unique_field_norm_ext
  intro a
  change wittAbsoluteValue p k n
      (algebraMap ℚ_[p] (C p k n) a) = ‖a‖
  rw [← (padicWittFraction p k n).commutes a]
  exact (witt_absolute_restrict p k n
    (algebraMap ℚ_[p] (L p n) a)).trans (spectralNorm_extends a)

/-- The comparison absolute value restricted further to its fixed basic
subfield. -/
noncomputable def padicAbsoluteValue
    (n : ℕ) (u : ℤ_[p]ˣ) : AbsoluteValue (F p k n u) ℝ :=
  (comparisonAbsoluteValue p k n u).comp
    (f := algebraMap (F p k n u) (M p k n u))
    (algebraMap (F p k n u) (M p k n u)).injective

set_option maxHeartbeats 3000000 in
-- The restricted absolute value and its ambient embedding elaborate together.
set_option synthInstance.maxHeartbeats 500000 in
/-- The restricted absolute value on the basic subfield is its spectral
norm over `Q_p`. -/
theorem padic_absolute_spectral
    (n : ℕ) (u : ℤ_[p]ˣ) (x : F p k n u) :
    padicAbsoluteValue p k n u x =
      spectralNorm ℚ_[p] (F p k n u) x := by
  apply spectralNorm_unique_field_norm_ext
  intro a
  change comparisonAbsoluteValue p k n u
      (algebraMap ℚ_[p] (M p k n u) a) = ‖a‖
  exact (comparison_absolute_spectral
    p k n u (algebraMap ℚ_[p] (M p k n u) a)).trans
      (spectralNorm_extends a)

set_option maxHeartbeats 3000000 in
-- The two intermediate-field algebra structures elaborate together.
set_option synthInstance.maxHeartbeats 500000 in
/-- The inclusion of the basic subfield into the comparison compositum is
isometric for their canonical spectral norms. -/
theorem padic_comparison_spectral
    (n : ℕ) (u : ℤ_[p]ˣ) (x : F p k n u) :
    spectralNorm ℚ_[p] (M p k n u)
        (algebraMap (F p k n u) (M p k n u) x) =
      spectralNorm ℚ_[p] (F p k n u) x := by
  rw [← comparison_absolute_spectral,
    ← padic_absolute_spectral]
  rfl

set_option maxHeartbeats 3000000 in
-- Restricting the intermediate-field inclusion to both dependent spectral
-- integer subrings requires a larger elaboration budget.
set_option synthInstance.maxHeartbeats 500000 in
/-- The inclusion of the basic field restricts to an algebra structure on
the two spectral integer rings. -/
@[implicit_reducible]
noncomputable def comparisonSpectralAlgebra
    (n : ℕ) (u : ℤ_[p]ˣ) :
    Algebra (Valuation.integer (qpadicSpectralValuation p (F p k n u)))
      (Valuation.integer (qpadicSpectralValuation p (M p k n u))) := by
  let F₀ := F p k n u
  let E := M p k n u
  letI : Algebra.IsAlgebraic ℚ_[p] F₀ :=
    Algebra.IsAlgebraic.of_finite ℚ_[p] F₀
  letI : NontriviallyNormedField F₀ :=
    spectralNorm.nontriviallyNormedField ℚ_[p] F₀
  letI : NormedField F₀ :=
    (spectralNorm.nontriviallyNormedField ℚ_[p] F₀).toNormedField
  letI : Algebra.IsAlgebraic ℚ_[p] E :=
    Algebra.IsAlgebraic.of_finite ℚ_[p] E
  letI : NontriviallyNormedField E :=
    spectralNorm.nontriviallyNormedField ℚ_[p] E
  letI : NormedField E :=
    (spectralNorm.nontriviallyNormedField ℚ_[p] E).toNormedField
  let OF := Valuation.integer (qpadicSpectralValuation p F₀)
  let OE := Valuation.integer (qpadicSpectralValuation p E)
  let g : OF →+* E := (algebraMap F₀ E).comp OF.subtype
  exact (g.codRestrict OE (fun x ↦ by
    rw [Valuation.mem_integer_iff]
    change spectralNorm ℚ_[p] E (algebraMap F₀ E (x : F₀)) ≤ 1
    rw [padic_comparison_spectral p k n u x]
    have hx := x.property
    rw [Valuation.mem_integer_iff] at hx
    exact hx)).toAlgebra

set_option maxHeartbeats 2000000 in
-- The displayed algebra map contains both dependent spectral valuations.
set_option synthInstance.maxHeartbeats 500000 in
@[simp]
theorem comparison_spectral_algebra
    (n : ℕ) (u : ℤ_[p]ˣ)
    (x : Valuation.integer
      (qpadicSpectralValuation p (F p k n u))) :
    let F₀ := F p k n u
    let E := M p k n u
    letI : Algebra
        (Valuation.integer (qpadicSpectralValuation p F₀))
        (Valuation.integer (qpadicSpectralValuation p E)) :=
      comparisonSpectralAlgebra p k n u
    ((algebraMap
        (Valuation.integer (qpadicSpectralValuation p F₀))
        (Valuation.integer (qpadicSpectralValuation p E)) x :
      Valuation.integer (qpadicSpectralValuation p E)) : E) =
        algebraMap F₀ E (x : F₀) := by
  rfl

/-- The integer-valued Witt valuation pulled back to the finite comparison
compositum. -/
noncomputable def wittComparisonValuation
    (n : ℕ) (u : ℤ_[p]ˣ) :
    Valuation (M p k n u) (WithZero (Multiplicative ℤ)) :=
  Valuation.comap (M p k n u).val.toRingHom
    (wittFractionValuation p k n)

/-- The embedded cyclotomic root still has additive order one in the
comparison compositum. -/
theorem witt_comparison_valuation
    (n : ℕ) (u : ℤ_[p]ˣ) :
    wittComparisonValuation p k n u
        (padicWittComparison p k n u
          ((cyclotomicLubinDatum p).root ℚ_[p] n)) =
      WithZero.exp (-1 : ℤ) := by
  change wittFractionValuation p k n
      ((padicWittComparison p k n u
        ((cyclotomicLubinDatum p).root ℚ_[p] n) : M p k n u) :
          C p k n) = _
  rw [witt_comparison_coe,
    padic_witt_fraction]
  exact witt_fraction_valuation p k n

/-- The associated basic Lubin--Tate root has the same normalized value as
the cyclotomic root in the comparison compositum. -/
theorem padic_comparison_valuation
    (n : ℕ) (u : ℤ_[p]ˣ) :
    wittComparisonValuation p k n u
        (wittComparisonAlg p k n u
          ((padicTateDatum p u).root ℚ_[p] n)) =
      WithZero.exp (-1 : ℤ) := by
  let b := padicWittRoot p k n u
  let r := cyclotomicWittRoot p k n
  obtain ⟨z, hz⟩ := padic_witt_associated p k n u
  let P := IsDiscreteValuationRing.maximalIdeal (B p k n)
  have hvz : P.valuation (C p k n)
      (algebraMap (B p k n) (C p k n) (z : B p k n)) = 1 := by
    rw [P.valuation_of_algebraMap, P.intValuation_eq_one_iff]
    exact IsLocalRing.notMem_maximalIdeal.mpr z.isUnit
  have hzval : P.valuation (C p k n)
      (algebraMap (B p k n) (C p k n) b) =
      P.valuation (C p k n)
        (algebraMap (B p k n) (C p k n) r) := by
    have h := congrArg (fun y : B p k n ↦
      P.valuation (C p k n) (algebraMap (B p k n) (C p k n) y)) hz
    simpa only [map_mul, hvz, mul_one] using h
  change wittFractionValuation p k n
      ((wittComparisonAlg p k n u
        ((padicTateDatum p u).root ℚ_[p] n) : M p k n u) :
          C p k n) = _
  rw [padic_comparison_coe,
    witt_fraction_alg]
  change wittFractionValuation p k n
      (algebraMap (B p k n) (C p k n) b) = _
  rw [show wittFractionValuation p k n =
      P.valuation (C p k n) by rfl, hzval]
  exact witt_fraction_valuation p k n

set_option maxHeartbeats 3000000 in
-- This identifies two valuation subrings by comparing their absolute values.
set_option synthInstance.maxHeartbeats 500000 in
/-- The pullback of the Witt DVR valuation ring is exactly the spectral
integer ring of the finite comparison compositum. -/
theorem comparison_valuation_spectral
    (n : ℕ) (u : ℤ_[p]ˣ) :
    let E := M p k n u
    letI : Algebra.IsAlgebraic ℚ_[p] E :=
      Algebra.IsAlgebraic.of_finite ℚ_[p] E
    letI : NontriviallyNormedField E :=
      spectralNorm.nontriviallyNormedField ℚ_[p] E
    letI : NormedAlgebra ℚ_[p] E := spectralNorm.normedAlgebra ℚ_[p] E
    letI : IsUltrametricDist E := IsUltrametricDist.of_normedAlgebra ℚ_[p]
    Valuation.integer (wittComparisonValuation p k n u) =
      Valuation.integer (NormedField.valuation (K := E)) := by
  let E := M p k n u
  letI : Algebra.IsAlgebraic ℚ_[p] E :=
    Algebra.IsAlgebraic.of_finite ℚ_[p] E
  letI : NontriviallyNormedField E :=
    spectralNorm.nontriviallyNormedField ℚ_[p] E
  letI : NormedAlgebra ℚ_[p] E := spectralNorm.normedAlgebra ℚ_[p] E
  letI : IsUltrametricDist E := IsUltrametricDist.of_normedAlgebra ℚ_[p]
  let w := wittComparisonValuation p k n u
  ext x
  rw [Valuation.mem_integer_iff, Valuation.mem_integer_iff]
  change w x ≤ 1 ↔ ‖x‖₊ ≤ 1
  rw [← WithZeroMulInt.toNNReal_le_one_iff
    (witt_absolute_base p n)]
  have hnn : WithZeroMulInt.toNNReal
      (ne_zero_of_lt (witt_absolute_base p n))
      (w x) = ‖x‖₊ := by
    apply NNReal.eq
    change comparisonAbsoluteValue p k n u x =
      spectralNorm ℚ_[p] E x
    exact comparison_absolute_spectral
      p k n u x
  rw [hnn]

set_option maxHeartbeats 4000000 in
-- The pulled-back integer-valued valuation is surjective because the
-- cyclotomic root has value `exp (-1)`.
set_option synthInstance.maxHeartbeats 500000 in
/-- The embedded cyclotomic root is a uniformizer of the spectral integer
ring of the finite comparison compositum. -/
theorem witt_comparison_uniformizer
    (n : ℕ) (u : ℤ_[p]ˣ) :
    let E := M p k n u
    letI : Algebra.IsAlgebraic ℚ_[p] E :=
      Algebra.IsAlgebraic.of_finite ℚ_[p] E
    letI : NontriviallyNormedField E :=
      spectralNorm.nontriviallyNormedField ℚ_[p] E
    letI : NormedAlgebra ℚ_[p] E := spectralNorm.normedAlgebra ℚ_[p] E
    letI : IsUltrametricDist E := IsUltrametricDist.of_normedAlgebra ℚ_[p]
    let O := Valuation.integer (NormedField.valuation (K := E))
    ∃ alpha : O,
      O.subtype alpha =
          padicWittComparison p k n u
            ((cyclotomicLubinDatum p).root ℚ_[p] n) ∧
        IsLocalRing.maximalIdeal O = Ideal.span {alpha} := by
  let E := M p k n u
  letI : Algebra.IsAlgebraic ℚ_[p] E :=
    Algebra.IsAlgebraic.of_finite ℚ_[p] E
  letI : NontriviallyNormedField E :=
    spectralNorm.nontriviallyNormedField ℚ_[p] E
  letI : NormedAlgebra ℚ_[p] E := spectralNorm.normedAlgebra ℚ_[p] E
  letI : IsUltrametricDist E := IsUltrametricDist.of_normedAlgebra ℚ_[p]
  let w := wittComparisonValuation p k n u
  let root : E :=
    padicWittComparison p k n u
      ((cyclotomicLubinDatum p).root ℚ_[p] n)
  have hroot : w root = WithZero.exp (-1 : ℤ) :=
    witt_comparison_valuation p k n u
  letI : w.IsNontrivial := Valuation.IsNontrivial.mk ⟨root, by
    rw [hroot]
    simp, by
    rw [hroot]
    simp⟩
  letI : w.IsRankOneDiscrete := inferInstance
  have hsurj : Function.Surjective w := by
    intro y
    by_cases hy : y = 0
    · exact ⟨0, by simp [hy]⟩
    let m : ℤ := -WithZero.log y
    have hroot0 : root ≠ 0 := by
      intro hr
      rw [hr, map_zero] at hroot
      exact WithZero.exp_ne_zero hroot.symm
    refine ⟨root ^ m, ?_⟩
    rw [map_zpow₀, hroot]
    change (WithZero.exp (-1 : ℤ) : WithZero (Multiplicative ℤ)) ^
      (-WithZero.log y) = y
    rw [← WithZero.exp_zsmul]
    convert WithZero.exp_log hy using 1
    simp only [smul_eq_mul]
    ring_nf
  have hgenerator :=
    Valuation.IsRankOneDiscrete.generator_eq_exp_neg_one_of_surjective
      (v := w) hsurj
  have hrootUniformizer : w.IsUniformizer root := by
    rw [Valuation.IsUniformizer, hgenerator]
    exact hroot
  let Ow := Valuation.integer w
  let Os := Valuation.integer (NormedField.valuation (K := E))
  have hO : Ow = Os :=
    comparison_valuation_spectral
      p k n u
  let alphaW : Ow := ⟨root, hrootUniformizer.val_lt_one.le⟩
  have hrootUniformizerW : w.IsUniformizer (alphaW : E) := by
    exact hrootUniformizer
  have hmaxW : IsLocalRing.maximalIdeal Ow = Ideal.span {alphaW} :=
    hrootUniformizerW.is_generator
  let eInt : Ow ≃+* Os := RingEquiv.subringCongr hO
  have hmaxMap : (IsLocalRing.maximalIdeal Ow).map eInt.toRingHom =
      IsLocalRing.maximalIdeal Os :=
    IsLocalRing.eq_maximalIdeal
      ((inferInstance : (IsLocalRing.maximalIdeal Ow).IsMaximal).map_bijective
        eInt.toRingHom eInt.bijective)
  refine ⟨eInt alphaW, ?_, ?_⟩
  · rfl
  · rw [← hmaxMap, hmaxW, Ideal.map_span, Set.image_singleton]
    rfl

set_option maxHeartbeats 4000000 in
-- This is the preceding argument with an arbitrary element of value `exp (-1)`.
set_option synthInstance.maxHeartbeats 500000 in
/-- Any comparison-field element of Witt value `exp (-1)` is a
uniformizer of the spectral integer ring. -/
theorem comparison_uniformizer_value
    (n : ℕ) (u : ℤ_[p]ˣ) (x : M p k n u)
    (hx : wittComparisonValuation p k n u x =
      WithZero.exp (-1 : ℤ)) :
    let E := M p k n u
    letI : Algebra.IsAlgebraic ℚ_[p] E :=
      Algebra.IsAlgebraic.of_finite ℚ_[p] E
    letI : NontriviallyNormedField E :=
      spectralNorm.nontriviallyNormedField ℚ_[p] E
    letI : NormedAlgebra ℚ_[p] E := spectralNorm.normedAlgebra ℚ_[p] E
    letI : IsUltrametricDist E := IsUltrametricDist.of_normedAlgebra ℚ_[p]
    let O := Valuation.integer (NormedField.valuation (K := E))
    ∃ alpha : O, O.subtype alpha = x ∧
      IsLocalRing.maximalIdeal O = Ideal.span {alpha} := by
  let E := M p k n u
  letI : Algebra.IsAlgebraic ℚ_[p] E :=
    Algebra.IsAlgebraic.of_finite ℚ_[p] E
  letI : NontriviallyNormedField E :=
    spectralNorm.nontriviallyNormedField ℚ_[p] E
  letI : NormedAlgebra ℚ_[p] E := spectralNorm.normedAlgebra ℚ_[p] E
  letI : IsUltrametricDist E := IsUltrametricDist.of_normedAlgebra ℚ_[p]
  let w := wittComparisonValuation p k n u
  let root : E :=
    padicWittComparison p k n u
      ((cyclotomicLubinDatum p).root ℚ_[p] n)
  have hroot : w root = WithZero.exp (-1 : ℤ) :=
    witt_comparison_valuation p k n u
  letI : w.IsNontrivial := Valuation.IsNontrivial.mk ⟨root, by
    rw [hroot]
    simp, by
    rw [hroot]
    simp⟩
  letI : w.IsRankOneDiscrete := inferInstance
  have hsurj : Function.Surjective w := by
    intro y
    by_cases hy : y = 0
    · exact ⟨0, by simp [hy]⟩
    let m : ℤ := -WithZero.log y
    have hroot0 : root ≠ 0 := by
      intro hr
      rw [hr, map_zero] at hroot
      exact WithZero.exp_ne_zero hroot.symm
    refine ⟨root ^ m, ?_⟩
    rw [map_zpow₀, hroot]
    change (WithZero.exp (-1 : ℤ) : WithZero (Multiplicative ℤ)) ^
      (-WithZero.log y) = y
    rw [← WithZero.exp_zsmul]
    convert WithZero.exp_log hy using 1
    simp only [smul_eq_mul]
    ring_nf
  have hgenerator :=
    Valuation.IsRankOneDiscrete.generator_eq_exp_neg_one_of_surjective
      (v := w) hsurj
  have hxUniformizer : w.IsUniformizer x := by
    rw [Valuation.IsUniformizer, hgenerator]
    exact hx
  let Ow := Valuation.integer w
  let Os := Valuation.integer (NormedField.valuation (K := E))
  have hO : Ow = Os :=
    comparison_valuation_spectral
      p k n u
  let alphaW : Ow := ⟨x, hxUniformizer.val_lt_one.le⟩
  have hxUniformizerW : w.IsUniformizer (alphaW : E) := hxUniformizer
  have hmaxW : IsLocalRing.maximalIdeal Ow = Ideal.span {alphaW} :=
    hxUniformizerW.is_generator
  let eInt : Ow ≃+* Os := RingEquiv.subringCongr hO
  have hmaxMap : (IsLocalRing.maximalIdeal Ow).map eInt.toRingHom =
      IsLocalRing.maximalIdeal Os :=
    IsLocalRing.eq_maximalIdeal
      ((inferInstance : (IsLocalRing.maximalIdeal Ow).IsMaximal).map_bijective
        eInt.toRingHom eInt.bijective)
  refine ⟨eInt alphaW, rfl, ?_⟩
  rw [← hmaxMap, hmaxW, Ideal.map_span, Set.image_singleton]
  rfl

set_option maxHeartbeats 5000000 in
-- The two explicit uniformizers identify the maximal ideals on both sides.
set_option synthInstance.maxHeartbeats 500000 in
/-- The finite comparison compositum is finite and formally unramified over
its fixed basic Lubin--Tate root field at the level of spectral integer
rings. -/
theorem padic_comparison_formally
    (n : ℕ) (u : ℤ_[p]ˣ) :
    let F₀ := F p k n u
    let E := M p k n u
    let OF := Valuation.integer (qpadicSpectralValuation p F₀)
    let OE := Valuation.integer (qpadicSpectralValuation p E)
    letI : Algebra OF OE :=
      comparisonSpectralAlgebra p k n u
    Module.Finite OF OE ∧ Algebra.FormallyUnramified OF OE := by
  let F₀ := F p k n u
  let E := M p k n u
  letI : Algebra.IsAlgebraic ℚ_[p] F₀ :=
    Algebra.IsAlgebraic.of_finite ℚ_[p] F₀
  letI : NontriviallyNormedField F₀ :=
    spectralNorm.nontriviallyNormedField ℚ_[p] F₀
  letI : NormedField F₀ :=
    (spectralNorm.nontriviallyNormedField ℚ_[p] F₀).toNormedField
  letI : UniformSpace F₀ := PseudoMetricSpace.toUniformSpace
  letI : TopologicalSpace F₀ :=
    PseudoMetricSpace.toUniformSpace.toTopologicalSpace
  letI : NormedAlgebra ℚ_[p] F₀ := spectralNorm.normedAlgebra ℚ_[p] F₀
  letI : IsUltrametricDist F₀ := IsUltrametricDist.of_normedAlgebra ℚ_[p]
  letI : Algebra.IsAlgebraic ℚ_[p] E :=
    Algebra.IsAlgebraic.of_finite ℚ_[p] E
  letI : NontriviallyNormedField E :=
    spectralNorm.nontriviallyNormedField ℚ_[p] E
  letI : NormedField E :=
    (spectralNorm.nontriviallyNormedField ℚ_[p] E).toNormedField
  letI : UniformSpace E := PseudoMetricSpace.toUniformSpace
  letI : TopologicalSpace E :=
    PseudoMetricSpace.toUniformSpace.toTopologicalSpace
  letI : NormedAlgebra ℚ_[p] E := spectralNorm.normedAlgebra ℚ_[p] E
  letI : IsUltrametricDist E := IsUltrametricDist.of_normedAlgebra ℚ_[p]
  have hqF : qpadicSpectralValuation p F₀ =
      NormedField.valuation (K := F₀) := by
    ext x
    rfl
  have hqE : qpadicSpectralValuation p E =
      NormedField.valuation (K := E) := by
    ext x
    rfl
  let OF := Valuation.integer (qpadicSpectralValuation p F₀)
  let OE := Valuation.integer (qpadicSpectralValuation p E)
  let OFn := Valuation.integer (NormedField.valuation (K := F₀))
  let OEn := Valuation.integer (NormedField.valuation (K := E))
  let eOF : OF ≃+* OFn := RingEquiv.subringCongr
    (congrArg Valuation.integer hqF)
  let eOE : OE ≃+* OEn := RingEquiv.subringCongr
    (congrArg Valuation.integer hqE)
  letI : ValuativeRel F₀ := FLExt.valuativeRel ℚ_[p] F₀
  letI : Valuation.Compatible (NormedField.valuation (K := F₀)) :=
    Valuation.Compatible.ofValuation (NormedField.valuation (K := F₀))
  letI : IsNonarchimedeanLocalField F₀ :=
    FLExt.nonarchimedeanLocalField ℚ_[p] F₀
  letI : ValuativeRel E := FLExt.valuativeRel ℚ_[p] E
  letI : Valuation.Compatible (NormedField.valuation (K := E)) :=
    Valuation.Compatible.ofValuation (NormedField.valuation (K := E))
  letI : IsNonarchimedeanLocalField E :=
    FLExt.nonarchimedeanLocalField ℚ_[p] E
  letI : Algebra OF OE :=
    comparisonSpectralAlgebra p k n u
  let e : (padicTateDatum p u).RootField ℚ_[p] n ≃ₐ[ℚ_[p]] F₀ :=
    (padicWittBasic p k n u).trans
      (padicCyclotomicWitt p k n u)
  let root₀ := (padicTateDatum p u).root ℚ_[p] n
  let rootF : F₀ := e root₀
  let rootE : E :=
    wittComparisonAlg p k n u root₀
  obtain ⟨alphaF, halphaF, hmaxF⟩ :=
    padic_witt_uniformizer p k n u
  have hrootEval :
      wittComparisonValuation p k n u rootE =
        WithZero.exp (-1 : ℤ) :=
    padic_comparison_valuation p k n u
  obtain ⟨alphaE, halphaE, hmaxE⟩ :=
    comparison_uniformizer_value
      p k n u rootE hrootEval
  have hrootMap : algebraMap F₀ E rootF = rootE := by
    apply Subtype.ext
    rfl
  let betaF : OF := eOF.symm alphaF
  let betaE : OE := eOE.symm alphaE
  have hbetaMap : algebraMap OF OE betaF = betaE := by
    apply Subtype.ext
    rw [comparison_spectral_algebra]
    change algebraMap F₀ E (alphaF : F₀) = (alphaE : E)
    exact (congrArg (algebraMap F₀ E) halphaF).trans
      (hrootMap.trans halphaE.symm)
  let eF := valuativeIntegerNorm F₀
  let eE := valuativeIntegerNorm E
  letI : Finite (IsLocalRing.ResidueField OF) :=
    Finite.of_equiv
      (IsLocalRing.ResidueField
        (Valuation.integer (ValuativeRel.valuation F₀)))
      (IsLocalRing.ResidueField.mapEquiv eF).toEquiv
  letI : Finite (IsLocalRing.ResidueField OE) :=
    Finite.of_equiv
      (IsLocalRing.ResidueField
        (Valuation.integer (ValuativeRel.valuation E)))
      (IsLocalRing.ResidueField.mapEquiv eE).toEquiv
  letI : Algebra.IsSeparable (IsLocalRing.ResidueField OF)
      (IsLocalRing.ResidueField OE) := by infer_instance
  letI : NormedAlgebra F₀ E := spectralNorm.normedAlgebra' ℚ_[p] F₀ E
  letI : Algebra OE E := OE.subtype.toAlgebra
  letI : IsFractionRing OF F₀ :=
    (Valuation.integer.integers (qpadicSpectralValuation p F₀)).isFractionRing
  letI : IsFractionRing OE E :=
    (Valuation.integer.integers (qpadicSpectralValuation p E)).isFractionRing
  letI : IsScalarTower OF OE E := IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower OF F₀ E := IsScalarTower.of_algebraMap_eq' rfl
  letI : IsIntegralClosure OE OF E := by
    constructor
    · exact Subtype.coe_injective
    · intro x
      have heOF : (algebraMap OFn E).comp eOF.toRingHom =
          algebraMap OF E := by
        ext z
        rfl
      rw [eOF.isIntegral_iff heOF x,
        FLExt.integral_integer_spectral F₀ E x]
      have hspectral (z : E) : spectralNorm F₀ E z =
          spectralNorm ℚ_[p] E z := by
        rw [← NormedAlgebra.norm_eq_spectralNorm F₀ z]
        rfl
      constructor
      · intro hx
        refine ⟨⟨x, ?_⟩, rfl⟩
        rw [Valuation.mem_integer_iff]
        change spectralNorm ℚ_[p] E x ≤ 1
        rw [← hspectral x]
        exact hx
      · rintro ⟨y, rfl⟩
        have hy := y.property
        rw [Valuation.mem_integer_iff] at hy
        change spectralNorm ℚ_[p] E (y : E) ≤ 1 at hy
        change spectralNorm F₀ E (y : E) ≤ 1
        rw [hspectral (y : E)]
        exact hy
  letI : IsNoetherianRing OF :=
    isNoetherianRing_of_ringEquiv
      (Valuation.integer (ValuativeRel.valuation F₀))
      (eF.trans eOF.symm)
  letI : Module.Finite OF OE := IsIntegralClosure.finite OF F₀ E OE
  have hmaxOF : IsLocalRing.maximalIdeal OF = Ideal.span {betaF} := by
    calc
      IsLocalRing.maximalIdeal OF =
          (IsLocalRing.maximalIdeal OFn).map eOF.symm.toRingHom :=
        (IsLocalRing.map_ringEquiv_maximalIdeal eOF.symm).symm
      _ = (Ideal.span {alphaF}).map eOF.symm.toRingHom := by rw [hmaxF]
      _ = Ideal.span {betaF} := by
        rw [Ideal.map_span, Set.image_singleton]
        rfl
  have hmaxOE : IsLocalRing.maximalIdeal OE = Ideal.span {betaE} := by
    calc
      IsLocalRing.maximalIdeal OE =
          (IsLocalRing.maximalIdeal OEn).map eOE.symm.toRingHom :=
        (IsLocalRing.map_ringEquiv_maximalIdeal eOE.symm).symm
      _ = (Ideal.span {alphaE}).map eOE.symm.toRingHom := by rw [hmaxE]
      _ = Ideal.span {betaE} := by
        rw [Ideal.map_span, Set.image_singleton]
        rfl
  have hmaxMap : (IsLocalRing.maximalIdeal OF).map (algebraMap OF OE) =
      IsLocalRing.maximalIdeal OE := by
    rw [hmaxOF, Ideal.map_span, Set.image_singleton, hbetaMap, ← hmaxOE]
  letI : IsLocalHom (algebraMap OF OE) :=
    ((IsLocalRing.local_hom_TFAE (algebraMap OF OE)).out 0 2).mpr
      (le_of_eq hmaxMap)
  exact ⟨inferInstance,
    Algebra.FormallyUnramified.of_map_maximalIdeal hmaxMap⟩

/-- The formal-unramifiedness projection of the finite integral comparison
data. -/
theorem comparison_formally_basic
    (n : ℕ) (u : ℤ_[p]ˣ) :
    let F₀ := F p k n u
    let E := M p k n u
    let OF := Valuation.integer (qpadicSpectralValuation p F₀)
    let OE := Valuation.integer (qpadicSpectralValuation p E)
    letI : Algebra OF OE :=
      comparisonSpectralAlgebra p k n u
    Algebra.FormallyUnramified OF OE :=
  (padic_comparison_formally
    p k n u).2

set_option maxHeartbeats 2000000 in
-- Both normalized spectral presentations elaborate in the same equality.
set_option synthInstance.maxHeartbeats 500000 in
/-- The intrinsic relative spectral norm on the comparison compositum is
the same normalized absolute value as its spectral norm over `Q_p`. -/
theorem padic_spectral_qpadic
    (n : ℕ) (u : ℤ_[p]ˣ) :
    let F₀ := F p k n u
    let E := M p k n u
    letI : Algebra.IsAlgebraic ℚ_[p] F₀ :=
      Algebra.IsAlgebraic.of_finite ℚ_[p] F₀
    letI : NontriviallyNormedField F₀ :=
      spectralNorm.nontriviallyNormedField ℚ_[p] F₀
    letI : NormedField F₀ :=
      (spectralNorm.nontriviallyNormedField ℚ_[p] F₀).toNormedField
    letI : UniformSpace F₀ := PseudoMetricSpace.toUniformSpace
    letI : TopologicalSpace F₀ :=
      PseudoMetricSpace.toUniformSpace.toTopologicalSpace
    letI : NormedAlgebra ℚ_[p] F₀ := spectralNorm.normedAlgebra ℚ_[p] F₀
    letI : IsUltrametricDist F₀ := IsUltrametricDist.of_normedAlgebra ℚ_[p]
    ∀ z : E, spectralNorm F₀ E z = spectralNorm ℚ_[p] E z := by
  let F₀ := F p k n u
  let E := M p k n u
  letI : Algebra.IsAlgebraic ℚ_[p] F₀ :=
    Algebra.IsAlgebraic.of_finite ℚ_[p] F₀
  letI : NontriviallyNormedField F₀ :=
    spectralNorm.nontriviallyNormedField ℚ_[p] F₀
  letI : NormedField F₀ :=
    (spectralNorm.nontriviallyNormedField ℚ_[p] F₀).toNormedField
  letI : UniformSpace F₀ := PseudoMetricSpace.toUniformSpace
  letI : TopologicalSpace F₀ :=
    PseudoMetricSpace.toUniformSpace.toTopologicalSpace
  letI : NormedAlgebra ℚ_[p] F₀ := spectralNorm.normedAlgebra ℚ_[p] F₀
  letI : IsUltrametricDist F₀ := IsUltrametricDist.of_normedAlgebra ℚ_[p]
  change ∀ z : E, spectralNorm F₀ E z = spectralNorm ℚ_[p] E z
  intro z
  letI : Algebra.IsAlgebraic ℚ_[p] E :=
    Algebra.IsAlgebraic.of_finite ℚ_[p] E
  letI : NontriviallyNormedField E :=
    spectralNorm.nontriviallyNormedField ℚ_[p] E
  letI : NormedField E :=
    (spectralNorm.nontriviallyNormedField ℚ_[p] E).toNormedField
  letI : UniformSpace E := PseudoMetricSpace.toUniformSpace
  letI : TopologicalSpace E :=
    PseudoMetricSpace.toUniformSpace.toTopologicalSpace
  letI : NormedAlgebra ℚ_[p] E := spectralNorm.normedAlgebra ℚ_[p] E
  letI : IsUltrametricDist E := IsUltrametricDist.of_normedAlgebra ℚ_[p]
  letI : NormedAlgebra F₀ E := spectralNorm.normedAlgebra' ℚ_[p] F₀ E
  rw [← NormedAlgebra.norm_eq_spectralNorm F₀ z]
  rfl

set_option maxHeartbeats 3000000 in
-- Transporting both spectral integer models unfolds the two dependent norm
-- structures at once.
set_option synthInstance.maxHeartbeats 500000 in
/-- The same finite formally-unramified integral model, expressed using the
intrinsic spectral norm for the relative extension over the basic field. -/
theorem witt_comparison_formally
    (n : ℕ) (u : ℤ_[p]ˣ) :
    let F₀ := F p k n u
    let E := M p k n u
    letI : Algebra.IsAlgebraic ℚ_[p] F₀ :=
      Algebra.IsAlgebraic.of_finite ℚ_[p] F₀
    letI : NontriviallyNormedField F₀ :=
      spectralNorm.nontriviallyNormedField ℚ_[p] F₀
    letI : NormedField F₀ :=
      (spectralNorm.nontriviallyNormedField ℚ_[p] F₀).toNormedField
    letI : UniformSpace F₀ := PseudoMetricSpace.toUniformSpace
    letI : TopologicalSpace F₀ :=
      PseudoMetricSpace.toUniformSpace.toTopologicalSpace
    letI : NormedAlgebra ℚ_[p] F₀ := spectralNorm.normedAlgebra ℚ_[p] F₀
    letI : IsUltrametricDist F₀ := IsUltrametricDist.of_normedAlgebra ℚ_[p]
    letI : Algebra.IsAlgebraic F₀ E :=
      Algebra.IsAlgebraic.of_finite F₀ E
    letI : NontriviallyNormedField E :=
      spectralNorm.nontriviallyNormedField F₀ E
    letI : NormedField E :=
      (spectralNorm.nontriviallyNormedField F₀ E).toNormedField
    letI : UniformSpace E := PseudoMetricSpace.toUniformSpace
    letI : TopologicalSpace E :=
      PseudoMetricSpace.toUniformSpace.toTopologicalSpace
    letI : NormedAlgebra F₀ E := spectralNorm.normedAlgebra F₀ E
    letI : IsUltrametricDist E := IsUltrametricDist.of_normedAlgebra F₀
    letI : ValuativeRel F₀ := ValuativeRel.ofValuation
      (NormedField.valuation (K := F₀))
    letI : Valuation.Compatible (NormedField.valuation (K := F₀)) :=
      Valuation.Compatible.ofValuation _
    letI : IsNonarchimedeanLocalField F₀ :=
      FLExt.nonarchimedeanLocalField ℚ_[p] F₀
    letI : (NormedField.valuation (K := F₀)).HasExtension
        (NormedField.valuation (K := E)) := spectralValuationExtension F₀ E
    let OF := Valuation.integer (NormedField.valuation (K := F₀))
    let OE := Valuation.integer (NormedField.valuation (K := E))
    Module.Finite OF OE ∧ Algebra.FormallyUnramified OF OE := by
  let F₀ := F p k n u
  let E := M p k n u
  letI : Algebra.IsAlgebraic ℚ_[p] F₀ :=
    Algebra.IsAlgebraic.of_finite ℚ_[p] F₀
  letI : NontriviallyNormedField F₀ :=
    spectralNorm.nontriviallyNormedField ℚ_[p] F₀
  letI : NormedField F₀ :=
    (spectralNorm.nontriviallyNormedField ℚ_[p] F₀).toNormedField
  letI : UniformSpace F₀ := PseudoMetricSpace.toUniformSpace
  letI : TopologicalSpace F₀ :=
    PseudoMetricSpace.toUniformSpace.toTopologicalSpace
  letI : NormedAlgebra ℚ_[p] F₀ := spectralNorm.normedAlgebra ℚ_[p] F₀
  letI : IsUltrametricDist F₀ := IsUltrametricDist.of_normedAlgebra ℚ_[p]
  have hspectral (z : E) :
      spectralNorm F₀ E z = spectralNorm ℚ_[p] E z := by
    letI : Algebra.IsAlgebraic ℚ_[p] E :=
      Algebra.IsAlgebraic.of_finite ℚ_[p] E
    letI : NontriviallyNormedField E :=
      spectralNorm.nontriviallyNormedField ℚ_[p] E
    letI : NormedField E :=
      (spectralNorm.nontriviallyNormedField ℚ_[p] E).toNormedField
    letI : UniformSpace E := PseudoMetricSpace.toUniformSpace
    letI : TopologicalSpace E :=
      PseudoMetricSpace.toUniformSpace.toTopologicalSpace
    letI : NormedAlgebra ℚ_[p] E := spectralNorm.normedAlgebra ℚ_[p] E
    letI : IsUltrametricDist E := IsUltrametricDist.of_normedAlgebra ℚ_[p]
    letI : NormedAlgebra F₀ E := spectralNorm.normedAlgebra' ℚ_[p] F₀ E
    rw [← NormedAlgebra.norm_eq_spectralNorm F₀ z]
    rfl
  letI : Algebra.IsAlgebraic F₀ E :=
    Algebra.IsAlgebraic.of_finite F₀ E
  letI : NontriviallyNormedField E :=
    spectralNorm.nontriviallyNormedField F₀ E
  letI : NormedField E :=
    (spectralNorm.nontriviallyNormedField F₀ E).toNormedField
  letI : UniformSpace E := PseudoMetricSpace.toUniformSpace
  letI : TopologicalSpace E :=
    PseudoMetricSpace.toUniformSpace.toTopologicalSpace
  letI : NormedAlgebra F₀ E := spectralNorm.normedAlgebra F₀ E
  letI : IsUltrametricDist E := IsUltrametricDist.of_normedAlgebra F₀
  letI : ValuativeRel F₀ := ValuativeRel.ofValuation
    (NormedField.valuation (K := F₀))
  letI : Valuation.Compatible (NormedField.valuation (K := F₀)) :=
    Valuation.Compatible.ofValuation _
  letI : IsNonarchimedeanLocalField F₀ :=
    FLExt.nonarchimedeanLocalField ℚ_[p] F₀
  letI : (NormedField.valuation (K := F₀)).HasExtension
      (NormedField.valuation (K := E)) := spectralValuationExtension F₀ E
  let OFq := Valuation.integer (qpadicSpectralValuation p F₀)
  let OEq := Valuation.integer (qpadicSpectralValuation p E)
  let OF := Valuation.integer (NormedField.valuation (K := F₀))
  let OE := Valuation.integer (NormedField.valuation (K := E))
  have hOF : OFq = OF := by
    apply SetLike.ext
    intro x
    rfl
  have hOE : OEq = OE := by
    apply SetLike.ext
    intro x
    change spectralNorm ℚ_[p] E x ≤ 1 ↔ spectralNorm F₀ E x ≤ 1
    rw [hspectral]
  change Module.Finite OFq OE ∧ Algebra.FormallyUnramified OFq OE
  let eE : OEq ≃+* OE := RingEquiv.subringCongr hOE
  letI : Algebra OFq OEq :=
    comparisonSpectralAlgebra p k n u
  letI : Algebra OFq OE := inferInstance
  let eEalg : OEq ≃ₐ[OFq] OE :=
    AlgEquiv.ofRingEquiv (f := eE) (fun x ↦ by
      apply Subtype.ext
      rfl)
  have hq :=
    padic_comparison_formally
      p k n u
  letI : Module.Finite OFq OEq := hq.1
  letI : Algebra.FormallyUnramified OFq OEq := hq.2
  exact ⟨Module.Finite.equiv eEalg.toLinearEquiv,
    Algebra.FormallyUnramified.of_equiv eEalg⟩

set_option maxHeartbeats 4000000 in
-- The lift is selected through the equality between the pulled-back Witt
-- valuation ring and the spectral integer ring.
set_option synthInstance.maxHeartbeats 500000 in
/-- Every spectral integer of the comparison compositum lifts to the common
Witt-root DVR. -/
theorem comparison_spectral_ring
    (n : ℕ) (u : ℤ_[p]ˣ)
    (z : Valuation.integer
      (qpadicSpectralValuation p (M p k n u))) :
    ∃ b : B p k n, algebraMap (B p k n) (C p k n) b =
      ((z : M p k n u) : C p k n) := by
  let E := M p k n u
  let w := wittComparisonValuation p k n u
  let OE := Valuation.integer (qpadicSpectralValuation p E)
  let Ow := Valuation.integer w
  letI : Algebra.IsAlgebraic ℚ_[p] E :=
    Algebra.IsAlgebraic.of_finite ℚ_[p] E
  letI : NontriviallyNormedField E :=
    spectralNorm.nontriviallyNormedField ℚ_[p] E
  letI : NormedField E :=
    (spectralNorm.nontriviallyNormedField ℚ_[p] E).toNormedField
  letI : NormedAlgebra ℚ_[p] E := spectralNorm.normedAlgebra ℚ_[p] E
  letI : IsUltrametricDist E := IsUltrametricDist.of_normedAlgebra ℚ_[p]
  have hq : qpadicSpectralValuation p E =
      NormedField.valuation (K := E) := by
    ext x
    rfl
  have hO : Ow = OE :=
    (comparison_valuation_spectral
      p k n u).trans (congrArg Valuation.integer hq).symm
  let eO : OE ≃+* Ow := RingEquiv.subringCongr hO.symm
  have hz : w (z : E) ≤ 1 := (eO z).property
  exact IsDiscreteValuationRing.exists_lift_of_le_one hz

set_option maxHeartbeats 4000000 in
-- Each ring law unfolds the selected lift in the dependent comparison
-- integer ring.
set_option synthInstance.maxHeartbeats 500000 in
/-- The unique lift of comparison-field spectral integers to the common
Witt-root DVR, packaged as a ring homomorphism. -/
noncomputable def wittComparisonSpectral
    (n : ℕ) (u : ℤ_[p]ˣ) :
    Valuation.integer (qpadicSpectralValuation p (M p k n u)) →+*
      B p k n :=
    { toFun := fun z ↦ Classical.choose
        (comparison_spectral_ring
          p k n u z)
      map_zero' := by
        apply IsFractionRing.injective (B p k n) (C p k n)
        rw [Classical.choose_spec
          (comparison_spectral_ring
            p k n u 0)]
        simp
      map_one' := by
        apply IsFractionRing.injective (B p k n) (C p k n)
        rw [Classical.choose_spec
          (comparison_spectral_ring
            p k n u 1)]
        simp
      map_add' := fun x y ↦ by
        apply IsFractionRing.injective (B p k n) (C p k n)
        rw [Classical.choose_spec
            (comparison_spectral_ring
              p k n u (x + y)), map_add,
          Classical.choose_spec
            (comparison_spectral_ring
              p k n u x),
          Classical.choose_spec
            (comparison_spectral_ring
              p k n u y)]
        rfl
      map_mul' := fun x y ↦ by
        apply IsFractionRing.injective (B p k n) (C p k n)
        rw [Classical.choose_spec
            (comparison_spectral_ring
              p k n u (x * y)), map_mul,
          Classical.choose_spec
            (comparison_spectral_ring
              p k n u x),
          Classical.choose_spec
            (comparison_spectral_ring
              p k n u y)]
        rfl }

set_option maxHeartbeats 2000000 in
-- Unfolding the selected DVR lift and both intermediate-field coercions is
-- needed to expose the defining fraction-field equality.
set_option synthInstance.maxHeartbeats 500000 in
@[simp]
theorem witt_comparison_spectral
    (n : ℕ) (u : ℤ_[p]ˣ)
    (z : Valuation.integer
      (qpadicSpectralValuation p (M p k n u))) :
    algebraMap (B p k n) (C p k n)
        (wittComparisonSpectral p k n u z) =
      ((z : M p k n u) : C p k n) := by
  exact Classical.choose_spec
    (comparison_spectral_ring p k n u z)

set_option maxHeartbeats 4000000 in
-- The proof compares the finite-field residue action in the Witt DVR with
-- the spectral norm on the finite comparison compositum.
set_option synthInstance.maxHeartbeats 500000 in
/-- On every spectral integer of the comparison compositum, the explicit
relative Witt Frobenius is congruent to the `p`-th power map modulo the
maximal ideal. -/
theorem padic_witt_comparison
    (n : ℕ) (u : ℤ_[p]ˣ)
    (z : Valuation.integer
      (qpadicSpectralValuation p (M p k n u))) :
    spectralNorm ℚ_[p] (M p k n u)
        (wittComparisonFrobenius p k n u (z : M p k n u) -
          (z : M p k n u) ^ p) < 1 := by
  let E := M p k n u
  let b : B p k n :=
    wittComparisonSpectral p k n u z
  let d : B p k n :=
    wittFrobeniusLift p k n u b - b ^ p
  have hb : algebraMap (B p k n) (C p k n) b =
      ((z : E) : C p k n) :=
    witt_comparison_spectral
      p k n u z
  have hresFrob : padicWittResidue p k n
      (wittFrobeniusLift p k n u b) =
        frobenius k p (padicWittResidue p k n b) := by
    exact DFunLike.congr_fun
      (padic_witt_lift p k n u) b
  have hres : padicWittResidue p k n d = 0 := by
    rw [map_sub, map_pow, hresFrob]
    simp only [frobenius_def, sub_self]
  have hdmem : d ∈ IsLocalRing.maximalIdeal (B p k n) := by
    rw [padic_witt_maximal p k n,
      ← padic_witt_ker p k n,
      RingHom.mem_ker]
    exact hres
  let P := IsDiscreteValuationRing.maximalIdeal (B p k n)
  have hdval : P.valuation (C p k n)
      (algebraMap (B p k n) (C p k n) d) < 1 := by
    rw [P.valuation_lt_one_iff_mem]
    simpa [P, IsDiscreteValuationRing.maximalIdeal] using hdmem
  have hdcoe :
      ((wittComparisonFrobenius p k n u (z : E) -
          (z : E) ^ p : E) : C p k n) =
        algebraMap (B p k n) (C p k n) d := by
    rw [padic_witt_coe]
    change padicFractionFrobenius p k n u
        ((z : E) : C p k n) - ((z : E) : C p k n) ^ p = _
    rw [← hb,
      witt_fraction_algebra]
    simp only [d, map_sub, map_pow]
  rw [← comparison_absolute_spectral]
  change wittAbsoluteValue p k n
      (((wittComparisonFrobenius p k n u (z : E) -
          (z : E) ^ p : E) : C p k n)) < 1
  rw [hdcoe]
  change ((WithZeroMulInt.toNNReal
      (ne_zero_of_lt (witt_absolute_base p n))
      (P.valuation (C p k n)
        (algebraMap (B p k n) (C p k n) d)) : ℝ≥0) : ℝ) < 1
  exact_mod_cast
    (WithZeroMulInt.toNNReal_lt_one_iff
      (witt_absolute_base p n)).2 hdval

set_option maxHeartbeats 4000000 in
-- The source and target are intermediate fields with inherited structures;
-- the statement fixes their canonical spectral norm structures explicitly.
set_option synthInstance.maxHeartbeats 500000 in
/-- The explicit relative Witt Frobenius satisfies the intrinsic arithmetic
Frobenius residue-power criterion over the fixed basic field. -/
theorem witt_comparison_arithmetic
    (n : ℕ) (u : ℤ_[p]ˣ) :
    let F₀ := F p k n u
    let E := M p k n u
    letI : Algebra.IsAlgebraic ℚ_[p] F₀ :=
      Algebra.IsAlgebraic.of_finite ℚ_[p] F₀
    letI : NontriviallyNormedField F₀ :=
      spectralNorm.nontriviallyNormedField ℚ_[p] F₀
    letI : NormedAlgebra ℚ_[p] F₀ := spectralNorm.normedAlgebra ℚ_[p] F₀
    letI : IsUltrametricDist F₀ := IsUltrametricDist.of_normedAlgebra ℚ_[p]
    letI : Algebra.IsAlgebraic ℚ_[p] E :=
      Algebra.IsAlgebraic.of_finite ℚ_[p] E
    letI : NontriviallyNormedField E :=
      spectralNorm.nontriviallyNormedField ℚ_[p] E
    letI : NormedAlgebra ℚ_[p] E := spectralNorm.normedAlgebra ℚ_[p] E
    letI : IsUltrametricDist E := IsUltrametricDist.of_normedAlgebra ℚ_[p]
    ∀ x : E, ‖x‖ ≤ 1 →
      ‖wittComparisonFrobenius p k n u x -
          x ^ Towers.CField.LFTheory.localResidueCardinality F₀‖ < 1 := by
  let F₀ := F p k n u
  let E := M p k n u
  letI : Algebra.IsAlgebraic ℚ_[p] F₀ :=
    Algebra.IsAlgebraic.of_finite ℚ_[p] F₀
  letI : NontriviallyNormedField F₀ :=
    spectralNorm.nontriviallyNormedField ℚ_[p] F₀
  letI : NormedAlgebra ℚ_[p] F₀ := spectralNorm.normedAlgebra ℚ_[p] F₀
  letI : IsUltrametricDist F₀ := IsUltrametricDist.of_normedAlgebra ℚ_[p]
  letI : Algebra.IsAlgebraic ℚ_[p] E :=
    Algebra.IsAlgebraic.of_finite ℚ_[p] E
  letI : NontriviallyNormedField E :=
    spectralNorm.nontriviallyNormedField ℚ_[p] E
  letI : NormedAlgebra ℚ_[p] E := spectralNorm.normedAlgebra ℚ_[p] E
  letI : IsUltrametricDist E := IsUltrametricDist.of_normedAlgebra ℚ_[p]
  have hcard : Towers.CField.LFTheory.localResidueCardinality F₀ = p :=
    padic_comparison_card p k n u
  change ∀ x : E, spectralNorm ℚ_[p] E x ≤ 1 →
    spectralNorm ℚ_[p] E
      (wittComparisonFrobenius p k n u x -
        x ^ Towers.CField.LFTheory.localResidueCardinality F₀) < 1
  intro x hx
  let z : Valuation.integer (qpadicSpectralValuation p E) := ⟨x, by
    rw [Valuation.mem_integer_iff]
    change spectralNorm ℚ_[p] E x ≤ 1
    exact hx⟩
  rw [hcard]
  change spectralNorm ℚ_[p] E
      (wittComparisonFrobenius p k n u x - x ^ p) < 1
  simpa only [z] using
    (padic_witt_comparison
      p k n u z)

end

end Towers.CField.LTate
