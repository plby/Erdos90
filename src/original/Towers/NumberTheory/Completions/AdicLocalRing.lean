import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.Flat.TorsionFree
import Towers.NumberTheory.Valuations.DiscreteValuations

/-!
# A local Dedekind ring inside its adic completion

This file constructs the canonical map from the localization of a Dedekind
domain at a height-one prime to the integer ring in its adic completion.  It
also records that this map is local, injective, and faithfully flat.  These
facts support descent along completion in Milne's proof of Theorem 8.42.
-/

namespace Towers.NumberTheory.Milne

open Ideal IsDedekindDomain HeightOneSpectrum WithZeroMulInt WithZero
open scoped WithZero Valued algebraMap Topology

noncomputable section

universe u

variable {R K : Type u} [CommRing R] [IsDedekindDomain R]
  [Field K] [Algebra R K] [IsFractionRing R K]

/-- The extension of a height-one prime to the integer ring in its adic
completion is the maximal ideal. -/
theorem adic_integers_maximal
    (v : HeightOneSpectrum R) [Finite (R ⧸ v.asIdeal)] :
    v.asIdeal.map (algebraMap R (v.adicCompletionIntegers K)) =
      IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) := by
  obtain ⟨pi, hpi⟩ := v.intValuation_exists_uniformizer
  let pihat : v.adicCompletionIntegers K :=
    algebraMap R (v.adicCompletionIntegers K) pi
  have hpimem : pi ∈ v.asIdeal := by
    rw [← v.intValuation_lt_one_iff_mem, hpi]
    simp [-exp_neg, ← exp_zero]
  have hpihat :
      (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰).IsUniformizer
        (pihat : v.adicCompletion K) := by
    rw [Valuation.IsUniformizer.iff]
    rw [Valuation.IsRankOneDiscrete.generator_eq_exp_neg_one_of_surjective
      (v.valuedAdicCompletion_surjective K)]
    change Valued.v (algebraMap R (v.adicCompletion K) pi) = exp (-1 : ℤ)
    rw [v.valuedAdicCompletion_eq_valuation pi, v.valuation_of_algebraMap]
    exact hpi
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    intro r hr
    change algebraMap R (v.adicCompletionIntegers K) r ∈
      IsLocalRing.maximalIdeal (v.adicCompletionIntegers K)
    unfold HeightOneSpectrum.adicCompletionIntegers
    rw [(Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰).mem_maximalIdeal_iff]
    change Valued.v (algebraMap R (v.adicCompletion K) r) < 1
    rw [v.valuedAdicCompletion_eq_valuation r, v.valuation_of_algebraMap,
      v.intValuation_lt_one_iff_mem]
    exact hr
  · have hmax :
        IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) =
          Ideal.span {pihat} := by
      simpa only [HeightOneSpectrum.adicCompletionIntegers] using hpihat.is_generator
    rw [hmax]
    apply Ideal.span_le.mpr
    intro x hx
    simp only [Set.mem_singleton_iff] at hx
    subst x
    exact Ideal.mem_map_of_mem (algebraMap R (v.adicCompletionIntegers K)) hpimem

private theorem adic_integers_compl
    (v : HeightOneSpectrum R) [Finite (R ⧸ v.asIdeal)]
    (r : v.asIdeal.primeCompl) :
    IsUnit (algebraMap R (v.adicCompletionIntegers K) (r : R)) := by
  rw [HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one]
  change Valued.v (algebraMap R (v.adicCompletion K) (r : R)) = 1
  rw [v.valuedAdicCompletion_eq_valuation (r : R), v.valuation_of_algebraMap,
    intValuation_eq_one_iff]
  exact r.property

/-- The canonical map from the local ring at a height-one prime to its
completed valuation ring. -/
noncomputable def primeAdicIntegers
    (v : HeightOneSpectrum R) [Finite (R ⧸ v.asIdeal)] :
    Localization.AtPrime v.asIdeal →+* v.adicCompletionIntegers K :=
  IsLocalization.lift
    (adic_integers_compl (K := K) v)

@[simp]
theorem adic_integers_algebra
    (v : HeightOneSpectrum R) [Finite (R ⧸ v.asIdeal)] (r : R) :
    primeAdicIntegers (K := K) v
        (algebraMap R (Localization.AtPrime v.asIdeal) r) =
      algebraMap R (v.adicCompletionIntegers K) r := by
  simp [primeAdicIntegers, IsLocalization.lift_eq]

/-- The local-to-completed-integers map is injective. -/
theorem adic_integers_injective
    (v : HeightOneSpectrum R) [Finite (R ⧸ v.asIdeal)] :
    Function.Injective (primeAdicIntegers (K := K) v) := by
  apply (IsLocalization.lift_injective_iff _).2
  intro x y
  rw [(IsLocalization.injective (Localization.AtPrime v.asIdeal)
      v.asIdeal.primeCompl_le_nonZeroDivisors).eq_iff,
    (FaithfulSMul.algebraMap_injective R (v.adicCompletionIntegers K)).eq_iff]

/-- The localized Dedekind ring has dense image in its completed valuation
ring. -/
theorem adic_integers_range
    (v : HeightOneSpectrum R) [Finite (R ⧸ v.asIdeal)] :
    DenseRange (primeAdicIntegers (K := K) v) := by
  rw [denseRange_iff_closure_range]
  apply Set.eq_univ_of_forall
  intro x
  rw [mem_closure_iff_nhds']
  intro s hs
  obtain ⟨u, hu, hus⟩ :=
    (mem_nhds_subtype (v.adicCompletionIntegers K :
      Set (v.adicCompletion K)) x s).mp hs
  have hinteger :=
    (Valued.isOpen_integer (v.adicCompletion K)).mem_nhds x.property
  obtain ⟨k, hk⟩ := (v.denseRange_algebraMap (K := K)).mem_nhds
    (Filter.inter_mem hu hinteger)
  have hkint : algebraMap K (v.adicCompletion K) k ∈
      v.adicCompletionIntegers K := hk.2
  have hkval : v.valuation K k ≤ 1 := by
    rw [← v.valuedAdicCompletion_eq_valuation' (K := K) k]
    exact hkint
  obtain ⟨n, d, hnd⟩ := v.exists_primeCompl_mul_eq_of_integer k hkval
  let a : Localization.AtPrime v.asIdeal :=
    IsLocalization.mk' (Localization.AtPrime v.asIdeal) n d
  let y : v.adicCompletionIntegers K :=
    ⟨algebraMap K (v.adicCompletion K) k, hkint⟩
  have hay : primeAdicIntegers (K := K) v a = y := by
    apply (IsLocalization.lift_mk'_spec
      (adic_integers_compl
        (K := K) v) n y d).2
    apply Subtype.ext
    change algebraMap R (v.adicCompletion K) n =
      algebraMap R (v.adicCompletion K) (d : R) *
        algebraMap K (v.adicCompletion K) k
    have hnd' := congrArg (algebraMap K (v.adicCompletion K)) hnd
    calc
      algebraMap R (v.adicCompletion K) n =
          algebraMap K (v.adicCompletion K) (algebraMap R K n) :=
        IsScalarTower.algebraMap_apply R K (v.adicCompletion K) n
      _ = algebraMap K (v.adicCompletion K) k *
          algebraMap K (v.adicCompletion K) (algebraMap R K (d : R)) := by
        simpa only [map_mul] using hnd'.symm
      _ = algebraMap R (v.adicCompletion K) (d : R) *
          algebraMap K (v.adicCompletion K) k := by
        rw [← IsScalarTower.algebraMap_apply R K (v.adicCompletion K), mul_comm]
  refine ⟨⟨primeAdicIntegers (K := K) v a, ⟨a, rfl⟩⟩, ?_⟩
  apply hus
  change ((primeAdicIntegers (K := K) v a :
    v.adicCompletionIntegers K) : v.adicCompletion K) ∈ u
  rw [hay]
  exact hk.1

/-- The localized maximal ideal extends to the maximal ideal of the
completed valuation ring. -/
theorem maximal_completion_integers
    (v : HeightOneSpectrum R) [Finite (R ⧸ v.asIdeal)] :
    (IsLocalRing.maximalIdeal (Localization.AtPrime v.asIdeal)).map
        (primeAdicIntegers (K := K) v) =
      IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) := by
  rw [← Localization.AtPrime.map_eq_maximalIdeal (I := v.asIdeal)]
  rw [Ideal.map_map]
  change v.asIdeal.map
      ((primeAdicIntegers (K := K) v).comp
        (algebraMap R (Localization.AtPrime v.asIdeal))) = _
  have hcomp :
      (primeAdicIntegers (K := K) v).comp
          (algebraMap R (Localization.AtPrime v.asIdeal)) =
        algebraMap R (v.adicCompletionIntegers K) := by
    ext r
    exact congrArg Subtype.val
      (adic_integers_algebra (K := K) v r)
  rw [hcomp]
  exact adic_integers_maximal (K := K) v

/-- The local-to-completion map is a local homomorphism. -/
theorem adic_integers_hom
    (v : HeightOneSpectrum R) [Finite (R ⧸ v.asIdeal)] :
    IsLocalHom (primeAdicIntegers (K := K) v) := by
  apply ((IsLocalRing.local_hom_TFAE
    (primeAdicIntegers (K := K) v)).out 2 0).mp
  exact le_of_eq
    (maximal_completion_integers (K := K) v)

set_option synthInstance.maxHeartbeats 200000 in
-- Inferring flatness passes through torsion-freeness over the localized DVR.
set_option maxHeartbeats 800000 in
/-- The completed valuation ring is faithfully flat over the local ring. -/
theorem integers_faithfully_flat
    (v : HeightOneSpectrum R) [Finite (R ⧸ v.asIdeal)] :
    letI : Algebra (Localization.AtPrime v.asIdeal)
        (v.adicCompletionIntegers K) :=
      (primeAdicIntegers (K := K) v).toAlgebra
    Module.FaithfullyFlat (Localization.AtPrime v.asIdeal)
      (v.adicCompletionIntegers K) := by
  letI : Algebra (Localization.AtPrime v.asIdeal)
      (v.adicCompletionIntegers K) :=
    (primeAdicIntegers (K := K) v).toAlgebra
  letI : FaithfulSMul (Localization.AtPrime v.asIdeal)
      (v.adicCompletionIntegers K) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr <| by
      change Function.Injective
        (primeAdicIntegers (K := K) v)
      exact adic_integers_injective (K := K) v
  letI : Module.IsTorsionFree (Localization.AtPrime v.asIdeal)
      (v.adicCompletionIntegers K) := inferInstance
  letI : Module.Flat (Localization.AtPrime v.asIdeal)
      (v.adicCompletionIntegers K) := inferInstance
  letI : IsLocalHom (algebraMap (Localization.AtPrime v.asIdeal)
      (v.adicCompletionIntegers K)) :=
    adic_integers_hom (K := K) v
  exact Module.FaithfullyFlat.of_flat_of_isLocalHom

set_option synthInstance.maxHeartbeats 200000 in
-- The target maximal ideal unfolds the completed valuation ring.
/-- Powers of the localized maximal ideal extend to the corresponding
powers of the maximal ideal in the completed valuation ring. -/
theorem maximal_adic_integers
    (v : HeightOneSpectrum R) [Finite (R ⧸ v.asIdeal)] (n : ℕ) :
    ((IsLocalRing.maximalIdeal (Localization.AtPrime v.asIdeal)) ^ n).map
        (primeAdicIntegers (K := K) v) =
      (IsLocalRing.maximalIdeal (v.adicCompletionIntegers K)) ^ n := by
  rw [Ideal.map_pow,
    maximal_completion_integers (K := K) v]

end

end Towers.NumberTheory.Milne
