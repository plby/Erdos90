import Towers.ClassField.Ideles.Ideles
import Mathlib.Topology.Maps.Basic

/-!
# Chapter V, Section 4, Statement 4.3

For every place `v` of a number field `K`, putting a local element in the
`v`-coordinate and `1` in every other coordinate gives a canonical injective
homomorphism `K_vˣ → ℐ_K`.  The topology induced from the idèle group is the
natural topology on `K_vˣ`.

The algebraic maps and their injectivity are defined in `IdeleGroup`.  Here the
induced-topology assertion is expressed literally by proving that both maps
are topological embeddings.
-/

namespace Towers.CField.Ideles

open Filter IsDedekindDomain NumberField Topology
open scoped RestrictedProduct

noncomputable section

universe u

variable {K : Type u} [Field K] [NumberField K]

local notation "𝓞K" => NumberField.RingOfIntegers K

/-- A one-coordinate element, first regarded as an element of the principal
restricted product whose integral set is the complement of that coordinate. -/
private def finitePrincipalSingle (v : HeightOneSpectrum 𝓞K)
    (x : (v.adicCompletion K)ˣ) :
    Πʳ w : HeightOneSpectrum 𝓞K,
      [(w.adicCompletion K)ˣ, IdeleUnitSubgroup 𝓞K K w]_[𝓟 ({v}ᶜ)] := by
  classical
  refine ⟨Pi.mulSingle (M := fun w => (w.adicCompletion K)ˣ) v x, ?_⟩
  rw [eventually_principal]
  intro w hw
  have hwv : w ≠ v := by simpa using hw
  rw [Pi.mulSingle_eq_of_ne hwv]
  exact (IdeleUnitSubgroup 𝓞K K w).one_mem

private theorem continuous_principal_single
    (v : HeightOneSpectrum 𝓞K) :
    Continuous (finitePrincipalSingle (K := K) v) := by
  classical
  apply RestrictedProduct.continuous_rng_of_principal_iff_forall.mpr
  intro w
  change Continuous (fun x : (v.adicCompletion K)ˣ =>
    Pi.mulSingle (M := fun w => (w.adicCompletion K)ˣ) v x w)
  have hsingle : Continuous (fun x : (v.adicCompletion K)ˣ =>
      (Pi.mulSingle (M := fun w => (w.adicCompletion K)ˣ) v x :
        (w : HeightOneSpectrum 𝓞K) → (w.adicCompletion K)ˣ)) := by
    exact continuous_mulSingle
      (A := fun w : HeightOneSpectrum 𝓞K => (w.adicCompletion K)ˣ) v
  exact (continuous_apply w).comp hsingle

omit [NumberField K] in
private theorem cofinite_compl_singleton
    (v : HeightOneSpectrum 𝓞K) :
    cofinite ≤ 𝓟 ({v}ᶜ) := by
  rw [le_principal_iff, mem_cofinite]
  simp

/-- The finite one-coordinate homomorphism is continuous for the
restricted-product topology. -/
theorem continuous_local_embedding
    (v : HeightOneSpectrum 𝓞K) :
    Continuous (finiteLocalEmbedding 𝓞K K v) := by
  classical
  let hS : cofinite ≤ 𝓟 ({v}ᶜ) :=
    cofinite_compl_singleton (K := K) v
  have hcontinuous : Continuous (fun x : (v.adicCompletion K)ˣ =>
      RestrictedProduct.inclusion
        (fun w : HeightOneSpectrum 𝓞K => (w.adicCompletion K)ˣ)
        (fun w => (IdeleUnitSubgroup 𝓞K K w :
          Set (w.adicCompletion K)ˣ)) hS
        (finitePrincipalSingle (K := K) v x)) :=
    (RestrictedProduct.continuous_inclusion hS).comp
      (continuous_principal_single (K := K) v)
  convert hcontinuous using 1

/-- The finite-place homomorphism into the full idèle group is continuous. -/
theorem continuous_finite_embedding
    (v : HeightOneSpectrum 𝓞K) :
    Continuous (finitePlaceEmbedding 𝓞K K v) :=
  continuous_const.prodMk (continuous_local_embedding (K := K) v)

/-- At a finite place, the canonical map `K_vˣ → ℐ_K` induces precisely the
natural topology on `K_vˣ`. -/
theorem embedding_finite_place
    (v : HeightOneSpectrum 𝓞K) :
    IsEmbedding (finitePlaceEmbedding 𝓞K K v) := by
  classical
  let project : IdeleGroup 𝓞K K → (v.adicCompletion K)ˣ := fun a => a.2.1 v
  have hproject : Continuous project :=
    by
      simpa [project, Function.comp_def] using
        ((RestrictedProduct.continuous_eval v).comp continuous_snd)
  have hleft : Function.LeftInverse project (finitePlaceEmbedding 𝓞K K v) := by
    intro x
    exact RestrictedProduct.mulSingle_eq_same
      (IdeleUnitSubgroup 𝓞K K) v x
  exact hleft.isEmbedding hproject
    (continuous_finite_embedding (K := K) v)

omit [NumberField K] in
/-- The infinite one-coordinate homomorphism is continuous. -/
theorem continuous_infinite_embedding (v : InfinitePlace K) :
    Continuous (infiniteLocalEmbedding K v) := by
  classical
  change Continuous (fun x : v.Completionˣ =>
    (ContinuousMulEquiv.piUnits.symm)
      (Pi.mulSingle v x : (w : InfinitePlace K) → w.Completionˣ))
  have hsingle : Continuous (fun x : v.Completionˣ =>
      (Pi.mulSingle v x : (w : InfinitePlace K) → w.Completionˣ)) := by
    exact continuous_mulSingle
      (A := fun w : InfinitePlace K => w.Completionˣ) v
  exact ContinuousMulEquiv.piUnits.symm.continuous.comp
    hsingle

/-- The infinite-place homomorphism into the full idèle group is continuous. -/
theorem continuous_place_embedding (v : InfinitePlace K) :
    Continuous (infinitePlaceEmbedding 𝓞K K v) :=
  (continuous_infinite_embedding (K := K) v).prodMk continuous_const

/-- At an infinite place, the canonical map `K_vˣ → ℐ_K` induces precisely
the natural topology on `K_vˣ`. -/
theorem embedding_infinite_place (v : InfinitePlace K) :
    IsEmbedding (infinitePlaceEmbedding 𝓞K K v) := by
  classical
  let project : IdeleGroup 𝓞K K → v.Completionˣ := fun a =>
    ContinuousMulEquiv.piUnits a.1 v
  have hproject : Continuous project :=
    (continuous_apply v).comp
      (ContinuousMulEquiv.piUnits.continuous.comp continuous_fst)
  have hleft : Function.LeftInverse project
      (infinitePlaceEmbedding 𝓞K K v) := by
    intro x
    change (MulEquiv.piUnits
      (MulEquiv.piUnits.symm
        (Pi.mulSingle v x : (w : InfinitePlace K) → w.Completionˣ))) v = x
    rw [MulEquiv.apply_symm_apply, Pi.mulSingle_eq_same]
  exact hleft.isEmbedding hproject
    (continuous_place_embedding (K := K) v)

/-- The literal assertion of Statement V.4.3: every canonical local map is
an embedding, hence is injective and carries the topology induced from the
idèle group back to the natural local topology. -/
def PlaceEmbeddingsTopological : Prop :=
  (∀ v : HeightOneSpectrum 𝓞K,
      IsEmbedding (finitePlaceEmbedding 𝓞K K v)) ∧
    (∀ v : InfinitePlace K,
      IsEmbedding (infinitePlaceEmbedding 𝓞K K v))

/-- Statement V.4.3. -/
theorem place_embeddings_topological :
    PlaceEmbeddingsTopological (K := K) :=
  ⟨embedding_finite_place,
    embedding_infinite_place⟩

end

end Towers.CField.Ideles
