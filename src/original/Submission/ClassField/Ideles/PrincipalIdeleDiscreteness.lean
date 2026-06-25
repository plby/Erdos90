import Submission.ClassField.Ideles.IdeleClassNorm
import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
import Mathlib.Topology.DiscreteSubset

/-!
# Chapter V, Section 4, Statement 4.2

The diagonal homomorphism `Kˣ → ℐ_K` is injective and has discrete image.
Injection is already `principalIdele_injective`.  For discreteness, this file
uses the source's neighborhood argument in a lattice form:

* requiring every finite coordinate to be a local unit is an open condition;
* such a principal idele comes from an algebraic integer; and
* the mixed embeddings of algebraic integers form a discrete lattice, so an
  algebraic integer sufficiently close to `1` at every infinite place is `1`.

The second bullet follows by translating completed local-unit membership to
a bound for every height-one valuation, then applying the characterization
of a Dedekind domain inside its fraction field by those valuation bounds.
-/

namespace Submission.CField.Ideles

open Filter IsDedekindDomain NumberField
open scoped RestrictedProduct nonZeroDivisors

noncomputable section

universe u

variable {K : Type u} [Field K] [NumberField K]

local notation "𝓞K" => NumberField.RingOfIntegers K

/-- The exact finite-place compatibility needed in the proof: a field
element whose diagonal image is a unit in every completed valuation ring is
an algebraic integer. -/
def PrincipalUnitIntegrality : Prop :=
  ∀ x : Kˣ,
    (∀ v : HeightOneSpectrum 𝓞K,
      (principalIdele 𝓞K K x).2.1 v ∈ IdeleUnitSubgroup 𝓞K K v) →
      IsIntegral ℤ (x : K)

private theorem integral_all_adic
    (x : Kˣ)
    (hx : ∀ v : HeightOneSpectrum 𝓞K,
      Units.map (algebraMap K (v.adicCompletion K)) x ∈
        (v.adicCompletionIntegers K).units) :
    IsIntegral ℤ (x : K) := by
  apply (IsIntegralClosure.isIntegral_iff (A := 𝓞K)).mpr
  apply IsDedekindDomain.HeightOneSpectrum.mem_integers_of_valuation_le_one K
  intro v
  have hv := hx v
  rw [IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one]
    at hv
  rw [show (((Units.map (algebraMap K (v.adicCompletion K)) x :
      (v.adicCompletion K)ˣ) : v.adicCompletion K)) =
      algebraMap K (v.adicCompletion K) (x : K) from rfl] at hv
  rw [← v.valuedAdicCompletion_eq_valuation' (x : K)]
  exact hv.le

/-- The finite-place compatibility follows from the valuation
characterization of a Dedekind domain inside its fraction field. -/
theorem principalUnitIntegrality :
    PrincipalUnitIntegrality (K := K) := by
  intro x hx
  apply integral_all_adic x
  intro v
  rw [← principal_idele_finite]
  exact hx v

/-- Literal combined assertion of Statement V.4.2. -/
def PrincipalEmbeddingDiscrete : Prop :=
  Function.Injective (principalIdele 𝓞K K) ∧
    DiscreteTopology (principalIdeles 𝓞K K)

omit [NumberField K] in
/-- The ring equivalence from infinite adeles to the mixed embedding space
is continuous. -/
theorem continuous_mixed_space :
    Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace K) := by
  change Continuous fun x : InfiniteAdeleRing K =>
    (fun (v : {w : InfinitePlace K // InfinitePlace.IsReal w}) =>
        InfinitePlace.Completion.extensionEmbeddingOfIsReal v.2 (x v),
      fun (v : {w : InfinitePlace K // InfinitePlace.IsComplex w}) =>
        InfinitePlace.Completion.extensionEmbedding v.1 (x v))
  apply Continuous.prodMk
  · exact continuous_pi fun v =>
      (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal v.2).continuous.comp
        (continuous_apply v.1)
  · exact continuous_pi fun v =>
      (InfinitePlace.Completion.isometry_extensionEmbedding v.1).continuous.comp
        (continuous_apply v.1)

/-- Read the infinite part of an idele in mixed-embedding coordinates. -/
def ideleInfiniteMixed (a : IdeleGroup 𝓞K K) : mixedEmbedding.mixedSpace K :=
  InfiniteAdeleRing.ringEquiv_mixedSpace K (a.1 : InfiniteAdeleRing K)

theorem continuous_infinite_mixed :
    Continuous (ideleInfiniteMixed (K := K)) := by
  apply continuous_mixed_space.comp
  exact Units.continuous_val.comp continuous_fst

/-- On a principal idele, the preceding map is the usual mixed embedding. -/
theorem idele_mixed_principal (x : Kˣ) :
    ideleInfiniteMixed (principalIdele 𝓞K K x) = mixedEmbedding K (x : K) := by
  rw [InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp]
  apply congrArg (InfiniteAdeleRing.ringEquiv_mixedSpace K)
  funext v
  rfl

private theorem idele_unit_open
    (v : HeightOneSpectrum 𝓞K) :
    IsOpen (IdeleUnitSubgroup 𝓞K K v : Set (v.adicCompletion K)ˣ) := by
  apply Submonoid.isOpen_units
  change IsOpen (v.adicCompletionIntegers K : Set (v.adicCompletion K))
  exact Valued.isOpen_valuationSubring _

/-- Requiring every finite coordinate to lie in its local unit subgroup is
open in the restricted-product topology. -/
theorem open_unit_locus :
    IsOpen {a : FiniteIdeles 𝓞K K |
      ∀ v, a.1 v ∈ IdeleUnitSubgroup 𝓞K K v} := by
  exact RestrictedProduct.isOpen_forall_mem
    (fun v => idele_unit_open (K := K) v)

omit [NumberField K] in
private theorem mixed_embedding_lattice
    {x : K} (hx : IsIntegral ℤ x) :
    mixedEmbedding K (x - 1) ∈ mixedEmbedding.integerLattice K := by
  obtain ⟨a : 𝓞K, ha⟩ :=
    (IsIntegralClosure.isIntegral_iff (A := 𝓞K)).mp hx
  change mixedEmbedding K (x - 1) ∈ LinearMap.range
    ((mixedEmbedding K).comp (algebraMap 𝓞K K)).toIntAlgHom.toLinearMap
  refine ⟨a - 1, ?_⟩
  change mixedEmbedding K (((a - 1 : 𝓞K) : K)) = mixedEmbedding K (x - 1)
  simp only [map_sub, map_one]
  rw [ha]

/-- All topological and archimedean steps of Statement V.4.2, conditional
only on the finite-unit/integrality adapter isolated above. -/
theorem ideles_discrete_integrality
    (hfinite : PrincipalUnitIntegrality (K := K)) :
    DiscreteTopology (principalIdeles 𝓞K K) := by
  let Λ := mixedEmbedding.integerLattice K
  have hΛdisc : DiscreteTopology Λ :=
    inferInstance
  obtain ⟨O, hOopen, hOΛ⟩ :=
    (discreteTopology_subtype_iff'.mp hΛdisc) 0 (zero_mem Λ)
  have hzeroO : (0 : mixedEmbedding.mixedSpace K) ∈ O := by
    have : (0 : mixedEmbedding.mixedSpace K) ∈ O ∩ (Λ : Set _) := by
      rw [hOΛ]
      simp
    exact this.1
  let Uinf : Set (IdeleGroup 𝓞K K) :=
    {a | ideleInfiniteMixed a - 1 ∈ O}
  have hUinfOpen : IsOpen Uinf := by
    exact hOopen.preimage
      (continuous_infinite_mixed.sub continuous_const)
  let Uf : Set (IdeleGroup 𝓞K K) :=
    {a | ∀ v, a.2.1 v ∈ IdeleUnitSubgroup 𝓞K K v}
  have hUfopen : IsOpen Uf := by
    exact open_unit_locus.preimage continuous_snd
  let U : Set (IdeleGroup 𝓞K K) := Uinf ∩ Uf
  have hUopen : IsOpen U := hUinfOpen.inter hUfopen
  rw [discreteTopology_iff_isOpen_singleton_one, isOpen_induced_iff]
  refine ⟨U, hUopen, ?_⟩
  ext y
  constructor
  · intro hy
    rcases y.property with ⟨x, hx⟩
    have hyInf : ideleInfiniteMixed (y : IdeleGroup 𝓞K K) - 1 ∈ O := hy.1
    have hyf : ∀ v, (y : IdeleGroup 𝓞K K).2.1 v ∈
        IdeleUnitSubgroup 𝓞K K v := hy.2
    have hxint : IsIntegral ℤ (x : K) := by
      apply hfinite x
      simpa [← hx] using hyf
    have hxO : mixedEmbedding K ((x : K) - 1) ∈ O := by
      rw [← hx] at hyInf
      rw [idele_mixed_principal] at hyInf
      simpa only [map_sub, map_one] using hyInf
    have hxΛ : mixedEmbedding K ((x : K) - 1) ∈ Λ :=
      mixed_embedding_lattice hxint
    have hxzero : mixedEmbedding K ((x : K) - 1) = 0 := by
      have hxmem : mixedEmbedding K ((x : K) - 1) ∈ O ∩ (Λ : Set _) :=
        ⟨hxO, hxΛ⟩
      rw [hOΛ] at hxmem
      exact Set.mem_singleton_iff.mp hxmem
    have hxone : x = 1 := by
      apply Units.ext
      apply sub_eq_zero.mp
      apply mixedEmbedding_injective K
      simpa using hxzero
    apply Subtype.ext
    simp [← hx, hxone]
  · intro hy
    have hyone : y = 1 := Set.mem_singleton_iff.mp hy
    subst y
    constructor
    · change ideleInfiniteMixed (1 : IdeleGroup 𝓞K K) - 1 ∈ O
      change InfiniteAdeleRing.ringEquiv_mixedSpace K
          (((1 : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K)) - 1 ∈ O
      rw [show (((1 : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K)) = 1 from rfl,
        map_one, sub_self]
      exact hzeroO
    · intro v
      exact (IdeleUnitSubgroup 𝓞K K v).one_mem

/-- Combined source assertion from the one concrete finite-place adapter. -/
theorem principal_discrete_integrality
    (hfinite : PrincipalUnitIntegrality (K := K)) :
    PrincipalEmbeddingDiscrete (K := K) :=
  ⟨principalIdele_injective 𝓞K K,
    ideles_discrete_integrality hfinite⟩

/-- The subgroup of principal ideles has the discrete topology. -/
theorem principalIdeles_discrete :
    DiscreteTopology (principalIdeles 𝓞K K) :=
  ideles_discrete_integrality
    principalUnitIntegrality

/-- **Statement V.4.2.** The diagonal map is injective and its image is
discrete. -/
theorem principalEmbeddingDiscrete : PrincipalEmbeddingDiscrete (K := K) :=
  ⟨principalIdele_injective 𝓞K K, principalIdeles_discrete⟩

end

end Submission.CField.Ideles
