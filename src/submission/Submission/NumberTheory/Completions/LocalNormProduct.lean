import Submission.NumberTheory.Completions.NormalizedExtension
import Submission.NumberTheory.Completions.CompletionNormTrace


/-!
# Milne, Chapter 8, Proposition 8.7: the local norm product

For the finite extensions of a completed local field occurring in the
completion decomposition, the product of their normalized values is the
absolute value of the product of their field norms.  Combining this with the
norm decomposition of Corollary 8.4 gives Milne's Proposition 8.7.

The final theorems use the place-indexed completion decomposition of
Proposition 8.2.  The nonarchimedean argument uses the actual completions,
while the archimedean argument groups the complex embeddings above a fixed
infinite place, including the conjugate pair belonging to a complex place
above a real one.
-/

namespace Submission.NumberTheory.Milne

open Module
open scoped TensorProduct

attribute [local instance] Algebra.TensorProduct.rightAlgebra

noncomputable section

universe u

variable {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K]
  [CompleteSpace K]
variable {ι : Type u} [Fintype ι]
variable (Li : ι → Type u) [∀ i, Field (Li i)] [∀ i, Algebra K (Li i)]
  [∀ i, Algebra.IsAlgebraic K (Li i)] [∀ i, FiniteDimensional K (Li i)]

/-- The local calculation in Milne's Proposition 8.7: over a finite family of
finite extensions of a complete nonarchimedean field, the product of the
normalized extension values is the norm of the product of the local field
norms. -/
theorem prod_normalized_algebra
    (x : ∀ i, Li i) :
    (∏ i, normalizedExtensionValue K (Li i) (x i)) =
      ‖∏ i, Algebra.norm K (x i)‖ := by
  rw [norm_prod]
  apply Finset.prod_congr rfl
  intro i _
  exact normalized_extension_norm K (Li i) (x i)

variable {A : Type u} [CommRing A] [Algebra K A] [Module.Free K A]
  [Module.Finite K A]

omit [Free K A] [Module.Finite K A] in
/-- Milne's Proposition 8.7 after choosing the completion factors above the
fixed place.  The hypothesis is exactly the norm decomposition supplied by
Corollary 8.4; the conclusion is the product of normalized local values. -/
theorem normalized_extension_algebra
    (α : A) (localImage : ∀ i, Li i)
    (hnorm : Algebra.norm K α = ∏ i, Algebra.norm K (localImage i)) :
    (∏ i, normalizedExtensionValue K (Li i) (localImage i)) =
      ‖Algebra.norm K α‖ := by
  rw [prod_normalized_algebra Li]
  exact congrArg norm hnorm.symm

omit [Free K A] [Module.Finite K A] in
/-- Milne's Proposition 8.7 for a specified finite decomposition into the
completion factors above one place.  Corollary 8.4 is built into the proof via
the finite-product algebra norm formula. -/
theorem prod_normalized_alg
    (e : A ≃ₐ[K] (∀ i, Li i)) (α : A) :
    (∏ i, normalizedExtensionValue K (Li i) (e α i)) =
      ‖Algebra.norm K α‖ := by
  apply normalized_extension_algebra Li α (e α)
  rw [← Algebra.norm_eq_of_algEquiv e α, algebraNorm_pi Li]

section CompletionFactors

variable {F E : Type u} [Field F] [Field E] [Algebra F E]
  (v : AbsoluteValue F ℝ) [IsUltrametricDist v.Completion]

private noncomputable local instance completionNontriviallyNormedField
    [Fact v.IsNontrivial] :
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

set_option backward.isDefEq.respectTransparency false in
local instance localNormProductCompletionBaseAlgebra : Algebra F v.Completion :=
  UniformSpace.Completion.algebra (WithAbs v) F

local instance localNormProductCompletionBaseSMul : SMul F v.Completion :=
  (localNormProductCompletionBaseAlgebra v).toSMul

local instance localNormProductCompletionBaseModule : Module F v.Completion :=
  Algebra.toModule

set_option backward.isDefEq.respectTransparency false in
local instance localNormProductCompletionPlaceAlgebra
    (w : {w : AbsoluteValue E ℝ // AbsoluteValue.LiesOver w v}) :
    Algebra v.Completion w.1.Completion :=
  (completionLies v w.1 w.2).toAlgebra

local instance localNormProductCompletionPlaceSMul
    (w : {w : AbsoluteValue E ℝ // AbsoluteValue.LiesOver w v}) :
    SMul v.Completion w.1.Completion :=
  (localNormProductCompletionPlaceAlgebra v w).toSMul

local instance localNormProductCompletionPlaceModule
    (w : {w : AbsoluteValue E ℝ // AbsoluteValue.LiesOver w v}) :
    Module v.Completion w.1.Completion :=
  Algebra.toModule

local instance extensionsFinite
    [FiniteDimensional F E] [Algebra.IsSeparable F E] [Fact v.IsNontrivial] :
    Finite {w : AbsoluteValue E ℝ // AbsoluteValue.LiesOver w v} :=
  absolute_extensions_separable v

noncomputable local instance extensionsFintype
    [FiniteDimensional F E] [Algebra.IsSeparable F E] [Fact v.IsNontrivial] :
    Fintype {w : AbsoluteValue E ℝ // AbsoluteValue.LiesOver w v} :=
  Fintype.ofFinite _

local instance completionTensorFinite [FiniteDimensional F E] :
    Module.Finite v.Completion (E ⊗[F] v.Completion) := by
  letI : Module.Finite v.Completion (v.Completion ⊗[F] E) :=
    Module.Finite.base_change F v.Completion E
  exact Module.Finite.equiv
    (Algebra.TensorProduct.commRight F v.Completion E).toLinearEquiv

local instance completionPlaceFinite
    [FiniteDimensional F E] [Fact v.IsNontrivial]
    (w : {w : AbsoluteValue E ℝ // AbsoluteValue.LiesOver w v}) :
    Module.Finite v.Completion w.1.Completion :=
  Module.Finite.of_surjective
    (completionTensorPlace v w).toLinearMap
    (completions_component_surjective v w)

local instance completionPlaceIsAlgebraic
    [FiniteDimensional F E] [Fact v.IsNontrivial]
    (w : {w : AbsoluteValue E ℝ // AbsoluteValue.LiesOver w v}) :
    Algebra.IsAlgebraic v.Completion w.1.Completion :=
  Algebra.IsAlgebraic.of_finite v.Completion w.1.Completion

local instance completionPlaceFree
    (w : {w : AbsoluteValue E ℝ // AbsoluteValue.LiesOver w v}) :
    Module.Free v.Completion w.1.Completion :=
  Module.Free.of_divisionRing v.Completion w.1.Completion

/-- The canonical extended absolute value on a completion factor is its
existing norm. -/
private theorem complete_extension_absolute
    [FiniteDimensional F E] [Fact v.IsNontrivial]
    (w : {w : AbsoluteValue E ℝ // AbsoluteValue.LiesOver w v}) :
    completeAbsoluteValue v.Completion w.1.Completion =
      NormedField.toAbsoluteValue w.1.Completion := by
  symm
  apply complete_absolute_unique
  intro x
  change ‖completionLies v w.1 w.2 x‖ = ‖x‖
  simpa only [dist_zero_right, map_zero] using
    (completion_lies_isometry v w.1 w.2).dist_eq x 0

/-- On the image of `E`, the normalized value of a completion factor is the
corresponding extension of `v`, raised to the local degree. -/
private theorem normalized_extension_embedding
    [FiniteDimensional F E] [Fact v.IsNontrivial]
    (w : {w : AbsoluteValue E ℝ // AbsoluteValue.LiesOver w v}) (x : E) :
    normalizedExtensionValue v.Completion w.1.Completion
        (completionEmbedding w.1 x) =
      w.1 x ^ finrank v.Completion w.1.Completion := by
  change completeAbsoluteValue v.Completion w.1.Completion
      (completionEmbedding w.1 x) ^ finrank v.Completion w.1.Completion = _
  rw [complete_extension_absolute v w]
  exact congrArg (· ^ finrank v.Completion w.1.Completion)
    (norm_completionEmbedding w.1 x)

/-- The completion-valued form of Milne's Proposition 8.7: the product of
the normalized values in every completion above `v` equals the value at `v`
of the global field norm. -/
theorem prod_normalized_completions
    [FiniteDimensional F E] [Algebra.IsSeparable F E] [Fact v.IsNontrivial]
    (x : E) :
    (∏ w : {w : AbsoluteValue E ℝ // AbsoluteValue.LiesOver w v},
        normalizedExtensionValue v.Completion w.1.Completion
          (completionEmbedding w.1 x)) =
      v (Algebra.norm F x) := by
  rw [show v (Algebra.norm F x) =
      ‖completionEmbedding v (Algebra.norm F x)‖ by
        rw [norm_completionEmbedding]]
  rw [show completionEmbedding v (Algebra.norm F x) =
      algebraMap F v.Completion (Algebra.norm F x) by rfl]
  rw [(completion_norm_trace v x).1, norm_prod]
  apply Finset.prod_congr rfl
  intro w _
  exact normalized_extension_norm
    v.Completion w.1.Completion (completionEmbedding w.1 x)

/-- Milne's Proposition 8.7 for a nonarchimedean place: the product of the
normalized values over all extensions of `v` equals the value at `v` of the
global field norm. -/
theorem prod_finrank_norm
    [FiniteDimensional F E] [Algebra.IsSeparable F E] [Fact v.IsNontrivial]
    (x : E) :
    (∏ w : {w : AbsoluteValue E ℝ // AbsoluteValue.LiesOver w v},
        w.1 x ^ finrank v.Completion w.1.Completion) =
      v (Algebra.norm F x) := by
  calc
    (∏ w : {w : AbsoluteValue E ℝ // AbsoluteValue.LiesOver w v},
        w.1 x ^ finrank v.Completion w.1.Completion) =
        ∏ w : {w : AbsoluteValue E ℝ // AbsoluteValue.LiesOver w v},
          normalizedExtensionValue v.Completion w.1.Completion
            (completionEmbedding w.1 x) := by
      apply Finset.prod_congr rfl
      intro w _
      exact (normalized_extension_embedding v w x).symm
    _ = v (Algebra.norm F x) :=
      prod_normalized_completions v x

end CompletionFactors

section InfinitePlaces

open NumberField

variable {F E : Type u} [Field F] [Field E] [Algebra F E]
  [NumberField F] [NumberField E] [FiniteDimensional F E]
  [Algebra.IsSeparable F E]

/-- Algebra homomorphisms into `ℂ`, when `ℂ` is made an `F`-algebra by
an infinite-place embedding, are the corresponding extensions of that
embedding as ring homomorphisms. -/
private noncomputable def complexEmbeddingExtension
    (v : InfinitePlace F) :
    letI : Algebra F ℂ := v.embedding.toAlgebra
    (E →ₐ[F] ℂ) ≃
      ComplexEmbeddingExtension (K := F) (L := E) v.embedding :=
  by
    letI : Algebra F ℂ := v.embedding.toAlgebra
    exact
      { toFun := fun f => ⟨f.toRingHom, by
      ext x
      exact f.commutes x⟩
        invFun := fun f =>
          { toRingHom := f.1
            commutes' := fun x => RingHom.congr_fun f.2 x }
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }

open Classical in
omit [NumberField F] in
/-- Applying an infinite place to a field norm gives the product of the
ordinary complex norms over the extensions of its chosen embedding. -/
private theorem complex_embedding_extensions
    (v : InfinitePlace F) (x : E) :
    v (Algebra.norm F x) =
      ∏ f : ComplexEmbeddingExtension (K := F) (L := E) v.embedding,
        ‖f.1 x‖ := by
  letI : Algebra F ℂ := v.embedding.toAlgebra
  have h := congrArg norm (Algebra.norm_eq_prod_embeddings F ℂ x)
  rw [norm_prod] at h
  change v (Algebra.norm F x) = _
  rw [show v (Algebra.norm F x) =
      ‖v.embedding (Algebra.norm F x)‖ by
    exact (v.norm_embedding_eq _).symm]
  change ‖algebraMap F ℂ (Algebra.norm F x)‖ = _
  rw [h]
  exact Fintype.prod_equiv (complexEmbeddingExtension v)
    (fun f : E →ₐ[F] ℂ => ‖f x‖)
    (fun f : ComplexEmbeddingExtension (K := F) (L := E) v.embedding =>
      ‖f.1 x‖) (fun _ => rfl)

open Classical in
omit [NumberField F] in
/-- The complex-base case of the archimedean local norm product. -/
private theorem prod_normalized_complex
    (v : InfinitePlace F) (hv : v.IsComplex) (x : E) :
    (∏ w : {w : InfinitePlace E // w.comap (algebraMap F E) = v},
        w.1 x ^ w.1.mult) =
      v (Algebra.norm F x) ^ v.mult := by
  let W := {w : InfinitePlace E // w.comap (algebraMap F E) = v}
  let X := ComplexEmbeddingExtension (K := F) (L := E) v.embedding
  let e : X ≃ W :=
    complexExtensionsAbove v hv
  have hwComplex (w : W) : w.1.IsComplex := by
    letI : AbsoluteValue.LiesOver w.1.1 v.1 :=
      infinite_lies_comap v w.1 w.2
    exact InfinitePlace.LiesOver.isComplex_of_isComplex_under w.1 hv
  have hprod : (∏ f : X, ‖f.1 x‖) = ∏ w : W, w.1 x := by
    exact Fintype.prod_equiv e (fun f : X => ‖f.1 x‖)
      (fun w : W => w.1 x) (fun f => by
        change ‖f.1 x‖ = (InfinitePlace.mk f.1) x
        rfl)
  have hvMult : v.mult = 2 := InfinitePlace.mult_isComplex ⟨v, hv⟩
  have hwMult (w : W) : w.1.mult = 2 :=
    InfinitePlace.mult_isComplex ⟨w.1, hwComplex w⟩
  calc
    (∏ w : W, w.1 x ^ w.1.mult) = ∏ w : W, w.1 x ^ 2 := by
      apply Finset.prod_congr rfl
      intro w _
      rw [hwMult w]
    _ = (∏ w : W, w.1 x) ^ 2 := by rw [Finset.prod_pow]
    _ = (∏ f : X, ‖f.1 x‖) ^ 2 := by rw [hprod]
    _ = v (Algebra.norm F x) ^ 2 := by
      rw [complex_embedding_extensions v x]
    _ = v (Algebra.norm F x) ^ v.mult := by rw [hvMult]

open Classical in
omit [NumberField F] in
/-- The real-base case of the archimedean local norm product.  The fiber of
the embedding-to-place map has cardinality `1` at a real place and `2` at a
complex place, exactly its infinite-place multiplicity. -/
private theorem prod_normalized_real
    (v : InfinitePlace F) (hv : v.IsReal) (x : E) :
    (∏ w : {w : InfinitePlace E // w.comap (algebraMap F E) = v},
        w.1 x ^ w.1.mult) =
      v (Algebra.norm F x) ^ v.mult := by
  let W := {w : InfinitePlace E // w.comap (algebraMap F E) = v}
  let X := ComplexEmbeddingExtension (K := F) (L := E) v.embedding
  let toPlace : X → W := fun f =>
    ⟨InfinitePlace.mk f.1, by
      rw [InfinitePlace.comap_mk, f.2, InfinitePlace.mk_embedding]⟩
  have hfiberCard (w : W) :
      Fintype.card {f : X // toPlace f = w} = w.1.mult := by
    let ef : {f : X // toPlace f = w} ≃
        {phi : E →+* ℂ // InfinitePlace.mk phi = w.1} :=
      { toFun := fun f => ⟨f.1.1, congrArg Subtype.val f.2⟩
        invFun := fun phi => by
          have hplace : InfinitePlace.mk
              (phi.1.comp (algebraMap F E)) = v := by
            calc
              InfinitePlace.mk (phi.1.comp (algebraMap F E)) =
                  (InfinitePlace.mk phi.1).comap (algebraMap F E) := rfl
              _ = w.1.comap (algebraMap F E) := by rw [phi.2]
              _ = v := w.2
          have hplaceReal : (InfinitePlace.mk
              (phi.1.comp (algebraMap F E))).IsReal := by
            rw [hplace]
            exact hv
          have hreal : ComplexEmbedding.IsReal
              (phi.1.comp (algebraMap F E)) :=
            InfinitePlace.isReal_mk_iff.mp hplaceReal
          have hover : phi.1.comp (algebraMap F E) = v.embedding := by
            calc
              phi.1.comp (algebraMap F E) =
                  (InfinitePlace.mk
                    (phi.1.comp (algebraMap F E))).embedding :=
                (InfinitePlace.embedding_mk_eq_of_isReal hreal).symm
              _ = v.embedding := congrArg InfinitePlace.embedding hplace
          refine ⟨⟨phi.1, hover⟩, ?_⟩
          apply Subtype.ext
          exact phi.2
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    calc
      Fintype.card {f : X // toPlace f = w} =
          Fintype.card {phi : E →+* ℂ // InfinitePlace.mk phi = w.1} :=
        Fintype.card_congr ef
      _ = w.1.mult := by
        rw [Fintype.card_subtype]
        exact InfinitePlace.card_filter_mk_eq w.1
  have hprod : (∏ f : X, ‖f.1 x‖) =
      ∏ w : W, w.1 x ^ w.1.mult := by
    rw [← Fintype.prod_fiberwise toPlace (fun f : X => ‖f.1 x‖)]
    apply Finset.prod_congr rfl
    intro w _
    have hfiberValue (f : {f : X // toPlace f = w}) :
        ‖f.1.1 x‖ = w.1 x := by
      change (InfinitePlace.mk f.1.1) x = w.1 x
      have hplace := congrArg Subtype.val f.2
      change InfinitePlace.mk f.1.1 = w.1 at hplace
      exact congrArg (fun z : InfinitePlace E => z x) hplace
    simp_rw [hfiberValue]
    rw [Finset.prod_const, Finset.card_univ, hfiberCard]
  have hvMult : v.mult = 1 := InfinitePlace.mult_isReal ⟨v, hv⟩
  calc
    (∏ w : W, w.1 x ^ w.1.mult) = ∏ f : X, ‖f.1 x‖ := hprod.symm
    _ = v (Algebra.norm F x) :=
      (complex_embedding_extensions v x).symm
    _ = v (Algebra.norm F x) ^ v.mult := by rw [hvMult, pow_one]

open Classical in
omit [NumberField F] in
/-- Milne, Proposition 8.7 at an infinite place: the product of the
normalized values over all infinite places above `v` is the normalized value
at `v` of the global field norm. -/
theorem prod_infinite_normalized
    (v : InfinitePlace F) (x : E) :
    (∏ w : {w : InfinitePlace E // w.comap (algebraMap F E) = v},
        w.1 x ^ w.1.mult) =
      v (Algebra.norm F x) ^ v.mult := by
  rcases v.isReal_or_isComplex with hv | hv
  · exact prod_normalized_real v hv x
  · exact prod_normalized_complex v hv x

end InfinitePlaces

end

end Submission.NumberTheory.Milne
