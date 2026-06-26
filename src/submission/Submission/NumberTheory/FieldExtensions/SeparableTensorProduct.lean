import Mathlib

/-!
# Milne, Algebraic Number Theory, Theorem 1.18

A finite separable field extension remains, after arbitrary scalar extension, a finite product
of finite separable field extensions.
-/

namespace Submission.NumberTheory.Milne

open scoped Matrix TensorProduct

universe u

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- If `K / k` is finite and separable and `Ω / k` is any field extension, then
`K ⊗[k] Ω` is a finite product of finite separable extensions of `Ω`.
This is the main assertion of Theorem 1.18. -/
theorem tensor_pi_separable
    (k K Ω : Type u) [Field k] [Field K] [Field Ω]
    [Algebra k K] [Algebra k Ω] [FiniteDimensional k K]
    [Algebra.IsSeparable k K] :
    ∃ (ι : Type u) (_ : Finite ι) (Ωi : ι → Type u)
      (_ : ∀ i, Field (Ωi i)) (_ : ∀ i, Algebra Ω (Ωi i))
      (_ : (K ⊗[k] Ω) ≃ₐ[Ω] ((i : ι) → Ωi i)),
      ∀ i, Module.Finite Ω (Ωi i) ∧ Algebra.IsSeparable Ω (Ωi i) := by
  letI : Algebra.Etale k K :=
    { formallyEtale := Algebra.FormallyEtale.of_isSeparable k K
      finitePresentation := Algebra.FinitePresentation.of_finiteType.mp inferInstance }
  rcases (Algebra.Etale.iff_exists_algEquiv_prod Ω (Ω ⊗[k] K)).mp inferInstance with
    ⟨ι, hι, Ωi, hfield, halgebra, e, hfinite⟩
  exact ⟨ι, hι, Ωi, hfield, halgebra,
    (Algebra.TensorProduct.commRight k Ω K).symm.trans e, hfinite⟩

/-- If `α` generates `K / k`, then its image generates each field factor after scalar extension.
This is the primitive-element assertion in Theorem 1.18. -/
theorem pi_primitive_element
    (k K Ω : Type u) [Field k] [Field K] [Field Ω]
    [Algebra k K] [Algebra k Ω] [FiniteDimensional k K]
    [Algebra.IsSeparable k K] (α : K) (hα : Algebra.adjoin k {α} = ⊤) :
    ∃ (ι : Type u) (_ : Finite ι) (Ωi : ι → Type u)
      (_ : ∀ i, Field (Ωi i)) (_ : ∀ i, Algebra Ω (Ωi i))
      (e : (Ω ⊗[k] K) ≃ₐ[Ω] ((i : ι) → Ωi i)),
      (∀ i, Algebra.adjoin Ω {e ((1 : Ω) ⊗ₜ[k] α) i} = ⊤) ∧
      ∀ i, Module.Finite Ω (Ωi i) ∧ Algebra.IsSeparable Ω (Ωi i) := by
  rcases tensor_pi_separable k K Ω with
    ⟨ι, hι, Ωi, hfield, halgebra, e, hfinite⟩
  let e' : (Ω ⊗[k] K) ≃ₐ[Ω] ((i : ι) → Ωi i) :=
    (Algebra.TensorProduct.commRight k Ω K).trans e
  refine ⟨ι, hι, Ωi, hfield, halgebra, e', ?_, hfinite⟩
  intro i
  let φ : Ω ⊗[k] K →ₐ[Ω] Ωi i :=
    (Pi.evalAlgHom Ω (fun i ↦ Ωi i) i).comp e'.toAlgHom
  have hφ : Function.Surjective φ :=
    (Function.surjective_eval i).comp e'.surjective
  have hgen :
      Algebra.adjoin Ω ({(1 : Ω) ⊗ₜ[k] α} : Set (Ω ⊗[k] K)) = ⊤ := by
    simpa using
      Algebra.TensorProduct.adjoin_one_tmul_image_eq_top (A := Ω) ({α} : Set K) hα
  change Algebra.adjoin Ω {φ ((1 : Ω) ⊗ₜ[k] α)} = ⊤
  calc
    Algebra.adjoin Ω {φ ((1 : Ω) ⊗ₜ[k] α)} =
        (Algebra.adjoin Ω ({(1 : Ω) ⊗ₜ[k] α} : Set (Ω ⊗[k] K))).map φ := by
          rw [AlgHom.map_adjoin]
          simp
    _ = (⊤ : Subalgebra Ω (Ω ⊗[k] K)).map φ := by rw [hgen]
    _ = ⊤ := by
      rw [Algebra.map_top, (AlgHom.range_eq_top φ).2 hφ]

private theorem pairwise_coprime_minpoly
    (Ω : Type*) [Field Ω] (ι : Type*)
    (L : ι → Type*) [∀ i, Field (L i)] [∀ i, Algebra Ω (L i)]
    [∀ i, FiniteDimensional Ω (L i)] (β : ∀ i, L i)
    (hβ : Algebra.adjoin Ω {β} = ⊤) :
    Pairwise (Function.onFun IsCoprime fun i => minpoly Ω (β i)) := by
  classical
  intro i j hij
  have he : (Pi.single j (1 : L j) : ∀ i, L i) ∈ Algebra.adjoin Ω {β} := by
    rw [hβ]
    trivial
  rw [Algebra.adjoin_singleton_eq_range_aeval] at he
  obtain ⟨p, hp⟩ := he
  have hpi : Polynomial.aeval (β i) p = 0 := by
    have h := congr_fun hp i
    change Polynomial.aeval β p i = Pi.single j 1 i at h
    rw [Polynomial.aeval_pi_apply₂] at h
    simpa [Pi.single_eq_of_ne hij] using h
  have hpj : Polynomial.aeval (β j) (p - 1) = 0 := by
    have h := congr_fun hp j
    change Polynomial.aeval β p j = Pi.single j 1 j at h
    rw [Polynomial.aeval_pi_apply₂] at h
    simpa using congr_arg (fun x : L j => x - 1) h
  obtain ⟨a, ha⟩ := minpoly.dvd Ω (β i) hpi
  obtain ⟨b, hb⟩ := minpoly.dvd Ω (β j) hpj
  refine ⟨a, -b, ?_⟩
  rw [mul_comm a, ← ha, neg_mul, mul_comm b, ← hb]
  ring

/-- In a product decomposition of scalar extension, the mapped minimal polynomial of a primitive
element is the product of the minimal polynomials of its coordinate images. This is the final
assertion of Theorem 1.18. -/
theorem minpoly_tensor_pi
    (k K Ω : Type*) [Field k] [Field K] [Field Ω]
    [Algebra k K] [Algebra k Ω] [FiniteDimensional k K]
    (α : K) (hα : Algebra.adjoin k {α} = ⊤)
    (ι : Type*) [Fintype ι] (L : ι → Type*)
    [∀ i, Field (L i)] [∀ i, Algebra Ω (L i)]
    [∀ i, FiniteDimensional Ω (L i)]
    (e : (Ω ⊗[k] K) ≃ₐ[Ω] ((i : ι) → L i)) :
    (minpoly k α).map (algebraMap k Ω) =
      ∏ i, minpoly Ω (e ((1 : Ω) ⊗ₜ[k] α) i) := by
  classical
  let β : ∀ i, L i := e ((1 : Ω) ⊗ₜ[k] α)
  have hgen : Algebra.adjoin Ω ({(1 : Ω) ⊗ₜ[k] α} : Set (Ω ⊗[k] K)) = ⊤ := by
    simpa using
      Algebra.TensorProduct.adjoin_one_tmul_image_eq_top (A := Ω) ({α} : Set K) hα
  have hβ : Algebra.adjoin Ω {β} = ⊤ := by
    calc
      Algebra.adjoin Ω {β} =
          (Algebra.adjoin Ω ({(1 : Ω) ⊗ₜ[k] α} : Set (Ω ⊗[k] K))).map
            e.toAlgHom := by
        rw [AlgHom.map_adjoin]
        simp [β]
      _ = (⊤ : Subalgebra Ω (Ω ⊗[k] K)).map e.toAlgHom := by rw [hgen]
      _ = ⊤ := by
        rw [Algebra.map_top, (AlgHom.range_eq_top e.toAlgHom).2 e.surjective]
  have hcop : Pairwise (Function.onFun IsCoprime fun i => minpoly Ω (β i)) :=
    pairwise_coprime_minpoly Ω ι L β hβ
  have hroot : Polynomial.aeval β ((minpoly k α).map (algebraMap k Ω)) = 0 := by
    change Polynomial.aeval (e.toAlgHom ((1 : Ω) ⊗ₜ[k] α))
      ((minpoly k α).map (algebraMap k Ω)) = 0
    rw [Polynomial.aeval_algHom_apply e.toAlgHom]
    rw [Polynomial.aeval_map_algebraMap]
    change e (Polynomial.aeval
      ((Algebra.TensorProduct.includeRight : K →ₐ[k] Ω ⊗[k] K) α)
      (minpoly k α)) = 0
    rw [Polynomial.aeval_algHom_apply, minpoly.aeval, map_zero, map_zero]
  have hdvd_each (i : ι) :
      minpoly Ω (β i) ∣ (minpoly k α).map (algebraMap k Ω) := by
    apply minpoly.dvd Ω (β i)
    have h := congr_fun hroot i
    rwa [Polynomial.aeval_pi_apply₂] at h
  have hdvd : (∏ i, minpoly Ω (β i)) ∣
      (minpoly k α).map (algebraMap k Ω) :=
    Fintype.prod_dvd_of_coprime hcop hdvd_each
  have hdeg_f : ((minpoly k α).map (algebraMap k Ω)).natDegree =
      Module.finrank k K := by
    have hα' : IntermediateField.adjoin k {α} = ⊤ := by
      apply IntermediateField.toSubalgebra_injective
      rw [IntermediateField.adjoin_toSubalgebra_of_isAlgebraic
        (fun x _ => IsAlgebraic.of_finite k x), IntermediateField.top_toSubalgebra]
      exact hα
    rw [(minpoly.monic (Algebra.IsIntegral.isIntegral α)).natDegree_map,
      ← Field.primitive_element_iff_minpoly_natDegree_eq k α]
    exact hα'
  have hdeg_prod : (∏ i, minpoly Ω (β i)).natDegree =
      Module.finrank k K := by
    have hcoord (i : ι) : Algebra.adjoin Ω {β i} = ⊤ := by
      let φ : (∀ j, L j) →ₐ[Ω] L i := Pi.evalAlgHom Ω L i
      change Algebra.adjoin Ω {φ β} = ⊤
      calc
        Algebra.adjoin Ω {φ β} = (Algebra.adjoin Ω {β}).map φ := by
          rw [AlgHom.map_adjoin]
          simp
        _ = (⊤ : Subalgebra Ω (∀ j, L j)).map φ := by rw [hβ]
        _ = ⊤ := by
          rw [Algebra.map_top, (AlgHom.range_eq_top φ).2 (Function.surjective_eval i)]
    have hminpoly_degree (i : ι) :
        (minpoly Ω (β i)).natDegree = Module.finrank Ω (L i) := by
      apply (Field.primitive_element_iff_minpoly_natDegree_eq Ω (β i)).mp
      apply IntermediateField.toSubalgebra_injective
      rw [IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic
        (IsAlgebraic.of_finite Ω (β i)), IntermediateField.top_toSubalgebra]
      exact hcoord i
    rw [Polynomial.natDegree_prod_of_monic (s := Finset.univ)
      (f := fun i => minpoly Ω (β i))
      (fun i _ => minpoly.monic (Algebra.IsIntegral.isIntegral (β i)))]
    simp_rw [hminpoly_degree]
    rw [← Module.finrank_pi_fintype Ω]
    calc
      Module.finrank Ω (∀ i, L i) = Module.finrank Ω (Ω ⊗[k] K) :=
        e.toLinearEquiv.finrank_eq.symm
      _ = Module.finrank k K := Module.finrank_baseChange
  apply Polynomial.eq_of_monic_of_dvd_of_natDegree_le
    (Polynomial.monic_prod_of_monic _ _
      fun i _ => minpoly.monic (Algebra.IsIntegral.isIntegral (β i)))
    ((minpoly.monic (Algebra.IsIntegral.isIntegral α)).map (algebraMap k Ω))
    hdvd
  rw [hdeg_f, hdeg_prod]

/-- The full primitive-element form of Theorem 1.18, including the factorization of the mapped
minimal polynomial into the coordinate minimal polynomials. -/
theorem pi_primitive_minpoly
    (k K Ω : Type u) [Field k] [Field K] [Field Ω]
    [Algebra k K] [Algebra k Ω] [FiniteDimensional k K]
    [Algebra.IsSeparable k K] (α : K) (hα : Algebra.adjoin k {α} = ⊤) :
    ∃ (ι : Type u) (_ : Fintype ι) (Ωi : ι → Type u)
      (_ : ∀ i, Field (Ωi i)) (_ : ∀ i, Algebra Ω (Ωi i))
      (e : (Ω ⊗[k] K) ≃ₐ[Ω] ((i : ι) → Ωi i)),
      (∀ i, Algebra.adjoin Ω {e ((1 : Ω) ⊗ₜ[k] α) i} = ⊤) ∧
      (minpoly k α).map (algebraMap k Ω) =
        ∏ i, minpoly Ω (e ((1 : Ω) ⊗ₜ[k] α) i) ∧
      ∀ i, Module.Finite Ω (Ωi i) ∧ Algebra.IsSeparable Ω (Ωi i) := by
  classical
  rcases pi_primitive_element k K Ω α hα with
    ⟨ι, hι, Ωi, hfield, halgebra, e, hgen, hfinite⟩
  letI : Fintype ι := Fintype.ofFinite ι
  letI (i : ι) : Module.Finite Ω (Ωi i) := (hfinite i).1
  refine ⟨ι, inferInstance, Ωi, hfield, halgebra, e, hgen, ?_, hfinite⟩
  exact minpoly_tensor_pi k K Ω α hα ι Ωi e

/-- For a finite extension `K / ℚ`, complex scalar extension is a product of one copy of `ℂ`
for every dimension of `K` over `ℚ`. This is the algebra decomposition in Example 1.19. -/
theorem complex_tensor_pi
    (K : Type) [Field K] [Algebra ℚ K] [FiniteDimensional ℚ K] :
    Nonempty ((K ⊗[ℚ] ℂ) ≃ₐ[ℂ] (Fin (Module.finrank ℚ K) → ℂ)) := by
  rcases tensor_pi_separable ℚ K ℂ with
    ⟨ι, hι, Ki, hfield, halgebra, e, hfinite⟩
  letI : Fintype ι := Fintype.ofFinite ι
  let factorEquiv (i : ι) : Ki i ≃ₐ[ℂ] ℂ := by
    letI : Module.Finite ℂ (Ki i) := (hfinite i).1
    exact (AlgEquiv.ofBijective (Algebra.ofId ℂ (Ki i))
      IsAlgClosed.algebraMap_bijective_of_isIntegral).symm
  let eℂ : (K ⊗[ℚ] ℂ) ≃ₐ[ℂ] (ι → ℂ) :=
    e.trans (AlgEquiv.piCongrRight factorEquiv)
  have hcard : Fintype.card ι = Module.finrank ℚ K := by
    calc
      Fintype.card ι = Module.finrank ℂ (ι → ℂ) :=
        (Module.finrank_fintype_fun_eq_card ℂ).symm
      _ = Module.finrank ℂ (K ⊗[ℚ] ℂ) := eℂ.toLinearEquiv.finrank_eq.symm
      _ = Module.finrank ℂ (ℂ ⊗[ℚ] K) :=
        (Algebra.TensorProduct.commRight ℚ ℂ K).toLinearEquiv.finrank_eq.symm
      _ = Module.finrank ℚ K := Module.finrank_baseChange
  exact ⟨eℂ.trans <|
    AlgEquiv.piCongrLeft' ℂ (fun _ : ι ↦ ℂ) (Fintype.equivFinOfCardEq hcard)⟩

/-- The canonical map from complex scalar extension to coordinates indexed by the embeddings of
`K` into `ℂ`. This is the map described explicitly in Example 1.19. -/
noncomputable def complexTensorEval
    (K : Type) [Field K] [Algebra ℚ K] :
    ℂ ⊗[ℚ] K →ₐ[ℂ] ((K →ₐ[ℚ] ℂ) → ℂ) :=
  AlgHom.liftEquiv ℚ ℂ K ((K →ₐ[ℚ] ℂ) → ℂ) <|
    Pi.algHom ℚ (fun _ : K →ₐ[ℚ] ℂ ↦ ℂ) fun σ ↦ σ

@[simp]
theorem complex_tensor_tmul
    (K : Type) [Field K] [Algebra ℚ K]
    (z : ℂ) (x : K) (σ : K →ₐ[ℚ] ℂ) :
    complexTensorEval K (z ⊗ₜ[ℚ] x) σ = z * σ x := by
  simp [complexTensorEval]

/-- The explicit evaluation map in Example 1.19 is an isomorphism. -/
theorem complex_tensor_bijective
    (K : Type) [Field K] [Algebra ℚ K] [FiniteDimensional ℚ K] :
    Function.Bijective (complexTensorEval K) := by
  classical
  let pb : PowerBasis ℚ K := Field.powerBasisOfFiniteOfSeparable ℚ K
  letI : Fintype (K →ₐ[ℚ] ℂ) := PowerBasis.AlgHom.fintype pb
  let e : Fin pb.dim ≃ (K →ₐ[ℚ] ℂ) := Fintype.equivOfCardEq <| by
    calc
      Fintype.card (Fin pb.dim) = pb.dim := Fintype.card_fin pb.dim
      _ = Fintype.card (K →ₐ[ℚ] ℂ) :=
        (AlgHom.card_of_powerBasis pb
          (Algebra.IsSeparable.isSeparable ℚ pb.gen)
          (IsAlgClosed.splits (k := ℂ) _)).symm
  let bdom : Module.Basis (Fin pb.dim) ℂ (ℂ ⊗[ℚ] K) := pb.basis.baseChange ℂ
  let bcod : Module.Basis (Fin pb.dim) ℂ ((K →ₐ[ℚ] ℂ) → ℂ) :=
    (Pi.basisFun ℂ (K →ₐ[ℚ] ℂ)).reindex e.symm
  have hmatrix :
      LinearMap.toMatrix bdom bcod (complexTensorEval K).toLinearMap =
        (Algebra.embeddingsMatrixReindex ℚ ℂ pb.basis e)ᵀ := by
    ext i j
    simp [LinearMap.toMatrix_apply, bdom, bcod,
      Algebra.embeddingsMatrixReindex, complex_tensor_tmul]
  have heval : Function.Injective (fun i : Fin pb.dim ↦ e i pb.gen) := by
    intro i j hij
    apply e.injective
    exact pb.algHom_ext hij
  have hdet :
      (LinearMap.toMatrix bdom bcod (complexTensorEval K).toLinearMap).det ≠ 0 := by
    rw [hmatrix, Matrix.det_transpose,
      Algebra.embeddingsMatrixReindex_eq_vandermonde ℂ pb e, Matrix.det_transpose]
    exact Matrix.det_vandermonde_ne_zero_iff.mpr heval
  have hinj : Function.Injective (complexTensorEval K).toLinearMap := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro x hx
    have hz : ((bdom.repr x : Fin pb.dim →₀ ℂ) : Fin pb.dim → ℂ) = 0 := by
      apply Matrix.eq_zero_of_mulVec_eq_zero hdet
      rw [LinearMap.toMatrix_mulVec_repr]
      simpa using hx
    apply bdom.repr.injective
    simp only [map_zero]
    ext i
    exact congr_fun hz i
  have hfinrank :
      Module.finrank ℂ (ℂ ⊗[ℚ] K) =
        Module.finrank ℂ ((K →ₐ[ℚ] ℂ) → ℂ) := by
    calc
      Module.finrank ℂ (ℂ ⊗[ℚ] K) = Module.finrank ℚ K := Module.finrank_baseChange
      _ = pb.dim := pb.finrank
      _ = Fintype.card (K →ₐ[ℚ] ℂ) :=
        (AlgHom.card_of_powerBasis pb
          (Algebra.IsSeparable.isSeparable ℚ pb.gen)
          (IsAlgClosed.splits (k := ℂ) _)).symm
      _ = Module.finrank ℂ ((K →ₐ[ℚ] ℂ) → ℂ) :=
        (Module.finrank_fintype_fun_eq_card ℂ).symm
  exact ⟨hinj,
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfinrank).mp hinj⟩

end Submission.NumberTheory.Milne
