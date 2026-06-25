import Mathlib
import Submission.Group.DenseGenerators.InitialZassenhausTerms


open scoped Topology Pointwise

noncomputable section

namespace Submission

universe u
universe v w z

namespace DPBuild

abbrev FinQuot
    (Γ : Type u) [Group Γ] [TopologicalSpace Γ] : Type u :=
  { N : Subgroup Γ // N.Normal ∧ IsOpen (N : Set Γ) ∧ Finite (Γ ⧸ N) }

abbrev Coord
    (p : ℕ) (Γ : Type u) [Group Γ] [TopologicalSpace Γ]
    (i : FinQuot Γ) : Type u :=
  letI : i.1.Normal := i.2.1
  MonoidAlgebra (ZMod p) (Γ ⧸ i.1)

instance coordUniformSpace
    (p : ℕ) (Γ : Type u) [Group Γ] [TopologicalSpace Γ]
    (i : FinQuot Γ) : UniformSpace (Coord p Γ i) :=
  ⊥

instance coordDiscreteUniformity
    (p : ℕ) (Γ : Type u) [Group Γ] [TopologicalSpace Γ]
    (i : FinQuot Γ) : DiscreteUniformity (Coord p Γ i) :=
  inferInstance

instance coordRing
    (p : ℕ) (Γ : Type u) [Group Γ] [TopologicalSpace Γ]
    (i : FinQuot Γ) : Ring (Coord p Γ i) := by
  dsimp [Coord]
  letI : i.1.Normal := i.2.1
  infer_instance

instance coordAlgebra
    (p : ℕ) (Γ : Type u) [Group Γ] [TopologicalSpace Γ]
    (i : FinQuot Γ) : Algebra (ZMod p) (Coord p Γ i) := by
  dsimp [Coord]
  letI : i.1.Normal := i.2.1
  change Algebra (ZMod p) (MonoidAlgebra (ZMod p) (Γ ⧸ i.1))
  infer_instance

instance coordDiscreteTopology
    (p : ℕ) (Γ : Type u) [Group Γ] [TopologicalSpace Γ]
    (i : FinQuot Γ) : DiscreteTopology (Coord p Γ i) := by
  infer_instance

instance coordFinite
    (p : ℕ) [Fact p.Prime] (Γ : Type u) [Group Γ] [TopologicalSpace Γ]
    (i : FinQuot Γ) : Finite (Coord p Γ i) := by
  dsimp [Coord]
  letI : i.1.Normal := i.2.1
  letI : Finite (Γ ⧸ i.1) := i.2.2.2
  letI : Fintype (Γ ⧸ i.1) := Fintype.ofFinite (Γ ⧸ i.1)
  letI : DecidableEq (Γ ⧸ i.1) := Classical.decEq _
  letI : NeZero p := ⟨Nat.Prime.ne_zero Fact.out⟩
  letI : Fintype (ZMod p) := ZMod.fintype p
  change Finite ((Γ ⧸ i.1) →₀ ZMod p)
  exact Fintype.finite Finsupp.fintype

instance coordCompactSpace
    (p : ℕ) [Fact p.Prime] (Γ : Type u) [Group Γ] [TopologicalSpace Γ]
    (i : FinQuot Γ) : CompactSpace (Coord p Γ i) := by
  infer_instance

instance coordTSpace
    (p : ℕ) [Fact p.Prime] (Γ : Type u) [Group Γ] [TopologicalSpace Γ]
    (i : FinQuot Γ) : T2Space (Coord p Γ i) := by
  infer_instance

instance coordDisconnectedSpace
    (p : ℕ) [Fact p.Prime] (Γ : Type u) [Group Γ] [TopologicalSpace Γ]
    (i : FinQuot Γ) : TotallyDisconnectedSpace (Coord p Γ i) := by
  infer_instance

instance coordTopologicalRing
    (p : ℕ) (Γ : Type u) [Group Γ] [TopologicalSpace Γ]
    (i : FinQuot Γ) : IsTopologicalRing (Coord p Γ i) := by
  infer_instance

abbrev ProdAlg
    (p : ℕ) (Γ : Type u) [Group Γ] [TopologicalSpace Γ] : Type u :=
  ∀ i : FinQuot Γ, Coord p Γ i

instance prodTopologicalRing
    (p : ℕ) (Γ : Type u) [Group Γ] [TopologicalSpace Γ] :
    IsTopologicalRing (ProdAlg p Γ) := by
  dsimp [ProdAlg]
  infer_instance

def groupAlgebraUnit
    (p : ℕ) {G : Type u} [Group G] (g : G) :
    Units (MonoidAlgebra (ZMod p) G) where
  val := MonoidAlgebra.single g 1
  inv := MonoidAlgebra.single g⁻¹ 1
  val_inv := by
    rw [MonoidAlgebra.single_mul_single]
    simp [MonoidAlgebra.one_def]
  inv_val := by
    rw [MonoidAlgebra.single_mul_single]
    simp [MonoidAlgebra.one_def]

def prodCanonicalUnit
    (p : ℕ) [Fact p.Prime]
    (Γ : Type u) [Group Γ] [TopologicalSpace Γ] :
    Γ →* Units (ProdAlg p Γ) where
  toFun g :=
    { val := fun i =>
        letI : i.1.Normal := i.2.1
        (groupAlgebraUnit p (QuotientGroup.mk' i.1 g) :
          Units (MonoidAlgebra (ZMod p) (Γ ⧸ i.1))).val
      inv := fun i =>
        letI : i.1.Normal := i.2.1
        (groupAlgebraUnit p (QuotientGroup.mk' i.1 g) :
          Units (MonoidAlgebra (ZMod p) (Γ ⧸ i.1))).inv
      val_inv := by
        funext i
        dsimp
        letI : i.1.Normal := i.2.1
        exact (groupAlgebraUnit p (QuotientGroup.mk' i.1 g)).val_inv
      inv_val := by
        funext i
        dsimp
        letI : i.1.Normal := i.2.1
        exact (groupAlgebraUnit p (QuotientGroup.mk' i.1 g)).inv_val }
  map_one' := by
    apply Units.ext
    funext i
    letI : i.1.Normal := i.2.1
    change MonoidAlgebra.single (QuotientGroup.mk' i.1 (1 : Γ)) (1 : ZMod p) =
      (1 : MonoidAlgebra (ZMod p) (Γ ⧸ i.1))
    simp [MonoidAlgebra.one_def]
  map_mul' a b := by
    apply Units.ext
    funext i
    letI : i.1.Normal := i.2.1
    change MonoidAlgebra.single (QuotientGroup.mk' i.1 (a * b)) (1 : ZMod p) =
      MonoidAlgebra.single (QuotientGroup.mk' i.1 a) (1 : ZMod p) *
        MonoidAlgebra.single (QuotientGroup.mk' i.1 b) (1 : ZMod p)
    rw [MonoidAlgebra.single_mul_single]
    simp

def denseSubalgebra
    (p : ℕ) [Fact p.Prime]
    (Γ : Type u) [Group Γ] [TopologicalSpace Γ] :
    Subalgebra (ZMod p) (ProdAlg p Γ) :=
  Algebra.adjoin (ZMod p)
    (Set.range fun g : Γ => (prodCanonicalUnit p Γ g : ProdAlg p Γ))

abbrev Completion
    (p : ℕ) [Fact p.Prime]
    (Γ : Type u) [Group Γ] [TopologicalSpace Γ] : Type u :=
  (denseSubalgebra p Γ).topologicalClosure

instance completionCompactSpace
    (p : ℕ) [Fact p.Prime]
    (Γ : Type u) [Group Γ] [TopologicalSpace Γ] :
    CompactSpace (Completion p Γ) := by
  dsimp [Completion]
  exact
    ((Subalgebra.isClosed_topologicalClosure
      (denseSubalgebra p Γ)).isClosedEmbedding_subtypeVal).compactSpace

instance completionTopologicalRing
    (p : ℕ) [Fact p.Prime]
    (Γ : Type u) [Group Γ] [TopologicalSpace Γ] :
    IsTopologicalRing (Completion p Γ) := by
  dsimp [Completion]
  exact Subring.instIsTopologicalRing
    ((denseSubalgebra p Γ).topologicalClosure.toSubring)

def topIndex
    (Γ : Type u) [Group Γ] [TopologicalSpace Γ] : FinQuot Γ where
  val := ⊤
  property := by
    refine ⟨inferInstance, ?_, ?_⟩
    · simp
    · infer_instance

def coordAug
    (p : ℕ) (Γ : Type u) [Group Γ] [TopologicalSpace Γ]
    (i : FinQuot Γ) : Coord p Γ i →ₐ[ZMod p] ZMod p := by
  dsimp [Coord]
  letI : i.1.Normal := i.2.1
  exact MonoidAlgebra.lift (ZMod p) (ZMod p) (Γ ⧸ i.1) (1 : (Γ ⧸ i.1) →* ZMod p)

def prodAug
    (p : ℕ) [Fact p.Prime]
    (Γ : Type u) [Group Γ] [TopologicalSpace Γ]
    (i : FinQuot Γ) : ProdAlg p Γ →ₐ[ZMod p] ZMod p :=
  (coordAug p Γ i).comp (Pi.evalAlgHom (ZMod p) (Coord p Γ) i)

lemma prodAug_canonical
    (p : ℕ) [Fact p.Prime]
    (Γ : Type u) [Group Γ] [TopologicalSpace Γ]
    (i : FinQuot Γ) (g : Γ) :
    prodAug p Γ i (prodCanonicalUnit p Γ g : ProdAlg p Γ) = 1 := by
  dsimp [prodAug, coordAug, prodCanonicalUnit, groupAlgebraUnit]
  letI : i.1.Normal := i.2.1
  change
    MonoidAlgebra.lift (ZMod p) (ZMod p) (Γ ⧸ i.1)
        (1 : (Γ ⧸ i.1) →* ZMod p)
      (MonoidAlgebra.single (QuotientGroup.mk' i.1 g) (1 : ZMod p)) = 1
  rw [MonoidAlgebra.lift_single]
  simp

lemma prod_aug_subalgebra
    (p : ℕ) [Fact p.Prime]
    (Γ : Type u) [Group Γ] [TopologicalSpace Γ]
    (i j : FinQuot Γ) {x : ProdAlg p Γ}
    (hx : x ∈ denseSubalgebra p Γ) :
    prodAug p Γ i x = prodAug p Γ j x := by
  exact (AlgHom.eqOn_adjoin_iff.mpr (fun x hx => by
    rcases hx with ⟨g, rfl⟩
    rw [prodAug_canonical p Γ i g, prodAug_canonical p Γ j g])) hx

lemma continuous_prodAug
    (p : ℕ) [Fact p.Prime]
    (Γ : Type u) [Group Γ] [TopologicalSpace Γ]
    (i : FinQuot Γ) :
    Continuous (prodAug p Γ i) := by
  exact (continuous_of_discreteTopology (f := coordAug p Γ i)).comp (continuous_apply i)

def completionAug
    (p : ℕ) [Fact p.Prime]
    (Γ : Type u) [Group Γ] [TopologicalSpace Γ] :
    Completion p Γ →ₐ[ZMod p] ZMod p :=
  (prodAug p Γ (topIndex Γ)).comp (Subalgebra.val _)

lemma continuous_completionAug
    (p : ℕ) [Fact p.Prime]
    (Γ : Type u) [Group Γ] [TopologicalSpace Γ] :
    Continuous (completionAug p Γ) := by
  exact (continuous_prodAug p Γ (topIndex Γ)).comp continuous_subtype_val

def completionCanonicalUnit
    (p : ℕ) [Fact p.Prime]
    (Γ : Type u) [Group Γ] [TopologicalSpace Γ] :
    Γ →* Units (Completion p Γ) where
  toFun g :=
    { val :=
        ⟨(prodCanonicalUnit p Γ g : ProdAlg p Γ),
          Subalgebra.le_topologicalClosure (denseSubalgebra p Γ)
            (Algebra.subset_adjoin ⟨g, rfl⟩)⟩
      inv :=
        ⟨(prodCanonicalUnit p Γ g⁻¹ : ProdAlg p Γ),
          Subalgebra.le_topologicalClosure (denseSubalgebra p Γ)
            (Algebra.subset_adjoin ⟨g⁻¹, rfl⟩)⟩
      val_inv := by
        apply Subtype.ext
        exact (prodCanonicalUnit p Γ g).val_inv
      inv_val := by
        apply Subtype.ext
        exact (prodCanonicalUnit p Γ g).inv_val }
  map_one' := by
    apply Units.ext
    apply Subtype.ext
    exact congrArg Units.val (map_one (prodCanonicalUnit p Γ))
  map_mul' a b := by
    apply Units.ext
    apply Subtype.ext
    exact congrArg Units.val (map_mul (prodCanonicalUnit p Γ) a b)

lemma continuous_prod_val
    (p : ℕ) [Fact p.Prime]
    (Γ : Type u) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] :
    Continuous (fun g : Γ => (prodCanonicalUnit p Γ g : ProdAlg p Γ)) := by
  apply continuous_pi
  intro i
  letI : i.1.Normal := i.2.1
  haveI : DiscreteTopology (Γ ⧸ i.1) :=
    (QuotientGroup.discreteTopology_iff).2 i.2.2.1
  have hsingle :
      Continuous
        (fun q : Γ ⧸ i.1 =>
          (MonoidAlgebra.single q (1 : ZMod p) : Coord p Γ i)) :=
    continuous_of_discreteTopology
  exact hsingle.comp QuotientGroup.continuous_mk

lemma continuous_prod_unit
    (p : ℕ) [Fact p.Prime]
    (Γ : Type u) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] :
    Continuous (prodCanonicalUnit p Γ) := by
  rw [Units.continuous_iff]
  constructor
  · exact continuous_prod_val p Γ
  · have h := (continuous_prod_val p Γ).comp continuous_inv
    convert h using 1

lemma continuous_canonical_unit
    (p : ℕ) [Fact p.Prime]
    (Γ : Type u) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] :
    Continuous (completionCanonicalUnit p Γ) := by
  rw [Units.continuous_iff]
  constructor
  · exact (continuous_prod_val p Γ).subtype_mk _
  · have h := ((continuous_prod_val p Γ).comp continuous_inv).subtype_mk
        (fun g =>
          Subalgebra.le_topologicalClosure (denseSubalgebra p Γ)
            (Algebra.subset_adjoin ⟨g⁻¹, rfl⟩))
    convert h using 1

def canonicalSpan
    (p : ℕ) [Fact p.Prime]
    (Γ : Type u) [Group Γ] [TopologicalSpace Γ] :
    Submodule (ZMod p) (Completion p Γ) :=
  Submodule.span (ZMod p)
    (Set.range fun g : Γ => (completionCanonicalUnit p Γ g : Completion p Γ))

lemma canonical_span_mul
    (p : ℕ) [Fact p.Prime]
    (Γ : Type u) [Group Γ] [TopologicalSpace Γ]
    {x y : Completion p Γ}
    (hx : x ∈ canonicalSpan p Γ) (hy : y ∈ canonicalSpan p Γ) :
    x * y ∈ canonicalSpan p Γ := by
  dsimp [canonicalSpan] at hx hy ⊢
  refine Submodule.span_induction₂
      (p := fun x y _ _ =>
        x * y ∈
          Submodule.span (ZMod p)
            (Set.range fun g : Γ =>
              (completionCanonicalUnit p Γ g : Completion p Γ)))
      ?mem_mem ?zero_left ?zero_right
      ?add_left ?add_right ?smul_left ?smul_right hx hy
  · intro x y hx hy
    rcases hx with ⟨g, rfl⟩
    rcases hy with ⟨h, rfl⟩
    have hgen :
        ((completionCanonicalUnit p Γ (g * h) : Units (Completion p Γ)) :
          Completion p Γ) ∈
          Submodule.span (ZMod p)
            (Set.range fun g : Γ =>
              (completionCanonicalUnit p Γ g : Completion p Γ)) :=
      Submodule.subset_span ⟨g * h, rfl⟩
    simpa using hgen
  · intro y hy
    simp
  · intro x hx
    simp
  · intro x y z hx hy hz hxz hyz
    rw [add_mul]
    exact Submodule.add_mem _ hxz hyz
  · intro x y z hx hy hz hxy hxz
    rw [mul_add]
    exact Submodule.add_mem _ hxy hxz
  · intro r x y hx hy hxy
    rw [smul_mul_assoc]
    exact Submodule.smul_mem _ r hxy
  · intro r x y hx hy hxy
    rw [mul_smul_comm]
    exact Submodule.smul_mem _ r hxy

lemma dense_subalgebra_span
    (p : ℕ) [Fact p.Prime]
    (Γ : Type u) [Group Γ] [TopologicalSpace Γ]
    {x : ProdAlg p Γ} (hx : x ∈ denseSubalgebra p Γ) :
    (⟨x, Subalgebra.le_topologicalClosure (denseSubalgebra p Γ) hx⟩ :
      Completion p Γ) ∈ canonicalSpan p Γ := by
  dsimp [denseSubalgebra] at hx
  refine Algebra.adjoin_induction
    (p := fun x hx =>
      (⟨x, Subalgebra.le_topologicalClosure (denseSubalgebra p Γ) hx⟩ :
        Completion p Γ) ∈ canonicalSpan p Γ)
    ?mem ?algebraMap ?add ?mul hx
  · intro x hx
    rcases hx with ⟨g, rfl⟩
    exact Submodule.subset_span ⟨g, rfl⟩
  · intro r
    have hone : (1 : Completion p Γ) ∈ canonicalSpan p Γ := by
      have hgen :
          ((completionCanonicalUnit p Γ 1 : Units (Completion p Γ)) :
            Completion p Γ) ∈ canonicalSpan p Γ :=
        Submodule.subset_span ⟨1, rfl⟩
      simpa using hgen
    simpa [Algebra.smul_def] using
      (Submodule.smul_mem (canonicalSpan p Γ) r hone)
  · intro x y hx hy hxspan hyspan
    simpa using Submodule.add_mem (canonicalSpan p Γ) hxspan hyspan
  · intro x y hx hy hxspan hyspan
    exact canonical_span_mul p Γ hxspan hyspan

lemma dense_subalgebra_completion
    (p : ℕ) [Fact p.Prime]
    (Γ : Type u) [Group Γ] [TopologicalSpace Γ] :
    DenseRange
      (Set.inclusion
        (Subalgebra.le_topologicalClosure (denseSubalgebra p Γ))) := by
  rw [denseRange_inclusion_iff]
  intro x hx
  simpa [Subalgebra.topologicalClosure_coe] using hx

lemma canonicalSpan_dense
    (p : ℕ) [Fact p.Prime]
    (Γ : Type u) [Group Γ] [TopologicalSpace Γ] :
    closure ((canonicalSpan p Γ : Set (Completion p Γ))) = Set.univ := by
  let incl :
      denseSubalgebra p Γ → Completion p Γ :=
    Set.inclusion
      (Subalgebra.le_topologicalClosure (denseSubalgebra p Γ))
  have hdense : DenseRange incl :=
    dense_subalgebra_completion p Γ
  have hrange_subset :
      Set.range incl ⊆ (canonicalSpan p Γ : Set (Completion p Γ)) := by
    rintro x ⟨y, rfl⟩
    exact dense_subalgebra_span p Γ y.2
  apply Set.Subset.antisymm
  · intro x hx
    trivial
  · rw [← hdense.closure_range]
    exact closure_mono hrange_subset

def kerIndex
    (Γ : Type u) [Group Γ] [TopologicalSpace Γ]
    {Λ : Type u} [Group Λ] [TopologicalSpace Λ] [DiscreteTopology Λ] [Finite Λ]
    (φ : Γ →* Λ) (hφ : Continuous (fun x : Γ => φ x)) : FinQuot Γ where
  val := φ.ker
  property := by
    refine ⟨inferInstance, ?_, ?_⟩
    · change IsOpen {x : Γ | φ x = 1}
      change IsOpen ((fun x : Γ => φ x) ⁻¹' ({1} : Set Λ))
      exact hφ.isOpen_preimage _ (isOpen_discrete _)
    · exact Finite.of_equiv φ.range (QuotientGroup.quotientKerEquivRange φ).symm

def quotientToTarget
    {Γ : Type u} [Group Γ]
    {Λ : Type u} [Group Λ]
    (φ : Γ →* Λ) : Γ ⧸ φ.ker →* Λ :=
  QuotientGroup.lift φ.ker φ le_rfl

def finiteAlgHom
    (p : ℕ) [Fact p.Prime]
    (Γ : Type u) [Group Γ] [TopologicalSpace Γ]
    {Λ : Type u} [Group Λ] [TopologicalSpace Λ] [DiscreteTopology Λ] [Finite Λ]
    (φ : Γ →* Λ) (hφ : Continuous (fun x : Γ => φ x)) :
    Completion p Γ →ₐ[ZMod p] MonoidAlgebra (ZMod p) Λ :=
  let i := kerIndex Γ φ hφ
  letI : i.1.Normal := i.2.1
  ((MonoidAlgebra.mapDomainAlgHom (ZMod p) (ZMod p) (quotientToTarget φ)).comp
      (Pi.evalAlgHom (ZMod p) (Coord p Γ) i)).comp
    (Subalgebra.val _)

lemma alg_canonical_unit
    (p : ℕ) [Fact p.Prime]
    (Γ : Type u) [Group Γ] [TopologicalSpace Γ]
    {Λ : Type u} [Group Λ] [TopologicalSpace Λ] [DiscreteTopology Λ] [Finite Λ]
    (φ : Γ →* Λ) (hφ : Continuous (fun x : Γ => φ x)) (g : Γ) :
    finiteAlgHom p Γ φ hφ
        (completionCanonicalUnit p Γ g : Completion p Γ) =
      MonoidAlgebra.single (φ g) 1 := by
  dsimp [finiteAlgHom, completionCanonicalUnit, prodCanonicalUnit,
    groupAlgebraUnit]
  change MonoidAlgebra.mapDomain (quotientToTarget φ)
      (MonoidAlgebra.single (QuotientGroup.mk' φ.ker g) (1 : ZMod p)) =
    MonoidAlgebra.single (φ g) 1
  simp [quotientToTarget]

lemma completion_prod_aug
    (p : ℕ) [Fact p.Prime]
    (Γ : Type u) [Group Γ] [TopologicalSpace Γ]
    (i : FinQuot Γ) (x : Completion p Γ) :
    prodAug p Γ i x.1 = completionAug p Γ x := by
  let incl :
      denseSubalgebra p Γ → Completion p Γ :=
    Set.inclusion
      (Subalgebra.le_topologicalClosure (denseSubalgebra p Γ))
  have hdense : Dense (Set.range incl) :=
    dense_subalgebra_completion p Γ
  let f : Completion p Γ → ZMod p := fun x => prodAug p Γ i x.1
  let g : Completion p Γ → ZMod p := fun x => completionAug p Γ x
  have hf : Continuous f :=
    (continuous_prodAug p Γ i).comp continuous_subtype_val
  have hg : Continuous g :=
    continuous_completionAug p Γ
  have heq : Set.EqOn f g (Set.range incl) := by
    rintro y ⟨z, rfl⟩
    dsimp [f, g, incl, completionAug]
    exact prod_aug_subalgebra p Γ i (topIndex Γ) z.2
  have hfg : f = g := Continuous.ext_on hdense hf hg heq
  exact congrFun hfg x

lemma alg_hom_augmentation
    (p : ℕ) [Fact p.Prime]
    (Γ : Type u) [Group Γ] [TopologicalSpace Γ]
    {Λ : Type u} [Group Λ] [TopologicalSpace Λ] [DiscreteTopology Λ] [Finite Λ]
    (φ : Γ →* Λ) (hφ : Continuous (fun x : Γ => φ x))
    (x : Completion p Γ) :
    MonoidAlgebra.lift (ZMod p) (ZMod p) Λ (1 : Λ →* ZMod p)
        (finiteAlgHom p Γ φ hφ x) =
      completionAug p Γ x := by
  have hcomp :
      (MonoidAlgebra.lift (ZMod p) (ZMod p) Λ (1 : Λ →* ZMod p)).comp
          (MonoidAlgebra.mapDomainAlgHom (ZMod p) (ZMod p)
            (quotientToTarget φ)) =
        coordAug p Γ (kerIndex Γ φ hφ) := by
    apply MonoidAlgebra.algHom_ext
    intro q
    dsimp [coordAug, kerIndex]
    rw [MonoidAlgebra.mapDomain_single, MonoidAlgebra.lift_single]
    have hright :
        ((MonoidAlgebra.lift (ZMod p) (ZMod p) (Γ ⧸ φ.ker))
            (1 : (Γ ⧸ φ.ker) →* ZMod p))
            (MonoidAlgebra.single q 1) = 1 := by
      rw [MonoidAlgebra.lift_single]
      simp
    calc
      (1 : ZMod p) • (1 : Λ →* ZMod p)
          ((quotientToTarget φ) q) = (1 : ZMod p) := by
            simp
      _ = ((MonoidAlgebra.lift (ZMod p) (ZMod p) (Γ ⧸ φ.ker))
            (1 : (Γ ⧸ φ.ker) →* ZMod p))
            (MonoidAlgebra.single q 1) := hright.symm
  calc
    MonoidAlgebra.lift (ZMod p) (ZMod p) Λ (1 : Λ →* ZMod p)
        (finiteAlgHom p Γ φ hφ x)
        = prodAug p Γ (kerIndex Γ φ hφ) x.1 := by
          dsimp [finiteAlgHom, prodAug]
          change
            ((MonoidAlgebra.lift (ZMod p) (ZMod p) Λ
                (1 : Λ →* ZMod p)).comp
              (MonoidAlgebra.mapDomainAlgHom (ZMod p) (ZMod p)
                (quotientToTarget φ)))
                (x.1 (kerIndex Γ φ hφ)) =
              coordAug p Γ (kerIndex Γ φ hφ)
                (x.1 (kerIndex Γ φ hφ))
          simpa using congrArg
            (fun F : Coord p Γ (kerIndex Γ φ hφ) →ₐ[ZMod p] ZMod p =>
              F (x.1 (kerIndex Γ φ hφ))) hcomp
    _ = completionAug p Γ x :=
        completion_prod_aug p Γ (kerIndex Γ φ hφ) x

theorem gens_completed_package
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} (s : Fin d → Γ)
    (hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤) :
    Nonempty
      (GCPackag
        (p := p) Γ s hs) := by
  let A : DCObject
      (p := p) (Γ := Γ) s hs := {
    completedGroupAlgebra := Completion p Γ
    instRing := inferInstance
    instAlgebra := inferInstance
    instUniformSpace := inferInstance
    topologicalRing := inferInstance
    instCompleteSpace := inferInstance
    t2Space := inferInstance
    instCompactSpace := inferInstance
    totallyDisconnected := inferInstance }
  let Aug : DenseCompletedAugmentation A := {
    augmentationMap := completionAug p Γ
    augmentationMap_continuous := continuous_completionAug p Γ
    augmentationIdeal := RingHom.ker (completionAug p Γ).toRingHom
    augmentation_ideal_ker := rfl }
  let U : DenseCompletedUnits A Aug := {
    canonicalUnit := completionCanonicalUnit p Γ
    canonicalUnit_continuous := continuous_canonical_unit p Γ
    canonicalUnit_augmentation := by
      intro g
      simpa [Aug, completionAug, completionCanonicalUnit] using
        prodAug_canonical p Γ (topIndex Γ) g }
  let D : DCSpan A Aug U := {
    dense_span := by
      simpa [A, U, canonicalSpan] using canonicalSpan_dense p Γ }
  let F :
      DenseCompletedExtension
        A Aug U := {
    quotient_alg_hom := fun φ hφ =>
      finiteAlgHom p Γ φ hφ
    alg_hom_unit := by
      intro Λ _ _ _ _ φ hφ g
      simpa [U] using alg_canonical_unit p Γ φ hφ g
    finite_alg_hom := by
      intro Λ _ _ _ _ φ hφ x
      simpa [Aug] using alg_hom_augmentation p Γ φ hφ x }
  exact ⟨{
    object := A
    augmentation := Aug
    canonicalUnits := U
    canonicalDenseSpan := D
    algebraMapExtension := F }⟩

end DPBuild

lemma gens_completed_package
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} (s : Fin d → Γ)
    (hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤) :
    Nonempty
      (GCPackag
        (p := p) Γ s hs) := by
  exact
    DPBuild.gens_completed_package
      s hs

lemma completed_object_units
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} (s : Fin d → Γ)
    (hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤) :
    ∃ A : DCObject
        (p := p) (Γ := Γ) s hs,
      ∃ Aug : DenseCompletedAugmentation A,
        Nonempty (DenseCompletedUnits A Aug) := by
  rcases
      gens_completed_package
        (p := p) (Γ := Γ) s hs with
    ⟨P⟩
  exact P.exists_object_augunits

lemma generators_completed_object
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} (s : Fin d → Γ)
    (hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤) :
    Nonempty
      (DCObject
        (p := p) (Γ := Γ) s hs) := by
  rcases completed_object_units
      (p := p) (Γ := Γ) s hs with ⟨A, _Aug, _U⟩
  exact ⟨A⟩

lemma dense_completed_object
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} (s : Fin d → Γ)
    (hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤) :
    ∃ A : DCObject
        (p := p) (Γ := Γ) s hs,
      Nonempty (DenseCompletedAugmentation A) := by
  rcases completed_object_units
      (p := p) (Γ := Γ) s hs with ⟨A, Aug, _U⟩
  exact ⟨A, ⟨Aug⟩⟩

lemma completed_algebra_ambient
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} (s : Fin d → Γ)
    (hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤) :
    Nonempty
      (GCAmbien
        (p := p) (Γ := Γ) s hs) := by
  rcases completed_object_units
      (p := p) (Γ := Γ) s hs with ⟨A, Aug, hU⟩
  rcases hU with ⟨U⟩
  exact ⟨A.toAmbient Aug U⟩

lemma dense_completed_algebraic
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (n : ℕ)
    (A : GCAmbien (p := p) (Γ := Γ) s hs) :
    Nonempty
      (GAAug
        (p := p) (Γ := Γ) (s := s) (hs := hs) n A) := by
  have haugmentation_two_sided : A.augmentationIdeal.IsTwoSided := by
    rw [A.augmentation_ideal_ker]
    infer_instance
  letI : A.augmentationIdeal.IsTwoSided := haugmentation_two_sided
  let I : Ideal A.completedGroupAlgebra := A.augmentationIdeal ^ n
  have hI_two_sided : I.IsTwoSided := by
    dsimp [I]
    infer_instance
  letI : I.IsTwoSided := hI_two_sided
  let quotientMap : A.completedGroupAlgebra →ₐ[ZMod p] A.completedGroupAlgebra ⧸ I :=
    Ideal.Quotient.mkₐ (ZMod p) I
  have hsurjective : Function.Surjective quotientMap := by
    simpa [quotientMap] using Ideal.Quotient.mkₐ_surjective (ZMod p) I
  have hker : RingHom.ker quotientMap.toRingHom = A.augmentationIdeal ^ n := by
    simp [quotientMap, I]
  refine ⟨?_⟩
  exact
    { augmentationQuotient := A.completedGroupAlgebra ⧸ I
      instQuotientRing := inferInstance
      instQuotientAlgebra := inferInstance
      quotientMap := quotientMap
      quotientMap_surjective := hsurjective
      quotientMap_ker := hker }

lemma GAAug.quotmap_eqzero_levelzero
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {A : GCAmbien (p := p) (Γ := Γ) s hs}
    (Q :
      GAAug
        (p := p) (Γ := Γ) (s := s) (hs := hs) 0 A)
    (x : A.completedGroupAlgebra) :
    Q.quotientMap x = 0 := by
  letI := A.instRing
  letI := Q.instQuotientRing
  have hxmem : x ∈ RingHom.ker Q.quotientMap.toRingHom := by
    rw [Q.quotientMap_ker]
    change x ∈ (1 : Ideal A.completedGroupAlgebra)
    rw [Ideal.one_eq_top]
    exact trivial
  have hxzero : Q.quotientMap.toRingHom x = 0 := by
    simpa [RingHom.mem_ker] using hxmem
  simpa using hxzero

lemma GAAug.subsingleton_level_zero
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {A : GCAmbien (p := p) (Γ := Γ) s hs}
    (Q :
      GAAug
        (p := p) (Γ := Γ) (s := s) (hs := hs) 0 A) :
    Subsingleton Q.augmentationQuotient := by
  letI := A.instRing
  letI := Q.instQuotientRing
  refine ⟨?_⟩
  intro y z
  rcases Q.quotientMap_surjective y with ⟨x, rfl⟩
  rcases Q.quotientMap_surjective z with ⟨w, rfl⟩
  rw [Q.quotmap_eqzero_levelzero x,
    Q.quotmap_eqzero_levelzero w]

lemma GAAug.topo_aug_quotsubsing
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    {A : GCAmbien (p := p) (Γ := Γ) s hs}
    (Q :
      GAAug
        (p := p) (Γ := Γ) (s := s) (hs := hs) n A)
    (hsub : Subsingleton Q.augmentationQuotient) :
    Nonempty
      (GTAug
        (p := p) (Γ := Γ) (s := s) (hs := hs) Q) := by
  letI := A.instRing
  letI := Q.instQuotientRing
  letI : TopologicalSpace Q.augmentationQuotient := ⊥
  letI : Subsingleton Q.augmentationQuotient := hsub
  haveI : DiscreteTopology Q.augmentationQuotient := inferInstance
  haveI : T2Space Q.augmentationQuotient := inferInstance
  haveI : IsTopologicalRing Q.augmentationQuotient := inferInstance
  haveI : IndiscreteTopology Q.augmentationQuotient := inferInstance
  have hcontinuous : Continuous Q.quotientMap := by
    exact continuous_of_indiscreteTopology
  exact
    ⟨{ quotientTopology := inferInstance
       quotientT2 := inferInstance
       quotientTopologicalRing := inferInstance
       quotientMap_continuous := hcontinuous }⟩

lemma GCAmbien.topo_aug_quotzero
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (A : GCAmbien (p := p) (Γ := Γ) s hs) :
    A.TopoAugQuot 0 := by
  rcases dense_completed_algebraic
      (p := p) (Γ := Γ) (s := s) (hs := hs) 0 A with ⟨Q⟩
  refine ⟨Q, ?_⟩
  exact
    Q.topo_aug_quotsubsing
      (Q.subsingleton_level_zero)

lemma completed_ambient_span
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} (s : Fin d → Γ)
    (hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤) :
    ∃ A : GCAmbien (p := p) (Γ := Γ) s hs,
      A.DenseAlgebraSpan := by
  rcases
      gens_completed_package
        (p := p) (Γ := Γ) s hs with
    ⟨P⟩
  exact P.existsambient_denseunit_algspan

lemma
    completed_topological_aug
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} (s : Fin d → Γ)
    (hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤) :
    ∃ A : GCAmbien (p := p) (Γ := Γ) s hs,
      A.DenseAlgebraSpan ∧
        A.TopoAugQuot 0 := by
  rcases completed_ambient_span
      (p := p) (Γ := Γ) s hs with ⟨A, hdense⟩
  exact ⟨A, hdense, A.topo_aug_quotzero⟩

def GCAmbien.ClosedAugPower
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (n : ℕ)
    (A : GCAmbien (p := p) (Γ := Γ) s hs) :
    Prop :=
  IsClosed ((A.augmentationIdeal ^ n : Ideal A.completedGroupAlgebra) :
    Set A.completedGroupAlgebra)

structure GCAmbien.ContAugPowerkernel
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (n : ℕ)
    (A : GCAmbien (p := p) (Γ := Γ) s hs) :
    Type (u + 2) where
  quotientProbe : Type (u + 1)
  [probeTopology : TopologicalSpace quotientProbe]
  [probeT2 : T2Space quotientProbe]
  [instProbeRing : Ring quotientProbe]
  probeMap : A.completedGroupAlgebra →+* quotientProbe
  probeMap_continuous : Continuous probeMap
  probeMap_ker :
    RingHom.ker probeMap = A.augmentationIdeal ^ n

attribute [instance]
  GCAmbien.ContAugPowerkernel.probeTopology
  GCAmbien.ContAugPowerkernel.probeT2
  GCAmbien.ContAugPowerkernel.instProbeRing

structure GCAmbien.FCAugtru
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (n : ℕ)
    (A : GCAmbien (p := p) (Γ := Γ) s hs) :
    Type (u + 2) where
  quotientProbe : Type (u + 1)
  [probeTopology : TopologicalSpace quotientProbe]
  [probeT2 : T2Space quotientProbe]
  [probeDiscrete : DiscreteTopology quotientProbe]
  [instProbeRing : Ring quotientProbe]
  [probeTopologicalRing : IsTopologicalRing quotientProbe]
  [instProbeFinite : Finite quotientProbe]
  probeMap : A.completedGroupAlgebra →+* quotientProbe
  probeMap_continuous : Continuous probeMap
  probeMap_ker :
    RingHom.ker probeMap = A.augmentationIdeal ^ n

attribute [instance]
  GCAmbien.FCAugtru.probeTopology
  GCAmbien.FCAugtru.probeT2
  GCAmbien.FCAugtru.probeDiscrete
  GCAmbien.FCAugtru.instProbeRing
  GCAmbien.FCAugtru.probeTopologicalRing
  GCAmbien.FCAugtru.instProbeFinite

structure GCAmbien.FAAugtru
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (n : ℕ)
    (A : GCAmbien (p := p) (Γ := Γ) s hs) :
    Type (u + 2) where
  quotientProbe : Type (u + 1)
  [instProbeRing : Ring quotientProbe]
  [instProbeFinite : Finite quotientProbe]
  probeMap : A.completedGroupAlgebra →+* quotientProbe
  probeMap_ker :
    RingHom.ker probeMap = A.augmentationIdeal ^ n

attribute [instance]
  GCAmbien.FAAugtru.instProbeRing
  GCAmbien.FAAugtru.instProbeFinite

def
    GAAug.fin_alg_augtrunc
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    {A : GCAmbien (p := p) (Γ := Γ) s hs}
    (Q :
      GAAug
        (p := p) (Γ := Γ) (s := s) (hs := hs) n A)
    [Finite Q.augmentationQuotient] :
    A.FAAugtru n where
  quotientProbe := ULift.{u + 1} Q.augmentationQuotient
  instProbeRing := inferInstance
  instProbeFinite := inferInstance
  probeMap :=
    (ULift.ringEquiv.symm.toRingHom :
        Q.augmentationQuotient →+* ULift.{u + 1} Q.augmentationQuotient).comp
      Q.quotientMap.toRingHom
  probeMap_ker := by
    ext x
    constructor
    · intro hx
      have hxzero_lift :
          ((ULift.ringEquiv.symm.toRingHom :
              Q.augmentationQuotient →+* ULift.{u + 1} Q.augmentationQuotient).comp
            Q.quotientMap.toRingHom) x = 0 := by
        simpa [RingHom.mem_ker] using hx
      have hxzero : Q.quotientMap.toRingHom x = 0 := by
        have hdown := congr_arg ULift.down hxzero_lift
        simpa using hdown
      have hxker : x ∈ RingHom.ker Q.quotientMap.toRingHom := by
        simpa [RingHom.mem_ker] using hxzero
      rw [← Q.quotientMap_ker]
      exact hxker
    · intro hxpow
      have hxker : x ∈ RingHom.ker Q.quotientMap.toRingHom := by
        rw [Q.quotientMap_ker]
        exact hxpow
      have hxzero : Q.quotientMap.toRingHom x = 0 := by
        simpa [RingHom.mem_ker] using hxker
      rw [RingHom.mem_ker]
      apply ULift.ext
      simpa using hxzero

lemma
    GAAug.open_keropen_augpower
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    {A : GCAmbien (p := p) (Γ := Γ) s hs}
    (Q :
      GAAug
        (p := p) (Γ := Γ) (s := s) (hs := hs) n A)
    [Finite Q.augmentationQuotient]
    (hopen :
      IsOpen ((A.augmentationIdeal ^ n : Ideal A.completedGroupAlgebra) :
        Set A.completedGroupAlgebra)) :
    IsOpen
      ((RingHom.ker Q.fin_alg_augtrunc.probeMap :
          Ideal A.completedGroupAlgebra) :
        Set A.completedGroupAlgebra) := by
  simpa [Q.fin_alg_augtrunc.probeMap_ker] using hopen

structure
    GCAmbien.FAAugtru.DiscreteContTopo
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    {A : GCAmbien (p := p) (Γ := Γ) s hs}
    (T : A.FAAugtru n) :
    Type (u + 2) where
  [probeTopology : TopologicalSpace T.quotientProbe]
  [probeDiscrete : DiscreteTopology T.quotientProbe]
  probeMap_continuous : Continuous T.probeMap

attribute [instance]
  GCAmbien.FAAugtru.DiscreteContTopo.probeTopology
  GCAmbien.FAAugtru.DiscreteContTopo.probeDiscrete

lemma
    GCAmbien.FAAugtru.open_preimsingleton_openker
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    {A : GCAmbien (p := p) (Γ := Γ) s hs}
    (T : A.FAAugtru n)
    (hker_open :
      IsOpen ((RingHom.ker T.probeMap : Ideal A.completedGroupAlgebra) :
        Set A.completedGroupAlgebra))
    (y : T.quotientProbe) :
    IsOpen (T.probeMap ⁻¹' ({y} : Set T.quotientProbe)) := by
  by_cases hy : ∃ x : A.completedGroupAlgebra, T.probeMap x = y
  · rcases hy with ⟨x, hx⟩
    have hfiber :
        T.probeMap ⁻¹' ({y} : Set T.quotientProbe) =
          (fun z : A.completedGroupAlgebra => z + x) ''
            ((RingHom.ker T.probeMap : Ideal A.completedGroupAlgebra) :
              Set A.completedGroupAlgebra) := by
      ext a
      constructor
      · intro ha
        refine ⟨a - x, ?_, ?_⟩
        · have ha_eq : T.probeMap a = y := by
            simpa using ha
          have hsub_zero : T.probeMap (a - x) = 0 := by
            calc
              T.probeMap (a - x) = T.probeMap a - T.probeMap x := by
                simp
              _ = y - y := by
                rw [ha_eq, hx]
              _ = 0 := sub_self y
          simpa [RingHom.mem_ker] using hsub_zero
        · simp
      · rintro ⟨z, hz, rfl⟩
        have hz_zero : T.probeMap z = 0 := by
          simpa [RingHom.mem_ker] using hz
        simp [hz_zero, hx]
    rw [hfiber]
    exact (isOpenMap_add_right x) _ hker_open
  · have hfiber :
        T.probeMap ⁻¹' ({y} : Set T.quotientProbe) =
          (∅ : Set A.completedGroupAlgebra) := by
      ext a
      constructor
      · intro ha
        have ha_eq : T.probeMap a = y := by
          simpa using ha
        exact False.elim (hy ⟨a, ha_eq⟩)
      · intro ha
        cases ha
    rw [hfiber]
    exact isOpen_empty

lemma
    GCAmbien.FAAugtru.cont_discrete_openker
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    {A : GCAmbien (p := p) (Γ := Γ) s hs}
    (T : A.FAAugtru n)
    (hker_open :
      IsOpen ((RingHom.ker T.probeMap : Ideal A.completedGroupAlgebra) :
        Set A.completedGroupAlgebra)) :
    letI : TopologicalSpace T.quotientProbe := ⊥
    Continuous T.probeMap := by
  classical
  letI : TopologicalSpace T.quotientProbe := ⊥
  rw [continuous_def]
  intro U _hU
  have hpreimage :
      T.probeMap ⁻¹' U =
        ⋃ y ∈ U, T.probeMap ⁻¹' ({y} : Set T.quotientProbe) := by
    ext x
    constructor
    · intro hx
      exact Set.mem_iUnion_of_mem (T.probeMap x)
        (Set.mem_iUnion_of_mem hx (by simp))
    · intro hx
      rcases Set.mem_iUnion.mp hx with ⟨y, hy⟩
      rcases Set.mem_iUnion.mp hy with ⟨hyU, hxy⟩
      have hxy_eq : T.probeMap x = y := by
        simpa using hxy
      simpa [hxy_eq] using hyU
  rw [hpreimage]
  exact
    isOpen_biUnion fun y _hy =>
      T.open_preimsingleton_openker hker_open y

def
    GCAmbien.FAAugtru.discrete_conttopo_openker
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    {A : GCAmbien (p := p) (Γ := Γ) s hs}
    (T : A.FAAugtru n)
    (hker_open :
      IsOpen ((RingHom.ker T.probeMap : Ideal A.completedGroupAlgebra) :
        Set A.completedGroupAlgebra)) :
    T.DiscreteContTopo where
  probeTopology := ⊥
  probeDiscrete := discreteTopology_bot T.quotientProbe
  probeMap_continuous := T.cont_discrete_openker hker_open

def
    GCAmbien.FAAugtru.discretecont_topoopen_augpower
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    {A : GCAmbien (p := p) (Γ := Γ) s hs}
    (T : A.FAAugtru n)
    (hopen :
      IsOpen ((A.augmentationIdeal ^ n : Ideal A.completedGroupAlgebra) :
        Set A.completedGroupAlgebra)) :
    T.DiscreteContTopo :=
  T.discrete_conttopo_openker
    (by simpa [T.probeMap_ker] using hopen)

def
    GCAmbien.FAAugtru.fin_cont_augtrunc
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    {A : GCAmbien (p := p) (Γ := Γ) s hs}
    (T : A.FAAugtru n)
    (H : T.DiscreteContTopo) :
    A.FCAugtru n where
  quotientProbe := T.quotientProbe
  probeTopology := H.probeTopology
  probeT2 := inferInstance
  probeDiscrete := H.probeDiscrete
  instProbeRing := T.instProbeRing
  probeTopologicalRing := inferInstance
  instProbeFinite := T.instProbeFinite
  probeMap := T.probeMap
  probeMap_continuous := H.probeMap_continuous
  probeMap_ker := T.probeMap_ker

def
    GCAmbien.FCAugtru.fin_alg_augtrunc
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    {A : GCAmbien (p := p) (Γ := Γ) s hs}
    (T : A.FCAugtru n) :
    A.FAAugtru n where
  quotientProbe := T.quotientProbe
  instProbeRing := T.instProbeRing
  instProbeFinite := T.instProbeFinite
  probeMap := T.probeMap
  probeMap_ker := T.probeMap_ker

def
    GCAmbien.FCAugtru.discrete_conttopo_finalg
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    {A : GCAmbien (p := p) (Γ := Γ) s hs}
    (T : A.FCAugtru n) :
    T.fin_alg_augtrunc.DiscreteContTopo where
  probeTopology := T.probeTopology
  probeDiscrete := T.probeDiscrete
  probeMap_continuous := T.probeMap_continuous

def
    GCAmbien.FCAugtru.cont_aug_powerkernel
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    {A : GCAmbien (p := p) (Γ := Γ) s hs}
    (T : A.FCAugtru n) :
    A.ContAugPowerkernel n where
  quotientProbe := T.quotientProbe
  probeTopology := T.probeTopology
  probeT2 := T.probeT2
  instProbeRing := T.instProbeRing
  probeMap := T.probeMap
  probeMap_continuous := T.probeMap_continuous
  probeMap_ker := T.probeMap_ker

noncomputable def
    GAAug.fin_trunc_fn
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    {A : GCAmbien (p := p) (Γ := Γ) s hs}
    (Q :
      GAAug
        (p := p) (Γ := Γ) (s := s) (hs := hs) n A)
    (T : A.FCAugtru n) :
    Q.augmentationQuotient → T.quotientProbe :=
  fun y => T.probeMap (Classical.choose (Q.quotientMap_surjective y))

lemma
    GAAug.fin_trunc_fninj
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    {A : GCAmbien (p := p) (Γ := Γ) s hs}
    (Q :
      GAAug
        (p := p) (Γ := Γ) (s := s) (hs := hs) n A)
    (T : A.FCAugtru n) :
    Function.Injective (Q.fin_trunc_fn T) := by
  intro y z hyz
  let x : A.completedGroupAlgebra :=
    Classical.choose (Q.quotientMap_surjective y)
  let w : A.completedGroupAlgebra :=
    Classical.choose (Q.quotientMap_surjective z)
  have hx : Q.quotientMap x = y := by
    exact Classical.choose_spec (Q.quotientMap_surjective y)
  have hw : Q.quotientMap w = z := by
    exact Classical.choose_spec (Q.quotientMap_surjective z)
  have htrunc_eq : T.probeMap x = T.probeMap w := by
    simpa [GAAug.fin_trunc_fn,
      x, w] using hyz
  have htrunc_sub_zero : T.probeMap (x - w) = 0 := by
    calc
      T.probeMap (x - w) = T.probeMap x - T.probeMap w := by
        simp
      _ = 0 := by
        simpa using sub_eq_zero.mpr htrunc_eq
  have htrunc_ker : x - w ∈ RingHom.ker T.probeMap := by
    simpa [RingHom.mem_ker] using htrunc_sub_zero
  have hpow : x - w ∈ A.augmentationIdeal ^ n := by
    simpa [T.probeMap_ker] using htrunc_ker
  have hquot_ker : x - w ∈ RingHom.ker Q.quotientMap.toRingHom := by
    rw [Q.quotientMap_ker]
    exact hpow
  have hquot_sub_zero : Q.quotientMap (x - w) = 0 := by
    simpa [RingHom.mem_ker] using hquot_ker
  have hquot_eq : Q.quotientMap x = Q.quotientMap w := by
    have hsub : Q.quotientMap x - Q.quotientMap w = 0 := by
      simpa [map_sub] using hquot_sub_zero
    exact sub_eq_zero.mp hsub
  calc
    y = Q.quotientMap x := hx.symm
    _ = Q.quotientMap w := hquot_eq
    _ = z := hw

lemma GAAug.fin_fin_trunc
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    {A : GCAmbien (p := p) (Γ := Γ) s hs}
    (Q :
      GAAug
        (p := p) (Γ := Γ) (s := s) (hs := hs) n A)
    (T : A.FCAugtru n) :
    Finite Q.augmentationQuotient := by
  letI : Finite T.quotientProbe := T.instProbeFinite
  exact
    Finite.of_injective (Q.fin_trunc_fn T)
      (Q.fin_trunc_fninj T)

noncomputable def
    GAAug.fin_alg_truncfn
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    {A : GCAmbien (p := p) (Γ := Γ) s hs}
    (Q :
      GAAug
        (p := p) (Γ := Γ) (s := s) (hs := hs) n A)
    (T : A.FAAugtru n) :
    Q.augmentationQuotient → T.quotientProbe :=
  fun y => T.probeMap (Classical.choose (Q.quotientMap_surjective y))

lemma
    GAAug.fin_algtrunc_fninj
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    {A : GCAmbien (p := p) (Γ := Γ) s hs}
    (Q :
      GAAug
        (p := p) (Γ := Γ) (s := s) (hs := hs) n A)
    (T : A.FAAugtru n) :
    Function.Injective (Q.fin_alg_truncfn T) := by
  intro y z hyz
  let x : A.completedGroupAlgebra :=
    Classical.choose (Q.quotientMap_surjective y)
  let w : A.completedGroupAlgebra :=
    Classical.choose (Q.quotientMap_surjective z)
  have hx : Q.quotientMap x = y := by
    exact Classical.choose_spec (Q.quotientMap_surjective y)
  have hw : Q.quotientMap w = z := by
    exact Classical.choose_spec (Q.quotientMap_surjective z)
  have htrunc_eq : T.probeMap x = T.probeMap w := by
    simpa [
      GAAug.fin_alg_truncfn,
      x, w] using hyz
  have htrunc_sub_zero : T.probeMap (x - w) = 0 := by
    calc
      T.probeMap (x - w) = T.probeMap x - T.probeMap w := by
        simp
      _ = 0 := by
        simpa using sub_eq_zero.mpr htrunc_eq
  have htrunc_ker : x - w ∈ RingHom.ker T.probeMap := by
    simpa [RingHom.mem_ker] using htrunc_sub_zero
  have hpow : x - w ∈ A.augmentationIdeal ^ n := by
    simpa [T.probeMap_ker] using htrunc_ker
  have hquot_ker : x - w ∈ RingHom.ker Q.quotientMap.toRingHom := by
    rw [Q.quotientMap_ker]
    exact hpow
  have hquot_sub_zero : Q.quotientMap (x - w) = 0 := by
    simpa [RingHom.mem_ker] using hquot_ker
  have hquot_eq : Q.quotientMap x = Q.quotientMap w := by
    have hsub : Q.quotientMap x - Q.quotientMap w = 0 := by
      simpa [map_sub] using hquot_sub_zero
    exact sub_eq_zero.mp hsub
  calc
    y = Q.quotientMap x := hx.symm
    _ = Q.quotientMap w := hquot_eq
    _ = z := hw

lemma
    GAAug.fin_fin_algtrunc
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    {A : GCAmbien (p := p) (Γ := Γ) s hs}
    (Q :
      GAAug
        (p := p) (Γ := Γ) (s := s) (hs := hs) n A)
    (T : A.FAAugtru n) :
    Finite Q.augmentationQuotient := by
  letI : Finite T.quotientProbe := T.instProbeFinite
  exact
    Finite.of_injective (Q.fin_alg_truncfn T)
      (Q.fin_algtrunc_fninj T)

lemma
    GCAmbien.existsfin_algaug_quotfintrunc
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    {A : GCAmbien (p := p) (Γ := Γ) s hs}
    (T : A.FCAugtru n) :
    ∃ Q :
      GAAug
        (p := p) (Γ := Γ) (s := s) (hs := hs) n A,
      Finite Q.augmentationQuotient := by
  rcases dense_completed_algebraic
      (p := p) (Γ := Γ) (s := s) (hs := hs) n A with ⟨Q⟩
  exact ⟨Q, Q.fin_fin_trunc T⟩

lemma
    GCAmbien.existsfin_algaug_finalgtrunc
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    {A : GCAmbien (p := p) (Γ := Γ) s hs}
    (T : A.FAAugtru n) :
    ∃ Q :
      GAAug
        (p := p) (Γ := Γ) (s := s) (hs := hs) n A,
      Finite Q.augmentationQuotient := by
  rcases dense_completed_algebraic
      (p := p) (Γ := Γ) (s := s) (hs := hs) n A with ⟨Q⟩
  exact ⟨Q, Q.fin_fin_algtrunc T⟩

lemma DCAlg.fin_fin_trunc
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    {A : GCAmbien (p := p) (Γ := Γ) s hs}
    (Q :
      DCAlg
        (p := p) (Γ := Γ) (s := s) (hs := hs) n A)
    (T : A.FCAugtru n) :
    Finite Q.augmentationQuotient := by
  let Qalg :
      GAAug
        (p := p) (Γ := Γ) (s := s) (hs := hs) n A :=
    { augmentationQuotient := Q.augmentationQuotient
      instQuotientRing := Q.instQuotientRing
      instQuotientAlgebra := Q.instQuotientAlgebra
      quotientMap := Q.quotientMap
      quotientMap_surjective := Q.quotientMap_surjective
      quotientMap_ker := Q.quotientMap_ker }
  exact Qalg.fin_fin_trunc T

lemma
    DCAlg.fin_fin_algtrunc
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    {A : GCAmbien (p := p) (Γ := Γ) s hs}
    (Q :
      DCAlg
        (p := p) (Γ := Γ) (s := s) (hs := hs) n A)
    (T : A.FAAugtru n) :
    Finite Q.augmentationQuotient := by
  let Qalg :
      GAAug
        (p := p) (Γ := Γ) (s := s) (hs := hs) n A :=
    { augmentationQuotient := Q.augmentationQuotient
      instQuotientRing := Q.instQuotientRing
      instQuotientAlgebra := Q.instQuotientAlgebra
      quotientMap := Q.quotientMap
      quotientMap_surjective := Q.quotientMap_surjective
      quotientMap_ker := Q.quotientMap_ker }
  exact Qalg.fin_fin_algtrunc T

lemma GCAmbien.closed_augpower_contkernel
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    {A : GCAmbien (p := p) (Γ := Γ) s hs}
    (K : A.ContAugPowerkernel n) :
    A.ClosedAugPower n := by
  letI := K.probeTopology
  letI := K.probeT2
  letI := K.instProbeRing
  have hzero_closed : IsClosed ({0} : Set K.quotientProbe) := by
    exact isClosed_singleton
  have hpreimage : IsClosed (K.probeMap ⁻¹' ({0} : Set K.quotientProbe)) := by
    exact hzero_closed.preimage K.probeMap_continuous
  have hset :
      ((A.augmentationIdeal ^ n : Ideal A.completedGroupAlgebra) :
          Set A.completedGroupAlgebra) =
        K.probeMap ⁻¹' ({0} : Set K.quotientProbe) := by
    ext x
    constructor
    · intro hx
      have hxker : x ∈ RingHom.ker K.probeMap := by
        rwa [K.probeMap_ker]
      have hxzero : K.probeMap x = 0 := by
        simpa [RingHom.mem_ker] using hxker
      exact hxzero
    · intro hx
      have hxzero : K.probeMap x = 0 := by
        simpa using hx
      have hxker : x ∈ RingHom.ker K.probeMap := by
        simpa [RingHom.mem_ker] using hxzero
      rwa [K.probeMap_ker] at hxker
  change
    IsClosed ((A.augmentationIdeal ^ n : Ideal A.completedGroupAlgebra) :
      Set A.completedGroupAlgebra)
  rw [hset]
  exact hpreimage

lemma GCAmbien.closed_augpower_fintrunc
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    {A : GCAmbien (p := p) (Γ := Γ) s hs}
    (T : A.FCAugtru n) :
    A.ClosedAugPower n := by
  let K : A.ContAugPowerkernel n :=
    T.cont_aug_powerkernel
  have hclosed : A.ClosedAugPower n :=
    A.closed_augpower_contkernel K
  exact hclosed

lemma GCAmbien.aug_idealeq_preimzero
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (A : GCAmbien (p := p) (Γ := Γ) s hs) :
    (A.augmentationIdeal : Set A.completedGroupAlgebra) =
      A.augmentationMap ⁻¹' ({0} : Set (ZMod p)) := by
  ext x
  constructor
  · intro hx
    have hxker : x ∈ RingHom.ker A.augmentationMap.toRingHom := by
      simpa [A.augmentation_ideal_ker] using hx
    have hxzero : A.augmentationMap.toRingHom x = 0 := by
      simpa [RingHom.mem_ker] using hxker
    exact hxzero
  · intro hx
    have hxzero : A.augmentationMap.toRingHom x = 0 := by
      simpa using hx
    have hxker : x ∈ RingHom.ker A.augmentationMap.toRingHom := by
      simpa [RingHom.mem_ker] using hxzero
    simpa [A.augmentation_ideal_ker] using hxker

lemma GCAmbien.aug_ideal_closed
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (A : GCAmbien (p := p) (Γ := Γ) s hs) :
    IsClosed (A.augmentationIdeal : Set A.completedGroupAlgebra) := by
  have hzero_closed : IsClosed ({0} : Set (ZMod p)) := by
    exact isClosed_singleton
  have hpreimage :
      IsClosed (A.augmentationMap ⁻¹' ({0} : Set (ZMod p))) := by
    exact hzero_closed.preimage A.augmentationMap_continuous
  have hset :
      (A.augmentationIdeal : Set A.completedGroupAlgebra) =
        A.augmentationMap ⁻¹' ({0} : Set (ZMod p)) :=
    A.aug_idealeq_preimzero
  simpa [hset] using hpreimage

def GCAmbien.fin_contaug_truncone
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (A : GCAmbien (p := p) (Γ := Γ) s hs) :
    A.FCAugtru 1 where
  quotientProbe := ULift.{u + 1} (ZMod p)
  probeTopology := inferInstance
  probeT2 := inferInstance
  probeDiscrete := inferInstance
  instProbeRing := inferInstance
  probeTopologicalRing := inferInstance
  instProbeFinite := inferInstance
  probeMap :=
    (ULift.ringEquiv.symm.toRingHom : ZMod p →+* ULift.{u + 1} (ZMod p)).comp
      A.augmentationMap.toRingHom
  probeMap_continuous := by
    exact continuous_uliftUp.comp A.augmentationMap_continuous
  probeMap_ker := by
    ext x
    constructor
    · intro hx
      have hxzero : A.augmentationMap.toRingHom x = 0 := by
        have hker :
            ((ULift.ringEquiv.symm.toRingHom : ZMod p →+* ULift.{u + 1} (ZMod p)).comp
                A.augmentationMap.toRingHom) x = 0 := by
          simpa [RingHom.mem_ker] using hx
        have hdown := congr_arg ULift.down hker
        simpa using hdown
      have hxker : x ∈ RingHom.ker A.augmentationMap.toRingHom := by
        simpa [RingHom.mem_ker] using hxzero
      have hxI : x ∈ A.augmentationIdeal := by
        simpa [A.augmentation_ideal_ker] using hxker
      simpa [Submodule.pow_one] using hxI
    · intro hx
      have hxI : x ∈ A.augmentationIdeal := by
        simpa [Submodule.pow_one] using hx
      have hxker : x ∈ RingHom.ker A.augmentationMap.toRingHom := by
        simpa [A.augmentation_ideal_ker] using hxI
      have hxzero : A.augmentationMap.toRingHom x = 0 := by
        simpa [RingHom.mem_ker] using hxker
      rw [RingHom.mem_ker]
      apply ULift.ext
      simpa using hxzero

def GCAmbien.cont_augpower_kernelone
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (A : GCAmbien (p := p) (Γ := Γ) s hs) :
    A.ContAugPowerkernel 1 :=
  A.fin_contaug_truncone.cont_aug_powerkernel

lemma GCAmbien.closed_aug_powerone
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (A : GCAmbien (p := p) (Γ := Γ) s hs) :
    A.ClosedAugPower 1 := by
  have T : A.FCAugtru 1 :=
    A.fin_contaug_truncone
  have hclosed : A.ClosedAugPower 1 :=
    A.closed_augpower_fintrunc T
  exact hclosed

lemma nat_or_pos {n : ℕ} (hn : 0 < n) :
    n = 1 ∨ 2 ≤ n := by
  cases n with
  | zero =>
      cases hn
  | succ n =>
      cases n with
      | zero =>
          left
          rfl
      | succ n =>
          right
          exact Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le n))

lemma ideal_open_mk
    {R : Type*} [TopologicalSpace R] [Ring R] [IsTopologicalRing R]
    (I : Ideal R) [I.IsTwoSided] :
    IsOpenQuotientMap (Ideal.Quotient.mk I) := by
  exact QuotientAddGroup.isOpenQuotientMap_mk

lemma ideal_prod_mk
    {R : Type*} [TopologicalSpace R] [Ring R] [IsTopologicalRing R]
    (I : Ideal R) [I.IsTwoSided] :
    Topology.IsQuotientMap
      (fun p : R × R => (Ideal.Quotient.mk I p.1, Ideal.Quotient.mk I p.2)) := by
  exact
    ((ideal_open_mk I).prodMap
        (ideal_open_mk I)).isQuotientMap

lemma ideal_topological_ring
    {R : Type*} [TopologicalSpace R] [Ring R] [IsTopologicalRing R]
    (I : Ideal R) [I.IsTwoSided] :
    IsTopologicalRing (R ⧸ I) := by
  refine
    { __ := QuotientAddGroup.instIsTopologicalAddGroup _
      continuous_mul := ?_ }
  exact
    (ideal_prod_mk I).continuous_iff.2
      (continuous_quot_mk.comp continuous_mul)

lemma t_space_closed
    {R : Type*} [TopologicalSpace R] [Ring R] [IsTopologicalRing R]
    (I : Ideal R) [I.IsTwoSided]
    (hI : IsClosed (I : Set R)) :
    T2Space (R ⧸ I) := by
  haveI : IsClosed (I.toAddSubgroup : Set R) := hI
  exact inferInstance

lemma idealQuotient_mkₐ_continuous
    {𝕜 R : Type*} [CommSemiring 𝕜] [TopologicalSpace R] [Ring R]
    [Algebra 𝕜 R] [IsTopologicalRing R]
    (I : Ideal R) [I.IsTwoSided] :
    Continuous (Ideal.Quotient.mkₐ 𝕜 I) := by
  exact continuous_quot_mk

lemma finite_ideal_open
    {R : Type*} [TopologicalSpace R] [Ring R] [IsTopologicalRing R] [CompactSpace R]
    (I : Ideal R) [I.IsTwoSided]
    (hI_open : IsOpen (I : Set R)) :
    Finite (R ⧸ I) := by
  have hfinite_add : Finite (R ⧸ I.toAddSubgroup) :=
    AddSubgroup.quotient_finite_of_isOpen I.toAddSubgroup hI_open
  simpa using hfinite_add

lemma ideal_open_closed
    {R : Type*} [TopologicalSpace R] [Ring R] [IsTopologicalRing R]
    (I : Ideal R) [I.IsTwoSided]
    (hI_closed : IsClosed (I : Set R))
    (hfinite : Finite (R ⧸ I)) :
    IsOpen (I : Set R) := by
  have hT2 : T2Space (R ⧸ I) :=
    t_space_closed I hI_closed
  letI : Finite (R ⧸ I) := hfinite
  letI : T2Space (R ⧸ I) := hT2
  haveI : DiscreteTopology (R ⧸ I) := inferInstance
  have hopen_zero : IsOpen ({0} : Set (R ⧸ I)) := by
    exact isOpen_discrete ({0} : Set (R ⧸ I))
  have hpreimage :
      IsOpen ((Ideal.Quotient.mk I) ⁻¹' ({0} : Set (R ⧸ I))) := by
    exact hopen_zero.preimage continuous_quot_mk
  have hset :
      (I : Set R) = (Ideal.Quotient.mk I) ⁻¹' ({0} : Set (R ⧸ I)) := by
    ext x
    constructor
    · intro hx
      change Ideal.Quotient.mk I x = 0
      exact Ideal.Quotient.eq_zero_iff_mem.mpr hx
    · intro hx
      change Ideal.Quotient.mk I x = 0 at hx
      exact Ideal.Quotient.eq_zero_iff_mem.mp hx
  simpa [hset] using hpreimage

structure DGFam
    {R : Type u} [Ring R] (I : Ideal R) : Type (u + 1) where
  index : Type u
  [finite_index : Fintype index]
  generator : index → R
  generator_mem : ∀ i : index, generator i ∈ I
  spans :
    ∀ x : R, x ∈ I ↔
      ∃ coeff : index → R,
        (∑ i : index, coeff i * generator i) = x

attribute [instance] DGFam.finite_index

def DGFam.eval
    {R : Type u} [Ring R] {I : Ideal R}
    (G : DGFam I) :
    (G.index → R) → R :=
  fun coeff => ∑ i : G.index, coeff i * G.generator i

lemma DGFam.range_eval
    {R : Type u} [Ring R] {I : Ideal R}
    (G : DGFam I) :
    Set.range G.eval = (I : Set R) := by
  classical
  ext x
  constructor
  · rintro ⟨coeff, hcoeff⟩
    have hxmem : x ∈ I := by
      exact
        (G.spans x).2
          ⟨coeff, by
            simpa [DGFam.eval] using hcoeff⟩
    exact hxmem
  · intro hx
    rcases (G.spans x).1 hx with ⟨coeff, hcoeff⟩
    exact ⟨coeff, by
      simpa [DGFam.eval] using hcoeff⟩

lemma DGFam.eval_continuous
    {R : Type u} [TopologicalSpace R] [Ring R] [IsTopologicalRing R] {I : Ideal R}
    (G : DGFam I) :
    Continuous G.eval := by
  classical
  change Continuous fun coeff : G.index → R =>
    ∑ i : G.index, coeff i * G.generator i
  exact
    continuous_finsetSum Finset.univ fun i _hi =>
      (continuous_apply i).mul continuous_const

lemma DGFam.isClosed_ideal
    {R : Type u} [TopologicalSpace R] [Ring R] [IsTopologicalRing R]
    [CompactSpace R] [T2Space R]
    {I : Ideal R}
    (G : DGFam I) :
    IsClosed (I : Set R) := by
  classical
  let evalMap : (G.index → R) → R := G.eval
  have hcontinuous : Continuous evalMap := by
    simpa [evalMap] using G.eval_continuous
  have hcompact_image : IsCompact (evalMap '' (Set.univ : Set (G.index → R))) := by
    exact isCompact_univ.image hcontinuous
  have hclosed_image :
      IsClosed (evalMap '' (Set.univ : Set (G.index → R))) := by
    exact hcompact_image.isClosed
  have himage :
      evalMap '' (Set.univ : Set (G.index → R)) = (I : Set R) := by
    ext x
    constructor
    · rintro ⟨coeff, _hcoeff, hx⟩
      have hxrange : x ∈ Set.range G.eval := by
        exact ⟨coeff, by
          simpa [evalMap] using hx⟩
      simpa [G.range_eval] using hxrange
    · intro hx
      have hxrange : x ∈ Set.range G.eval := by
        simpa [G.range_eval] using hx
      rcases hxrange with ⟨coeff, hcoeff⟩
      exact ⟨coeff, Set.mem_univ coeff, by
        simpa [evalMap] using hcoeff⟩
  simpa [himage] using hclosed_image

structure TGFam
    {R : Type u} [TopologicalSpace R] [Ring R] (I : Ideal R) : Type (u + 1) where
  index : Type u
  [finite_index : Fintype index]
  generator : index → R
  generator_mem : ∀ i : index, generator i ∈ I
  dense_span :
    (I : Set R) ⊆
      closure
        (Set.range
          (fun coeff : index → R =>
            ∑ i : index, coeff i * generator i))

attribute [instance] TGFam.finite_index

def TGFam.eval
    {R : Type u} [TopologicalSpace R] [Ring R] {I : Ideal R}
    (G : TGFam I) :
    (G.index → R) → R :=
  fun coeff => ∑ i : G.index, coeff i * G.generator i

lemma TGFam.range_eval_subset
    {R : Type u} [TopologicalSpace R] [Ring R] {I : Ideal R}
    (G : TGFam I) :
    Set.range G.eval ⊆ (I : Set R) := by
  classical
  rintro x ⟨coeff, hxcoeff⟩
  rw [← hxcoeff]
  change (∑ i : G.index, coeff i * G.generator i) ∈ I
  exact
    Ideal.sum_mem I fun i _hi =>
      I.mul_mem_left (coeff i) (G.generator_mem i)

lemma TGFam.ideal_subsetclosure_rangeeval
    {R : Type u} [TopologicalSpace R] [Ring R] {I : Ideal R}
    (G : TGFam I) :
    (I : Set R) ⊆ closure (Set.range G.eval) := by
  classical
  simpa [TGFam.eval]
    using G.dense_span

lemma TGFam.eval_continuous
    {R : Type u} [TopologicalSpace R] [Ring R] [IsTopologicalRing R] {I : Ideal R}
    (G : TGFam I) :
    Continuous G.eval := by
  classical
  change Continuous fun coeff : G.index → R =>
    ∑ i : G.index, coeff i * G.generator i
  exact
    continuous_finsetSum Finset.univ fun i _hi =>
      (continuous_apply i).mul continuous_const

lemma TGFam.compact_range_eval
    {R : Type u} [TopologicalSpace R] [Ring R] [IsTopologicalRing R]
    [CompactSpace R]
    {I : Ideal R}
    (G : TGFam I) :
    IsCompact (Set.range G.eval) := by
  classical
  let evalMap : (G.index → R) → R := G.eval
  have hcontinuous : Continuous evalMap := by
    simpa [evalMap] using G.eval_continuous
  have hcompact_image :
      IsCompact (evalMap '' (Set.univ : Set (G.index → R))) := by
    exact isCompact_univ.image hcontinuous
  have himage :
      evalMap '' (Set.univ : Set (G.index → R)) = Set.range G.eval := by
    ext x
    constructor
    · rintro ⟨coeff, _hcoeff, hx⟩
      exact ⟨coeff, by
        simpa [evalMap] using hx⟩
    · rintro ⟨coeff, hxcoeff⟩
      exact ⟨coeff, Set.mem_univ coeff, by
        simpa [evalMap] using hxcoeff⟩
  simpa [himage] using hcompact_image

lemma TGFam.closed_range_eval
    {R : Type u} [TopologicalSpace R] [Ring R] [IsTopologicalRing R]
    [CompactSpace R] [T2Space R]
    {I : Ideal R}
    (G : TGFam I) :
    IsClosed (Set.range G.eval) := by
  exact G.compact_range_eval.isClosed

lemma TGFam.isClosed_ideal
    {R : Type u} [TopologicalSpace R] [Ring R] [IsTopologicalRing R]
    [CompactSpace R] [T2Space R]
    {I : Ideal R}
    (G : TGFam I) :
    IsClosed (I : Set R) := by
  classical
  have hclosed_range : IsClosed (Set.range G.eval) :=
    G.closed_range_eval
  have hclosure :
      closure (Set.range G.eval) = Set.range G.eval :=
    hclosed_range.closure_eq
  have hI_subset_range : (I : Set R) ⊆ Set.range G.eval := by
    intro x hx
    have hxclosure : x ∈ closure (Set.range G.eval) :=
      G.ideal_subsetclosure_rangeeval hx
    simpa [hclosure] using hxclosure
  have hset : (I : Set R) = Set.range G.eval := by
    exact Set.Subset.antisymm hI_subset_range G.range_eval_subset
  simpa [hset] using hclosed_range

lemma
    GTAug.open_aug_powerfin
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    {A : GCAmbien (p := p) (Γ := Γ) s hs}
    {Q :
      GAAug
        (p := p) (Γ := Γ) (s := s) (hs := hs) n A}
    (T :
      GTAug
        (p := p) (Γ := Γ) (s := s) (hs := hs) Q)
    (hfinite : Finite Q.augmentationQuotient) :
    IsOpen ((A.augmentationIdeal ^ n : Ideal A.completedGroupAlgebra) :
      Set A.completedGroupAlgebra) := by
  letI : TopologicalSpace Q.augmentationQuotient := T.quotientTopology
  letI : T2Space Q.augmentationQuotient := T.quotientT2
  letI : Finite Q.augmentationQuotient := hfinite
  haveI : DiscreteTopology Q.augmentationQuotient := inferInstance
  have hopen_zero : IsOpen ({0} : Set Q.augmentationQuotient) := by
    exact isOpen_discrete ({0} : Set Q.augmentationQuotient)
  have hpreimage :
      IsOpen (Q.quotientMap ⁻¹' ({0} : Set Q.augmentationQuotient)) := by
    exact hopen_zero.preimage T.quotientMap_continuous
  have hset :
      ((A.augmentationIdeal ^ n : Ideal A.completedGroupAlgebra) :
          Set A.completedGroupAlgebra) =
        Q.quotientMap ⁻¹' ({0} : Set Q.augmentationQuotient) := by
    ext x
    constructor
    · intro hx
      have hxker : x ∈ RingHom.ker Q.quotientMap.toRingHom := by
        rw [Q.quotientMap_ker]
        exact hx
      have hxzero : Q.quotientMap.toRingHom x = 0 := by
        simpa [RingHom.mem_ker] using hxker
      simpa using hxzero
    · intro hx
      have hxzero : Q.quotientMap.toRingHom x = 0 := by
        simpa using hx
      have hxker : x ∈ RingHom.ker Q.quotientMap.toRingHom := by
        simpa [RingHom.mem_ker] using hxzero
      rw [Q.quotientMap_ker] at hxker
      exact hxker
  simpa [hset] using hpreimage

lemma
    GCAmbien.openaug_powerfin_topoaugquot
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    {A : GCAmbien (p := p) (Γ := Γ) s hs}
    (h :
      ∃ Q :
        GAAug
          (p := p) (Γ := Γ) (s := s) (hs := hs) n A,
        Finite Q.augmentationQuotient ∧
          Nonempty
            (GTAug
              (p := p) (Γ := Γ) (s := s) (hs := hs) Q)) :
    IsOpen ((A.augmentationIdeal ^ n : Ideal A.completedGroupAlgebra) :
      Set A.completedGroupAlgebra) := by
  rcases h with ⟨Q, hfiniteQ, hTop⟩
  rcases hTop with ⟨Top⟩
  exact Top.open_aug_powerfin hfiniteQ

lemma
    GCAmbien.existsfin_algaug_openaugpower
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (A : GCAmbien (p := p) (Γ := Γ) s hs)
    (hopen :
      IsOpen ((A.augmentationIdeal ^ n : Ideal A.completedGroupAlgebra) :
        Set A.completedGroupAlgebra)) :
    ∃ Q :
      GAAug
        (p := p) (Γ := Γ) (s := s) (hs := hs) n A,
      Finite Q.augmentationQuotient := by
  have haugmentation_two_sided : A.augmentationIdeal.IsTwoSided := by
    rw [A.augmentation_ideal_ker]
    infer_instance
  letI : A.augmentationIdeal.IsTwoSided := haugmentation_two_sided
  let I : Ideal A.completedGroupAlgebra := A.augmentationIdeal ^ n
  have hI_two_sided : I.IsTwoSided := by
    dsimp [I]
    infer_instance
  letI : I.IsTwoSided := hI_two_sided
  have hI_open : IsOpen (I : Set A.completedGroupAlgebra) := by
    simpa [I] using hopen
  let quotientMap : A.completedGroupAlgebra →ₐ[ZMod p] A.completedGroupAlgebra ⧸ I :=
    Ideal.Quotient.mkₐ (ZMod p) I
  have hsurjective : Function.Surjective quotientMap := by
    simpa [quotientMap] using Ideal.Quotient.mkₐ_surjective (ZMod p) I
  have hker : RingHom.ker quotientMap.toRingHom = A.augmentationIdeal ^ n := by
    simp [quotientMap, I]
  have hfinite : Finite (A.completedGroupAlgebra ⧸ I) :=
    finite_ideal_open I hI_open
  let Q :
      GAAug
        (p := p) (Γ := Γ) (s := s) (hs := hs) n A :=
    { augmentationQuotient := A.completedGroupAlgebra ⧸ I
      instQuotientRing := inferInstance
      instQuotientAlgebra := inferInstance
      quotientMap := quotientMap
      quotientMap_surjective := hsurjective
      quotientMap_ker := hker }
  refine ⟨Q, ?_⟩
  dsimp [Q]
  exact hfinite

lemma
    GCAmbien.existsfin_contaug_openaugpower
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (A : GCAmbien (p := p) (Γ := Γ) s hs)
    (hopen :
      IsOpen ((A.augmentationIdeal ^ n : Ideal A.completedGroupAlgebra) :
        Set A.completedGroupAlgebra)) :
    Nonempty (A.FCAugtru n) := by
  rcases
      A.existsfin_algaug_openaugpower
        (p := p) (Γ := Γ) (s := s) (hs := hs) hopen with
    ⟨Q, hfiniteQ⟩
  letI : Finite Q.augmentationQuotient := hfiniteQ
  let Talg : A.FAAugtru n :=
    Q.fin_alg_augtrunc
  have hker_open :
      IsOpen ((RingHom.ker Talg.probeMap : Ideal A.completedGroupAlgebra) :
        Set A.completedGroupAlgebra) := by
    simpa [Talg] using
      Q.open_keropen_augpower
        hopen
  let HTop : Talg.DiscreteContTopo :=
    Talg.discrete_conttopo_openker hker_open
  exact ⟨Talg.fin_cont_augtrunc HTop⟩

lemma
    GCAmbien.contaug_powerkernel_openaugpower
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (A : GCAmbien (p := p) (Γ := Γ) s hs)
    (hopen :
      IsOpen ((A.augmentationIdeal ^ n : Ideal A.completedGroupAlgebra) :
        Set A.completedGroupAlgebra)) :
    Nonempty (A.ContAugPowerkernel n) := by
  rcases
      A.existsfin_contaug_openaugpower
        (p := p) (Γ := Γ) (s := s) (hs := hs) hopen with
    ⟨T⟩
  exact ⟨T.cont_aug_powerkernel⟩

lemma GCAmbien.topoaug_quotclosed_augpower
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (A : GCAmbien (p := p) (Γ := Γ) s hs)
    (hclosed : A.ClosedAugPower n) :
    A.TopoAugQuot n := by
  have haugmentation_two_sided : A.augmentationIdeal.IsTwoSided := by
    rw [A.augmentation_ideal_ker]
    infer_instance
  letI : A.augmentationIdeal.IsTwoSided := haugmentation_two_sided
  let I : Ideal A.completedGroupAlgebra := A.augmentationIdeal ^ n
  have hI_two_sided : I.IsTwoSided := by
    dsimp [I]
    infer_instance
  letI : I.IsTwoSided := hI_two_sided
  have hI_closed : IsClosed (I : Set A.completedGroupAlgebra) := by
    simpa [I, GCAmbien.ClosedAugPower]
      using hclosed
  let quotientMap : A.completedGroupAlgebra →ₐ[ZMod p] A.completedGroupAlgebra ⧸ I :=
    Ideal.Quotient.mkₐ (ZMod p) I
  have hsurjective : Function.Surjective quotientMap := by
    simpa [quotientMap] using Ideal.Quotient.mkₐ_surjective (ZMod p) I
  have hker : RingHom.ker quotientMap.toRingHom = A.augmentationIdeal ^ n := by
    simp [quotientMap, I]
  let Q :
      GAAug
        (p := p) (Γ := Γ) (s := s) (hs := hs) n A :=
    { augmentationQuotient := A.completedGroupAlgebra ⧸ I
      instQuotientRing := inferInstance
      instQuotientAlgebra := inferInstance
      quotientMap := quotientMap
      quotientMap_surjective := hsurjective
      quotientMap_ker := hker }
  refine ⟨Q, ?_⟩
  letI : TopologicalSpace Q.augmentationQuotient :=
    inferInstanceAs (TopologicalSpace (A.completedGroupAlgebra ⧸ I))
  have hT2 :
      T2Space Q.augmentationQuotient := by
    dsimp [Q]
    exact t_space_closed I hI_closed
  have htopRing :
      IsTopologicalRing Q.augmentationQuotient := by
    dsimp [Q]
    exact ideal_topological_ring I
  have hcontinuous : Continuous Q.quotientMap := by
    dsimp [Q, quotientMap]
    exact idealQuotient_mkₐ_continuous (𝕜 := ZMod p) I
  exact
    ⟨{ quotientTopology := inferInstance
       quotientT2 := hT2
       quotientTopologicalRing := htopRing
       quotientMap_continuous := hcontinuous }⟩

structure GCAmbien.FCAugpow
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (n : ℕ)
    (A : GCAmbien (p := p) (Γ := Γ) s hs) :
    Type (u + 2) where
  algebraicQuotient :
    GAAug
      (p := p) (Γ := Γ) (s := s) (hs := hs) n A
  algebraicQuotient_finite : Finite algebraicQuotient.augmentationQuotient
  augmentationPower_closed : A.ClosedAugPower n

lemma
    GCAmbien.finclosed_augpowerfin_algquotclosed
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (A : GCAmbien (p := p) (Γ := Γ) s hs)
    (Q :
      GAAug
        (p := p) (Γ := Γ) (s := s) (hs := hs) n A)
    (hfiniteQ : Finite Q.augmentationQuotient)
    (hclosed : A.ClosedAugPower n) :
    Nonempty (A.FCAugpow n) := by
  let D : A.FCAugpow n :=
    { algebraicQuotient := Q
      algebraicQuotient_finite := hfiniteQ
      augmentationPower_closed := hclosed }
  exact ⟨D⟩

lemma
    GCAmbien.FCAugpow.exists_fintopo_augquot
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    {A : GCAmbien (p := p) (Γ := Γ) s hs}
    (D : A.FCAugpow n) :
    ∃ Q :
      GAAug
        (p := p) (Γ := Γ) (s := s) (hs := hs) n A,
      Finite Q.augmentationQuotient ∧
        Nonempty
          (GTAug
            (p := p) (Γ := Γ) (s := s) (hs := hs) Q) := by
  have htop : A.TopoAugQuot n :=
    A.topoaug_quotclosed_augpower
      D.augmentationPower_closed
  rcases htop with ⟨Qtop, hTop⟩
  letI : Finite D.algebraicQuotient.augmentationQuotient :=
    D.algebraicQuotient_finite
  let Tfinite : A.FAAugtru n :=
    D.algebraicQuotient.fin_alg_augtrunc
  have hfinite_top : Finite Qtop.augmentationQuotient := by
    exact Qtop.fin_fin_algtrunc Tfinite
  exact ⟨Qtop, hfinite_top, hTop⟩

lemma
    GCAmbien.existsfin_topoaug_quotfinclosed
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    {A : GCAmbien (p := p) (Γ := Γ) s hs}
    (hdata : Nonempty (A.FCAugpow n)) :
    ∃ Q :
      GAAug
        (p := p) (Γ := Γ) (s := s) (hs := hs) n A,
      Finite Q.augmentationQuotient ∧
        Nonempty
          (GTAug
            (p := p) (Γ := Γ) (s := s) (hs := hs) Q) := by
  rcases hdata with ⟨D⟩
  exact D.exists_fintopo_augquot

lemma
    gens_closed_aug
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} (s : Fin d → Γ)
    (hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤) :
    ∃ A : GCAmbien (p := p) (Γ := Γ) s hs,
      A.DenseAlgebraSpan ∧
        A.ClosedAugPower 1 := by
  rcases completed_ambient_span
      (p := p) (Γ := Γ) s hs with ⟨A, hdense⟩
  have hclosed_one : A.ClosedAugPower 1 := by
    exact A.closed_aug_powerone
  exact ⟨A, hdense, hclosed_one⟩

lemma GCAmbien.closedaug_powernonempty_contkernel
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (A : GCAmbien (p := p) (Γ := Γ) s hs)
    (hK : Nonempty (A.ContAugPowerkernel n)) :
    A.ClosedAugPower n := by
  rcases hK with ⟨K⟩
  have hclosed_from_kernel :
      A.ClosedAugPower n := by
    exact A.closed_augpower_contkernel K
  exact hclosed_from_kernel

lemma GCAmbien.closedaug_poweropen_augpower
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (A : GCAmbien (p := p) (Γ := Γ) s hs)
    (hopen :
      IsOpen ((A.augmentationIdeal ^ n : Ideal A.completedGroupAlgebra) :
        Set A.completedGroupAlgebra)) :
    A.ClosedAugPower n := by
  have hK : Nonempty (A.ContAugPowerkernel n) := by
    exact
      A.contaug_powerkernel_openaugpower
        (p := p) (Γ := Γ) (s := s) (hs := hs) hopen
  have hclosed :
      A.ClosedAugPower n := by
    exact A.closedaug_powernonempty_contkernel hK
  exact hclosed

lemma
    GCAmbien.topoaug_quotnonempty_contkernel
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (A : GCAmbien (p := p) (Γ := Γ) s hs)
    (hK : Nonempty (A.ContAugPowerkernel n)) :
    A.TopoAugQuot n := by
  have hclosed :
      A.ClosedAugPower n := by
    exact A.closedaug_powernonempty_contkernel hK
  have hquotient :
      A.TopoAugQuot n := by
    exact A.topoaug_quotclosed_augpower hclosed
  exact hquotient

lemma
    GCAmbien.contaug_powerkernel_topoaugquot
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    {A : GCAmbien (p := p) (Γ := Γ) s hs}
    (hQ : A.TopoAugQuot n) :
    Nonempty (A.ContAugPowerkernel n) := by
  rcases hQ with ⟨Q, hTop⟩
  rcases hTop with ⟨Top⟩
  letI : TopologicalSpace Q.augmentationQuotient := Top.quotientTopology
  letI : T2Space Q.augmentationQuotient := Top.quotientT2
  letI : Ring Q.augmentationQuotient := Q.instQuotientRing
  let liftedMap :
      A.completedGroupAlgebra →+* ULift.{u + 1} Q.augmentationQuotient :=
    (ULift.ringEquiv.symm.toRingHom :
        Q.augmentationQuotient →+* ULift.{u + 1} Q.augmentationQuotient).comp
      Q.quotientMap.toRingHom
  have hlifted_continuous : Continuous liftedMap := by
    simpa [liftedMap] using
      (continuous_uliftUp.comp Top.quotientMap_continuous)
  have hlifted_ker :
      RingHom.ker liftedMap = A.augmentationIdeal ^ n := by
    ext x
    constructor
    · intro hx
      have hxzero_lift : liftedMap x = 0 := by
        simpa [RingHom.mem_ker] using hx
      have hxzero : Q.quotientMap.toRingHom x = 0 := by
        have hdown := congr_arg ULift.down hxzero_lift
        simpa [liftedMap] using hdown
      have hxker : x ∈ RingHom.ker Q.quotientMap.toRingHom := by
        simpa [RingHom.mem_ker] using hxzero
      rw [← Q.quotientMap_ker]
      exact hxker
    · intro hxpow
      have hxker : x ∈ RingHom.ker Q.quotientMap.toRingHom := by
        rw [Q.quotientMap_ker]
        exact hxpow
      have hxzero : Q.quotientMap.toRingHom x = 0 := by
        simpa [RingHom.mem_ker] using hxker
      rw [RingHom.mem_ker]
      apply ULift.ext
      simpa [liftedMap] using hxzero
  refine ⟨?_⟩
  exact
    { quotientProbe := ULift.{u + 1} Q.augmentationQuotient
      probeTopology := inferInstance
      probeT2 := inferInstance
      instProbeRing := inferInstance
      probeMap := liftedMap
      probeMap_continuous := hlifted_continuous
      probeMap_ker := hlifted_ker }

def GCAmbien.finalg_augtrunc_finidealquot
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (A : GCAmbien (p := p) (Γ := Γ) s hs)
    (hfinite :
      Finite (A.completedGroupAlgebra ⧸
        (A.augmentationIdeal ^ n : Ideal A.completedGroupAlgebra))) :
    A.FAAugtru n := by
  have haugmentation_two_sided : A.augmentationIdeal.IsTwoSided := by
    rw [A.augmentation_ideal_ker]
    infer_instance
  letI : A.augmentationIdeal.IsTwoSided := haugmentation_two_sided
  let I : Ideal A.completedGroupAlgebra := A.augmentationIdeal ^ n
  have hI_two_sided : I.IsTwoSided := by
    dsimp [I]
    infer_instance
  letI : I.IsTwoSided := hI_two_sided
  let quotientMap : A.completedGroupAlgebra →+* A.completedGroupAlgebra ⧸ I :=
    Ideal.Quotient.mk I
  let liftedMap :
      A.completedGroupAlgebra →+* ULift.{u + 1} (A.completedGroupAlgebra ⧸ I) :=
    (ULift.ringEquiv.symm.toRingHom :
        (A.completedGroupAlgebra ⧸ I) →+*
          ULift.{u + 1} (A.completedGroupAlgebra ⧸ I)).comp quotientMap
  have hker :
      RingHom.ker liftedMap = A.augmentationIdeal ^ n := by
    ext x
    constructor
    · intro hx
      have hxzero_lift : liftedMap x = 0 := by
        simpa [RingHom.mem_ker] using hx
      have hxzero : quotientMap x = 0 := by
        have hdown := congr_arg ULift.down hxzero_lift
        simpa [liftedMap] using hdown
      have hxI : x ∈ I := by
        change Ideal.Quotient.mk I x = 0 at hxzero
        exact Ideal.Quotient.eq_zero_iff_mem.mp hxzero
      simpa [I] using hxI
    · intro hxpow
      have hxI : x ∈ I := by
        simpa [I] using hxpow
      have hxzero : quotientMap x = 0 := by
        change Ideal.Quotient.mk I x = 0
        exact Ideal.Quotient.eq_zero_iff_mem.mpr hxI
      rw [RingHom.mem_ker]
      apply ULift.ext
      simpa [liftedMap] using hxzero
  letI : Finite (A.completedGroupAlgebra ⧸ I) := by
    simpa [I] using hfinite
  letI : Finite (ULift.{u + 1} (A.completedGroupAlgebra ⧸ I)) := inferInstance
  exact
    { quotientProbe := ULift.{u + 1} (A.completedGroupAlgebra ⧸ I)
      instProbeRing := inferInstance
      instProbeFinite := inferInstance
      probeMap := liftedMap
      probeMap_ker := hker }

abbrev denseGeneratorsLetter (d : ℕ) : Type :=
  Fin d × Bool

def denseLetterElement
    {Γ : Type u} [Group Γ]
    {d : ℕ} (s : Fin d → Γ)
    (a : denseGeneratorsLetter d) : Γ :=
  if a.2 then s a.1 else (s a.1)⁻¹

end Submission
