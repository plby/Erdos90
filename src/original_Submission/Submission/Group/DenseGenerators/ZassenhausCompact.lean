import Mathlib
import Submission.Algebra.DenseGenerators.FiniteGroupAlgebra


open scoped Topology Pointwise

noncomputable section

namespace Submission

universe u
universe v w z

namespace DGTest

lemma target_zassenhaus
    {p : ℕ}
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ]
    (T : DGTest Γ)
    {n : ℕ}
    {g : Γ}
    (hg : g ∈ zassenhausFiltration p Γ n) :
    T.quotientMap g ∈ T.targetZassenhaus p n := by
  letI : Group T.quotientGroup := T.instGroup
  have hmem :
      T.quotientMap g ∈ zassenhausFiltration p T.quotientGroup n :=
    filtration_map_mem
      (p := p)
      (n := n)
      (f := T.quotientMap)
      hg
  simpa [targetZassenhaus] using hmem

end DGTest

structure DGSep
    (p : ℕ)
    (Γ : Type u) [Group Γ] [TopologicalSpace Γ]
    (n : ℕ) :
    Type (u + 1) where
  test_not :
    ∀ {g : Γ},
      g ∉ zassenhausFiltration p Γ n →
        ∃ T : DGTest Γ,
          T.quotientMap g ∉
            DGTest.targetZassenhaus T p n

namespace DGSep

lemma forall_test_images
    {p : ℕ}
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ]
    {n : ℕ}
    (H : DGSep p Γ n)
    {g : Γ}
    (himages :
      ∀ T : DGTest Γ,
        T.quotientMap g ∈
          DGTest.targetZassenhaus T p n) :
    g ∈ zassenhausFiltration p Γ n := by
  by_contra hgnot
  rcases H.test_not hgnot with ⟨T, hT⟩
  exact hT (himages T)

end DGSep

abbrev denseSelfQuotient
    (p : ℕ)
    (Γ : Type u) [Group Γ]
    (n : ℕ) :
    Type u :=
  Γ ⧸ zassenhausFiltration p Γ n

noncomputable instance instGeneratorsSelf
    (p : ℕ) [Fact p.Prime]
    (Γ : Type u) [Group Γ]
    (n : ℕ) :
    Group (denseSelfQuotient p Γ n) := by
  letI : (zassenhausFiltration p Γ n).Normal :=
    zassenhausFiltration_normal p Γ n
  dsimp [denseSelfQuotient]
  infer_instance

noncomputable def denseGeneratorsSelf
    (p : ℕ) [Fact p.Prime]
    (Γ : Type u) [Group Γ]
    (n : ℕ) :
    Γ →*
      denseSelfQuotient p Γ n := by
  letI : (zassenhausFiltration p Γ n).Normal :=
    zassenhausFiltration_normal p Γ n
  exact QuotientGroup.mk' (zassenhausFiltration p Γ n)

noncomputable def denseSelfTarget
    (p : ℕ) [Fact p.Prime]
    (Γ : Type u) [Group Γ]
    (n : ℕ) :
    Subgroup (denseSelfQuotient p Γ n) := by
  letI : (zassenhausFiltration p Γ n).Normal :=
    zassenhausFiltration_normal p Γ n
  exact
    zassenhausFiltration p
      (denseSelfQuotient p Γ n) n

lemma dense_zassenhaus_self
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ]
    {n : ℕ}
    (g : Γ) :
    denseGeneratorsSelf p Γ n g = 1 ↔
      g ∈ zassenhausFiltration p Γ n := by
  let D : Subgroup Γ := zassenhausFiltration p Γ n
  letI : D.Normal := by
    dsimp [D]
    exact zassenhausFiltration_normal p Γ n
  change
    (QuotientGroup.mk' D g : Γ ⧸ D) = 1 ↔
      g ∈ D
  exact QuotientGroup.eq_one_iff (N := D) g

structure STData
    (p : ℕ) [Fact p.Prime]
    (Γ : Type u) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ]
    (n : ℕ) :
    Type u where
  isOpen_zassenhaus :
    IsOpen ((zassenhausFiltration p Γ n : Subgroup Γ) : Set Γ)

namespace STData

lemma discreteTopology
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ]
    {n : ℕ}
    (H : STData p Γ n) :
    DiscreteTopology (denseSelfQuotient p Γ n) := by
  let D : Subgroup Γ := zassenhausFiltration p Γ n
  change DiscreteTopology (Γ ⧸ D)
  exact QuotientGroup.discreteTopology H.isOpen_zassenhaus

lemma finite_quotient
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ]
    {n : ℕ}
    (H : STData p Γ n) :
    Finite (denseSelfQuotient p Γ n) := by
  let D : Subgroup Γ := zassenhausFiltration p Γ n
  change Finite (Γ ⧸ D)
  exact D.quotient_finite_of_isOpen H.isOpen_zassenhaus

lemma quotientMap_continuous
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ]
    {n : ℕ}
    (_H : STData p Γ n) :
    Continuous
      (fun x : Γ =>
        denseGeneratorsSelf p Γ n x) := by
  let D : Subgroup Γ := zassenhausFiltration p Γ n
  letI : D.Normal := by
    dsimp [D]
    exact zassenhausFiltration_normal p Γ n
  change Continuous (fun x : Γ => (QuotientGroup.mk' D) x)
  change Continuous (QuotientGroup.mk : Γ → Γ ⧸ D)
  exact QuotientGroup.continuous_mk

noncomputable def finiteQuotientTest
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ]
    {n : ℕ}
    (H : STData p Γ n) :
    DGTest Γ := by
  letI : (zassenhausFiltration p Γ n).Normal :=
    zassenhausFiltration_normal p Γ n
  letI : Group (denseSelfQuotient p Γ n) := by
    dsimp [denseSelfQuotient]
    infer_instance
  letI : TopologicalSpace (denseSelfQuotient p Γ n) := by
    dsimp [denseSelfQuotient]
    infer_instance
  letI : DiscreteTopology (denseSelfQuotient p Γ n) :=
    H.discreteTopology
  letI : Finite (denseSelfQuotient p Γ n) :=
    H.finite_quotient
  exact
    { quotientGroup := denseSelfQuotient p Γ n
      instGroup := inferInstance
      instTopologicalSpace := inferInstance
      instDiscreteTopology := inferInstance
      instFinite := inferInstance
      quotientMap := denseGeneratorsSelf p Γ n
      quotientMap_continuous :=
        STData.quotientMap_continuous H }

end STData

structure DenseSelfData
    (p : ℕ) [Fact p.Prime]
    (Γ : Type u) [Group Γ]
    (n : ℕ) :
    Type u where
  target_eq_bot :
    denseSelfTarget p Γ n = ⊥

structure DCInput
    (p : ℕ) [Fact p.Prime]
    (Γ : Type u) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ]
    (n : ℕ) :
    Type u where
  isClosed_zassenhaus :
    IsClosed ((zassenhausFiltration p Γ n : Subgroup Γ) : Set Γ)
  finite_selfQuotient :
    Finite (denseSelfQuotient p Γ n)

namespace DCInput

lemma finiteIndex_zassenhaus
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ]
    {n : ℕ}
    (H : DCInput p Γ n) :
    (zassenhausFiltration p Γ n).FiniteIndex := by
  let D : Subgroup Γ := zassenhausFiltration p Γ n
  have hfinite_quotient : Finite (Γ ⧸ D) := by
    change Finite (denseSelfQuotient p Γ n)
    exact H.finite_selfQuotient
  letI : Finite (Γ ⧸ D) := hfinite_quotient
  change D.FiniteIndex
  exact Subgroup.finiteIndex_of_finite_quotient

lemma isOpen_zassenhaus
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ]
    {n : ℕ}
    (H : DCInput p Γ n) :
    IsOpen ((zassenhausFiltration p Γ n : Subgroup Γ) : Set Γ) := by
  let D : Subgroup Γ := zassenhausFiltration p Γ n
  have hclosed : IsClosed (D : Set Γ) := by
    simpa [D] using H.isClosed_zassenhaus
  have hfinite_index : D.FiniteIndex := by
    simpa [D] using H.finiteIndex_zassenhaus
  letI : D.FiniteIndex := hfinite_index
  exact D.isOpen_of_isClosed_of_finiteIndex hclosed

def toTopologyData
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ]
    {n : ℕ}
    (H : DCInput p Γ n) :
    STData p Γ n where
  isOpen_zassenhaus := H.isOpen_zassenhaus

end DCInput

def zGFact
    (p : ℕ)
    (Γ : Type u) [Group Γ]
    (n : ℕ)
    (x : Γ) :
    Prop :=
  ∃ l : List Γ,
    (∀ y ∈ l, y ∈ zassenhausGeneratorSet p Γ n) ∧
      l.prod = x

lemma generator_set_inv
    {p : ℕ}
    {Γ : Type u} [Group Γ]
    {n : ℕ}
    {x : Γ}
    (hx : x ∈ zassenhausGeneratorSet p Γ n) :
    x⁻¹ ∈ zassenhausGeneratorSet p Γ n := by
  rcases hx with ⟨i, j, y, hy, hbound, rfl⟩
  refine ⟨i, j, y⁻¹, ?_, hbound, ?_⟩
  · exact (Subgroup.lowerCentralSeries Γ i).inv_mem hy
  · simp

lemma zGFact.one
    {p : ℕ}
    {Γ : Type u} [Group Γ]
    {n : ℕ} :
    zGFact p Γ n 1 := by
  refine ⟨[], ?_, ?_⟩
  · intro y hy
    cases hy
  · simp

lemma zGFact.of_generator
    {p : ℕ}
    {Γ : Type u} [Group Γ]
    {n : ℕ}
    {x : Γ}
    (hx : x ∈ zassenhausGeneratorSet p Γ n) :
    zGFact p Γ n x := by
  refine ⟨[x], ?_, ?_⟩
  · intro y hy
    have hyx : y = x := by
      simpa using hy
    simpa [hyx] using hx
  · simp

lemma zGFact.mul
    {p : ℕ}
    {Γ : Type u} [Group Γ]
    {n : ℕ}
    {x y : Γ}
    (hx : zGFact p Γ n x)
    (hy : zGFact p Γ n y) :
    zGFact p Γ n (x * y) := by
  rcases hx with ⟨lx, hlx, hprod_x⟩
  rcases hy with ⟨ly, hly, hprod_y⟩
  refine ⟨lx ++ ly, ?_, ?_⟩
  · intro z hz
    rw [List.mem_append] at hz
    rcases hz with hz | hz
    · exact hlx z hz
    · exact hly z hz
  · simp [List.prod_append, hprod_x, hprod_y]

lemma zGFact.inv
    {p : ℕ}
    {Γ : Type u} [Group Γ]
    {n : ℕ}
    {x : Γ}
    (hx : zGFact p Γ n x) :
    zGFact p Γ n x⁻¹ := by
  rcases hx with ⟨l, hl, hprod⟩
  refine ⟨(l.map fun y => y⁻¹).reverse, ?_, ?_⟩
  · intro z hz
    rw [List.mem_reverse] at hz
    rcases List.mem_map.mp hz with ⟨y, hy, rfl⟩
    exact generator_set_inv (p := p) (n := n) (hl y hy)
  · rw [← hprod]
    exact (List.prod_inv_reverse l).symm

lemma zassenhaus_generator_filtration
    {p : ℕ}
    {Γ : Type u} [Group Γ]
    {n : ℕ}
    {x : Γ}
    (hx : x ∈ zassenhausGeneratorSet p Γ n) :
    x ∈ zassenhausFiltration p Γ n := by
  change
    x ∈ Subgroup.closure
      (zassenhausGeneratorSet p Γ n)
  exact
    Subgroup.subset_closure hx

lemma filtration_subset_factorization
    {p : ℕ}
    {Γ : Type u} [Group Γ]
    {n : ℕ} :
    (((zassenhausFiltration p Γ n : Subgroup Γ) : Set Γ)) ⊆
      {x : Γ | zGFact p Γ n x} := by
  intro x hx
  change x ∈ Subgroup.closure (zassenhausGeneratorSet p Γ n) at hx
  refine
    Subgroup.closure_induction
      (k := zassenhausGeneratorSet p Γ n)
      (p := fun g _ => zGFact p Γ n g)
      ?_
      ?_
      ?_
      ?_
      hx
  · intro y hy
    exact zGFact.of_generator
      (p := p)
      (n := n)
      hy
  · exact zGFact.one
      (p := p)
      (Γ := Γ)
      (n := n)
  · intro y z _hy _hz hfy hfz
    exact zGFact.mul hfy hfz
  · intro y _hy hfy
    exact zGFact.inv hfy

lemma generator_prod_filtration
    {p : ℕ}
    {Γ : Type u} [Group Γ]
    {n : ℕ}
    {l : List Γ}
    (hl : ∀ y ∈ l, y ∈ zassenhausGeneratorSet p Γ n) :
    l.prod ∈ zassenhausFiltration p Γ n := by
  induction l with
  | nil =>
      simp [zassenhausFiltration]
  | cons y ys ih =>
      have hy :
          y ∈ zassenhausFiltration p Γ n := by
        exact
          zassenhaus_generator_filtration
            (p := p)
            (n := n)
            (hl y (by simp))
      have hys :
          ys.prod ∈ zassenhausFiltration p Γ n := by
        exact ih fun z hz =>
          hl z (by simp [hz])
      exact
        (zassenhausFiltration p Γ n).mul_mem hy hys

lemma zGFact.mem_zassenhausFiltration
    {p : ℕ}
    {Γ : Type u} [Group Γ]
    {n : ℕ}
    {x : Γ}
    (hx : zGFact p Γ n x) :
    x ∈ zassenhausFiltration p Γ n := by
  rcases hx with ⟨l, hl, hprod⟩
  rw [← hprod]
  exact
    generator_prod_filtration
      (p := p)
      (n := n)
      hl

lemma filtration_topological_factorization
    {p : ℕ}
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    {n : ℕ}
    (hfactor :
      ∀ x : Γ,
        x ∈ (zassenhausFiltration p Γ n).topologicalClosure →
          zGFact p Γ n x) :
    (zassenhausFiltration p Γ n).topologicalClosure ≤
      zassenhausFiltration p Γ n := by
  intro x hx
  exact
    zGFact.mem_zassenhausFiltration
      (p := p)
      (n := n)
      (hfactor x hx)

lemma closed_topological_closure
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    (H : Subgroup Γ)
    (hle : H.topologicalClosure ≤ H) :
    IsClosed (H : Set Γ) := by
  have hclosure_eq :
      H.topologicalClosure = H := by
    exact le_antisymm hle H.le_topologicalClosure
  rw [← hclosure_eq]
  exact H.isClosed_topologicalClosure

lemma topological_subset_closed
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    {H : Subgroup Γ}
    {S : Set Γ}
    (hHS : ((H : Subgroup Γ) : Set Γ) ⊆ S)
    (hS : IsClosed S) :
    (((H.topologicalClosure : Subgroup Γ) : Set Γ)) ⊆ S := by
  rw [Subgroup.topologicalClosure_coe]
  exact closure_minimal hHS hS

def zassenhausProductImage
    {Γ : Type u} [Group Γ]
    {k : ℕ}
    (K : Fin k → Set Γ) :
    Set Γ :=
  {x : Γ | ∃ f : ∀ i : Fin k, K i,
      (List.ofFn fun i : Fin k => (f i : Γ)).prod = x}

lemma zassenhaus_product_image
    {Γ : Type u} [Group Γ]
    {k : ℕ}
    {K : Fin k → Set Γ}
    {x : Γ} :
    x ∈ zassenhausProductImage K ↔
      ∃ f : ∀ i : Fin k, K i,
        (List.ofFn fun i : Fin k => (f i : Γ)).prod = x := by
  rfl

lemma image_pointwise_prod
    {Γ : Type u} [Group Γ]
    {k : ℕ}
    (K : Fin k → Set Γ) :
    zassenhausProductImage K = (List.ofFn K).prod := by
  ext x
  simpa [zassenhausProductImage] using
    (Set.mem_prod_list_ofFn (a := x) (s := K)).symm

lemma compact_pointwise_prod
    {Γ : Type u} [Monoid Γ] [TopologicalSpace Γ] [ContinuousMul Γ]
    {l : List (Set Γ)}
    (hl : ∀ K ∈ l, IsCompact K) :
    IsCompact l.prod := by
  induction l with
  | nil =>
      simp
  | cons K Ks ih =>
      have hK : IsCompact K := by
        exact hl K (by simp)
      have hKs : IsCompact Ks.prod := by
        exact ih fun L hL =>
          hl L (by simp [hL])
      simpa [List.prod_cons] using hK.mul hKs

lemma zassenhaus_image_compact
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    {k : ℕ}
    {K : Fin k → Set Γ}
    (hK : ∀ i : Fin k, IsCompact (K i)) :
    IsCompact (zassenhausProductImage K) := by
  rw [image_pointwise_prod]
  exact
    compact_pointwise_prod
      (l := List.ofFn K)
      (by
        rw [List.forall_mem_ofFn_iff]
        exact hK)

lemma zassenhaus_image_closed
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [T2Space Γ]
    {k : ℕ}
    {K : Fin k → Set Γ}
    (hK : ∀ i : Fin k, IsCompact (K i)) :
    IsClosed (zassenhausProductImage K) := by
  exact
    (zassenhaus_image_compact
      (Γ := Γ)
      (K := K)
      hK).isClosed

def zassenhausUnionImage
    {Γ : Type u}
    {k : ℕ}
    (K : Fin k → Set Γ) :
    Set Γ :=
  ⋃ i : Fin k, K i

lemma zassenhaus_union_image
    {Γ : Type u}
    {k : ℕ}
    {K : Fin k → Set Γ}
    {x : Γ} :
    x ∈ zassenhausUnionImage K ↔
      ∃ i : Fin k, x ∈ K i := by
  simp [zassenhausUnionImage]

lemma union_image_compact
    {Γ : Type u} [TopologicalSpace Γ]
    {k : ℕ}
    {K : Fin k → Set Γ}
    (hK : ∀ i : Fin k, IsCompact (K i)) :
    IsCompact (zassenhausUnionImage K) := by
  dsimp [zassenhausUnionImage]
  exact isCompact_iUnion hK

lemma union_subset_forall
    {Γ : Type u}
    {k : ℕ}
    {K : Fin k → Set Γ}
    {S : Set Γ}
    (hK : ∀ i : Fin k, K i ⊆ S) :
    zassenhausUnionImage K ⊆ S := by
  intro x hx
  rcases (zassenhaus_union_image (K := K)).mp hx with ⟨i, hxi⟩
  exact hK i hxi

lemma union_subset_set
    {p : ℕ}
    {Γ : Type u} [Group Γ]
    {n k : ℕ}
    {K : Fin k → Set Γ}
    (hK : ∀ i : Fin k, K i ⊆ zassenhausGeneratorSet p Γ n) :
    zassenhausUnionImage K ⊆ zassenhausGeneratorSet p Γ n := by
  exact union_subset_forall hK

lemma image_subset_factorization
    {p : ℕ}
    {Γ : Type u} [Group Γ]
    {n k : ℕ}
    {K : Fin k → Set Γ}
    (hK : ∀ i : Fin k, K i ⊆ zassenhausGeneratorSet p Γ n) :
    zassenhausProductImage K ⊆
      {x : Γ | zGFact p Γ n x} := by
  intro x hx
  rcases hx with ⟨f, hprod⟩
  refine
    ⟨List.ofFn fun i : Fin k => (f i : Γ), ?_, hprod⟩
  rw [List.forall_mem_ofFn_iff]
  intro i
  exact hK i (f i).property

lemma image_subset_filtration
    {p : ℕ}
    {Γ : Type u} [Group Γ]
    {n k : ℕ}
    {K : Fin k → Set Γ}
    (hK : ∀ i : Fin k, K i ⊆ zassenhausGeneratorSet p Γ n) :
    zassenhausProductImage K ⊆
      ((zassenhausFiltration p Γ n : Subgroup Γ) : Set Γ) := by
  intro x hx
  exact
    zGFact.mem_zassenhausFiltration
      (p := p)
      (n := n)
      (image_subset_factorization
        (p := p)
        (Γ := Γ)
        (n := n)
        (K := K)
        hK
        hx)

structure FCCover
    (p : ℕ)
    (Γ : Type u) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    (n : ℕ) where
  width : ℕ
  pieces : Fin width → Set Γ
  pieces_compact : ∀ i : Fin width, IsCompact (pieces i)
  pieces_generators : ∀ i : Fin width, pieces i ⊆ zassenhausGeneratorSet p Γ n
  closure_subset_product :
    (((zassenhausFiltration p Γ n).topologicalClosure : Subgroup Γ) : Set Γ) ⊆
      zassenhausProductImage pieces

lemma FCCover.product_isCompact
    {p : ℕ}
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    {n : ℕ}
    (C : FCCover p Γ n) :
    IsCompact (zassenhausProductImage C.pieces) := by
  exact
    zassenhaus_image_compact
      (Γ := Γ)
      (K := C.pieces)
      C.pieces_compact

lemma FCCover.product_isClosed
    {p : ℕ}
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [T2Space Γ]
    {n : ℕ}
    (C : FCCover p Γ n) :
    IsClosed (zassenhausProductImage C.pieces) := by
  exact C.product_isCompact.isClosed

structure ACCover
    (p : ℕ)
    (Γ : Type u) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    (n : ℕ) where
  width : ℕ
  pieces : Fin width → Set Γ
  pieces_compact : ∀ i : Fin width, IsCompact (pieces i)
  pieces_generators : ∀ i : Fin width, pieces i ⊆ zassenhausGeneratorSet p Γ n
  subgroup_subset_product :
    (((zassenhausFiltration p Γ n : Subgroup Γ) : Set Γ)) ⊆
      zassenhausProductImage pieces

structure ZCCover
    (p : ℕ)
    (Γ : Type u) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    (n : ℕ) where
  width : ℕ
  pieces : Fin width → Set Γ
  pieces_compact : ∀ i : Fin width, IsCompact (pieces i)
  pieces_generators : ∀ i : Fin width, pieces i ⊆ zassenhausGeneratorSet p Γ n
  prod_subset_product :
    ∀ l : List Γ,
      (∀ y ∈ l, y ∈ zassenhausGeneratorSet p Γ n) →
        l.prod ∈ zassenhausProductImage pieces

lemma ZCCover.pieces_compact_apply
    {p : ℕ}
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    {n : ℕ}
    (C : ZCCover p Γ n)
    (i : Fin C.width) :
    IsCompact (C.pieces i) := by
  exact C.pieces_compact i

lemma ZCCover.pieces_generators_apply
    {p : ℕ}
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    {n : ℕ}
    (C : ZCCover p Γ n)
    (i : Fin C.width) :
    C.pieces i ⊆ zassenhausGeneratorSet p Γ n := by
  exact C.pieces_generators i

lemma ZCCover.mem_product_listfactor
    {p : ℕ}
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    {n : ℕ}
    (C : ZCCover p Γ n)
    {x : Γ}
    (hx : zGFact p Γ n x) :
    x ∈ zassenhausProductImage C.pieces := by
  rcases hx with ⟨l, hl, hprod⟩
  rw [← hprod]
  exact C.prod_subset_product l hl

def ZCCover.algebraicCompactCover
    {p : ℕ}
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    {n : ℕ}
    (C : ZCCover p Γ n) :
    ACCover p Γ n := by
  refine
    { width := C.width
      pieces := C.pieces
      pieces_compact := C.pieces_compact
      pieces_generators := C.pieces_generators
      subgroup_subset_product := ?_ }
  intro x hx
  have hfactor :
      zGFact p Γ n x :=
    filtration_subset_factorization
      (p := p)
      (Γ := Γ)
      (n := n)
      hx
  exact C.mem_product_listfactor hfactor

structure WCCover
    (p : ℕ)
    (Γ : Type u) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    (n : ℕ) where
  baseWidth : ℕ
  basePieces : Fin baseWidth → Set Γ
  basePieces_compact : ∀ i : Fin baseWidth, IsCompact (basePieces i)
  basePieces_generators : ∀ i : Fin baseWidth, basePieces i ⊆ zassenhausGeneratorSet p Γ n
  bound : ℕ
  prod_union_product :
    ∀ l : List Γ,
      (∀ y ∈ l, y ∈ zassenhausGeneratorSet p Γ n) →
        ∃ f : Fin bound → Γ,
          (∀ i : Fin bound, f i ∈ zassenhausUnionImage basePieces) ∧
            (List.ofFn f).prod = l.prod

def WCCover.unionPiece
    {p : ℕ}
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    {n : ℕ}
    (C : WCCover p Γ n) :
    Set Γ :=
  zassenhausUnionImage C.basePieces

lemma WCCover.unionPiece_compact
    {p : ℕ}
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    {n : ℕ}
    (C : WCCover p Γ n) :
    IsCompact C.unionPiece := by
  simpa [WCCover.unionPiece] using
    union_image_compact C.basePieces_compact

lemma WCCover.unionPiece_generators
    {p : ℕ}
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    {n : ℕ}
    (C : WCCover p Γ n) :
    C.unionPiece ⊆ zassenhausGeneratorSet p Γ n := by
  simpa [WCCover.unionPiece] using
    union_subset_set
      (p := p)
      (Γ := Γ)
      (n := n)
      C.basePieces_generators

lemma WCCover.mem_repeatedunion_productlist
    {p : ℕ}
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    {n : ℕ}
    (C : WCCover p Γ n)
    {l : List Γ}
    (hl : ∀ y ∈ l, y ∈ zassenhausGeneratorSet p Γ n) :
    l.prod ∈ zassenhausProductImage
      (fun _ : Fin C.bound => C.unionPiece) := by
  rcases C.prod_union_product l hl with ⟨f, hfmem, hprod⟩
  refine ⟨fun i : Fin C.bound => ⟨f i, ?_⟩, ?_⟩
  · simpa [WCCover.unionPiece] using hfmem i
  · change (List.ofFn f).prod = l.prod
    exact hprod

def WCCover.listCompactCover
    {p : ℕ}
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    {n : ℕ}
    (C : WCCover p Γ n) :
    ZCCover p Γ n := by
  refine
    { width := C.bound
      pieces := fun _ : Fin C.bound => C.unionPiece
      pieces_compact := ?_
      pieces_generators := ?_
      prod_subset_product := ?_ }
  · intro i
    exact C.unionPiece_compact
  · intro i
    exact C.unionPiece_generators
  · intro l hl
    exact C.mem_repeatedunion_productlist hl

lemma ACCover.product_isCompact
    {p : ℕ}
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    {n : ℕ}
    (C : ACCover p Γ n) :
    IsCompact (zassenhausProductImage C.pieces) := by
  exact
    zassenhaus_image_compact
      (Γ := Γ)
      (K := C.pieces)
      C.pieces_compact

lemma ACCover.product_isClosed
    {p : ℕ}
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [T2Space Γ]
    {n : ℕ}
    (C : ACCover p Γ n) :
    IsClosed (zassenhausProductImage C.pieces) := by
  exact C.product_isCompact.isClosed

lemma ACCover.topo_closure_subsetproduct
    {p : ℕ}
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    {n : ℕ}
    (C : ACCover p Γ n)
    (hclosed : IsClosed (zassenhausProductImage C.pieces)) :
    (((zassenhausFiltration p Γ n).topologicalClosure : Subgroup Γ) : Set Γ) ⊆
      zassenhausProductImage C.pieces := by
  exact
    topological_subset_closed
      (Γ := Γ)
      (H := zassenhausFiltration p Γ n)
      (S := zassenhausProductImage C.pieces)
      C.subgroup_subset_product
      hclosed

def ACCover.compact_cover_closed
    {p : ℕ}
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    {n : ℕ}
    (C : ACCover p Γ n)
    (hclosed : IsClosed (zassenhausProductImage C.pieces)) :
    FCCover p Γ n := by
  refine
    { width := C.width
      pieces := C.pieces
      pieces_compact := C.pieces_compact
      pieces_generators := C.pieces_generators
      closure_subset_product := ?_ }
  exact C.topo_closure_subsetproduct hclosed

def ACCover.toCompactCover
    {p : ℕ}
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [T2Space Γ]
    {n : ℕ}
    (C : ACCover p Γ n) :
    FCCover p Γ n := by
  exact C.compact_cover_closed C.product_isClosed

lemma ACCover.piece_subtype_compactspace
    {p : ℕ}
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    {n : ℕ}
    (C : ACCover p Γ n)
    (i : Fin C.width) :
    CompactSpace (C.pieces i) := by
  exact isCompact_iff_compactSpace.mp (C.pieces_compact i)

lemma ACCover.piece_subtype_valcont
    {p : ℕ}
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    {n : ℕ}
    (C : ACCover p Γ n)
    (i : Fin C.width) :
    Continuous (fun x : C.pieces i => (x : Γ)) := by
  exact continuous_subtype_val

lemma ACCover.range_piece_subtypeval
    {p : ℕ}
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    {n : ℕ}
    (C : ACCover p Γ n)
    (i : Fin C.width) :
    Set.range (fun x : C.pieces i => (x : Γ)) = C.pieces i := by
  exact Subtype.range_coe

lemma ACCover.range_piecesubtype_valgens
    {p : ℕ}
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    {n : ℕ}
    (C : ACCover p Γ n)
    (i : Fin C.width) :
    Set.range (fun x : C.pieces i => (x : Γ)) ⊆ zassenhausGeneratorSet p Γ n := by
  intro a ha
  rcases ha with ⟨b, rfl⟩
  have hb_piece : (b : Γ) ∈ C.pieces i := b.property
  have hb_generator : (b : Γ) ∈ zassenhausGeneratorSet p Γ n :=
    C.pieces_generators i hb_piece
  exact hb_generator

lemma t_space_disconnected
    (Γ : Type u) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [TotallyDisconnectedSpace Γ] :
    T2Space Γ := by
  haveI : T1Space Γ := inferInstance
  exact
    IsTopologicalGroup.t2Space_iff_one_closed.mpr
      (show IsClosed ({1} : Set Γ) from isClosed_singleton)

structure WICover
    (p : ℕ)
    (Γ : Type u) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    (n : ℕ) where
  width : ℕ
  domains : Fin width → Type u
  domain_topology : ∀ i : Fin width, TopologicalSpace (domains i)
  domain_compact : ∀ i : Fin width, @CompactSpace (domains i) (domain_topology i)
  maps : ∀ i : Fin width, domains i → Γ
  maps_continuous :
    ∀ i : Fin width,
      @Continuous (domains i) Γ (domain_topology i) _ (maps i)
  maps_generators :
    ∀ i : Fin width, ∀ a : domains i, maps i a ∈ zassenhausGeneratorSet p Γ n
  subgroup_subset_product :
    (((zassenhausFiltration p Γ n : Subgroup Γ) : Set Γ)) ⊆
      zassenhausProductImage (fun i : Fin width => Set.range (maps i))

def WICover.pieces
    {p : ℕ}
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    {n : ℕ}
    (C : WICover p Γ n) :
    Fin C.width → Set Γ :=
  fun i => Set.range (C.maps i)

lemma WICover.piece_isCompact
    {p : ℕ}
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    {n : ℕ}
    (C : WICover p Γ n)
    (i : Fin C.width) :
    IsCompact (C.pieces i) := by
  simpa [WICover.pieces] using
    (@isCompact_range
      (C.domains i)
      Γ
      (C.domain_topology i)
      _
      (C.domain_compact i)
      (C.maps i)
      (C.maps_continuous i))

lemma WICover.pieces_compact
    {p : ℕ}
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    {n : ℕ}
    (C : WICover p Γ n) :
    ∀ i : Fin C.width, IsCompact (C.pieces i) := by
  intro i
  exact C.piece_isCompact i

lemma WICover.pieces_generators
    {p : ℕ}
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    {n : ℕ}
    (C : WICover p Γ n) :
    ∀ i : Fin C.width, C.pieces i ⊆ zassenhausGeneratorSet p Γ n := by
  intro i x hx
  rcases hx with ⟨a, rfl⟩
  exact C.maps_generators i a

def WICover.algebraicCompactCover
    {p : ℕ}
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    {n : ℕ}
    (C : WICover p Γ n) :
    ACCover p Γ n := by
  refine
    { width := C.width
      pieces := C.pieces
      pieces_compact := C.pieces_compact
      pieces_generators := C.pieces_generators
      subgroup_subset_product := ?_ }
  simpa [WICover.pieces] using
    C.subgroup_subset_product

def WICover.toCompactCover
    {p : ℕ}
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [T2Space Γ]
    {n : ℕ}
    (C : WICover p Γ n) :
    FCCover p Γ n := by
  exact C.algebraicCompactCover.toCompactCover

def ACCover.gen_image_cover
    {p : ℕ}
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    {n : ℕ}
    (C : ACCover p Γ n) :
    WICover p Γ n := by
  refine
    { width := C.width
      domains := fun i : Fin C.width => C.pieces i
      domain_topology := fun i : Fin C.width => inferInstance
      domain_compact := ?_
      maps := fun i : Fin C.width => fun x : C.pieces i => (x : Γ)
      maps_continuous := ?_
      maps_generators := ?_
      subgroup_subset_product := ?_ }
  · intro i
    exact C.piece_subtype_compactspace i
  · intro i
    exact C.piece_subtype_valcont i
  · intro i a
    exact C.range_piecesubtype_valgens i ⟨a, rfl⟩
  · simpa [ACCover.range_piece_subtypeval] using
      C.subgroup_subset_product

lemma WICover.mem_finunion_mempiece
    {p : ℕ}
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    {n : ℕ}
    (C : WICover p Γ n)
    (i : Fin C.width)
    {x : Γ}
    (hx : x ∈ C.pieces i) :
    x ∈ zassenhausUnionImage C.pieces := by
  refine
    (zassenhaus_union_image
      (K := C.pieces)
      (x := x)).mpr ?_
  exact ⟨i, hx⟩

lemma WICover.list_prodmem_zassfilt
    {p : ℕ}
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    {n : ℕ}
    (_C : WICover p Γ n)
    {l : List Γ}
    (hl : ∀ y ∈ l, y ∈ zassenhausGeneratorSet p Γ n) :
    l.prod ∈ zassenhausFiltration p Γ n := by
  exact
    generator_prod_filtration
      (p := p)
      (n := n)
      hl

lemma WICover.list_prod_memproduct
    {p : ℕ}
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    {n : ℕ}
    (C : WICover p Γ n)
    {l : List Γ}
    (hl : ∀ y ∈ l, y ∈ zassenhausGeneratorSet p Γ n) :
    l.prod ∈ zassenhausProductImage C.pieces := by
  have hfiltration :
      l.prod ∈ zassenhausFiltration p Γ n := by
    exact C.list_prodmem_zassfilt hl
  have hproduct :
      l.prod ∈
        zassenhausProductImage (fun i : Fin C.width => Set.range (C.maps i)) := by
    exact C.subgroup_subset_product hfiltration
  simpa [WICover.pieces] using hproduct

lemma WICover.exists_unionword_memproduct
    {p : ℕ}
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    {n : ℕ}
    (C : WICover p Γ n)
    {x : Γ}
    (hx : x ∈ zassenhausProductImage C.pieces) :
    ∃ f : Fin C.width → Γ,
      (∀ i : Fin C.width, f i ∈ zassenhausUnionImage C.pieces) ∧
        (List.ofFn f).prod = x := by
  rcases hx with ⟨f, hprod⟩
  refine ⟨fun i : Fin C.width => (f i : Γ), ?_, ?_⟩
  · intro i
    exact
      C.mem_finunion_mempiece
        i
        (show (f i : Γ) ∈ C.pieces i from (f i).property)
  · simpa using hprod

lemma WICover.prod_union_product
    {p : ℕ}
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    {n : ℕ}
    (C : WICover p Γ n) :
    ∀ l : List Γ,
      (∀ y ∈ l, y ∈ zassenhausGeneratorSet p Γ n) →
        ∃ f : Fin C.width → Γ,
          (∀ i : Fin C.width, f i ∈ zassenhausUnionImage C.pieces) ∧
            (List.ofFn f).prod = l.prod := by
  intro l hl
  have hmem :
      l.prod ∈ zassenhausProductImage C.pieces := by
    exact C.list_prod_memproduct hl
  exact C.exists_unionword_memproduct hmem

def WICover.unionCompactCover
    {p : ℕ}
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    {n : ℕ}
    (C : WICover p Γ n) :
    WCCover p Γ n := by
  refine
    { baseWidth := C.width
      basePieces := C.pieces
      basePieces_compact := C.pieces_compact
      basePieces_generators := C.pieces_generators
      bound := C.width
      prod_union_product := ?_ }
  intro l hl
  exact C.prod_union_product l hl

structure WGFam
    (p : ℕ)
    (Γ : Type u) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    (n : ℕ) where
  width : ℕ
  domains : Fin width → Type u
  domain_topology : ∀ i : Fin width, TopologicalSpace (domains i)
  domain_compact : ∀ i : Fin width, @CompactSpace (domains i) (domain_topology i)
  maps : ∀ i : Fin width, domains i → Γ
  maps_continuous :
    ∀ i : Fin width,
      @Continuous (domains i) Γ (domain_topology i) _ (maps i)
  maps_generators :
    ∀ i : Fin width, ∀ a : domains i, maps i a ∈ zassenhausGeneratorSet p Γ n

def WGFam.pieces
    {p : ℕ}
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    {n : ℕ}
    (F : WGFam p Γ n) :
    Fin F.width → Set Γ :=
  fun i => Set.range (F.maps i)

lemma WGFam.piece_isCompact
    {p : ℕ}
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    {n : ℕ}
    (F : WGFam p Γ n)
    (i : Fin F.width) :
    IsCompact (F.pieces i) := by
  simpa [WGFam.pieces] using
    (@isCompact_range
      (F.domains i)
      Γ
      (F.domain_topology i)
      _
      (F.domain_compact i)
      (F.maps i)
      (F.maps_continuous i))

lemma WGFam.pieces_compact
    {p : ℕ}
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    {n : ℕ}
    (F : WGFam p Γ n) :
    ∀ i : Fin F.width, IsCompact (F.pieces i) := by
  intro i
  exact F.piece_isCompact i

lemma WGFam.pieces_generators
    {p : ℕ}
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    {n : ℕ}
    (F : WGFam p Γ n) :
    ∀ i : Fin F.width, F.pieces i ⊆ zassenhausGeneratorSet p Γ n := by
  intro i x hx
  rcases hx with ⟨a, rfl⟩
  exact F.maps_generators i a

structure WidthGeneratorCover
    {p : ℕ}
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    {n : ℕ}
    (F : WGFam p Γ n) : Prop where
  subgroup_subset_product :
    (((zassenhausFiltration p Γ n : Subgroup Γ) : Set Γ)) ⊆
      zassenhausProductImage F.pieces

def WGFam.gen_image_cover
    {p : ℕ}
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    {n : ℕ}
    (F : WGFam p Γ n)
    (H : WidthGeneratorCover F) :
    WICover p Γ n := by
  refine
    { width := F.width
      domains := F.domains
      domain_topology := F.domain_topology
      domain_compact := F.domain_compact
      maps := F.maps
      maps_continuous := F.maps_continuous
      maps_generators := F.maps_generators
      subgroup_subset_product := ?_ }
  simpa [WGFam.pieces] using
    H.subgroup_subset_product

def WICover.toMapFamily
    {p : ℕ}
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    {n : ℕ}
    (C : WICover p Γ n) :
    WGFam p Γ n where
  width := C.width
  domains := C.domains
  domain_topology := C.domain_topology
  domain_compact := C.domain_compact
  maps := C.maps
  maps_continuous := C.maps_continuous
  maps_generators := C.maps_generators

lemma WICover.map_fam_pieces
    {p : ℕ}
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    {n : ℕ}
    (C : WICover p Γ n) :
    C.toMapFamily.pieces = C.pieces := by
  rfl

lemma WICover.map_fam_productcovera
    {p : ℕ}
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    {n : ℕ}
    (C : WICover p Γ n) :
    WidthGeneratorCover C.toMapFamily := by
  refine ⟨?_⟩
  simpa [WICover.map_fam_pieces] using
    C.subgroup_subset_product

structure WGWord
    (p : ℕ)
    (Γ : Type u) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    (n : ℕ) where
  arity : ℕ
  map : (Fin arity → Γ) → Γ
  map_continuous : Continuous map
  map_generators : ∀ a : Fin arity → Γ, map a ∈ zassenhausGeneratorSet p Γ n

lemma WGWord.range_subset_generators
    {p : ℕ}
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    {n : ℕ}
    (W : WGWord p Γ n) :
    Set.range W.map ⊆ zassenhausGeneratorSet p Γ n := by
  intro x hx
  rcases hx with ⟨a, rfl⟩
  exact W.map_generators a

lemma WGWord.range_isCompact
    {p : ℕ}
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ]
    {n : ℕ}
    (W : WGWord p Γ n) :
    IsCompact (Set.range W.map) := by
  haveI : CompactSpace (Fin W.arity → Γ) := inferInstance
  simpa using
    (@isCompact_range
      (Fin W.arity → Γ)
      Γ
      _
      _
      inferInstance
      W.map
      W.map_continuous)

def WGWord.toMapFamily
    {p : ℕ}
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ]
    {n k : ℕ}
    (W : Fin k → WGWord p Γ n) :
    WGFam p Γ n := by
  refine
    { width := k
      domains := fun i : Fin k => Fin (W i).arity → Γ
      domain_topology := fun i : Fin k => inferInstance
      domain_compact := ?_
      maps := fun i : Fin k => (W i).map
      maps_continuous := ?_
      maps_generators := ?_ }
  · intro i
    infer_instance
  · intro i
    exact (W i).map_continuous
  · intro i a
    exact (W i).map_generators a

lemma WGWord.map_fam_pieces
    {p : ℕ}
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ]
    {n k : ℕ}
    (W : Fin k → WGWord p Γ n) :
    (WGWord.toMapFamily W).pieces =
      fun i : Fin k => Set.range ((W i).map) := by
  rfl

lemma WGWord.map_fam_piececompact
    {p : ℕ}
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ]
    {n k : ℕ}
    (W : Fin k → WGWord p Γ n)
    (i : Fin k) :
    IsCompact ((WGWord.toMapFamily W).pieces i) := by
  simpa [WGWord.map_fam_pieces] using
    (W i).range_isCompact

lemma WGWord.map_fam_piecegens
    {p : ℕ}
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ]
    {n k : ℕ}
    (W : Fin k → WGWord p Γ n)
    (i : Fin k) :
    (WGWord.toMapFamily W).pieces i ⊆
      zassenhausGeneratorSet p Γ n := by
  simpa [WGWord.map_fam_pieces] using
    (W i).range_subset_generators

structure ZWCover
    {p : ℕ}
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    {n k : ℕ}
    (W : Fin k → WGWord p Γ n) : Prop where
  subgroup_subset_product :
    (((zassenhausFiltration p Γ n : Subgroup Γ) : Set Γ)) ⊆
      zassenhausProductImage (fun i : Fin k => Set.range ((W i).map))

lemma ZWCover.map_fam_productcover
    {p : ℕ}
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ]
    {n k : ℕ}
    {W : Fin k → WGWord p Γ n}
    (H : ZWCover W) :
    WidthGeneratorCover
      (WGWord.toMapFamily W) := by
  refine ⟨?_⟩
  simpa [WGWord.map_fam_pieces] using
    H.subgroup_subset_product

lemma dense_width_cover
    {p : ℕ}
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ]
    {n k : ℕ}
    {W : Fin k → WGWord p Γ n}
    (H : ZWCover W) :
    ∃ F : WGFam p Γ n,
      Nonempty (WidthGeneratorCover F) := by
  refine
    ⟨WGWord.toMapFamily W, ?_⟩
  exact ⟨H.map_fam_productcover⟩

def ZWCover.gen_image_cover
    {p : ℕ}
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ]
    {n k : ℕ}
    {W : Fin k → WGWord p Γ n}
    (H : ZWCover W) :
    WICover p Γ n := by
  exact
    (WGWord.toMapFamily W).gen_image_cover
      H.map_fam_productcover

lemma ZWCover.gen_image_coverpieces
    {p : ℕ}
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ]
    {n k : ℕ}
    {W : Fin k → WGWord p Γ n}
    (H : ZWCover W) :
    H.gen_image_cover.pieces =
      fun i : Fin k => Set.range ((W i).map) := by
  rfl

lemma width_image_cover
    {p : ℕ}
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ]
    {n k : ℕ}
    {W : Fin k → WGWord p Γ n}
    (H : ZWCover W) :
    Nonempty (WICover p Γ n) := by
  exact ⟨H.gen_image_cover⟩

lemma ZWCover.prod_union_product
    {p : ℕ}
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    {n k : ℕ}
    {W : Fin k → WGWord p Γ n}
    (H : ZWCover W) :
    ∀ l : List Γ,
      (∀ y ∈ l, y ∈ zassenhausGeneratorSet p Γ n) →
        ∃ f : Fin k → Γ,
          (∀ i : Fin k,
            f i ∈ zassenhausUnionImage
              (fun j : Fin k => Set.range ((W j).map))) ∧
            (List.ofFn f).prod = l.prod := by
  intro l hl
  have hfiltration :
      l.prod ∈ zassenhausFiltration p Γ n := by
    exact
      generator_prod_filtration
        (p := p)
        (n := n)
        hl
  have hproduct :
      l.prod ∈ zassenhausProductImage
        (fun i : Fin k => Set.range ((W i).map)) := by
    exact H.subgroup_subset_product hfiltration
  rcases hproduct with ⟨f, hprod⟩
  refine ⟨fun i : Fin k => (f i : Γ), ?_, ?_⟩
  · intro i
    exact
      (zassenhaus_union_image
        (K := fun j : Fin k => Set.range ((W j).map))
        (x := (f i : Γ))).mpr
        ⟨i, (f i).property⟩
  · simpa using hprod

def ZWCover.unionCompactCover
    {p : ℕ}
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ]
    {n k : ℕ}
    {W : Fin k → WGWord p Γ n}
    (H : ZWCover W) :
    WCCover p Γ n := by
  refine
    { baseWidth := k
      basePieces := fun i : Fin k => Set.range ((W i).map)
      basePieces_compact := ?_
      basePieces_generators := ?_
      bound := k
      prod_union_product := ?_ }
  · intro i
    exact (W i).range_isCompact
  · intro i
    exact (W i).range_subset_generators
  · exact H.prod_union_product

lemma ZWCover.compact_cover_piece
    {p : ℕ}
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ]
    {n k : ℕ}
    {W : Fin k → WGWord p Γ n}
    (H : ZWCover W) :
    H.unionCompactCover.unionPiece =
      zassenhausUnionImage
        (fun i : Fin k => Set.range ((W i).map)) := by
  rfl

lemma width_union_cover
    {p : ℕ}
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ]
    {n k : ℕ}
    {W : Fin k → WGWord p Γ n}
    (H : ZWCover W) :
    Nonempty (WCCover p Γ n) := by
  exact ⟨H.unionCompactCover⟩

lemma dense_compact_cover
    {p : ℕ}
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ]
    {n k : ℕ}
    {W : Fin k → WGWord p Γ n}
    (H : ZWCover W) :
    Nonempty (ZCCover p Γ n) := by
  exact ⟨H.unionCompactCover.listCompactCover⟩

lemma algebraic_compact_cover
    {p : ℕ}
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ]
    {n k : ℕ}
    {W : Fin k → WGWord p Γ n}
    (H : ZWCover W) :
    Nonempty (ACCover p Γ n) := by
  exact ⟨H.unionCompactCover.listCompactCover.algebraicCompactCover⟩

structure WPFact
    {p : ℕ}
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    {n k : ℕ}
    (W : Fin k → WGWord p Γ n) : Prop where
  subgroup_factorization :
    ∀ x : Γ,
      x ∈ (((zassenhausFiltration p Γ n : Subgroup Γ) : Set Γ)) →
        ∃ f : Fin k → Γ,
          (∀ i : Fin k, f i ∈ Set.range ((W i).map)) ∧
            (List.ofFn f).prod = x

lemma WPFact.mem_product
    {p : ℕ}
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    {n k : ℕ}
    {W : Fin k → WGWord p Γ n}
    (H : WPFact W)
    {x : Γ}
    (hx : x ∈ (((zassenhausFiltration p Γ n : Subgroup Γ) : Set Γ))) :
    x ∈ zassenhausProductImage
      (fun i : Fin k => Set.range ((W i).map)) := by
  rcases H.subgroup_factorization x hx with ⟨f, hfmem, hprod⟩
  refine ⟨fun i : Fin k => ⟨f i, hfmem i⟩, ?_⟩
  change (List.ofFn f).prod = x
  exact hprod

lemma WPFact.toProductCover
    {p : ℕ}
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    {n k : ℕ}
    {W : Fin k → WGWord p Γ n}
    (H : WPFact W) :
    ZWCover W := by
  refine ⟨?_⟩
  intro x hx
  exact H.mem_product hx

lemma ZWCover.toPointwiseFactorization
    {p : ℕ}
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    {n k : ℕ}
    {W : Fin k → WGWord p Γ n}
    (H : ZWCover W) :
    WPFact W := by
  refine ⟨?_⟩
  intro x hx
  have hxprod :
      x ∈ zassenhausProductImage
        (fun i : Fin k => Set.range ((W i).map)) := by
    exact H.subgroup_subset_product hx
  rcases hxprod with ⟨f, hprod⟩
  refine ⟨fun i : Fin k => (f i : Γ), ?_, ?_⟩
  · intro i
    exact (f i).property
  · simpa using hprod

lemma width_pointwise_cover
    {p : ℕ}
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    {n k : ℕ}
    {W : Fin k → WGWord p Γ n} :
    WPFact W ↔
      ZWCover W := by
  constructor
  · intro H
    exact H.toProductCover
  · intro H
    exact H.toPointwiseFactorization

lemma
    width_cover_pointwise
    {p : ℕ}
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    {n k : ℕ}
    {W : Fin k → WGWord p Γ n}
    (H : WPFact W) :
    ∃ k : ℕ,
      ∃ W : Fin k → WGWord p Γ n,
        Nonempty (ZWCover W) := by
  refine ⟨k, W, ?_⟩
  exact ⟨H.toProductCover⟩

structure WGRed
    {p : ℕ}
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    {n k : ℕ}
    (W : Fin k → WGWord p Γ n) : Prop where
  list_prod_factorization :
    ∀ l : List Γ,
      (∀ y ∈ l, y ∈ zassenhausGeneratorSet p Γ n) →
        ∃ f : Fin k → Γ,
          (∀ i : Fin k, f i ∈ Set.range ((W i).map)) ∧
            (List.ofFn f).prod = l.prod

lemma WGRed.factor_list_factor
    {p : ℕ}
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    {n k : ℕ}
    {W : Fin k → WGWord p Γ n}
    (H : WGRed W)
    {x : Γ}
    (hx : zGFact p Γ n x) :
    ∃ f : Fin k → Γ,
      (∀ i : Fin k, f i ∈ Set.range ((W i).map)) ∧
        (List.ofFn f).prod = x := by
  rcases hx with ⟨l, hl, hprod⟩
  rcases H.list_prod_factorization l hl with ⟨f, hfmem, hfprod⟩
  refine ⟨f, hfmem, ?_⟩
  rw [hfprod]
  exact hprod

lemma WGRed.toPointwiseFactorization
    {p : ℕ}
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    {n k : ℕ}
    {W : Fin k → WGWord p Γ n}
    (H : WGRed W) :
    WPFact W := by
  refine ⟨?_⟩
  intro x hx
  have hxlist :
      zGFact p Γ n x := by
    exact
      filtration_subset_factorization
        (p := p)
        (Γ := Γ)
        (n := n)
        hx
  exact H.factor_list_factor hxlist

lemma WPFact.toListReduction
    {p : ℕ}
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    {n k : ℕ}
    {W : Fin k → WGWord p Γ n}
    (H : WPFact W) :
    WGRed W := by
  refine ⟨?_⟩
  intro l hl
  have hprod_mem :
      l.prod ∈ zassenhausFiltration p Γ n := by
    exact
      generator_prod_filtration
        (p := p)
        (n := n)
        hl
  exact H.subgroup_factorization l.prod hprod_mem

lemma width_reduction_pointwise
    {p : ℕ}
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    {n k : ℕ}
    {W : Fin k → WGWord p Γ n} :
    WGRed W ↔
      WPFact W := by
  constructor
  · intro H
    exact H.toPointwiseFactorization
  · intro H
    exact H.toListReduction

lemma
    width_pointwise_reduction
    {p : ℕ}
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    {n k : ℕ}
    {W : Fin k → WGWord p Γ n}
    (H : WGRed W) :
    ∃ k : ℕ,
      ∃ W : Fin k → WGWord p Γ n,
        Nonempty
          (WPFact W) := by
  refine ⟨k, W, ?_⟩
  exact ⟨H.toPointwiseFactorization⟩

structure WLWord
    (p : ℕ)
    (Γ : Type u) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    (n : ℕ) where
  lowerLevel : ℕ
  frobenius : ℕ
  arity : ℕ
  lowerMap : (Fin arity → Γ) → Γ
  lowerMap_continuous : Continuous lowerMap
  lower_map_central :
    ∀ a : Fin arity → Γ, lowerMap a ∈ Subgroup.lowerCentralSeries Γ lowerLevel
  level_bound : n ≤ (lowerLevel + 1) * p ^ frobenius
  poweredMap_continuous :
    Continuous (fun a : Fin arity → Γ => lowerMap a ^ (p ^ frobenius))

lemma WLWord.powered_mem_generators
    {p : ℕ}
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    {n : ℕ}
    (V : WLWord p Γ n)
    (a : Fin V.arity → Γ) :
    V.lowerMap a ^ (p ^ V.frobenius) ∈ zassenhausGeneratorSet p Γ n := by
  refine
    ⟨V.lowerLevel, V.frobenius, V.lowerMap a, ?_, ?_, ?_⟩
  · exact V.lower_map_central a
  · exact V.level_bound
  · rfl

def WLWord.const
    {p : ℕ}
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    {n i j : ℕ}
    (x : Γ)
    (hx : x ∈ Subgroup.lowerCentralSeries Γ i)
    (hbound : n ≤ (i + 1) * p ^ j) :
    WLWord p Γ n where
  lowerLevel := i
  frobenius := j
  arity := 0
  lowerMap := fun _ => x
  lowerMap_continuous := by
    exact continuous_const
  lower_map_central := by
    intro _a
    exact hx
  level_bound := hbound
  poweredMap_continuous := by
    exact continuous_const

lemma WLWord.const_lower_mapapply
    {p : ℕ}
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    {n i j : ℕ}
    {x : Γ}
    {hx : x ∈ Subgroup.lowerCentralSeries Γ i}
    {hbound : n ≤ (i + 1) * p ^ j}
    (a :
      Fin (WLWord.const
        (p := p) (Γ := Γ) (n := n) (i := i) (j := j) x hx hbound).arity → Γ) :
    (WLWord.const
        (p := p) (Γ := Γ) (n := n) (i := i) (j := j) x hx hbound).lowerMap a = x := by
  rfl

lemma WLWord.const_powered_apply
    {p : ℕ}
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    {n i j : ℕ}
    {x : Γ}
    {hx : x ∈ Subgroup.lowerCentralSeries Γ i}
    {hbound : n ≤ (i + 1) * p ^ j}
    (a :
      Fin (WLWord.const
        (p := p) (Γ := Γ) (n := n) (i := i) (j := j) x hx hbound).arity → Γ) :
    (WLWord.const
        (p := p) (Γ := Γ) (n := n) (i := i) (j := j) x hx hbound).lowerMap a ^
        (p ^
          (WLWord.const
            (p := p) (Γ := Γ) (n := n) (i := i) (j := j) x hx hbound).frobenius) =
      x ^ (p ^ j) := by
  rfl

lemma lower_generator_set
    {p : ℕ}
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    {n : ℕ}
    {g : Γ}
    (hg : g ∈ zassenhausGeneratorSet p Γ n) :
    ∃ V : WLWord p Γ n,
      ∃ a : Fin V.arity → Γ,
        V.lowerMap a ^ (p ^ V.frobenius) = g := by
  rcases hg with ⟨i, j, x, hx, hbound, hpow⟩
  let V :=
    WLWord.const
      (p := p) (Γ := Γ) (n := n) (i := i) (j := j) x hx hbound
  refine ⟨V, ?_, ?_⟩
  · intro a
    exact Fin.elim0 a
  · simpa [V, WLWord.const] using hpow

lemma generator_set_value
    {p : ℕ}
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    {n : ℕ}
    {g : Γ} :
    g ∈ zassenhausGeneratorSet p Γ n ↔
      ∃ V : WLWord p Γ n,
        ∃ a : Fin V.arity → Γ,
          V.lowerMap a ^ (p ^ V.frobenius) = g := by
  constructor
  · intro hg
    exact
      lower_generator_set
        (p := p)
        (n := n)
        hg
  · rintro ⟨V, a, hpow⟩
    rw [← hpow]
    exact V.powered_mem_generators a

def ZLValue
    (p : ℕ)
    (Γ : Type u) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    (n : ℕ) :
    Type u :=
  Σ V : WLWord p Γ n, Fin V.arity → Γ

namespace ZLValue

def value
    {p : ℕ}
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    {n : ℕ}
    (q : ZLValue p Γ n) :
    Γ :=
  q.1.lowerMap q.2 ^ (p ^ q.1.frobenius)

def wordMap
    {p : ℕ}
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    {n : ℕ}
    (q : ZLValue p Γ n) :
    WLWord p Γ n :=
  q.1

def argument
    {p : ℕ}
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    {n : ℕ}
    (q : ZLValue p Γ n) :
    Fin q.wordMap.arity → Γ :=
  q.2

lemma value_word
    {p : ℕ}
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    {n : ℕ}
    (q : ZLValue p Γ n) :
    q.value = q.wordMap.lowerMap q.argument ^ (p ^ q.wordMap.frobenius) := by
  rfl

lemma value_mem_generators
    {p : ℕ}
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    {n : ℕ}
    (q : ZLValue p Γ n) :
    q.value ∈ zassenhausGeneratorSet p Γ n := by
  exact q.wordMap.powered_mem_generators q.argument

end ZLValue

lemma lower_value_set
    {p : ℕ}
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    {n : ℕ}
    {g : Γ}
    (hg : g ∈ zassenhausGeneratorSet p Γ n) :
    ∃ q : ZLValue p Γ n,
      q.value = g := by
  rcases
    lower_generator_set
      (p := p)
      (Γ := Γ)
      (n := n)
      (g := g)
      hg with ⟨V, a, hvalue⟩
  exact ⟨⟨V, a⟩, hvalue⟩

structure LCExp
    (p : ℕ)
    (Γ : Type u) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    (n : ℕ)
    (l : List Γ) : Type u where
  values : List (ZLValue p Γ n)
  values_map_eq :
    values.map (fun q => ZLValue.value q) = l

namespace LCExp

lemma values_mem_generators
    {p : ℕ}
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    {n : ℕ}
    {l : List Γ}
    (E : LCExp p Γ n l) :
    ∀ q ∈ E.values,
      ZLValue.value q ∈ zassenhausGeneratorSet p Γ n := by
  intro q _hq
  exact ZLValue.value_mem_generators q

lemma prod_eq
    {p : ℕ}
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    {n : ℕ}
    {l : List Γ}
    (E : LCExp p Γ n l) :
    (E.values.map fun q => ZLValue.value q).prod =
      l.prod := by
  rw [E.values_map_eq]

lemma list_mem_generators
    {p : ℕ}
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    {n : ℕ}
    {l : List Γ}
    (E : LCExp p Γ n l) :
    ∀ y ∈ l, y ∈ zassenhausGeneratorSet p Γ n := by
  intro y hy
  have hymap :
      y ∈
        E.values.map
          (fun q : ZLValue p Γ n =>
            ZLValue.value q) := by
    simpa [E.values_map_eq] using hy
  rcases List.mem_map.mp hymap with ⟨q, hq, hqvalue⟩
  rw [← hqvalue]
  exact ZLValue.value_mem_generators q

end LCExp

lemma expansion_forall_set
    {p : ℕ}
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    {n : ℕ}
    {l : List Γ}
    (hl : ∀ y ∈ l, y ∈ zassenhausGeneratorSet p Γ n) :
    Nonempty (LCExp p Γ n l) := by
  induction l with
  | nil =>
      refine ⟨?_⟩
      refine
        { values := []
          values_map_eq := ?_ }
      simp
  | cons y ys ih =>
      have hy :
          y ∈ zassenhausGeneratorSet p Γ n := by
        exact hl y (by simp)
      have hys :
          ∀ z ∈ ys, z ∈ zassenhausGeneratorSet p Γ n := by
        intro z hz
        exact hl z (by simp [hz])
      rcases
        lower_value_set
          (p := p)
          (Γ := Γ)
          (n := n)
          (g := y)
          hy with ⟨q, hq⟩
      rcases ih hys with ⟨E⟩
      refine ⟨?_⟩
      refine
        { values := q :: E.values
          values_map_eq := ?_ }
      simp [hq, E.values_map_eq]

lemma lower_forall_set
    {p : ℕ}
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    {n : ℕ}
    {l : List Γ}
    (hl : ∀ y ∈ l, y ∈ zassenhausGeneratorSet p Γ n) :
    ∃ values : List (ZLValue p Γ n),
      (∀ q ∈ values,
        ZLValue.value q ∈ zassenhausGeneratorSet p Γ n) ∧
        (values.map fun q => ZLValue.value q).prod =
          l.prod := by
  rcases
    expansion_forall_set
      (p := p)
      (Γ := Γ)
      (n := n)
      (l := l)
      hl with ⟨E⟩
  exact
    ⟨E.values,
      E.values_mem_generators,
      E.prod_eq⟩

def WLWord.generatorWord
    {p : ℕ}
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    {n : ℕ}
    (V : WLWord p Γ n) :
    WGWord p Γ n where
  arity := V.arity
  map := fun a : Fin V.arity → Γ => V.lowerMap a ^ (p ^ V.frobenius)
  map_continuous := V.poweredMap_continuous
  map_generators := by
    intro a
    exact V.powered_mem_generators a

lemma WLWord.generator_word
    {p : ℕ}
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    {n : ℕ}
    (V : WLWord p Γ n)
    (a : Fin V.arity → Γ) :
    V.generatorWord.map a = V.lowerMap a ^ (p ^ V.frobenius) := by
  rfl

lemma WLWord.range_subset_generators
    {p : ℕ}
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    {n : ℕ}
    (V : WLWord p Γ n) :
    Set.range (fun a : Fin V.arity → Γ => V.lowerMap a ^ (p ^ V.frobenius)) ⊆
      zassenhausGeneratorSet p Γ n := by
  intro x hx
  rcases hx with ⟨a, rfl⟩
  exact V.powered_mem_generators a

lemma WLWord.range_isCompact
    {p : ℕ}
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ]
    {n : ℕ}
    (V : WLWord p Γ n) :
    IsCompact
      (Set.range (fun a : Fin V.arity → Γ => V.lowerMap a ^ (p ^ V.frobenius))) := by
  simpa [WLWord.generatorWord] using
    V.generatorWord.range_isCompact

def WLWord.generatorWordFamily
    {p : ℕ}
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    {n k : ℕ}
    (V : Fin k → WLWord p Γ n) :
    Fin k → WGWord p Γ n :=
  fun i => (V i).generatorWord

def WLWord.poweredRange
    {p : ℕ}
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    {n : ℕ}
    (V : WLWord p Γ n) :
    Set Γ :=
  Set.range (fun a : Fin V.arity → Γ => V.lowerMap a ^ (p ^ V.frobenius))

def zassenhausRangeUnion
    (p : ℕ)
    (Γ : Type u) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    (n : ℕ) :
    Set Γ :=
  ⋃ V : WLWord p Γ n, V.poweredRange

lemma union_subset_generators
    {p : ℕ}
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    {n : ℕ} :
    zassenhausRangeUnion p Γ n ⊆
      zassenhausGeneratorSet p Γ n := by
  intro g hg
  rcases Set.mem_iUnion.mp hg with ⟨V, hgV⟩
  rcases hgV with ⟨a, hga⟩
  rw [← hga]
  exact V.powered_mem_generators a

lemma set_subset_union
    {p : ℕ}
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    {n : ℕ} :
    zassenhausGeneratorSet p Γ n ⊆
      zassenhausRangeUnion p Γ n := by
  intro g hg
  rcases
    lower_generator_set
      (p := p)
      (Γ := Γ)
      (n := n)
      (g := g)
      hg with ⟨V, a, hpow⟩
  exact
    Set.mem_iUnion.mpr
      ⟨V, by
        exact ⟨a, hpow⟩⟩

lemma range_union_generators
    {p : ℕ}
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    {n : ℕ} :
    zassenhausRangeUnion p Γ n =
      zassenhausGeneratorSet p Γ n := by
  exact
    Set.Subset.antisymm
      union_subset_generators
      set_subset_union

lemma WLWord.powered_rangeeq_genrange
    {p : ℕ}
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    {n : ℕ}
    (V : WLWord p Γ n) :
    V.poweredRange = Set.range V.generatorWord.map := by
  rfl

def WLWord.familyPoweredRanges
    {p : ℕ}
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    {n k : ℕ}
    (V : Fin k → WLWord p Γ n) :
    Fin k → Set Γ :=
  fun i => (V i).poweredRange

lemma WLWord.fam_powered_rangesgens
    {p : ℕ}
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    {n k : ℕ}
    (V : Fin k → WLWord p Γ n) :
    ∀ i : Fin k,
      WLWord.familyPoweredRanges V i ⊆
        zassenhausGeneratorSet p Γ n := by
  intro i
  simpa [WLWord.familyPoweredRanges,
    WLWord.poweredRange] using
    (V i).range_subset_generators

lemma WLWord.fam_powered_rangescompact
    {p : ℕ}
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ]
    {n k : ℕ}
    (V : Fin k → WLWord p Γ n) :
    ∀ i : Fin k,
      IsCompact (WLWord.familyPoweredRanges V i) := by
  intro i
  simpa [WLWord.familyPoweredRanges,
    WLWord.poweredRange] using
    (V i).range_isCompact

lemma WLWord.fampowered_rangessubset_rangeunion
    {p : ℕ}
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    {n k : ℕ}
    (V : Fin k → WLWord p Γ n)
    (i : Fin k) :
    WLWord.familyPoweredRanges V i ⊆
      zassenhausRangeUnion p Γ n := by
  intro x hx
  exact
    Set.mem_iUnion.mpr
      ⟨V i, by
        simpa [WLWord.familyPoweredRanges] using hx⟩

lemma powered_ranges_range
    {p : ℕ}
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    {n k : ℕ}
    (V : Fin k → WLWord p Γ n) :
    zassenhausUnionImage
        (WLWord.familyPoweredRanges V) ⊆
      zassenhausRangeUnion p Γ n := by
  intro x hx
  rcases
    (zassenhaus_union_image
      (K := WLWord.familyPoweredRanges V)).mp hx with
    ⟨i, hxi⟩
  exact
    WLWord.fampowered_rangessubset_rangeunion
      V
      i
      hxi

lemma powered_ranges_generators
    {p : ℕ}
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    {n k : ℕ}
    (V : Fin k → WLWord p Γ n) :
    zassenhausUnionImage
        (WLWord.familyPoweredRanges V) ⊆
      zassenhausGeneratorSet p Γ n := by
  intro x hx
  exact
    union_subset_generators
      (powered_ranges_range V hx)

structure WLRed
    {p : ℕ}
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    {n k : ℕ}
    (V : Fin k → WLWord p Γ n) : Prop where
  list_prod_factorization :
    ∀ l : List Γ,
      (∀ y ∈ l, y ∈ zassenhausGeneratorSet p Γ n) →
        ∃ f : Fin k → Γ,
          (∀ i : Fin k,
            f i ∈ Set.range
              (fun a : Fin (V i).arity → Γ =>
                (V i).lowerMap a ^ (p ^ (V i).frobenius))) ∧
            (List.ofFn f).prod = l.prod

lemma WLRed.gen_wordmap_listreduce
    {p : ℕ}
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    {n k : ℕ}
    {V : Fin k → WLWord p Γ n}
    (H : WLRed V) :
    WGRed
      (WLWord.generatorWordFamily V) := by
  refine ⟨?_⟩
  intro l hl
  rcases H.list_prod_factorization l hl with ⟨f, hfmem, hprod⟩
  refine ⟨f, ?_, hprod⟩
  intro i
  simpa [WLWord.generatorWordFamily,
    WLWord.generatorWord] using
    hfmem i

lemma WLRed.list_prod_memproduct
    {p : ℕ}
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    {n k : ℕ}
    {V : Fin k → WLWord p Γ n}
    (H : WLRed V)
    {l : List Γ}
    (hl : ∀ y ∈ l, y ∈ zassenhausGeneratorSet p Γ n) :
    l.prod ∈ zassenhausProductImage
      (WLWord.familyPoweredRanges V) := by
  rcases H.list_prod_factorization l hl with ⟨f, hfmem, hprod⟩
  refine ⟨fun i : Fin k => ⟨f i, ?_⟩, ?_⟩
  · simpa [WLWord.familyPoweredRanges,
      WLWord.poweredRange] using
      hfmem i
  · change (List.ofFn f).prod = l.prod
    exact hprod

structure ZUCompre
    {p : ℕ}
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    {n k : ℕ}
    (V : Fin k → WLWord p Γ n) : Prop where
  expansion_prod_mem :
    ∀ l : List Γ,
      LCExp p Γ n l →
        l.prod ∈ zassenhausProductImage
          (WLWord.familyPoweredRanges V)

namespace ZUCompre

lemma factorization_of_expansion
    {p : ℕ}
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    {n k : ℕ}
    {V : Fin k → WLWord p Γ n}
    (H : ZUCompre V)
    {l : List Γ}
    (E : LCExp p Γ n l) :
    ∃ f : Fin k → Γ,
      (∀ i : Fin k,
        f i ∈ Set.range
          (fun a : Fin (V i).arity → Γ =>
            (V i).lowerMap a ^ (p ^ (V i).frobenius))) ∧
        (List.ofFn f).prod = l.prod := by
  have hprod :
      l.prod ∈ zassenhausProductImage
        (WLWord.familyPoweredRanges V) := by
    exact H.expansion_prod_mem l E
  rcases hprod with ⟨f, hfprod⟩
  refine ⟨fun i : Fin k => (f i : Γ), ?_, ?_⟩
  · intro i
    simp [WLWord.familyPoweredRanges,
      WLWord.poweredRange]
  · simpa using hfprod

lemma toListReduction
    {p : ℕ}
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    {n k : ℕ}
    {V : Fin k → WLWord p Γ n}
    (H : ZUCompre V) :
    WLRed V := by
  refine ⟨?_⟩
  intro l hl
  rcases
    expansion_forall_set
      (p := p)
      (Γ := Γ)
      (n := n)
      (l := l)
      hl with ⟨E⟩
  exact H.factorization_of_expansion (l := l) E

lemma ofListReduction
    {p : ℕ}
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    {n k : ℕ}
    {V : Fin k → WLWord p Γ n}
    (H : WLRed V) :
    ZUCompre V := by
  refine ⟨?_⟩
  intro l E
  exact
    H.list_prod_memproduct
      (E.list_mem_generators)

end ZUCompre

lemma uniform_compression_reduction
    {p : ℕ}
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    {n k : ℕ}
    {V : Fin k → WLWord p Γ n} :
    ZUCompre V ↔
      WLRed V := by
  constructor
  · intro H
    exact H.toListReduction
  · intro H
    exact
      ZUCompre.ofListReduction
        H

structure RUCompre
    {p : ℕ}
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    {n k : ℕ}
    (V : Fin k → WLWord p Γ n) : Prop where
  range_union_prod :
    ∀ l : List Γ,
      (∀ y ∈ l, y ∈ zassenhausRangeUnion p Γ n) →
        l.prod ∈ zassenhausProductImage
          (WLWord.familyPoweredRanges V)

namespace RUCompre

lemma factorization_union_list
    {p : ℕ}
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    {n k : ℕ}
    {V : Fin k → WLWord p Γ n}
    (H : RUCompre V)
    {l : List Γ}
    (hl : ∀ y ∈ l, y ∈ zassenhausRangeUnion p Γ n) :
    ∃ f : Fin k → Γ,
      (∀ i : Fin k,
        f i ∈ Set.range
          (fun a : Fin (V i).arity → Γ =>
            (V i).lowerMap a ^ (p ^ (V i).frobenius))) ∧
        (List.ofFn f).prod = l.prod := by
  have hprod :
      l.prod ∈ zassenhausProductImage
        (WLWord.familyPoweredRanges V) := by
    exact H.range_union_prod l hl
  rcases hprod with ⟨f, hfprod⟩
  refine ⟨fun i : Fin k => (f i : Γ), ?_, ?_⟩
  · intro i
    simp [WLWord.familyPoweredRanges,
      WLWord.poweredRange]
  · simpa using hfprod

lemma toUniformCompression
    {p : ℕ}
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    {n k : ℕ}
    {V : Fin k → WLWord p Γ n}
    (H : RUCompre V) :
    ZUCompre V := by
  refine ⟨?_⟩
  intro l E
  exact
    H.range_union_prod
      l
      (by
        intro y hy
        exact
          set_subset_union
            (E.list_mem_generators y hy))

lemma ofUniformCompression
    {p : ℕ}
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    {n k : ℕ}
    {V : Fin k → WLWord p Γ n}
    (H : ZUCompre V) :
    RUCompre V := by
  refine ⟨?_⟩
  intro l hl
  have hgen :
      ∀ y ∈ l, y ∈ zassenhausGeneratorSet p Γ n := by
    intro y hy
    exact union_subset_generators (hl y hy)
  rcases
    expansion_forall_set
      (p := p)
      (Γ := Γ)
      (n := n)
      (l := l)
      hgen with ⟨E⟩
  exact H.expansion_prod_mem l E

lemma generator_set_prod
    {p : ℕ}
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    {n k : ℕ}
    {V : Fin k → WLWord p Γ n}
    (H : RUCompre V)
    {l : List Γ}
    (hl : ∀ y ∈ l, y ∈ zassenhausGeneratorSet p Γ n) :
    l.prod ∈ zassenhausProductImage
      (WLWord.familyPoweredRanges V) := by
  refine H.range_union_prod l ?_
  intro y hy
  exact
    set_subset_union
      (hl y hy)

lemma factorization_set_list
    {p : ℕ}
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    {n k : ℕ}
    {V : Fin k → WLWord p Γ n}
    (H : RUCompre V)
    {l : List Γ}
    (hl : ∀ y ∈ l, y ∈ zassenhausGeneratorSet p Γ n) :
    ∃ f : Fin k → Γ,
      (∀ i : Fin k,
        f i ∈ Set.range
          (fun a : Fin (V i).arity → Γ =>
            (V i).lowerMap a ^ (p ^ (V i).frobenius))) ∧
        (List.ofFn f).prod = l.prod := by
  refine H.factorization_union_list ?_
  intro y hy
  exact
    set_subset_union
      (hl y hy)

lemma toListReduction
    {p : ℕ}
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    {n k : ℕ}
    {V : Fin k → WLWord p Γ n}
    (H : RUCompre V) :
    WLRed V := by
  refine ⟨?_⟩
  intro l hl
  exact
    H.factorization_set_list
      hl

lemma ofListReduction
    {p : ℕ}
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    {n k : ℕ}
    {V : Fin k → WLWord p Γ n}
    (H : WLRed V) :
    RUCompre V := by
  refine ⟨?_⟩
  intro l hl
  exact
    H.list_prod_memproduct
      (by
        intro y hy
        exact
          union_subset_generators
            (hl y hy))

lemma factorization_range_union
    {p : ℕ}
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    {n k : ℕ}
    {V : Fin k → WLWord p Γ n}
    (H : WLRed V)
    {l : List Γ}
    (hl : ∀ y ∈ l, y ∈ zassenhausRangeUnion p Γ n) :
    ∃ f : Fin k → Γ,
      (∀ i : Fin k,
        f i ∈ Set.range
          (fun a : Fin (V i).arity → Γ =>
            (V i).lowerMap a ^ (p ^ (V i).frobenius))) ∧
        (List.ofFn f).prod = l.prod := by
  have Hrange :
      RUCompre V := by
    exact ofListReduction H
  exact
    Hrange.factorization_union_list
      hl

lemma union_subset_range
    {p : ℕ}
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    {n k : ℕ}
    {V : Fin k → WLWord p Γ n}
    (_H : RUCompre V) :
    zassenhausUnionImage
        (WLWord.familyPoweredRanges V) ⊆
      zassenhausRangeUnion p Γ n := by
  exact powered_ranges_range V

lemma finite_union_generators
    {p : ℕ}
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    {n k : ℕ}
    {V : Fin k → WLWord p Γ n}
    (_H : RUCompre V) :
    zassenhausUnionImage
        (WLWord.familyPoweredRanges V) ⊆
      zassenhausGeneratorSet p Γ n := by
  exact powered_ranges_generators V

lemma subset_union_product
    {p : ℕ}
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    {n k : ℕ}
    {V : Fin k → WLWord p Γ n}
    (H : RUCompre V) :
    ∀ l : List Γ,
      (∀ y ∈ l, y ∈ zassenhausGeneratorSet p Γ n) →
        ∃ f : Fin k → Γ,
          (∀ i : Fin k,
            f i ∈ zassenhausUnionImage
              (WLWord.familyPoweredRanges V)) ∧
            (List.ofFn f).prod = l.prod := by
  intro l hl
  have hprod :
      l.prod ∈ zassenhausProductImage
        (WLWord.familyPoweredRanges V) := by
    exact H.generator_set_prod hl
  rcases hprod with ⟨f, hprod⟩
  refine ⟨fun i : Fin k => (f i : Γ), ?_, ?_⟩
  · intro i
    exact
      (zassenhaus_union_image
        (K := WLWord.familyPoweredRanges V)
        (x := (f i : Γ))).mpr
        ⟨i, (f i).property⟩
  · simpa using hprod

def unionCompactCover
    {p : ℕ}
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ]
    {n k : ℕ}
    {V : Fin k → WLWord p Γ n}
    (H : RUCompre V) :
    WCCover p Γ n := by
  refine
    { baseWidth := k
      basePieces := WLWord.familyPoweredRanges V
      basePieces_compact := ?_
      basePieces_generators := ?_
      bound := k
      prod_union_product := ?_ }
  · exact WLWord.fam_powered_rangescompact V
  · exact WLWord.fam_powered_rangesgens V
  · exact H.subset_union_product

lemma compact_cover_piece
    {p : ℕ}
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ]
    {n k : ℕ}
    {V : Fin k → WLWord p Γ n}
    (H : RUCompre V) :
    H.unionCompactCover.unionPiece =
      zassenhausUnionImage
        (WLWord.familyPoweredRanges V) := by
  rfl

def listCompactCover
    {p : ℕ}
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ]
    {n k : ℕ}
    {V : Fin k → WLWord p Γ n}
    (H : RUCompre V) :
    ZCCover p Γ n := by
  exact H.unionCompactCover.listCompactCover

def algebraicCompactCover
    {p : ℕ}
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ]
    {n k : ℕ}
    {V : Fin k → WLWord p Γ n}
    (H : RUCompre V) :
    ACCover p Γ n := by
  exact H.listCompactCover.algebraicCompactCover

end RUCompre

lemma union_compression_uniform
    {p : ℕ}
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    {n k : ℕ}
    {V : Fin k → WLWord p Γ n} :
    RUCompre V ↔
      ZUCompre V := by
  constructor
  · intro H
    exact H.toUniformCompression
  · intro H
    exact
      RUCompre.ofUniformCompression
        H

lemma union_compression_reduction
    {p : ℕ}
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    {n k : ℕ}
    {V : Fin k → WLWord p Γ n} :
    RUCompre V ↔
      WLRed V := by
  constructor
  · intro H
    exact
      H.toListReduction
  · intro H
    exact
      RUCompre.ofListReduction
        H

lemma
    dense_gens_compression
    {p : ℕ}
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    {n : ℕ}
    (h :
      ∃ k : ℕ,
        ∃ V : Fin k → WLWord p Γ n,
          Nonempty
            (RUCompre V)) :
    ∃ k : ℕ,
      ∃ V : Fin k → WLWord p Γ n,
        Nonempty
          (WLRed V) := by
  rcases h with ⟨k, V, hV⟩
  rcases hV with ⟨H⟩
  refine ⟨k, V, ?_⟩
  exact
    ⟨H.toListReduction⟩

lemma compact_cover_compression
    {p : ℕ}
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ]
    {n : ℕ}
    (h :
      ∃ k : ℕ,
        ∃ V : Fin k → WLWord p Γ n,
          Nonempty
            (RUCompre V)) :
    Nonempty (WCCover p Γ n) := by
  rcases h with ⟨k, V, hV⟩
  rcases hV with ⟨H⟩
  exact ⟨H.unionCompactCover⟩

lemma width_cover_compression
    {p : ℕ}
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ]
    {n : ℕ}
    (h :
      ∃ k : ℕ,
        ∃ V : Fin k → WLWord p Γ n,
          Nonempty
            (RUCompre V)) :
    Nonempty (ZCCover p Γ n) := by
  rcases
    compact_cover_compression
      (p := p)
      (Γ := Γ)
      (n := n)
      h with ⟨C⟩
  exact ⟨C.listCompactCover⟩

lemma
  algebraic_cover_compression
    {p : ℕ}
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ]
    {n : ℕ}
    (h :
      ∃ k : ℕ,
        ∃ V : Fin k → WLWord p Γ n,
          Nonempty
            (RUCompre V)) :
    Nonempty (ACCover p Γ n) := by
  rcases
    width_cover_compression
      (p := p)
      (Γ := Γ)
      (n := n)
      h with ⟨C⟩
  exact ⟨C.algebraicCompactCover⟩

structure ZLCompre
    {p : ℕ}
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    {n k : ℕ}
    (V : Fin k → WLWord p Γ n) : Prop where
  subgroup_subset_product :
    (((zassenhausFiltration p Γ n : Subgroup Γ) : Set Γ)) ⊆
      zassenhausProductImage
        (WLWord.familyPoweredRanges V)

namespace ZLCompre

lemma mem_product
    {p : ℕ}
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    {n k : ℕ}
    {V : Fin k → WLWord p Γ n}
    (H : ZLCompre V)
    {x : Γ}
    (hx : x ∈ (((zassenhausFiltration p Γ n : Subgroup Γ) : Set Γ))) :
    x ∈ zassenhausProductImage
      (WLWord.familyPoweredRanges V) := by
  exact H.subgroup_subset_product hx

lemma factorization_of_mem
    {p : ℕ}
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    {n k : ℕ}
    {V : Fin k → WLWord p Γ n}
    (H : ZLCompre V)
    {x : Γ}
    (hx : x ∈ (((zassenhausFiltration p Γ n : Subgroup Γ) : Set Γ))) :
    ∃ f : Fin k → Γ,
      (∀ i : Fin k,
        f i ∈ Set.range
          (fun a : Fin (V i).arity → Γ =>
            (V i).lowerMap a ^ (p ^ (V i).frobenius))) ∧
        (List.ofFn f).prod = x := by
  have hxprod :
      x ∈ zassenhausProductImage
        (WLWord.familyPoweredRanges V) := by
    exact H.mem_product hx
  rcases hxprod with ⟨f, hprod⟩
  refine ⟨fun i : Fin k => (f i : Γ), ?_, ?_⟩
  · intro i
    simp [WLWord.familyPoweredRanges,
      WLWord.poweredRange]
  · simpa using hprod

lemma unionProductCompression
    {p : ℕ}
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    {n k : ℕ}
    {V : Fin k → WLWord p Γ n}
    (H : ZLCompre V) :
    RUCompre V := by
  refine ⟨?_⟩
  intro l hl
  have hgen :
      ∀ y ∈ l, y ∈ zassenhausGeneratorSet p Γ n := by
    intro y hy
    exact union_subset_generators (hl y hy)
  have hfiltration :
      l.prod ∈ (((zassenhausFiltration p Γ n : Subgroup Γ) : Set Γ)) := by
    exact
      generator_prod_filtration
        (p := p)
        (n := n)
        hgen
  exact H.mem_product hfiltration

lemma rangeUnionCompression
    {p : ℕ}
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    {n k : ℕ}
    {V : Fin k → WLWord p Γ n}
    (H : RUCompre V) :
    ZLCompre V := by
  refine ⟨?_⟩
  intro x hx
  have hfactor :
      zGFact p Γ n x :=
    filtration_subset_factorization
      (p := p)
      (Γ := Γ)
      (n := n)
      hx
  rcases hfactor with ⟨l, hl, hprod⟩
  have hlrange :
      ∀ y ∈ l, y ∈ zassenhausRangeUnion p Γ n := by
    intro y hy
    exact set_subset_union (hl y hy)
  have hmem :
      l.prod ∈ zassenhausProductImage
        (WLWord.familyPoweredRanges V) := by
    exact H.range_union_prod l hlrange
  rw [← hprod]
  exact hmem

lemma toListReduction
    {p : ℕ}
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    {n k : ℕ}
    {V : Fin k → WLWord p Γ n}
    (H : ZLCompre V) :
    WLRed V := by
  exact H.unionProductCompression.toListReduction

def unionCompactCover
    {p : ℕ}
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ]
    {n k : ℕ}
    {V : Fin k → WLWord p Γ n}
    (H : ZLCompre V) :
    WCCover p Γ n := by
  exact H.unionProductCompression.unionCompactCover

def algebraicCompactCover
    {p : ℕ}
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ]
    {n k : ℕ}
    {V : Fin k → WLWord p Γ n}
    (H : ZLCompre V) :
    ACCover p Γ n := by
  exact H.unionProductCompression.algebraicCompactCover

end ZLCompre

structure ZLExp
    (p : ℕ)
    (Γ : Type u) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    (n : ℕ)
    (x : Γ) : Type u where
  values : List (ZLValue p Γ n)
  values_prod_eq :
    (values.map fun q => ZLValue.value q).prod = x

namespace ZLExp

lemma values_mem_generators
    {p : ℕ}
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    {n : ℕ}
    {x : Γ}
    (E : ZLExp p Γ n x) :
    ∀ y ∈
      E.values.map
        (fun q : ZLValue p Γ n =>
          ZLValue.value q),
        y ∈ zassenhausGeneratorSet p Γ n := by
  intro y hy
  rcases List.mem_map.mp hy with ⟨q, _hq, hqvalue⟩
  rw [← hqvalue]
  exact ZLValue.value_mem_generators q

lemma prod_zassenhaus_filtration
    {p : ℕ}
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    {n : ℕ}
    {x : Γ}
    (E : ZLExp p Γ n x) :
    x ∈ (((zassenhausFiltration p Γ n : Subgroup Γ) : Set Γ)) := by
  rw [← E.values_prod_eq]
  exact
    generator_prod_filtration
      (p := p)
      (n := n)
      E.values_mem_generators

def toListExpansion
    {p : ℕ}
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    {n : ℕ}
    {x : Γ}
    (E : ZLExp p Γ n x) :
    LCExp p Γ n
      (E.values.map
        (fun q : ZLValue p Γ n =>
          ZLValue.value q)) := by
  refine
    { values := E.values
      values_map_eq := ?_ }
  rfl

lemma list_expansion_prod
    {p : ℕ}
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    {n : ℕ}
    {x : Γ}
    (E : ZLExp p Γ n x) :
    ((E.toListExpansion).values.map
        (fun q : ZLValue p Γ n =>
          ZLValue.value q)).prod = x := by
  simpa [toListExpansion] using E.values_prod_eq

end ZLExp

lemma lower_expansion_factorization
    {p : ℕ}
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    {n : ℕ}
    {x : Γ}
    (hx : zGFact p Γ n x) :
    Nonempty (ZLExp p Γ n x) := by
  rcases hx with ⟨l, hl, hprod⟩
  rcases
    expansion_forall_set
      (p := p)
      (Γ := Γ)
      (n := n)
      (l := l)
      hl with ⟨E⟩
  refine ⟨?_⟩
  refine
    { values := E.values
      values_prod_eq := ?_ }
  exact E.prod_eq.trans hprod

lemma lower_expansion_filtration
    {p : ℕ}
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    {n : ℕ}
    {x : Γ}
    (hx : x ∈ (((zassenhausFiltration p Γ n : Subgroup Γ) : Set Γ))) :
    Nonempty (ZLExp p Γ n x) := by
  have hfactor :
      zGFact p Γ n x :=
    filtration_subset_factorization
      (p := p)
      (Γ := Γ)
      (n := n)
      hx
  exact
    lower_expansion_factorization
      (p := p)
      (Γ := Γ)
      (n := n)
      hfactor

structure ZPFact
    {p : ℕ}
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    {n k : ℕ}
    (V : Fin k → WLWord p Γ n) : Prop where
  subgroup_factorization :
    ∀ x : Γ,
      x ∈ (((zassenhausFiltration p Γ n : Subgroup Γ) : Set Γ)) →
        ∃ f : Fin k → Γ,
          (∀ i : Fin k,
            f i ∈ Set.range
              (fun a : Fin (V i).arity → Γ =>
                (V i).lowerMap a ^ (p ^ (V i).frobenius))) ∧
            (List.ofFn f).prod = x

namespace ZPFact

lemma mem_product
    {p : ℕ}
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    {n k : ℕ}
    {V : Fin k → WLWord p Γ n}
    (H : ZPFact V)
    {x : Γ}
    (hx : x ∈ (((zassenhausFiltration p Γ n : Subgroup Γ) : Set Γ))) :
    x ∈ zassenhausProductImage
      (WLWord.familyPoweredRanges V) := by
  rcases H.subgroup_factorization x hx with ⟨f, hfmem, hprod⟩
  refine ⟨fun i : Fin k => ⟨f i, ?_⟩, ?_⟩
  · simpa [WLWord.familyPoweredRanges,
      WLWord.poweredRange] using
      hfmem i
  · change (List.ofFn f).prod = x
    exact hprod

lemma subgroupProductCompression
    {p : ℕ}
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    {n k : ℕ}
    {V : Fin k → WLWord p Γ n}
    (H : ZPFact V) :
    ZLCompre V := by
  refine ⟨?_⟩
  intro x hx
  exact H.mem_product hx

lemma unionProductCompression
    {p : ℕ}
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    {n k : ℕ}
    {V : Fin k → WLWord p Γ n}
    (H : ZPFact V) :
    RUCompre V := by
  exact H.subgroupProductCompression.unionProductCompression

lemma toListReduction
    {p : ℕ}
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    {n k : ℕ}
    {V : Fin k → WLWord p Γ n}
    (H : ZPFact V) :
    WLRed V := by
  exact H.subgroupProductCompression.toListReduction

lemma generatorPointwiseFactorization
    {p : ℕ}
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    {n k : ℕ}
    {V : Fin k → WLWord p Γ n}
    (H : ZPFact V) :
    WPFact
      (WLWord.generatorWordFamily V) := by
  refine ⟨?_⟩
  intro x hx
  rcases H.subgroup_factorization x hx with ⟨f, hfmem, hprod⟩
  refine ⟨f, ?_, hprod⟩
  intro i
  simpa [WLWord.generatorWordFamily,
    WLWord.generatorWord] using
    hfmem i

lemma generatorProductCover
    {p : ℕ}
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    {n k : ℕ}
    {V : Fin k → WLWord p Γ n}
    (H : ZPFact V) :
    ZWCover
      (WLWord.generatorWordFamily V) := by
  exact H.generatorPointwiseFactorization.toProductCover

end ZPFact

namespace ZLCompre

lemma toPointwiseFactorization
    {p : ℕ}
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    {n k : ℕ}
    {V : Fin k → WLWord p Γ n}
    (H : ZLCompre V) :
    ZPFact V := by
  refine ⟨?_⟩
  intro x hx
  exact H.factorization_of_mem hx

end ZLCompre

lemma pointwise_factorization_compression
    {p : ℕ}
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    {n k : ℕ}
    {V : Fin k → WLWord p Γ n} :
    ZPFact V ↔
      ZLCompre V := by
  constructor
  · intro H
    exact H.subgroupProductCompression
  · intro H
    exact H.toPointwiseFactorization

lemma
    gens_pointwise_factorization
    {p : ℕ}
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    {n : ℕ}
    (h :
      ∃ k : ℕ,
        ∃ V : Fin k → WLWord p Γ n,
          Nonempty
            (ZPFact V)) :
    ∃ k : ℕ,
      ∃ V : Fin k → WLWord p Γ n,
        Nonempty
          (ZLCompre V) := by
  rcases h with ⟨k, V, hV⟩
  rcases hV with ⟨H⟩
  exact ⟨k, V, ⟨H.subgroupProductCompression⟩⟩

lemma
    dense_pointwise_compression
    {p : ℕ}
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    {n : ℕ}
    (h :
      ∃ k : ℕ,
        ∃ V : Fin k → WLWord p Γ n,
          Nonempty
            (ZLCompre V)) :
    ∃ k : ℕ,
      ∃ V : Fin k → WLWord p Γ n,
        Nonempty
          (ZPFact V) := by
  rcases h with ⟨k, V, hV⟩
  rcases hV with ⟨H⟩
  exact ⟨k, V, ⟨H.toPointwiseFactorization⟩⟩

lemma
    dense_width_pointwise
    {p : ℕ}
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    {n k : ℕ}
    {V : Fin k → WLWord p Γ n}
    (H : ZPFact V) :
    ∃ k : ℕ,
      ∃ W : Fin k → WGWord p Γ n,
        Nonempty
          (WPFact W) := by
  refine
    ⟨k,
      WLWord.generatorWordFamily V,
      ?_⟩
  exact ⟨H.generatorPointwiseFactorization⟩

lemma compression_range_union
    {p : ℕ}
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    {n k : ℕ}
    {V : Fin k → WLWord p Γ n} :
    ZLCompre V ↔
      RUCompre V := by
  constructor
  · intro H
    exact H.unionProductCompression
  · intro H
    exact
      ZLCompre.rangeUnionCompression
        H

lemma
    gens_product_compression
    {p : ℕ}
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    {n : ℕ}
    (h :
      ∃ k : ℕ,
        ∃ V : Fin k → WLWord p Γ n,
          Nonempty
            (ZLCompre V)) :
    ∃ k : ℕ,
      ∃ V : Fin k → WLWord p Γ n,
        Nonempty
          (RUCompre V) := by
  rcases h with ⟨k, V, hV⟩
  rcases hV with ⟨H⟩
  exact ⟨k, V, ⟨H.unionProductCompression⟩⟩

lemma
    gens_union_compression
    {p : ℕ}
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    {n : ℕ}
    (h :
      ∃ k : ℕ,
        ∃ V : Fin k → WLWord p Γ n,
          Nonempty
            (RUCompre V)) :
    ∃ k : ℕ,
      ∃ V : Fin k → WLWord p Γ n,
        Nonempty
          (ZLCompre V) := by
  rcases h with ⟨k, V, hV⟩
  rcases hV with ⟨H⟩
  exact
    ⟨k,
      V,
      ⟨ZLCompre.rangeUnionCompression
        H⟩⟩

def WLRed.unionCompactCover
    {p : ℕ}
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ]
    {n k : ℕ}
    {V : Fin k → WLWord p Γ n}
    (H : WLRed V) :
    WCCover p Γ n := by
  refine
    { baseWidth := k
      basePieces := WLWord.familyPoweredRanges V
      basePieces_compact := ?_
      basePieces_generators := ?_
      bound := k
      prod_union_product := ?_ }
  · exact WLWord.fam_powered_rangescompact V
  · exact WLWord.fam_powered_rangesgens V
  · intro l hl
    rcases H.list_prod_factorization l hl with ⟨f, hfmem, hprod⟩
    refine ⟨f, ?_, hprod⟩
    intro i
    exact
      (zassenhaus_union_image
        (K := WLWord.familyPoweredRanges V)
        (x := f i)).mpr
        ⟨i, by
          simpa [WLWord.familyPoweredRanges,
            WLWord.poweredRange] using
            hfmem i⟩

lemma WLRed.compact_cover_piece
    {p : ℕ}
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ]
    {n k : ℕ}
    {V : Fin k → WLWord p Γ n}
    (H : WLRed V) :
    H.unionCompactCover.unionPiece =
      zassenhausUnionImage
        (WLWord.familyPoweredRanges V) := by
  rfl

lemma
    dense_generators_width
    {p : ℕ}
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    {n k : ℕ}
    {V : Fin k → WLWord p Γ n}
    (H : WLRed V) :
    ∃ k : ℕ,
      ∃ W : Fin k → WGWord p Γ n,
        Nonempty (WGRed W) := by
  refine
    ⟨k,
      WLWord.generatorWordFamily V,
      ?_⟩
  exact ⟨H.gen_wordmap_listreduce⟩

lemma union_compact_cover
    {p : ℕ}
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ]
    {n k : ℕ}
    {V : Fin k → WLWord p Γ n}
    (H : WLRed V) :
    Nonempty (WCCover p Γ n) := by
  exact ⟨H.unionCompactCover⟩

structure ZECompre
    {p : ℕ}
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    {n k : ℕ}
    (V : Fin k → WLWord p Γ n) : Prop where
  expansion_factorization :
    ∀ x : Γ,
      ZLExp p Γ n x →
        ∃ f : Fin k → Γ,
          (∀ i : Fin k,
            f i ∈ Set.range
              (fun a : Fin (V i).arity → Γ =>
                (V i).lowerMap a ^ (p ^ (V i).frobenius))) ∧
            (List.ofFn f).prod = x

namespace ZECompre

lemma factorization_of_mem
    {p : ℕ}
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    {n k : ℕ}
    {V : Fin k → WLWord p Γ n}
    (H : ZECompre V)
    {x : Γ}
    (hx : x ∈ (((zassenhausFiltration p Γ n : Subgroup Γ) : Set Γ))) :
    ∃ f : Fin k → Γ,
      (∀ i : Fin k,
        f i ∈ Set.range
          (fun a : Fin (V i).arity → Γ =>
            (V i).lowerMap a ^ (p ^ (V i).frobenius))) ∧
        (List.ofFn f).prod = x := by
  rcases
    lower_expansion_filtration
      (p := p)
      (Γ := Γ)
      (n := n)
      hx with ⟨E⟩
  exact H.expansion_factorization x E

lemma toPointwiseFactorization
    {p : ℕ}
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    {n k : ℕ}
    {V : Fin k → WLWord p Γ n}
    (H : ZECompre V) :
    ZPFact V := by
  refine ⟨?_⟩
  intro x hx
  exact H.factorization_of_mem hx

lemma subgroupProductCompression
    {p : ℕ}
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    {n k : ℕ}
    {V : Fin k → WLWord p Γ n}
    (H : ZECompre V) :
    ZLCompre V := by
  exact H.toPointwiseFactorization.subgroupProductCompression

lemma unionProductCompression
    {p : ℕ}
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    {n k : ℕ}
    {V : Fin k → WLWord p Γ n}
    (H : ZECompre V) :
    RUCompre V := by
  exact H.toPointwiseFactorization.unionProductCompression

lemma toUniformCompression
    {p : ℕ}
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    {n k : ℕ}
    {V : Fin k → WLWord p Γ n}
    (H : ZECompre V) :
    ZUCompre V := by
  refine ⟨?_⟩
  intro l E
  let Esub : ZLExp p Γ n l.prod :=
    { values := E.values
      values_prod_eq := E.prod_eq }
  rcases H.expansion_factorization l.prod Esub with ⟨f, hfmem, hprod⟩
  refine ⟨fun i : Fin k => ⟨f i, ?_⟩, ?_⟩
  · simpa [WLWord.familyPoweredRanges,
      WLWord.poweredRange] using
      hfmem i
  · change (List.ofFn f).prod = l.prod
    exact hprod

lemma ofUniformCompression
    {p : ℕ}
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    {n k : ℕ}
    {V : Fin k → WLWord p Γ n}
    (H : ZUCompre V) :
    ZECompre V := by
  refine ⟨?_⟩
  intro x E
  rcases H.factorization_of_expansion E.toListExpansion with ⟨f, hfmem, hprod⟩
  refine ⟨f, hfmem, ?_⟩
  exact hprod.trans E.values_prod_eq

lemma ofPointwiseFactorization
    {p : ℕ}
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    {n k : ℕ}
    {V : Fin k → WLWord p Γ n}
    (H : ZPFact V) :
    ZECompre V := by
  refine ⟨?_⟩
  intro x E
  have hx :
      x ∈ (((zassenhausFiltration p Γ n : Subgroup Γ) : Set Γ)) := by
    exact E.prod_zassenhaus_filtration
  exact H.subgroup_factorization x hx

end ZECompre

lemma
    compression_pointwise_factorization
    {p : ℕ}
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    {n k : ℕ}
    {V : Fin k → WLWord p Γ n} :
    ZECompre V ↔
      ZPFact V := by
  constructor
  · intro H
    exact H.toPointwiseFactorization
  · intro H
    exact
      ZECompre.ofPointwiseFactorization
        H

lemma
    expansion_compression_uniform
    {p : ℕ}
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    {n k : ℕ}
    {V : Fin k → WLWord p Γ n} :
    ZECompre V ↔
      ZUCompre V := by
  constructor
  · intro H
    exact H.toUniformCompression
  · intro H
    exact
      ZECompre.ofUniformCompression
        H

lemma
    gens_pointwise_compression
    {p : ℕ}
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    {n : ℕ}
    (h :
      ∃ k : ℕ,
        ∃ V : Fin k → WLWord p Γ n,
          Nonempty
            (ZECompre V)) :
    ∃ k : ℕ,
      ∃ V : Fin k → WLWord p Γ n,
        Nonempty
          (ZPFact V) := by
  rcases h with ⟨k, V, hV⟩
  rcases hV with ⟨H⟩
  exact ⟨k, V, ⟨H.toPointwiseFactorization⟩⟩

lemma
    gens_uniform_compression
    {p : ℕ}
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    {n : ℕ}
    (h :
      ∃ k : ℕ,
        ∃ V : Fin k → WLWord p Γ n,
          Nonempty
            (ZECompre V)) :
    ∃ k : ℕ,
      ∃ V : Fin k → WLWord p Γ n,
        Nonempty
          (ZUCompre V) := by
  rcases h with ⟨k, V, hV⟩
  rcases hV with ⟨H⟩
  exact ⟨k, V, ⟨H.toUniformCompression⟩⟩

lemma
    gens_expansion_compression
    {p : ℕ}
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    {n : ℕ}
    (h :
      ∃ k : ℕ,
        ∃ V : Fin k → WLWord p Γ n,
          Nonempty
            (ZECompre V)) :
    ∃ k : ℕ,
      ∃ V : Fin k → WLWord p Γ n,
        Nonempty
          (ZLCompre V) := by
  rcases h with ⟨k, V, hV⟩
  rcases hV with ⟨H⟩
  exact ⟨k, V, ⟨H.subgroupProductCompression⟩⟩

lemma
    gens_range_compression
    {p : ℕ}
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    {n : ℕ}
    (h :
      ∃ k : ℕ,
        ∃ V : Fin k → WLWord p Γ n,
          Nonempty
            (ZECompre V)) :
    ∃ k : ℕ,
      ∃ V : Fin k → WLWord p Γ n,
        Nonempty
          (RUCompre V) := by
  rcases h with ⟨k, V, hV⟩
  rcases hV with ⟨H⟩
  exact ⟨k, V, ⟨H.unionProductCompression⟩⟩

lemma
    dense_expansion_compression
    {p : ℕ}
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    {n : ℕ}
    (h :
      ∃ k : ℕ,
        ∃ V : Fin k → WLWord p Γ n,
          Nonempty
            (ZECompre V)) :
    ∃ k : ℕ,
      ∃ V : Fin k → WLWord p Γ n,
        Nonempty
          (WLRed V) := by
  rcases h with ⟨k, V, hV⟩
  rcases hV with ⟨H⟩
  exact ⟨k, V, ⟨H.toPointwiseFactorization.toListReduction⟩⟩

lemma
    width_compact_compression
    {p : ℕ}
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ]
    {n : ℕ}
    (h :
      ∃ k : ℕ,
        ∃ V : Fin k → WLWord p Γ n,
          Nonempty
            (ZECompre V)) :
    Nonempty (WCCover p Γ n) := by
  rcases h with ⟨k, V, hV⟩
  rcases hV with ⟨H⟩
  exact ⟨H.subgroupProductCompression.unionCompactCover⟩

lemma
    gens_algebraic_compression
    {p : ℕ}
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ]
    {n : ℕ}
    (h :
      ∃ k : ℕ,
        ∃ V : Fin k → WLWord p Γ n,
          Nonempty
            (ZECompre V)) :
    Nonempty (ACCover p Γ n) := by
  rcases h with ⟨k, V, hV⟩
  rcases hV with ⟨H⟩
  exact ⟨H.subgroupProductCompression.algebraicCompactCover⟩

lemma
    gens_compression_uniform
    {p : ℕ}
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    {n : ℕ}
    (h :
      ∃ k : ℕ,
        ∃ V : Fin k → WLWord p Γ n,
          Nonempty
            (ZUCompre V)) :
    ∃ k : ℕ,
      ∃ V : Fin k → WLWord p Γ n,
        Nonempty
          (ZECompre V) := by
  rcases h with ⟨k, V, hV⟩
  rcases hV with ⟨H⟩
  exact
    ⟨k,
      V,
      ⟨ZECompre.ofUniformCompression
        H⟩⟩

lemma
    gens_compression_pointwise
    {p : ℕ}
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    {n : ℕ}
    (h :
      ∃ k : ℕ,
        ∃ V : Fin k → WLWord p Γ n,
          Nonempty
            (ZPFact V)) :
    ∃ k : ℕ,
      ∃ V : Fin k → WLWord p Γ n,
        Nonempty
          (ZECompre V) := by
  rcases h with ⟨k, V, hV⟩
  rcases hV with ⟨H⟩
  exact
    ⟨k,
      V,
      ⟨ZECompre.ofPointwiseFactorization
        H⟩⟩

lemma
    uniform_compression_pointwise
    {p : ℕ}
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    {n : ℕ} :
    (∃ k : ℕ,
      ∃ V : Fin k → WLWord p Γ n,
        Nonempty
          (ZUCompre V)) ↔
      ∃ k : ℕ,
        ∃ V : Fin k → WLWord p Γ n,
          Nonempty
            (ZPFact V) := by
  constructor
  · intro h
    exact
      gens_pointwise_compression
        (p := p)
        (Γ := Γ)
        (n := n)
        (gens_compression_uniform
          (p := p)
          (Γ := Γ)
          (n := n)
          h)
  · intro h
    exact
      gens_uniform_compression
        (p := p)
        (Γ := Γ)
        (n := n)
        (gens_compression_pointwise
          (p := p)
          (Γ := Γ)
          (n := n)
          h)

lemma
    gens_compression_factorization
    {p : ℕ}
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    {n : ℕ} :
    (∃ k : ℕ,
      ∃ V : Fin k → WLWord p Γ n,
        Nonempty
          (ZECompre V)) ↔
      ∃ k : ℕ,
        ∃ V : Fin k → WLWord p Γ n,
          Nonempty
            (ZPFact V) := by
  constructor
  · intro h
    exact
      gens_pointwise_compression
        (p := p) (Γ := Γ) (n := n) h
  · intro h
    exact
      gens_compression_pointwise
        (p := p) (Γ := Γ) (n := n) h

lemma
    gens_subgroup_compression
    {p : ℕ}
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    {n : ℕ} :
    (∃ k : ℕ,
      ∃ V : Fin k → WLWord p Γ n,
        Nonempty
          (ZUCompre V)) ↔
      ∃ k : ℕ,
        ∃ V : Fin k → WLWord p Γ n,
          Nonempty
            (ZECompre V) := by
  constructor
  · intro h
    exact
      gens_compression_uniform
        (p := p) (Γ := Γ) (n := n) h
  · intro h
    exact
      gens_uniform_compression
        (p := p) (Γ := Γ) (n := n) h

structure DCPackag
    (p : ℕ)
    (Γ : Type u) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    (n : ℕ) : Type (u + 1) where
  width : ℕ
  family : Fin width → WLWord p Γ n
  compression :
    ZECompre family

namespace DCPackag

lemma subgroup_expansion_compression
    {p : ℕ}
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    {n : ℕ}
    (P :
      DCPackag
        p Γ n) :
    ∃ k : ℕ,
      ∃ V : Fin k → WLWord p Γ n,
        Nonempty
          (ZECompre V) := by
  exact ⟨P.width, P.family, ⟨P.compression⟩⟩

lemma exists_pointwiseFactorization
    {p : ℕ}
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    {n : ℕ}
    (P :
      DCPackag
        p Γ n) :
    ∃ k : ℕ,
      ∃ V : Fin k → WLWord p Γ n,
        Nonempty
          (ZPFact V) := by
  exact
    gens_pointwise_compression
      (p := p)
      (Γ := Γ)
      (n := n)
      P.subgroup_expansion_compression

lemma exists_uniformCompression
    {p : ℕ}
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    {n : ℕ}
    (P :
      DCPackag
        p Γ n) :
    ∃ k : ℕ,
      ∃ V : Fin k → WLWord p Γ n,
        Nonempty
          (ZUCompre V) := by
  exact
    gens_uniform_compression
      (p := p)
      (Γ := Γ)
      (n := n)
      P.subgroup_expansion_compression

lemma subgroup_product_compression
    {p : ℕ}
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    {n : ℕ}
    (P :
      DCPackag
        p Γ n) :
    ∃ k : ℕ,
      ∃ V : Fin k → WLWord p Γ n,
        Nonempty
          (ZLCompre V) := by
  exact
    gens_expansion_compression
      (p := p)
      (Γ := Γ)
      (n := n)
      P.subgroup_expansion_compression

lemma range_union_compression
    {p : ℕ}
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    {n : ℕ}
    (P :
      DCPackag
        p Γ n) :
    ∃ k : ℕ,
      ∃ V : Fin k → WLWord p Γ n,
        Nonempty
          (RUCompre V) := by
  exact
    gens_range_compression
      (p := p)
      (Γ := Γ)
      (n := n)
      P.subgroup_expansion_compression

lemma lower_central_reduction
    {p : ℕ}
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    {n : ℕ}
    (P :
      DCPackag
        p Γ n) :
    ∃ k : ℕ,
      ∃ V : Fin k → WLWord p Γ n,
        Nonempty
          (WLRed V) := by
  exact
    dense_expansion_compression
      (p := p)
      (Γ := Γ)
      (n := n)
      P.subgroup_expansion_compression

lemma generator_list_reduction
    {p : ℕ}
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    {n : ℕ}
    (P :
      DCPackag
        p Γ n) :
    ∃ k : ℕ,
      ∃ W : Fin k → WGWord p Γ n,
        Nonempty (WGRed W) := by
  rcases P.lower_central_reduction with ⟨k, V, ⟨H⟩⟩
  exact
    dense_generators_width
      (V := V)
      H

lemma generator_word_pointwise
    {p : ℕ}
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    {n : ℕ}
    (P :
      DCPackag
        p Γ n) :
    ∃ k : ℕ,
      ∃ W : Fin k → WGWord p Γ n,
        Nonempty
          (WPFact W) := by
  rcases P.generator_list_reduction with ⟨k, W, ⟨H⟩⟩
  exact
    width_pointwise_reduction
      (W := W)
      H

lemma generator_product_cover
    {p : ℕ}
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    {n : ℕ}
    (P :
      DCPackag
        p Γ n) :
    ∃ k : ℕ,
      ∃ W : Fin k → WGWord p Γ n,
        Nonempty (ZWCover W) := by
  rcases P.generator_word_pointwise with ⟨k, W, ⟨H⟩⟩
  exact
    width_cover_pointwise
      (W := W)
      H

lemma generator_family_cover
    {p : ℕ}
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ]
    {n : ℕ}
    (P :
      DCPackag
        p Γ n) :
    ∃ F : WGFam p Γ n,
      Nonempty (WidthGeneratorCover F) := by
  rcases P.generator_product_cover with ⟨k, W, ⟨H⟩⟩
  exact
    dense_width_cover
      (W := W)
      H

lemma generator_image_cover
    {p : ℕ}
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ]
    {n : ℕ}
    (P :
      DCPackag
        p Γ n) :
    Nonempty (WICover p Γ n) := by
  rcases P.generator_product_cover with ⟨k, W, ⟨H⟩⟩
  exact
    width_image_cover
      (W := W)
      H

lemma compact_cover
    {p : ℕ}
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ]
    {n : ℕ}
    (P :
      DCPackag
        p Γ n) :
    Nonempty (WCCover p Γ n) := by
  exact
    width_compact_compression
      (p := p)
      (Γ := Γ)
      (n := n)
      P.subgroup_expansion_compression

lemma algebraic_cover
    {p : ℕ}
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ]
    {n : ℕ}
    (P :
      DCPackag
        p Γ n) :
    Nonempty (ACCover p Γ n) := by
  exact
    gens_algebraic_compression
      (p := p)
      (Γ := Γ)
      (n := n)
      P.subgroup_expansion_compression

lemma exists_compactCover
    {p : ℕ}
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [T2Space Γ]
    {n : ℕ}
    (P :
      DCPackag
        p Γ n) :
    Nonempty (FCCover p Γ n) := by
  rcases P.algebraic_cover with ⟨C⟩
  exact ⟨C.toCompactCover⟩

end DCPackag

lemma
    dense_gens_pointwise
    {p : ℕ}
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    {n : ℕ}
    (h :
      ∃ k : ℕ,
        ∃ V : Fin k → WLWord p Γ n,
          Nonempty
            (ZPFact V)) :
    ∃ k : ℕ,
      ∃ V : Fin k → WLWord p Γ n,
        Nonempty
          (WLRed V) := by
  rcases h with ⟨k, V, hV⟩
  rcases hV with ⟨H⟩
  exact ⟨k, V, ⟨H.toListReduction⟩⟩

lemma
    compact_cover_pointwise
    {p : ℕ}
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ]
    {n : ℕ}
    (h :
      ∃ k : ℕ,
        ∃ V : Fin k → WLWord p Γ n,
          Nonempty
            (ZPFact V)) :
    Nonempty (WCCover p Γ n) := by
  rcases h with ⟨k, V, hV⟩
  rcases hV with ⟨H⟩
  exact ⟨H.toListReduction.unionCompactCover⟩

lemma
    algebraic_cover_pointwise
    {p : ℕ}
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ]
    {n : ℕ}
    (h :
      ∃ k : ℕ,
        ∃ V : Fin k → WLWord p Γ n,
          Nonempty
            (ZPFact V)) :
    Nonempty (ACCover p Γ n) := by
  rcases h with ⟨k, V, hV⟩
  rcases hV with ⟨H⟩
  exact ⟨H.toListReduction.unionCompactCover.listCompactCover.algebraicCompactCover⟩

end Submission
