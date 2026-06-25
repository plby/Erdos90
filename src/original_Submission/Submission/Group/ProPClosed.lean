import Mathlib
import Submission.Group.PGroup
import Submission.Group.ProPTopology
import Submission.Group.Zassenhaus.Core
import Submission.Group.TwoDimensionSubgroup
import Submission.Group.Zassenhaus.ChapmanEfrat
import Submission.Group.Zassenhaus.FinitePGroup
import Submission.Group.Zassenhaus.RetainedOccurrenceBridges
import Submission.Group.ZassenhausFiniteQuotient.ResidualSeparation
import Submission.Group.ProPJennings

/-!
# Closedness of Zassenhaus terms in finitely generated pro-p groups

This file isolates the pro-`p`-specific closedness input needed by the
presentation layer.  Its proof should use a pro-`p` argument rather than the
general Nikolov-Segal or restricted-Burnside packages.
-/

open scoped Topology commutatorElement IsMulCommutative

noncomputable section

namespace Submission

universe u v

namespace ProP

open DGSep
open PPJennin
open TCTex

/-- A compact totally disconnected topological group is pro-`p` when all of its
quotients by open normal subgroups are finite `p`-groups. -/
def ProPGroup (p : ℕ) (G : Type u) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] : Prop :=
  ∀ N : OpenNormalSubgroup G, IsPGroup p (G ⧸ (N : Subgroup G))

/-- Open subgroups of compact totally disconnected pro-`p` groups are again
pro-`p`. -/
lemma pro_open_subgroup
    (p : ℕ)
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [TotallyDisconnectedSpace G]
    (hProP : ProPGroup p G)
    (K : Subgroup G)
    (hKopen : IsOpen ((K : Subgroup G) : Set G)) :
    ProPGroup p K := by
  intro N
  let imageN : Set G := Subtype.val '' ((N.toSubgroup : Subgroup K) : Set K)
  have hImageOpen : IsOpen imageN := by
    dsimp [imageN]
    exact hKopen.isOpenMap_subtype_val _ N.isOpen
  have hOneImage : (1 : G) ∈ imageN := by
    refine ⟨(1 : K), N.toSubgroup.one_mem, ?_⟩
    simp
  rcases
      ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one
        (G := G) hImageOpen hOneImage with
    ⟨M, hMImage⟩
  intro y
  refine QuotientGroup.induction_on y ?_
  intro k
  rcases hProP M (k : G) with ⟨a, ha⟩
  refine ⟨a, ?_⟩
  apply (QuotientGroup.eq_one_iff (N := N.toSubgroup) (k ^ (p ^ a))).mpr
  have hkM : (k : G) ^ (p ^ a) ∈ M.toSubgroup := by
    apply (QuotientGroup.eq_one_iff (N := M.toSubgroup) ((k : G) ^ (p ^ a))).mp
    simpa using ha
  rcases hMImage hkM with ⟨n, hnN, hn_eq⟩
  have hk_eq_n : k ^ (p ^ a) = n := by
    exact Subtype.ext (by simpa using hn_eq.symm)
  simpa [hk_eq_n] using hnN

/-- A finite family topologically generates a group when its algebraic subgroup
has dense image. -/
def TopologicallyGenerates {G : Type u} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] {ι : Type v} (s : ι → G) : Prop :=
  Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤

/--
Compact quotient reflection turns a uniform finite-`p`-group word-map family
and product-length bound into a compact product cover in the ambient pro-`p`
group.

This is the topology half of the argument.  The finite collection family and
bound are explicit inputs, so this lemma does not contain the finite group
theory and does not assert closedness.
-/
lemma algebraic_cover_collection
    (p : ℕ) [Fact p.Prime]
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [TotallyDisconnectedSpace G]
    (hProP : ProPGroup p G)
    {d : ℕ} (s : Fin d → G)
    (hs : TopologicallyGenerates s)
    (n : ℕ)
    (C : PGColl.{u} p d n) :
    Nonempty (ACCover p G n) := by
  classical
  letI : T2Space G :=
    t_space_disconnected G
  refine ⟨{
    width := C.bound
    pieces := C.pieces G
    pieces_compact := C.pieces_isCompact
    pieces_generators := C.pieces_subset_set
    subgroup_subset_product := ?_
  }⟩
  intro x hx
  have hxrange :
      x ∈ zassenhausProductImage (C.pieces G) := by
    by_contra hxnot
    have hrangeClosed :
        IsClosed (zassenhausProductImage (C.pieces G)) := by
      exact zassenhaus_image_closed C.pieces_isCompact
    rcases
        separate_sets_disconnected
          hrangeClosed x hxnot with
      ⟨N, hN⟩
    apply hN
    let q : G →* G ⧸ N.toSubgroup := QuotientGroup.mk' N.toSubgroup
    letI : DiscreteTopology (G ⧸ N.toSubgroup) :=
      pro_discrete_topology N
    letI : Finite (G ⧸ N.toSubgroup) :=
      pro_p_open N
    have hqGenerated :
        GeneratedBy (fun i : Fin d => q (s i)) := by
      exact
        pro_generated_image
          s hs q (pro_open_continuous N)
          (QuotientGroup.mk'_surjective N.toSubgroup)
    have hxq : q x ∈ zassenhausFiltration p (G ⧸ N.toSubgroup) n := by
      exact filtration_map_mem p n q hx
    rcases
        C.factor (G ⧸ N.toSubgroup) (hProP N)
          (fun i : Fin d => q (s i)) hqGenerated (q x) hxq with
      ⟨f, hprod⟩
    choose j hj using fun i =>
      (zassenhaus_union_image
        (K := C.family.ranges (G ⧸ N.toSubgroup))).mp
        (f i).property
    choose a ha using fun i => hj i
    let b :
        ∀ i : Fin C.bound,
          Fin ((C.family.slot (j i)).arity) → G :=
      fun i k =>
        (QuotientGroup.mk'_surjective N.toSubgroup (a i k)).choose
    have hb :
        ∀ i k, q (b i k) = a i k := by
      intro i k
      exact (QuotientGroup.mk'_surjective N.toSubgroup (a i k)).choose_spec
    let g : ∀ i : Fin C.bound, C.pieces G i :=
      fun i =>
        ⟨(C.family.slot (j i)).eval (b i),
          (zassenhaus_union_image
            (K := C.family.ranges G)).mpr
            ⟨j i, ⟨b i, rfl⟩⟩⟩
    have hg :
        ∀ i : Fin C.bound, q (g i : G) = (f i : G ⧸ N.toSubgroup) := by
      intro i
      dsimp [g]
      rw [(C.family.slot (j i)).eval_map q (b i)]
      rw [show (fun k => q (b i k)) = a i by
        funext k
        exact hb i k]
      exact ha i
    refine
      ⟨(List.ofFn fun i : Fin C.bound => (g i : G)).prod,
        ⟨g, rfl⟩,
        ?_⟩
    calc
      q (List.ofFn fun i : Fin C.bound => (g i : G)).prod =
          (List.ofFn fun i : Fin C.bound => q (g i : G)).prod := by
            rw [map_list_prod, List.map_ofFn]
            rfl
      _ = (List.ofFn fun i : Fin C.bound => (f i : G ⧸ N.toSubgroup)).prod := by
            apply congrArg List.prod
            apply congrArg List.ofFn
            funext i
            exact hg i
      _ = q x := hprod
  exact hxrange

/-- A uniform finite-`p`-group collection bound gives closedness of the
corresponding abstract Zassenhaus term in a topologically finitely generated
pro-`p` group. -/
lemma filtration_closed_collection
    (p : ℕ) [Fact p.Prime]
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [TotallyDisconnectedSpace G]
    (hProP : ProPGroup p G)
    {d : ℕ} (s : Fin d → G)
    (hs : TopologicallyGenerates s)
    (n : ℕ)
    (C : PGColl.{u} p d n) :
    IsClosed ((zassenhausFiltration p G n : Subgroup G) : Set G) := by
  classical
  letI : T2Space G :=
    t_space_disconnected G
  rcases
      algebraic_cover_collection
        p hProP s hs n C with
    ⟨K⟩
  have hproduct_closed :
      IsClosed (zassenhausProductImage K.pieces) :=
    K.product_isClosed
  have hproduct_subset :
      zassenhausProductImage K.pieces ⊆
        ((zassenhausFiltration p G n : Subgroup G) : Set G) :=
    image_subset_filtration
      (p := p) (Γ := G) (n := n) (K := K.pieces)
      K.pieces_generators
  have hset :
      ((zassenhausFiltration p G n : Subgroup G) : Set G) =
        zassenhausProductImage K.pieces :=
    Set.Subset.antisymm K.subgroup_subset_product hproduct_subset
  simpa [hset] using hproduct_closed

/-- Nonempty uniform finite-`p`-group collection data is enough for closedness. -/
lemma filtration_closed_nonempty
    (p : ℕ) [Fact p.Prime]
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [TotallyDisconnectedSpace G]
    (hProP : ProPGroup p G)
    {d : ℕ} (s : Fin d → G)
    (hs : TopologicallyGenerates s)
    (n : ℕ)
    (hC : Nonempty (PGColl.{u} p d n)) :
    IsClosed ((zassenhausFiltration p G n : Subgroup G) : Set G) := by
  rcases hC with ⟨C⟩
  exact
    filtration_closed_collection
      p hProP s hs n C

/-- A free lower-central truncation collection bound gives closedness after
transporting it through the finite-`p`-group collection package. -/
lemma filtration_closed_bound
    (p : ℕ) [Fact p.Prime]
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [TotallyDisconnectedSpace G]
    (hProP : ProPGroup p G)
    {d : ℕ} (s : Fin d → G)
    (hs : TopologicallyGenerates s)
    {n : ℕ}
    (hn : 2 ≤ n)
    (hfree : ∃ k : ℕ,
      TCTex.TruncationCollectionBound.{u}
        p d n k) :
    IsClosed ((zassenhausFiltration p G n : Subgroup G) : Set G) := by
  apply
    filtration_closed_nonempty
      p hProP s hs n
  exact
    collection_truncation_bound
      p d n hn hfree

/-- Hall collection-polynomial inputs give closedness via the finite
`p`-group collection package. -/
lemma closed_collection_inputs
    (p : ℕ) [Fact p.Prime]
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [TotallyDisconnectedSpace G]
    (hProP : ProPGroup p G)
    {d : ℕ} (s : Fin d → G)
    (hs : TopologicallyGenerates s)
    {n : ℕ}
    (hn : 2 ≤ n)
    (I : Ctex.HallCollectionInputs.{u} d n) :
    IsClosed ((zassenhausFiltration p G n : Subgroup G) : Set G) := by
  exact
    filtration_closed_nonempty
      p hProP s hs n
      (p_collection_inputs
        (p := p) (d := d) (n := n) hn I)

/-- Concrete Hall-coordinate divisibility for the free lower-central truncation
gives closedness after the finite-`p`-group collection transport. -/
lemma filtration_closed_divisibility
    (p : ℕ) [Fact p.Prime]
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [TotallyDisconnectedSpace G]
    (hProP : ProPGroup p G)
    {d : ℕ} (s : Fin d → G)
    (hs : TopologicallyGenerates s)
    {n : ℕ}
    (hn : 2 ≤ n)
    (hdiv :
      let H : ∀ r : ℕ, TCTex.BCWta.{u} d r :=
        TCTex.collectionConcreteCommutators.{u} d
      let hH :
        ∀ r : ℕ,
          1 ≤ r →
            r < n →
              (H r).FormsAssocGradedbasis (n := n) :=
        fun r hr hrn =>
          TCTex.concrete_forms_associated
            d n r hr hrn
      ∀ y :
          TCTex.LowerCentralTruncation
            (FreeGroup (TCTex.FreeGenerator.{u} d)) n,
        y ∈ zassenhausFiltration
          p
          (TCTex.LowerCentralTruncation
            (FreeGroup (TCTex.FreeGenerator.{u} d)) n)
          n →
          TCTex.HallCoordinateLattice (p := p) hn H hH y) :
    IsClosed ((zassenhausFiltration p G n : Subgroup G) : Set G) := by
  exact
    filtration_closed_nonempty
      p hProP s hs n
      (collection_concrete_divisibility
        (p := p) (d := d) (n := n) hn hdiv)

/-- A concrete Hall-coordinate lattice subgroup, plus the Hall power
coordinate input for powered lower-central generators, gives closedness. -/
lemma filtration_closed_lattice
    (p : ℕ) [Fact p.Prime]
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [TotallyDisconnectedSpace G]
    (hProP : ProPGroup p G)
    {d : ℕ} (s : Fin d → G)
    (hs : TopologicallyGenerates s)
    {n : ℕ}
    (hn : 2 ≤ n)
    (hpower :
      let H : ∀ r : ℕ, TCTex.BCWta.{u} d r :=
        TCTex.collectionConcreteCommutators.{u} d
      ∀ (e : TCTex.HEFam H) (t : ℕ),
        1 ≤ t →
          TCTex.CollectedPolynomialData
            (n := n) H e t)
    (L :
      Subgroup
        (TCTex.LowerCentralTruncation
          (FreeGroup (TCTex.FreeGenerator.{u} d)) n))
    (hL :
      let H : ∀ r : ℕ, TCTex.BCWta.{u} d r :=
        TCTex.collectionConcreteCommutators.{u} d
      let hH :
        ∀ r : ℕ,
          1 ≤ r →
            r < n →
              (H r).FormsAssocGradedbasis (n := n) :=
        fun r hr hrn =>
          TCTex.concrete_forms_associated
            d n r hr hrn
      ∀ y :
          TCTex.LowerCentralTruncation
            (FreeGroup (TCTex.FreeGenerator.{u} d)) n,
        y ∈ L ↔
          TCTex.HallCoordinateLattice
            (p := p) hn H hH y) :
    IsClosed ((zassenhausFiltration p G n : Subgroup G) : Set G) := by
  exact
    filtration_closed_bound
      p hProP s hs hn
      (free_truncation_lattice
        p d n hn
        (collectionConcreteCommutators.{u} d)
        (fun r hr hrn =>
          concrete_forms_associated
            d n r hr hrn)
        hpower
        L
        hL)

/-- A concrete lower-triangular Hall `g h` law gives closedness after it is
converted to Hall collection-polynomial inputs. -/
lemma closed_gh_law
    (p : ℕ) [Fact p.Prime]
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [TotallyDisconnectedSpace G]
    (hProP : ProPGroup p G)
    {d : ℕ} (s : Fin d → G)
    (hs : TopologicallyGenerates s)
    {n : ℕ}
    (hn : 2 ≤ n)
    (law :
      TCTex.LGLaw
        (n := n)
        (TCTex.concreteCommutatorsWeight.{u} d)) :
    IsClosed ((zassenhausFiltration p G n : Subgroup G) : Set G) := by
  exact
    filtration_closed_nonempty
      p hProP s hs n
      (collection_triangular_gh
        (p := p) (d := d) (n := n) hn law)

/-- Payload-shaped concrete Hall law data gives closedness.  This matches the
shape of the old `concreteHallTriangularGHLaw` endpoint while using the
currently verified bridge. -/
lemma triangular_law_payload
    (p : ℕ) [Fact p.Prime]
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [TotallyDisconnectedSpace G]
    (hProP : ProPGroup p G)
    {d : ℕ} (s : Fin d → G)
    (hs : TopologicallyGenerates s)
    {n : ℕ}
    (hn : 2 ≤ n)
    (htri :
      let H : ∀ r : ℕ, TCTex.BCWta.{u} d r :=
        TCTex.collectionConcreteCommutators.{u} d
      (∀ r : ℕ,
          1 ≤ r →
            r < n →
              (H r).FormsAssocGradedbasis (n := n)) ∧
        Nonempty (TCTex.LGLaw (n := n) H)) :
    IsClosed ((zassenhausFiltration p G n : Subgroup G) : Set G) := by
  exact
    filtration_closed_nonempty
      p hProP s hs n
      (gh_law_payload
        (p := p) (d := d) (n := n) hn htri)

/-- Retained-recipe collection inputs give closedness via the free-truncation
collection bound. -/
lemma filtration_collection_inputs
    (p : ℕ) [Fact p.Prime]
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [TotallyDisconnectedSpace G]
    (hProP : ProPGroup p G)
    {d : ℕ} (s : Fin d → G)
    (hs : TopologicallyGenerates s)
    {n : ℕ}
    (hn : 2 ≤ n)
    (I : Ctex.RCInputs.{u} d n) :
    IsClosed ((zassenhausFiltration p G n : Subgroup G) : Set G) := by
  exact
    filtration_closed_bound
      p hProP s hs hn
      (Ctex.uniform_recipe_inputs
        (p := p) (d := d) (n := n) hn I)

/-- Occurrence-level retained collection inputs give closedness via the
retained-recipe bridge. -/
lemma closed_occurrence_inputs
    (p : ℕ) [Fact p.Prime]
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [TotallyDisconnectedSpace G]
    (hProP : ProPGroup p G)
    {d : ℕ} (s : Fin d → G)
    (hs : TopologicallyGenerates s)
    {n : ℕ}
    (hn : 2 ≤ n)
    (I : TCTex.OCInputs.{u} d n) :
    IsClosed ((zassenhausFiltration p G n : Subgroup G) : Set G) := by
  exact
    filtration_collection_inputs
      p hProP s hs hn I.retained_recipe_collectinputs

/-- Finite-index trace/profile collection inputs give closedness via the
free-truncation collection bound. -/
lemma filtration_closed_inputs
    (p : ℕ) [Fact p.Prime]
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [TotallyDisconnectedSpace G]
    (hProP : ProPGroup p G)
    {d : ℕ} (s : Fin d → G)
    (hs : TopologicallyGenerates s)
    {n : ℕ}
    (hn : 2 ≤ n)
    (I : Ctex.ProfileCollectionInputs.{u} d n) :
    IsClosed ((zassenhausFiltration p G n : Subgroup G) : Set G) := by
  exact
    filtration_closed_bound
      p hProP s hs hn
      (Ctex.uniform_collection_inputs
        (p := p) (d := d) (n := n) hn I)

/-- Scalar finite-index trace-count collection inputs give closedness via the
free-truncation collection bound. -/
lemma closed_scalar_inputs
    (p : ℕ) [Fact p.Prime]
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [TotallyDisconnectedSpace G]
    (hProP : ProPGroup p G)
    {d : ℕ} (s : Fin d → G)
    (hs : TopologicallyGenerates s)
    {n : ℕ}
    (hn : 2 ≤ n)
    (I : Ctex.SCInputs.{u} d n) :
    IsClosed ((zassenhausFiltration p G n : Subgroup G) : Set G) := by
  exact
    filtration_closed_bound
      p hProP s hs hn
      (Ctex.uniform_scalar_inputs
        (p := p) (d := d) (n := n) hn I)

/-- Decomposed scheduled multiplicity collection inputs give closedness via
the free-truncation collection bound. -/
lemma closed_decomposed_inputs
    (p : ℕ) [Fact p.Prime]
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [TotallyDisconnectedSpace G]
    (hProP : ProPGroup p G)
    {d : ℕ} (s : Fin d → G)
    (hs : TopologicallyGenerates s)
    {n : ℕ}
    (hn : 2 ≤ n)
    (I : Ctex.DecomposedSchedulerInputs.{u} d n) :
    IsClosed ((zassenhausFiltration p G n : Subgroup G) : Set G) := by
  exact
    filtration_closed_bound
      p hProP s hs hn
      (Ctex.uniform_decomposed_inputs
        (p := p) (d := d) (n := n) hn I)

/-- Universal signed-block collection inputs give closedness via the
free-truncation collection bound. -/
lemma closed_universal_inputs
    (p : ℕ) [Fact p.Prime]
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [TotallyDisconnectedSpace G]
    (hProP : ProPGroup p G)
    {d : ℕ} (s : Fin d → G)
    (hs : TopologicallyGenerates s)
    {n : ℕ}
    (hn : 2 ≤ n)
    (I : Ctex.UniversalCollectionInputs.{u} d n) :
    IsClosed ((zassenhausFiltration p G n : Subgroup G) : Set G) := by
  exact
    filtration_closed_bound
      p hProP s hs hn
      (Ctex.uniform_universal_inputs
        (p := p) (d := d) (n := n) hn I)

/-- The finite NS/RBT prime-power package gives closedness through finite
quotient residual separation. -/
lemma filtration_closed_nsrbt
    (p : ℕ) [Fact p.Prime]
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [TotallyDisconnectedSpace G]
    {d : ℕ} (s : Fin d → G)
    (hs : TopologicallyGenerates s)
    (n : ℕ)
    (hNS : NPPower.{u} d p n) :
    IsClosed ((zassenhausFiltration p G n : Subgroup G) : Set G) := by
  by_cases hn : n ≤ 1
  · rw [zassenhaus_filtration_top p G hn]
    exact isClosed_univ
  have hn' : 1 < n := by omega
  exact
    (dense_separation_nsrbt
      (p := p) (Γ := G) s hs hn' hNS).closed_zassenhaus_filtration

/--
A same-core dense-span positive Jennings input gives finite-quotient residual
separation for `D_n`.  The bounded-word part is formal from density of the
chosen generators; the positive Jennings input supplies the kernel identity.
-/
noncomputable def
    separation_jennings_input
    (p : ℕ) [Fact p.Prime]
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [TotallyDisconnectedSpace G]
    {d : ℕ} (s : Fin d → G)
    (hs : TopologicallyGenerates s)
    {n : ℕ}
    (H :
      ∃ C : DCCore
          (p := p) (Γ := G) s hs n,
        C.DenseSpanposJenningsinput) :
    DGSep p G n := by
  classical
  let C : DCCore
      (p := p) (Γ := G) s hs n :=
    Classical.choose H
  have HC : C.DenseSpanposJenningsinput :=
    Classical.choose_spec H
  have hpositiveRaw : C.BoundedwordSpanposRawinputs := by
    exact ⟨HC.1, C.posdense_subgroupspan_signedwords (s := s) (n := n)⟩
  have hraw : C.BoundedWordspanRawinputs :=
    C.boundedword_spanrawinputs_posrawinputs
      (s := s) (n := n) hpositiveRaw
  have hproof : C.BoundedWordspanProofinputs :=
    C.boundedword_spanproof_inputsrawinputs
      (s := s) (n := n) hraw
  have hbounded : C.BoundedAugWordspan :=
    C.bounded_wordspan_proofinputs
      (s := s) (n := n) hproof
  have hcore :
      ∃ C : DCCore
          (p := p) (Γ := G) s hs n,
        Finite C.augmentationQuotient ∧
          (letI := C.quotientTopology
          DiscreteTopology C.quotientUnitMap.range) ∧
          Nonempty (DenseLazardIdentification C) :=
    gens_completed_input
      (p := p) (Γ := G) (s := s) (hs := hs) (n := n)
      ⟨C, hbounded, HC.2⟩
  refine
    { test_not := ?_ }
  intro g hg
  let C' : DCCore
      (p := p) (Γ := G) s hs n :=
    Classical.choose hcore
  have hcore' :
      Finite C'.augmentationQuotient ∧
        (letI := C'.quotientTopology
        DiscreteTopology C'.quotientUnitMap.range) ∧
        Nonempty (DenseLazardIdentification C') :=
    Classical.choose_spec hcore
  rcases hcore' with ⟨hfinite, hdiscrete, hJ⟩
  let J : DenseLazardIdentification C' :=
    Classical.choice hJ
  let hmodel :=
      model_discrete_core
        (p := p) (Γ := G) (s := s) (hs := hs) (n := n)
        C' J hfinite hdiscrete
  let M : DCModel
      (p := p) (Γ := G) s hs n :=
    Classical.choose hmodel
  have hmodel' :
      Finite M.augmentationQuotient ∧
        (letI := M.quotientTopology
        DiscreteTopology M.quotientUnitMap.range) :=
    Classical.choose_spec hmodel
  rcases hmodel' with ⟨hfiniteM, hdiscreteM⟩
  exact
    M.test_not_target
      (p := p) (Γ := G) (s := s) (hs := hs) (n := n)
      hfiniteM hdiscreteM hg

/-- Same-core dense-span positive Jennings input implies closedness of `D_n`. -/
lemma closed_jennings_input
    (p : ℕ) [Fact p.Prime]
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [TotallyDisconnectedSpace G]
    {d : ℕ} (s : Fin d → G)
    (hs : TopologicallyGenerates s)
    {n : ℕ}
    (H :
      ∃ C : DCCore
          (p := p) (Γ := G) s hs n,
        C.DenseSpanposJenningsinput) :
    IsClosed ((zassenhausFiltration p G n : Subgroup G) : Set G) :=
  (separation_jennings_input
    p s hs H).closed_zassenhaus_filtration

/--
Finite-shadow intersection plus finite ordinary Jennings upper control gives
closedness through the completed group-algebra route.
-/
lemma shadow_intersection_bound
    (p : ℕ) [Fact p.Prime]
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [TotallyDisconnectedSpace G]
    {d : ℕ} (s : Fin d → G)
    (hs : TopologicallyGenerates s)
    {n : ℕ}
    (hn : 1 < n)
    (Hshadow : PPJennin.FiniteShadowIntersection
      (p := p) (Γ := G) s hs n)
    (Hfinite :
      DenseUpperBound.{u}
        (p := p) n) :
    IsClosed ((zassenhausFiltration p G n : Subgroup G) : Set G) := by
  exact
    closed_jennings_input
      p s hs
      (core_shadow_intersection
        (p := p) (Γ := G) s hs hn Hshadow Hfinite)

/-- The closure of the mod-`p` Frattini subgroup is open whenever a finitely
generated abstract group maps densely into the ambient group.

This is the finite elementary-abelian quotient argument: after quotienting by
the closed Frattini closure, the dense finitely generated image is a finitely
generated torsion abelian group of exponent `p`, hence finite; density in a
Hausdorff group then makes the whole quotient finite. -/
lemma mod_topological_fg
    (p : ℕ) [Fact p.Prime]
    {K L : Type u} [Group K] [TopologicalSpace K] [IsTopologicalGroup K]
    [T2Space K] [Group L] [Group.FG L]
    (ι : L →* K)
    (hι : DenseRange ι) :
    IsOpen
      (((modPFrattini p K).topologicalClosure : Subgroup K) : Set K) := by
  let Φ : Subgroup K := modPFrattini p K
  let C : Subgroup K := Φ.topologicalClosure
  letI : Φ.Normal := by
    dsimp [Φ]
    infer_instance
  letI : C.Normal := by
    dsimp [C]
    exact Subgroup.is_normal_topologicalClosure Φ
  letI : IsClosed (C : Set K) := by
    dsimp [C]
    exact Subgroup.isClosed_topologicalClosure Φ
  let q : K →* K ⧸ C := QuotientGroup.mk' C
  let r : L →* K ⧸ C := q.comp ι
  let P : Subgroup (K ⧸ C) := r.range
  letI : IsMulCommutative (K ⧸ C) :=
    (Subgroup.Normal.quotient_commutative_iff_commutator_le
      (N := C)).2
      ((le_sup_right : _root_.commutator K ≤ modPFrattini p K).trans
        Φ.le_topologicalClosure)
  letI : CommGroup (K ⧸ C) := inferInstance
  have hpow : ∀ y : K ⧸ C, y ^ p = 1 := by
    intro y
    refine QuotientGroup.induction_on y ?_
    intro k
    apply (QuotientGroup.eq_one_iff (N := C) (k ^ p)).2
    exact Φ.le_topologicalClosure (pow_mod_frattini p K k)
  haveI : Group.FG P := by
    dsimp [P]
    infer_instance
  have hP_torsion : Monoid.IsTorsion P := by
    intro y
    exact
      isOfFinOrder_iff_pow_eq_one.mpr
        ⟨p, (Fact.out : Nat.Prime p).pos, by
          apply Subtype.ext
          exact hpow y⟩
  letI : Finite P :=
    CommGroup.finite_of_fg_torsion P hP_torsion
  have hr_dense : DenseRange r := by
    exact
      (QuotientGroup.mk'_surjective C).denseRange.comp hι
        QuotientGroup.continuous_mk
  have hP_dense :
      closure ((P : Subgroup (K ⧸ C)) : Set (K ⧸ C)) =
        Set.univ := by
    simpa [P, r, q] using hr_dense.closure_range
  letI : Finite (K ⧸ C) :=
    finite_dense_subgroup P hP_dense
  letI : C.FiniteIndex :=
    Subgroup.finiteIndex_of_finite_quotient
  exact C.isOpen_of_isClosed_of_finiteIndex inferInstance

/-- If `D₂` is closed and the ambient group has a dense finitely generated
abstract subgroup, then `D₂` is open. -/
lemma filtration_fg_closed
    (p : ℕ) [Fact p.Prime]
    {K L : Type u} [Group K] [TopologicalSpace K] [IsTopologicalGroup K]
    [T2Space K] [Group L] [Group.FG L]
    (ι : L →* K)
    (hι : DenseRange ι)
    (hDclosed :
      IsClosed ((zassenhausFiltration p K 2 : Subgroup K) : Set K)) :
    IsOpen ((zassenhausFiltration p K 2 : Subgroup K) : Set K) := by
  let Φ : Subgroup K := modPFrattini p K
  have hΦclosed : IsClosed (Φ : Set K) := by
    simpa [Φ, filtration_p_frattini (p := p) K] using
      hDclosed
  have hΦclosure_eq : Φ.topologicalClosure = Φ := by
    exact le_antisymm
      (Φ.topologicalClosure_minimal le_rfl hΦclosed)
      Φ.le_topologicalClosure
  have hΦclosure_open :
      IsOpen ((Φ.topologicalClosure : Subgroup K) : Set K) :=
    mod_topological_fg
      (p := p) (K := K) (L := L) ι hι
  have hΦopen : IsOpen (Φ : Set K) := by
    simpa [hΦclosure_eq] using hΦclosure_open
  simpa [Φ, filtration_p_frattini (p := p) K] using
    hΦopen

/-- In a topologically finitely generated pro-`p` group, the second
Zassenhaus term is open.  This is a useful non-NS base case for Frattini-style
inductive approaches to the full closedness theorem. -/
lemma filtration_pro_p
    (p : ℕ) [Fact p.Prime]
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [TotallyDisconnectedSpace G]
    (hProP : ProPGroup p G)
    {d : ℕ} (s : Fin d → G)
    (hs : TopologicallyGenerates s) :
    IsOpen ((zassenhausFiltration p G 2 : Subgroup G) : Set G) := by
  classical
  letI : T2Space G :=
    t_space_disconnected G
  let H : Subgroup G := Subgroup.closure (Set.range s)
  have hHdense : Dense (H : Set G) := by
    rw [dense_iff_closure_eq]
    simpa [H, Subgroup.topologicalClosure_coe] using
      congrArg (fun L : Subgroup G => (L : Set G)) hs
  let ι : H →* G := H.subtype
  have hιdense : DenseRange ι := by
    rw [DenseRange, dense_iff_closure_eq]
    simpa [ι, H.range_subtype] using hHdense.closure_eq
  haveI : Group.FG H := by
    dsimp [H]
    infer_instance
  let Φ : Subgroup G := modPFrattini p G
  have hΦclosed : IsClosed (Φ : Set G) := by
    have hDclosed :
        IsClosed ((zassenhausFiltration p G 2 : Subgroup G) : Set G) :=
      filtration_closed_nonempty
        p hProP s hs 2
        (collection_n_four p d 2
          (by norm_num))
    simpa [Φ, filtration_p_frattini (p := p) G] using
      hDclosed
  have hΦclosure_eq : Φ.topologicalClosure = Φ := by
    exact le_antisymm
      (Φ.topologicalClosure_minimal le_rfl hΦclosed)
      Φ.le_topologicalClosure
  have hΦclosure_open :
      IsOpen ((Φ.topologicalClosure : Subgroup G) : Set G) :=
    mod_topological_fg
      (p := p) (K := G) (L := H) ι hιdense
  have hΦopen : IsOpen (Φ : Set G) := by
    simpa [hΦclosure_eq]
      using hΦclosure_open
  simpa [Φ, filtration_p_frattini (p := p) G] using
    hΦopen

/-- In a topologically finitely generated pro-`p` group, the mod-`p`
Frattini subgroup is open. -/
lemma mod_open_pro
    (p : ℕ) [Fact p.Prime]
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [TotallyDisconnectedSpace G]
    (hProP : ProPGroup p G)
    {d : ℕ} (s : Fin d → G)
    (hs : TopologicallyGenerates s) :
    IsOpen ((modPFrattini p G : Subgroup G) : Set G) := by
  simpa [filtration_p_frattini (p := p) G] using
    filtration_pro_p
      (p := p) hProP s hs

/-- If a finitely generated dense subgroup meets an open subgroup, the
intersection is dense in the open subgroup. -/
lemma dense_open_closure
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {d : ℕ} (s : Fin d → G)
    (hs : TopologicallyGenerates s)
    (K : Subgroup G)
    (hKopen : IsOpen ((K : Subgroup G) : Set G)) :
    let H : Subgroup G := Subgroup.closure (Set.range s)
    let L : Subgroup H := K.subgroupOf H
    DenseRange
      ({ toFun := fun x : L => (⟨x, x.property⟩ : K)
         map_one' := rfl
         map_mul' := fun _ _ => rfl } : L →* K) := by
  classical
  let H : Subgroup G := Subgroup.closure (Set.range s)
  have hHdense : Dense (H : Set G) := by
    rw [dense_iff_closure_eq]
    simpa [H, Subgroup.topologicalClosure_coe] using
      congrArg (fun L : Subgroup G => (L : Set G)) hs
  let L : Subgroup H := K.subgroupOf H
  let ι : L →* K :=
    { toFun := fun x => ⟨x, x.property⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  change DenseRange ι
  rw [DenseRange, dense_iff_closure_eq]
  apply Set.eq_univ_of_forall
  intro k
  rw [closure_subtype]
  have hk :
      (k : G) ∈ closure ((K : Set G) ∩ (H : Set G)) :=
    hHdense.open_subset_closure_inter hKopen k.property
  apply closure_mono _ hk
  rintro g ⟨hgK, hgH⟩
  refine ⟨⟨g, hgK⟩, ?_, rfl⟩
  exact ⟨⟨⟨g, hgH⟩, hgK⟩, rfl⟩

/-- The intersection of an open subgroup with a finitely generated dense
subgroup is again finitely generated. -/
lemma open_closure_fg
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G]
    {d : ℕ} (s : Fin d → G)
    (_hs : TopologicallyGenerates s)
    (K : Subgroup G)
    (hKopen : IsOpen ((K : Subgroup G) : Set G)) :
    let H : Subgroup G := Subgroup.closure (Set.range s)
    Group.FG (K.subgroupOf H) := by
  classical
  letI : K.FiniteIndex := by
    letI : Finite (G ⧸ K) := K.quotient_finite_of_isOpen hKopen
    exact Subgroup.finiteIndex_of_finite_quotient
  let H : Subgroup G := Subgroup.closure (Set.range s)
  haveI : Group.FG H := by
    dsimp [H]
    infer_instance
  let L : Subgroup H := K.subgroupOf H
  haveI : L.FiniteIndex := by
    dsimp [L]
    infer_instance
  exact (inferInstance : Group.FG L)

/-- A dense homomorphic image of an abstract finitely generated group gives a
finite topological generating tuple. -/
lemma topologically_generates_fg
    {K L : Type u} [Group K] [TopologicalSpace K] [IsTopologicalGroup K]
    [Group L] [Group.FG L]
    (ι : L →* K)
    (hι : DenseRange ι) :
    ∃ d : ℕ, ∃ s : Fin d → K, TopologicallyGenerates s := by
  classical
  obtain ⟨_m, S, _hScard, hSgen⟩ :=
    Group.fg_iff'.mp (inferInstance : Group.FG L)
  let t : Fin S.card → L := fun i => (S.equivFin.symm i : L)
  let sK : Fin S.card → K := fun i => ι (t i)
  refine ⟨S.card, sK, ?_⟩
  have ht_range : Set.range t = (S : Set L) := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact (S.equivFin.symm i).property
    · intro hx
      refine ⟨S.equivFin ⟨x, hx⟩, ?_⟩
      simp [t]
  have ht_gen : Subgroup.closure (Set.range t) = (⊤ : Subgroup L) := by
    simpa [ht_range] using hSgen
  have hmap :
      (Subgroup.closure (Set.range t)).map ι =
        Subgroup.closure (Set.range sK) := by
    rw [MonoidHom.map_closure]
    congr 1
    ext y
    constructor
    · rintro ⟨x, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨t i, ⟨i, rfl⟩, rfl⟩
  have hclosure_eq_range :
      Subgroup.closure (Set.range sK) = ι.range := by
    rw [← hmap, ht_gen]
    ext y
    constructor
    · rintro ⟨x, _hx, rfl⟩
      exact ⟨x, rfl⟩
    · rintro ⟨x, rfl⟩
      exact ⟨x, trivial, rfl⟩
  have hι_dense :
      closure ((ι.range : Subgroup K) : Set K) = Set.univ := by
    simpa [MonoidHom.range_eq_map] using hι.closure_range
  apply SetLike.ext
  intro x
  rw [hclosure_eq_range]
  change x ∈ closure ((ι.range : Subgroup K) : Set K) ↔
    x ∈ (Set.univ : Set K)
  rw [hι_dense]

/-- Degree-two openness for an open subgroup, reduced to closedness of its
degree-two Zassenhaus term. -/
lemma filtration_open_closed
    (p : ℕ) [Fact p.Prime]
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G]
    {d : ℕ} (s : Fin d → G)
    (hs : TopologicallyGenerates s)
    (K : Subgroup G)
    (hKopen : IsOpen ((K : Subgroup G) : Set G))
    (hDclosed :
      IsClosed ((zassenhausFiltration p K 2 : Subgroup K) : Set K)) :
    IsOpen ((zassenhausFiltration p K 2 : Subgroup K) : Set K) := by
  classical
  let H : Subgroup G := Subgroup.closure (Set.range s)
  let L : Subgroup H := K.subgroupOf H
  let ι : L →* K :=
    { toFun := fun x => ⟨x, x.property⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  haveI : Group.FG L := by
    dsimp [L, H]
    exact
      open_closure_fg
        (G := G) s hs K hKopen
  have hι : DenseRange ι := by
    dsimp [ι, L, H]
    exact
      dense_open_closure
        (G := G) s hs K hKopen
  exact
    filtration_fg_closed
      (p := p) (K := K) (L := L) ι hι hDclosed

/-- The second Zassenhaus term is closed in any open subgroup of a
topologically finitely generated pro-`p` group. -/
lemma filtration_closed_pro
    (p : ℕ) [Fact p.Prime]
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [TotallyDisconnectedSpace G]
    (hProP : ProPGroup p G)
    {d : ℕ} (s : Fin d → G)
    (hs : TopologicallyGenerates s)
    (K : Subgroup G)
    (hKopen : IsOpen ((K : Subgroup G) : Set G)) :
    IsClosed ((zassenhausFiltration p K 2 : Subgroup K) : Set K) := by
  classical
  have hKclosed : IsClosed ((K : Subgroup G) : Set G) :=
    K.isClosed_of_isOpen hKopen
  letI : CompactSpace K :=
    isCompact_iff_compactSpace.mp hKclosed.isCompact
  let H : Subgroup G := Subgroup.closure (Set.range s)
  let L : Subgroup H := K.subgroupOf H
  let ι : L →* K :=
    { toFun := fun x => ⟨x, x.property⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  haveI : Group.FG L := by
    dsimp [L, H]
    exact
      open_closure_fg
        (G := G) s hs K hKopen
  have hι : DenseRange ι := by
    dsimp [ι, L, H]
    exact
      dense_open_closure
        (G := G) s hs K hKopen
  rcases
      topologically_generates_fg
        (K := K) (L := L) ι hι with
    ⟨e, t, ht⟩
  exact
    filtration_closed_nonempty
      p
      (pro_open_subgroup p hProP K hKopen)
      t ht 2
      (collection_n_four p e 2
        (by norm_num))

/-- The second Zassenhaus term is open in any open subgroup of a topologically
finitely generated pro-`p` group. -/
lemma filtration_open_pro
    (p : ℕ) [Fact p.Prime]
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [TotallyDisconnectedSpace G]
    (hProP : ProPGroup p G)
    {d : ℕ} (s : Fin d → G)
    (hs : TopologicallyGenerates s)
    (K : Subgroup G)
    (hKopen : IsOpen ((K : Subgroup G) : Set G)) :
    IsOpen ((zassenhausFiltration p K 2 : Subgroup K) : Set K) := by
  letI : T2Space G :=
    t_space_disconnected G
  exact
    filtration_open_closed
      p s hs K hKopen
      (filtration_closed_pro
        p hProP s hs K hKopen)

/--
The usual restricted-filtration laws imply the Frattini-step hypothesis used by
the topological induction below.
-/
lemma zassenhaus_frattini_comm
    (p : ℕ) [Fact p.Prime]
    {G : Type u} [Group G]
    {n : ℕ}
    (hpow :
      ∀ x : G,
        x ∈ zassenhausFiltration p G n →
          x ^ p ∈ zassenhausFiltration p G (n + 1))
    (hcomm :
      ∀ x y : G,
        x ∈ zassenhausFiltration p G n →
        y ∈ zassenhausFiltration p G n →
          ⁅x, y⁆ ∈ zassenhausFiltration p G (n + 1)) :
    Subgroup.map (zassenhausFiltration p G n).subtype
        (zassenhausFiltration p (zassenhausFiltration p G n) 2) ≤
      zassenhausFiltration p G (n + 1) := by
  classical
  let K : Subgroup G := zassenhausFiltration p G n
  let D : Subgroup G := zassenhausFiltration p G (n + 1)
  haveI : D.Normal := by
    dsimp [D]
    exact zassenhausFiltration_normal p G (n + 1)
  rw [filtration_p_frattini]
  refine Subgroup.map_le_iff_le_comap.mpr ?_
  rw [modPFrattini]
  refine sup_le ?_ ?_
  · dsimp [pPowerSubgroup]
    refine Subgroup.normalClosure_le_normal ?_
    rintro _ ⟨x, rfl⟩
    change ((x : K) : G) ^ p ∈ D
    exact hpow (x : G) x.property
  · rw [_root_.commutator_eq_closure]
    refine (Subgroup.closure_le _).mpr ?_
    rintro _ ⟨x, y, rfl⟩
    change ⁅(x : G), (y : G)⁆ ∈ D
    exact hcomm (x : G) (y : G) x.property y.property

/--
Conditional Frattini induction for Zassenhaus openness.

The remaining algebraic input is the step hypothesis: inside each ambient
term `D_n(G)`, the degree-two Zassenhaus term of that subgroup maps into
`D_{n+1}(G)`.
-/
lemma filtration_open_frattini
    (p : ℕ) [Fact p.Prime]
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [TotallyDisconnectedSpace G]
    (hProP : ProPGroup p G)
    {d : ℕ} (s : Fin d → G)
    (hs : TopologicallyGenerates s)
    (hstep :
      ∀ n : ℕ,
        1 ≤ n →
          Subgroup.map (zassenhausFiltration p G n).subtype
              (zassenhausFiltration p (zassenhausFiltration p G n) 2) ≤
            zassenhausFiltration p G (n + 1))
    (n : ℕ) :
    IsOpen ((zassenhausFiltration p G n : Subgroup G) : Set G) := by
  classical
  letI : T2Space G :=
    t_space_disconnected G
  induction n using Nat.strong_induction_on with
  | h n ih =>
      by_cases hn : n ≤ 1
      · rw [zassenhaus_filtration_top p G hn]
        exact isOpen_univ
      · cases n with
        | zero =>
            omega
        | succ m =>
            cases m with
            | zero =>
                omega
            | succ r =>
                let k : ℕ := r + 1
                have hkpos : 1 ≤ k := by
                  dsimp [k]
                  omega
                have hklt : k < Nat.succ (Nat.succ r) := by
                  dsimp [k]
                  omega
                let K : Subgroup G := zassenhausFiltration p G k
                have hKopen : IsOpen ((K : Subgroup G) : Set G) := by
                  dsimp [K]
                  exact ih k hklt
                have hD2open :
                    IsOpen
                      ((zassenhausFiltration p K 2 : Subgroup K) : Set K) := by
                  exact
                    filtration_open_pro
                      p hProP s hs K hKopen
                have hImageOpen :
                    IsOpen
                      (((Subgroup.map K.subtype
                            (zassenhausFiltration p K 2) : Subgroup G)) :
                          Set G) := by
                  rw [Subgroup.coe_map]
                  exact hKopen.isOpenMap_subtype_val _ hD2open
                have hle :
                    Subgroup.map K.subtype (zassenhausFiltration p K 2) ≤
                      zassenhausFiltration p G (k + 1) := by
                  dsimp [K]
                  exact hstep k hkpos
                have hopen :
                    IsOpen
                      ((zassenhausFiltration p G (k + 1) : Subgroup G) :
                        Set G) :=
                  Subgroup.isOpen_mono hle hImageOpen
                simpa [k, Nat.add_assoc] using hopen

/-- The product-form Zassenhaus filtration agrees with the recursive
Chapman--Efrat `q`-Zassenhaus filtration at `q = p`. -/
lemma zassenhaus_filtration_p
    (p : ℕ) [Fact p.Prime]
    {G : Type u} [Group G]
    {n : ℕ} (hn : 1 ≤ n) :
    zassenhausFiltration p G n =
      EChapma.qZassenhausFiltration G p p (Fact.out : p.Prime) n := by
  exact
    (CEfrat.explicit_logarithmic_product
      (G := G) p n (Fact.out : p.Prime) hn).trans
      (CEfrat.p_filtration_logarithmic
        (G := G) p n (Fact.out : p.Prime) hn).symm

/-- Restricted power law for the product-form Zassenhaus filtration. -/
lemma filtration_succ_self
    (p : ℕ) [Fact p.Prime]
    {G : Type u} [Group G]
    {n : ℕ} (hn : 1 ≤ n)
    {x : G}
    (hx : x ∈ zassenhausFiltration p G n) :
    x ^ p ∈ zassenhausFiltration p G (n + 1) := by
  classical
  let hp : p.Prime := Fact.out
  have hEqn :
      zassenhausFiltration p G n =
        EChapma.qZassenhausFiltration G p p hp n :=
    zassenhaus_filtration_p (p := p) (G := G) hn
  have hEqSucc :
      zassenhausFiltration p G (n + 1) =
        EChapma.qZassenhausFiltration G p p hp (n + 1) :=
    zassenhaus_filtration_p
      (p := p) (G := G) (by omega : 1 ≤ n + 1)
  have hxq :
      x ∈ EChapma.qZassenhausFiltration G p p hp n := by
    simpa [hEqn] using hx
  have hpowMul :
      x ^ p ∈ EChapma.qZassenhausFiltration G p p hp (n * p) :=
    EChapma.q_filtration_prime
      (G := G) p p n hp hn
      (EChapma.pow_subgroup_power
        (EChapma.qZassenhausFiltration G p p hp n) p hxq)
  have hsucc_le_mul : n + 1 ≤ n * p := by
    have hp2 : 2 ≤ p := hp.two_le
    have htwo : n + 1 ≤ n * 2 := by omega
    exact htwo.trans (Nat.mul_le_mul_left n hp2)
  have hpowSucc :
      x ^ p ∈ EChapma.qZassenhausFiltration G p p hp (n + 1) :=
    EChapma.q_filtration_antitone
      (G := G) p p hp (by omega : 1 ≤ n + 1) hsucc_le_mul hpowMul
  simpa [hEqSucc] using hpowSucc

/-- Restricted commutator law for the product-form Zassenhaus filtration. -/
lemma commutator_filtration_self
    (p : ℕ) [Fact p.Prime]
    {G : Type u} [Group G]
    {n : ℕ} (hn : 1 ≤ n)
    {x y : G}
    (hx : x ∈ zassenhausFiltration p G n)
    (hy : y ∈ zassenhausFiltration p G n) :
    ⁅x, y⁆ ∈ zassenhausFiltration p G (n + 1) := by
  classical
  let hp : p.Prime := Fact.out
  have hEqn :
      zassenhausFiltration p G n =
        EChapma.qZassenhausFiltration G p p hp n :=
    zassenhaus_filtration_p (p := p) (G := G) hn
  have hEqSucc :
      zassenhausFiltration p G (n + 1) =
        EChapma.qZassenhausFiltration G p p hp (n + 1) :=
    zassenhaus_filtration_p
      (p := p) (G := G) (by omega : 1 ≤ n + 1)
  have hxq :
      x ∈ EChapma.qZassenhausFiltration G p p hp n := by
    simpa [hEqn] using hx
  have hyq :
      y ∈ EChapma.qZassenhausFiltration G p p hp n := by
    simpa [hEqn] using hy
  have hcommAdd :
      ⁅x, y⁆ ∈ EChapma.qZassenhausFiltration G p p hp (n + n) :=
    EChapma.q_filtration_commutator
      (G := G) p p n n hp hn hn
      (Subgroup.commutator_mem_commutator hxq hyq)
  have hsucc_le_add : n + 1 ≤ n + n := by
    omega
  have hcommSucc :
      ⁅x, y⁆ ∈ EChapma.qZassenhausFiltration G p p hp (n + 1) :=
    EChapma.q_filtration_antitone
      (G := G) p p hp (by omega : 1 ≤ n + 1) hsucc_le_add hcommAdd
  simpa [hEqSucc] using hcommSucc

/--
The restricted laws put the mod-`p` Frattini subgroup of `D_n(G)` inside
`D_{n+1}(G)` for the product-form Zassenhaus filtration.
-/
lemma filtration_frattini_step
    (p : ℕ) [Fact p.Prime]
    {G : Type u} [Group G]
    (n : ℕ) (hn : 1 ≤ n) :
    Subgroup.map (zassenhausFiltration p G n).subtype
        (zassenhausFiltration p (zassenhausFiltration p G n) 2) ≤
      zassenhausFiltration p G (n + 1) :=
  zassenhaus_frattini_comm
    p
    (fun _ hx => filtration_succ_self p hn hx)
    (fun _ _ hx hy =>
      commutator_filtration_self p hn hx hy)

/--
In a topologically finitely generated pro-`p` group, every product-form
Zassenhaus term is open.
-/
theorem open_pro_p
    (p : ℕ) [Fact p.Prime]
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [TotallyDisconnectedSpace G]
    (hProP : ProPGroup p G)
    {d : ℕ} (s : Fin d → G)
    (hs : TopologicallyGenerates s)
    (n : ℕ) :
    IsOpen ((zassenhausFiltration p G n : Subgroup G) : Set G) :=
  filtration_open_frattini
    p hProP s hs
    (fun n hn => filtration_frattini_step p n hn)
    n

/--
The restricted Zassenhaus laws put the mod-`p` Frattini subgroup of
`D_n(G)` inside `D_{n+1}(G)` for the augmentation-defined Zassenhaus terms.
-/
lemma zassenhaus_frattini_step
    (p : ℕ) [Fact p.Prime]
    {G : Type u} [Group G]
    (n : ℕ) :
    Subgroup.map (GroupAlgebra.zSubgro p G n).subtype
        (GroupAlgebra.zSubgro p
          (GroupAlgebra.zSubgro p G n) 2) ≤
      GroupAlgebra.zSubgro p G (n + 1) := by
  classical
  let K : Subgroup G := GroupAlgebra.zSubgro p G n
  let D : Subgroup G := GroupAlgebra.zSubgro p G (n + 1)
  haveI : D.Normal := by
    dsimp [D]
    exact GroupAlgebra.zassenhausSubgroup_normal p G (n + 1)
  rw [zassenhaus_mod_frattini]
  refine Subgroup.map_le_iff_le_comap.mpr ?_
  rw [modPFrattini]
  refine sup_le ?_ ?_
  · dsimp [pPowerSubgroup]
    refine Subgroup.normalClosure_le_normal ?_
    rintro _ ⟨x, rfl⟩
    change ((x : K) : G) ^ p ∈ D
    exact
      GroupAlgebra.pow_succ_self
        (p := p) (G := G) x.property
  · rw [_root_.commutator_eq_closure]
    refine (Subgroup.closure_le _).mpr ?_
    rintro _ ⟨x, y, rfl⟩
    change ⁅(x : G), (y : G)⁆ ∈ D
    exact
      GroupAlgebra.commutator_succ_self
        (p := p) (G := G) x.property y.property

/--
Frattini induction for the augmentation-defined Zassenhaus terms.
-/
lemma open_frattini_step
    (p : ℕ) [Fact p.Prime]
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [TotallyDisconnectedSpace G]
    (hProP : ProPGroup p G)
    {d : ℕ} (s : Fin d → G)
    (hs : TopologicallyGenerates s)
    (hstep :
      ∀ n : ℕ,
        1 ≤ n →
          Subgroup.map (GroupAlgebra.zSubgro p G n).subtype
              (GroupAlgebra.zSubgro p
                (GroupAlgebra.zSubgro p G n) 2) ≤
            GroupAlgebra.zSubgro p G (n + 1))
    (n : ℕ) :
    IsOpen ((GroupAlgebra.zSubgro p G n : Subgroup G) : Set G) := by
  classical
  letI : T2Space G :=
    t_space_disconnected G
  induction n using Nat.strong_induction_on with
  | h n ih =>
      by_cases hn : n ≤ 1
      · rw [GroupAlgebra.zassenhaus_top_one p G hn]
        exact isOpen_univ
      · cases n with
        | zero =>
            omega
        | succ m =>
            cases m with
            | zero =>
                omega
            | succ r =>
                let k : ℕ := r + 1
                have hkpos : 1 ≤ k := by
                  dsimp [k]
                  omega
                have hklt : k < Nat.succ (Nat.succ r) := by
                  dsimp [k]
                  omega
                let K : Subgroup G := GroupAlgebra.zSubgro p G k
                have hKopen : IsOpen ((K : Subgroup G) : Set G) := by
                  dsimp [K]
                  exact ih k hklt
                have hD2open :
                    IsOpen
                      ((GroupAlgebra.zSubgro p K 2 :
                          Subgroup K) : Set K) := by
                  have hFiltrationD2open :
                      IsOpen
                        ((zassenhausFiltration p K 2 : Subgroup K) :
                          Set K) :=
                    filtration_open_pro
                      p hProP s hs K hKopen
                  simpa [
                    zassenhaus_mod_frattini
                      (p := p) (G := K),
                    filtration_p_frattini (p := p) K
                  ] using hFiltrationD2open
                have hImageOpen :
                    IsOpen
                      (((Subgroup.map K.subtype
                            (GroupAlgebra.zSubgro p K 2) :
                          Subgroup G)) :
                        Set G) := by
                  rw [Subgroup.coe_map]
                  exact hKopen.isOpenMap_subtype_val _ hD2open
                have hle :
                    Subgroup.map K.subtype
                        (GroupAlgebra.zSubgro p K 2) ≤
                      GroupAlgebra.zSubgro p G (k + 1) := by
                  dsimp [K]
                  exact hstep k hkpos
                have hopen :
                    IsOpen
                      ((GroupAlgebra.zSubgro p G (k + 1) :
                          Subgroup G) :
                        Set G) :=
                  Subgroup.isOpen_mono hle hImageOpen
                simpa [k, Nat.add_assoc] using hopen

/--
In a topologically finitely generated pro-`p` group, every augmentation-defined
Zassenhaus term is open.
-/
theorem open_pro_group
    (p : ℕ) [Fact p.Prime]
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [TotallyDisconnectedSpace G]
    (hProP : ProPGroup p G)
    {d : ℕ} (s : Fin d → G)
    (hs : TopologicallyGenerates s)
    (n : ℕ) :
    IsOpen ((GroupAlgebra.zSubgro p G n : Subgroup G) : Set G) :=
  open_frattini_step
    p hProP s hs
    (fun n _hn => zassenhaus_frattini_step p n)
    n

/--
In a topologically finitely generated pro-`p` group, every augmentation-defined
Zassenhaus term is closed.
-/
theorem closed_pro_group
    (p : ℕ) [Fact p.Prime]
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [TotallyDisconnectedSpace G]
    (hProP : ProPGroup p G)
    {d : ℕ} (s : Fin d → G)
    (hs : TopologicallyGenerates s)
    (n : ℕ) :
    IsClosed ((GroupAlgebra.zSubgro p G n : Subgroup G) : Set G) :=
  (GroupAlgebra.zSubgro p G n).isClosed_of_isOpen
    (open_pro_group p hProP s hs n)

/-- The closedness theorem in the elementary cases where the dense generating
tuple has at most one entry. -/
lemma filtration_closed_generators
    (p : ℕ) [Fact p.Prime]
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [TotallyDisconnectedSpace G]
    (hProP : ProPGroup p G)
    {d : ℕ} (s : Fin d → G)
    (hs : TopologicallyGenerates s)
    (hd : d ≤ 1)
    (n : ℕ) :
    IsClosed ((zassenhausFiltration p G n : Subgroup G) : Set G) := by
  rcases
      p_collection_generators
        (p := p) (d := d) (n := n) hd with
    ⟨Cfixed⟩
  exact
    filtration_closed_collection
      p hProP s hs n Cfixed.toCollection

/--
The abstract Zassenhaus filtration terms of a topologically finitely generated
pro-`p` group are closed.

This is the pro-`p`-specific group-theoretic input.  In particular, the
conclusion concerns the abstract subgroup `zassenhausFiltration p G n`, not
merely its topological closure.
-/
theorem closed_pro_p
    (p : ℕ) [Fact p.Prime]
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [TotallyDisconnectedSpace G]
    (hProP : ProPGroup p G)
    {d : ℕ} (s : Fin d → G)
    (hs : TopologicallyGenerates s)
    (n : ℕ) :
    IsClosed ((zassenhausFiltration p G n : Subgroup G) : Set G) :=
  (zassenhausFiltration p G n).isClosed_of_isOpen
    (open_pro_p p hProP s hs n)

end ProP

end Submission
