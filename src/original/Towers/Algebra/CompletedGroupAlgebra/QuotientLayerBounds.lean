import Mathlib
import Towers.Algebra.CompletedGroupAlgebra.CanonicalCarrier
import Towers.Algebra.CompletedGroupAlgebra.CoreBoundedWords


open scoped Topology Pointwise BigOperators

noncomputable section

namespace Towers

universe u
universe v w z

/-- Literal finite ideal quotients give finite formal algebraic augmentation quotients.

This is a packaging step.  From finiteness of the actual quotient by `I^m`, we choose the
canonical algebraic quotient record whose target is that literal quotient.  The quotient map,
surjectivity, and kernel equality are the formal quotient facts already used elsewhere; only the
finite type instance is imported from `FinPosIdealquots`. -/
lemma GCAmbien.finpos_algfin_idealquots
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (A : GCAmbien (p := p) (Γ := Γ) s hs)
    (Hquot : A.FinPosIdealquots) :
    A.FinPosalgAugquots := by
  intro m hm
  have haugmentation_two_sided : A.augmentationIdeal.IsTwoSided := by
    rw [show A.augmentationIdeal = RingHom.ker A.augmentationMap.toRingHom from
      A.augmentation_ideal_ker]
    infer_instance
  letI : A.augmentationIdeal.IsTwoSided := haugmentation_two_sided
  let I : Ideal A.completedGroupAlgebra := A.augmentationIdeal ^ m
  have hI_two_sided : I.IsTwoSided := by
    dsimp [I]
    infer_instance
  letI : I.IsTwoSided := hI_two_sided
  let quotientMap : A.completedGroupAlgebra →ₐ[ZMod p] A.completedGroupAlgebra ⧸ I :=
    Ideal.Quotient.mkₐ (ZMod p) I
  have hsurjective : Function.Surjective quotientMap := by
    simpa [quotientMap] using Ideal.Quotient.mkₐ_surjective (ZMod p) I
  have hker : RingHom.ker quotientMap.toRingHom = A.augmentationIdeal ^ m := by
    simp [quotientMap, I]
  let Q :
      GAAug
        (p := p) (Γ := Γ) (s := s) (hs := hs) m A := {
    augmentationQuotient := A.completedGroupAlgebra ⧸ I
    instQuotientRing := inferInstance
    instQuotientAlgebra := inferInstance
    quotientMap := quotientMap
    quotientMap_surjective := hsurjective
    quotientMap_ker := hker
  }
  have hfiniteQ : Finite Q.augmentationQuotient := by
    simpa [
      Q, I,
      GCAmbien.FinPosIdealquots
    ] using Hquot hm
  exact ⟨Q, hfiniteQ⟩

/-- Literal open augmentation powers give open kernels for every same-kernel algebraic truncation.

This is another packaging step.  A finite algebraic truncation does not need a new topological
argument: by definition its kernel is exactly `A.augmentationIdeal ^ m`, so openness of that
literal augmentation-power ideal transfers across the recorded kernel equality. -/
lemma GCAmbien.openkernel_openpos_augpowers
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (A : GCAmbien (p := p) (Γ := Γ) s hs)
    (Hopen : A.OpenPosAugpowers) :
    A.OpenkernelFinalgPostruncations := by
  intro m hm T
  have hopen_power : A.OpenAugPower m :=
    A.openaug_poweropen_posaugpowers
      (p := p) (Γ := Γ) (s := s) (hs := hs) Hopen hm
  have hopen_raw :
      IsOpen ((A.augmentationIdeal ^ m : Ideal A.completedGroupAlgebra) :
        Set A.completedGroupAlgebra) :=
    (A.openaug_poweriff_openaugpower
      (p := p) (Γ := Γ) (s := s) (hs := hs)).2 hopen_power
  have hker : RingHom.ker T.probeMap = A.augmentationIdeal ^ m := by
    exact T.probeMap_ker
  simpa [hker] using hopen_raw

/-- A finite discrete continuous truncation makes its kernel, hence the augmentation power, open.

This is the formal topological half of the augmentation-adic openness theorem.  The only inputs
used are discreteness of the target, continuity of the truncation map, and the recorded kernel
identity `ker(probeMap) = I^n`; no completed-group-algebra construction occurs here. -/
lemma GCAmbien.openaug_powerfin_conttrunc
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (A : GCAmbien (p := p) (Γ := Γ) s hs)
    (T : A.FCAugtru n) :
    A.OpenAugPower n := by
  letI := T.probeTopology
  letI := T.probeDiscrete
  letI := T.instProbeRing
  have hopen_zero : IsOpen ({0} : Set T.quotientProbe) := by
    exact isOpen_discrete ({0} : Set T.quotientProbe)
  have hpreimage :
      IsOpen (T.probeMap ⁻¹' ({0} : Set T.quotientProbe)) := by
    exact hopen_zero.preimage T.probeMap_continuous
  have hset :
      ((A.augmentationIdeal ^ n : Ideal A.completedGroupAlgebra) :
          Set A.completedGroupAlgebra) =
        T.probeMap ⁻¹' ({0} : Set T.quotientProbe) := by
    ext x
    constructor
    · intro hx
      have hxker : x ∈ RingHom.ker T.probeMap := by
        rw [show RingHom.ker T.probeMap = A.augmentationIdeal ^ n from
          T.probeMap_ker]
        exact hx
      have hxzero : T.probeMap x = 0 := by
        simpa [RingHom.mem_ker] using hxker
      exact hxzero
    · intro hx
      have hxzero : T.probeMap x = 0 := by
        simpa using hx
      have hxker : x ∈ RingHom.ker T.probeMap := by
        simpa [RingHom.mem_ker] using hxzero
      rw [show RingHom.ker T.probeMap = A.augmentationIdeal ^ n from
        T.probeMap_ker] at hxker
      exact hxker
  exact
    (A.openaug_poweriff_openaugpower
      (p := p) (Γ := Γ) (s := s) (hs := hs)).1
      (by simpa [hset] using hpreimage)

/-- Finite discrete positive truncations imply open positive augmentation powers.

This is just the previous single-level kernel argument applied uniformly in `m`.  It keeps the
remaining completed-group-algebra input concentrated in the existence of finite continuous
truncations, instead of mixing that construction with the topological open-kernel consequence. -/
lemma GCAmbien.openpos_augfin_conttruncations
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (A : GCAmbien (p := p) (Γ := Γ) s hs)
    (H : A.FinContposAugtruncations) :
    A.OpenPosAugpowers := by
  intro m hm
  rcases H hm with ⟨T⟩
  exact
    A.openaug_powerfin_conttrunc
      (p := p) (Γ := Γ) (s := s) (hs := hs) T

/-- The core Jennings upper-bound package unpacks to the quotient-layer kernel inclusion. -/
lemma GCAmbien.jenningskernel_upperjennings_kernuppeboun
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (A : GCAmbien (p := p) (Γ := Γ) s hs)
    (Q : DCLayer
      (p := p) (Γ := Γ) (s := s) (hs := hs) n A)
    (H : Nonempty (LUBound (A.toCore Q))) :
    A.JenningskernelUpperboundQuotlayer Q := by
  rcases H with ⟨U⟩
  dsimp [
    GCAmbien.JenningskernelUpperboundQuotlayer,
    LUBound
  ] at U ⊢
  exact U.quotient_unit_ker

/-- The pointwise Jennings-Lazard theorem packages as the subgroup-bound interface.

This is a formal conversion: it uses the already-proved equivalence between pointwise congruence
and the subgroup inclusion for the core `A.toCore Q`.  No completed-group-algebra construction and
no Jennings-Lazard mathematics happens here. -/
lemma GCAmbien.posdim_subgroupquot_layerpointwise
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (A : GCAmbien (p := p) (Γ := Γ) s hs)
    (Q : DCLayer
      (p := p) (Γ := Γ) (s := s) (hs := hs) n A)
    (_hn : 1 < n)
    (H : A.PointwiseposDimboundQuotlayer Q) :
    A.PosdimSubgroupboundQuotlayer Q := by
  dsimp [
    GCAmbien.PosdimSubgroupboundQuotlayer,
    GCAmbien.PointwiseposDimboundQuotlayer
  ] at H ⊢
  have hpointwise :
      ∀ g : Γ,
        ((A.toCore Q).canonicalUnit g : (A.toCore Q).completedGroupAlgebra) - 1 ∈
            (A.toCore Q).augmentationIdeal ^ n →
          g ∈ zassenhausFiltration p Γ n := H
  exact
    (dense_lazard_bound
      (p := p) (Γ := Γ) (s := s) (hs := hs) (A.toCore Q)).2
      hpointwise

/-- At positive levels, the pointwise and subgroup-bound Jennings-Lazard interfaces are equivalent.

The forward direction packages the pointwise theorem as a subgroup inclusion; the reverse direction
unpacks a subgroup inclusion at a single group element.  This keeps the hard theorem below in the
clean subgroup-inclusion form while preserving the pointwise API used by the final same-core
construction. -/
lemma GCAmbien.pointwisepos_dimiffpos_dimsubgboun
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (A : GCAmbien (p := p) (Γ := Γ) s hs)
    (Q : DCLayer
      (p := p) (Γ := Γ) (s := s) (hs := hs) n A)
    (hn : 1 < n) :
    A.PointwiseposDimboundQuotlayer Q ↔
      A.PosdimSubgroupboundQuotlayer Q := by
  constructor
  · intro Hpoint
    exact
      A.posdim_subgroupquot_layerpointwise
        (p := p) (Γ := Γ) (s := s) (hs := hs) Q hn Hpoint
  · intro Hsubgroup
    exact
      A.pointwisepos_dimpos_dimsubgboun
        (p := p) (Γ := Γ) (s := s) (hs := hs) Q Hsubgroup

/-- Pointwise positive Jennings-Lazard input feeds the quotient-layer positive-input package.

This is a convenience bridge for downstream construction lemmas.  At a positive level, the
pointwise implication first packages as the subgroup-bound theorem, and the subgroup-bound theorem
then converts to the core-level `PosJenningsInput` interface.  The lemma contains no new
Jennings-Lazard mathematics; it just composes the two already-separated interface conversions. -/
lemma GCAmbien.posjennings_inputpos_dimsubgboun
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (A : GCAmbien (p := p) (Γ := Γ) s hs)
    (Q : DCLayer
      (p := p) (Γ := Γ) (s := s) (hs := hs) n A)
    (hn : 1 < n)
    (Hpoint : A.PointwiseposDimboundQuotlayer Q) :
    A.PosJenningsinputQuotlayer Q := by
  have Hsubgroup :
      A.PosdimSubgroupboundQuotlayer Q :=
    A.posdim_subgroupquot_layerpointwise
      (p := p) (Γ := Γ) (s := s) (hs := hs) Q hn Hpoint
  have Hinput : A.PosJenningsinputQuotlayer Q :=
    A.posjennings_inputpos_dimsubgbouna
      (p := p) (Γ := Γ) (s := s) (hs := hs) Q Hsubgroup
  exact Hinput
end Towers
