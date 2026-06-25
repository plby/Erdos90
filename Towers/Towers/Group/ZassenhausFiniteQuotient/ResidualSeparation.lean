import Mathlib
import Towers.Algebra.CompletedGroupAlgebra.FiniteQuotientModel
import Towers.Algebra.DenseGenerators.JenningsReductions
import Towers.Algebra.DenseGenerators.CoreJennings
import Towers.Group.DenseGenerators.ZassenhausSeparation
import Towers.Group.DenseGenerators.ZassenhausPowerSeparation
import Towers.Topology.ClosedSeparation



open scoped Topology Pointwise

noncomputable section

namespace Towers

universe u
universe v w z


namespace DGSep

variable {p : ℕ}
variable {Γ : Type u} [Group Γ] [TopologicalSpace Γ]
variable {n : ℕ}

/-- Residual finite-quotient separation supplies the closed-overgroup separation criterion.

This is the point-set topology bridge needed by the final theorem.  The genuinely mathematical
input is the existence of a finite quotient test detecting a given `g ∉ D_n(Γ)`; after that, the
closed overgroup is just the preimage of the target `D_n` in the finite discrete quotient. -/
lemma closedOvergroupSeparation
    (R : DGSep p Γ n) :
    ∀ g : Γ, g ∉ zassenhausFiltration p Γ n →
      ∃ H : Subgroup Γ,
        zassenhausFiltration p Γ n ≤ H ∧
          IsClosed ((H : Subgroup Γ) : Set Γ) ∧
          g ∉ H := by
  intro g hg
  rcases R.test_not hg with ⟨T, hT⟩
  have hg_comap :
      g ∉ DGTest.targetZassenhausComap T p n := by
    intro hg_preimage
    apply hT
    letI : Group T.quotientGroup := T.instGroup
    simpa [DGTest.targetZassenhausComap] using
      hg_preimage
  exact
    T.closed_overgroup_target
      (p := p) (n := n) hg_comap

/-- The residual finite-quotient criterion implies closedness of `D_n(Γ)`.

This leaves the later proof passes with a crisp target: construct enough finite quotient tests.
All remaining topology is now already discharged by `closedOvergroupSeparation`. -/
lemma closed_zassenhaus_filtration
    (R : DGSep p Γ n) :
    IsClosed ((zassenhausFiltration p Γ n : Subgroup Γ) : Set Γ) := by
  have hsep :
      ∀ g : Γ, g ∉ zassenhausFiltration p Γ n →
        ∃ H : Subgroup Γ,
          zassenhausFiltration p Γ n ≤ H ∧
            IsClosed ((H : Subgroup Γ) : Set Γ) ∧
            g ∉ H := by
    exact R.closedOvergroupSeparation
  exact overgroup_separation hsep

/-- Dense generators give a finite Hausdorff completed augmentation quotient core.

This is the part of the remaining construction that is already available from the completed
group-algebra infrastructure in `T0.lean`.  It corresponds to the finite-dimensional truncation
`A / I^n` in `T.tex` Step 5, with the more explicit bounded-word quotient construction described
in `T2.tex` Steps 6--8.  The proof below is only packaging: it starts from the existing finite
topological augmentation quotient, adds the induced unit reduction and quotient-unit map, and then
forms the core.
-/
lemma t_completed_core
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} (s : Fin d → Γ)
    (hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤)
    {n : ℕ}
    (hn : 1 < n) :
    ∃ C : DCCore
        (p := p) (Γ := Γ) s hs n,
      Finite C.augmentationQuotient ∧
        (letI := C.quotientTopology
        T2Space C.augmentationQuotient) := by
  have htwo : 2 ≤ n := Nat.succ_le_of_lt hn
  rcases
      dense_gens_topological
        (p := p) (Γ := Γ) s hs htwo with
    ⟨A, _hdense, Qalg, hfiniteQalg, htopQ⟩
  rcases htopQ with ⟨Qtop⟩
  let Q : DCAlg
      (p := p) (Γ := Γ) (s := s) (hs := hs) n A :=
    Qalg.toAugmentationQuotient Qtop
  rcases dense_completed_reduction
      (p := p) (Γ := Γ) (s := s) (hs := hs) Q with
    ⟨R⟩
  rcases dense_generators_completed
      (p := p) (Γ := Γ) (s := s) (hs := hs) R with
    ⟨U⟩
  let L : DCLayer
      (p := p) (Γ := Γ) (s := s) (hs := hs) n A :=
    Q.toQuotientLayer R U
  let C : DCCore
      (p := p) (Γ := Γ) s hs n :=
    A.toCore L
  have hfiniteC : Finite C.augmentationQuotient := by
    simpa [
      C,
      L,
      Q,
      GCAmbien.toCore,
      DCAlg.toQuotientLayer,
      GAAug.toAugmentationQuotient
    ] using hfiniteQalg
  have hT2C :
      letI := C.quotientTopology
      T2Space C.augmentationQuotient := by
    letI : TopologicalSpace C.augmentationQuotient := C.quotientTopology
    exact C.quotientT2
  exact ⟨C, hfiniteC, hT2C⟩

/-- The scalar map `ZMod p → A` is injective for any completed group-algebra core.

The augmentation map is a left inverse to the scalar map, so the core cannot collapse the
coefficient field.  This is a formal consequence of the core fields and is independent of any
Jennings-Lazard theorem. -/
lemma completed_core_injective
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (C : DCCore (p := p) (Γ := Γ) s hs n) :
    Function.Injective (algebraMap (ZMod p) C.completedGroupAlgebra) := by
  intro a b hab
  have haug :=
    congr_arg C.augmentationMap hab
  simpa using haug

/-- Any completed group-algebra core has characteristic `p`.

This is used only for the formal lower Jennings calculation: because the coefficient field
`ZMod p` embeds into the completed algebra, the Frobenius/binomial identity in characteristic `p`
is available in the core. -/
lemma core_char_p
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (C : DCCore (p := p) (Γ := Γ) s hs n) :
    CharP C.completedGroupAlgebra p := by
  exact
    charP_of_injective_ringHom
      (completed_core_injective
        (p := p) (Γ := Γ) (s := s) (hs := hs) C)
      p

/-- A positive subgroup bound gives the positive dimension input interface at the same level.

`JLInput` stores the positive theorem behind a
function taking a proof of `1 < n`.  Once the bound has been constructed for this fixed positive
level, the input interface is just packaging. -/
def lazard_input_bound
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    {C : DCCore (p := p) (Γ := Γ) s hs n}
    (H : JLBound C) :
    JLInput C where
  positive_bound := by
    intro _hn
    exact ⟨H⟩

/-- Finite-shadow intersection for the positive Zassenhaus subgroup.

This is the intrinsic group-theoretic bridge left after the finite ordinary group-algebra
Jennings theorem has been applied in every finite continuous quotient.  It says that, for the
dense-generator profinite group under discussion, membership in `D_n(Γ)` can be tested after all
continuous maps to finite discrete groups.

The statement is deliberately free of completed group-algebra data.  The finite quotient
congruence theorem below supplies the hypotheses in every finite shadow; this structure is only
responsible for reflecting those shadows back to the original group. -/
structure DSInter
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} (s : Fin d → Γ)
    (hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤)
    (n : ℕ) :
    Type (u + 1) where
  forall_finite_quotient :
    ∀ g : Γ,
      (∀ {Λ : Type u} [Group Λ] [TopologicalSpace Λ] [DiscreteTopology Λ] [Finite Λ]
        (φ : Γ →* Λ),
        Continuous (fun x : Γ => φ x) →
          φ g ∈ zassenhausFiltration p Λ n) →
      g ∈ zassenhausFiltration p Γ n

/-- The same finite-shadow intersection principle, but stated in terms of packaged finite
quotient tests.

This is the form closest to the residual-separation structure in `T0.lean`.  A test already
contains the finite discrete target, the continuous quotient map, and the target Zassenhaus
subgroup, so this statement only says that passing every such test forces membership in
`D_n(Γ)`. -/
structure DTInter
    (p : ℕ)
    (Γ : Type u) [Group Γ] [TopologicalSpace Γ]
    (n : ℕ) :
    Type (u + 1) where
  forall_test_images :
    ∀ g : Γ,
      (∀ T : DGTest Γ,
        T.quotientMap g ∈
          DGTest.targetZassenhaus T p n) →
      g ∈ zassenhausFiltration p Γ n

/-- Residual finite-quotient separation supplies the packaged test-intersection principle.

This is just the contrapositive argument already isolated in `T0.lean`: if an element is not in
`D_n(Γ)`, residual separation produces a finite quotient test in which its image is not in the
target Zassenhaus subgroup. -/
def test_intersection_separation
    {p : ℕ}
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ]
    {n : ℕ}
    (R : DGSep p Γ n) :
    DTInter p Γ n := by
  refine
    { forall_test_images := ?_ }
  intro g himages
  exact
    DGSep.forall_test_images
      R himages

/-- Packaged finite quotient tests imply the explicit finite-shadow formulation.

The explicit formulation quantifies over every finite discrete target and every continuous
homomorphism to it.  Such a homomorphism is exactly a packaged finite quotient test via
`DGTest.ofHom`, so this direction is only bookkeeping. -/
def DTInter.fin_shadow_inter
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (H : DTInter p Γ n) :
    DSInter
      (p := p) (Γ := Γ) s hs n := by
  refine
    { forall_finite_quotient := ?_ }
  intro g hfinite
  exact
    H.forall_test_images g
      (by
        intro T
        letI : Group T.quotientGroup := T.instGroup
        letI : TopologicalSpace T.quotientGroup := T.instTopologicalSpace
        letI : DiscreteTopology T.quotientGroup := T.instDiscreteTopology
        letI : Finite T.quotientGroup := T.instFinite
        have hT :
            T.quotientMap g ∈ zassenhausFiltration p T.quotientGroup n := by
          exact hfinite T.quotientMap T.quotientMap_continuous
        simpa [DGTest.targetZassenhaus]
          using hT)

/-- The explicit finite-shadow formulation also gives the packaged test-intersection
formulation.

This is the converse bookkeeping direction.  To test an arbitrary finite homomorphism, package it
as a `DGTest`; the test-intersection hypothesis then gives
the required target Zassenhaus membership. -/
def DSInter.toTestIntersection
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (H : DSInter
      (p := p) (Γ := Γ) s hs n) :
    DTInter p Γ n := by
  refine
    { forall_test_images := ?_ }
  intro g htests
  exact
    H.forall_finite_quotient g
      (by
        intro Λ _instGroupΛ _instTopΛ _instDiscreteΛ _instFiniteΛ φ hφ
        let T : DGTest Γ :=
          DGTest.ofHom φ hφ
        have hT :
            T.quotientMap g ∈
              DGTest.targetZassenhaus T p n :=
          htests T
        simpa [
          T,
          DGTest.targetZassenhaus,
          DGTest.ofHom
        ] using hT)

/-- The packaged-test and explicit-homomorphism finite-shadow principles are equivalent.

Keeping this equivalence explicit makes the remaining mathematical input smaller: it can be
proved in whichever finite-quotient language is most convenient, while the positive
Jennings-Lazard construction consumes the explicit homomorphism form. -/
lemma shadow_intersection_test
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ} :
    Nonempty
        (DSInter
          (p := p) (Γ := Γ) s hs n) ↔
      Nonempty (DTInter p Γ n) := by
  constructor
  · rintro ⟨Hshadow⟩
    exact
      ⟨Hshadow.toTestIntersection (p := p) (Γ := Γ) (s := s) (hs := hs)⟩
  · rintro ⟨Htests⟩
    exact
      ⟨Htests.fin_shadow_inter
        (p := p) (Γ := Γ) (s := s) (hs := hs)⟩

/-- The finite NS/RBT prime-power package supplies residual finite-quotient separation.

The conditional separation theorem produces an open normal quotient detecting each
`g ∉ D_n(Γ)`.  Open-normal quotients of compact groups are finite and, because the subgroup is open,
discrete; hence each separator is exactly one of the packaged finite quotient tests. -/
def dense_separation_nsrbt
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} (s : Fin d → Γ)
    (hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤)
    {n : ℕ}
    (hn : 1 < n)
    (hNS : NPPower.{u} d p n) :
    DGSep p Γ n := by
  refine
    { test_not := ?_ }
  intro g hg
  rcases
      dense_separates_nsrbt
        (p := p) (Γ := Γ) s hs hn hNS hg with
    ⟨N, hN⟩
  letI : DiscreteTopology (Γ ⧸ N.toSubgroup) :=
    open_discrete_topology N
  letI : Finite (Γ ⧸ N.toSubgroup) :=
    open_normal_finite N
  let T : DGTest Γ :=
    DGTest.ofHom
      (QuotientGroup.mk' N.toSubgroup)
      (open_normal_continuous N)
  refine ⟨T, ?_⟩
  simpa [
    T,
    DGTest.ofHom,
    DGTest.targetZassenhaus
  ] using hN

/-- Finite NS/RBT prime-power separation gives the finite-shadow intersection principle.

This is the intrinsic form consumed by the positive Jennings-Lazard reduction: membership in
`D_n(Γ)` can be reflected from all finite continuous shadows whenever the NS/RBT finite-quotient
separation hypothesis is available at the same level. -/
def shadow_intersection_nsrbt
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} (s : Fin d → Γ)
    (hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤)
    {n : ℕ}
    (hn : 1 < n)
    (hNS : NPPower.{u} d p n) :
    DSInter
      (p := p) (Γ := Γ) s hs n := by
  exact
    (test_intersection_separation
      (dense_separation_nsrbt
        (p := p) (Γ := Γ) s hs hn hNS)).fin_shadow_inter
      (p := p) (Γ := Γ) (s := s) (hs := hs)

/-- Finite quotient upper control plus finite-shadow intersection gives the pointwise
positive dimension-subgroup bound for the canonical quotient layer.

This is a formal step: the completed group-algebra congruence is first sent to every finite
ordinary group algebra by `Hupper`, and the finite-shadow intersection principle then reflects the
resulting family of finite Zassenhaus memberships back to `Γ`. -/
def pointwise_shadow_intersection
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {P :
      GCPackag
        (p := p) Γ s hs}
    {n : ℕ}
    {Q : DCAlg
      (p := p) (Γ := Γ) (s := s) (hs := hs) n P.toAmbient}
    {R : DenseCompletedReduction Q}
    {U : DenseGeneratorsCompleted R}
    (Hupper : P.PFUpperb Q R U)
    (Hshadow :
      DSInter
        (p := p) (Γ := Γ) s hs n) :
    P.PDUpperb Q R U := by
  refine
    { pointwise_mem_zassenhaus := ?_ }
  intro g hcongruence
  exact
    Hshadow.forall_finite_quotient g
      (by
        intro Λ _instGroupΛ _instTopΛ _instDiscreteΛ _instFiniteΛ φ hφ
        exact Hupper.finite_quotient_zassenhaus g hcongruence φ hφ)

/-- Convert the canonical pointwise upper bound into the subgroup-inclusion interface used by
the Jennings-Lazard kernel proof.

The only work here is unfolding the augmentation-power subgroup: its membership predicate is
definitionally the congruence `u_g - 1 ∈ I^n`, which is exactly what the pointwise upper bound
expects. -/
def lazard_pointwise_upper
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {P :
      GCPackag
        (p := p) Γ s hs}
    {n : ℕ}
    (Q : DCAlg
      (p := p) (Γ := Γ) (s := s) (hs := hs) n P.toAmbient)
    (R : DenseCompletedReduction Q)
    (U : DenseGeneratorsCompleted R)
    (Hpoint : P.PDUpperb Q R U) :
    JLBound
      (P.toAmbient.toCore (Q.toQuotientLayer R U)) := by
  refine
    { augmentation_subgroup_zassenhaus := ?_ }
  intro g hg
  exact
    Hpoint.pointwise_mem_zassenhaus g
      ((jennings_lazard_augmentation
        (p := p) (Γ := Γ) (s := s) (hs := hs)
        (P.toAmbient.toCore (Q.toQuotientLayer R U)) g).1 hg)

/-- Build a finite Hausdorff canonical quotient layer while retaining the canonical package.

The earlier finite quotient construction in `T0.lean` is stated for an ambient algebra.  Here we
run the same formal steps on `P.toAmbient`, using the dense canonical-unit span carried by the
canonical package.  Keeping `P` in the witness is important because the finite-quotient
Jennings transport is a property of the canonical package, not of an arbitrary ambient algebra
with a dense span. -/
lemma t_dense_generators
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} (s : Fin d → Γ)
    (hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤)
    {n : ℕ}
    (hn : 1 < n) :
    ∃ P :
        GCPackag
          (p := p) Γ s hs,
      ∃ Q : DCAlg
          (p := p) (Γ := Γ) (s := s) (hs := hs) n P.toAmbient,
        ∃ R : DenseCompletedReduction Q,
          ∃ U : DenseGeneratorsCompleted R,
            Finite (P.toAmbient.toCore (Q.toQuotientLayer R U)).augmentationQuotient ∧
              (letI :=
                (P.toAmbient.toCore (Q.toQuotientLayer R U)).quotientTopology
              T2Space (P.toAmbient.toCore (Q.toQuotientLayer R U)).augmentationQuotient) := by
  classical
  rcases
      gens_completed_package
        (p := p) (Γ := Γ) s hs with
    ⟨P⟩
  have hdense : P.toAmbient.DenseAlgebraSpan :=
    P.ambient_denseunit_algspan
  have hclosed : P.toAmbient.ClosedAugPower n := by
    rcases
        P.toAmbient.existsaug_idealettdens_unitalgspan
          hdense with
      ⟨Hletters⟩
    rcases
        P.toAmbient.existsaugpower_wordspanideal_letterdensespan
          (n := n) Hletters with
      ⟨Hpower⟩
    exact
      P.toAmbient.closedaug_powertopologi_leftaugpower
        (P.toAmbient.fintopologi_leftaugpower_worddensespan
          Hpower)
  rcases
      P.toAmbient.existsfin_algaugquot_powertwole
        (p := p) (Γ := Γ) (s := s) (hs := hs) hdense hclosed hn with
    ⟨Qalg, hfiniteQalg⟩
  rcases
      P.toAmbient.finclosed_augpowerfin_algquotclosed
        Qalg hfiniteQalg hclosed with
    ⟨D⟩
  rcases D.exists_fintopo_augquot with
    ⟨Qtop, hfiniteQtop, hTop⟩
  rcases hTop with ⟨Ttop⟩
  let Q : DCAlg
      (p := p) (Γ := Γ) (s := s) (hs := hs) n P.toAmbient :=
    Qtop.toAugmentationQuotient Ttop
  have hfiniteQ : Finite Q.augmentationQuotient := by
    dsimp [Q, GAAug.toAugmentationQuotient]
    exact hfiniteQtop
  have hT2Q :
      (letI := Q.quotientTopology
      T2Space Q.augmentationQuotient) := by
    dsimp [Q, GAAug.toAugmentationQuotient]
    exact Ttop.quotientT2
  rcases dense_completed_reduction
      (p := p) (Γ := Γ) (s := s) (hs := hs) Q with
    ⟨R⟩
  rcases dense_generators_completed
      (p := p) (Γ := Γ) (s := s) (hs := hs) R with
    ⟨U⟩
  let C : DCCore
      (p := p) (Γ := Γ) s hs n :=
    P.toAmbient.toCore (Q.toQuotientLayer R U)
  have hfiniteC : Finite C.augmentationQuotient := by
    dsimp [
      C,
      GCAmbien.toCore,
      DCAlg.toQuotientLayer
    ]
    exact hfiniteQ
  have hT2C :
      (letI := C.quotientTopology
      T2Space C.augmentationQuotient) := by
    dsimp [
      C,
      GCAmbien.toCore,
      DCAlg.toQuotientLayer
    ]
    exact hT2Q
  exact ⟨P, Q, R, U, hfiniteC, hT2C⟩

/-- Positive-level same-core Jennings input from finite-shadow intersection and finite Jennings.

At a fixed positive level, the canonical finite Hausdorff quotient layer supplies the same core.
  The
finite ordinary group-algebra upper bound is transported to every finite continuous quotient, and
the supplied finite-shadow intersection principle reflects those finite memberships back to `Γ`.
The result is precisely the dense-span plus positive Jennings input needed by the bounded-word
endgame. -/
lemma gens_shadow_dim
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} (s : Fin d → Γ)
    (hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤)
    {n : ℕ}
    (hn : 1 < n)
    (Hshadow :
      DSInter
        (p := p) (Γ := Γ) s hs n)
    (Hfinite : DenseUpperBound.{u} (p := p) n) :
    ∃ C : DCCore
        (p := p) (Γ := Γ) s hs n,
      C.DenseSpanposJenningsinput := by
  rcases t_dense_generators
      (p := p) (Γ := Γ) s hs hn with
    ⟨P, Q, R, U, _hfiniteC, _hT2C⟩
  rcases
      P.existspos_dimfincong_transportonelt
        (p := p) (Γ := Γ) (s := s) (hs := hs) Q R U hn with
    ⟨Htransport⟩
  let Hupper : P.PFUpperb Q R U :=
    Htransport.fin_quot_upperbound Hfinite
  let Hpoint : P.PDUpperb Q R U :=
    pointwise_shadow_intersection
      (p := p) (Γ := Γ) (s := s) (hs := hs) Hupper Hshadow
  let Hsub :
      JLBound
        (P.toAmbient.toCore (Q.toQuotientLayer R U)) :=
    lazard_pointwise_upper
      (p := p) (Γ := Γ) (s := s) (hs := hs) Q R U Hpoint
  let C : DCCore
      (p := p) (Γ := Γ) s hs n :=
    P.toAmbient.toCore (Q.toQuotientLayer R U)
  have hdense : C.DenseAlgebraSpan := by
    simpa [C] using
      P.toAmbient.densecanon_unitalg_spancore
        (p := p) (Γ := Γ) (s := s) (hs := hs)
        (Q.toQuotientLayer R U)
        P.ambient_denseunit_algspan
  have hpositive : C.PosJenningsInput := by
    have hsub_nonempty :
        Nonempty (JLBound C) := by
      exact ⟨by simpa [C] using Hsub⟩
    exact
      (DCCore.posjennings_inputiffpos_dimsubgboun
        (p := p) (Γ := Γ) (s := s) (hs := hs) C).2 hsub_nonempty
  exact ⟨C, hdense, hpositive⟩

/-- Conditional positive-level same-core Jennings input from the two finite reductions.

At a fixed positive level, the canonical finite Hausdorff quotient layer supplies the same core.
  The
finite ordinary group-algebra upper bound is transported to every finite continuous quotient, and
the finite-shadow intersection principle coming from `NPPower` reflects those finite
memberships back to `Γ`.  The result is precisely the dense-span plus positive Jennings input needed
by the bounded-word endgame. -/
lemma gens_nsrbt_dim
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} (s : Fin d → Γ)
    (hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤)
    {n : ℕ}
    (hn : 1 < n)
    (hNS : NPPower.{u} d p n)
    (Hfinite : DenseUpperBound.{u} (p := p) n) :
    ∃ C : DCCore
        (p := p) (Γ := Γ) s hs n,
      C.DenseSpanposJenningsinput := by
  let Hshadow :
      DSInter
        (p := p) (Γ := Γ) s hs n :=
    shadow_intersection_nsrbt
      (p := p) (Γ := Γ) s hs hn hNS
  exact
    gens_shadow_dim
      (p := p) (Γ := Γ) s hs hn Hshadow Hfinite

/-- The dense-generator self-quotient has trivial target Zassenhaus subgroup.

This is purely algebraic and does not use the topology of `Γ` or the dense-generator tuple.  It is
the exact quotient statement: after quotienting by `D_n(Γ)`, the image of the same Zassenhaus term
is the trivial subgroup. -/
def denseSelfData
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ]
    (n : ℕ) :
    DenseSelfData p Γ n := by
  refine
    { target_eq_bot := ?_ }
  dsimp [
    denseSelfTarget,
    denseSelfQuotient
  ]
  exact filtration_self_bot p Γ n

/-- A point outside `D_n(Γ)` maps nontrivially to the self-quotient by `D_n(Γ)`. -/
lemma dense_self_not
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ]
    {n : ℕ}
    {g : Γ}
    (hg : g ∉ zassenhausFiltration p Γ n) :
    denseGeneratorsSelf p Γ n g ≠ 1 := by
  intro hg_one
  exact hg
    ((dense_zassenhaus_self
      (p := p) (Γ := Γ) (n := n) g).mp hg_one)

/-- The tuple induced by the dense generators in the intrinsic self-quotient. -/
noncomputable def denseSelfTuple
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ]
    {d : ℕ} (s : Fin d → Γ)
    (n : ℕ) :
    Fin d → denseSelfQuotient p Γ n :=
  fun i => denseGeneratorsSelf p Γ n (s i)

/-- Abstract generation of the self-quotient by the images of the dense tuple.

This is the algebraic finite-width part of the self-quotient theorem.  It deliberately forgets the
topology: the assertion is only that the images of the chosen topological generators generate the
abstract quotient `Γ / D_n(Γ)`.  Once this is known, the restricted-Burnside input already proved
in `T0.lean` makes the quotient finite because its own `D_n` is trivial. -/
structure SelfAbstractGeneration
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ]
    {d : ℕ} (s : Fin d → Γ)
    (n : ℕ) :
    Type u where
  closure_range_top :
    Subgroup.closure
        (Set.range (denseSelfTuple
          (p := p) (Γ := Γ) s n)) =
      ⊤

/-- A signed generator letter maps into the subgroup generated by the self-quotient tuple.

This is the first purely algebraic bookkeeping step behind the finite-width input: allowing
inverse letters does not enlarge the abstract subgroup generated by the quotient images of `s`. -/
lemma self_letter_closure
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ]
    {d : ℕ} (s : Fin d → Γ)
    {n : ℕ}
    (a : denseGeneratorsLetter d) :
    denseGeneratorsSelf p Γ n
        (denseLetterElement s a) ∈
      Subgroup.closure
        (Set.range (denseSelfTuple
          (p := p) (Γ := Γ) s n)) := by
  let K : Subgroup (denseSelfQuotient p Γ n) :=
    Subgroup.closure
      (Set.range (denseSelfTuple
        (p := p) (Γ := Γ) s n))
  change
    denseGeneratorsSelf p Γ n
        (denseLetterElement s a) ∈ K
  by_cases hsign : a.2
  · have hgen :
        denseSelfTuple
            (p := p) (Γ := Γ) s n a.1 ∈ K := by
      exact Subgroup.subset_closure ⟨a.1, rfl⟩
    simpa [
      K,
      denseSelfTuple,
      denseLetterElement,
      hsign
    ] using hgen
  · have hgen :
        denseSelfTuple
            (p := p) (Γ := Γ) s n a.1 ∈ K := by
      exact Subgroup.subset_closure ⟨a.1, rfl⟩
    have hinv :
        (denseSelfTuple
            (p := p) (Γ := Γ) s n a.1)⁻¹ ∈ K :=
      K.inv_mem hgen
    simpa [
      K,
      denseSelfTuple,
      denseLetterElement,
      hsign
    ] using hinv

/-- A signed word in the dense generators maps into the subgroup generated by the
self-quotient tuple.

This removes the routine word induction from the finite-width theorem.  The remaining finite-width
input may therefore speak only about finding a signed-word representative for each quotient point.
-/
lemma dense_self_closure
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ]
    {d : ℕ} (s : Fin d → Γ)
    {n : ℕ}
    (w : List (denseGeneratorsLetter d)) :
    denseGeneratorsSelf p Γ n
        (denseSignedElement s w) ∈
      Subgroup.closure
        (Set.range (denseSelfTuple
          (p := p) (Γ := Γ) s n)) := by
  let K : Subgroup (denseSelfQuotient p Γ n) :=
    Subgroup.closure
      (Set.range (denseSelfTuple
        (p := p) (Γ := Γ) s n))
  change
    denseGeneratorsSelf p Γ n
        (denseSignedElement s w) ∈ K
  induction w with
  | nil =>
      rw [dense_element_nil]
      exact K.one_mem
  | cons a w ih =>
      rw [dense_element_cons]
      have ha :
          denseGeneratorsSelf p Γ n
              (denseLetterElement s a) ∈ K :=
        self_letter_closure
          (p := p) (Γ := Γ) s (n := n) a
      exact K.mul_mem ha ih

/-- Finite-width word representatives for the intrinsic self-quotient.

The mathematical content is deliberately sharper than abstract generation: every element of
`Γ / D_n(Γ)` must be represented by one explicit finite signed word in the original dense tuple.
Once such representatives exist, abstract generation is formal. -/
structure DSWidth
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ]
    {d : ℕ} (s : Fin d → Γ)
    (n : ℕ) :
    Type u where
  wordOf :
    denseSelfQuotient p Γ n →
      List (denseGeneratorsLetter d)
  wordOf_spec :
    ∀ q : denseSelfQuotient p Γ n,
      denseGeneratorsSelf p Γ n
          (denseSignedElement s (wordOf q)) = q


namespace DSWidth

/-- Finite-width representatives imply abstract generation of the self-quotient.

This is a formal algebraic conversion: if every quotient element has a signed-word representative
in the chosen dense tuple, then the images of that tuple generate the entire quotient group. -/
def toAbstractGeneration
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ]
    {d : ℕ} {s : Fin d → Γ}
    {n : ℕ}
    (W : DSWidth
      (p := p) (Γ := Γ) s n) :
    SelfAbstractGeneration
      (p := p) (Γ := Γ) s n := by
  refine ⟨?_⟩
  let K : Subgroup (denseSelfQuotient p Γ n) :=
    Subgroup.closure
      (Set.range (denseSelfTuple
        (p := p) (Γ := Γ) s n))
  change K = ⊤
  refine le_antisymm le_top ?_
  intro q _hq
  have hword :
      denseGeneratorsSelf p Γ n
          (denseSignedElement s (W.wordOf q)) ∈ K := by
    simpa [K] using
      dense_self_closure
        (p := p) (Γ := Γ) s (n := n) (W.wordOf q)
  have hspec :
      denseGeneratorsSelf p Γ n
          (denseSignedElement s (W.wordOf q)) = q :=
    W.wordOf_spec q
  simpa [hspec] using hword

end DSWidth

/-- Ambient coset representatives for the intrinsic self-quotient.

This formulation keeps the normal-form statement on `Γ` itself: every ambient element has a signed
word in the dense tuple with the same image in `Γ / D_n(Γ)`.  It is slightly stronger to use than
the quotient-level `FiniteWidth` structure, but it avoids any quotient-choice bookkeeping in the
mathematical input. -/
structure SCRepres
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ]
    {d : ℕ} (s : Fin d → Γ)
    (n : ℕ) :
    Type u where
  wordOf : Γ → List (denseGeneratorsLetter d)
  wordOf_spec :
    ∀ g : Γ,
      denseGeneratorsSelf p Γ n
          (denseSignedElement s (wordOf g)) =
        denseGeneratorsSelf p Γ n g


namespace SCRepres

/-- Ambient coset representatives induce quotient-level finite-width representatives.

The only extra work is choosing an ambient representative for each quotient point; the
representative theorem itself remains a statement about elements of `Γ`. -/
noncomputable def toFiniteWidth
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ]
    {d : ℕ} {s : Fin d → Γ}
    {n : ℕ}
    (C : SCRepres
      (p := p) (Γ := Γ) s n) :
    DSWidth
      (p := p) (Γ := Γ) s n := by
  classical
  let D : Subgroup Γ := zassenhausFiltration p Γ n
  letI : D.Normal := by
    dsimp [D]
    exact zassenhausFiltration_normal p Γ n
  let rep : denseSelfQuotient p Γ n → Γ :=
    fun q => Classical.choose (QuotientGroup.mk'_surjective D q)
  refine
    { wordOf := fun q => C.wordOf (rep q)
      wordOf_spec := ?_ }
  intro q
  have hrep : QuotientGroup.mk' D (rep q) = q :=
    Classical.choose_spec (QuotientGroup.mk'_surjective D q)
  have hC :
      denseGeneratorsSelf p Γ n
          (denseSignedElement s (C.wordOf (rep q))) =
        denseGeneratorsSelf p Γ n (rep q) :=
    C.wordOf_spec (rep q)
  have hmap_rep :
      denseGeneratorsSelf p Γ n (rep q) = q := by
    simpa [denseGeneratorsSelf, D] using hrep
  exact hC.trans hmap_rep

end SCRepres

/-- A factorization form of the finite-width normal form.

For each `g : Γ`, the chosen signed word represents the same coset modulo `D_n(Γ)`: equivalently,
the error `(word)⁻¹ * g` lies in `D_n(Γ)`.  This is the group-theoretic heart of the
Nikolov-Segal/Jennings finite-width step, separated from the quotient-map algebra. -/
structure SCFact
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ]
    {d : ℕ} (s : Fin d → Γ)
    (n : ℕ) :
    Type u where
  wordOf : Γ → List (denseGeneratorsLetter d)
  quotient_error_mem :
    ∀ g : Γ,
      (denseSignedElement s (wordOf g))⁻¹ * g ∈
        zassenhausFiltration p Γ n


namespace SCFact

/-- A `D_n`-error factorization gives equality of images in the self-quotient.

This is the formal kernel calculation that turns the ambient normal form into actual quotient
representatives. -/
def toCosetRepresentatives
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ]
    {d : ℕ} {s : Fin d → Γ}
    {n : ℕ}
    (F : SCFact
      (p := p) (Γ := Γ) s n) :
    SCRepres
      (p := p) (Γ := Γ) s n := by
  refine
    { wordOf := F.wordOf
      wordOf_spec := ?_ }
  intro g
  let w : Γ := denseSignedElement s (F.wordOf g)
  have hker :
      denseGeneratorsSelf p Γ n (w⁻¹ * g) = 1 :=
    (dense_zassenhaus_self
      (p := p) (Γ := Γ) (n := n) (w⁻¹ * g)).2
      (by simpa [w] using F.quotient_error_mem g)
  have hmul :
      (denseGeneratorsSelf p Γ n w)⁻¹ *
          denseGeneratorsSelf p Γ n g =
        1 := by
    simpa [w] using hker
  have heq :
      denseGeneratorsSelf p Γ n w =
        denseGeneratorsSelf p Γ n g :=
    inv_mul_eq_one.mp hmul
  simpa [w] using heq

end SCFact

/-- Coset cover of `Γ / D_n(Γ)` by the abstract subgroup generated by the dense tuple.

This is an existential, non-algorithmic form of the finite-width congruence theorem: every ambient
element is congruent modulo `D_n` to some element of the abstract subgroup generated by `s`. -/
structure DCCover
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ]
    {d : ℕ} (s : Fin d → Γ)
    (n : ℕ) :
    Type u where
  exists_closure_representative :
    ∀ g : Γ,
      ∃ h : Γ,
        h ∈ Subgroup.closure (Set.range s) ∧
          h⁻¹ * g ∈ zassenhausFiltration p Γ n

/-- Equality in the self-quotient is the same as a `D_n`-error.

This is the kernel calculation used to turn quotient-generation statements into coset-cover
statements.  If two ambient elements have the same image modulo `D_n`, then their quotient lies in
`D_n`. -/
lemma dense_self_error
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ]
    {n : ℕ}
    {h g : Γ}
    (hmap :
      denseGeneratorsSelf p Γ n h =
        denseGeneratorsSelf p Γ n g) :
    h⁻¹ * g ∈ zassenhausFiltration p Γ n := by
  have hker :
      denseGeneratorsSelf p Γ n (h⁻¹ * g) = 1 := by
    calc
      denseGeneratorsSelf p Γ n (h⁻¹ * g) =
          (denseGeneratorsSelf p Γ n h)⁻¹ *
            denseGeneratorsSelf p Γ n g := by
        simp
      _ =
          (denseGeneratorsSelf p Γ n g)⁻¹ *
            denseGeneratorsSelf p Γ n g := by
        rw [hmap]
      _ = 1 := by
        simp
  exact
    (dense_zassenhaus_self
      (p := p) (Γ := Γ) (n := n) (h⁻¹ * g)).1 hker

/-- A `D_n`-error gives equality in the self-quotient.

This is the converse kernel calculation, useful for checking that the coset-cover formulation and
the quotient-image formulation say the same thing. -/
lemma dense_generators_error
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ]
    {n : ℕ}
    {h g : Γ}
    (herror : h⁻¹ * g ∈ zassenhausFiltration p Γ n) :
    denseGeneratorsSelf p Γ n h =
      denseGeneratorsSelf p Γ n g := by
  have hker :
      denseGeneratorsSelf p Γ n (h⁻¹ * g) = 1 :=
    (dense_zassenhaus_self
      (p := p) (Γ := Γ) (n := n) (h⁻¹ * g)).2 herror
  have hmul :
      (denseGeneratorsSelf p Γ n h)⁻¹ *
          denseGeneratorsSelf p Γ n g =
        1 := by
    simpa using hker
  exact inv_mul_eq_one.mp hmul

/-- Quotient generation by the abstract dense subgroup.

Instead of choosing representatives, this says that the image of
`Subgroup.closure (Set.range s)` in the self-quotient `Γ / D_n(Γ)` is all of the quotient.  The
coset-cover theorem is a formal consequence of this statement. -/
structure DGGenera
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ]
    {d : ℕ} (s : Fin d → Γ)
    (n : ℕ) :
    Type u where
  map_closure_top :
    Subgroup.map (denseGeneratorsSelf p Γ n)
        (Subgroup.closure (Set.range s)) =
      ⊤


namespace DGGenera

/-- Quotient generation gives the existential dense-subgroup coset cover.

Given `g`, the class of `g` lies in the image of the abstract subgroup generated by `s`; choosing a
preimage `h` from that subgroup gives `h⁻¹ * g ∈ D_n` by the kernel calculation above. -/
def toCosetCover
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ]
    {d : ℕ} {s : Fin d → Γ}
    {n : ℕ}
    (Q : DGGenera
      (p := p) (Γ := Γ) s n) :
    DCCover
      (p := p) (Γ := Γ) s n := by
  refine
    { exists_closure_representative := ?_ }
  intro g
  let H : Subgroup Γ := Subgroup.closure (Set.range s)
  let q : Γ →* denseSelfQuotient p Γ n :=
    denseGeneratorsSelf p Γ n
  have hg_top : q g ∈ (⊤ : Subgroup (denseSelfQuotient p Γ n)) := by
    exact Subgroup.mem_top _
  have hg_image : q g ∈ Subgroup.map q H := by
    simp [q, H, Q.map_closure_top]
  rcases hg_image with ⟨h, hhH, hhmap⟩
  refine ⟨h, by simpa [H] using hhH, ?_⟩
  exact
    dense_self_error
      (p := p) (Γ := Γ) (n := n)
      (h := h) (g := g)
      (by simpa [q] using hhmap)

end DGGenera

/-- The generator-image subgroup in the Zassenhaus self-quotient is closed.

This is a smaller finite-width input than quotient generation.  It says only that, after passing
to `Γ / D_n(Γ)`, the abstract subgroup generated by the image of the dense tuple is topologically
closed.  Together with the dense-image theorem already proved in `T0.lean`, closedness forces that
subgroup to be the whole self-quotient. -/
structure SCImage
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ]
    {d : ℕ} (s : Fin d → Γ)
    (n : ℕ) :
    Type u where
  closed_generator_image :
    IsClosed
      (((Subgroup.closure
        (Set.range
          (fun i : Fin d =>
            denseGeneratorsSelf p Γ n (s i)))) :
        Subgroup (denseSelfQuotient p Γ n)) :
        Set (denseSelfQuotient p Γ n))


namespace SCImage

/-- The subgroup generated by the images of `s` is contained in the image of the subgroup
generated by `s`.

This is the purely algebraic bridge between the generator-image subgroup used by the density
theorem in `T0.lean` and the quotient-generation statement needed for coset representatives. -/
lemma generator_image_subgroup
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ]
    {d : ℕ} (s : Fin d → Γ)
    (n : ℕ) :
    Subgroup.closure
        (Set.range
          (fun i : Fin d =>
            denseGeneratorsSelf p Γ n (s i))) ≤
      Subgroup.map (denseGeneratorsSelf p Γ n)
        (Subgroup.closure (Set.range s)) := by
  classical
  let q : Γ →* denseSelfQuotient p Γ n :=
    denseGeneratorsSelf p Γ n
  let H : Subgroup Γ := Subgroup.closure (Set.range s)
  change
    Subgroup.closure (Set.range fun i : Fin d => q (s i)) ≤
      Subgroup.map q H
  refine (Subgroup.closure_le _).2 ?_
  rintro y ⟨i, rfl⟩
  refine ⟨s i, ?_, rfl⟩
  change s i ∈ H
  exact Subgroup.subset_closure ⟨i, rfl⟩

/-- A closed dense generator-image subgroup is the whole Zassenhaus self-quotient. -/
lemma image_closed_dense
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {n : ℕ}
    (C : SCImage
      (p := p) (Γ := Γ) s n)
    (hdense :
      closure
        (((Subgroup.closure
          (Set.range
            (fun i : Fin d =>
              denseGeneratorsSelf p Γ n (s i)))) :
          Subgroup (denseSelfQuotient p Γ n)) :
          Set (denseSelfQuotient p Γ n)) =
        Set.univ) :
    Subgroup.closure
        (Set.range
          (fun i : Fin d =>
            denseGeneratorsSelf p Γ n (s i))) =
      (⊤ : Subgroup (denseSelfQuotient p Γ n)) := by
  classical
  let K : Subgroup (denseSelfQuotient p Γ n) :=
    Subgroup.closure
      (Set.range
        (fun i : Fin d =>
          denseGeneratorsSelf p Γ n (s i)))
  have hK_closed : IsClosed (K : Set (denseSelfQuotient p Γ n)) := by
    simpa [K] using C.closed_generator_image
  have hK_dense : closure ((K : Subgroup (denseSelfQuotient p Γ n)) :
      Set (denseSelfQuotient p Γ n)) = Set.univ := by
    simpa [K] using hdense
  have hK_univ : (K : Set (denseSelfQuotient p Γ n)) = Set.univ := by
    rw [← hK_closed.closure_eq]
    exact hK_dense
  change K = (⊤ : Subgroup (denseSelfQuotient p Γ n))
  refine le_antisymm le_top ?_
  intro x _hx
  have hxK : x ∈ (K : Set (denseSelfQuotient p Γ n)) := by
    rw [hK_univ]
    exact Set.mem_univ x
  exact hxK

/-- Closedness of the generator-image subgroup upgrades the dense-image theorem from `T0.lean`
to quotient generation by the abstract dense subgroup. -/
def toQuotientGeneration
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    {d : ℕ} {s : Fin d → Γ}
    {n : ℕ}
    (C : SCImage
      (p := p) (Γ := Γ) s n)
    (hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤) :
    DGGenera
      (p := p) (Γ := Γ) s n := by
  classical
  let q : Γ →* denseSelfQuotient p Γ n :=
    denseGeneratorsSelf p Γ n
  let H : Subgroup Γ := Subgroup.closure (Set.range s)
  let K : Subgroup (denseSelfQuotient p Γ n) :=
    Subgroup.closure (Set.range fun i : Fin d => q (s i))
  have hK_dense :
      closure ((K : Subgroup (denseSelfQuotient p Γ n)) :
        Set (denseSelfQuotient p Γ n)) =
        Set.univ := by
    simpa [K, q] using
      dense_self_quotient
        (p := p) (Γ := Γ) s hs (n := n)
  have hK_top : K = (⊤ : Subgroup (denseSelfQuotient p Γ n)) := by
    simpa [K, q] using
      image_closed_dense
        (p := p) (Γ := Γ) (s := s) (n := n) C
        (by simpa [K, q] using hK_dense)
  have hK_le_image : K ≤ Subgroup.map q H := by
    simpa [K, q, H] using
      generator_image_subgroup (p := p) (Γ := Γ) s n
  have htop_le_image :
      (⊤ : Subgroup (denseSelfQuotient p Γ n)) ≤
        Subgroup.map q H := by
    simpa [hK_top] using hK_le_image
  refine ⟨?_⟩
  exact le_antisymm le_top htop_le_image

end SCImage

/-- An open normal finite-index core inside the generator-image subgroup of the self-quotient.

This is a smaller and more intrinsic form of the Step 5 finite-width/topological input.  If the
subgroup generated by the images of the dense tuple contains an open normal finite-index subgroup
of the self-quotient, then quotienting by that core gives a finite discrete model whose pullback
recovers the generator-image subgroup. -/
structure DSCore
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ]
    {d : ℕ} (s : Fin d → Γ)
    (n : ℕ) :
    Type u where
  normalCore : Subgroup (denseSelfQuotient p Γ n)
  normalCore_normal : normalCore.Normal
  normal_core_image :
    normalCore ≤
      Subgroup.closure
        (Set.range
          (fun i : Fin d =>
            denseGeneratorsSelf p Γ n (s i)))
  normal_core_index : normalCore.FiniteIndex
  normal_core_open :
    IsOpen
      ((normalCore : Subgroup (denseSelfQuotient p Γ n)) :
        Set (denseSelfQuotient p Γ n))
  normal_core_continuous :
    letI : normalCore.Normal := normalCore_normal
    letI : TopologicalSpace
      (denseSelfQuotient p Γ n ⧸ normalCore) := ⊥
    Continuous
      (fun x : denseSelfQuotient p Γ n =>
        (QuotientGroup.mk' normalCore) x)


namespace DSCore

/-- Quotienting by a normal subgroup contained in `K` recovers `K` as the comap of its image. -/
lemma generator_image_comap
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {n : ℕ}
    (C : DSCore
      (p := p) (Γ := Γ) s n) :
    letI : C.normalCore.Normal := C.normalCore_normal
    Subgroup.closure
        (Set.range
          (fun i : Fin d =>
            denseGeneratorsSelf p Γ n (s i))) =
      Subgroup.comap (QuotientGroup.mk' C.normalCore)
        (Subgroup.map (QuotientGroup.mk' C.normalCore)
          (Subgroup.closure
            (Set.range
              (fun i : Fin d =>
                denseGeneratorsSelf p Γ n (s i))))) := by
  classical
  let Ω : Type u := denseSelfQuotient p Γ n
  letI : Group Ω := by
    dsimp [Ω]
    infer_instance
  let K : Subgroup Ω :=
    Subgroup.closure
      (Set.range
        (fun i : Fin d =>
          denseGeneratorsSelf p Γ n (s i)))
  let N : Subgroup Ω := C.normalCore
  letI : N.Normal := C.normalCore_normal
  let q : Ω →* Ω ⧸ N := QuotientGroup.mk' N
  change K = Subgroup.comap q (Subgroup.map q K)
  ext x
  constructor
  · intro hxK
    exact ⟨x, hxK, rfl⟩
  · intro hx_comap
    rcases hx_comap with ⟨y, hyK, hyq⟩
    have hyx_mem_N : y⁻¹ * x ∈ N := by
      have hyx_eq_one : q (y⁻¹ * x) = 1 := by
        calc
          q (y⁻¹ * x) = (q y)⁻¹ * q x := by
            simp [q]
          _ = (q x)⁻¹ * q x := by
            rw [hyq]
          _ = 1 := by
            simp
      exact (QuotientGroup.eq_one_iff (N := N) (y⁻¹ * x)).mp hyx_eq_one
    have hyx_mem_K : y⁻¹ * x ∈ K := by
      exact C.normal_core_image hyx_mem_N
    have hx_eq : x = y * (y⁻¹ * x) := by
      simp
    rw [hx_eq]
    exact K.mul_mem hyK hyx_mem_K

/-- The quotient map by the open normal core is continuous for the discrete quotient topology. -/
lemma quotient_continuous_discrete
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {n : ℕ}
    (C : DSCore
      (p := p) (Γ := Γ) s n) :
    let Ω : Type u := denseSelfQuotient p Γ n
    let N : Subgroup Ω := C.normalCore
    letI : N.Normal := C.normalCore_normal
    letI : TopologicalSpace (Ω ⧸ N) := ⊥
    Continuous (fun x : Ω => (QuotientGroup.mk' N) x) := by
  simpa using C.normal_core_continuous

end DSCore

/-- A continuous homomorphism to a discrete group has open kernel.

This is the formal topological bridge used by the Step 5 finite shadow: once a finite abstract
target has the discrete topology and the shadow map is continuous, its kernel is an open subgroup
of the self-quotient. -/
lemma monoid_open_discrete
    {Γ Λ : Type u} [Group Γ] [TopologicalSpace Γ]
    [Group Λ] [TopologicalSpace Λ] [DiscreteTopology Λ]
    (φ : Γ →* Λ)
    (hφ : Continuous (fun x : Γ => φ x)) :
    IsOpen ((φ.ker : Subgroup Γ) : Set Γ) := by
  have hone : IsOpen ({1} : Set Λ) := isOpen_discrete _
  have hpre :
      IsOpen ((fun x : Γ => φ x) ⁻¹' ({1} : Set Λ)) :=
    hone.preimage hφ
  have hpre_eq :
      ((fun x : Γ => φ x) ⁻¹' ({1} : Set Λ)) =
        ((φ.ker : Subgroup Γ) : Set Γ) := by
    ext x
    change φ x = 1 ↔ x ∈ φ.ker
    rfl
  simpa [hpre_eq] using hpre

/-- A group homomorphism to a discrete group is continuous if its kernel is open.

The proof is the standard coset argument.  Each fiber is either empty or a translate of the kernel;
the codomain is discrete, so continuity is reduced to openness of all singleton fibers. -/
lemma monoid_continuous_discrete
    {Γ Λ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [Group Λ] [TopologicalSpace Λ] [DiscreteTopology Λ]
    (φ : Γ →* Λ)
    (hker : IsOpen ((φ.ker : Subgroup Γ) : Set Γ)) :
    Continuous (fun x : Γ => φ x) := by
  classical
  have hsingle :
      ∀ y : Λ, IsOpen ((fun x : Γ => φ x) ⁻¹' ({y} : Set Λ)) := by
    intro y
    by_cases hy : ∃ a : Γ, φ a = y
    · rcases hy with ⟨a, ha⟩
      have hfiber_eq :
          ((fun x : Γ => φ x) ⁻¹' ({y} : Set Λ)) =
            (fun x : Γ => a⁻¹ * x) ⁻¹'
              (((φ.ker : Subgroup Γ) : Set Γ)) := by
        ext x
        constructor
        · intro hx
          change φ x = y at hx
          change φ (a⁻¹ * x) = 1
          calc
            φ (a⁻¹ * x) = (φ a)⁻¹ * φ x := by simp
            _ = y⁻¹ * y := by rw [ha, hx]
            _ = 1 := by simp
        · intro hx
          change φ (a⁻¹ * x) = 1 at hx
          have hmul : y⁻¹ * φ x = 1 := by
            calc
              y⁻¹ * φ x = (φ a)⁻¹ * φ x := by rw [ha]
              _ = φ (a⁻¹ * x) := by simp
              _ = 1 := hx
          exact (inv_mul_eq_one.mp hmul).symm
      have hshift : Continuous (fun x : Γ => a⁻¹ * x) := by
        continuity
      simpa [hfiber_eq] using hker.preimage hshift
    · have hfiber_empty :
          ((fun x : Γ => φ x) ⁻¹' ({y} : Set Λ)) = ∅ := by
        ext x
        constructor
        · intro hx
          change φ x = y at hx
          exact False.elim (hy ⟨x, hx⟩)
        · intro hx
          exact False.elim hx
      simp [hfiber_empty]
  rw [continuous_def]
  intro U _hU
  have hpre_eq :
      ((fun x : Γ => φ x) ⁻¹' U) =
        ⋃ y : U, ((fun x : Γ => φ x) ⁻¹' ({(y : Λ)} : Set Λ)) := by
    ext x
    constructor
    · intro hx
      exact Set.mem_iUnion.2 ⟨⟨φ x, hx⟩, by simp⟩
    · intro hx
      rcases Set.mem_iUnion.1 hx with ⟨y, hy⟩
      have hxy : φ x = (y : Λ) := by
        simpa using hy
      change φ x ∈ U
      rw [hxy]
      exact y.property
  rw [hpre_eq]
  exact isOpen_iUnion (fun y : U => hsingle (y : Λ))

/-- An algebraic finite kernel shadow for the generator-image subgroup.

This is the algebraic part of the finite-kernel model: a finite group quotient of the
self-quotient whose kernel is already contained in the subgroup generated by the images of the
dense tuple.  It deliberately carries no topology or continuity data. -/
structure GAModel
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ]
    {d : ℕ} (s : Fin d → Γ)
    (n : ℕ) :
    Type (u + 1) where
  quotientGroup : Type u
  [instGroup : Group quotientGroup]
  [instFinite : Finite quotientGroup]
  quotientMap :
    denseSelfQuotient p Γ n →* quotientGroup
  kernel_generator_image :
    quotientMap.ker ≤
      Subgroup.closure
        (Set.range
          (fun i : Fin d =>
            denseGeneratorsSelf p Γ n (s i)))

/-- The algebraic finite quotient produced by truncating the Fox map, before topology and before
kernel control.

In `T2.tex`, Step 8 first constructs the finite-dimensional target of the truncated map `μₙ`.
This structure records only that algebraic quotient of the self-quotient.  It deliberately omits
both continuity and the assertion that the kernel is generated by the dense tuple; those are
separate mathematical steps. -/
structure GSAlg
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ]
    {d : ℕ} (s : Fin d → Γ)
    (n : ℕ) :
    Type (u + 1) where
  quotientGroup : Type u
  [instGroup : Group quotientGroup]
  [instFinite : Finite quotientGroup]
  quotientMap :
    denseSelfQuotient p Γ n →* quotientGroup

/-- Topological data for the algebraic finite shadow quotient.

This is the part of the finite-shadow construction that remembers the quotient as the image of a
continuous finite-dimensional completed-algebra map.  It equips the algebraic target with the
discrete topology, proves continuity of the target-valued map, and records continuity of the
canonical quotient by its kernel. -/
structure ShadowTopologyData
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {n : ℕ}
    (A : GSAlg
      (p := p) (Γ := Γ) s n) :
    Type (u + 1) where
  quotientTopologicalSpace : TopologicalSpace A.quotientGroup
  quotientDiscreteTopology : @DiscreteTopology A.quotientGroup quotientTopologicalSpace
  quotientMap_continuous :
    letI : Group A.quotientGroup := A.instGroup
    letI : TopologicalSpace A.quotientGroup := quotientTopologicalSpace
    Continuous
      (fun x : denseSelfQuotient p Γ n =>
        A.quotientMap x)
  kernel_map_continuous :
    letI : Group A.quotientGroup := A.instGroup
    letI : A.quotientMap.ker.Normal := inferInstance
    letI : TopologicalSpace
      (denseSelfQuotient p Γ n ⧸ A.quotientMap.ker) := ⊥
    Continuous
      (fun x : denseSelfQuotient p Γ n =>
        (QuotientGroup.mk' A.quotientMap.ker) x)

/-- The actual finite shadow quotient produced by the truncated Fox construction, together with
the topology that comes from that construction.

This avoids a false universal statement: not every abstract finite quotient of the self-quotient
is automa continuous.  The topology data belongs to the particular finite-dimensional
quotient constructed from `μₙ`. -/
structure GCShadow
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ]
    {d : ℕ} (s : Fin d → Γ)
    (n : ℕ) :
    Type (u + 1) where
  algebraic :
    GSAlg
      (p := p) (Γ := Γ) s n
  topologyData :
    ShadowTopologyData
      (p := p) (Γ := Γ) algebraic

/-- The finite continuous quotient produced by the truncated Fox construction, before the kernel
calculation is applied.

This is the formal counterpart of the first half of `T2.tex`, Step 8: form the finite-dimensional
quotient map obtained by truncating the Fox map modulo powers of the augmentation ideal.  It keeps
the finite discrete target, the induced map out of `Γ / D_n(Γ)`, and the continuity data needed
later.  It deliberately does not yet say that the kernel is generated by the images of the dense
tuple; that is the separate `Δₙ`-surjectivity calculation below. -/
structure SCShadow
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ]
    {d : ℕ} (s : Fin d → Γ)
    (n : ℕ) :
    Type (u + 1) where
  quotientGroup : Type u
  [instGroup : Group quotientGroup]
  [instTopologicalSpace : TopologicalSpace quotientGroup]
  [instDiscreteTopology : DiscreteTopology quotientGroup]
  [instFinite : Finite quotientGroup]
  quotientMap :
    denseSelfQuotient p Γ n →* quotientGroup
  quotientMap_continuous :
    Continuous
      (fun x : denseSelfQuotient p Γ n =>
        quotientMap x)
  kernel_map_continuous :
    letI : quotientMap.ker.Normal := inferInstance
    letI : TopologicalSpace
      (denseSelfQuotient p Γ n ⧸ quotientMap.ker) := ⊥
    Continuous
      (fun x : denseSelfQuotient p Γ n =>
        (QuotientGroup.mk' quotientMap.ker) x)


namespace GSAlg

/-- An algebraic finite quotient plus its topology gives the finite continuous shadow used before
kernel control. -/
def continuousFinShadow
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {n : ℕ}
    (A : GSAlg
      (p := p) (Γ := Γ) s n)
    (T : ShadowTopologyData
      (p := p) (Γ := Γ) A) :
    SCShadow
      (p := p) (Γ := Γ) s n := by
  classical
  letI : Group A.quotientGroup := A.instGroup
  letI : TopologicalSpace A.quotientGroup := T.quotientTopologicalSpace
  letI : DiscreteTopology A.quotientGroup := T.quotientDiscreteTopology
  letI : Finite A.quotientGroup := A.instFinite
  refine
    { quotientGroup := A.quotientGroup
      instGroup := inferInstance
      instTopologicalSpace := inferInstance
      instDiscreteTopology := inferInstance
      instFinite := inferInstance
      quotientMap := A.quotientMap
      quotientMap_continuous := ?_
      kernel_map_continuous := ?_ }
  · simpa using T.quotientMap_continuous
  · simpa using T.kernel_map_continuous

end GSAlg

namespace GCShadow

/-- Forget the topology and retain only the algebraic finite quotient. -/
def toAlgebraicQuotient
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {n : ℕ}
    (C : GCShadow
      (p := p) (Γ := Γ) s n) :
    GSAlg
      (p := p) (Γ := Γ) s n :=
  C.algebraic

/-- The constructed finite shadow supplies the continuous finite shadow before kernel control. -/
def continuousFinShadow
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {n : ℕ}
    (C : GCShadow
      (p := p) (Γ := Γ) s n) :
    SCShadow
      (p := p) (Γ := Γ) s n := by
  classical
  exact
    C.algebraic.continuousFinShadow
      (p := p) (Γ := Γ) C.topologyData

end GCShadow

/-- The truncated Fox kernel calculation for a chosen finite continuous shadow.

This packages the second half of `T2.tex`, Step 8.  The informal proof constructs the relator map
`Δₙ`, proves that its image lies in `ker μₙ`, and then proves that it surjects onto `ker μₙ`.
Translated back to the self-quotient, this is exactly the kernel containment needed here: the
kernel of the finite shadow is contained in the subgroup generated by the images of the dense
tuple. -/
structure SFContro
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {n : ℕ}
    (S : SCShadow
      (p := p) (Γ := Γ) s n) :
    Type u where
  relator_truncated_kernel : Prop
  surjective_truncated_kernel : Prop
  kernel_generator_image :
    letI : Group S.quotientGroup := S.instGroup
    S.quotientMap.ker ≤
      Subgroup.closure
        (Set.range
          (fun i : Fin d =>
            denseGeneratorsSelf p Γ n (s i)))

/-- Once `D_n(Γ)` is known to be open, the identity map on the finite discrete self-quotient is a
controlled finite shadow.

This isolates the exact topological input needed by the shadow construction.  The kernel
containment is not assumed: the chosen shadow has trivial kernel. -/
lemma dense_gens_topology
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ]
    {d : ℕ} (s : Fin d → Γ)
    {n : ℕ}
    (Htop : STData p Γ n) :
    ∃ C : GCShadow
        (p := p) (Γ := Γ) s n,
      (let S := C.continuousFinShadow
      letI : Group S.quotientGroup := S.instGroup
      S.quotientMap.ker ≤
        Subgroup.closure
          (Set.range
            (fun i : Fin d =>
              denseGeneratorsSelf p Γ n (s i)))) := by
  classical
  let Ω : Type u := denseSelfQuotient p Γ n
  letI : Finite Ω := Htop.finite_quotient
  letI : DiscreteTopology Ω := Htop.discreteTopology
  let A :
      GSAlg
        (p := p) (Γ := Γ) s n :=
    { quotientGroup := Ω
      instGroup := inferInstance
      instFinite := inferInstance
      quotientMap := MonoidHom.id Ω }
  let T :
      ShadowTopologyData
        (p := p) (Γ := Γ) A :=
    { quotientTopologicalSpace := inferInstance
      quotientDiscreteTopology := inferInstance
      quotientMap_continuous := by
        simpa [A] using (continuous_id : Continuous (fun x : Ω => x))
      kernel_map_continuous := by
        letI : A.quotientMap.ker.Normal := inferInstance
        letI : TopologicalSpace
            (denseSelfQuotient p Γ n ⧸ A.quotientMap.ker) := ⊥
        exact continuous_of_discreteTopology }
  let C :
      GCShadow
        (p := p) (Γ := Γ) s n :=
    { algebraic := A
      topologyData := T }
  refine ⟨C, ?_⟩
  dsimp [
    C,
    T,
    A,
    GCShadow.continuousFinShadow,
    GSAlg.continuousFinShadow
  ]
  intro x hx
  change x = 1 at hx
  simp [hx]

/-- Closedness of `D_n(Γ)` supplies the controlled self-quotient shadow.

Once `D_n(Γ)` is closed, the restricted-Burnside argument makes the self-quotient finite.  Closed
finite-index openness then supplies exactly the topology data consumed by the identity-shadow
construction. -/
lemma gens_zassenhaus_closed
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} (s : Fin d → Γ)
    (hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤)
    {n : ℕ}
    (hn : 1 < n)
    (hclosed :
      IsClosed ((zassenhausFiltration p Γ n : Subgroup Γ) : Set Γ)) :
    ∃ C : GCShadow
        (p := p) (Γ := Γ) s n,
      (let S := C.continuousFinShadow
      letI : Group S.quotientGroup := S.instGroup
      S.quotientMap.ker ≤
        Subgroup.closure
          (Set.range
            (fun i : Fin d =>
              denseGeneratorsSelf p Γ n (s i)))) := by
  have hfinite :
      Finite (denseSelfQuotient p Γ n) :=
    dense_self_one
      (p := p) (Γ := Γ) s hs hclosed hn
  let Hclosed :
      DCInput p Γ n :=
    { isClosed_zassenhaus := hclosed
      finite_selfQuotient := hfinite }
  exact
    dense_gens_topology
      (p := p) (Γ := Γ) s Hclosed.toTopologyData

/-- The controlled shadow exists when the ambient group is finite.

In this case `D_n(Γ)` is a finite subset of the Hausdorff ambient group, hence closed. -/
lemma gens_control_fin
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ] [Finite Γ]
    {d : ℕ} (s : Fin d → Γ)
    (hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤)
    {n : ℕ}
    (hn : 1 < n) :
    ∃ C : GCShadow
        (p := p) (Γ := Γ) s n,
      (let S := C.continuousFinShadow
      letI : Group S.quotientGroup := S.instGroup
      S.quotientMap.ker ≤
        Subgroup.closure
          (Set.range
            (fun i : Fin d =>
              denseGeneratorsSelf p Γ n (s i)))) := by
  have hclosed :
      IsClosed ((zassenhausFiltration p Γ n : Subgroup Γ) : Set Γ) :=
    Set.toFinite ((zassenhausFiltration p Γ n : Subgroup Γ) : Set Γ) |>.isClosed
  exact
    gens_zassenhaus_closed
      (p := p) (Γ := Γ) s hs hn hclosed

/-- Openness of the relevant prime-power subgroup supplies the controlled self-quotient shadow.

The open power subgroup lies in `D_n(Γ)`, so `D_n(Γ)` is closed.  Its self-quotient is then finite
by the restricted-Burnside argument for the finite dense generator-image subgroup, and the
identity-shadow construction applies. -/
lemma dense_gens_open
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} (s : Fin d → Γ)
    (hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤)
    {n : ℕ}
    (hn : 1 < n)
    (hopen :
      IsOpen ((powerSubgroup Γ (p ^ n) : Subgroup Γ) : Set Γ)) :
    ∃ C : GCShadow
        (p := p) (Γ := Γ) s n,
      (let S := C.continuousFinShadow
      letI : Group S.quotientGroup := S.instGroup
      S.quotientMap.ker ≤
        Subgroup.closure
          (Set.range
            (fun i : Fin d =>
              denseGeneratorsSelf p Γ n (s i)))) := by
  have hle : n ≤ p ^ n :=
    nat_pow_self (Fact.out : Nat.Prime p).two_le
  have hclosed :
      IsClosed ((zassenhausFiltration p Γ n : Subgroup Γ) : Set Γ) :=
    filtration_closed_open
      (p := p) (G := Γ) hle hopen
  exact
    gens_zassenhaus_closed
      (p := p) (Γ := Γ) s hs hn hclosed

/-- In a densely finitely generated compact totally disconnected commutative group, every positive
power subgroup is open.

Commutativity gives power width one.  The quotient by the power subgroup therefore has a finite
dense finitely generated torsion subgroup; closedness of the width-one image upgrades that finite
dense subgroup to finiteness of the whole quotient. -/
lemma open_generators_comm
    {Γ : Type u} [CommGroup Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} (s : Fin d → Γ)
    (hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤)
    {m : ℕ}
    (hm : 0 < m) :
    IsOpen ((powerSubgroup Γ m : Subgroup Γ) : Set Γ) := by
  let P : Subgroup Γ := powerSubgroup Γ m
  letI : P.Normal := by
    dsimp [P]
    infer_instance
  have hwidth : HPWidth Γ m 1 :=
    power_width_comm Γ m
  have hclosed :
      IsClosed ((powerSubgroup Γ m : Subgroup Γ) : Set Γ) :=
    closed_totally_disconnected hwidth
  let K : Subgroup (Γ ⧸ P) :=
    Subgroup.closure
      (Set.range
        (fun i : Fin d =>
          QuotientGroup.mk' P (s i)))
  haveI : Finite K := by
    have hfg : Group.FG K := by
      simpa [K, P] using
        power_dense_fg
          (Γ := Γ) s m
    have htor : Monoid.IsTorsion K := by
      simpa [K, P] using
        power_dense_torsion
          (Γ := Γ) s hm
    exact CommGroup.finite_of_fg_torsion K htor
  have hfinite :
      Finite (Γ ⧸ powerSubgroup Γ m) := by
    simpa [P] using
      power_subgroup_dense
        (Γ := Γ) s hs m hclosed (by simpa [K, P] using (inferInstance : Finite K))
  letI : Finite (Γ ⧸ powerSubgroup Γ m) := hfinite
  exact
    width_totally_disconnected
      hwidth

/-- Commutative profinite dense-generator groups have finite-quotient separation for every
Zassenhaus level.

The point is that all prime-power subgroups are open in the commutative case, so the standard
power-subgroup separator applies and each open-normal quotient is a finite continuous quotient. -/
def dense_separation_comm
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [CommGroup Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} (s : Fin d → Γ)
    (hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤)
    (n : ℕ) :
    DGSep p Γ n := by
  refine
    { test_not := ?_ }
  intro g hg
  rcases
      filtration_separates_open
        (p := p) (Γ := Γ) (n := n)
        (fun j =>
          open_generators_comm
            (Γ := Γ) s hs (pow_pos (Fact.out : Nat.Prime p).pos j))
        hg with
    ⟨N, hN⟩
  letI : DiscreteTopology (Γ ⧸ N.toSubgroup) :=
    open_discrete_topology N
  letI : Finite (Γ ⧸ N.toSubgroup) :=
    open_normal_finite N
  let T : DGTest Γ :=
    DGTest.ofHom
      (QuotientGroup.mk' N.toSubgroup)
      (open_normal_continuous N)
  refine ⟨T, ?_⟩
  simpa [
    T,
    DGTest.ofHom,
    DGTest.targetZassenhaus
  ] using hN

/-- Commutativity supplies the finite-shadow intersection principle without NS/RBT. -/
def shadow_intersection_comm
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [CommGroup Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} (s : Fin d → Γ)
    (hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤)
    (n : ℕ) :
    DSInter
      (p := p) (Γ := Γ) s hs n := by
  exact
    (test_intersection_separation
      (dense_separation_comm
        (p := p) (Γ := Γ) s hs n)).fin_shadow_inter
      (p := p) (Γ := Γ) (s := s) (hs := hs)

/-- The controlled self-quotient shadow exists unconditionally for a commutative profinite group
with a dense finite generating tuple. -/
lemma gens_control_comm
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [CommGroup Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} (s : Fin d → Γ)
    (hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤)
    {n : ℕ}
    (hn : 1 < n) :
    ∃ C : GCShadow
        (p := p) (Γ := Γ) s n,
      (let S := C.continuousFinShadow
      letI : Group S.quotientGroup := S.instGroup
      S.quotientMap.ker ≤
        Subgroup.closure
          (Set.range
            (fun i : Fin d =>
              denseGeneratorsSelf p Γ n (s i)))) := by
  exact
    dense_gens_open
      (p := p) (Γ := Γ) s hs hn
      (open_generators_comm
        (Γ := Γ) s hs (pow_pos (Fact.out : Nat.Prime p).pos n))

/-- Residual finite-quotient separation for `D_n(Γ)` supplies the controlled self-quotient shadow.

Separation makes `D_n(Γ)` closed.  The restricted-Burnside argument then makes the self-quotient
finite, so closed finite-index openness supplies the topology data consumed by the identity-shadow
construction. -/
lemma gens_control_separation
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} (s : Fin d → Γ)
    (hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤)
    {n : ℕ}
    (hn : 1 < n)
    (R : DGSep p Γ n) :
    ∃ C : GCShadow
        (p := p) (Γ := Γ) s n,
      (let S := C.continuousFinShadow
      letI : Group S.quotientGroup := S.instGroup
      S.quotientMap.ker ≤
        Subgroup.closure
          (Set.range
            (fun i : Fin d =>
              denseGeneratorsSelf p Γ n (s i)))) := by
  have hclosed :
      IsClosed ((zassenhausFiltration p Γ n : Subgroup Γ) : Set Γ) :=
    closed_zassenhaus_filtration R
  exact
    gens_zassenhaus_closed
      (p := p) (Γ := Γ) s hs hn hclosed

/-- The finite NS/RBT package supplies the controlled self-quotient shadow.

Finite NS/RBT first gives residual finite-quotient separation for `D_n(Γ)`, hence closedness of
`D_n(Γ)`.  The restricted-Burnside argument then makes the self-quotient finite, so closed
finite-index openness supplies the topology data consumed by the identity-shadow construction. -/
lemma dense_gens_nsrbt
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} (s : Fin d → Γ)
    (hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤)
    {n : ℕ}
    (hn : 1 < n)
    (hNS : NPPower.{u} d p n) :
    ∃ C : GCShadow
        (p := p) (Γ := Γ) s n,
      (let S := C.continuousFinShadow
      letI : Group S.quotientGroup := S.instGroup
      S.quotientMap.ker ≤
        Subgroup.closure
          (Set.range
            (fun i : Fin d =>
              denseGeneratorsSelf p Γ n (s i)))) := by
  exact
    gens_control_separation
      (p := p) (Γ := Γ) s hs hn
      (dense_separation_nsrbt
        (p := p) (Γ := Γ) s hs hn hNS)

/-- The controlled self-quotient shadow exists for a dense tuple of size at most one.

This is the first unconditional case of the Step 8 target: finite NS/RBT is already proved in
rank zero and rank one. -/
lemma dense_gens_one
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} (s : Fin d → Γ)
    (hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤)
    (hd : d ≤ 1)
    {n : ℕ}
    (hn : 1 < n) :
    ∃ C : GCShadow
        (p := p) (Γ := Γ) s n,
      (let S := C.continuousFinShadow
      letI : Group S.quotientGroup := S.instGroup
      S.quotientMap.ker ≤
        Subgroup.closure
          (Set.range
            (fun i : Fin d =>
              denseGeneratorsSelf p Γ n (s i)))) := by
  exact
    dense_gens_nsrbt
      (p := p) (Γ := Γ) s hs hn
      (nsrbt_generators_one (p := p) (e := n) hd)

/-- Abstract generation of the self-quotient supplies a controlled finite shadow.

The finite target can be the trivial group: its kernel is the whole self-quotient, which lies in
the generator-image subgroup exactly because that subgroup is assumed to be all of the
self-quotient. -/
lemma gens_control_generation
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ]
    {d : ℕ} (s : Fin d → Γ)
    {n : ℕ}
    (Hgen : SelfAbstractGeneration
      (p := p) (Γ := Γ) s n) :
    ∃ C : GCShadow
        (p := p) (Γ := Γ) s n,
      (let S := C.continuousFinShadow
      letI : Group S.quotientGroup := S.instGroup
      S.quotientMap.ker ≤
        Subgroup.closure
          (Set.range
            (fun i : Fin d =>
              denseGeneratorsSelf p Γ n (s i)))) := by
  classical
  let Ω : Type u := denseSelfQuotient p Γ n
  let A :
      GSAlg
        (p := p) (Γ := Γ) s n :=
    { quotientGroup := PUnit
      instGroup := inferInstance
      instFinite := inferInstance
      quotientMap :=
        { toFun := fun _ => 1
          map_one' := rfl
          map_mul' := by
            intro _ _
            rfl } }
  let T :
      ShadowTopologyData
        (p := p) (Γ := Γ) A :=
    { quotientTopologicalSpace := ⊥
      quotientDiscreteTopology := discreteTopology_bot PUnit
      quotientMap_continuous := continuous_const
      kernel_map_continuous := by
        letI : A.quotientMap.ker.Normal := inferInstance
        letI : TopologicalSpace
            (denseSelfQuotient p Γ n ⧸ A.quotientMap.ker) := ⊥
        have hconst :
            (fun x : denseSelfQuotient p Γ n =>
              (QuotientGroup.mk' A.quotientMap.ker) x) =
              fun _ => 1 := by
          funext x
          exact
            (QuotientGroup.eq_one_iff (N := A.quotientMap.ker) x).2
              (by rfl)
        rw [hconst]
        exact continuous_const }
  let C :
      GCShadow
        (p := p) (Γ := Γ) s n :=
    { algebraic := A
      topologyData := T }
  refine ⟨C, ?_⟩
  have htop :
      Subgroup.closure
          (Set.range
            (fun i : Fin d =>
              denseGeneratorsSelf p Γ n (s i))) =
        (⊤ : Subgroup Ω) := by
    simpa [Ω, denseSelfTuple] using
      Hgen.closure_range_top
  dsimp [
    C,
    T,
    A,
    GCShadow.continuousFinShadow,
    GSAlg.continuousFinShadow
  ]
  rw [htop]
  exact le_top

/-- Any controlled finite shadow forces abstract generation of the entire self-quotient.

The shadow kernel is open because its target is discrete.  If that open kernel lies in the
generator-image subgroup, then the generator-image subgroup is itself open and hence closed.
Density of the tuple images therefore makes it the whole self-quotient. -/
lemma gens_shadow_control
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    {d : ℕ} {s : Fin d → Γ}
    {n : ℕ}
    (C : GCShadow
      (p := p) (Γ := Γ) s n)
    (hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤)
    (hkernel :
      let S := C.continuousFinShadow
      letI : Group S.quotientGroup := S.instGroup
      S.quotientMap.ker ≤
        Subgroup.closure
          (Set.range
            (fun i : Fin d =>
              denseGeneratorsSelf p Γ n (s i)))) :
    Subgroup.closure
        (Set.range
          (fun i : Fin d =>
            denseGeneratorsSelf p Γ n (s i))) =
      (⊤ : Subgroup (denseSelfQuotient p Γ n)) := by
  classical
  let Ω : Type u := denseSelfQuotient p Γ n
  letI : (zassenhausFiltration p Γ n).Normal :=
    zassenhausFiltration_normal p Γ n
  letI : IsTopologicalGroup Ω := by
    dsimp [Ω, denseSelfQuotient]
    exact
      QuotientGroup.instIsTopologicalGroup
        (N := zassenhausFiltration p Γ n)
  haveI : ContinuousMul Ω :=
    IsTopologicalGroup.toContinuousMul
  haveI : SeparatelyContinuousMul Ω :=
    instSeparatelyContinuousMulOfContinuousMul
  let K : Subgroup Ω :=
    Subgroup.closure
      (Set.range
        (fun i : Fin d =>
          denseGeneratorsSelf p Γ n (s i)))
  let S :
      SCShadow
        (p := p) (Γ := Γ) s n :=
    C.continuousFinShadow
  letI : Group S.quotientGroup := S.instGroup
  letI : TopologicalSpace S.quotientGroup := S.instTopologicalSpace
  letI : DiscreteTopology S.quotientGroup := S.instDiscreteTopology
  have hker_le : S.quotientMap.ker ≤ K := by
    simpa [S, K, Ω] using hkernel
  have hker_open :
      IsOpen ((S.quotientMap.ker : Subgroup Ω) : Set Ω) :=
    monoid_open_discrete
      (Γ := Ω) (Λ := S.quotientGroup)
      S.quotientMap
      S.quotientMap_continuous
  have hK_nhds : (K : Set Ω) ∈ 𝓝 (1 : Ω) :=
    Filter.mem_of_superset
      (hker_open.mem_nhds S.quotientMap.ker.one_mem)
      hker_le
  have hK_open : IsOpen (K : Set Ω) :=
    Subgroup.isOpen_of_mem_nhds K hK_nhds
  have hK_closed : IsClosed (K : Set Ω) :=
    K.isClosed_of_isOpen hK_open
  have hK_dense : closure (K : Set Ω) = Set.univ := by
    simpa [K, Ω] using
      dense_self_quotient
        (p := p) (Γ := Γ) s hs (n := n)
  have hK_univ : (K : Set Ω) = Set.univ := by
    rw [← hK_closed.closure_eq]
    exact hK_dense
  change K = ⊤
  apply top_unique
  intro x _hx
  change x ∈ (K : Set Ω)
  rw [hK_univ]
  exact Set.mem_univ x

/-- Finite NS/RBT supplies enough finite-shadow control to make the dense tuple images
algebraically generate the Zassenhaus self-quotient. -/
lemma dense_self_nsrbt
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} (s : Fin d → Γ)
    (hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤)
    {n : ℕ}
    (hn : 1 < n)
    (hNS : NPPower.{u} d p n) :
    Subgroup.closure
        (Set.range
          (fun i : Fin d =>
            denseGeneratorsSelf p Γ n (s i))) =
      (⊤ : Subgroup (denseSelfQuotient p Γ n)) := by
  rcases
    dense_gens_nsrbt
      (p := p) (Γ := Γ) s hs hn hNS with
    ⟨C, hkernel⟩
  exact
    gens_shadow_control
      (p := p) (Γ := Γ) (s := s) (n := n) C hs hkernel

/-- For a dense tuple of size at most one, the images algebraically generate the Zassenhaus
self-quotient. -/
lemma dense_generators_self
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} (s : Fin d → Γ)
    (hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤)
    (hd : d ≤ 1)
    {n : ℕ}
    (hn : 1 < n) :
    Subgroup.closure
        (Set.range
          (fun i : Fin d =>
            denseGeneratorsSelf p Γ n (s i))) =
      (⊤ : Subgroup (denseSelfQuotient p Γ n)) := by
  exact
    dense_self_nsrbt
      (p := p) (Γ := Γ) s hs hn
      (nsrbt_generators_one (p := p) (e := n) hd)

/-- Closedness of `D_n(Γ)` is enough to make the dense tuple images algebraically generate the
Zassenhaus self-quotient. -/
lemma dense_self_closed
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} (s : Fin d → Γ)
    (hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤)
    {n : ℕ}
    (hn : 1 < n)
    (hclosed :
      IsClosed ((zassenhausFiltration p Γ n : Subgroup Γ) : Set Γ)) :
    Subgroup.closure
        (Set.range
          (fun i : Fin d =>
            denseGeneratorsSelf p Γ n (s i))) =
      (⊤ : Subgroup (denseSelfQuotient p Γ n)) := by
  rcases
    gens_zassenhaus_closed
      (p := p) (Γ := Γ) s hs hn hclosed with
    ⟨C, hkernel⟩
  exact
    gens_shadow_control
      (p := p) (Γ := Γ) (s := s) (n := n) C hs hkernel

/-- A finite-width compact cover of `D_n(Γ)` supplies the closedness needed for abstract
generation of the Zassenhaus self-quotient by dense generator images. -/
lemma width_compact_cover
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} (s : Fin d → Γ)
    (hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤)
    {n : ℕ}
    (hn : 1 < n)
    (C : FCCover p Γ n) :
    Subgroup.closure
        (Set.range
          (fun i : Fin d =>
            denseGeneratorsSelf p Γ n (s i))) =
      (⊤ : Subgroup (denseSelfQuotient p Γ n)) := by
  exact
    dense_self_closed
      (p := p) (Γ := Γ) s hs hn C.isClosed

/-- A lower-central/power word-map compression package gives abstract generation of the
Zassenhaus self-quotient by the dense tuple images. -/
lemma
  self_compression_package
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} (s : Fin d → Γ)
    (hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤)
    {n : ℕ}
    (hn : 1 < n)
    (P :
      DCPackag
        p Γ n) :
    Subgroup.closure
        (Set.range
          (fun i : Fin d =>
            denseGeneratorsSelf p Γ n (s i))) =
      (⊤ : Subgroup (denseSelfQuotient p Γ n)) := by
  haveI : T2Space Γ := t_space_disconnected Γ
  rcases P.exists_compactCover with ⟨C⟩
  exact
    width_compact_cover
      (p := p) (Γ := Γ) s hs hn C

/-- Residual finite-quotient separation of `D_n(Γ)` implies abstract generation of the
self-quotient by the dense tuple images. -/
lemma dense_self_separation
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} (s : Fin d → Γ)
    (hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤)
    {n : ℕ}
    (hn : 1 < n)
    (R : DGSep p Γ n) :
    Subgroup.closure
        (Set.range
          (fun i : Fin d =>
            denseGeneratorsSelf p Γ n (s i))) =
      (⊤ : Subgroup (denseSelfQuotient p Γ n)) := by
  exact
    dense_self_closed
      (p := p) (Γ := Γ) s hs hn
      (DGSep.closed_zassenhaus_filtration R)

/-- In the commutative profinite case, the dense tuple images algebraically generate the
Zassenhaus self-quotient. -/
lemma self_top_comm
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [CommGroup Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} (s : Fin d → Γ)
    (hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤)
    {n : ℕ}
    (hn : 1 < n) :
    Subgroup.closure
        (Set.range
          (fun i : Fin d =>
            denseGeneratorsSelf p Γ n (s i))) =
      (⊤ : Subgroup (denseSelfQuotient p Γ n)) := by
  exact
    dense_self_separation
      (p := p) (Γ := Γ) s hs hn
      (dense_separation_comm
        (p := p) (Γ := Γ) s hs n)

/-- At one fixed degree, bounded power width and the weak restricted-Burnside consequence of
Zelmanov's theorem supply the controlled self-quotient shadow.

This isolates the smallest deep inputs needed by the general target: Nikolov-Segal power width and
Zelmanov remain separate, and neither is strengthened to a uniform cardinal bound. -/
lemma gens_quotients_burnside
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} (s : Fin d → Γ)
    (hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤)
    {n k : ℕ}
    (hn : 1 < n)
    (hwidth : HPWidth Γ (p ^ n) k)
    (hBurnside :
      SQBurnsi.{u} (p ^ n)) :
    ∃ C : GCShadow
        (p := p) (Γ := Γ) s n,
      let S := C.continuousFinShadow
      letI : Group S.quotientGroup := S.instGroup
      S.quotientMap.ker ≤
        Subgroup.closure
          (Set.range
            (fun i : Fin d =>
              denseGeneratorsSelf p Γ n (s i))) := by
  exact
    dense_gens_open
      (p := p) (Γ := Γ) s hs hn
      (separating_quotients_burnside
        (Γ := Γ) s hs hwidth hBurnside)

/-- A fixed-exponent power-width witness for one abstract group.

This package isolates the Nikolov--Segal part of the general controlled-shadow theorem.  It does
not mention Zassenhaus filtrations, finite shadows, or restricted Burnside: it only records that
the subgroup generated by the `m`th powers is the image of one bounded power-word map. -/
structure DWInput
    (Γ : Type u) [Group Γ]
    (m : ℕ) :
    Type u where
  width : ℕ
  hasPowerWidth : HPWidth Γ m width

namespace DWInput

/-- Package an existential fixed-exponent width bound. -/
noncomputable def of_exists
    {Γ : Type u} [Group Γ]
    {m : ℕ}
    (hwidth : ∃ k : ℕ, HPWidth Γ m k) :
    DWInput Γ m := by
  exact
    { width := Classical.choose hwidth
      hasPowerWidth := Classical.choose_spec hwidth }

/-- A fixed-exponent width package is equivalent to an existential width bound. -/
lemma nonempty_iff_exists
    {Γ : Type u} [Group Γ]
    {m : ℕ} :
    Nonempty (DWInput Γ m) ↔
      ∃ k : ℕ, HPWidth Γ m k := by
  constructor
  · rintro ⟨W⟩
    exact ⟨W.width, W.hasPowerWidth⟩
  · intro hwidth
    exact ⟨of_exists hwidth⟩

/-- A packaged width witness identifies the power subgroup with a single power-word range. -/
lemma power_range_word
    {Γ : Type u} [Group Γ]
    {m : ℕ}
    (W : DWInput Γ m) :
    ((powerSubgroup Γ m : Subgroup Γ) : Set Γ) =
      Set.range (powerWordMap Γ m W.width) := by
  exact
    power_range_width
      W.hasPowerWidth

/-- In a compact totally disconnected topological group, packaged width makes the power subgroup
closed. -/
lemma power_subgroup_closed
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {m : ℕ}
    (W : DWInput Γ m) :
    IsClosed ((powerSubgroup Γ m : Subgroup Γ) : Set Γ) := by
  exact
    closed_totally_disconnected
      (Γ := Γ) W.hasPowerWidth

/-- Increasing the number of power-word slots preserves a packaged fixed-exponent witness. -/
def enlarge
    {Γ : Type u} [Group Γ]
    {m : ℕ}
    (W : DWInput Γ m)
    {k : ℕ}
    (hwidth : W.width ≤ k) :
    DWInput Γ m := by
  exact
    { width := k
      hasPowerWidth :=
        HPWidth.mono_k
          W.hasPowerWidth hwidth }

/-- Adding one padding slot preserves a packaged fixed-exponent witness. -/
def succ
    {Γ : Type u} [Group Γ]
    {m : ℕ}
    (W : DWInput Γ m) :
    DWInput Γ m := by
  exact
    W.enlarge
      (Nat.le_succ W.width)

end DWInput

/-- The weak restricted-Burnside input at one fixed exponent.

This package isolates the Zelmanov part of the controlled-shadow theorem.  Unlike the width input,
it does not depend on the ambient profinite group or its dense tuple. -/
structure DBInput
    (m : ℕ) :
    Type (u + 1) where
  separatingBoundedExponent :
    SQBurnsi.{u} m

namespace DBInput

/-- Package a weak restricted-Burnside statement at one exponent. -/
def of_statement
    {m : ℕ}
    (hBurnside :
      SQBurnsi.{u} m) :
    DBInput.{u} m := by
  exact
    { separatingBoundedExponent := hBurnside }

/-- A packaged Burnside input is equivalent to the underlying fixed-exponent statement. -/
lemma nonempty_iff
    {m : ℕ} :
    Nonempty (DBInput.{u} m) ↔
      SQBurnsi.{u} m := by
  constructor
  · rintro ⟨B⟩
    exact B.separatingBoundedExponent
  · intro hBurnside
    exact ⟨of_statement hBurnside⟩

/-- A Burnside input for a larger exponent restricts to any divisor exponent. -/
def of_dvd
    {mSmall mBig : ℕ}
    (hdiv : mSmall ∣ mBig)
    (B : DBInput.{u} mBig) :
    DBInput.{u} mSmall := by
  exact
    { separatingBoundedExponent :=
        SQBurnsi.of_dvd_exponent
          hdiv
          B.separatingBoundedExponent }

/-- The elementary exponent-two Burnside statement as a packaged input. -/
def two :
    DBInput.{u} 2 := by
  exact
    of_statement
      separating_quotients_two

/-- The elementary exponent-one Burnside statement as a packaged input. -/
def one :
    DBInput.{u} 1 := by
  exact
    of_statement
      separating_quotients_bounded

end DBInput

/-- The two fixed-exponent deep inputs needed to prove openness of a power subgroup.

Keeping this intermediate package independent of `p` and `n` makes the reduction reusable: the
topological argument only consumes an exponent, a power-width witness, and the weak
restricted-Burnside statement at that same exponent. -/
structure DOInput
    (Γ : Type u) [Group Γ]
    (m : ℕ) :
    Type (u + 1) where
  widthInput : DWInput Γ m
  burnsideInput : DBInput.{u} m

namespace DOInput

/-- Combine separate fixed-exponent width and Burnside inputs. -/
def of_parts
    {Γ : Type u} [Group Γ]
    {m : ℕ}
    (W : DWInput Γ m)
    (B : DBInput.{u} m) :
    DOInput Γ m := by
  exact
    { widthInput := W
      burnsideInput := B }

/-- Nonemptiness of the combined fixed-exponent package is exactly the conjunction of its two
constituent inputs. -/
lemma nonempty_iff
    {Γ : Type u} [Group Γ]
    {m : ℕ} :
    Nonempty (DOInput Γ m) ↔
      (∃ k : ℕ, HPWidth Γ m k) ∧
        SQBurnsi.{u} m := by
  constructor
  · rintro ⟨I⟩
    exact
      ⟨⟨I.widthInput.width, I.widthInput.hasPowerWidth⟩,
        I.burnsideInput.separatingBoundedExponent⟩
  · rintro ⟨hwidth, hBurnside⟩
    exact
      ⟨of_parts
        (DWInput.of_exists hwidth)
        (DBInput.of_statement hBurnside)⟩

/-- The combined fixed-exponent package proves openness of the corresponding power subgroup in a
dense finitely generated profinite group. -/
lemma power_subgroup_open
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} (s : Fin d → Γ)
    (hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤)
    {m : ℕ}
    (I : DOInput Γ m) :
    IsOpen ((powerSubgroup Γ m : Subgroup Γ) : Set Γ) := by
  exact
    separating_quotients_burnside
      (Γ := Γ) s hs
      I.widthInput.hasPowerWidth
      I.burnsideInput.separatingBoundedExponent

/-- The combined fixed-exponent package also records the closedness step used inside the openness
proof. -/
lemma power_subgroup_closed
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {m : ℕ}
    (I : DOInput Γ m) :
    IsClosed ((powerSubgroup Γ m : Subgroup Γ) : Set Γ) := by
  exact
    I.widthInput.power_subgroup_closed

end DOInput

/-- The deep fixed-degree input for the general Zassenhaus controlled-shadow theorem.

At degree `n`, the formal construction needs openness of the `p ^ n` power subgroup.  The package
below retains the two independent ingredients proving that openness, so later rounds can attack
Nikolov--Segal and Zelmanov separately. -/
structure CSInput
    {p : ℕ} [Fact p.Prime]
    (Γ : Type u) [Group Γ]
    (n : ℕ) :
    Type (u + 1) where
  fixedExponentInput :
    DOInput Γ (p ^ n)

namespace CSInput

/-- Build the degree-`n` package from separate width and Burnside inputs at exponent `p ^ n`. -/
def of_parts
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ]
    {n : ℕ}
    (W : DWInput Γ (p ^ n))
    (B : DBInput.{u} (p ^ n)) :
    CSInput (p := p) Γ n := by
  exact
    { fixedExponentInput :=
        DOInput.of_parts W B }

/-- Nonemptiness of the prime-power package is exactly the conjunction of the two deep inputs at
the selected degree. -/
lemma nonempty_iff
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ]
    {n : ℕ} :
    Nonempty (CSInput (p := p) Γ n) ↔
      (∃ k : ℕ, HPWidth Γ (p ^ n) k) ∧
        SQBurnsi.{u} (p ^ n) := by
  constructor
  · rintro ⟨I⟩
    exact
      DOInput.nonempty_iff.mp
        ⟨I.fixedExponentInput⟩
  · intro h
    rcases
        DOInput.nonempty_iff.mpr h with
      ⟨I⟩
    exact
      ⟨{ fixedExponentInput := I }⟩

/-- The prime-power package proves openness of the power subgroup used at degree `n`. -/
lemma power_subgroup_open
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} (s : Fin d → Γ)
    (hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤)
    {n : ℕ}
    (I : CSInput (p := p) Γ n) :
    IsOpen ((powerSubgroup Γ (p ^ n) : Subgroup Γ) : Set Γ) := by
  exact
    I.fixedExponentInput.power_subgroup_open
      s hs

/-- Openness of the selected prime-power subgroup makes the corresponding Zassenhaus filtration
term closed. -/
lemma zassenhaus_filtration_closed
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} (s : Fin d → Γ)
    (hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤)
    {n : ℕ}
    (I : CSInput (p := p) Γ n) :
    IsClosed ((zassenhausFiltration p Γ n : Subgroup Γ) : Set Γ) := by
  have hle : n ≤ p ^ n :=
    nat_pow_self
      (Fact.out : Nat.Prime p).two_le
  exact
    filtration_closed_open
      (p := p) (G := Γ) hle
      (I.power_subgroup_open s hs)

/-- The prime-power package supplies the controlled finite shadow by the already-proved openness
reduction. -/
lemma constructed_shadow_control
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} (s : Fin d → Γ)
    (hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤)
    {n : ℕ}
    (I : CSInput (p := p) Γ n)
    (hn : 1 < n) :
    ∃ C : GCShadow
        (p := p) (Γ := Γ) s n,
      let S := C.continuousFinShadow
      letI : Group S.quotientGroup := S.instGroup
      S.quotientMap.ker ≤
        Subgroup.closure
          (Set.range
            (fun i : Fin d =>
              denseGeneratorsSelf p Γ n (s i))) := by
  exact
    dense_gens_open
      (p := p) (Γ := Γ) s hs hn
      (I.power_subgroup_open s hs)

end CSInput

/-- The finite-group Nikolov--Segal power-width input at one generator count and one exponent.

This is the algebraic core of the profinite power-width theorem.  It deliberately mentions only
finite abstract groups generated by a fixed-size tuple.  In particular, it has no topology,
open-normal subgroup, inverse-limit, or Zassenhaus content. -/
structure GWInput
    (d m : ℕ) :
    Type (u + 1) where
  width : ℕ
  powerWidthBound : PWBound.{u} d m width

namespace GWInput

/-- Package an existential finite-group power-width bound. -/
noncomputable def of_exists
    {d m : ℕ}
    (hwidth : ∃ k : ℕ, PWBound.{u} d m k) :
    GWInput.{u} d m := by
  exact
    { width := Classical.choose hwidth
      powerWidthBound := Classical.choose_spec hwidth }

/-- A finite-group width package is equivalent to an existential uniform bound. -/
lemma nonempty_iff_exists
    {d m : ℕ} :
    Nonempty (GWInput.{u} d m) ↔
      ∃ k : ℕ, PWBound.{u} d m k := by
  constructor
  · rintro ⟨W⟩
    exact
      ⟨W.width,
        W.powerWidthBound⟩
  · intro hwidth
    exact
      ⟨of_exists hwidth⟩

/-- Apply a packaged finite width theorem to one finite generated group. -/
lemma hasPowerWidth
    {d m : ℕ}
    (W : GWInput.{u} d m)
    (Q : Type u) [Group Q] [Finite Q]
    (t : Fin d → Q)
    (ht : GeneratedBy t) :
    HPWidth Q m W.width := by
  exact
    W.powerWidthBound
      Q
      t
      ht

/-- Increasing the number of available power-word slots preserves a finite width package. -/
def enlarge
    {d m : ℕ}
    (W : GWInput.{u} d m)
    {k : ℕ}
    (hwidth : W.width ≤ k) :
    GWInput.{u} d m := by
  refine
    { width := k
      powerWidthBound := ?_ }
  intro Q _instGroupQ _instFiniteQ t ht
  exact
    HPWidth.mono_k
      (W.hasPowerWidth Q t ht)
      hwidth

/-- One padding slot preserves a finite width package. -/
def succ
    {d m : ℕ}
    (W : GWInput.{u} d m) :
    GWInput.{u} d m := by
  exact
    W.enlarge
      (Nat.le_succ W.width)

/-- A bound for larger generating tuples restricts to smaller tuples. -/
def mono_generators
    {d d' m : ℕ}
    (hdd' : d ≤ d')
    (W : GWInput.{u} d' m) :
    GWInput.{u} d m := by
  refine
    { width := W.width
      powerWidthBound := ?_ }
  exact
    PWBound.mono_generators
      hdd'
      W.powerWidthBound

/-- The empty tuple case is elementary. -/
def zero
    (m : ℕ) :
    GWInput.{u} 0 m := by
  refine
    { width := 0
      powerWidthBound := ?_ }
  exact
    width_bound_generators
      m

/-- First powers have width one for every generator count. -/
def one
    (d : ℕ) :
    GWInput.{u} d 1 := by
  refine
    { width := 1
      powerWidthBound := ?_ }
  exact
    width_bound_one
      d

/-- One-generated finite groups have width one for every exponent. -/
def oneGenerator
    (m : ℕ) :
    GWInput.{u} 1 m := by
  refine
    { width := 1
      powerWidthBound := ?_ }
  exact
    width_bound_generator
      m

/-- The elementary one-generator theorem restricts to any generator count at most one. -/
def generators_one
    {d m : ℕ}
    (hd : d ≤ 1) :
    GWInput.{u} d m := by
  exact
    (oneGenerator m).mono_generators
      hd

end GWInput

/-- Uniform power width for all open-normal quotients of one profinite group.

This package is the middle layer between the finite abstract Nikolov--Segal theorem and the
ambient profinite conclusion.  It keeps the compact-image detection argument independent from the
finite-group theorem used to establish the quotient bounds. -/
structure OWInput
    (Γ : Type u) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    (m k : ℕ) :
    Type (u + 1) where
  quotientPowerWidth :
    ∀ N : OpenNormalSubgroup Γ,
      HPWidth (Γ ⧸ N.toSubgroup) m k

namespace OWInput

/-- A finite uniform width theorem applies to every open-normal quotient of a densely generated
profinite group. -/
def of_finiteInput
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ]
    {d m : ℕ}
    (s : Fin d → Γ)
    (hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤)
    (W : GWInput.{u} d m) :
    OWInput Γ m W.width := by
  refine
    { quotientPowerWidth := ?_ }
  intro N
  letI : DiscreteTopology (Γ ⧸ N.toSubgroup) :=
    open_discrete_topology N
  letI : Finite (Γ ⧸ N.toSubgroup) :=
    open_normal_finite N
  have hgenerated :
      GeneratedBy
        (fun i : Fin d =>
          QuotientGroup.mk' N.toSubgroup (s i)) := by
    exact
      GeneratedBy.of_dense_image
        s
        hs
        (QuotientGroup.mk' N.toSubgroup)
        (open_normal_continuous N)
        (QuotientGroup.mk'_surjective N.toSubgroup)
  exact
    W.hasPowerWidth
      (Γ ⧸ N.toSubgroup)
      (fun i : Fin d =>
        QuotientGroup.mk' N.toSubgroup (s i))
      hgenerated

/-- Quotient width remains valid after increasing the number of power-word slots. -/
def enlarge
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    {m k : ℕ}
    (I : OWInput Γ m k)
    {k' : ℕ}
    (hkk' : k ≤ k') :
    OWInput Γ m k' := by
  refine
    { quotientPowerWidth := ?_ }
  intro N
  exact
    HPWidth.mono_k
      (I.quotientPowerWidth N)
      hkk'

/-- Adding one padding slot preserves open-normal quotient width. -/
def succ
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    {m k : ℕ}
    (I : OWInput Γ m k) :
    OWInput Γ m (k + 1) := by
  exact
    I.enlarge
      (Nat.le_succ k)

/-- Compact-image detection lifts uniform open-normal quotient width to the ambient group. -/
lemma ambientPowerWidth
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {m k : ℕ}
    (I : OWInput Γ m k) :
    HPWidth Γ m k := by
  exact
    width_open_normal
      (Γ := Γ)
      (m := m)
      (k := k)
      (detection_compact_disconnected
        (Γ := Γ))
      I.quotientPowerWidth

/-- Uniform open-normal quotient width gives the fixed-exponent ambient package. -/
def fixedInput
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {m k : ℕ}
    (I : OWInput Γ m k) :
    DWInput Γ m := by
  exact
    { width := k
      hasPowerWidth :=
        I.ambientPowerWidth }

end OWInput

namespace GWInput

/-- A finite uniform theorem supplies the corresponding open-normal quotient package. -/
def openNormalInput
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ]
    {d m : ℕ}
    (W : GWInput.{u} d m)
    (s : Fin d → Γ)
    (hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤) :
    OWInput Γ m W.width := by
  exact
    OWInput.of_finiteInput
      s
      hs
      W

/-- A finite uniform theorem gives bounded width in the ambient compact totally disconnected
group. -/
lemma ambientPowerWidth
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d m : ℕ}
    (W : GWInput.{u} d m)
    (s : Fin d → Γ)
    (hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤) :
    HPWidth Γ m W.width := by
  exact
    (W.openNormalInput s hs).ambientPowerWidth

/-- A finite uniform theorem gives the packaged ambient fixed-exponent width input. -/
def fixedInput
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d m : ℕ}
    (W : GWInput.{u} d m)
    (s : Fin d → Γ)
    (hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤) :
    DWInput Γ m := by
  exact
    (W.openNormalInput s hs).fixedInput

/-- The finite input immediately proves the ambient nonemptiness formulation. -/
lemma fixed_input_nonempty
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d m : ℕ}
    (W : GWInput.{u} d m)
    (s : Fin d → Γ)
    (hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤) :
    Nonempty (DWInput Γ m) := by
  exact
    ⟨W.fixedInput
      s
      hs⟩

end GWInput

/-- Uniform power width restricted to finite commutative groups.

This is one half of the finite abstract Nikolov--Segal input.  Keeping the commutative branch
separate is useful because it can be attacked by abelian generation arguments without carrying
any of the noncommutative finite-group theory. -/
def CWBound.{q}
    (d m k : ℕ) :
    Prop :=
  ∀ (G : Type q) [Group G] [Finite G]
      (t : Fin d → G),
    GeneratedBy t →
      (∀ a b : G, a * b = b * a) →
        HPWidth G m k

/-- Uniform power width restricted to finite genuinely noncommutative groups.

This is the complementary finite-group branch.  It is strictly weaker than an unrestricted
finite power-width theorem: commutative groups have been removed from its quantifier. -/
def NWBound.{q}
    (d m k : ℕ) :
    Prop :=
  ∀ (G : Type q) [Group G] [Finite G]
      (t : Fin d → G),
    GeneratedBy t →
      (¬ ∀ a b : G, a * b = b * a) →
        HPWidth G m k

namespace CWBound

/-- A commutative finite width bound remains valid after increasing the number of word slots. -/
lemma mono_width
    {d m k k' : ℕ}
    (h : CWBound.{u} d m k)
    (hkk' : k ≤ k') :
    CWBound.{u} d m k' := by
  intro G _instGroupG _instFiniteG t ht hcomm
  exact
    HPWidth.mono_k
      (h G t ht hcomm)
      hkk'

/-- A commutative finite width theorem for larger tuples restricts to smaller tuples. -/
lemma mono_generators
    {d d' m k : ℕ}
    (hdd' : d ≤ d')
    (h : CWBound.{u} d' m k) :
    CWBound.{u} d m k := by
  intro G _instGroupG _instFiniteG t ht hcomm
  exact
    h G
      (padGenerators hdd' t)
      (GeneratedBy.pad hdd' ht)
      hcomm

/-- An unrestricted finite power-width bound gives its commutative restriction. -/
lemma finite_width_bound
    {d m k : ℕ}
    (h : PWBound.{u} d m k) :
    CWBound.{u} d m k := by
  intro G _instGroupG _instFiniteG t ht _hcomm
  exact
    h G
      t
      ht

/-- Apply a commutative bound to one finite generated commutative group. -/
lemma hasPowerWidth
    {d m k : ℕ}
    (h : CWBound.{u} d m k)
    (G : Type u) [Group G] [Finite G]
    (t : Fin d → G)
    (ht : GeneratedBy t)
    (hcomm : ∀ a b : G, a * b = b * a) :
    HPWidth G m k := by
  exact
    h G
      t
      ht
      hcomm

end CWBound

namespace NWBound

/-- A noncommutative finite width bound remains valid after increasing the number of word
slots. -/
lemma mono_width
    {d m k k' : ℕ}
    (h : NWBound.{u} d m k)
    (hkk' : k ≤ k') :
    NWBound.{u} d m k' := by
  intro G _instGroupG _instFiniteG t ht hnoncomm
  exact
    HPWidth.mono_k
      (h G t ht hnoncomm)
      hkk'

/-- A noncommutative finite width theorem for larger tuples restricts to smaller tuples. -/
lemma mono_generators
    {d d' m k : ℕ}
    (hdd' : d ≤ d')
    (h : NWBound.{u} d' m k) :
    NWBound.{u} d m k := by
  intro G _instGroupG _instFiniteG t ht hnoncomm
  exact
    h G
      (padGenerators hdd' t)
      (GeneratedBy.pad hdd' ht)
      hnoncomm

/-- An unrestricted finite power-width bound gives its noncommutative restriction. -/
lemma finite_width_bound
    {d m k : ℕ}
    (h : PWBound.{u} d m k) :
    NWBound.{u} d m k := by
  intro G _instGroupG _instFiniteG t ht _hnoncomm
  exact
    h G
      t
      ht

/-- Apply a noncommutative bound to one finite generated noncommutative group. -/
lemma hasPowerWidth
    {d m k : ℕ}
    (h : NWBound.{u} d m k)
    (G : Type u) [Group G] [Finite G]
    (t : Fin d → G)
    (ht : GeneratedBy t)
    (hnoncomm : ¬ ∀ a b : G, a * b = b * a) :
    HPWidth G m k := by
  exact
    h G
      t
      ht
      hnoncomm

end NWBound

/-- A pair of disjoint finite-group inputs for one generator count and exponent.

The two stored bounds need not agree.  Taking their maximum recovers an unrestricted finite
power-width bound by deciding whether the finite target group is commutative. -/
structure WSInput
    (d m : ℕ) :
    Type (u + 1) where
  commutativeWidth : ℕ
  noncommutativeWidth : ℕ
  commutativeBound :
    CWBound.{u} d m commutativeWidth
  noncommutativeBound :
    NWBound.{u} d m noncommutativeWidth

namespace WSInput

/-- The common width obtained by padding the two disjoint finite-group branches. -/
def width
    {d m : ℕ}
    (S : WSInput.{u} d m) :
    ℕ :=
  max S.commutativeWidth S.noncommutativeWidth

/-- The commutative branch remains valid at the common padded width. -/
lemma commutativeBound_width
    {d m : ℕ}
    (S : WSInput.{u} d m) :
    CWBound.{u} d m S.width := by
  exact
    S.commutativeBound.mono_width
      (le_max_left
        S.commutativeWidth
        S.noncommutativeWidth)

/-- The noncommutative branch remains valid at the common padded width. -/
lemma noncommutativeBound_width
    {d m : ℕ}
    (S : WSInput.{u} d m) :
    NWBound.{u} d m S.width := by
  exact
    S.noncommutativeBound.mono_width
      (le_max_right
        S.commutativeWidth
        S.noncommutativeWidth)

/-- Splitting finite groups according to commutativity recovers an unrestricted finite
power-width theorem. -/
lemma powerWidthBound
    {d m : ℕ}
    (S : WSInput.{u} d m) :
    PWBound.{u} d m S.width := by
  intro G _instGroupG _instFiniteG t ht
  by_cases hcomm :
      ∀ a b : G,
        a * b = b * a
  · exact
      S.commutativeBound_width
        G
        t
        ht
        hcomm
  · exact
      S.noncommutativeBound_width
        G
        t
        ht
        hcomm

/-- Package the recombined finite theorem in the interface consumed by the profinite bridge. -/
def toFiniteInput
    {d m : ℕ}
    (S : WSInput.{u} d m) :
    GWInput.{u} d m := by
  exact
    { width := S.width
      powerWidthBound :=
        S.powerWidthBound }

/-- The packaged finite input produced by a split input is nonempty. -/
lemma finiteInput_nonempty
    {d m : ℕ}
    (S : WSInput.{u} d m) :
    Nonempty (GWInput.{u} d m) := by
  exact
    ⟨S.toFiniteInput⟩

/-- Build a split package from existential bounds for the two disjoint branches. -/
noncomputable def of_exists
    {d m : ℕ}
    (hcomm :
      ∃ k : ℕ,
        CWBound.{u} d m k)
    (hnoncomm :
      ∃ k : ℕ,
        NWBound.{u} d m k) :
    WSInput.{u} d m := by
  exact
    { commutativeWidth :=
        Classical.choose hcomm
      noncommutativeWidth :=
        Classical.choose hnoncomm
      commutativeBound :=
        Classical.choose_spec hcomm
      noncommutativeBound :=
        Classical.choose_spec hnoncomm }

/-- Nonemptiness of the split package is exactly separate boundedness of the commutative and
noncommutative families. -/
lemma nonempty_iff_exists
    {d m : ℕ} :
    Nonempty (WSInput.{u} d m) ↔
      (∃ k : ℕ,
        CWBound.{u} d m k) ∧
      (∃ k : ℕ,
        NWBound.{u} d m k) := by
  constructor
  · rintro ⟨S⟩
    exact
      ⟨⟨S.commutativeWidth,
          S.commutativeBound⟩,
        ⟨S.noncommutativeWidth,
          S.noncommutativeBound⟩⟩
  · rintro ⟨hcomm, hnoncomm⟩
    exact
      ⟨of_exists
        hcomm
        hnoncomm⟩

/-- Increasing each branch width gives another split package. -/
def enlarge
    {d m : ℕ}
    (S : WSInput.{u} d m)
    {commutativeWidth' noncommutativeWidth' : ℕ}
    (hcomm :
      S.commutativeWidth ≤
        commutativeWidth')
    (hnoncomm :
      S.noncommutativeWidth ≤
        noncommutativeWidth') :
    WSInput.{u} d m := by
  exact
    { commutativeWidth :=
        commutativeWidth'
      noncommutativeWidth :=
        noncommutativeWidth'
      commutativeBound :=
        S.commutativeBound.mono_width
          hcomm
      noncommutativeBound :=
        S.noncommutativeBound.mono_width
          hnoncomm }

/-- Add one padding slot to each branch of a split package. -/
def succ
    {d m : ℕ}
    (S : WSInput.{u} d m) :
    WSInput.{u} d m := by
  exact
    S.enlarge
      (Nat.le_succ S.commutativeWidth)
      (Nat.le_succ S.noncommutativeWidth)

/-- A split theorem for larger generating tuples restricts to smaller tuples branchwise. -/
def mono_generators
    {d d' m : ℕ}
    (hdd' : d ≤ d')
    (S : WSInput.{u} d' m) :
    WSInput.{u} d m := by
  exact
    { commutativeWidth :=
        S.commutativeWidth
      noncommutativeWidth :=
        S.noncommutativeWidth
      commutativeBound :=
        S.commutativeBound.mono_generators
          hdd'
      noncommutativeBound :=
        S.noncommutativeBound.mono_generators
          hdd' }

/-- An unrestricted finite input can always be viewed as a split input with the same bound on
both branches. -/
def of_finiteInput
    {d m : ℕ}
    (W : GWInput.{u} d m) :
    WSInput.{u} d m := by
  exact
    { commutativeWidth :=
        W.width
      noncommutativeWidth :=
        W.width
      commutativeBound :=
        CWBound.finite_width_bound
          W.powerWidthBound
      noncommutativeBound :=
        NWBound.finite_width_bound
          W.powerWidthBound }

end WSInput

/-- A finite tuple carrying an abstract generation proof.

This package is useful when a statement starts with the `Group.FG` typeclass but the finite
restricted-Burnside input is phrased for an explicitly sized tuple. -/
structure DGTuple
    (G : Type u) [Group G] :
    Type u where
  size : ℕ
  tuple : Fin size → G
  generates : GeneratedBy tuple

namespace DGTuple

/-- Extract an explicitly sized generating tuple from an abstract finite-generation proof. -/
noncomputable def of_groupFG
    (G : Type u) [Group G]
    (hfg : Group.FG G) :
    DGTuple G := by
  classical
  let hdata :=
    Group.fg_iff.mp hfg
  let S : Set G :=
    Classical.choose hdata
  have hSdata :
      Subgroup.closure S = (⊤ : Subgroup G) ∧
        S.Finite :=
    Classical.choose_spec hdata
  have hgen :
      Subgroup.closure S = (⊤ : Subgroup G) :=
    hSdata.1
  have hS :
      S.Finite :=
    hSdata.2
  letI : Fintype S :=
    hS.fintype
  let t : Fin (Fintype.card S) → G :=
    fun i =>
      ((Fintype.equivFin S).symm i : S)
  have hrange :
      Set.range t = S := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact
        ((Fintype.equivFin S).symm i).property
    · intro hx
      refine
        ⟨Fintype.equivFin S ⟨x, hx⟩, ?_⟩
      simp [t]
  have hgent :
      GeneratedBy t := by
    rw [GeneratedBy, hrange]
    exact hgen
  exact
    { size := Fintype.card S
      tuple := t
      generates := hgent }

/-- An explicit finite generating tuple recovers the abstract finite-generation typeclass. -/
lemma groupFG
    {G : Type u} [Group G]
    (T : DGTuple G) :
    Group.FG G := by
  exact
    GeneratedBy.groupFG
      T.generates

/-- Homomorphisms out of a group generated by an explicit tuple are determined by their values
on that tuple. -/
lemma monoidHom_ext
    {G : Type u} {Q : Type v} [Group G] [Group Q]
    (T : DGTuple G)
    {φ ψ : G →* Q}
    (hφψ :
      ∀ i : Fin T.size,
        φ (T.tuple i) =
          ψ (T.tuple i)) :
    φ = ψ := by
  apply DFunLike.ext _ _
  intro x
  have hx :
      x ∈ Subgroup.closure (Set.range T.tuple) := by
    rw [T.generates]
    exact
      Subgroup.mem_top x
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
      rcases hx with
        ⟨i, rfl⟩
      exact
        hφψ i
  | one =>
      simp
  | mul x y _hx _hy hx hy =>
      simp [hx, hy]
  | inv x _hx hx =>
      simp [hx]

/-- A surjective homomorphic image inherits the image generating tuple with the same size. -/
def map_surjective
    {G Q : Type u} [Group G] [Group Q]
    (T : DGTuple G)
    (φ : G →* Q)
    (hφ : Function.Surjective φ) :
    DGTuple Q := by
  exact
    { size := T.size
      tuple := fun i => φ (T.tuple i)
      generates :=
        GeneratedBy.map_surjective
          φ
          hφ
          T.generates }

/-- The image tuple introduced by `map_surjective` is definitionally the pointwise image. -/
@[simp] lemma map_surjective_tuple
    {G Q : Type u} [Group G] [Group Q]
    (T : DGTuple G)
    (φ : G →* Q)
    (hφ : Function.Surjective φ)
    (i : Fin T.size) :
    (T.map_surjective φ hφ).tuple i =
      φ (T.tuple i) := by
  rfl

/-- Mapping an explicit tuple through a surjection preserves the number of generators. -/
@[simp] lemma map_surjective_size
    {G Q : Type u} [Group G] [Group Q]
    (T : DGTuple G)
    (φ : G →* Q)
    (hφ : Function.Surjective φ) :
    (T.map_surjective φ hφ).size =
      T.size := by
  rfl

end DGTuple

/-- A uniform cardinality bound for all finite quotient images of one abstract group.

Unlike a restricted-Burnside theorem, this definition no longer mentions an exponent or a
chosen generating tuple.  It is the exact finite-quotient datum consumed by the residual
finiteness extraction step below. -/
def DCBound
    (G : Type u) [Group G]
    (B : ℕ) :
    Prop :=
  ∀ (Q : Type u) [Group Q] [Finite Q]
      (φ : G →* Q),
    Function.Surjective φ →
      Nat.card Q ≤ B

namespace DCBound

/-- A finite-quotient cardinality bound remains true after increasing the numeric bound. -/
lemma mono
    {G : Type u} [Group G]
    {B B' : ℕ}
    (h : DCBound G B)
    (hBB' : B ≤ B') :
    DCBound G B' := by
  intro Q _instGroupQ _instFiniteQ φ hφ
  exact
    (h Q φ hφ).trans
      hBB'

/-- A finite group has the tautological quotient-image cardinality bound given by its own
cardinality. -/
lemma of_finite
    (G : Type u) [Group G] [Finite G] :
    DCBound G (Nat.card G) := by
  intro Q _instGroupQ _instFiniteQ φ hφ
  exact
    Nat.card_le_card_of_surjective
      φ
      hφ

/-- A restricted-Burnside bound for one explicit tuple controls every finite quotient image.

This is the finite algebraic transport step: the image tuple generates each quotient, and the
ambient exponent identity descends through the quotient map. -/
lemma tuple_restricted_burnside
    {G : Type u} [Group G]
    {d m B : ℕ}
    (t : Fin d → G)
    (ht : GeneratedBy t)
    (hexp : ∀ x : G, x ^ m = 1)
    (hRBT : RBBound.{u} d m B) :
    DCBound G B := by
  intro Q _instGroupQ _instFiniteQ φ hφ
  apply hRBT Q
  · exact
      ⟨fun i => φ (t i),
        GeneratedBy.map_surjective
          φ
          hφ
          ht⟩
  · intro q
    rcases hφ q with
      ⟨x, rfl⟩
    calc
      φ x ^ m = φ (x ^ m) := by
        rw [map_pow]
      _ = φ 1 := by
        rw [hexp x]
      _ = 1 := by
        exact φ.map_one

/-- The tuple-packaged version of `tuple_restricted_burnside`. -/
lemma restricted_burnside_bound
    {G : Type u} [Group G]
    {m B : ℕ}
    (T : DGTuple G)
    (hexp : ∀ x : G, x ^ m = 1)
    (hRBT : RBBound.{u} T.size m B) :
    DCBound G B := by
  exact
    tuple_restricted_burnside
      T.tuple
      T.generates
      hexp
      hRBT

/-- Finite-quotient cardinality bounds descend along surjective homomorphisms. -/
lemma map_surjective
    {G Q : Type u} [Group G] [Group Q]
    {B : ℕ}
    (hG : DCBound G B)
    (φ : G →* Q)
    (hφ : Function.Surjective φ) :
    DCBound Q B := by
  intro F _instGroupF _instFiniteF ψ hψ
  exact
    hG F
      (ψ.comp φ)
      (hψ.comp hφ)

end DCBound

/-- Uniform finite restricted-Burnside cardinality bounds at one exponent.

This is the finite abstract Zelmanov layer.  It only quantifies over finite groups generated by
an explicit tuple, in contrast with the target weak consequence for arbitrary residually finite
finitely generated groups. -/
structure BCInput
    (m : ℕ) :
    Type (u + 1) where
  bound : ℕ → ℕ
  restrictedBurnsideBound :
    ∀ d : ℕ,
      RBBound.{u} d m (bound d)

namespace BCInput

/-- Package existential restricted-Burnside bounds, one for every finite tuple size. -/
noncomputable def of_exists
    {m : ℕ}
    (hRBT :
      ∀ d : ℕ,
        ∃ B : ℕ,
          RBBound.{u} d m B) :
    BCInput.{u} m := by
  exact
    { bound := fun d =>
        Classical.choose (hRBT d)
      restrictedBurnsideBound := fun d =>
        Classical.choose_spec (hRBT d) }

/-- Nonemptiness of the packaged finite input is equivalent to existential bounds at every
generator count. -/
lemma nonempty_iff_exists
    {m : ℕ} :
    Nonempty (BCInput.{u} m) ↔
      ∀ d : ℕ,
        ∃ B : ℕ,
          RBBound.{u} d m B := by
  constructor
  · rintro ⟨R⟩ d
    exact
      ⟨R.bound d,
        R.restrictedBurnsideBound d⟩
  · intro hRBT
    exact
      ⟨of_exists hRBT⟩

/-- A finite restricted-Burnside package for a larger exponent restricts to every divisor
exponent. -/
def of_dvd
    {mSmall mBig : ℕ}
    (hdiv : mSmall ∣ mBig)
    (R : BCInput.{u} mBig) :
    BCInput.{u} mSmall := by
  exact
    { bound := R.bound
      restrictedBurnsideBound := fun d =>
        RBBound.of_dvd_exponent
          hdiv
          (R.restrictedBurnsideBound d) }

/-- Exponent one has the elementary uniform finite restricted-Burnside cardinality package. -/
def one :
    BCInput.{u} 1 := by
  exact
    { bound := fun _d => 1
      restrictedBurnsideBound := fun d =>
        burnside_bound_one
          d }

/-- Exponent two has the elementary uniform finite restricted-Burnside cardinality package. -/
def two :
    BCInput.{u} 2 := by
  exact
    { bound := fun d => 2 ^ d
      restrictedBurnsideBound := fun d =>
        restricted_burnside_two
          d }

/-- A packaged finite restricted-Burnside theorem controls every finite quotient image of a
group presented with one explicit finite generating tuple. -/
lemma finiteCardinalityBound
    {G : Type u} [Group G]
    {m : ℕ}
    (R : BCInput.{u} m)
    (T : DGTuple G)
    (hexp : ∀ x : G, x ^ m = 1) :
    DCBound G (R.bound T.size) := by
  exact
    DCBound.restricted_burnside_bound
      T
      hexp
      (R.restrictedBurnsideBound T.size)

/-- A packaged finite restricted-Burnside theorem gives some uniform finite-quotient bound for
every finitely generated group of the selected exponent. -/
lemma cardinality_bound_fg
    {G : Type u} [Group G]
    {m : ℕ}
    (R : BCInput.{u} m)
    (hfg : Group.FG G)
    (hexp : ∀ x : G, x ^ m = 1) :
    ∃ B : ℕ,
      DCBound G B := by
  let T :
      DGTuple G :=
    DGTuple.of_groupFG
      G
      hfg
  exact
    ⟨R.bound T.size,
      R.finiteCardinalityBound
        T
        hexp⟩

end BCInput

/-- A copy of `Fin n` used for bounded finite quotient models without inheriting the cyclic group
structure carried by `Fin n`. -/
def DGCarrie
    (n : ℕ) :=
  Fin n

namespace DGCarrie

instance (n : ℕ) :
    Finite (DGCarrie n) := by
  exact
    Finite.of_equiv
      (Fin n)
      (Equiv.refl _)

/-- On a fixed finite carrier there are only finitely many group structures: a group structure is
determined by its multiplication table. -/
instance instFiniteGroup
    (n : ℕ) :
    Finite
      (Group
        (DGCarrie n)) := by
  exact
    Finite.of_injective
      (fun group :
          Group
            (DGCarrie n) =>
        group.mul)
      (by
        intro group₁ group₂ hmul
        exact
          Group.ext
            hmul)

def equivFin
    (n : ℕ) :
    DGCarrie n ≃
      Fin n :=
  Equiv.refl _

end DGCarrie

/-- One normalized bounded finite quotient model: a small carrier, an arbitrary group structure on
it, and the images of a fixed finite generating tuple. -/
structure DBModel
    (B d : ℕ) where
  card : Fin (B + 1)
  group :
    Group
      (DGCarrie card)
  tuple :
    Fin d →
      DGCarrie card

namespace DBModel

def Carrier
    {B d : ℕ}
    (M : DBModel B d) :=
  DGCarrie M.card

instance instGroupCarrier
    {B d : ℕ}
    (M : DBModel B d) :
    Group M.Carrier :=
  M.group

instance instFiniteCarrier
    {B d : ℕ}
    (M : DBModel B d) :
    Finite M.Carrier := by
  dsimp [Carrier]
  infer_instance

instance instFiniteModel
    (B d : ℕ) :
    Finite (DBModel B d) := by
  let encode :
      DBModel B d →
        Σ n : Fin (B + 1),
          Group (DGCarrie n) ×
            (Fin d →
              DGCarrie n) :=
    fun M =>
      ⟨M.card,
        M.group,
        M.tuple⟩
  exact
    Finite.of_injective
      encode
      (by
        intro M N hMN
        cases M
        cases N
        cases hMN
        rfl)

/-- A normalized model is realized if its displayed tuple is the image of the chosen generators
under some homomorphism. -/
def Realizes
    {G : Type u} [Group G]
    {B : ℕ}
    (T : DGTuple G)
    (M : DBModel B T.size) :
    Prop :=
  ∃ φ : G →* M.Carrier,
    ∀ i : Fin T.size,
      φ (T.tuple i) =
        M.tuple i

/-- The realizing homomorphism of a normalized model, using the trivial homomorphism for models
whose displayed tuple does not occur as an image of the chosen generators. -/
noncomputable def hom
    {G : Type u} [Group G]
    {B : ℕ}
    (T : DGTuple G)
    (M : DBModel B T.size) :
    G →* M.Carrier := by
  by_cases hM :
      M.Realizes T
  · exact
      Classical.choose hM
  · exact
      1

/-- On a realized model, the selected homomorphism has the displayed generator values. -/
lemma hom_tuple
    {G : Type u} [Group G]
    {B : ℕ}
    (T : DGTuple G)
    (M : DBModel B T.size)
    (hM : M.Realizes T)
    (i : Fin T.size) :
    M.hom T (T.tuple i) =
      M.tuple i := by
  rw [hom]
  simp only [dif_pos hM]
  exact
    Classical.choose_spec hM i

/-- Any realizing homomorphism is the selected homomorphism, because the source tuple generates. -/
lemma hom_realizes
    {G : Type u} [Group G]
    {B : ℕ}
    (T : DGTuple G)
    (M : DBModel B T.size)
    (φ : G →* M.Carrier)
    (hφ :
      ∀ i : Fin T.size,
        φ (T.tuple i) =
          M.tuple i) :
    M.hom T =
      φ := by
  apply
    DGTuple.monoidHom_ext
      (Q := M.Carrier)
      T
      (φ := M.hom T)
      (ψ := φ)
  intro i
  rw [M.hom_tuple T ⟨φ, hφ⟩]
  exact
    (hφ i).symm

end DBModel

/-- A finitely generated group with separating finite quotients is finite once its finite
quotient images have uniformly bounded cardinality.

This is a general residual-finiteness extraction lemma.  It contains no exponent hypothesis and
no restricted-Burnside theorem: those are used separately above to produce the cardinality
bound. -/
lemma fg_separating_quotients
    (G : Type u) [Group G]
    (hsep : SFQuotie G)
    (hfg : Group.FG G)
    (hbound :
      ∃ B : ℕ,
        DCBound G B) :
    Finite G := by
  rcases hbound with
    ⟨B, hB⟩
  let T :
      DGTuple G :=
    DGTuple.of_groupFG
      G
      hfg
  let K : Subgroup G :=
    ⨅ M : DBModel B T.size,
      (M.hom T).ker
  haveI hKfiniteIndex :
      K.FiniteIndex := by
    dsimp [K]
    apply Subgroup.finiteIndex_iInf
    intro M
    infer_instance
  have hKbot :
      K =
        ⊥ := by
    apply le_antisymm
    · intro g hgK
      by_contra hg
      rcases hsep hg with
        ⟨F, instGroupF, instFiniteF, φ, hφg⟩
      letI : Group F :=
        instGroupF
      letI : Finite F :=
        instFiniteF
      let ψRange :
          G →* φ.range :=
        φ.rangeRestrict
      have hψRangeSurjective :
          Function.Surjective ψRange :=
        φ.rangeRestrict_surjective
      letI : Finite φ.range := by
        infer_instance
      letI : Fintype φ.range :=
        Fintype.ofFinite
          φ.range
      have hcard :
          Nat.card φ.range ≤
            B := by
        exact
          hB
            φ.range
            ψRange
            hψRangeSurjective
      let e :
          φ.range ≃
            DGCarrie
              (Nat.card φ.range) :=
        (Finite.equivFin φ.range).trans
          (DGCarrie.equivFin _).symm
      letI groupCarrier :
          Group
            (DGCarrie
              (Nat.card φ.range)) :=
        e.symm.group
      let eMul :
          φ.range ≃*
            DGCarrie
              (Nat.card φ.range) := by
        exact
          { toEquiv := e
            map_mul' := by
              intro x y
              change
                e (x * y) =
                  e (e.symm (e x) * e.symm (e y))
              simp }
      let ψ :
          G →*
            DGCarrie
              (Nat.card φ.range) :=
        eMul.toMonoidHom.comp
          ψRange
      let M :
          DBModel B T.size :=
        { card :=
            ⟨Nat.card φ.range,
              Nat.lt_succ_of_le hcard⟩
          group := groupCarrier
          tuple := fun i =>
            ψ (T.tuple i) }
      have hMrealizes :
          M.Realizes T := by
        exact
          ⟨ψ,
            fun _i =>
              rfl⟩
      have hgker :
          g ∈ (M.hom T).ker := by
        exact
          Subgroup.mem_iInf.mp hgK M
      have hhom :
          M.hom T =
            ψ := by
        exact
          M.hom_realizes
            T
            ψ
            (fun _i =>
              rfl)
      have hψg :
          ψ g ≠
            1 := by
        intro hψg
        apply hφg
        have hψRange :
            ψRange g =
              1 := by
          apply eMul.injective
          simpa [ψ] using hψg
        exact
          congrArg
            Subtype.val
            hψRange
      apply hψg
      change ψ g = 1
      rw [← hhom]
      exact
        hgker
    · exact
        bot_le
  letI :
      (⊥ : Subgroup G).FiniteIndex := by
    rw [← hKbot]
    infer_instance
  exact
    (Subgroup.finite_iff_finite_and_finiteIndex
      (⊥ : Subgroup G)).mpr
      ⟨inferInstance,
        inferInstance⟩

namespace BCInput

/-- The finite abstract cardinality package implies the weak separating-finite-quotients
Burnside statement consumed by the profinite power-subgroup argument. -/
lemma to_statement
    {m : ℕ}
    (R : BCInput.{u} m) :
    SQBurnsi.{u} m := by
  intro G _instGroupG hsep hfg hexp
  exact
    fg_separating_quotients
      G
      hsep
      hfg
      (R.cardinality_bound_fg
        hfg
        hexp)

/-- The finite abstract cardinality package gives the repository's fixed-exponent Burnside input
wrapper. -/
def fixedInput
    {m : ℕ}
    (R : BCInput.{u} m) :
    DBInput.{u} m := by
  exact
    DBInput.of_statement
      R.to_statement

end BCInput

/-- Restricted-Burnside bounds for groups with at least two named generators.

The zero-generator and one-generator cases are elementary and already proved in
`RestrictedBurnside.lean`.  Keeping only the higher-generator family in this package separates
those easy edges from the finite-group theorem that remains genuinely deep. -/
structure RBInput
    (m : ℕ) :
    Type (u + 1) where
  bound : ℕ → ℕ
  restrictedBurnsideBound :
    ∀ d : ℕ,
      2 ≤ d →
        RBBound.{u} d m (bound d)

namespace RBInput

/-- Package existential bounds for every generator count at least two. -/
noncomputable def of_exists
    {m : ℕ}
    (hRBT :
      ∀ d : ℕ,
        2 ≤ d →
          ∃ B : ℕ,
            RBBound.{u} d m B) :
    RBInput.{u} m := by
  classical
  exact
    { bound := fun d =>
        if hd : 2 ≤ d then
          Classical.choose (hRBT d hd)
        else
          1
      restrictedBurnsideBound := by
        intro d hd
        simpa [hd] using
          (Classical.choose_spec
            (hRBT d hd)) }

/-- Nonemptiness of the higher-generator package is equivalent to separate existential bounds
for every generator count at least two. -/
lemma nonempty_iff_exists
    {m : ℕ} :
    Nonempty (RBInput.{u} m) ↔
      ∀ d : ℕ,
        2 ≤ d →
          ∃ B : ℕ,
            RBBound.{u} d m B := by
  constructor
  · rintro ⟨H⟩ d hd
    exact
      ⟨H.bound d,
        H.restrictedBurnsideBound d hd⟩
  · intro hRBT
    exact
      ⟨of_exists hRBT⟩

/-- Apply a packaged higher-generator theorem at one selected generator count. -/
lemma bound_of_le
    {m d : ℕ}
    (H : RBInput.{u} m)
    (hd : 2 ≤ d) :
    RBBound.{u} d m (H.bound d) := by
  exact
    H.restrictedBurnsideBound
      d
      hd

/-- A packaged higher-generator theorem provides an existential bound at one selected generator
count. -/
lemma bound_two
    {m d : ℕ}
    (H : RBInput.{u} m)
    (hd : 2 ≤ d) :
    ∃ B : ℕ,
      RBBound.{u} d m B := by
  exact
    ⟨H.bound d,
      H.bound_of_le hd⟩

/-- A full restricted-Burnside cardinality package restricts to the higher-generator family. -/
def of_cardinalityInput
    {m : ℕ}
    (R : BCInput.{u} m) :
    RBInput.{u} m := by
  exact
    { bound := R.bound
      restrictedBurnsideBound := fun d _hd =>
        R.restrictedBurnsideBound d }

/-- A higher-generator package for a larger exponent restricts to every divisor exponent. -/
def of_dvd
    {mSmall mBig : ℕ}
    (hdiv : mSmall ∣ mBig)
    (H : RBInput.{u} mBig) :
    RBInput.{u} mSmall := by
  exact
    { bound := H.bound
      restrictedBurnsideBound := fun d hd =>
        RBBound.of_dvd_exponent
          hdiv
          (H.restrictedBurnsideBound d hd) }

end RBInput

/-- Restricted-Burnside cardinality bounds split by generator count.

The first two fields record the elementary edge cases.  The last field records only groups with
at least two named generators.  This package is useful as an explicit assembly layer between the
deep higher-generator theorem and the all-generator-count interface consumed downstream. -/
structure BSInput
    (m : ℕ) :
    Type (u + 1) where
  zeroGeneratorBound : ℕ
  oneGeneratorBound : ℕ
  higherGeneratorBound : ℕ → ℕ
  restricted_burnside_zero :
    RBBound.{u} 0 m zeroGeneratorBound
  burnside_bound_one :
    RBBound.{u} 1 m oneGeneratorBound
  restricted_burnside_higher :
    ∀ d : ℕ,
      2 ≤ d →
        RBBound.{u} d m (higherGeneratorBound d)

namespace BSInput

/-- The piecewise cardinality bound assembled from the three generator-count branches. -/
def bound
    {m : ℕ}
    (S : BSInput.{u} m)
    (d : ℕ) :
    ℕ :=
  if d = 0 then
    S.zeroGeneratorBound
  else if d = 1 then
    S.oneGeneratorBound
  else
    S.higherGeneratorBound d

/-- The split package proves an unrestricted finite restricted-Burnside bound at every generator
count. -/
lemma restrictedBurnsideBound
    {m : ℕ}
    (S : BSInput.{u} m)
    (d : ℕ) :
    RBBound.{u} d m (S.bound d) := by
  by_cases hd0 : d = 0
  · subst d
    simpa [bound] using
      S.restricted_burnside_zero
  · by_cases hd1 : d = 1
    · subst d
      simpa [bound] using
        S.burnside_bound_one
    · have hd2 :
          2 ≤ d := by
        omega
      simpa [bound, hd0, hd1] using
        S.restricted_burnside_higher
          d
          hd2

/-- Assemble the downstream all-generator-count cardinality package from a generator split. -/
def toCardinalityInput
    {m : ℕ}
    (S : BSInput.{u} m) :
    BCInput.{u} m := by
  exact
    { bound := S.bound
      restrictedBurnsideBound :=
        S.restrictedBurnsideBound }

/-- The assembled cardinality package uses the zero-generator branch at generator count zero. -/
@[simp] lemma bound_zero
    {m : ℕ}
    (S : BSInput.{u} m) :
    S.bound 0 =
      S.zeroGeneratorBound := by
  simp [bound]

/-- The assembled cardinality package uses the one-generator branch at generator count one. -/
@[simp] lemma bound_one
    {m : ℕ}
    (S : BSInput.{u} m) :
    S.bound 1 =
      S.oneGeneratorBound := by
  simp [bound]

/-- The assembled cardinality package uses the higher-generator branch from generator count two
onward. -/
lemma bound_of_le
    {m d : ℕ}
    (S : BSInput.{u} m)
    (hd : 2 ≤ d) :
    S.bound d =
      S.higherGeneratorBound d := by
  have hd0 :
      d ≠ 0 := by
    omega
  have hd1 :
      d ≠ 1 := by
    omega
  simp [bound, hd0, hd1]

/-- Build the generator split from a higher-generator package and explicit bounds for the two
elementary edge cases. -/
def higher_generator_input
    {m : ℕ}
    (H : RBInput.{u} m)
    {zeroGeneratorBound oneGeneratorBound : ℕ}
    (hzero :
      RBBound.{u} 0 m zeroGeneratorBound)
    (hone :
      RBBound.{u} 1 m oneGeneratorBound) :
    BSInput.{u} m := by
  exact
    { zeroGeneratorBound := zeroGeneratorBound
      oneGeneratorBound := oneGeneratorBound
      higherGeneratorBound := H.bound
      restricted_burnside_zero := hzero
      burnside_bound_one := hone
      restricted_burnside_higher := fun d hd =>
        H.restrictedBurnsideBound d hd }

/-- At a positive exponent, the known zero-generator and one-generator theorems fill the edge
branches around any higher-generator package. -/
def higher_input_pos
    {m : ℕ}
    (hm : 0 < m)
    (H : RBInput.{u} m) :
    BSInput.{u} m := by
  exact
    higher_generator_input
      H
      (restricted_burnside_generators
        m)
      (restricted_burnside_pos
        hm)

/-- A higher-generator package at positive exponent yields the complete cardinality package. -/
def cardinality_input_pos
    {m : ℕ}
    (hm : 0 < m)
    (H : RBInput.{u} m) :
    BCInput.{u} m := by
  exact
    (higher_input_pos
      hm
      H).toCardinalityInput

/-- A full cardinality package can always be viewed as an explicit generator split. -/
def of_cardinalityInput
    {m : ℕ}
    (R : BCInput.{u} m) :
    BSInput.{u} m := by
  exact
    { zeroGeneratorBound :=
        R.bound 0
      oneGeneratorBound :=
        R.bound 1
      higherGeneratorBound :=
        R.bound
      restricted_burnside_zero :=
        R.restrictedBurnsideBound 0
      burnside_bound_one :=
        R.restrictedBurnsideBound 1
      restricted_burnside_higher := fun d _hd =>
        R.restrictedBurnsideBound d }

/-- A generator split for a larger exponent restricts branchwise to every divisor exponent. -/
def of_dvd
    {mSmall mBig : ℕ}
    (hdiv : mSmall ∣ mBig)
    (S : BSInput.{u} mBig) :
    BSInput.{u} mSmall := by
  exact
    { zeroGeneratorBound :=
        S.zeroGeneratorBound
      oneGeneratorBound :=
        S.oneGeneratorBound
      higherGeneratorBound :=
        S.higherGeneratorBound
      restricted_burnside_zero :=
        RBBound.of_dvd_exponent
          hdiv
          S.restricted_burnside_zero
      burnside_bound_one :=
        RBBound.of_dvd_exponent
          hdiv
          S.burnside_bound_one
      restricted_burnside_higher := fun d hd =>
        RBBound.of_dvd_exponent
          hdiv
          (S.restricted_burnside_higher d hd) }

end BSInput

/-- Under density, the requested controlled-shadow statement is equivalent to abstract generation
of the self-quotient by the dense tuple images.

This records the exact mathematical content of the target: a shadow is not a shortcut around the
finite-width theorem. -/
lemma control_abstract_generation
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    {d : ℕ} (s : Fin d → Γ)
    (hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤)
    {n : ℕ} :
    (∃ C : GCShadow
        (p := p) (Γ := Γ) s n,
      (let S := C.continuousFinShadow
      letI : Group S.quotientGroup := S.instGroup
      S.quotientMap.ker ≤
        Subgroup.closure
          (Set.range
            (fun i : Fin d =>
              denseGeneratorsSelf p Γ n (s i))))) ↔
      Subgroup.closure
          (Set.range
            (fun i : Fin d =>
              denseGeneratorsSelf p Γ n (s i))) =
        (⊤ : Subgroup (denseSelfQuotient p Γ n)) := by
  constructor
  · rintro ⟨C, hkernel⟩
    exact
      gens_shadow_control
        (p := p) (Γ := Γ) (s := s) (n := n) C hs hkernel
  · intro hgen
    exact
      gens_control_generation
        (p := p) (Γ := Γ) s
        ⟨by
          simpa [denseSelfTuple] using hgen⟩

/-- Closed generator-image data is exactly enough to turn topological density of the image into
abstract generation of the self-quotient. -/
lemma self_top_closed
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    {d : ℕ} {s : Fin d → Γ}
    {n : ℕ}
    (C : SCImage
      (p := p) (Γ := Γ) s n)
    (hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤) :
    Subgroup.closure
        (Set.range
          (fun i : Fin d =>
            denseGeneratorsSelf p Γ n (s i))) =
      (⊤ : Subgroup (denseSelfQuotient p Γ n)) := by
  exact
    SCImage.image_closed_dense
      (p := p) (Γ := Γ) (s := s) (n := n) C
      (by
        simpa using
          dense_self_quotient
            (p := p) (Γ := Γ) s hs (n := n))

namespace SCShadow

/-- Adding the truncated Fox kernel calculation turns a finite shadow into the algebraic
finite-kernel model. -/
def algebraicKernelModel
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {n : ℕ}
    (S : SCShadow
      (p := p) (Γ := Γ) s n)
    (K : SFContro
      (p := p) (Γ := Γ) S) :
    GAModel
      (p := p) (Γ := Γ) s n := by
  classical
  letI : Group S.quotientGroup := S.instGroup
  letI : Finite S.quotientGroup := S.instFinite
  refine
    { quotientGroup := S.quotientGroup
      instGroup := inferInstance
      instFinite := inferInstance
      quotientMap := S.quotientMap
      kernel_generator_image := ?_ }
  exact K.kernel_generator_image

end SCShadow

/-- A Step 5 finite kernel shadow together with the topology on its finite target.

This is the honest package supplied by the truncated Fox/Jennings construction: an algebraic
finite quotient whose kernel is contained in the subgroup generated by the dense tuple, plus the
discrete target topology and continuity of the actual shadow map.  Continuity is not automatic for
an arbitrary finite abstract quotient, so it is part of the constructed Step 5 object rather than
a property later asserted for every algebraic shadow. -/
structure DSShadow
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ]
    {d : ℕ} (s : Fin d → Γ)
    (n : ℕ) :
    Type (u + 1) where
  algebraic :
    GAModel
      (p := p) (Γ := Γ) s n
  quotientTopologicalSpace : TopologicalSpace algebraic.quotientGroup
  quotientDiscreteTopology : @DiscreteTopology algebraic.quotientGroup quotientTopologicalSpace
  quotientMap_continuous :
    letI : Group algebraic.quotientGroup := algebraic.instGroup
    letI : TopologicalSpace algebraic.quotientGroup := quotientTopologicalSpace
    Continuous
      (fun x : denseSelfQuotient p Γ n =>
        algebraic.quotientMap x)
  kernel_map_continuous :
    letI : Group algebraic.quotientGroup := algebraic.instGroup
    letI : algebraic.quotientMap.ker.Normal := inferInstance
    letI : TopologicalSpace
      (denseSelfQuotient p Γ n ⧸ algebraic.quotientMap.ker) := ⊥
    Continuous
      (fun x : denseSelfQuotient p Γ n =>
        (QuotientGroup.mk' algebraic.quotientMap.ker) x)


namespace SCShadow

/-- Adding the truncated Fox kernel calculation turns a finite shadow into the full continuous
finite-kernel package used downstream. -/
def continuousKernelShadow
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {n : ℕ}
    (S : SCShadow
      (p := p) (Γ := Γ) s n)
    (K : SFContro
      (p := p) (Γ := Γ) S) :
    DSShadow
      (p := p) (Γ := Γ) s n := by
  classical
  let A :
      GAModel
        (p := p) (Γ := Γ) s n :=
    S.algebraicKernelModel (p := p) (Γ := Γ) K
  refine
    { algebraic := A
      quotientTopologicalSpace := S.instTopologicalSpace
      quotientDiscreteTopology := S.instDiscreteTopology
      quotientMap_continuous := ?_
      kernel_map_continuous := ?_ }
  · simpa [A, algebraicKernelModel] using S.quotientMap_continuous
  · simpa [A, algebraicKernelModel] using S.kernel_map_continuous

end SCShadow

/-- Continuity of the finite shadow map itself.

This is the first half of the topology attached to an algebraic finite kernel shadow: equip the
finite target with a discrete topology and prove that the chosen map out of the self-quotient is
continuous. -/
structure DenseContinuityData
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {n : ℕ}
    (A : GAModel
      (p := p) (Γ := Γ) s n) :
    Type (u + 1) where
  quotientTopologicalSpace : TopologicalSpace A.quotientGroup
  quotientDiscreteTopology : @DiscreteTopology A.quotientGroup quotientTopologicalSpace
  quotientMap_continuous :
    letI : Group A.quotientGroup := A.instGroup
    letI : TopologicalSpace A.quotientGroup := quotientTopologicalSpace
    Continuous
      (fun x : denseSelfQuotient p Γ n =>
        A.quotientMap x)

/-- Continuity of the canonical quotient by the finite shadow kernel.

This is the second half of the topology attached to an algebraic finite kernel shadow.  It is
separate from continuity of the target-valued shadow map because the later open-normal-core
construction needs the quotient by the kernel itself as a finite discrete model. -/
structure
  SelfContinuityData
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {n : ℕ}
    (A : GAModel
      (p := p) (Γ := Γ) s n) :
    Type (u + 1) where
  kernel_map_continuous :
    letI : Group A.quotientGroup := A.instGroup
    letI : A.quotientMap.ker.Normal := inferInstance
    letI : TopologicalSpace
      (denseSelfQuotient p Γ n ⧸ A.quotientMap.ker) := ⊥
    Continuous
      (fun x : denseSelfQuotient p Γ n =>
        (QuotientGroup.mk' A.quotientMap.ker) x)

/-- Continuity data for an algebraic finite kernel shadow.

This is the topological part separated from the algebraic finite quotient.  The target is equipped
with the discrete topology, the chosen finite quotient map is required to be continuous, and the
canonical quotient map by its kernel is also recorded as continuous for the discrete quotient
topology. -/
structure DenseSelfContinuity
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {n : ℕ}
    (A : GAModel
      (p := p) (Γ := Γ) s n) :
    Type (u + 1) where
  quotientTopologicalSpace : TopologicalSpace A.quotientGroup
  quotientDiscreteTopology : @DiscreteTopology A.quotientGroup quotientTopologicalSpace
  quotientMap_continuous :
    letI : Group A.quotientGroup := A.instGroup
    letI : TopologicalSpace A.quotientGroup := quotientTopologicalSpace
    Continuous
      (fun x : denseSelfQuotient p Γ n =>
        A.quotientMap x)
  kernel_map_continuous :
    letI : Group A.quotientGroup := A.instGroup
    letI : A.quotientMap.ker.Normal := inferInstance
    letI : TopologicalSpace
      (denseSelfQuotient p Γ n ⧸ A.quotientMap.ker) := ⊥
    Continuous
      (fun x : denseSelfQuotient p Γ n =>
        (QuotientGroup.mk' A.quotientMap.ker) x)


namespace GAModel

/-- Combine the two continuity halves for an algebraic finite kernel shadow. -/
def continuity_of_parts
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {n : ℕ}
    (A : GAModel
      (p := p) (Γ := Γ) s n)
    (Q : DenseContinuityData
      (p := p) (Γ := Γ) A)
    (K : SelfContinuityData
      (p := p) (Γ := Γ) A) :
    DenseSelfContinuity
      (p := p) (Γ := Γ) A := by
  classical
  refine
    { quotientTopologicalSpace := Q.quotientTopologicalSpace
      quotientDiscreteTopology := Q.quotientDiscreteTopology
      quotientMap_continuous := ?_
      kernel_map_continuous := ?_ }
  · simpa using Q.quotientMap_continuous
  · simpa using K.kernel_map_continuous

end GAModel

namespace DSShadow

/-- Forget the target topology and keep only the algebraic finite-kernel shadow. -/
def algebraicKernelModel
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {n : ℕ}
    (S : DSShadow
      (p := p) (Γ := Γ) s n) :
    GAModel
      (p := p) (Γ := Γ) s n :=
  S.algebraic

/-- The target-valued continuity half carried by a continuous finite-kernel shadow. -/
def quotientContinuityData
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {n : ℕ}
    (S : DSShadow
      (p := p) (Γ := Γ) s n) :
    DenseContinuityData
      (p := p) (Γ := Γ) S.algebraic := by
  classical
  refine
    { quotientTopologicalSpace := S.quotientTopologicalSpace
      quotientDiscreteTopology := S.quotientDiscreteTopology
      quotientMap_continuous := ?_ }
  simpa using S.quotientMap_continuous

/-- The kernel-quotient continuity half carried by a continuous finite-kernel shadow. -/
def kernelContinuityData
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {n : ℕ}
    (S : DSShadow
      (p := p) (Γ := Γ) s n) :
    SelfContinuityData
      (p := p) (Γ := Γ) S.algebraic := by
  classical
  refine
    { kernel_map_continuous := ?_ }
  simpa using S.kernel_map_continuous

/-- A continuous finite-kernel shadow supplies all continuity data needed downstream. -/
def continuityData
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {n : ℕ}
    (S : DSShadow
      (p := p) (Γ := Γ) s n) :
    DenseSelfContinuity
      (p := p) (Γ := Γ) S.algebraic := by
  classical
  exact
    GAModel.continuity_of_parts
      (p := p) (Γ := Γ) S.algebraic
      S.quotientContinuityData
      S.kernelContinuityData

end DSShadow

/-- A finite continuous kernel model for the generator-image subgroup.

This is one step more concrete than an open normal core.  It records a homomorphism from the
self-quotient to a finite discrete group whose kernel lies in the subgroup generated by the image
of the dense tuple.  The kernel is automa normal, open, and finite-index; the only
additional topological field retained is continuity of the canonical quotient map by that kernel,
because the self-quotient topology is not packaged here as a topological group. -/
structure DSModel
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ]
    {d : ℕ} (s : Fin d → Γ)
    (n : ℕ) :
    Type (u + 1) where
  quotientGroup : Type u
  [instGroup : Group quotientGroup]
  [instTopologicalSpace : TopologicalSpace quotientGroup]
  [instDiscreteTopology : DiscreteTopology quotientGroup]
  [instFinite : Finite quotientGroup]
  quotientMap :
    denseSelfQuotient p Γ n →* quotientGroup
  quotientMap_continuous :
    Continuous
      (fun x : denseSelfQuotient p Γ n =>
        quotientMap x)
  kernel_generator_image :
    quotientMap.ker ≤
      Subgroup.closure
        (Set.range
          (fun i : Fin d =>
            denseGeneratorsSelf p Γ n (s i)))
  kernel_map_continuous :
    letI : quotientMap.ker.Normal := inferInstance
    letI : TopologicalSpace
      (denseSelfQuotient p Γ n ⧸ quotientMap.ker) := ⊥
    Continuous
      (fun x : denseSelfQuotient p Γ n =>
        (QuotientGroup.mk' quotientMap.ker) x)


namespace DSModel

/-- The kernel of the finite model map is open, by continuity and discreteness of the target. -/
lemma kernel_isOpen
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {n : ℕ}
    (M : DSModel
      (p := p) (Γ := Γ) s n) :
    letI : Group M.quotientGroup := M.instGroup
    IsOpen
      ((M.quotientMap.ker :
        Subgroup (denseSelfQuotient p Γ n)) :
        Set (denseSelfQuotient p Γ n)) := by
  classical
  letI : Group M.quotientGroup := M.instGroup
  letI : TopologicalSpace M.quotientGroup := M.instTopologicalSpace
  letI : DiscreteTopology M.quotientGroup := M.instDiscreteTopology
  have hone : IsOpen ({1} : Set M.quotientGroup) := by
    exact isOpen_discrete _
  have hpre :
      IsOpen
        ((fun x : denseSelfQuotient p Γ n =>
            M.quotientMap x) ⁻¹' ({1} : Set M.quotientGroup)) := by
    exact hone.preimage M.quotientMap_continuous
  have hpre_eq :
      ((fun x : denseSelfQuotient p Γ n =>
          M.quotientMap x) ⁻¹' ({1} : Set M.quotientGroup)) =
        ((M.quotientMap.ker :
          Subgroup (denseSelfQuotient p Γ n)) :
          Set (denseSelfQuotient p Γ n)) := by
    ext x
    change M.quotientMap x = 1 ↔ x ∈ M.quotientMap.ker
    rfl
  simpa [hpre_eq] using hpre

/-- The kernel has finite index because its quotient is equivalent to the finite range. -/
lemma kernel_finiteIndex
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {n : ℕ}
    (M : DSModel
      (p := p) (Γ := Γ) s n) :
    letI : Group M.quotientGroup := M.instGroup
    (M.quotientMap.ker :
      Subgroup (denseSelfQuotient p Γ n)).FiniteIndex := by
  classical
  letI : Group M.quotientGroup := M.instGroup
  letI : Finite M.quotientGroup := M.instFinite
  have hfinite_quotient :
      Finite
        (denseSelfQuotient p Γ n ⧸
          (M.quotientMap.ker :
            Subgroup (denseSelfQuotient p Γ n))) := by
    exact
      Finite.of_equiv M.quotientMap.range
        (QuotientGroup.quotientKerEquivRange M.quotientMap).symm
  letI :
      Finite
        (denseSelfQuotient p Γ n ⧸
          (M.quotientMap.ker :
            Subgroup (denseSelfQuotient p Γ n))) :=
    hfinite_quotient
  exact Subgroup.finiteIndex_of_finite_quotient

/-- A finite continuous kernel model supplies the open normal core. -/
def openNormalCore
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {n : ℕ}
    (M : DSModel
      (p := p) (Γ := Γ) s n) :
    DSCore
      (p := p) (Γ := Γ) s n := by
  classical
  letI : Group M.quotientGroup := M.instGroup
  refine
    { normalCore := M.quotientMap.ker
      normalCore_normal := inferInstance
      normal_core_image := M.kernel_generator_image
      normal_core_index := M.kernel_finiteIndex
      normal_core_open := M.kernel_isOpen
      normal_core_continuous := ?_ }
  simpa using M.kernel_map_continuous

end DSModel

namespace GAModel

/-- Algebraic finite kernel data plus continuity data give the finite-kernel model. -/
def finiteKernelModel
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {n : ℕ}
    (A : GAModel
      (p := p) (Γ := Γ) s n)
    (C : DenseSelfContinuity
      (p := p) (Γ := Γ) A) :
    DSModel
      (p := p) (Γ := Γ) s n := by
  classical
  letI : Group A.quotientGroup := A.instGroup
  letI : TopologicalSpace A.quotientGroup := C.quotientTopologicalSpace
  letI : DiscreteTopology A.quotientGroup := C.quotientDiscreteTopology
  letI : Finite A.quotientGroup := A.instFinite
  refine
    { quotientGroup := A.quotientGroup
      instGroup := inferInstance
      instTopologicalSpace := inferInstance
      instDiscreteTopology := inferInstance
      instFinite := inferInstance
      quotientMap := A.quotientMap
      quotientMap_continuous := ?_
      kernel_generator_image := A.kernel_generator_image
      kernel_map_continuous := ?_ }
  · simpa using C.quotientMap_continuous
  · simpa using C.kernel_map_continuous

end GAModel

/-- A finite discrete model whose pullback cuts out the generator-image subgroup.

This is a more concrete version of the Step 5 finite-width input from `T.tex`.  Instead of
asserting directly that the generator-image subgroup in `Γ / D_n(Γ)` is closed, it records a
finite discrete quotient of that self-quotient and a subgroup downstairs whose comap is exactly
the generator-image subgroup.  Closedness is then a formal topological consequence. -/
structure DGModel
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ]
    {d : ℕ} (s : Fin d → Γ)
    (n : ℕ) :
    Type (u + 1) where
  quotientGroup : Type u
  [instGroup : Group quotientGroup]
  [instTopologicalSpace : TopologicalSpace quotientGroup]
  [instDiscreteTopology : DiscreteTopology quotientGroup]
  [instFinite : Finite quotientGroup]
  quotientMap :
    denseSelfQuotient p Γ n →* quotientGroup
  quotientMap_continuous :
    Continuous
      (fun x : denseSelfQuotient p Γ n =>
        quotientMap x)
  targetSubgroup : Subgroup quotientGroup
  generator_comap :
    Subgroup.closure
        (Set.range
          (fun i : Fin d =>
            denseGeneratorsSelf p Γ n (s i))) =
      Subgroup.comap quotientMap targetSubgroup


namespace DGModel

/-- The finite model target subgroup is closed because the target is discrete. -/
lemma target_closed
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {n : ℕ}
    (M : DGModel
      (p := p) (Γ := Γ) s n) :
    letI : TopologicalSpace M.quotientGroup := M.instTopologicalSpace
    IsClosed (M.targetSubgroup : Set M.quotientGroup) := by
  classical
  letI : Group M.quotientGroup := M.instGroup
  letI : TopologicalSpace M.quotientGroup := M.instTopologicalSpace
  letI : DiscreteTopology M.quotientGroup := M.instDiscreteTopology
  have hclosed :
      IsClosed (M.targetSubgroup : Set M.quotientGroup) := by
    exact isClosed_discrete _
  exact hclosed

/-- The comap of the finite target subgroup is closed in the self-quotient. -/
lemma target_subgroup_closed
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {n : ℕ}
    (M : DGModel
      (p := p) (Γ := Γ) s n) :
    letI : Group M.quotientGroup := M.instGroup
    IsClosed
      (((Subgroup.comap M.quotientMap M.targetSubgroup) :
        Subgroup (denseSelfQuotient p Γ n)) :
        Set (denseSelfQuotient p Γ n)) := by
  classical
  letI : Group M.quotientGroup := M.instGroup
  letI : TopologicalSpace M.quotientGroup := M.instTopologicalSpace
  letI : DiscreteTopology M.quotientGroup := M.instDiscreteTopology
  let L : Subgroup M.quotientGroup := M.targetSubgroup
  have hL_closed : IsClosed (L : Set M.quotientGroup) := by
    change IsClosed (M.targetSubgroup : Set M.quotientGroup)
    exact M.target_closed
  have hpre_closed :
      IsClosed
        ((fun x : denseSelfQuotient p Γ n =>
            M.quotientMap x) ⁻¹' (L : Set M.quotientGroup)) := by
    exact hL_closed.preimage M.quotientMap_continuous
  change
    IsClosed
      ((fun x : denseSelfQuotient p Γ n =>
          M.quotientMap x) ⁻¹' (L : Set M.quotientGroup))
  exact hpre_closed

/-- The finite model makes the generator-image subgroup closed. -/
lemma generator_image_closed
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {n : ℕ}
    (M : DGModel
      (p := p) (Γ := Γ) s n) :
    IsClosed
      (((Subgroup.closure
        (Set.range
          (fun i : Fin d =>
            denseGeneratorsSelf p Γ n (s i)))) :
        Subgroup (denseSelfQuotient p Γ n)) :
        Set (denseSelfQuotient p Γ n)) := by
  classical
  let K : Subgroup (denseSelfQuotient p Γ n) :=
    Subgroup.closure
      (Set.range
        (fun i : Fin d =>
          denseGeneratorsSelf p Γ n (s i)))
  letI : Group M.quotientGroup := M.instGroup
  let L : Subgroup (denseSelfQuotient p Γ n) :=
    Subgroup.comap M.quotientMap M.targetSubgroup
  have hK_eq_L : K = L := by
    simpa [K, L] using M.generator_comap
  have hL_closed : IsClosed (L : Set (denseSelfQuotient p Γ n)) := by
    simpa [L] using M.target_subgroup_closed
  change IsClosed (K : Set (denseSelfQuotient p Γ n))
  simpa [hK_eq_L] using hL_closed

/-- The finite discrete model supplies the closed-generator-image package. -/
def closedGeneratorImage
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {n : ℕ}
    (M : DGModel
      (p := p) (Γ := Γ) s n) :
    SCImage
      (p := p) (Γ := Γ) s n := by
  refine
    { closed_generator_image := ?_ }
  exact M.generator_image_closed

end DGModel

namespace DSCore

/-- An open normal core gives the finite discrete model by quotienting the self-quotient. -/
noncomputable def toFiniteModel
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    {d : ℕ} {s : Fin d → Γ}
    {n : ℕ}
    (C : DSCore
      (p := p) (Γ := Γ) s n) :
    DGModel
      (p := p) (Γ := Γ) s n := by
  classical
  let Ω : Type u := denseSelfQuotient p Γ n
  letI : Group Ω := by
    dsimp [Ω]
    infer_instance
  letI : TopologicalSpace Ω := by
    dsimp [Ω]
    infer_instance
  let K : Subgroup Ω :=
    Subgroup.closure
      (Set.range
        (fun i : Fin d =>
          denseGeneratorsSelf p Γ n (s i)))
  let N : Subgroup Ω := C.normalCore
  letI : N.Normal := C.normalCore_normal
  letI : N.FiniteIndex := C.normal_core_index
  haveI : Finite (Ω ⧸ N) := by
    infer_instance
  letI : TopologicalSpace (Ω ⧸ N) := ⊥
  letI : DiscreteTopology (Ω ⧸ N) := discreteTopology_bot (Ω ⧸ N)
  let q : Ω →* Ω ⧸ N := QuotientGroup.mk' N
  refine
    { quotientGroup := Ω ⧸ N
      instGroup := inferInstance
      instTopologicalSpace := inferInstance
      instDiscreteTopology := inferInstance
      instFinite := inferInstance
      quotientMap := q
      quotientMap_continuous := ?_
      targetSubgroup := Subgroup.map q K
      generator_comap := ?_ }
  · simpa [Ω, N, q] using
      C.quotient_continuous_discrete
  · change K = Subgroup.comap q (Subgroup.map q K)
    ext x
    constructor
    · intro hxK
      exact ⟨x, hxK, rfl⟩
    · intro hx_comap
      rcases hx_comap with ⟨y, hyK, hyq⟩
      have hyx_mem_N : y⁻¹ * x ∈ N := by
        have hyx_eq_one : q (y⁻¹ * x) = 1 := by
          calc
            q (y⁻¹ * x) = (q y)⁻¹ * q x := by
              simp [q]
            _ = (q x)⁻¹ * q x := by
              rw [hyq]
            _ = 1 := by
              simp
        exact (QuotientGroup.eq_one_iff (N := N) (y⁻¹ * x)).mp hyx_eq_one
      have hyx_mem_K : y⁻¹ * x ∈ K := by
        exact C.normal_core_image hyx_mem_N
      have hx_eq : x = y * (y⁻¹ * x) := by
        simp
      rw [hx_eq]
      exact K.mul_mem hyK hyx_mem_K

end DSCore

/-- An open normal core inside the generator-image subgroup gives a finite model, hence closed
generator-image data, and therefore abstract generation. -/
lemma dense_self_core
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    {d : ℕ} {s : Fin d → Γ}
    {n : ℕ}
    (C : DSCore
      (p := p) (Γ := Γ) s n)
    (hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤) :
    Subgroup.closure
        (Set.range
          (fun i : Fin d =>
            denseGeneratorsSelf p Γ n (s i))) =
      (⊤ : Subgroup (denseSelfQuotient p Γ n)) := by
  exact
    self_top_closed
      (p := p) (Γ := Γ) (s := s) (n := n)
      (C.toFiniteModel.closedGeneratorImage)
      hs

/-- A chosen coset representative in the abstract subgroup generated by the dense tuple.

This packages the preceding existential cover into functions.  It still does not mention signed
words; it only chooses an element of `Subgroup.closure (Set.range s)` in each `D_n`-coset. -/
structure DCDecomp
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ]
    {d : ℕ} (s : Fin d → Γ)
    (n : ℕ) :
    Type u where
  representative : Γ → Γ
  representative_mem_closure :
    ∀ g : Γ, representative g ∈ Subgroup.closure (Set.range s)
  quotient_error_mem :
    ∀ g : Γ, (representative g)⁻¹ * g ∈ zassenhausFiltration p Γ n


namespace DCCover

/-- Choose representatives from a dense-subgroup coset cover.

This is just choice: the mathematical content remains the existential cover, while this structure
is easier to feed into the signed-word normal-form conversion. -/
noncomputable def toCosetDecomposition
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ]
    {d : ℕ} {s : Fin d → Γ}
    {n : ℕ}
    (C : DCCover
      (p := p) (Γ := Γ) s n) :
    DCDecomp
      (p := p) (Γ := Γ) s n := by
  classical
  refine
    { representative := fun g =>
        Classical.choose (C.exists_closure_representative g)
      representative_mem_closure := ?_
      quotient_error_mem := ?_ }
  · intro g
    have hspec :
        Classical.choose (C.exists_closure_representative g) ∈
          Subgroup.closure (Set.range s) ∧
        (Classical.choose (C.exists_closure_representative g))⁻¹ * g ∈
          zassenhausFiltration p Γ n :=
      Classical.choose_spec (C.exists_closure_representative g)
    exact hspec.1
  · intro g
    have hspec :
        Classical.choose (C.exists_closure_representative g) ∈
          Subgroup.closure (Set.range s) ∧
        (Classical.choose (C.exists_closure_representative g))⁻¹ * g ∈
          zassenhausFiltration p Γ n :=
      Classical.choose_spec (C.exists_closure_representative g)
    exact hspec.2

end DCCover

namespace DCDecomp

/-- A chosen dense-subgroup representative can be represented by a signed word.

The proof uses the existing `T0.lean` lemma that every element of
`Subgroup.closure (Set.range s)` is represented by a finite signed word in `s`. -/
noncomputable def toCosetFactorization
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ]
    {d : ℕ} {s : Fin d → Γ}
    {n : ℕ}
    (D : DCDecomp
      (p := p) (Γ := Γ) s n) :
    SCFact
      (p := p) (Γ := Γ) s n := by
  classical
  refine
    { wordOf := fun g =>
        Classical.choose
          (dense_element_closure
            s (D.representative_mem_closure g))
      quotient_error_mem := ?_ }
  intro g
  let w : List (denseGeneratorsLetter d) :=
    Classical.choose
      (dense_element_closure
        s (D.representative_mem_closure g))
  have hw :
      denseSignedElement s w =
        D.representative g :=
    Classical.choose_spec
      (dense_element_closure
        s (D.representative_mem_closure g))
  have herror :
      (D.representative g)⁻¹ * g ∈ zassenhausFiltration p Γ n :=
    D.quotient_error_mem g
  simpa [w, hw] using herror

end DCDecomp

/-- The self-quotient has trivial `D_n` as an ordinary Zassenhaus filtration statement. -/
lemma self_filtration_bot
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ]
    (n : ℕ) :
    zassenhausFiltration p (denseSelfQuotient p Γ n) n = ⊥ := by
  have Halg : DenseSelfData p Γ n :=
    denseSelfData (p := p) (Γ := Γ) n
  simpa [denseSelfTarget] using Halg.target_eq_bot

/-- The abstract subgroup generated by the dense tuple images in `Γ / D_n(Γ)` is finite.

This does not yet prove that the subgroup is the whole self-quotient: the remaining topological
input is precisely that this finite generator-image subgroup is closed in the quotient topology. -/
lemma dense_self_image
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ]
    {d : ℕ} (s : Fin d → Γ)
    {n : ℕ}
    (hn : 1 < n) :
    Finite
      (Subgroup.closure
        (Set.range
          (fun i : Fin d =>
            denseGeneratorsSelf p Γ n (s i))) :
        Subgroup (denseSelfQuotient p Γ n)) := by
  let t : Fin d → denseSelfQuotient p Γ n :=
    fun i => denseGeneratorsSelf p Γ n (s i)
  have htrivial :
      zassenhausFiltration p (denseSelfQuotient p Γ n) n = ⊥ :=
    self_filtration_bot
      (p := p) (Γ := Γ) n
  simpa [t] using
    trivial_restricted_burnside
      (p := p)
      (Ω := denseSelfQuotient p Γ n)
      t
      hn
      htrivial

/-- The finite generator-image subgroup accounts for the self-quotient up to the closure of the
identity.

Thus the remaining obstruction to abstract generation is exactly the non-separated part of the
quotient topology, equivalently the possible non-closedness of `D_n(Γ)`. -/
lemma dense_self_univ
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    {d : ℕ} (s : Fin d → Γ)
    (hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤)
    {n : ℕ}
    (hn : 1 < n) :
    let K : Subgroup (denseSelfQuotient p Γ n) :=
      Subgroup.closure
        (Set.range
          (fun i : Fin d =>
            denseGeneratorsSelf p Γ n (s i)))
    ((K : Set (denseSelfQuotient p Γ n)) *
        closure ({1} : Set (denseSelfQuotient p Γ n))) =
      Set.univ := by
  classical
  let Ω : Type u := denseSelfQuotient p Γ n
  letI : (zassenhausFiltration p Γ n).Normal :=
    zassenhausFiltration_normal p Γ n
  haveI : IsTopologicalGroup Ω := by
    dsimp [Ω, denseSelfQuotient]
    exact QuotientGroup.instIsTopologicalGroup
      (N := zassenhausFiltration p Γ n)
  let K : Subgroup Ω :=
    Subgroup.closure
      (Set.range
        (fun i : Fin d =>
          denseGeneratorsSelf p Γ n (s i)))
  haveI : Finite K := by
    simpa [Ω, K] using
      dense_self_image
        (p := p) (Γ := Γ) s hn
  have hcompact : IsCompact (K : Set Ω) :=
    (Set.toFinite (K : Set Ω)).isCompact
  have hdense : closure (K : Set Ω) = Set.univ := by
    simpa [Ω, K] using
      dense_self_quotient
        (p := p) (Γ := Γ) s hs (n := n)
  have hmul :
      (K : Set Ω) * closure ({1} : Set Ω) = closure (K : Set Ω) :=
    hcompact.mul_closure_one_eq_closure
  simpa [Ω, K, hdense] using hmul

/-- If the closure of the identity in the self-quotient already lies in the finite generator-image
subgroup, then the dense tuple images algebraically generate the self-quotient. -/
lemma dense_self_top
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    {d : ℕ} (s : Fin d → Γ)
    (hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤)
    {n : ℕ}
    (hn : 1 < n)
    (hclosure :
      closure ({1} : Set (denseSelfQuotient p Γ n)) ⊆
        (Subgroup.closure
          (Set.range
            (fun i : Fin d =>
              denseGeneratorsSelf p Γ n (s i))) :
          Set (denseSelfQuotient p Γ n))) :
    Subgroup.closure
        (Set.range
          (fun i : Fin d =>
            denseGeneratorsSelf p Γ n (s i))) =
      (⊤ : Subgroup (denseSelfQuotient p Γ n)) := by
  classical
  let Ω : Type u := denseSelfQuotient p Γ n
  let K : Subgroup Ω :=
    Subgroup.closure
      (Set.range
        (fun i : Fin d =>
          denseGeneratorsSelf p Γ n (s i)))
  have hmul_univ :
      (K : Set Ω) * closure ({1} : Set Ω) = Set.univ := by
    simpa [Ω, K] using
      dense_self_univ
        (p := p) (Γ := Γ) s hs hn
  have hmul_subset : (K : Set Ω) * closure ({1} : Set Ω) ⊆ (K : Set Ω) := by
    rintro x ⟨k, hk, e, he, rfl⟩
    exact K.mul_mem hk (by simpa [Ω, K] using hclosure he)
  have hK_univ : (K : Set Ω) = Set.univ := by
    refine Set.eq_univ_iff_forall.mpr ?_
    intro x
    have hx : x ∈ (K : Set Ω) * closure ({1} : Set Ω) := by
      simp [hmul_univ]
    exact hmul_subset hx
  change K = (⊤ : Subgroup Ω)
  exact SetLike.ext' hK_univ

/-- In a totally disconnected space, the closure of a singleton is that singleton.

This is the point-set topology reason a totally disconnected self-quotient has no residual
closure-of-identity obstruction. -/
lemma singleton_totally_disconnected
    {X : Type u} [TopologicalSpace X] [TotallyDisconnectedSpace X]
    (x : X) :
    closure ({x} : Set X) = {x} := by
  have hpre : IsPreconnected (closure ({x} : Set X)) :=
    isPreconnected_singleton.closure
  have hsub : (closure ({x} : Set X)).Subsingleton :=
    hpre.subsingleton
  exact hsub.eq_singleton_of_mem (subset_closure (by simp))

/-- A totally disconnected self-quotient turns the finite dense generator-image subgroup into the
whole self-quotient. -/
lemma self_totally_disconnected
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    {d : ℕ} (s : Fin d → Γ)
    (hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤)
    {n : ℕ}
    (hn : 1 < n)
    [TotallyDisconnectedSpace (denseSelfQuotient p Γ n)] :
    Subgroup.closure
        (Set.range
          (fun i : Fin d =>
            denseGeneratorsSelf p Γ n (s i))) =
      (⊤ : Subgroup (denseSelfQuotient p Γ n)) := by
  classical
  let Ω : Type u := denseSelfQuotient p Γ n
  let K : Subgroup Ω :=
    Subgroup.closure
      (Set.range
        (fun i : Fin d =>
          denseGeneratorsSelf p Γ n (s i)))
  have hclosure :
      closure ({1} : Set Ω) ⊆ (K : Set Ω) := by
    intro x hx
    have hx_one : x = (1 : Ω) := by
      have hsingle :
          closure ({1} : Set Ω) = ({1} : Set Ω) :=
        singleton_totally_disconnected (X := Ω) (1 : Ω)
      exact Set.mem_singleton_iff.mp (by simpa [hsingle] using hx)
    simp [hx_one]
  exact
    dense_self_top
      (p := p) (Γ := Γ) s hs hn
      (by simp )

/-- If the self-quotient is `T1`, the finite generator-image subgroup is closed. -/
def closed_t_1
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ]
    {d : ℕ} (s : Fin d → Γ)
    {n : ℕ}
    (hn : 1 < n)
    [T1Space (denseSelfQuotient p Γ n)] :
    SCImage
      (p := p) (Γ := Γ) s n := by
  let K : Subgroup (denseSelfQuotient p Γ n) :=
    Subgroup.closure
      (Set.range
        (fun i : Fin d =>
          denseGeneratorsSelf p Γ n (s i)))
  haveI : Finite K := by
    simpa [K] using
      dense_self_image
        (p := p) (Γ := Γ) s hn
  refine ⟨?_⟩
  change IsClosed (K : Set (denseSelfQuotient p Γ n))
  exact (Set.toFinite (K : Set (denseSelfQuotient p Γ n))).isClosed

/-- A `T1` self-quotient turns the finite dense generator-image subgroup into the whole
self-quotient. -/
lemma self_t_1
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    {d : ℕ} (s : Fin d → Γ)
    (hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤)
    {n : ℕ}
    (hn : 1 < n)
    [T1Space (denseSelfQuotient p Γ n)] :
    Subgroup.closure
        (Set.range
          (fun i : Fin d =>
            denseGeneratorsSelf p Γ n (s i))) =
      (⊤ : Subgroup (denseSelfQuotient p Γ n)) := by
  exact
    self_top_closed
      (p := p) (Γ := Γ) (s := s) (n := n)
      (closed_t_1
        (p := p) (Γ := Γ) s hn)
      hs

/-- A `T1` self-quotient is exactly the closedness of the Zassenhaus term downstairs. -/
lemma closed_self_t
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    {n : ℕ}
    [T1Space (denseSelfQuotient p Γ n)] :
    IsClosed ((zassenhausFiltration p Γ n : Subgroup Γ) : Set Γ) := by
  letI : (zassenhausFiltration p Γ n).Normal :=
    zassenhausFiltration_normal p Γ n
  simpa [denseSelfQuotient] using
      (QuotientGroup.t1Space_iff
        (G := Γ)
        (N := zassenhausFiltration p Γ n)).mp
      (show T1Space (Γ ⧸ zassenhausFiltration p Γ n) from inferInstance)

/-- A totally disconnected self-quotient is `T1`, hence `D_n(Γ)` is closed. -/
lemma filtration_totally_disconnected
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    {n : ℕ}
    [TotallyDisconnectedSpace (denseSelfQuotient p Γ n)] :
    IsClosed ((zassenhausFiltration p Γ n : Subgroup Γ) : Set Γ) := by
  let Ω : Type u := denseSelfQuotient p Γ n
  letI : (zassenhausFiltration p Γ n).Normal :=
    zassenhausFiltration_normal p Γ n
  haveI : IsTopologicalGroup Ω := by
    dsimp [Ω, denseSelfQuotient]
    exact QuotientGroup.instIsTopologicalGroup
      (N := zassenhausFiltration p Γ n)
  have hclosed_one : IsClosed ({1} : Set Ω) := by
    have hclosure :
        closure ({1} : Set Ω) = ({1} : Set Ω) :=
      singleton_totally_disconnected (X := Ω) (1 : Ω)
    rw [← hclosure]
    exact isClosed_closure
  haveI : T1Space Ω := IsTopologicalGroup.t1Space Ω hclosed_one
  exact closed_self_t
    (p := p) (Γ := Γ) (n := n)

/-- Abstract generation of the self-quotient makes it finite.

This is the formal restricted-Burnside step: the self-quotient is generated by finitely many
images of `s`, and its `n`th Zassenhaus subgroup is trivial by construction, so the abstract
restricted-Burnside theorem from `T0.lean` applies. -/
lemma self_abstract_generation
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ]
    {d : ℕ} {s : Fin d → Γ}
    {n : ℕ}
    (hn : 1 < n)
    (Hgen : SelfAbstractGeneration
      (p := p) (Γ := Γ) s n) :
    Finite (denseSelfQuotient p Γ n) := by
  let t : Fin d → denseSelfQuotient p Γ n :=
    denseSelfTuple
      (p := p) (Γ := Γ) s n
  have hgen : Subgroup.closure (Set.range t) = ⊤ := by
    simpa [t] using Hgen.closure_range_top
  have htrivial :
      zassenhausFiltration p (denseSelfQuotient p Γ n) n = ⊥ :=
    self_filtration_bot
      (p := p) (Γ := Γ) n
  exact
    fg_trivial_burnside
      (p := p)
      (Λ := denseSelfQuotient p Γ n)
      t
      hn
      hgen
      htrivial

/-- Finite-index openness for densely finitely generated profinite groups.

This is the topological Nikolov-Segal input stripped of all Zassenhaus language.  It says that in
the ambient compact totally disconnected group topologically generated by `s`, every normal
finite-index subgroup is open.  The Zassenhaus application below only has to prove that `D_n(Γ)` is
normal and finite index. -/
structure DGOpenne
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} (s : Fin d → Γ) :
    Type u where
  open_finite_index :
    ∀ N : Subgroup Γ,
      N.Normal →
      N.FiniteIndex →
      IsOpen ((N : Subgroup Γ) : Set Γ)


namespace DGOpenne

/-- Apply finite-index openness to the Zassenhaus subgroup once finite index is known. -/
lemma zassenhaus_open_index
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    (H : DGOpenne (Γ := Γ) s)
    {n : ℕ}
    (hfiniteIndex : (zassenhausFiltration p Γ n).FiniteIndex) :
    IsOpen ((zassenhausFiltration p Γ n : Subgroup Γ) : Set Γ) := by
  let D : Subgroup Γ := zassenhausFiltration p Γ n
  have hnormal : D.Normal := by
    dsimp [D]
    exact zassenhausFiltration_normal p Γ n
  have hfiniteIndexD : D.FiniteIndex := by
    simpa [D] using hfiniteIndex
  have hopen : IsOpen ((D : Subgroup Γ) : Set Γ) :=
    H.open_finite_index D hnormal hfiniteIndexD
  simpa [D] using hopen

end DGOpenne

/-- Openness of kernels of finite abstract quotient maps.

This is the kernel-level automatic-continuity input.  It is smaller than continuity of every finite
quotient map: once kernels are open, the coset argument above proves continuity formally. -/
structure DAOpenne
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} (s : Fin d → Γ) :
    Type (u + 1) where
  open_ker_discrete :
    ∀ {Λ : Type u} [Group Λ] [TopologicalSpace Λ] [DiscreteTopology Λ] [Finite Λ],
      (φ : Γ →* Λ) →
        IsOpen ((φ.ker : Subgroup Γ) : Set Γ)

/-- Continuity of all finite abstract quotients of a densely finitely generated profinite group.

This is a standard Nikolov-Segal formulation: an abstract homomorphism from the group to a finite
discrete group is automa continuous.  It is smaller than finite-index openness because it
does not mention subgroups or Zassenhaus filtrations; those are recovered formally from kernels. -/
structure DAContin
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} (s : Fin d → Γ) :
    Type (u + 1) where
  continuous_finite_discrete :
    ∀ {Λ : Type u} [Group Λ] [TopologicalSpace Λ] [DiscreteTopology Λ] [Finite Λ],
      (φ : Γ →* Λ) →
        Continuous (fun x : Γ => φ x)


namespace DAOpenne

/-- Kernel openness implies automatic continuity of finite abstract quotient maps. -/
def finiteAbstractContinuity
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    (H : DAOpenne (Γ := Γ) s) :
    DAContin (Γ := Γ) s := by
  refine
    { continuous_finite_discrete := ?_ }
  intro Λ _hGroupΛ _hTopΛ _hDiscΛ _hFiniteΛ φ
  exact
    monoid_continuous_discrete
      (Γ := Γ) (Λ := Λ) φ
      (H.open_ker_discrete (Λ := Λ) φ)

end DAOpenne

namespace DGOpenne

/-- Finite-index openness implies openness of kernels of finite abstract quotient maps. -/
noncomputable def abstractKernelOpenness
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    (H : DGOpenne (Γ := Γ) s) :
    DAOpenne (Γ := Γ) s := by
  classical
  refine
    { open_ker_discrete := ?_ }
  intro Λ _hGroupΛ _hTopΛ _hDiscΛ _hFiniteΛ φ
  have hfinite_quotient : Finite (Γ ⧸ φ.ker) := by
    exact Finite.of_equiv φ.range (QuotientGroup.quotientKerEquivRange φ).symm
  have hfiniteIndex : φ.ker.FiniteIndex := by
    letI : Finite (Γ ⧸ φ.ker) := hfinite_quotient
    exact Subgroup.finiteIndex_of_finite_quotient
  exact
    H.open_finite_index φ.ker
      (by infer_instance)
      hfiniteIndex

/-- Finite-index openness implies automatic continuity of finite abstract quotient maps. -/
noncomputable def finiteAbstractContinuity
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    (H : DGOpenne (Γ := Γ) s) :
    DAContin (Γ := Γ) s :=
  H.abstractKernelOpenness.finiteAbstractContinuity

end DGOpenne

namespace DAContin

/-- Automatic continuity of finite quotients makes every normal finite-index subgroup open.

Given a normal finite-index subgroup `N`, endow the abstract quotient `Γ ⧸ N` with the discrete
topology.  Automatic continuity applies to the quotient map, and the preceding kernel lemma
identifies its open kernel with `N`. -/
noncomputable def normalIndexOpenness
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    (H : DAContin (Γ := Γ) s) :
    DGOpenne (Γ := Γ) s := by
  classical
  refine
    { open_finite_index := ?_ }
  intro N hnormal hfiniteIndex
  letI : N.Normal := hnormal
  haveI : N.FiniteIndex := hfiniteIndex
  haveI : Finite (Γ ⧸ N) := by
    infer_instance
  letI : TopologicalSpace (Γ ⧸ N) := ⊥
  letI : DiscreteTopology (Γ ⧸ N) := discreteTopology_bot (Γ ⧸ N)
  let φ : Γ →* Γ ⧸ N := QuotientGroup.mk' N
  have hφ_cont : Continuous (fun x : Γ => φ x) :=
    H.continuous_finite_discrete (Λ := Γ ⧸ N) φ
  have hker_open : IsOpen ((φ.ker : Subgroup Γ) : Set Γ) :=
    monoid_open_discrete
      (Γ := Γ) (Λ := Γ ⧸ N) φ hφ_cont
  have hker_eq : φ.ker = N := by
    ext x
    change φ x = 1 ↔ x ∈ N
    dsimp [φ]
    exact QuotientGroup.eq_one_iff (N := N) x
  simpa [hker_eq] using hker_open

end DAContin

/-- The self-quotient being finite is the finite-index statement for `D_n(Γ)`. -/
lemma filtration_index_self
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ]
    {n : ℕ}
    (hfinite : Finite (denseSelfQuotient p Γ n)) :
    (zassenhausFiltration p Γ n).FiniteIndex := by
  let D : Subgroup Γ := zassenhausFiltration p Γ n
  have hfinite_quotient : Finite (Γ ⧸ D) := by
    change Finite (denseSelfQuotient p Γ n)
    exact hfinite
  letI : Finite (Γ ⧸ D) := hfinite_quotient
  change D.FiniteIndex
  exact Subgroup.finiteIndex_of_finite_quotient

/-- Abstract generation of the self-quotient plus finite-index openness gives residual
finite-quotient separation of `D_n(Γ)`.

The generation hypothesis makes `Γ / D_n(Γ)` finite by the restricted-Burnside argument already
formalized above.  Finite-index openness then makes `D_n(Γ)` open, so the canonical self-quotient
is a finite discrete continuous quotient detecting elements outside `D_n(Γ)`. -/
def separation_abstract_openness
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {n : ℕ}
    (hn : 1 < n)
    (Hgen : SelfAbstractGeneration
      (p := p) (Γ := Γ) s n)
    (Hopen : DGOpenne (Γ := Γ) s) :
    DGSep p Γ n := by
  have hfinite :
      Finite (denseSelfQuotient p Γ n) :=
    self_abstract_generation
      (p := p) (Γ := Γ) hn Hgen
  have hfiniteIndex :
      (zassenhausFiltration p Γ n).FiniteIndex :=
    filtration_index_self
      (p := p) (Γ := Γ) (n := n) hfinite
  have hopenD :
      IsOpen ((zassenhausFiltration p Γ n : Subgroup Γ) : Set Γ) :=
    Hopen.zassenhaus_open_index
      (p := p) (Γ := Γ) hfiniteIndex
  let Htop : STData p Γ n :=
    { isOpen_zassenhaus := hopenD }
  let Halg : DenseSelfData p Γ n :=
    denseSelfData (p := p) (Γ := Γ) n
  refine
    { test_not := ?_ }
  intro g hg
  let T : DGTest Γ :=
    Htop.finiteQuotientTest
  refine ⟨T, ?_⟩
  have hne :
      denseGeneratorsSelf p Γ n g ≠ 1 :=
    dense_self_not
      (p := p) (Γ := Γ) (n := n) hg
  intro hg_target
  have hg_target' :
      denseGeneratorsSelf p Γ n g ∈
        denseSelfTarget p Γ n := by
    simpa [
      T,
      STData.finiteQuotientTest,
      DGTest.targetZassenhaus,
      denseSelfTarget
    ] using hg_target
  have hg_bot :
      denseGeneratorsSelf p Γ n g ∈
        (⊥ : Subgroup (denseSelfQuotient p Γ n)) := by
    simpa [Halg.target_eq_bot] using hg_target'
  exact hne (Subgroup.mem_bot.mp hg_bot)

/-- Abstract generation of the self-quotient plus finite-index openness gives the finite-shadow
intersection principle. -/
def intersection_abstract_openness
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} (s : Fin d → Γ)
    (hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤)
    {n : ℕ}
    (hn : 1 < n)
    (Hgen : SelfAbstractGeneration
      (p := p) (Γ := Γ) s n)
    (Hopen : DGOpenne (Γ := Γ) s) :
    DSInter
      (p := p) (Γ := Γ) s hs n := by
  exact
    (test_intersection_separation
      (separation_abstract_openness
        (p := p) (Γ := Γ) (s := s) hn Hgen Hopen)).fin_shadow_inter
      (p := p) (Γ := Γ) (s := s) (hs := hs)

/-- The theorem-shaped generator-image equality supplies the abstract-generation package. -/
def abstract_generation_top
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ]
    {d : ℕ} {s : Fin d → Γ}
    {n : ℕ}
    (hgen :
      Subgroup.closure
          (Set.range
            (fun i : Fin d =>
              denseGeneratorsSelf p Γ n (s i))) =
        (⊤ : Subgroup (denseSelfQuotient p Γ n))) :
    SelfAbstractGeneration
      (p := p) (Γ := Γ) s n :=
  { closure_range_top := by
      simpa [denseSelfTuple] using hgen }

/-- The theorem-shaped generator-image equality plus finite-index openness gives residual
finite-quotient separation of `D_n(Γ)`. -/
def separation_idx_openness
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {n : ℕ}
    (hn : 1 < n)
    (hgen :
      Subgroup.closure
          (Set.range
            (fun i : Fin d =>
              denseGeneratorsSelf p Γ n (s i))) =
        (⊤ : Subgroup (denseSelfQuotient p Γ n)))
    (Hopen : DGOpenne (Γ := Γ) s) :
    DGSep p Γ n :=
  separation_abstract_openness
    (p := p) (Γ := Γ) (s := s) hn
    (abstract_generation_top
      (p := p) (Γ := Γ) (s := s) hgen)
    Hopen

/-- The theorem-shaped generator-image equality plus finite-index openness gives finite-shadow
intersection. -/
def intersection_idx_openness
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} (s : Fin d → Γ)
    (hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤)
    {n : ℕ}
    (hn : 1 < n)
    (hgen :
      Subgroup.closure
          (Set.range
            (fun i : Fin d =>
              denseGeneratorsSelf p Γ n (s i))) =
        (⊤ : Subgroup (denseSelfQuotient p Γ n)))
    (Hopen : DGOpenne (Γ := Γ) s) :
    DSInter
      (p := p) (Γ := Γ) s hs n :=
  intersection_abstract_openness
    (p := p) (Γ := Γ) s hs hn
    (abstract_generation_top
      (p := p) (Γ := Γ) (s := s) hgen)
    Hopen

/-- Abstract generation of the self-quotient plus automatic continuity of finite abstract
quotients gives residual finite-quotient separation. -/
noncomputable def separation_abstract_continuity
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {n : ℕ}
    (hn : 1 < n)
    (Hgen : SelfAbstractGeneration
      (p := p) (Γ := Γ) s n)
    (Hcont : DAContin (Γ := Γ) s) :
    DGSep p Γ n :=
  separation_abstract_openness
    (p := p) (Γ := Γ) (s := s) hn Hgen Hcont.normalIndexOpenness

/-- Abstract generation of the self-quotient plus automatic continuity of finite abstract
quotients gives finite-shadow intersection. -/
noncomputable def intersection_abstract_continuity
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} (s : Fin d → Γ)
    (hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤)
    {n : ℕ}
    (hn : 1 < n)
    (Hgen : SelfAbstractGeneration
      (p := p) (Γ := Γ) s n)
    (Hcont : DAContin (Γ := Γ) s) :
    DSInter
      (p := p) (Γ := Γ) s hs n :=
  intersection_abstract_openness
    (p := p) (Γ := Γ) s hs hn Hgen Hcont.normalIndexOpenness

/-- Self-quotient topology and algebra data give one finite quotient test separating `g`.

The test is the canonical quotient map `Γ → Γ / D_n(Γ)`.  Topology data makes this quotient finite
and discrete, while algebra data says its target `D_n` is trivial.  Therefore any `g ∉ D_n(Γ)` is
detected outside the target subgroup in this finite quotient. -/
lemma test_topology_data
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ]
    {n : ℕ}
    (Htop : STData p Γ n)
    (Halg : DenseSelfData p Γ n)
    {g : Γ}
    (hg : g ∉ zassenhausFiltration p Γ n) :
    ∃ T : DGTest Γ,
      T.quotientMap g ∉
        DGTest.targetZassenhaus T p n := by
  classical
  let T : DGTest Γ :=
    Htop.finiteQuotientTest
  refine ⟨T, ?_⟩
  have hne :
      denseGeneratorsSelf p Γ n g ≠ 1 :=
    dense_self_not
      (p := p) (Γ := Γ) (n := n) hg
  intro hg_target
  have hg_target' :
      denseGeneratorsSelf p Γ n g ∈
        denseSelfTarget p Γ n := by
    simpa [
      T,
      STData.finiteQuotientTest,
      DGTest.targetZassenhaus,
      denseSelfTarget
    ] using hg_target
  have hg_bot :
      denseGeneratorsSelf p Γ n g ∈
        (⊥ : Subgroup (denseSelfQuotient p Γ n)) := by
    simpa [Halg.target_eq_bot] using hg_target'
  exact hne (Subgroup.mem_bot.mp hg_bot)

/-- Self-quotient topology data gives residual finite-quotient separation.

This packages the preceding pointwise separator for every element outside `D_n(Γ)`.  It is the
formal path from a finite discrete self-quotient to the residual-separation API used by the final
closedness criterion. -/
def separation_self_topology
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ]
    {n : ℕ}
    (Htop : STData p Γ n) :
    DGSep p Γ n := by
  let Halg : DenseSelfData p Γ n :=
    denseSelfData (p := p) (Γ := Γ) n
  refine
    { test_not := ?_ }
  intro g hg
  exact
    test_topology_data
      (p := p) (Γ := Γ) (n := n) Htop Halg hg

/-- Closed finite-index data for `D_n(Γ)` supplies residual finite-quotient separation via the
canonical self-quotient. -/
def separation_closed_input
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ]
    {n : ℕ}
    (Hclosed : DCInput p Γ n) :
    DGSep p Γ n :=
  separation_self_topology
    (p := p) (Γ := Γ) (n := n) Hclosed.toTopologyData

/-- Closedness of `D_n(Γ)` supplies residual finite-quotient separation for densely finitely
generated profinite groups. -/
def dense_separation_closed
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} (s : Fin d → Γ)
    (hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤)
    {n : ℕ}
    (hn : 1 < n)
    (hclosed :
      IsClosed ((zassenhausFiltration p Γ n : Subgroup Γ) : Set Γ)) :
    DGSep p Γ n := by
  have hfinite :
      Finite (denseSelfQuotient p Γ n) :=
    dense_self_one
      (p := p) (Γ := Γ) s hs hclosed hn
  let Hclosed : DCInput p Γ n :=
    { isClosed_zassenhaus := hclosed
      finite_selfQuotient := hfinite }
  exact
    separation_closed_input
      (p := p) (Γ := Γ) (n := n) Hclosed

/-- A separated (`T1`) self-quotient supplies residual finite-quotient separation of `D_n(Γ)`. -/
def separation_t_1
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} (s : Fin d → Γ)
    (hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤)
    {n : ℕ}
    (hn : 1 < n)
    [T1Space (denseSelfQuotient p Γ n)] :
    DGSep p Γ n :=
  dense_separation_closed
    (p := p) (Γ := Γ) s hs hn
    (closed_self_t
      (p := p) (Γ := Γ) (n := n))

/-- A totally disconnected self-quotient supplies residual finite-quotient separation of
`D_n(Γ)`. -/
def separation_totally_disconnected
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} (s : Fin d → Γ)
    (hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤)
    {n : ℕ}
    (hn : 1 < n)
    [TotallyDisconnectedSpace (denseSelfQuotient p Γ n)] :
    DGSep p Γ n :=
  dense_separation_closed
    (p := p) (Γ := Γ) s hs hn
    (filtration_totally_disconnected
      (p := p) (Γ := Γ) (n := n))

/-- A finite-width compact cover gives residual finite-quotient separation of `D_n(Γ)`. -/
def separation_compact_cover
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} (s : Fin d → Γ)
    (hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤)
    {n : ℕ}
    (hn : 1 < n)
    (C : FCCover p Γ n) :
    DGSep p Γ n :=
  dense_separation_closed
    (p := p) (Γ := Γ) s hs hn C.isClosed

/-- A lower-central/power word-map compression package gives residual finite-quotient separation
of `D_n(Γ)`. -/
def separation_compression_package
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} (s : Fin d → Γ)
    (hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤)
    {n : ℕ}
    (hn : 1 < n)
    (P :
      DCPackag
        p Γ n) :
    DGSep p Γ n := by
  haveI : T2Space Γ := t_space_disconnected Γ
  let C : FCCover p Γ n := Classical.choice P.exists_compactCover
  exact
    separation_compact_cover
      (p := p) (Γ := Γ) s hs hn C

/-- Closedness of `D_n(Γ)` supplies the finite-shadow intersection principle needed by the
positive Jennings reduction. -/
def shadow_intersection_closed
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} (s : Fin d → Γ)
    (hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤)
    {n : ℕ}
    (hn : 1 < n)
    (hclosed :
      IsClosed ((zassenhausFiltration p Γ n : Subgroup Γ) : Set Γ)) :
    DSInter
      (p := p) (Γ := Γ) s hs n := by
  exact
    (test_intersection_separation
      (dense_separation_closed
        (p := p) (Γ := Γ) s hs hn hclosed)).fin_shadow_inter
      (p := p) (Γ := Γ) (s := s) (hs := hs)

/-- A separated (`T1`) self-quotient supplies the finite-shadow intersection principle used by
the completed group-algebra construction. -/
def shadow_intersection_t
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} (s : Fin d → Γ)
    (hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤)
    {n : ℕ}
    (hn : 1 < n)
    [T1Space (denseSelfQuotient p Γ n)] :
    DSInter
      (p := p) (Γ := Γ) s hs n := by
  exact
    (test_intersection_separation
      (separation_t_1
        (p := p) (Γ := Γ) s hs hn)).fin_shadow_inter
      (p := p) (Γ := Γ) (s := s) (hs := hs)

/-- A totally disconnected self-quotient supplies the finite-shadow intersection principle used
by the completed group-algebra construction. -/
def shadow_intersection_disconnected
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} (s : Fin d → Γ)
    (hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤)
    {n : ℕ}
    (hn : 1 < n)
    [TotallyDisconnectedSpace (denseSelfQuotient p Γ n)] :
    DSInter
      (p := p) (Γ := Γ) s hs n := by
  exact
    (test_intersection_separation
      (separation_totally_disconnected
        (p := p) (Γ := Γ) s hs hn)).fin_shadow_inter
      (p := p) (Γ := Γ) (s := s) (hs := hs)

/-- A finite-width compact cover gives the finite-shadow intersection principle used by the
completed group-algebra construction. -/
def intersection_compact_cover
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} (s : Fin d → Γ)
    (hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤)
    {n : ℕ}
    (hn : 1 < n)
    (C : FCCover p Γ n) :
    DSInter
      (p := p) (Γ := Γ) s hs n := by
  exact
    (test_intersection_separation
      (separation_compact_cover
        (p := p) (Γ := Γ) s hs hn C)).fin_shadow_inter
      (p := p) (Γ := Γ) (s := s) (hs := hs)

/-- A lower-central/power word-map compression package gives the finite-shadow intersection
principle used by the completed group-algebra construction. -/
def intersection_compression_package
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} (s : Fin d → Γ)
    (hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤)
    {n : ℕ}
    (hn : 1 < n)
    (P :
      DCPackag
        p Γ n) :
    DSInter
      (p := p) (Γ := Γ) s hs n := by
  haveI : T2Space Γ := t_space_disconnected Γ
  let C : FCCover p Γ n := Classical.choice P.exists_compactCover
  exact
    intersection_compact_cover
      (p := p) (Γ := Γ) s hs hn C

/-- A controlled finite shadow plus finite-index openness gives residual finite-quotient
separation.

The controlled shadow makes the dense generator image all of the self-quotient, hence the
self-quotient is finite by restricted Burnside.  Finite-index openness then makes the canonical
quotient by `D_n(Γ)` a finite discrete continuous quotient, which separates elements outside
`D_n(Γ)`. -/
def gens_separation_openness
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    (hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤)
    {n : ℕ}
    (hn : 1 < n)
    (C : GCShadow
      (p := p) (Γ := Γ) s n)
    (hkernel :
      let S := C.continuousFinShadow
      letI : Group S.quotientGroup := S.instGroup
      S.quotientMap.ker ≤
        Subgroup.closure
          (Set.range
            (fun i : Fin d =>
              denseGeneratorsSelf p Γ n (s i))))
    (Hopen : DGOpenne (Γ := Γ) s) :
    DGSep p Γ n := by
  let Ktop :
      Subgroup.closure
          (Set.range
            (fun i : Fin d =>
              denseGeneratorsSelf p Γ n (s i))) =
        (⊤ : Subgroup (denseSelfQuotient p Γ n)) :=
    gens_shadow_control
      (p := p) (Γ := Γ) (s := s) C hs hkernel
  let Hgen :
      SelfAbstractGeneration
        (p := p) (Γ := Γ) s n :=
    { closure_range_top := by
        simpa [denseSelfTuple] using Ktop }
  have hfinite :
      Finite (denseSelfQuotient p Γ n) :=
    self_abstract_generation
      (p := p) (Γ := Γ) (s := s) hn Hgen
  have hfiniteIndex :
      (zassenhausFiltration p Γ n).FiniteIndex :=
    filtration_index_self
      (p := p) (Γ := Γ) (n := n) hfinite
  have hopenD :
      IsOpen ((zassenhausFiltration p Γ n : Subgroup Γ) : Set Γ) :=
    Hopen.zassenhaus_open_index
      (p := p) (Γ := Γ) hfiniteIndex
  let Htop : STData p Γ n :=
    { isOpen_zassenhaus := hopenD }
  exact
    separation_self_topology
      (p := p) (Γ := Γ) (n := n) Htop

/-- A controlled finite shadow plus finite-index openness gives finite-shadow intersection. -/
def gens_intersection_openness
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} (s : Fin d → Γ)
    (hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤)
    {n : ℕ}
    (hn : 1 < n)
    (C : GCShadow
      (p := p) (Γ := Γ) s n)
    (hkernel :
      let S := C.continuousFinShadow
      letI : Group S.quotientGroup := S.instGroup
      S.quotientMap.ker ≤
        Subgroup.closure
          (Set.range
            (fun i : Fin d =>
              denseGeneratorsSelf p Γ n (s i))))
    (Hopen : DGOpenne (Γ := Γ) s) :
    DSInter
      (p := p) (Γ := Γ) s hs n := by
  exact
    (test_intersection_separation
      (gens_separation_openness
        (p := p) (Γ := Γ) (s := s) hs hn C hkernel Hopen)).fin_shadow_inter
      (p := p) (Γ := Γ) (s := s) (hs := hs)

/-- A controlled finite shadow plus automatic continuity of finite abstract quotients gives
residual finite-quotient separation. -/
noncomputable def gens_separation_continuity
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    (hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤)
    {n : ℕ}
    (hn : 1 < n)
    (C : GCShadow
      (p := p) (Γ := Γ) s n)
    (hkernel :
      let S := C.continuousFinShadow
      letI : Group S.quotientGroup := S.instGroup
      S.quotientMap.ker ≤
        Subgroup.closure
          (Set.range
            (fun i : Fin d =>
              denseGeneratorsSelf p Γ n (s i))))
    (Hcont : DAContin (Γ := Γ) s) :
    DGSep p Γ n :=
  gens_separation_openness
    (p := p) (Γ := Γ) (s := s) hs hn C hkernel
    Hcont.normalIndexOpenness

/-- A controlled finite shadow plus automatic continuity of finite abstract quotients gives
finite-shadow intersection. -/
noncomputable def gens_abstract_continuity
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} (s : Fin d → Γ)
    (hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤)
    {n : ℕ}
    (hn : 1 < n)
    (C : GCShadow
      (p := p) (Γ := Γ) s n)
    (hkernel :
      let S := C.continuousFinShadow
      letI : Group S.quotientGroup := S.instGroup
      S.quotientMap.ker ≤
        Subgroup.closure
          (Set.range
            (fun i : Fin d =>
              denseGeneratorsSelf p Γ n (s i))))
    (Hcont : DAContin (Γ := Γ) s) :
    DSInter
      (p := p) (Γ := Γ) s hs n := by
  exact
    (test_intersection_separation
      (gens_separation_continuity
        (p := p) (Γ := Γ) (s := s) hs hn C hkernel Hcont)).fin_shadow_inter
      (p := p) (Γ := Γ) (s := s) (hs := hs)

/-- The upper Jennings-Lazard kernel inclusion follows formally from the positive
dimension-subgroup input.

The proof first converts membership in the quotient-unit kernel into the congruence
`canonicalUnit g - 1 ∈ I^n` using the already-formal quotient-map lemma from `T0.lean`, and then
applies the positive dimension-subgroup implication. -/
lemma lazard_upper_input
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (C : DCCore (p := p) (Γ := Γ) s hs n)
    (Hinput : JLInput C) :
    Nonempty (LUBound C) := by
  refine ⟨{ quotient_unit_ker := ?_ }⟩
  intro g hg
  have hcongruence :
      (C.canonicalUnit g : C.completedGroupAlgebra) - 1 ∈ C.augmentationIdeal ^ n :=
    jennings_lazard_ker
      (p := p) (Γ := Γ) (s := s) (hs := hs) (n := n) C hg
  exact
    dense_generators_lazard
      (p := p) (Γ := Γ) (s := s) (hs := hs) C Hinput g hcongruence

/-- Every canonical group-like element is congruent to `1` modulo the augmentation ideal. -/
lemma jennings_lazard_ideal
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (C : DCCore (p := p) (Γ := Γ) s hs n)
    (g : Γ) :
    (C.canonicalUnit g : C.completedGroupAlgebra) - 1 ∈ C.augmentationIdeal := by
  rw [C.augmentation_ideal_ker]
  change
    C.augmentationMap.toRingHom
        ((C.canonicalUnit g : C.completedGroupAlgebra) - 1) = 0
  simp [map_sub, C.canonicalUnit_augmentation g]

/-- Commutators add augmentation degree for the canonical completed group-algebra congruence
subgroups. -/
lemma jennings_lazard_commutator
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {level : ℕ}
    (C : DCCore (p := p) (Γ := Γ) s hs level)
    {m n : ℕ} {g h : Γ}
    (hg : g ∈ generators_lazard_subgroup C n)
    (hh : h ∈ generators_lazard_subgroup C m) :
    g * h * g⁻¹ * h⁻¹ ∈
      generators_lazard_subgroup C (n + m) := by
  letI : C.augmentationIdeal.IsTwoSided := by
    rw [C.augmentation_ideal_ker]
    infer_instance
  change
    (C.canonicalUnit (g * h * g⁻¹ * h⁻¹) : C.completedGroupAlgebra) - 1 ∈
      C.augmentationIdeal ^ (n + m)
  let u : C.completedGroupAlgebra := C.canonicalUnit g
  let v : C.completedGroupAlgebra := C.canonicalUnit h
  let uinv : C.completedGroupAlgebra := C.canonicalUnit g⁻¹
  let vinv : C.completedGroupAlgebra := C.canonicalUnit h⁻¹
  have hcomm :
      (C.canonicalUnit (g * h * g⁻¹ * h⁻¹) : C.completedGroupAlgebra) - 1 =
        (((u - 1) * (v - 1) - (v - 1) * (u - 1)) * uinv) * vinv := by
    calc
      (C.canonicalUnit (g * h * g⁻¹ * h⁻¹) : C.completedGroupAlgebra) - 1 =
          u * v * uinv * vinv - 1 := by
        simp [u, v, uinv, vinv, mul_assoc]
      _ = u * v * uinv * vinv - v * u * uinv * vinv := by
        have hcancel : v * u * uinv * vinv = 1 := by
          simp [u, v, uinv, vinv, mul_assoc]
        rw [hcancel]
      _ = ((u * v - v * u) * uinv) * vinv := by
        noncomm_ring
      _ = (((u - 1) * (v - 1) - (v - 1) * (u - 1)) * uinv) * vinv := by
        noncomm_ring
  rw [hcomm]
  let I : Ideal C.completedGroupAlgebra := C.augmentationIdeal
  have hgmem :
      (C.canonicalUnit g : C.completedGroupAlgebra) - 1 ∈ I ^ n := by
    simpa [I] using
      (jennings_lazard_augmentation
        (p := p) (Γ := Γ) (s := s) (hs := hs) C g).1 hg
  have hhmem :
      (C.canonicalUnit h : C.completedGroupAlgebra) - 1 ∈ I ^ m := by
    simpa [I] using
      (jennings_lazard_augmentation
        (p := p) (Γ := Γ) (s := s) (hs := hs) C h).1 hh
  have hnm :
      (u - 1) * (v - 1) ∈ I ^ (n + m) := by
    have hmul : (u - 1) * (v - 1) ∈ I ^ n * I ^ m := by
      exact Ideal.mul_mem_mul (by simpa [u, I] using hgmem) (by simpa [v, I] using hhmem)
    have hpow : I ^ (n + m) = I ^ n * I ^ m := by
      simpa using (Ideal.IsTwoSided.pow_add (I := I) (m := n) (n := m))
    exact hpow.symm ▸ hmul
  have hmn :
      (v - 1) * (u - 1) ∈ I ^ (n + m) := by
    have hmul : (v - 1) * (u - 1) ∈ I ^ m * I ^ n := by
      exact Ideal.mul_mem_mul (by simpa [v, I] using hhmem) (by simpa [u, I] using hgmem)
    have hpow : I ^ (m + n) = I ^ m * I ^ n := by
      simpa using (Ideal.IsTwoSided.pow_add (I := I) (m := m) (n := n))
    exact by
      rw [Nat.add_comm] at hpow
      exact hpow.symm ▸ hmul
  have hsub :
      (u - 1) * (v - 1) - (v - 1) * (u - 1) ∈ I ^ (n + m) :=
    sub_mem hnm hmn
  have hright :
      ((u - 1) * (v - 1) - (v - 1) * (u - 1)) * uinv ∈ I ^ (n + m) :=
    Ideal.mul_mem_right uinv (I ^ (n + m)) hsub
  exact Ideal.mul_mem_right vinv (I ^ (n + m)) hright

/-- The canonical completed group-algebra augmentation-power subgroups form a descending central
series after shifting by one. -/
lemma lazard_descending_series
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {level : ℕ}
    (C : DCCore (p := p) (Γ := Γ) s hs level) :
    Subgroup.IsDescendingCentralSeries
      (fun k => generators_lazard_subgroup C (k + 1)) := by
  constructor
  · ext g
    constructor
    · intro _
      simp
    · intro _
      have h :
          (C.canonicalUnit g : C.completedGroupAlgebra) - 1 ∈ C.augmentationIdeal ^ 1 := by
        simpa [Submodule.pow_one] using
          jennings_lazard_ideal
            (p := p) (Γ := Γ) (s := s) (hs := hs) C g
      exact
        (jennings_lazard_augmentation
          (p := p) (Γ := Γ) (s := s) (hs := hs) C g).2 h
  · intro x k hx g
    have hg : g ∈ generators_lazard_subgroup C 1 := by
      have h :
          (C.canonicalUnit g : C.completedGroupAlgebra) - 1 ∈ C.augmentationIdeal ^ 1 := by
        simpa [Submodule.pow_one] using
          jennings_lazard_ideal
            (p := p) (Γ := Γ) (s := s) (hs := hs) C g
      exact
        (jennings_lazard_augmentation
          (p := p) (Γ := Γ) (s := s) (hs := hs) C g).2 h
    simpa [Nat.add_assoc] using
      jennings_lazard_commutator
        (p := p) (Γ := Γ) (s := s) (hs := hs) C hx hg

/-- Lower-central elements have the corresponding completed augmentation degree. -/
lemma jennings_lazard_succ
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {level : ℕ}
    (C : DCCore (p := p) (Γ := Γ) s hs level)
    (i : ℕ) :
    Subgroup.lowerCentralSeries Γ i ≤
      generators_lazard_subgroup C (i + 1) := by
  exact Subgroup.descending_central_series_ge_lower
    (H := fun k => generators_lazard_subgroup C (k + 1))
    (lazard_descending_series
      (p := p) (Γ := Γ) (s := s) (hs := hs) C)
    i

/-- In characteristic `p`, taking a `p^j`-power multiplies completed augmentation degree by
`p^j`. -/
lemma dense_lazard_subgroup
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {level : ℕ}
    (C : DCCore (p := p) (Γ := Γ) s hs level)
    [CharP C.completedGroupAlgebra p]
    {m j : ℕ} {g : Γ}
    (hg : g ∈ generators_lazard_subgroup C m) :
    g ^ (p ^ j) ∈
      generators_lazard_subgroup C (m * p ^ j) := by
  letI : C.augmentationIdeal.IsTwoSided := by
    rw [C.augmentation_ideal_ker]
    infer_instance
  change
    (C.canonicalUnit (g ^ (p ^ j)) : C.completedGroupAlgebra) - 1 ∈
      C.augmentationIdeal ^ (m * p ^ j)
  let I : Ideal C.completedGroupAlgebra := C.augmentationIdeal
  have hgmem :
      (C.canonicalUnit g : C.completedGroupAlgebra) - 1 ∈ I ^ m := by
    simpa [I] using
      (jennings_lazard_augmentation
        (p := p) (Γ := Γ) (s := s) (hs := hs) C g).1 hg
  have hpow_eq :
      ((C.canonicalUnit g : C.completedGroupAlgebra) - 1) ^ (p ^ j) =
        (C.canonicalUnit (g ^ (p ^ j)) : C.completedGroupAlgebra) - 1 := by
    rw [sub_pow_char_pow_of_commute (p := p) (n := j)
      (x := (C.canonicalUnit g : C.completedGroupAlgebra))
      (y := (1 : C.completedGroupAlgebra)) (Commute.one_right _)]
    simp [map_pow]
  rw [← hpow_eq]
  have hpow :
      ((C.canonicalUnit g : C.completedGroupAlgebra) - 1) ^ (p ^ j) ∈
        (I ^ m) ^ (p ^ j) :=
    Ideal.pow_mem_pow hgmem (p ^ j)
  convert hpow using 1
  exact (GShafar.ideal_pow_mul I m (p ^ j)).symm

/-- The lower Jennings-Lazard generator calculation.

This is the reverse, generator-by-generator half of the kernel theorem.  It is the formal version
of the argument in `T2.tex` Step 4: lower-central elements have the expected augmentation degree,
prime powers multiply that degree in characteristic `p`, and the subgroup generated by the
Zassenhaus generators therefore maps trivially modulo `I^n`.

Unlike the upper direction, this should be purely algebraic for any completed core whose canonical
units augment to `1`; no positive dimension-subgroup input is used here. -/
lemma dense_lazard_ker
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (C : DCCore (p := p) (Γ := Γ) s hs n)
    [CharP C.completedGroupAlgebra p] :
    zassenhausGeneratorSet p Γ n ≤ C.quotientUnitMap.ker := by
  intro g hg
  rcases hg with ⟨i, j, x, hx_lower, hbound, rfl⟩
  have hx_depth :
      x ∈ generators_lazard_subgroup C (i + 1) :=
    jennings_lazard_succ
      (p := p) (Γ := Γ) (s := s) (hs := hs) C i hx_lower
  have hx_power :
      x ^ (p ^ j) ∈
        generators_lazard_subgroup C ((i + 1) * p ^ j) :=
    dense_lazard_subgroup
      (p := p) (Γ := Γ) (s := s) (hs := hs) C hx_depth
  have hx_target :
      x ^ (p ^ j) ∈ generators_lazard_subgroup C n := by
    have hmem :
        (C.canonicalUnit (x ^ (p ^ j)) : C.completedGroupAlgebra) - 1 ∈
          C.augmentationIdeal ^ ((i + 1) * p ^ j) :=
      (jennings_lazard_augmentation
        (p := p) (Γ := Γ) (s := s) (hs := hs) C (x ^ (p ^ j))).1 hx_power
    exact
      (jennings_lazard_augmentation
        (p := p) (Γ := Γ) (s := s) (hs := hs) C (x ^ (p ^ j))).2
        (Ideal.pow_le_pow_right hbound hmem)
  exact
    jennings_lazard_sub
      (p := p) (Γ := Γ) (s := s) (hs := hs) (n := n) C
      ((jennings_lazard_augmentation
        (p := p) (Γ := Γ) (s := s) (hs := hs) C (x ^ (p ^ j))).1 hx_target)

/-- The lower Jennings-Lazard kernel inclusion follows from the generator calculation and subgroup
closure. -/
lemma jennings_lazard_core
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (C : DCCore (p := p) (Γ := Γ) s hs n)
    [CharP C.completedGroupAlgebra p] :
    Nonempty (DenseLazardBound C) := by
  refine ⟨{ zassenhaus_filtration_ker := ?_ }⟩
  exact
    filtration_generator_set
      (p := p) (Γ := Γ) (n := n) (K := C.quotientUnitMap.ker)
      (dense_lazard_ker
        (p := p) (Γ := Γ) (s := s) (hs := hs) (n := n) C)

/-- The remaining Jennings-Lazard kernel theorem for a completed quotient core.

Mathematically this is true by the mod-`p` dimension-subgroup theorem for the completed group
algebra: the kernel of the quotient-unit map modulo `I^n` is exactly `D_n(Γ)`.  This is strictly
smaller than the previous construction placeholder: all finite Hausdorff quotient construction has
already been done by `t_completed_core`, and this lemma
only asks for the kernel equality.
-/
lemma lazard_identification_core
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (C : DCCore (p := p) (Γ := Γ) s hs n)
    (Hinput : JLInput C)
    [CharP C.completedGroupAlgebra p]
    (_hn : 1 < n) :
    Nonempty (JLIdenti C) := by
  rcases lazard_upper_input
      (p := p) (Γ := Γ) (s := s) (hs := hs) C Hinput with
    ⟨U⟩
  rcases jennings_lazard_core
      (p := p) (Γ := Γ) (s := s) (hs := hs) (n := n) C with
    ⟨L⟩
  exact ⟨U.toIdentification L⟩

/-- The first-isomorphism/range half of the Jennings-Lazard identification.

Once the kernel has been identified with `D_n(Γ)`, the range of the quotient-unit map is
canonically isomorphic to the intrinsic quotient `Γ ⧸ D_n(Γ)`.  This is separate from the kernel
theorem: it is quotient-group bookkeeping and the normalization of the equivalence on elements
coming from `Γ`.
-/
lemma lazard_equivalence_identification
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    {C : DCCore (p := p) (Γ := Γ) s hs n}
    (K : JLIdenti C) :
    Nonempty (JenningsLazardEquivalence C K) := by
  classical
  letI : (C.quotientUnitMap.ker).Normal := inferInstance
  letI : (zassenhausFiltration p Γ n).Normal := zassenhausFiltration_normal p Γ n
  let eKer :
      C.quotientUnitMap.range ≃* Γ ⧸ C.quotientUnitMap.ker :=
    (QuotientGroup.quotientKerEquivRange C.quotientUnitMap).symm
  let eZassenhaus :
      Γ ⧸ C.quotientUnitMap.ker ≃*
        generators_jennings_approx (p := p) (Γ := Γ) s hs n :=
    by
      dsimp [generators_jennings_approx]
      exact QuotientGroup.quotientMulEquivOfEq K.unit_map_ker
  let e :
      C.quotientUnitMap.range ≃*
        generators_jennings_approx (p := p) (Γ := Γ) s hs n :=
    eKer.trans eZassenhaus
  refine ⟨{ quotientEquiv := e, quotientEquiv_apply := ?_ }⟩
  intro g
  have hRangeInverse :
      (QuotientGroup.quotientKerEquivRange C.quotientUnitMap).symm
          ⟨C.quotientUnitMap g, ⟨g, rfl⟩⟩ =
        QuotientGroup.mk' C.quotientUnitMap.ker g := by
    apply (QuotientGroup.quotientKerEquivRange C.quotientUnitMap).injective
    rw [(QuotientGroup.quotientKerEquivRange C.quotientUnitMap).apply_symm_apply]
    rfl
  dsimp [e, eKer, eZassenhaus, dense_jennings_approx]
  rw [hRangeInverse]
  rfl


end DGSep

end Towers
