import Mathlib
import Towers.Algebra.CompletedGroupAlgebra.CoreBoundedWords
import Towers.Algebra.DenseGenerators.FiniteGroupAlgebra


open scoped Topology Pointwise

noncomputable section

namespace Towers

universe u

namespace PPJennin

/-- Reflection of positive Zassenhaus membership from all continuous finite
shadows. -/
structure FiniteShadowIntersection
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

/-- Finite quotient upper control plus finite-shadow intersection gives the
pointwise positive dimension-subgroup bound for the canonical quotient layer. -/
def positive_pointwise_intersection
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
    (Hshadow : FiniteShadowIntersection (p := p) (Γ := Γ) s hs n) :
    P.PDUpperb Q R U := by
  refine
    { pointwise_mem_zassenhaus := ?_ }
  intro g hcongruence
  exact
    Hshadow.forall_finite_quotient g
      (by
        intro Λ _instGroupΛ _instTopΛ _instDiscreteΛ _instFiniteΛ φ hφ
        exact Hupper.finite_quotient_zassenhaus g hcongruence φ hφ)

/-- Convert the canonical pointwise upper bound into the subgroup-inclusion
interface used by the Jennings-Lazard kernel proof. -/
def positive_pointwise_upper
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

/-- Build a finite Hausdorff canonical quotient layer while retaining the
canonical package needed by finite-quotient Jennings transport. -/
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

/-- Positive-level same-core Jennings input from finite-shadow intersection and
finite ordinary Jennings. -/
lemma core_shadow_intersection
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} (s : Fin d → Γ)
    (hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤)
    {n : ℕ}
    (hn : 1 < n)
    (Hshadow : FiniteShadowIntersection (p := p) (Γ := Γ) s hs n)
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
    positive_pointwise_intersection
      (p := p) (Γ := Γ) (s := s) (hs := hs) Hupper Hshadow
  let Hsub :
      JLBound
        (P.toAmbient.toCore (Q.toQuotientLayer R U)) :=
    positive_pointwise_upper
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

end PPJennin

end Towers
