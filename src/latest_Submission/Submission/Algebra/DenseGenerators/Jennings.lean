import Mathlib
import Submission.Group.DenseGenerators.ZassenhausCompact


open scoped Topology Pointwise

noncomputable section

namespace Submission

universe u
universe v w z

structure
    GCPackag.PosDimfinQuotsep
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (P :
      GCPackag
        (p := p) Γ s hs)
    (n : ℕ) :
    Type (u + 1) where
  zassenhaus_quotient_images :
    ∀ g : Γ,
      (∀ {Λ : Type u} [Group Λ] [TopologicalSpace Λ] [DiscreteTopology Λ] [Finite Λ]
        (φ : Γ →* Λ),
          Continuous (fun x : Γ => φ x) →
          φ g ∈ zassenhausFiltration p Λ n) →
      g ∈ zassenhausFiltration p Γ n

namespace DGSep

def positiveDimensionSeparation
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {P :
      GCPackag
        (p := p) Γ s hs}
    {n : ℕ}
    (H : DGSep p Γ n) :
    P.PosDimfinQuotsep n := by
  refine
    { zassenhaus_quotient_images := ?_ }
  intro g himages
  exact
    H.forall_test_images
      (g := g)
      (fun T => by
        letI : Group T.quotientGroup := T.instGroup
        letI : TopologicalSpace T.quotientGroup := T.instTopologicalSpace
        letI : DiscreteTopology T.quotientGroup := T.instDiscreteTopology
        letI : Finite T.quotientGroup := T.instFinite
        have htarget :
            T.quotientMap g ∈ zassenhausFiltration p T.quotientGroup n :=
          himages
            (Λ := T.quotientGroup)
            T.quotientMap
            T.quotientMap_continuous
        simpa [DGTest.targetZassenhaus] using htarget)

end DGSep

def
    GCPackag.PFUpperb.pointwise_upper_bound
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
    (Hfinite : P.PFUpperb Q R U)
    (Hseparation : P.PosDimfinQuotsep n) :
    P.PDUpperb Q R U := by
  refine
    { pointwise_mem_zassenhaus := ?_ }
  intro g hcongruence
  refine
    Hseparation.zassenhaus_quotient_images g ?_
  intro Λ _instGroupΛ _instTopΛ _instDiscreteΛ _instFiniteΛ φ hφ
  exact
    Hfinite.finite_quotient_zassenhaus g hcongruence φ hφ

def
    GCPackag.PDUpperb.pos_dim_subgroupbound
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
    (H : P.PDUpperb Q R U) :
    JLBound
      (P.toAmbient.toCore (Q.toQuotientLayer R U)) := by
  let C : DCCore (p := p) (Γ := Γ) s hs n :=
    P.toAmbient.toCore (Q.toQuotientLayer R U)
  refine
    { augmentation_subgroup_zassenhaus := ?_ }
  intro g hg
  have hcongruence :
      (C.canonicalUnit g : C.completedGroupAlgebra) - 1 ∈ C.augmentationIdeal ^ n :=
    (jennings_lazard_augmentation
      (p := p) (Γ := Γ) (s := s) (hs := hs) C g).1 hg
  simpa [C] using H.pointwise_mem_zassenhaus g hcongruence

def
    GCPackag.posdim_inputpos_subgroupbounds
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (P :
      GCPackag
        (p := p) Γ s hs)
    {n : ℕ}
    (Q : DCAlg
      (p := p) (Γ := Γ) (s := s) (hs := hs) n P.toAmbient)
    (R : DenseCompletedReduction Q)
    (U : DenseGeneratorsCompleted R)
    (hbound :
      ∀ _ : 1 < n,
        Nonempty
          (JLBound
            (P.toAmbient.toCore (Q.toQuotientLayer R U)))) :
    JLInput
      (P.toAmbient.toCore (Q.toQuotientLayer R U)) := by
  refine ⟨?_⟩
  intro hn
  exact hbound hn

structure CJPackag
    (p : ℕ) [Fact p.Prime]
    (Γ : Type u) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} (s : Fin d → Γ)
    (hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤) :
    Type (u + 2) where
  densePackage :
    GCPackag
      (p := p) Γ s hs
  positiveDimensionInputs :
    densePackage.toAmbient.JLDiminp

def CJPackag.toAmbient
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (P :
      CJPackag
        (p := p) Γ s hs) :
    GCAmbien (p := p) (Γ := Γ) s hs :=
  P.densePackage.toAmbient

lemma
    CJPackag.ambient_denseunit_algspan
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (P :
      CJPackag
        (p := p) Γ s hs) :
    P.toAmbient.DenseAlgebraSpan := by
  simpa [CJPackag.toAmbient] using
    P.densePackage.ambient_denseunit_algspan

def
    CJPackag.ambientjennings_lazardpos_diminputs
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (P :
      CJPackag
        (p := p) Γ s hs) :
    P.toAmbient.JLDiminp := by
  simpa [CJPackag.toAmbient] using
    P.positiveDimensionInputs

lemma
    CJPackag.existsambient_densespan_posdiminputs
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (P :
      CJPackag
        (p := p) Γ s hs) :
    ∃ A : GCAmbien (p := p) (Γ := Γ) s hs,
      A.DenseAlgebraSpan ∧
        Nonempty A.JLDiminp := by
  exact
    ⟨P.toAmbient,
      P.ambient_denseunit_algspan,
      ⟨P.ambientjennings_lazardpos_diminputs⟩⟩

lemma
    CJPackag.ambientcont_augkernel_twole
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (P :
      CJPackag
        (p := p) Γ s hs)
    {n : ℕ} (hn : 2 ≤ n) :
    Nonempty (P.toAmbient.ContAugPowerkernel n) := by
  have hdense :
      P.toAmbient.DenseAlgebraSpan :=
    P.ambient_denseunit_algspan
  rcases
      P.toAmbient.existsaug_idealettdens_unitalgspan
        hdense with
    ⟨Hletters⟩
  rcases
      P.toAmbient.existsaugpower_wordspanideal_letterdensespan
        (n := n) Hletters with
    ⟨Hpower⟩
  let G :
      P.toAmbient.FintopologiLeftgenAugpower n :=
    P.toAmbient.fintopologi_leftaugpower_worddensespan
      Hpower
  have hclosed :
      P.toAmbient.ClosedAugPower n :=
    P.toAmbient.closedaug_powertopologi_leftaugpower G
  have hopen :
      IsOpen
        ((P.toAmbient.augmentationIdeal ^ n :
            Ideal P.toAmbient.completedGroupAlgebra) :
          Set P.toAmbient.completedGroupAlgebra) :=
    P.toAmbient.openaug_powerpower_twole
      hdense hclosed hn
  exact
    P.toAmbient.contaug_powerkernel_openaugpower
      (p := p) (Γ := Γ) (s := s) (hs := hs) hopen

lemma
    CJPackag.ambient_closedpower_twole
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (P :
      CJPackag
        (p := p) Γ s hs)
    {n : ℕ} (hn : 2 ≤ n) :
    P.toAmbient.ClosedAugPower n := by
  rcases
      P.ambientcont_augkernel_twole
        (p := p) (Γ := Γ) (s := s) (hs := hs) hn with
    ⟨K⟩
  exact P.toAmbient.closed_augpower_contkernel K

lemma
    CJPackag.ambient_closedaug_powerpos
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (P :
      CJPackag
        (p := p) Γ s hs)
    {n : ℕ} (hn : 0 < n) :
    P.toAmbient.ClosedAugPower n := by
  rcases nat_or_pos hn with hOne | htwo
  · subst n
    exact P.toAmbient.closed_aug_powerone
  · exact
      P.ambient_closedpower_twole
        (p := p) (Γ := Γ) (s := s) (hs := hs) htwo

lemma
    CJPackag.ambient_topo_augquot
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (P :
      CJPackag
        (p := p) Γ s hs)
    (n : ℕ) :
    P.toAmbient.TopoAugQuot n := by
  cases n with
  | zero =>
      exact P.toAmbient.topo_aug_quotzero
  | succ n =>
      have hclosed : P.toAmbient.ClosedAugPower (Nat.succ n) :=
        P.ambient_closedaug_powerpos
          (p := p) (Γ := Γ) (s := s) (hs := hs) (Nat.succ_pos n)
      exact P.toAmbient.topoaug_quotclosed_augpower hclosed

lemma JLInput.mem_zassenhaus
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    {C : DCCore (p := p) (Γ := Γ) s hs n}
    (H : JLInput C) :
    ∀ g : Γ,
      (C.canonicalUnit g : C.completedGroupAlgebra) - 1 ∈ C.augmentationIdeal ^ n →
        g ∈ zassenhausFiltration p Γ n := by
  by_cases hn : n ≤ 1
  · exact
      dense_jennings_lazard
        (p := p) (Γ := Γ) (s := s) (hs := hs) C hn
  · have hpos : 1 < n := Nat.lt_of_not_ge hn
    rcases H.positive_bound hpos with ⟨B⟩
    intro g hg
    exact B.mem_zassenhaus (p := p) (Γ := Γ) (s := s) (hs := hs) hg

lemma jennings_lazard_input
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (C : DCCore (p := p) (Γ := Γ) s hs n)
    (H : JLInput C) :
    Nonempty (LUBound C) := by
  refine ⟨?_⟩
  refine
    { quotient_unit_ker := ?_ }
  intro g hg
  have hcongruence :
      (C.canonicalUnit g : C.completedGroupAlgebra) - 1 ∈
        C.augmentationIdeal ^ n :=
    jennings_lazard_ker
      (p := p) (Γ := Γ) (s := s) (hs := hs) (n := n) C hg
  exact H.mem_zassenhaus (p := p) (Γ := Γ) (s := s) (hs := hs) g hcongruence

lemma lazard_upper_bound
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (C : DCCore (p := p) (Γ := Γ) s hs n)
    (Hinput : JLInput C) :
    Nonempty (LUBound C) := by
  exact
    jennings_lazard_input
      (p := p) (Γ := Γ) (s := s) (hs := hs) (n := n) C Hinput

lemma jennings_lazard_ideal
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (C : DCCore (p := p) (Γ := Γ) s hs n)
    (x : Γ) :
    (C.canonicalUnit x : C.completedGroupAlgebra) - 1 ∈ C.augmentationIdeal := by
  rw [C.augmentation_ideal_ker]
  change
    C.augmentationMap.toRingHom
        ((C.canonicalUnit x : C.completedGroupAlgebra) - 1) = 0
  simp [map_sub, C.canonicalUnit_augmentation x]

lemma jennings_lazard_unit
    {R : Type u} [Ring R]
    (u v : Units R) :
    ((u * v * u⁻¹ * v⁻¹ : Units R) : R) - 1 =
      ((((u : R) - 1) * ((v : R) - 1) -
          (((v : R) - 1) * ((u : R) - 1))) *
        ((u⁻¹ : Units R) : R)) * ((v⁻¹ : Units R) : R) := by
  simp only [Units.val_mul]
  noncomm_ring [Units.mul_inv, Units.inv_mul]

lemma dense_lazard_add
    {R : Type u} [Ring R]
    (I : Ideal R)
    [I.IsTwoSided]
    {m n : ℕ}
    {u v : Units R}
    (hu : (u : R) - 1 ∈ I ^ m)
    (hv : (v : R) - 1 ∈ I ^ n) :
    ((u * v * u⁻¹ * v⁻¹ : Units R) : R) - 1 ∈ I ^ (m + n) := by
  have hleft :
      ((u : R) - 1) * ((v : R) - 1) ∈ I ^ (m + n) := by
    rw [Ideal.IsTwoSided.pow_add (I := I) m n]
    exact Ideal.mul_mem_mul hu hv
  have hright :
      ((v : R) - 1) * ((u : R) - 1) ∈ I ^ (m + n) := by
    have hright' :
        ((v : R) - 1) * ((u : R) - 1) ∈ I ^ (n + m) := by
      rw [Ideal.IsTwoSided.pow_add (I := I) n m]
      exact Ideal.mul_mem_mul hv hu
    simpa [Nat.add_comm] using hright'
  have hdiff :
      ((u : R) - 1) * ((v : R) - 1) -
          (((v : R) - 1) * ((u : R) - 1)) ∈ I ^ (m + n) :=
    (I ^ (m + n)).sub_mem hleft hright
  rw [jennings_lazard_unit]
  exact
    (I ^ (m + n)).mul_mem_right ((v⁻¹ : Units R) : R)
      ((I ^ (m + n)).mul_mem_right ((u⁻¹ : Units R) : R) hdiff)

lemma jennings_lazard_add
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n m k : ℕ}
    (C : DCCore (p := p) (Γ := Γ) s hs n)
    {x y : Γ}
    (hx :
      (C.canonicalUnit x : C.completedGroupAlgebra) - 1 ∈
        C.augmentationIdeal ^ m)
    (hy :
      (C.canonicalUnit y : C.completedGroupAlgebra) - 1 ∈
        C.augmentationIdeal ^ k) :
    (C.canonicalUnit (x * y * x⁻¹ * y⁻¹) : C.completedGroupAlgebra) - 1 ∈
      C.augmentationIdeal ^ (m + k) := by
  letI : C.augmentationIdeal.IsTwoSided := by
    rw [C.augmentation_ideal_ker]
    infer_instance
  have hunit :
      C.canonicalUnit (x * y * x⁻¹ * y⁻¹) =
        C.canonicalUnit x * C.canonicalUnit y *
          (C.canonicalUnit x)⁻¹ * (C.canonicalUnit y)⁻¹ := by
    simp [map_mul, map_inv, mul_assoc]
  simpa [hunit] using
    dense_lazard_add
      (I := C.augmentationIdeal) (m := m) (n := k)
      (u := C.canonicalUnit x) (v := C.canonicalUnit y) hx hy

lemma jennings_lazard_power
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n i : ℕ}
    (C : DCCore (p := p) (Γ := Γ) s hs n)
    {x : Γ}
    (hx : x ∈ Subgroup.lowerCentralSeries Γ i) :
    (C.canonicalUnit x : C.completedGroupAlgebra) - 1 ∈ C.augmentationIdeal ^ (i + 1) := by
  letI : C.augmentationIdeal.IsTwoSided := by
    rw [C.augmentation_ideal_ker]
    infer_instance
  induction i generalizing x with
  | zero =>
      have hbase :
          (C.canonicalUnit x : C.completedGroupAlgebra) - 1 ∈ C.augmentationIdeal :=
        jennings_lazard_ideal
          (p := p) (Γ := Γ) (s := s) (hs := hs) (n := n) C x
      simpa [Submodule.pow_one] using hbase
  | succ i ih =>
      rw [Subgroup.lowerCentralSeries_succ] at hx
      let P :=
        generators_lazard_subgroup
          (p := p) (Γ := Γ) (s := s) (hs := hs) (n := n) C (i + 2)
      have hclosure :
          Subgroup.closure
              { g : Γ | ∃ a ∈ Subgroup.lowerCentralSeries Γ i,
                  ∃ b ∈ (⊤ : Subgroup Γ), a * b * a⁻¹ * b⁻¹ = g } ≤ P := by
        rw [Subgroup.closure_le]
        rintro g ⟨a, ha, b, _hb, rfl⟩
        change
          (C.canonicalUnit (a * b * a⁻¹ * b⁻¹) : C.completedGroupAlgebra) - 1 ∈
            C.augmentationIdeal ^ (i + 2)
        have haI :
            (C.canonicalUnit a : C.completedGroupAlgebra) - 1 ∈
              C.augmentationIdeal ^ (i + 1) :=
          ih ha
        have hbI :
            (C.canonicalUnit b : C.completedGroupAlgebra) - 1 ∈
              C.augmentationIdeal ^ 1 := by
          have hbI0 :
              (C.canonicalUnit b : C.completedGroupAlgebra) - 1 ∈
                C.augmentationIdeal :=
            jennings_lazard_ideal
              (p := p) (Γ := Γ) (s := s) (hs := hs) (n := n) C b
          simpa [Submodule.pow_one] using hbI0
        have hcomm :
            (C.canonicalUnit (a * b * a⁻¹ * b⁻¹) : C.completedGroupAlgebra) - 1 ∈
              C.augmentationIdeal ^ ((i + 1) + 1) :=
          jennings_lazard_add
            (p := p) (Γ := Γ) (s := s) (hs := hs) (n := n)
            (m := i + 1) (k := 1) C haI hbI
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hcomm
      exact hclosure hx

lemma dense_lazard_augmentation
    {R : Type u} [Ring R]
    (I : Ideal R)
    {m n : ℕ} {a : R}
    (hbound : n ≤ m)
    (ha : a ∈ I ^ m) :
    a ∈ I ^ n := by
  exact Ideal.pow_le_pow_right hbound ha

lemma jennings_lazard_mul
    {R : Type u} [Ring R]
    (I : Ideal R)
    [I.IsTwoSided]
    {m k : ℕ} {a : R}
    (ha : a ∈ I ^ m) :
    a ^ k ∈ I ^ (m * k) := by
  have hpowers : (I ^ m) ^ k = I ^ (m * k) := by
    induction k with
    | zero =>
        rw [mul_zero, Submodule.pow_zero, Submodule.pow_zero]
    | succ k ih =>
        calc
          (I ^ m) ^ (k + 1) = (I ^ m) ^ k * I ^ m := by
            rw [Ideal.IsTwoSided.pow_add, Submodule.pow_one]
          _ = I ^ (m * k) * I ^ m := by
            rw [ih]
          _ = I ^ (m * k + m) := by
            exact (Ideal.IsTwoSided.pow_add (I := I) (m * k) m).symm
          _ = I ^ (m * (k + 1)) := by
            rw [Nat.mul_succ]
  have hpow : a ^ k ∈ (I ^ m) ^ k :=
    Ideal.pow_mem_pow ha k
  simpa [hpowers] using hpow

lemma jennings_lazard_bound
    {R : Type u} [Ring R]
    (I : Ideal R)
    [I.IsTwoSided]
    {p n i j : ℕ} {a : R}
    (ha : a ∈ I ^ (i + 1))
    (hbound : n ≤ (i + 1) * p ^ j) :
    a ^ (p ^ j) ∈ I ^ n := by
  have hpow :
      a ^ (p ^ j) ∈ I ^ ((i + 1) * p ^ j) :=
    jennings_lazard_mul
      (I := I) (m := i + 1) (k := p ^ j) ha
  exact
    dense_lazard_augmentation
      (I := I) (m := (i + 1) * p ^ j) (n := n) hbound hpow

lemma lazard_char_zmod
    {p : ℕ} {A : Type u} [Ring A] [Algebra (ZMod p) A]
    (ε : A →ₐ[ZMod p] ZMod p) :
    CharP A p where
  cast_eq_zero_iff k := by
    constructor
    · intro hk
      have hmap :
          ε ((k : A)) = 0 := by
        rw [hk, map_zero]
      have hzmod :
          (k : ZMod p) = 0 := by
        simpa only [map_natCast, map_zero] using hmap
      exact (CharP.cast_eq_zero_iff (ZMod p) p k).1 hzmod
    · intro hk
      have hzmod :
          (k : ZMod p) = 0 :=
        (CharP.cast_eq_zero_iff (ZMod p) p k).2 hk
      have hscalar :
          algebraMap (ZMod p) A (k : ZMod p) = algebraMap (ZMod p) A 0 := by
        rw [hzmod]
      simpa only [map_natCast, map_zero] using hscalar

lemma lazard_completed_char
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (C : DCCore (p := p) (Γ := Γ) s hs n) :
    CharP C.completedGroupAlgebra p :=
  lazard_char_zmod C.augmentationMap

lemma lazard_char_p
    {R : Type u} [Ring R]
    {p j : ℕ} [Fact p.Prime] [CharP R p]
    (a : R) :
    a ^ (p ^ j) - 1 = (a - 1) ^ (p ^ j) := by
  have hsub :
      (a - 1) ^ (p ^ j) = a ^ (p ^ j) - (1 : R) ^ (p ^ j) := by
    simpa only [one_pow] using
      (sub_pow_char_pow_of_commute (R := R) (p := p) (n := j)
        (x := a) (y := 1) (Commute.one_right a))
  calc
    a ^ (p ^ j) - 1 = a ^ (p ^ j) - (1 : R) ^ (p ^ j) := by
      rw [one_pow]
    _ = (a - 1) ^ (p ^ j) := hsub.symm

lemma dense_lazard_sub
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n j : ℕ}
    (C : DCCore (p := p) (Γ := Γ) s hs n)
    {x : Γ} :
    (C.canonicalUnit (x ^ (p ^ j)) : C.completedGroupAlgebra) - 1 =
      ((C.canonicalUnit x : C.completedGroupAlgebra) - 1) ^ (p ^ j) := by
  letI : CharP C.completedGroupAlgebra p :=
    lazard_completed_char
      (p := p) (Γ := Γ) (s := s) (hs := hs) (n := n) C
  have hunit :
      (C.canonicalUnit (x ^ (p ^ j)) : C.completedGroupAlgebra) =
        (C.canonicalUnit x : C.completedGroupAlgebra) ^ (p ^ j) := by
    have hunitUnits :
        C.canonicalUnit (x ^ (p ^ j)) = C.canonicalUnit x ^ (p ^ j) :=
      map_pow C.canonicalUnit x (p ^ j)
    simpa only [Units.val_pow_eq_pow_val] using
      congrArg (fun u : Units C.completedGroupAlgebra => (u : C.completedGroupAlgebra)) hunitUnits
  calc
    (C.canonicalUnit (x ^ (p ^ j)) : C.completedGroupAlgebra) - 1 =
        (C.canonicalUnit x : C.completedGroupAlgebra) ^ (p ^ j) - 1 := by
      rw [hunit]
    _ = ((C.canonicalUnit x : C.completedGroupAlgebra) - 1) ^ (p ^ j) :=
      lazard_char_p
        (p := p) (j := j) (C.canonicalUnit x : C.completedGroupAlgebra)

lemma dense_lazard_power
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n i j : ℕ}
    (C : DCCore (p := p) (Γ := Γ) s hs n)
    {x : Γ}
    (hxI :
      (C.canonicalUnit x : C.completedGroupAlgebra) - 1 ∈
        C.augmentationIdeal ^ (i + 1))
    (hbound : n ≤ (i + 1) * p ^ j) :
    (C.canonicalUnit (x ^ (p ^ j)) : C.completedGroupAlgebra) - 1 ∈
      C.augmentationIdeal ^ n := by
  letI : C.augmentationIdeal.IsTwoSided := by
    rw [C.augmentation_ideal_ker]
    infer_instance
  have hpow :
      ((C.canonicalUnit x : C.completedGroupAlgebra) - 1) ^ (p ^ j) ∈
        C.augmentationIdeal ^ n :=
    jennings_lazard_bound
      (I := C.augmentationIdeal) (p := p) (n := n) (i := i) (j := j) hxI hbound
  have hidentity :
      (C.canonicalUnit (x ^ (p ^ j)) : C.completedGroupAlgebra) - 1 =
        ((C.canonicalUnit x : C.completedGroupAlgebra) - 1) ^ (p ^ j) :=
    dense_lazard_sub
      (p := p) (Γ := Γ) (s := s) (hs := hs) (n := n) (j := j) C
  rw [hidentity]
  exact hpow

lemma generators_lazard_ker
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n i j : ℕ}
    (C : DCCore (p := p) (Γ := Γ) s hs n)
    {x g : Γ}
    (hx : x ∈ Subgroup.lowerCentralSeries Γ i)
    (hbound : n ≤ (i + 1) * p ^ j)
    (hpow : x ^ (p ^ j) = g) :
    g ∈ C.quotientUnitMap.ker := by
  have hxI :
      (C.canonicalUnit x : C.completedGroupAlgebra) - 1 ∈
        C.augmentationIdeal ^ (i + 1) :=
    jennings_lazard_power
      (p := p) (Γ := Γ) (s := s) (hs := hs) (n := n) C hx
  have hpowI :
      (C.canonicalUnit (x ^ (p ^ j)) : C.completedGroupAlgebra) - 1 ∈
        C.augmentationIdeal ^ n :=
    dense_lazard_power
      (p := p) (Γ := Γ) (s := s) (hs := hs) (n := n) (i := i) (j := j) C
      hxI hbound
  have hgI :
      (C.canonicalUnit g : C.completedGroupAlgebra) - 1 ∈ C.augmentationIdeal ^ n := by
    simpa [← hpow] using hpowI
  exact
    jennings_lazard_sub
      (p := p) (Γ := Γ) (s := s) (hs := hs) (n := n) C hgI

lemma dense_lazard_ker
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (C : DCCore (p := p) (Γ := Γ) s hs n) :
    zassenhausGeneratorSet p Γ n ≤ C.quotientUnitMap.ker := by
  intro g hg
  rcases hg with ⟨i, j, x, hx, hbound, hpow⟩
  exact
    generators_lazard_ker
      (p := p) (Γ := Γ) (s := s) (hs := hs) (n := n) C hx hbound hpow

lemma generators_lazard_bound
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (C : DCCore (p := p) (Γ := Γ) s hs n) :
    Nonempty (DenseLazardBound C) := by
  have hgenerators :
      zassenhausGeneratorSet p Γ n ≤ C.quotientUnitMap.ker :=
    dense_lazard_ker
      (p := p) (Γ := Γ) (s := s) (hs := hs) (n := n) C
  have hclosure :
      zassenhausFiltration p Γ n ≤ C.quotientUnitMap.ker :=
    filtration_generator_set
      (p := p) (Γ := Γ) (n := n) hgenerators
  refine ⟨?_⟩
  exact
    { zassenhaus_filtration_ker := hclosure }

lemma lazard_identification_input
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (C : DCCore (p := p) (Γ := Γ) s hs n)
    (H : JLInput C) :
    Nonempty (JLIdenti C) := by
  rcases
      jennings_lazard_input
        (p := p) (Γ := Γ) (s := s) (hs := hs) (n := n) C H with
    ⟨U⟩
  rcases generators_lazard_bound
      (p := p) (Γ := Γ) (s := s) (hs := hs) (n := n) C with
    ⟨L⟩
  exact ⟨U.toIdentification L⟩

lemma dense_lazard_identification
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (C : DCCore (p := p) (Γ := Γ) s hs n)
    (Hinput : JLInput C) :
    Nonempty (JLIdenti C) := by
  exact
    lazard_identification_input
      (p := p) (Γ := Γ) (s := s) (hs := hs) (n := n) C Hinput

lemma jennings_lazard_equivalence
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (C : DCCore (p := p) (Γ := Γ) s hs n)
    (K : JLIdenti C) :
    Nonempty (JenningsLazardEquivalence C K) := by
  letI : (zassenhausFiltration p Γ n).Normal := zassenhausFiltration_normal p Γ n
  letI := C.instQuotientRing
  let f : Γ →* Units C.augmentationQuotient := C.quotientUnitMap
  let firstIso : Γ ⧸ f.ker ≃* f.range :=
    QuotientGroup.quotientKerEquivRange f
  let rewriteKernel : Γ ⧸ f.ker ≃*
      generators_jennings_approx (p := p) (Γ := Γ) s hs n :=
    QuotientGroup.quotientMulEquivOfEq K.unit_map_ker
  let quotientEquiv :
      C.quotientUnitMap.range ≃*
        generators_jennings_approx (p := p) (Γ := Γ) s hs n :=
    firstIso.symm.trans rewriteKernel
  refine ⟨?_⟩
  refine
    { quotientEquiv := quotientEquiv
      quotientEquiv_apply := ?_ }
  intro g
  have hfirst :
      firstIso (QuotientGroup.mk' f.ker g) =
        (⟨f g, ⟨g, rfl⟩⟩ : f.range) := by
    rfl
  have hsymm :
      firstIso.symm (⟨f g, ⟨g, rfl⟩⟩ : f.range) =
        QuotientGroup.mk' f.ker g := by
    rw [← hfirst]
    exact firstIso.symm_apply_apply (QuotientGroup.mk' f.ker g)
  calc
    quotientEquiv ⟨C.quotientUnitMap g, ⟨g, rfl⟩⟩
        = rewriteKernel
            (firstIso.symm (⟨f g, ⟨g, rfl⟩⟩ : f.range)) := by
          rfl
    _ = rewriteKernel (QuotientGroup.mk' f.ker g) := by
          rw [hsymm]
    _ = dense_jennings_approx
          (p := p) (Γ := Γ) s hs n g := by
          rfl

lemma jennings_lazard_identification
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (C : DCCore (p := p) (Γ := Γ) s hs n)
    (H : JLInput C) :
    Nonempty (DenseLazardIdentification C) := by
  rcases
      lazard_identification_input
        (p := p) (Γ := Γ) (s := s) (hs := hs) (n := n) C H with
    ⟨K⟩
  rcases jennings_lazard_equivalence
      (p := p) (Γ := Γ) (s := s) (hs := hs) (n := n) C K with
    ⟨R⟩
  exact ⟨K.toIdentification R⟩

lemma lazard_identification_inputs
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    {A : GCAmbien (p := p) (Γ := Γ) s hs}
    (H : A.JLDiminp)
    (Q : DCAlg
      (p := p) (Γ := Γ) (s := s) (hs := hs) n A)
    (R : DenseCompletedReduction Q)
    (U : DenseGeneratorsCompleted R) :
    Nonempty
      (DenseLazardIdentification
        (A.toCore (Q.toQuotientLayer R U))) := by
  let C : DCCore (p := p) (Γ := Γ) s hs n :=
    A.toCore (Q.toQuotientLayer R U)
  have hinput : JLInput C := by
    simpa [C] using H.toCore Q R U
  exact
    jennings_lazard_identification
      (p := p) (Γ := Γ) (s := s) (hs := hs) (n := n) C hinput

lemma generators_lazard_identification
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (C : DCCore (p := p) (Γ := Γ) s hs n)
    (Hinput : JLInput C) :
    Nonempty (DenseLazardIdentification C) := by
  exact
    jennings_lazard_identification
      (p := p) (Γ := Γ) (s := s) (hs := hs) (n := n) C Hinput

lemma DCAlg.fin_quot_layer
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    {A : GCAmbien (p := p) (Γ := Γ) s hs}
    (Q : DCAlg
      (p := p) (Γ := Γ) (s := s) (hs := hs) n A)
    (R : DenseCompletedReduction Q)
    (U : DenseGeneratorsCompleted R)
    (hfinite : Finite Q.augmentationQuotient) :
    Finite (Q.toQuotientLayer R U).augmentationQuotient := by
  simpa [DCAlg.toQuotientLayer] using
    hfinite

lemma DCLayer.finite_toCore
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    {A : GCAmbien (p := p) (Γ := Γ) s hs}
    (Q : DCLayer
      (p := p) (Γ := Γ) (s := s) (hs := hs) n A)
    (hfinite : Finite Q.augmentationQuotient) :
    Finite (A.toCore Q).augmentationQuotient := by
  simpa [GCAmbien.toCore] using hfinite

lemma DCCore.finite_toModel
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (C : DCCore (p := p) (Γ := Γ) s hs n)
    (J : DenseLazardIdentification C)
    (hfinite : Finite C.augmentationQuotient) :
    Finite (C.toModel J).augmentationQuotient := by
  simpa [DCCore.toModel] using hfinite

lemma DCAlg.fin_model_fintrunc
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    {A : GCAmbien (p := p) (Γ := Γ) s hs}
    (Q : DCAlg
      (p := p) (Γ := Γ) (s := s) (hs := hs) n A)
    (T : A.FCAugtru n)
    (R : DenseCompletedReduction Q)
    (U : DenseGeneratorsCompleted R)
    (J : DenseLazardIdentification (A.toCore (Q.toQuotientLayer R U))) :
    Finite ((A.toCore (Q.toQuotientLayer R U)).toModel J).augmentationQuotient := by
  have hfiniteQ : Finite Q.augmentationQuotient :=
    Q.fin_fin_trunc T
  have hfiniteLayer : Finite (Q.toQuotientLayer R U).augmentationQuotient :=
    Q.fin_quot_layer R U hfiniteQ
  have hfiniteCore : Finite (A.toCore (Q.toQuotientLayer R U)).augmentationQuotient :=
    (Q.toQuotientLayer R U).finite_toCore hfiniteLayer
  exact
    (A.toCore (Q.toQuotientLayer R U)).finite_toModel J hfiniteCore

lemma
    DCAlg.fin_modelfin_algtrunc
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    {A : GCAmbien (p := p) (Γ := Γ) s hs}
    (Q : DCAlg
      (p := p) (Γ := Γ) (s := s) (hs := hs) n A)
    (T : A.FAAugtru n)
    (R : DenseCompletedReduction Q)
    (U : DenseGeneratorsCompleted R)
    (J : DenseLazardIdentification (A.toCore (Q.toQuotientLayer R U))) :
    Finite ((A.toCore (Q.toQuotientLayer R U)).toModel J).augmentationQuotient := by
  have hfiniteQ : Finite Q.augmentationQuotient :=
    Q.fin_fin_algtrunc T
  have hfiniteLayer : Finite (Q.toQuotientLayer R U).augmentationQuotient :=
    Q.fin_quot_layer R U hfiniteQ
  have hfiniteCore : Finite (A.toCore (Q.toQuotientLayer R U)).augmentationQuotient :=
    (Q.toQuotientLayer R U).finite_toCore hfiniteLayer
  exact
    (A.toCore (Q.toQuotientLayer R U)).finite_toModel J hfiniteCore

lemma
    DCAlg.existsidentifi_finfin_posdiminput
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    {A : GCAmbien (p := p) (Γ := Γ) s hs}
    (Q : DCAlg
      (p := p) (Γ := Γ) (s := s) (hs := hs) n A)
    (T : A.FCAugtru n)
    (R : DenseCompletedReduction Q)
    (U : DenseGeneratorsCompleted R)
    (H :
      JLInput
        (A.toCore (Q.toQuotientLayer R U))) :
    ∃ J : DenseLazardIdentification (A.toCore (Q.toQuotientLayer R U)),
      Finite ((A.toCore (Q.toQuotientLayer R U)).toModel J).augmentationQuotient := by
  rcases
      jennings_lazard_identification
        (p := p) (Γ := Γ) (s := s) (hs := hs) (n := n)
        (A.toCore (Q.toQuotientLayer R U)) H with
    ⟨J⟩
  exact ⟨J, Q.fin_model_fintrunc T R U J⟩

lemma
    DCAlg.existsidentifi_finalg_posdiminput
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    {A : GCAmbien (p := p) (Γ := Γ) s hs}
    (Q : DCAlg
      (p := p) (Γ := Γ) (s := s) (hs := hs) n A)
    (T : A.FAAugtru n)
    (R : DenseCompletedReduction Q)
    (U : DenseGeneratorsCompleted R)
    (H :
      JLInput
        (A.toCore (Q.toQuotientLayer R U))) :
    ∃ J : DenseLazardIdentification (A.toCore (Q.toQuotientLayer R U)),
      Finite ((A.toCore (Q.toQuotientLayer R U)).toModel J).augmentationQuotient := by
  rcases
      jennings_lazard_identification
        (p := p) (Γ := Γ) (s := s) (hs := hs) (n := n)
        (A.toCore (Q.toQuotientLayer R U)) H with
    ⟨J⟩
  exact ⟨J, Q.fin_modelfin_algtrunc T R U J⟩

lemma gens_ambient_trunc
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (A : GCAmbien (p := p) (Γ := Γ) s hs)
    (HJL : A.JLDiminp)
    (T : A.FCAugtru n) :
    ∃ M : DCModel (p := p) (Γ := Γ) s hs n,
      Finite M.augmentationQuotient := by
  have hclosed : A.ClosedAugPower n :=
    A.closed_augpower_fintrunc T
  have htop : A.TopoAugQuot n :=
    A.topoaug_quotclosed_augpower hclosed
  rcases htop with ⟨Qalg, hTop⟩
  rcases hTop with ⟨Top⟩
  let Q : DCAlg
      (p := p) (Γ := Γ) (s := s) (hs := hs) n A :=
    Qalg.toAugmentationQuotient Top
  rcases dense_completed_reduction
      (p := p) (Γ := Γ) (s := s) (hs := hs) Q with ⟨R⟩
  rcases dense_generators_completed
      (p := p) (Γ := Γ) (s := s) (hs := hs) R with ⟨U⟩
  let C : DCCore (p := p) (Γ := Γ) s hs n :=
    A.toCore (Q.toQuotientLayer R U)
  have hinput : JLInput C := by
    simpa [C] using HJL.toCore Q R U
  rcases generators_lazard_identification
      (p := p) (Γ := Γ) (s := s) (hs := hs) (n := n) C hinput with ⟨J⟩
  refine ⟨C.toModel J, ?_⟩
  have hfinite :
      Finite ((A.toCore (Q.toQuotientLayer R U)).toModel J).augmentationQuotient :=
    Q.fin_model_fintrunc T R U J
  simpa [C] using hfinite

lemma
    gens_algebraic_trunc
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (A : GCAmbien (p := p) (Γ := Γ) s hs)
    (HJL : A.JLDiminp)
    (T : A.FAAugtru n)
    (HTop : T.DiscreteContTopo) :
    ∃ M : DCModel (p := p) (Γ := Γ) s hs n,
      Finite M.augmentationQuotient := by
  let Tcont : A.FCAugtru n :=
    T.fin_cont_augtrunc HTop
  have hclosed : A.ClosedAugPower n :=
    A.closed_augpower_fintrunc Tcont
  have htop : A.TopoAugQuot n :=
    A.topoaug_quotclosed_augpower hclosed
  rcases htop with ⟨Qalg, hTop⟩
  rcases hTop with ⟨Top⟩
  let Q : DCAlg
      (p := p) (Γ := Γ) (s := s) (hs := hs) n A :=
    Qalg.toAugmentationQuotient Top
  rcases dense_completed_reduction
      (p := p) (Γ := Γ) (s := s) (hs := hs) Q with ⟨R⟩
  rcases dense_generators_completed
      (p := p) (Γ := Γ) (s := s) (hs := hs) R with ⟨U⟩
  let C : DCCore (p := p) (Γ := Γ) s hs n :=
    A.toCore (Q.toQuotientLayer R U)
  have hinput : JLInput C := by
    simpa [C] using HJL.toCore Q R U
  rcases generators_lazard_identification
      (p := p) (Γ := Γ) (s := s) (hs := hs) (n := n) C hinput with ⟨J⟩
  refine ⟨C.toModel J, ?_⟩
  have hfinite :
      Finite ((A.toCore (Q.toQuotientLayer R U)).toModel J).augmentationQuotient :=
    Q.fin_modelfin_algtrunc T R U J
  simpa [C] using hfinite

lemma
    aug_dim_inputs
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (A : GCAmbien (p := p) (Γ := Γ) s hs)
    (HJL : A.JLDiminp)
    (T : A.FCAugtru n) :
    ∃ M : DCModel (p := p) (Γ := Γ) s hs n,
      Finite M.augmentationQuotient := by
  have hclosed : A.ClosedAugPower n :=
    A.closed_augpower_fintrunc T
  have htop : A.TopoAugQuot n :=
    A.topoaug_quotclosed_augpower hclosed
  rcases htop with ⟨Qalg, hTop⟩
  rcases hTop with ⟨Top⟩
  let Q : DCAlg
      (p := p) (Γ := Γ) (s := s) (hs := hs) n A :=
    Qalg.toAugmentationQuotient Top
  rcases dense_completed_reduction
      (p := p) (Γ := Γ) (s := s) (hs := hs) Q with ⟨R⟩
  rcases dense_generators_completed
      (p := p) (Γ := Γ) (s := s) (hs := hs) R with ⟨U⟩
  let C : DCCore (p := p) (Γ := Γ) s hs n :=
    A.toCore (Q.toQuotientLayer R U)
  have hinput : JLInput C := by
    simpa [C] using HJL.toCore Q R U
  rcases Q.existsidentifi_finfin_posdiminput
      T R U hinput with
    ⟨J, hfinite⟩
  exact ⟨C.toModel J, by simpa [C] using hfinite⟩

lemma
    algebraic_dim_inputs
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (A : GCAmbien (p := p) (Γ := Γ) s hs)
    (HJL : A.JLDiminp)
    (T : A.FAAugtru n)
    (HTop : T.DiscreteContTopo) :
    ∃ M : DCModel (p := p) (Γ := Γ) s hs n,
      Finite M.augmentationQuotient := by
  let Tcont : A.FCAugtru n :=
    T.fin_cont_augtrunc HTop
  have hclosed : A.ClosedAugPower n :=
    A.closed_augpower_fintrunc Tcont
  have htop : A.TopoAugQuot n :=
    A.topoaug_quotclosed_augpower hclosed
  rcases htop with ⟨Qalg, hTop⟩
  rcases hTop with ⟨Top⟩
  let Q : DCAlg
      (p := p) (Γ := Γ) (s := s) (hs := hs) n A :=
    Qalg.toAugmentationQuotient Top
  rcases dense_completed_reduction
      (p := p) (Γ := Γ) (s := s) (hs := hs) Q with ⟨R⟩
  rcases dense_generators_completed
      (p := p) (Γ := Γ) (s := s) (hs := hs) R with ⟨U⟩
  let C : DCCore (p := p) (Γ := Γ) s hs n :=
    A.toCore (Q.toQuotientLayer R U)
  have hinput : JLInput C := by
    simpa [C] using HJL.toCore Q R U
  rcases
      Q.existsidentifi_finalg_posdiminput
        T R U hinput with
    ⟨J, hfinite⟩
  exact ⟨C.toModel J, by simpa [C] using hfinite⟩

structure CMInput
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} (s : Fin d → Γ)
    (hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤)
    (n : ℕ) :
    Type (u + 2) where
  ambient :
    GCAmbien (p := p) (Γ := Γ) s hs
  positiveDimensionInputs :
    ambient.JLDiminp
  finiteAlgebraicTruncation :
    ambient.FAAugtru n
  truncationTopology :
    finiteAlgebraicTruncation.DiscreteContTopo

lemma CMInput.exists_model
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (F :
      CMInput
        (p := p) (Γ := Γ) s hs n) :
    ∃ M : DCModel (p := p) (Γ := Γ) s hs n,
      Finite M.augmentationQuotient := by
  exact
    algebraic_dim_inputs
      (p := p) (Γ := Γ) (s := s) (hs := hs)
      F.ambient F.positiveDimensionInputs F.finiteAlgebraicTruncation F.truncationTopology

lemma
    gens_dim_inputs
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (A : GCAmbien (p := p) (Γ := Γ) s hs)
    (HJL : A.JLDiminp) :
    ∃ M : DCModel (p := p) (Γ := Γ) s hs 0,
      Finite M.augmentationQuotient := by
  rcases A.topo_aug_quotzero with ⟨Qalg, hTop⟩
  rcases hTop with ⟨Top⟩
  let Q : DCAlg
      (p := p) (Γ := Γ) (s := s) (hs := hs) 0 A :=
    Qalg.toAugmentationQuotient Top
  rcases dense_completed_reduction
      (p := p) (Γ := Γ) (s := s) (hs := hs) Q with ⟨R⟩
  rcases dense_generators_completed
      (p := p) (Γ := Γ) (s := s) (hs := hs) R with ⟨U⟩
  let C : DCCore (p := p) (Γ := Γ) s hs 0 :=
    A.toCore (Q.toQuotientLayer R U)
  have hinput : JLInput C := by
    simpa [C] using HJL.toCore Q R U
  rcases
      jennings_lazard_identification
        (p := p) (Γ := Γ) (s := s) (hs := hs) (n := 0) C hinput with
    ⟨J⟩
  refine ⟨C.toModel J, ?_⟩
  have hfiniteQ : Finite Q.augmentationQuotient :=
    by
      let Qalg' :
          GAAug
            (p := p) (Γ := Γ) (s := s) (hs := hs) 0 A :=
        { augmentationQuotient := Q.augmentationQuotient
          instQuotientRing := Q.instQuotientRing
          instQuotientAlgebra := Q.instQuotientAlgebra
          quotientMap := Q.quotientMap
          quotientMap_surjective := Q.quotientMap_surjective
          quotientMap_ker := Q.quotientMap_ker }
      have hsub : Subsingleton Q.augmentationQuotient := by
        simpa [Qalg'] using Qalg'.subsingleton_level_zero
      letI : Subsingleton Q.augmentationQuotient := hsub
      exact
        Finite.of_injective (fun _ : Q.augmentationQuotient => ())
          (by
            intro x y _h
            exact Subsingleton.elim x y)
  have hfiniteLayer : Finite (Q.toQuotientLayer R U).augmentationQuotient :=
    Q.fin_quot_layer R U hfiniteQ
  have hfiniteCore : Finite (A.toCore (Q.toQuotientLayer R U)).augmentationQuotient :=
    (Q.toQuotientLayer R U).finite_toCore hfiniteLayer
  have hfiniteModel : Finite ((A.toCore (Q.toQuotientLayer R U)).toModel J).augmentationQuotient :=
    (A.toCore (Q.toQuotientLayer R U)).finite_toModel J hfiniteCore
  simpa [C] using hfiniteModel

lemma
    ambient_dim_inputs
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (A : GCAmbien (p := p) (Γ := Γ) s hs)
    (HJL : A.JLDiminp) :
    ∃ M : DCModel (p := p) (Γ := Γ) s hs 1,
      Finite M.augmentationQuotient := by
  exact
    aug_dim_inputs
      (p := p) (Γ := Γ) (s := s) (hs := hs) A HJL
      A.fin_contaug_truncone

lemma
    dense_gens_input
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ} (_hn : 2 ≤ n)
    (F :
      CMInput
        (p := p) (Γ := Γ) s hs n) :
    ∃ M : DCModel (p := p) (Γ := Γ) s hs n,
      Finite M.augmentationQuotient := by
  exact F.exists_model

lemma
    gens_cases_inputs
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} (s : Fin d → Γ)
    (hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤)
    (A0 : GCAmbien (p := p) (Γ := Γ) s hs)
    (H0 : A0.JLDiminp)
    (Htwo :
      ∀ {m : ℕ}, 2 ≤ m →
        Nonempty
          (CMInput
            (p := p) (Γ := Γ) s hs m))
    (n : ℕ) :
    ∃ M : DCModel (p := p) (Γ := Γ) s hs n,
      Finite M.augmentationQuotient := by
  cases n with
  | zero =>
      exact
        gens_dim_inputs
          (p := p) (Γ := Γ) (s := s) (hs := hs) A0 H0
  | succ n =>
      cases n with
      | zero =>
          exact
            ambient_dim_inputs
              (p := p) (Γ := Γ) (s := s) (hs := hs) A0 H0
      | succ n =>
          have htwo : 2 ≤ Nat.succ (Nat.succ n) :=
            Nat.succ_le_succ (Nat.succ_pos n)
          rcases Htwo htwo with ⟨F⟩
          exact
            dense_gens_input
              (p := p) (Γ := Γ) (s := s) (hs := hs) htwo F

lemma dense_generators_subsingleton {α : Type u} [Subsingleton α] :
    Finite α := by
  exact
    Finite.of_injective (fun _ : α => ())
      (by
        intro x y _h
        exact Subsingleton.elim x y)

lemma DCAlg.fin_level_zero
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {A : GCAmbien (p := p) (Γ := Γ) s hs}
    (Q :
      DCAlg
        (p := p) (Γ := Γ) (s := s) (hs := hs) 0 A) :
    Finite Q.augmentationQuotient := by
  let Qalg :
      GAAug
        (p := p) (Γ := Γ) (s := s) (hs := hs) 0 A :=
    { augmentationQuotient := Q.augmentationQuotient
      instQuotientRing := Q.instQuotientRing
      instQuotientAlgebra := Q.instQuotientAlgebra
      quotientMap := Q.quotientMap
      quotientMap_surjective := Q.quotientMap_surjective
      quotientMap_ker := Q.quotientMap_ker }
  have hsub : Subsingleton Q.augmentationQuotient := by
    simpa [Qalg] using Qalg.subsingleton_level_zero
  letI : Subsingleton Q.augmentationQuotient := hsub
  exact dense_generators_subsingleton

def DCModel.FinDenseWordspan
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (M : DCModel (p := p) (Γ := Γ) s hs n) : Prop :=
  letI := M.instQuotientRing
  letI := M.instQuotientAlgebra
  ∃ ι : Type u, Finite ι ∧
    ∃ w : ι → M.augmentationQuotient,
      Submodule.span (ZMod p) (Set.range w) = ⊤

abbrev denseSignedLetter (d : ℕ) : Type :=
  Fin d × Bool

def generatorsLetterElement
    {Γ : Type u} [Group Γ]
    {d : ℕ} (s : Fin d → Γ)
    (a : denseSignedLetter d) : Γ :=
  if a.2 then s a.1 else (s a.1)⁻¹

def generatorsSignedElement
    {Γ : Type u} [Group Γ]
    {d : ℕ} (s : Fin d → Γ)
    (w : List (denseSignedLetter d)) : Γ :=
  (w.map (generatorsLetterElement s)).prod

@[simp]
lemma generators_element_nil
    {Γ : Type u} [Group Γ]
    {d : ℕ} (s : Fin d → Γ) :
    generatorsSignedElement s [] = 1 := by
  simp [generatorsSignedElement]

@[simp]
lemma generators_element_cons
    {Γ : Type u} [Group Γ]
    {d : ℕ} (s : Fin d → Γ)
    (a : denseSignedLetter d)
    (w : List (denseSignedLetter d)) :
    generatorsSignedElement s (a :: w) =
      generatorsLetterElement s a *
        generatorsSignedElement s w := by
  simp [generatorsSignedElement]

lemma generators_element_append
    {Γ : Type u} [Group Γ]
    {d : ℕ} (s : Fin d → Γ)
    (w₁ w₂ : List (denseSignedLetter d)) :
    generatorsSignedElement s (w₁ ++ w₂) =
      generatorsSignedElement s w₁ *
        generatorsSignedElement s w₂ := by
  rw [generatorsSignedElement]
  rw [List.map_append]
  rw [List.prod_append]
  rfl

def generatorsLetterFlip
    {d : ℕ} (a : denseSignedLetter d) :
    denseSignedLetter d :=
  (a.1, !a.2)

lemma dense_letter_flip
    {Γ : Type u} [Group Γ]
    {d : ℕ} (s : Fin d → Γ)
    (a : denseSignedLetter d) :
    generatorsLetterElement s
        (generatorsLetterFlip a) =
      (generatorsLetterElement s a)⁻¹ := by
  rcases a with ⟨i, b⟩
  cases b
  · simp [generatorsLetterFlip, generatorsLetterElement]
  · simp [generatorsLetterFlip, generatorsLetterElement]

def denseSignedInverse
    {d : ℕ} (w : List (denseSignedLetter d)) :
    List (denseSignedLetter d) :=
  (w.map generatorsLetterFlip).reverse

lemma generators_element_inverse
    {Γ : Type u} [Group Γ]
    {d : ℕ} (s : Fin d → Γ)
    (w : List (denseSignedLetter d)) :
    generatorsSignedElement s
        (denseSignedInverse w) =
      (generatorsSignedElement s w)⁻¹ := by
  induction w with
  | nil =>
      rw [denseSignedInverse]
      simp [generatorsSignedElement]
  | cons a w ih =>
      rw [denseSignedInverse]
      rw [List.map_cons]
      rw [List.reverse_cons]
      rw [generators_element_append]
      change
        generatorsSignedElement s
            (denseSignedInverse w) *
          generatorsSignedElement s
            [generatorsLetterFlip a] =
        (generatorsSignedElement s (a :: w))⁻¹
      rw [ih]
      have hsingle :
          generatorsSignedElement s
              [generatorsLetterFlip a] =
            (generatorsLetterElement s a)⁻¹ := by
        rw [generators_element_cons]
        rw [generators_element_nil]
        rw [mul_one]
        exact dense_letter_flip s a
      rw [hsingle]
      rw [generators_element_cons]
      rw [mul_inv_rev]

lemma dense_letter_closure
    {Γ : Type u} [Group Γ]
    {d : ℕ} (s : Fin d → Γ)
    (a : denseSignedLetter d) :
    generatorsLetterElement s a ∈
      Subgroup.closure (Set.range s) := by
  by_cases h : a.2
  · rw [generatorsLetterElement, if_pos h]
    exact Subgroup.subset_closure ⟨a.1, rfl⟩
  · rw [generatorsLetterElement, if_neg h]
    exact
      (Subgroup.closure (Set.range s)).inv_mem
        (Subgroup.subset_closure ⟨a.1, rfl⟩)

lemma signed_element_closure
    {Γ : Type u} [Group Γ]
    {d : ℕ} (s : Fin d → Γ)
    (w : List (denseSignedLetter d)) :
    generatorsSignedElement s w ∈
      Subgroup.closure (Set.range s) := by
  induction w with
  | nil =>
      rw [generators_element_nil]
      exact (Subgroup.closure (Set.range s)).one_mem
  | cons a w ih =>
      rw [generators_element_cons]
      exact
        (Subgroup.closure (Set.range s)).mul_mem
          (dense_letter_closure s a)
          ih

lemma generators_element_closure
    {Γ : Type u} [Group Γ]
    {d : ℕ} (s : Fin d → Γ)
    {g : Γ}
    (hg : g ∈ Subgroup.closure (Set.range s)) :
    ∃ w : List (denseSignedLetter d),
      generatorsSignedElement s w = g := by
  refine Subgroup.closure_induction (k := Set.range s) ?mem ?one ?mul ?inv hg
  · intro x hx
    rcases hx with ⟨i, rfl⟩
    refine ⟨[(i, true)], ?_⟩
    rw [generators_element_cons]
    rw [generators_element_nil]
    simp [generatorsLetterElement]
  · refine ⟨[], ?_⟩
    rw [generators_element_nil]
  · intro x y _hx _hy hx_word hy_word
    rcases hx_word with ⟨wx, hwx⟩
    rcases hy_word with ⟨wy, hwy⟩
    refine ⟨wx ++ wy, ?_⟩
    rw [generators_element_append]
    rw [hwx, hwy]
  · intro x _hx hx_word
    rcases hx_word with ⟨wx, hwx⟩
    refine ⟨denseSignedInverse wx, ?_⟩
    rw [generators_element_inverse]
    rw [hwx]

abbrev denseBoundedIndex (d n : ℕ) : Type :=
  Σ k : Fin (n + 1), List.Vector (denseSignedLetter d) k

def denseEmptyBounded (d n : ℕ) :
    denseBoundedIndex d n :=
  ⟨⟨0, Nat.succ_pos n⟩, List.Vector.nil⟩

def denseSingletonBounded
    {d n : ℕ} (hn : 0 < n)
    (a : denseSignedLetter d) :
    denseBoundedIndex d n :=
  ⟨⟨1, Nat.succ_lt_succ hn⟩, List.Vector.cons a List.Vector.nil⟩

def denseConsBounded
    {d n : ℕ}
    (a : denseSignedLetter d)
    (v : denseBoundedIndex d n)
    (hv : v.1.1 < n) :
    denseBoundedIndex d n :=
  ⟨⟨v.1.1 + 1, Nat.succ_lt_succ hv⟩, List.Vector.cons a v.2⟩

lemma dense_bounded_index (d n : ℕ) :
    Finite (ULift.{u} (denseBoundedIndex d n)) := by
  have hletters : Finite (denseSignedLetter d) := by
    dsimp [denseSignedLetter]
    infer_instance
  letI : Finite (denseSignedLetter d) := hletters
  have hsmall : Finite (denseBoundedIndex d n) := by
    dsimp [denseBoundedIndex]
    infer_instance
  letI : Finite (denseBoundedIndex d n) := hsmall
  infer_instance

noncomputable def DCModel.signedAugmentationLetter
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (M : DCModel (p := p) (Γ := Γ) s hs n)
    (a : denseSignedLetter d) : M.augmentationQuotient := by
  letI := M.instRing
  letI := M.instQuotientRing
  exact
    M.quotientMap
      ((M.canonicalUnit (generatorsLetterElement s a) :
        M.completedGroupAlgebra) - 1)

noncomputable def DCModel.boundedAugmentationWord
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (M : DCModel (p := p) (Γ := Γ) s hs n)
    (w : denseBoundedIndex d n) : M.augmentationQuotient := by
  letI := M.instQuotientRing
  exact
    (w.2.toList.map fun a =>
      M.signedAugmentationLetter (s := s) a).prod

noncomputable def DCModel.bounded_aug_wordspan
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (M : DCModel (p := p) (Γ := Γ) s hs n) :
    letI := M.instQuotientRing
    letI := M.instQuotientAlgebra
    Submodule (ZMod p) M.augmentationQuotient := by
  letI := M.instQuotientRing
  letI := M.instQuotientAlgebra
  exact
    Submodule.span (ZMod p)
      (Set.range fun w : ULift.{u} (denseBoundedIndex d n) =>
        M.boundedAugmentationWord (s := s) (n := n) w.down)

lemma DCModel.bounded_augword_memspan
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (M : DCModel (p := p) (Γ := Γ) s hs n)
    (w : denseBoundedIndex d n) :
    letI := M.instQuotientRing
    letI := M.instQuotientAlgebra
    M.boundedAugmentationWord (s := s) (n := n) w ∈
      M.bounded_aug_wordspan := by
  letI := M.instQuotientRing
  letI := M.instQuotientAlgebra
  exact Submodule.subset_span ⟨ULift.up w, rfl⟩

@[simp]
lemma DCModel.bounded_aug_wordempty
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (M : DCModel (p := p) (Γ := Γ) s hs n) :
    letI := M.instQuotientRing
    M.boundedAugmentationWord (s := s) (n := n)
      (denseEmptyBounded d n) = 1 := by
  letI := M.instQuotientRing
  simp [DCModel.boundedAugmentationWord,
    denseEmptyBounded]

lemma DCModel.onemem_boundedaug_wordspan
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (M : DCModel (p := p) (Γ := Γ) s hs n) :
    letI := M.instQuotientRing
    letI := M.instQuotientAlgebra
    (1 : M.augmentationQuotient) ∈ M.bounded_aug_wordspan := by
  letI := M.instQuotientRing
  letI := M.instQuotientAlgebra
  simpa using
    M.bounded_augword_memspan
      (s := s) (n := n) (denseEmptyBounded d n)

@[simp]
lemma DCModel.bounded_aug_wordsingleton
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (M : DCModel (p := p) (Γ := Γ) s hs n)
    (hn : 0 < n)
    (a : denseSignedLetter d) :
    letI := M.instQuotientRing
    M.boundedAugmentationWord (s := s) (n := n)
      (denseSingletonBounded hn a) =
      M.signedAugmentationLetter (s := s) a := by
  letI := M.instQuotientRing
  simp [DCModel.boundedAugmentationWord,
    denseSingletonBounded]

@[simp]
lemma DCModel.boundedaug_wordcons_boundedword
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (M : DCModel (p := p) (Γ := Γ) s hs n)
    (a : denseSignedLetter d)
    (v : denseBoundedIndex d n)
    (hv : v.1.1 < n) :
    letI := M.instQuotientRing
    M.boundedAugmentationWord (s := s) (n := n)
      (denseConsBounded a v hv) =
      M.signedAugmentationLetter (s := s) a *
        M.boundedAugmentationWord (s := s) (n := n) v := by
  letI := M.instQuotientRing
  simp [DCModel.boundedAugmentationWord,
    denseConsBounded]

lemma DCModel.signedaug_lettermem_boundedspan
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (M : DCModel (p := p) (Γ := Γ) s hs n)
    (hn : 0 < n)
    (a : denseSignedLetter d) :
    letI := M.instQuotientRing
    letI := M.instQuotientAlgebra
    M.signedAugmentationLetter (s := s) a ∈ M.bounded_aug_wordspan := by
  letI := M.instQuotientRing
  letI := M.instQuotientAlgebra
  simpa using
    M.bounded_augword_memspan
      (s := s) (n := n) (denseSingletonBounded hn a)

def DCModel.BoundedAugWordspan
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (M : DCModel (p := p) (Γ := Γ) s hs n) : Prop :=
  letI := M.instQuotientRing
  letI := M.instQuotientAlgebra
  M.bounded_aug_wordspan = ⊤

lemma dense_generators_zmod
    (p : ℕ) [Fact p.Prime] :
    Finite (ZMod p) := by
  haveI : NeZero p := ⟨(Fact.out : Nat.Prime p).ne_zero⟩
  infer_instance

lemma DCModel.fg_boundedaug_wordspan
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (M : DCModel (p := p) (Γ := Γ) s hs n) :
    letI := M.instQuotientRing
    letI := M.instQuotientAlgebra
    M.bounded_aug_wordspan.FG := by
  letI := M.instQuotientRing
  letI := M.instQuotientAlgebra
  rw [DCModel.bounded_aug_wordspan]
  exact
    Submodule.fg_span
      (Set.finite_range fun w : ULift.{u} (denseBoundedIndex d n) =>
        M.boundedAugmentationWord (s := s) (n := n) w.down)

lemma DCModel.modulefin_boundedaug_wordspan
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (M : DCModel (p := p) (Γ := Γ) s hs n) :
    letI := M.instQuotientRing
    letI := M.instQuotientAlgebra
    Module.Finite (ZMod p) M.bounded_aug_wordspan := by
  letI := M.instQuotientRing
  letI := M.instQuotientAlgebra
  exact
    Module.Finite.of_fg
      (M.fg_boundedaug_wordspan (s := s) (n := n))

lemma DCModel.fin_boundedaug_wordspan
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (M : DCModel (p := p) (Γ := Γ) s hs n) :
    letI := M.instQuotientRing
    letI := M.instQuotientAlgebra
    Finite M.bounded_aug_wordspan := by
  letI := M.instQuotientRing
  letI := M.instQuotientAlgebra
  haveI : Module.Finite (ZMod p) M.bounded_aug_wordspan :=
    M.modulefin_boundedaug_wordspan (s := s) (n := n)
  haveI : Finite (ZMod p) :=
    dense_generators_zmod p
  exact Module.finite_of_finite (ZMod p)

lemma DCModel.setfin_boundedaug_wordspan
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (M : DCModel (p := p) (Γ := Γ) s hs n) :
    letI := M.instQuotientRing
    letI := M.instQuotientAlgebra
    (M.bounded_aug_wordspan : Set M.augmentationQuotient).Finite := by
  classical
  letI := M.instQuotientRing
  letI := M.instQuotientAlgebra
  haveI : Finite M.bounded_aug_wordspan :=
    M.fin_boundedaug_wordspan (s := s) (n := n)
  haveI : Fintype M.bounded_aug_wordspan :=
    Fintype.ofFinite M.bounded_aug_wordspan
  exact Set.toFinite (M.bounded_aug_wordspan : Set M.augmentationQuotient)

lemma DCModel.closed_boundedaug_wordspan
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (M : DCModel (p := p) (Γ := Γ) s hs n) :
    letI := M.instQuotientRing
    letI := M.instQuotientAlgebra
    letI := M.quotientTopology
    IsClosed (M.bounded_aug_wordspan : Set M.augmentationQuotient) := by
  letI := M.instQuotientRing
  letI := M.instQuotientAlgebra
  letI := M.quotientTopology
  letI := M.quotientT2
  exact
    (M.setfin_boundedaug_wordspan (s := s) (n := n)).isClosed

def DCModel.DenseCanonunitQuotspan
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (M : DCModel (p := p) (Γ := Γ) s hs n) : Prop :=
  letI := M.instQuotientRing
  letI := M.instQuotientAlgebra
  letI := M.quotientTopology
  closure
    ((Submodule.span (ZMod p)
      (Set.range fun g : Γ =>
        M.quotientMap (M.canonicalUnit g : M.completedGroupAlgebra)) :
        Set M.augmentationQuotient)) = Set.univ

def DCModel.DenseAlgebraSpan
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (M : DCModel (p := p) (Γ := Γ) s hs n) : Prop :=
  letI := M.instRing
  letI := M.instAlgebra
  letI := M.instUniformSpace
  closure
    ((Submodule.span (ZMod p)
      (Set.range fun g : Γ => (M.canonicalUnit g : M.completedGroupAlgebra)) :
        Set M.completedGroupAlgebra)) = Set.univ

lemma GCAmbien.densecanon_unitalg_spanmodel
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (A : GCAmbien (p := p) (Γ := Γ) s hs)
    (Q : DCLayer
      (p := p) (Γ := Γ) (s := s) (hs := hs) n A)
    (J : DenseLazardIdentification (A.toCore Q))
    (hdense : A.DenseAlgebraSpan) :
    ((A.toCore Q).toModel J).DenseAlgebraSpan := by
  letI := A.instRing
  letI := A.instAlgebra
  letI := A.instUniformSpace
  simpa [GCAmbien.DenseAlgebraSpan,
    DCModel.DenseAlgebraSpan,
    GCAmbien.toCore,
    DCCore.toModel] using hdense

lemma DCModel.densecanon_unitquot_spanalgspan
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (M : DCModel (p := p) (Γ := Γ) s hs n)
    (hdense : M.DenseAlgebraSpan) :
    M.DenseCanonunitQuotspan := by
  letI := M.instRing
  letI := M.instAlgebra
  letI := M.instUniformSpace
  letI := M.instQuotientRing
  letI := M.instQuotientAlgebra
  letI := M.quotientTopology
  let algebraSpan : Submodule (ZMod p) M.completedGroupAlgebra :=
    Submodule.span (ZMod p)
      (Set.range fun g : Γ => (M.canonicalUnit g : M.completedGroupAlgebra))
  let quotientSpan : Submodule (ZMod p) M.augmentationQuotient :=
    Submodule.span (ZMod p)
      (Set.range fun g : Γ =>
        M.quotientMap (M.canonicalUnit g : M.completedGroupAlgebra))
  have himage_subset :
      M.quotientMap '' (algebraSpan : Set M.completedGroupAlgebra) ⊆
        (quotientSpan : Set M.augmentationQuotient) := by
    have himage_range :
        M.quotientMap.toLinearMap ''
            (Set.range fun g : Γ =>
              (M.canonicalUnit g : M.completedGroupAlgebra)) =
          Set.range fun g : Γ =>
            M.quotientMap (M.canonicalUnit g : M.completedGroupAlgebra) := by
      ext y
      constructor
      · rintro ⟨x, ⟨g, rfl⟩, rfl⟩
        exact ⟨g, rfl⟩
      · rintro ⟨g, rfl⟩
        exact ⟨(M.canonicalUnit g : M.completedGroupAlgebra), ⟨g, rfl⟩, rfl⟩
    rintro y ⟨x, hx, rfl⟩
    have hximage :
        M.quotientMap.toLinearMap x ∈
          Submodule.span (ZMod p)
            (M.quotientMap.toLinearMap ''
              (Set.range fun g : Γ =>
                (M.canonicalUnit g : M.completedGroupAlgebra))) :=
      (Submodule.image_span_subset_span
        M.quotientMap.toLinearMap
        (Set.range fun g : Γ =>
          (M.canonicalUnit g : M.completedGroupAlgebra))) ⟨x, hx, rfl⟩
    rw [himage_range] at hximage
    simpa [quotientSpan] using hximage
  apply Set.eq_univ_iff_forall.mpr
  intro y
  rcases M.quotientMap_surjective y with ⟨x, rfl⟩
  have hx : x ∈ closure (algebraSpan : Set M.completedGroupAlgebra) := by
    rw [show closure (algebraSpan : Set M.completedGroupAlgebra) = Set.univ by
      simpa [DCModel.DenseAlgebraSpan,
        algebraSpan] using hdense]
    exact Set.mem_univ x
  have hquotient_image :
      M.quotientMap x ∈
        closure (M.quotientMap '' (algebraSpan : Set M.completedGroupAlgebra)) :=
    mem_closure_image M.quotientMap_continuous.continuousAt hx
  exact closure_mono himage_subset hquotient_image

def DCModel.CanonunitSuboneBoundedspan
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (M : DCModel (p := p) (Γ := Γ) s hs n) : Prop :=
  letI := M.instRing
  letI := M.instQuotientRing
  letI := M.instQuotientAlgebra
  ∀ g : Γ,
    M.quotientMap ((M.canonicalUnit g : M.completedGroupAlgebra) - 1) ∈
      M.bounded_aug_wordspan

lemma DCModel.quotmap_eqzero_levelzero
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (M : DCModel (p := p) (Γ := Γ) s hs n)
    (hn : n = 0)
    (x : M.completedGroupAlgebra) :
    letI := M.instRing
    letI := M.instAlgebra
    letI := M.instQuotientRing
    letI := M.instQuotientAlgebra
    M.quotientMap x = 0 := by
  subst n
  letI := M.instRing
  letI := M.instAlgebra
  letI := M.instQuotientRing
  letI := M.instQuotientAlgebra
  have hxker : x ∈ RingHom.ker M.quotientMap.toRingHom := by
    rw [M.quotientMap_ker]
    rw [Submodule.pow_zero, Ideal.one_eq_top]
    trivial
  exact RingHom.mem_ker.mp hxker

lemma DCModel.quotmap_unitsubeq_zerolevelzero
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (M : DCModel (p := p) (Γ := Γ) s hs n)
    (hn : n = 0)
    (g : Γ) :
    letI := M.instRing
    letI := M.instAlgebra
    letI := M.instQuotientRing
    letI := M.instQuotientAlgebra
    M.quotientMap ((M.canonicalUnit g : M.completedGroupAlgebra) - 1) = 0 := by
  letI := M.instRing
  letI := M.instAlgebra
  letI := M.instQuotientRing
  letI := M.instQuotientAlgebra
  exact M.quotmap_eqzero_levelzero (s := s) (n := n) hn
    ((M.canonicalUnit g : M.completedGroupAlgebra) - 1)

lemma DCModel.canonunit_subonebounded_spanlevelzero
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (M : DCModel (p := p) (Γ := Γ) s hs n)
    (hn : n = 0) :
    M.CanonunitSuboneBoundedspan := by
  letI := M.instRing
  letI := M.instAlgebra
  letI := M.instQuotientRing
  letI := M.instQuotientAlgebra
  intro g
  have hzero :
      M.quotientMap ((M.canonicalUnit g : M.completedGroupAlgebra) - 1) = 0 :=
    M.quotmap_unitsubeq_zerolevelzero
      (s := s) (n := n) hn g
  rw [hzero]
  exact M.bounded_aug_wordspan.zero_mem

def DCModel.PoscanonUnitsubOneboundedspan
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (M : DCModel (p := p) (Γ := Γ) s hs n) : Prop :=
  letI := M.instRing
  letI := M.instQuotientRing
  letI := M.instQuotientAlgebra
  n ≠ 0 →
    ∀ g : Γ,
      M.quotientMap ((M.canonicalUnit g : M.completedGroupAlgebra) - 1) ∈
        M.bounded_aug_wordspan

def DCModel.PosdenseSubgroupsubOneboundedspan
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (M : DCModel (p := p) (Γ := Γ) s hs n) : Prop :=
  letI := M.instRing
  letI := M.instQuotientRing
  letI := M.instQuotientAlgebra
  n ≠ 0 →
    ∀ g : Γ,
      g ∈ Subgroup.closure (Set.range s) →
        M.quotientMap ((M.canonicalUnit g : M.completedGroupAlgebra) - 1) ∈
          M.bounded_aug_wordspan

lemma DCModel.quotmapsigned_wordelementnil_subonemem
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (M : DCModel (p := p) (Γ := Γ) s hs n) :
    letI := M.instRing
    letI := M.instQuotientRing
    letI := M.instQuotientAlgebra
    M.quotientMap
        ((M.canonicalUnit (generatorsSignedElement s []) :
          M.completedGroupAlgebra) - 1) ∈
      M.bounded_aug_wordspan := by
  letI := M.instRing
  letI := M.instQuotientRing
  letI := M.instQuotientAlgebra
  have hzero :
      M.quotientMap
          ((M.canonicalUnit (generatorsSignedElement s []) :
            M.completedGroupAlgebra) - 1) = 0 := by
    simp [generatorsSignedElement]
  rw [hzero]
  exact M.bounded_aug_wordspan.zero_mem

lemma DCModel.quotmapsigned_wordelemsing_subonemem
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (M : DCModel (p := p) (Γ := Γ) s hs n)
    (hn : n ≠ 0)
    (a : denseSignedLetter d) :
    letI := M.instRing
    letI := M.instQuotientRing
    letI := M.instQuotientAlgebra
    M.quotientMap
        ((M.canonicalUnit (generatorsSignedElement s [a]) :
          M.completedGroupAlgebra) - 1) ∈
      M.bounded_aug_wordspan := by
  letI := M.instRing
  letI := M.instQuotientRing
  letI := M.instQuotientAlgebra
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn
  have hletter :
      M.signedAugmentationLetter (s := s) a ∈
        M.bounded_aug_wordspan :=
    M.signedaug_lettermem_boundedspan (s := s) (n := n) hnpos a
  simpa [generatorsSignedElement,
    DCModel.signedAugmentationLetter] using hletter

lemma DCModel.signedaug_lettermul_memspanlt
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (M : DCModel (p := p) (Γ := Γ) s hs n)
    (a : denseSignedLetter d)
    (v : denseBoundedIndex d n)
    (hv : v.1.1 < n) :
    letI := M.instQuotientRing
    letI := M.instQuotientAlgebra
    M.signedAugmentationLetter (s := s) a *
        M.boundedAugmentationWord (s := s) (n := n) v ∈
      M.bounded_aug_wordspan := by
  letI := M.instQuotientRing
  letI := M.instQuotientAlgebra
  have hmem :
      M.boundedAugmentationWord (s := s) (n := n)
          (denseConsBounded a v hv) ∈
        M.bounded_aug_wordspan :=
    M.bounded_augword_memspan
      (s := s) (n := n) (denseConsBounded a v hv)
  simpa using hmem

lemma DCModel.canonunit_subone_memaugideal
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (M : DCModel (p := p) (Γ := Γ) s hs n)
    (x : Γ) :
    letI := M.instRing
    (M.canonicalUnit x : M.completedGroupAlgebra) - 1 ∈ M.augmentationIdeal := by
  letI := M.instRing
  letI := M.instAlgebra
  rw [M.augmentation_ideal_ker]
  change
    M.augmentationMap.toRingHom
        ((M.canonicalUnit x : M.completedGroupAlgebra) - 1) = 0
  simp [map_sub, M.canonicalUnit_augmentation x]

lemma DCModel.signedaug_factormem_augideal
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (M : DCModel (p := p) (Γ := Γ) s hs n)
    (a : denseSignedLetter d) :
    letI := M.instRing
    (M.canonicalUnit (generatorsLetterElement s a) :
        M.completedGroupAlgebra) - 1 ∈
      M.augmentationIdeal := by
  letI := M.instRing
  letI := M.instAlgebra
  exact
    M.canonunit_subone_memaugideal
      (s := s) (n := n) (generatorsLetterElement s a)

lemma DCModel.signedaug_factorsprod_mempower
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (M : DCModel (p := p) (Γ := Γ) s hs n)
    (w : List (denseSignedLetter d)) :
    letI := M.instRing
    (w.map fun a =>
        (M.canonicalUnit (generatorsLetterElement s a) :
            M.completedGroupAlgebra) - 1).prod ∈
      M.augmentationIdeal ^ w.length := by
  letI := M.instRing
  letI := M.instAlgebra
  letI : M.augmentationIdeal.IsTwoSided := by
    rw [M.augmentation_ideal_ker]
    infer_instance
  induction w with
  | nil =>
      rw [List.map_nil, List.prod_nil, List.length_nil]
      rw [Submodule.pow_zero, Ideal.one_eq_top]
      trivial
  | cons a w ih =>
      let head : M.completedGroupAlgebra :=
        (M.canonicalUnit (generatorsLetterElement s a) :
            M.completedGroupAlgebra) - 1
      let tail : M.completedGroupAlgebra :=
        (w.map fun b =>
          (M.canonicalUnit (generatorsLetterElement s b) :
              M.completedGroupAlgebra) - 1).prod
      have hhead_one : head ∈ M.augmentationIdeal ^ 1 := by
        have hhead : head ∈ M.augmentationIdeal := by
          dsimp [head]
          exact M.signedaug_factormem_augideal
            (s := s) (n := n) a
        simpa [Submodule.pow_one] using hhead
      have htail : tail ∈ M.augmentationIdeal ^ w.length := by
        dsimp [tail]
        exact ih
      have hmul :
          head * tail ∈ M.augmentationIdeal ^ (1 + w.length) := by
        rw [Ideal.IsTwoSided.pow_add (I := M.augmentationIdeal) 1 w.length]
        exact Ideal.mul_mem_mul hhead_one htail
      simpa [head, tail, Nat.add_comm] using hmul

lemma DCModel.quotmap_signedaug_factorsprodlist
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (M : DCModel (p := p) (Γ := Γ) s hs n)
    (w : List (denseSignedLetter d)) :
    letI := M.instRing
    letI := M.instAlgebra
    letI := M.instQuotientRing
    letI := M.instQuotientAlgebra
    M.quotientMap
        ((w.map fun a =>
          (M.canonicalUnit (generatorsLetterElement s a) :
              M.completedGroupAlgebra) - 1).prod) =
      (w.map fun a => M.signedAugmentationLetter (s := s) a).prod := by
  letI := M.instRing
  letI := M.instAlgebra
  letI := M.instQuotientRing
  letI := M.instQuotientAlgebra
  induction w with
  | nil =>
      simp [DCModel.signedAugmentationLetter]
  | cons a w ih =>
      simp [DCModel.signedAugmentationLetter,
        map_mul, ih]

lemma DCModel.quotmap_signedaug_factorsprod
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (M : DCModel (p := p) (Γ := Γ) s hs n)
    (w : denseBoundedIndex d n) :
    letI := M.instRing
    letI := M.instQuotientRing
    M.quotientMap
        ((w.2.toList.map fun a =>
          (M.canonicalUnit (generatorsLetterElement s a) :
              M.completedGroupAlgebra) - 1).prod) =
      M.boundedAugmentationWord (s := s) (n := n) w := by
  letI := M.instRing
  letI := M.instAlgebra
  letI := M.instQuotientRing
  letI := M.instQuotientAlgebra
  simpa [DCModel.boundedAugmentationWord] using
    M.quotmap_signedaug_factorsprodlist (s := s) (n := n) w.2.toList

lemma DCModel.signedaug_lettermuleq_quotmapcons
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (M : DCModel (p := p) (Γ := Γ) s hs n)
    (a : denseSignedLetter d)
    (v : denseBoundedIndex d n) :
    letI := M.instRing
    letI := M.instAlgebra
    letI := M.instQuotientRing
    letI := M.instQuotientAlgebra
    M.signedAugmentationLetter (s := s) a *
        M.boundedAugmentationWord (s := s) (n := n) v =
      M.quotientMap
        (((a :: v.2.toList).map fun b =>
          (M.canonicalUnit (generatorsLetterElement s b) :
              M.completedGroupAlgebra) - 1).prod) := by
  letI := M.instRing
  letI := M.instAlgebra
  letI := M.instQuotientRing
  letI := M.instQuotientAlgebra
  have hlist :
      M.quotientMap
          (((a :: v.2.toList).map fun b =>
            (M.canonicalUnit (generatorsLetterElement s b) :
                M.completedGroupAlgebra) - 1).prod) =
        ((a :: v.2.toList).map fun b =>
          M.signedAugmentationLetter (s := s) b).prod :=
    M.quotmap_signedaug_factorsprodlist
      (s := s) (n := n) (a :: v.2.toList)
  simpa [DCModel.boundedAugmentationWord] using hlist.symm

lemma DCModel.signedaug_lettermul_memspantop
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (M : DCModel (p := p) (Γ := Γ) s hs n)
    (a : denseSignedLetter d)
    (v : denseBoundedIndex d n)
    (hv : n ≤ v.1.1) :
    letI := M.instQuotientRing
    letI := M.instQuotientAlgebra
    M.signedAugmentationLetter (s := s) a *
        M.boundedAugmentationWord (s := s) (n := n) v ∈
      M.bounded_aug_wordspan := by
  letI := M.instRing
  letI := M.instAlgebra
  letI := M.instQuotientRing
  letI := M.instQuotientAlgebra
  let w : List (denseSignedLetter d) := a :: v.2.toList
  have hprod_power :
      (w.map fun b =>
          (M.canonicalUnit (generatorsLetterElement s b) :
              M.completedGroupAlgebra) - 1).prod ∈
        M.augmentationIdeal ^ w.length :=
    M.signedaug_factorsprod_mempower (s := s) (n := n) w
  have hv_len : v.2.toList.length = v.1.1 := by
    simp
  have hdegree_tail : n ≤ v.2.toList.length := by
    simpa [hv_len] using hv
  have hdegree : n ≤ w.length := by
    dsimp [w]
    exact Nat.le_trans hdegree_tail (Nat.le_succ v.2.toList.length)
  have hprod_power_n :
      (w.map fun b =>
          (M.canonicalUnit (generatorsLetterElement s b) :
              M.completedGroupAlgebra) - 1).prod ∈
        M.augmentationIdeal ^ n :=
    dense_lazard_augmentation
      (I := M.augmentationIdeal) (m := w.length) (n := n) hdegree hprod_power
  have hquotient_zero :
      M.quotientMap
          ((w.map fun b =>
            (M.canonicalUnit (generatorsLetterElement s b) :
                M.completedGroupAlgebra) - 1).prod) = 0 := by
    have hker :
        (w.map fun b =>
            (M.canonicalUnit (generatorsLetterElement s b) :
                M.completedGroupAlgebra) - 1).prod ∈
          RingHom.ker M.quotientMap.toRingHom := by
      rw [M.quotientMap_ker]
      exact hprod_power_n
    exact RingHom.mem_ker.mp hker
  have hmul_eq :
      M.signedAugmentationLetter (s := s) a *
          M.boundedAugmentationWord (s := s) (n := n) v =
        M.quotientMap
          ((w.map fun b =>
            (M.canonicalUnit (generatorsLetterElement s b) :
                M.completedGroupAlgebra) - 1).prod) := by
    dsimp [w]
    exact
      M.signedaug_lettermuleq_quotmapcons
        (s := s) (n := n) a v
  rw [hmul_eq, hquotient_zero]
  exact M.bounded_aug_wordspan.zero_mem

lemma DCModel.signedaug_lettmulboun_wordmemspan
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (M : DCModel (p := p) (Γ := Γ) s hs n)
    (_hn : n ≠ 0)
    (a : denseSignedLetter d)
    (v : denseBoundedIndex d n) :
    letI := M.instQuotientRing
    letI := M.instQuotientAlgebra
    M.signedAugmentationLetter (s := s) a *
        M.boundedAugmentationWord (s := s) (n := n) v ∈
      M.bounded_aug_wordspan := by
  letI := M.instQuotientRing
  letI := M.instQuotientAlgebra
  by_cases hv : v.1.1 < n
  · exact
      M.signedaug_lettermul_memspanlt
        (s := s) (n := n) a v hv
  · have hvtop : n ≤ v.1.1 := le_of_not_gt hv
    exact
      M.signedaug_lettermul_memspantop
        (s := s) (n := n) a v hvtop

lemma DCModel.signedaug_lettermul_memboundedspan
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (M : DCModel (p := p) (Γ := Γ) s hs n)
    (hn : n ≠ 0)
    (a : denseSignedLetter d)
    {x : M.augmentationQuotient}
    (hx : x ∈ M.bounded_aug_wordspan) :
    letI := M.instQuotientRing
    letI := M.instQuotientAlgebra
    M.signedAugmentationLetter (s := s) a * x ∈
      M.bounded_aug_wordspan := by
  letI := M.instQuotientRing
  letI := M.instQuotientAlgebra
  let S : Set M.augmentationQuotient :=
    Set.range fun v : ULift.{u} (denseBoundedIndex d n) =>
      M.boundedAugmentationWord (s := s) (n := n) v.down
  have hxspan : x ∈ Submodule.span (ZMod p) S := by
    simpa [DCModel.bounded_aug_wordspan, S] using hx
  change
    M.signedAugmentationLetter (s := s) a * x ∈
      Submodule.span (ZMod p) S
  refine Submodule.span_induction
    (s := S)
    (p := fun y _ =>
      M.signedAugmentationLetter (s := s) a * y ∈
        Submodule.span (ZMod p) S)
    ?mem ?zero ?add ?smul hxspan
  · intro y hy
    rcases hy with ⟨v, rfl⟩
    simpa [S] using
      M.signedaug_lettmulboun_wordmemspan
        (s := s) (n := n) hn a v.down
  · change M.signedAugmentationLetter (s := s) a * 0 ∈
      Submodule.span (ZMod p) S
    rw [mul_zero]
    exact Submodule.zero_mem _
  · intro x y _hx _hy hx_mem hy_mem
    change M.signedAugmentationLetter (s := s) a * (x + y) ∈
      Submodule.span (ZMod p) S
    rw [mul_add]
    exact Submodule.add_mem _ hx_mem hy_mem
  · intro c x _hx hx_mem
    change M.signedAugmentationLetter (s := s) a * (c • x) ∈
      Submodule.span (ZMod p) S
    rw [Algebra.mul_smul_comm]
    exact Submodule.smul_mem _ c hx_mem

lemma DCModel.quotmap_signwordelem_consproducteq
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (M : DCModel (p := p) (Γ := Γ) s hs n)
    (a : denseSignedLetter d)
    (w : List (denseSignedLetter d)) :
    letI := M.instRing
    letI := M.instQuotientRing
    M.quotientMap
        (((M.canonicalUnit (generatorsLetterElement s a) :
            M.completedGroupAlgebra) - 1) *
          ((M.canonicalUnit (generatorsSignedElement s w) :
            M.completedGroupAlgebra) - 1)) =
      M.signedAugmentationLetter (s := s) a *
        M.quotientMap
          ((M.canonicalUnit (generatorsSignedElement s w) :
            M.completedGroupAlgebra) - 1) := by
  letI := M.instRing
  letI := M.instQuotientRing
  rw [map_mul]
  rfl

lemma DCModel.quotmap_signwordelem_consproductmem
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (M : DCModel (p := p) (Γ := Γ) s hs n)
    (hn : n ≠ 0)
    (a : denseSignedLetter d)
    (w : List (denseSignedLetter d))
    (htail :
      letI := M.instRing
      letI := M.instQuotientRing
      letI := M.instQuotientAlgebra
      M.quotientMap
          ((M.canonicalUnit (generatorsSignedElement s w) :
            M.completedGroupAlgebra) - 1) ∈
        M.bounded_aug_wordspan) :
    letI := M.instRing
    letI := M.instQuotientRing
    letI := M.instQuotientAlgebra
    M.quotientMap
        (((M.canonicalUnit (generatorsLetterElement s a) :
            M.completedGroupAlgebra) - 1) *
          ((M.canonicalUnit (generatorsSignedElement s w) :
            M.completedGroupAlgebra) - 1)) ∈
      M.bounded_aug_wordspan := by
  letI := M.instRing
  letI := M.instQuotientRing
  letI := M.instQuotientAlgebra
  rw [M.quotmap_signwordelem_consproducteq (s := s) (n := n) a w]
  exact
    M.signedaug_lettermul_memboundedspan
      (s := s) (n := n) hn a htail

lemma DCModel.quotmapsigned_wordelementcons_subonemem
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (M : DCModel (p := p) (Γ := Γ) s hs n)
    (hn : n ≠ 0)
    (a : denseSignedLetter d)
    (w : List (denseSignedLetter d))
    (htail :
      letI := M.instRing
      letI := M.instQuotientRing
      letI := M.instQuotientAlgebra
      M.quotientMap
          ((M.canonicalUnit (generatorsSignedElement s w) :
            M.completedGroupAlgebra) - 1) ∈
        M.bounded_aug_wordspan) :
    letI := M.instRing
    letI := M.instQuotientRing
    letI := M.instQuotientAlgebra
    M.quotientMap
        ((M.canonicalUnit (generatorsSignedElement s (a :: w)) :
          M.completedGroupAlgebra) - 1) ∈
      M.bounded_aug_wordspan := by
  letI := M.instRing
  letI := M.instQuotientRing
  letI := M.instQuotientAlgebra
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn
  have hletter :
      M.quotientMap
          ((M.canonicalUnit (generatorsLetterElement s a) :
            M.completedGroupAlgebra) - 1) ∈
        M.bounded_aug_wordspan := by
    simpa [DCModel.signedAugmentationLetter] using
      M.signedaug_lettermem_boundedspan (s := s) (n := n) hnpos a
  have hproduct :
      M.quotientMap
          (((M.canonicalUnit (generatorsLetterElement s a) :
              M.completedGroupAlgebra) - 1) *
            ((M.canonicalUnit (generatorsSignedElement s w) :
              M.completedGroupAlgebra) - 1)) ∈
        M.bounded_aug_wordspan :=
    M.quotmap_signwordelem_consproductmem
      (s := s) (n := n) hn a w htail
  have hsum :
      M.quotientMap
          (((M.canonicalUnit (generatorsLetterElement s a) :
              M.completedGroupAlgebra) - 1) *
            ((M.canonicalUnit (generatorsSignedElement s w) :
              M.completedGroupAlgebra) - 1)) +
        M.quotientMap
          ((M.canonicalUnit (generatorsLetterElement s a) :
            M.completedGroupAlgebra) - 1) +
        M.quotientMap
          ((M.canonicalUnit (generatorsSignedElement s w) :
            M.completedGroupAlgebra) - 1) ∈
        M.bounded_aug_wordspan :=
    M.bounded_aug_wordspan.add_mem
      (M.bounded_aug_wordspan.add_mem hproduct hletter)
      htail
  have hidentity :
      (M.canonicalUnit (generatorsSignedElement s (a :: w)) :
          M.completedGroupAlgebra) - 1 =
        ((M.canonicalUnit (generatorsLetterElement s a) :
            M.completedGroupAlgebra) - 1) *
          ((M.canonicalUnit (generatorsSignedElement s w) :
            M.completedGroupAlgebra) - 1) +
        ((M.canonicalUnit (generatorsLetterElement s a) :
            M.completedGroupAlgebra) - 1) +
        ((M.canonicalUnit (generatorsSignedElement s w) :
            M.completedGroupAlgebra) - 1) := by
    rw [generators_element_cons]
    simp only [map_mul, Units.val_mul]
    noncomm_ring
  rw [hidentity]
  simpa [map_add] using hsum

lemma DCModel.quotmap_signedwordone_memboundedspan
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (M : DCModel (p := p) (Γ := Γ) s hs n)
    (hn : n ≠ 0)
    (w : List (denseSignedLetter d)) :
    letI := M.instRing
    letI := M.instQuotientRing
    letI := M.instQuotientAlgebra
    M.quotientMap
        ((M.canonicalUnit (generatorsSignedElement s w) :
          M.completedGroupAlgebra) - 1) ∈
      M.bounded_aug_wordspan := by
  induction w with
  | nil =>
      exact M.quotmapsigned_wordelementnil_subonemem (s := s) (n := n)
  | cons a w ih =>
      exact M.quotmapsigned_wordelementcons_subonemem
        (s := s) (n := n) hn a w ih

lemma DCModel.posdense_subgroupspan_signedwords
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (M : DCModel (p := p) (Γ := Γ) s hs n) :
    M.PosdenseSubgroupsubOneboundedspan := by
  letI := M.instRing
  letI := M.instQuotientRing
  letI := M.instQuotientAlgebra
  intro hn g hg
  rcases generators_element_closure
      (s := s) hg with ⟨w, hw⟩
  have hword :
      M.quotientMap
          ((M.canonicalUnit (generatorsSignedElement s w) :
            M.completedGroupAlgebra) - 1) ∈
        M.bounded_aug_wordspan :=
    M.quotmap_signedwordone_memboundedspan
      (s := s) (n := n) hn w
  simpa [hw] using hword

lemma DCModel.posunit_subspan_densesubgroup
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (M : DCModel (p := p) (Γ := Γ) s hs n)
    (H : M.PosdenseSubgroupsubOneboundedspan) :
    M.PoscanonUnitsubOneboundedspan := by
  letI := M.instRing
  letI := M.instAlgebra
  letI := M.instUniformSpace
  letI := M.topologicalRing
  letI := M.instQuotientRing
  letI := M.instQuotientAlgebra
  letI := M.quotientTopology
  letI := M.quotientTopologicalRing
  intro hn g
  let f : Γ → M.augmentationQuotient := fun x =>
    M.quotientMap ((M.canonicalUnit x : M.completedGroupAlgebra) - 1)
  have hcanonical :
      Continuous fun x : Γ => (M.canonicalUnit x : M.completedGroupAlgebra) := by
    exact Units.continuous_val.comp M.canonicalUnit_continuous
  have hf : Continuous f := by
    have hsub :
        Continuous fun x : Γ =>
          (M.canonicalUnit x : M.completedGroupAlgebra) - 1 := by
      exact hcanonical.sub continuous_const
    exact M.quotientMap_continuous.comp hsub
  have hclosed_span :
      IsClosed (M.bounded_aug_wordspan : Set M.augmentationQuotient) :=
    M.closed_boundedaug_wordspan (s := s) (n := n)
  have hclosed_preimage :
      IsClosed (f ⁻¹' (M.bounded_aug_wordspan : Set M.augmentationQuotient)) :=
    hclosed_span.preimage hf
  have hdense :
      closure ((Subgroup.closure (Set.range s) : Subgroup Γ) : Set Γ) = Set.univ := by
    simpa [Subgroup.topologicalClosure_coe] using
      congrArg (fun H : Subgroup Γ => (H : Set Γ)) hs
  have hsubset :
      ((Subgroup.closure (Set.range s) : Subgroup Γ) : Set Γ) ⊆
        f ⁻¹' (M.bounded_aug_wordspan : Set M.augmentationQuotient) := by
    intro x hx
    exact H hn x hx
  have hclosure_subset :
      closure ((Subgroup.closure (Set.range s) : Subgroup Γ) : Set Γ) ⊆
        f ⁻¹' (M.bounded_aug_wordspan : Set M.augmentationQuotient) :=
    closure_minimal hsubset hclosed_preimage
  have hg :
      g ∈ closure ((Subgroup.closure (Set.range s) : Subgroup Γ) : Set Γ) := by
    rw [hdense]
    exact Set.mem_univ g
  exact hclosure_subset hg

lemma DCModel.canonunit_subonebounded_spaniffpos
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (M : DCModel (p := p) (Γ := Γ) s hs n) :
    M.CanonunitSuboneBoundedspan ↔
      M.PoscanonUnitsubOneboundedspan := by
  constructor
  · intro H _hn
    exact H
  · intro H
    by_cases hn : n = 0
    · exact M.canonunit_subonebounded_spanlevelzero (s := s) (n := n) hn
    · exact H hn

structure DCModel.BoundedWordspanRawinputs
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (M : DCModel (p := p) (Γ := Γ) s hs n) : Prop where
  algebra_span_dense : M.DenseAlgebraSpan
  canonical_sub_one : M.CanonunitSuboneBoundedspan

structure DCModel.BoundedwordSpanposRawinputs
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (M : DCModel (p := p) (Γ := Γ) s hs n) : Prop where
  algebra_span_dense : M.DenseAlgebraSpan
  sub_dense_subgroup :
    M.PosdenseSubgroupsubOneboundedspan

lemma DCModel.boundedword_spanrawinputs_posrawinputs
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (M : DCModel (p := p) (Γ := Γ) s hs n)
    (H : M.BoundedwordSpanposRawinputs) :
    M.BoundedWordspanRawinputs := by
  refine
    { algebra_span_dense := H.algebra_span_dense
      canonical_sub_one := ?_ }
  rw [M.canonunit_subonebounded_spaniffpos (s := s) (n := n)]
  exact M.posunit_subspan_densesubgroup
    (s := s) (n := n) H.sub_dense_subgroup

structure DCModel.BoundedWordspanProofinputs
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (M : DCModel (p := p) (Γ := Γ) s hs n) : Prop where
  canonical_span_dense : M.DenseCanonunitQuotspan
  canonical_sub_one :
    letI := M.instRing
    letI := M.instQuotientRing
    letI := M.instQuotientAlgebra
    ∀ g : Γ,
      M.quotientMap ((M.canonicalUnit g : M.completedGroupAlgebra) - 1) ∈
        M.bounded_aug_wordspan

lemma DCModel.boundedword_spanproof_inputsrawinputs
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (M : DCModel (p := p) (Γ := Γ) s hs n)
    (H : M.BoundedWordspanRawinputs) :
    M.BoundedWordspanProofinputs := by
  refine
    { canonical_span_dense :=
        M.densecanon_unitquot_spanalgspan
          (s := s) (n := n) H.algebra_span_dense
      canonical_sub_one := ?_ }
  letI := M.instRing
  letI := M.instQuotientRing
  letI := M.instQuotientAlgebra
  exact H.canonical_sub_one

lemma DCModel.quotmap_canonunit_memboundedspan
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (M : DCModel (p := p) (Γ := Γ) s hs n)
    (g : Γ)
    (hsub :
      letI := M.instRing
      letI := M.instQuotientRing
      letI := M.instQuotientAlgebra
      M.quotientMap ((M.canonicalUnit g : M.completedGroupAlgebra) - 1) ∈
        M.bounded_aug_wordspan) :
    letI := M.instRing
    letI := M.instQuotientRing
    letI := M.instQuotientAlgebra
    M.quotientMap (M.canonicalUnit g : M.completedGroupAlgebra) ∈
      M.bounded_aug_wordspan := by
  letI := M.instRing
  letI := M.instQuotientRing
  letI := M.instQuotientAlgebra
  have hone : (1 : M.augmentationQuotient) ∈ M.bounded_aug_wordspan :=
    M.onemem_boundedaug_wordspan (s := s) (n := n)
  have hsum :
      M.quotientMap ((M.canonicalUnit g : M.completedGroupAlgebra) - 1) + 1 ∈
        M.bounded_aug_wordspan :=
    M.bounded_aug_wordspan.add_mem hsub hone
  simpa using hsum

lemma DCModel.bounded_wordspan_proofinputs
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (M : DCModel (p := p) (Γ := Γ) s hs n)
    (H : M.BoundedWordspanProofinputs) :
    M.BoundedAugWordspan := by
  letI := M.instQuotientRing
  letI := M.instQuotientAlgebra
  letI := M.quotientTopology
  let canonicalSpan : Submodule (ZMod p) M.augmentationQuotient :=
    Submodule.span (ZMod p)
      (Set.range fun g : Γ =>
        M.quotientMap (M.canonicalUnit g : M.completedGroupAlgebra))
  have hcanonical_le : canonicalSpan ≤ M.bounded_aug_wordspan := by
    refine Submodule.span_le.mpr ?_
    rintro x ⟨g, rfl⟩
    exact
      M.quotmap_canonunit_memboundedspan
        (s := s) (n := n) g (H.canonical_sub_one g)
  have hclosure_subset :
      closure (canonicalSpan : Set M.augmentationQuotient) ⊆
        (M.bounded_aug_wordspan : Set M.augmentationQuotient) :=
    closure_minimal hcanonical_le
      (M.closed_boundedaug_wordspan (s := s) (n := n))
  refine le_antisymm le_top ?_
  intro x _hx
  have hxclosure : x ∈ closure (canonicalSpan : Set M.augmentationQuotient) := by
    rw [H.canonical_span_dense]
    exact Set.mem_univ x
  exact hclosure_subset hxclosure

lemma DCModel.findense_wordspan_boundedwordspan
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (M : DCModel (p := p) (Γ := Γ) s hs n)
    (hspan : M.BoundedAugWordspan) :
    M.FinDenseWordspan := by
  letI := M.instQuotientRing
  letI := M.instQuotientAlgebra
  let ι : Type u := ULift.{u} (denseBoundedIndex d n)
  have hι : Finite ι := by
    dsimp [ι]
    exact dense_bounded_index d n
  let w : ι → M.augmentationQuotient :=
    fun x => M.boundedAugmentationWord (s := s) (n := n) x.down
  have hw : Submodule.span (ZMod p) (Set.range w) = ⊤ := by
    simpa [DCModel.BoundedAugWordspan, ι, w]
      using hspan
  exact ⟨ι, hι, w, hw⟩

lemma dense_spanning_family
    {R : Type*} {M : Type*}
    [Semiring R] [AddCommMonoid M] [Module R M]
    {ι : Type*} [Finite ι]
    (w : ι → M)
    (hspan : Submodule.span R (Set.range w) = ⊤) :
    Module.Finite R M := by
  rw [Module.finite_def]
  exact
    Submodule.fg_def.mpr
      ⟨Set.range w, Set.finite_range w, hspan⟩

lemma DCModel.modulefin_findense_wordspan
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (M : DCModel (p := p) (Γ := Γ) s hs n)
    (hspan : M.FinDenseWordspan) :
    letI := M.instQuotientRing
    letI := M.instQuotientAlgebra
    Module.Finite (ZMod p) M.augmentationQuotient := by
  letI := M.instQuotientRing
  letI := M.instQuotientAlgebra
  rcases hspan with ⟨ι, hι, w, hw⟩
  letI : Finite ι := hι
  exact
    dense_spanning_family
      (R := ZMod p) (M := M.augmentationQuotient) w hw

lemma DCModel.finaug_quotfin_densewordspan
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (M : DCModel (p := p) (Γ := Γ) s hs n)
    (hspan : M.FinDenseWordspan) :
    Finite M.augmentationQuotient := by
  letI := M.instQuotientRing
  letI := M.instQuotientAlgebra
  haveI : Module.Finite (ZMod p) M.augmentationQuotient :=
    M.modulefin_findense_wordspan hspan
  haveI : Finite (ZMod p) :=
    dense_generators_zmod p
  exact Module.finite_of_finite (ZMod p)

lemma model_discrete_t
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} (s : Fin d → Γ)
    (hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤)
    (n : ℕ)
    (h :
      ∃ M : DCModel
          (p := p) (Γ := Γ) s hs n,
        Finite M.augmentationQuotient ∧
          (letI := M.quotientTopology
          T2Space M.augmentationQuotient)) :
    ∃ M : DCModel
        (p := p) (Γ := Γ) s hs n,
      Finite M.augmentationQuotient ∧
        (letI := M.quotientTopology
        DiscreteTopology M.quotientUnitMap.range) := by
  rcases h with ⟨M, hfinite, hT2⟩
  refine ⟨M, hfinite, ?_⟩
  exact
    completed_discrete_t
      (p := p) (Γ := Γ) (s := s) (hs := hs) (n := n) M hfinite hT2

end Submission
