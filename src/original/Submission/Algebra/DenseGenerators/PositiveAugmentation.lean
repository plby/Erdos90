import Mathlib
import Submission.Algebra.DenseGenerators.CanonicalAlgebra
import Submission.Topology.CompactTotallyDisconnected


open scoped Topology Pointwise

noncomputable section

namespace Submission

universe u
universe v w z

def GCAmbien.OpenAugPower
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (n : ℕ)
    (A : GCAmbien (p := p) (Γ := Γ) s hs) :
    Prop :=
  IsOpen ((A.augmentationIdeal ^ n : Ideal A.completedGroupAlgebra) :
    Set A.completedGroupAlgebra)

def GCAmbien.OpenPosAugpowers
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (A : GCAmbien (p := p) (Γ := Γ) s hs) :
    Prop :=
  ∀ {m : ℕ}, 1 < m → A.OpenAugPower m

lemma GCAmbien.openaug_poweriff_openaugpower
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (A : GCAmbien (p := p) (Γ := Γ) s hs) :
    IsOpen ((A.augmentationIdeal ^ n : Ideal A.completedGroupAlgebra) :
      Set A.completedGroupAlgebra) ↔
      A.OpenAugPower n := by
  constructor
  · intro hopen
    simpa [GCAmbien.OpenAugPower]
      using hopen
  · intro hopen
    simpa [GCAmbien.OpenAugPower]
      using hopen

lemma GCAmbien.openaug_poweropen_posaugpowers
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (A : GCAmbien (p := p) (Γ := Γ) s hs)
    (H : A.OpenPosAugpowers)
    (hn : 1 < n) :
    A.OpenAugPower n := by
  have hsingle : A.OpenAugPower n := H hn
  exact hsingle

def GCAmbien.FinContposAugtruncations
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (A : GCAmbien (p := p) (Γ := Γ) s hs) :
    Prop :=
  ∀ {m : ℕ}, 1 < m → Nonempty (A.FCAugtru m)

def GCAmbien.FinAlgposAugtruncations
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (A : GCAmbien (p := p) (Γ := Γ) s hs) :
    Prop :=
  ∀ {m : ℕ}, 1 < m → Nonempty (A.FAAugtru m)

def GCAmbien.ClosedPosAugpowers
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (A : GCAmbien (p := p) (Γ := Γ) s hs) :
    Prop :=
  ∀ {m : ℕ}, 1 < m → A.ClosedAugPower m

def GCAmbien.ContPosaugPowerkernels
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (A : GCAmbien (p := p) (Γ := Γ) s hs) :
    Prop :=
  ∀ {m : ℕ}, 1 < m → Nonempty (A.ContAugPowerkernel m)

lemma GCAmbien.nonemptycont_augpowerpos_augpowerkernels
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {m : ℕ}
    (A : GCAmbien (p := p) (Γ := Γ) s hs)
    (Hkernels : A.ContPosaugPowerkernels)
    (hm : 1 < m) :
    Nonempty (A.ContAugPowerkernel m) := by
  have hkernel : Nonempty (A.ContAugPowerkernel m) :=
    Hkernels hm
  exact hkernel

lemma GCAmbien.closedaug_powerclosed_posaugpowers
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {m : ℕ}
    (A : GCAmbien (p := p) (Γ := Γ) s hs)
    (Hclosed : A.ClosedPosAugpowers)
    (hm : 1 < m) :
    A.ClosedAugPower m := by
  have hclosed : A.ClosedAugPower m := Hclosed hm
  exact hclosed

lemma GCAmbien.closedpos_augpos_augpowerkernels
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (A : GCAmbien (p := p) (Γ := Γ) s hs)
    (Hkernels : A.ContPosaugPowerkernels) :
    A.ClosedPosAugpowers := by
  intro m hm
  rcases
      A.nonemptycont_augpowerpos_augpowerkernels
        (p := p) (Γ := Γ) (s := s) (hs := hs) Hkernels hm with
    ⟨K⟩
  have hclosed : A.ClosedAugPower m :=
    A.closed_augpower_contkernel K
  exact hclosed

def GCAmbien.FinPosIdealquots
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (A : GCAmbien (p := p) (Γ := Γ) s hs) :
    Prop :=
  ∀ {m : ℕ}, 1 < m →
    Finite (A.completedGroupAlgebra ⧸
      (A.augmentationIdeal ^ m : Ideal A.completedGroupAlgebra))

lemma GCAmbien.finpos_idealclosed_posaugpowers
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (A : GCAmbien (p := p) (Γ := Γ) s hs)
    (hdense : A.DenseAlgebraSpan)
    (Hclosed : A.ClosedPosAugpowers) :
    A.FinPosIdealquots := by
  intro m hm
  have hm_two : 2 ≤ m := Nat.succ_le_of_lt hm
  have hclosed : A.ClosedAugPower m :=
    A.closedaug_powerclosed_posaugpowers
      (p := p) (Γ := Γ) (s := s) (hs := hs) Hclosed hm
  exact
    A.finideal_quotaug_powertwole
      (p := p) (Γ := Γ) (s := s) (hs := hs) hdense hclosed hm_two

lemma GCAmbien.openpos_augclosed_posaugpowers
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (A : GCAmbien (p := p) (Γ := Γ) s hs)
    (hdense : A.DenseAlgebraSpan)
    (Hclosed : A.ClosedPosAugpowers) :
    A.OpenPosAugpowers := by
  intro m hm
  have hm_two : 2 ≤ m := Nat.succ_le_of_lt hm
  have hclosed : A.ClosedAugPower m :=
    A.closedaug_powerclosed_posaugpowers
      (p := p) (Γ := Γ) (s := s) (hs := hs) Hclosed hm
  have hopen_raw :
      IsOpen ((A.augmentationIdeal ^ m : Ideal A.completedGroupAlgebra) :
        Set A.completedGroupAlgebra) :=
    A.openaug_powerpower_twole
      (p := p) (Γ := Γ) (s := s) (hs := hs) hdense hclosed hm_two
  exact
    (A.openaug_poweriff_openaugpower
      (p := p) (Γ := Γ) (s := s) (hs := hs)).1 hopen_raw

def GCAmbien.FinPosalgAugquots
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (A : GCAmbien (p := p) (Γ := Γ) s hs) :
    Prop :=
  ∀ {m : ℕ}, 1 < m →
    ∃ Q :
      GAAug
        (p := p) (Γ := Γ) (s := s) (hs := hs) m A,
      Finite Q.augmentationQuotient

lemma GCAmbien.finalg_postruncations_finquots
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (A : GCAmbien (p := p) (Γ := Γ) s hs)
    (Hquot : A.FinPosalgAugquots) :
    A.FinAlgposAugtruncations := by
  intro m hm
  rcases Hquot hm with ⟨Q, hfiniteQ⟩
  letI : Finite Q.augmentationQuotient := hfiniteQ
  let T : A.FAAugtru m :=
    Q.fin_alg_augtrunc
  have hT : Nonempty (A.FAAugtru m) := ⟨T⟩
  exact hT

def GCAmbien.DiscretecontTopofinAlgpostrun
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (A : GCAmbien (p := p) (Γ := Γ) s hs) :
    Prop :=
  ∀ {m : ℕ}, 1 < m →
    ∀ T : A.FAAugtru m,
      Nonempty T.DiscreteContTopo

def GCAmbien.OpenkernelFinalgPostruncations
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (A : GCAmbien (p := p) (Γ := Γ) s hs) :
    Prop :=
  ∀ {m : ℕ}, 1 < m →
    ∀ T : A.FAAugtru m,
      IsOpen ((RingHom.ker T.probeMap : Ideal A.completedGroupAlgebra) :
        Set A.completedGroupAlgebra)

lemma GCAmbien.discretecont_topotruncations_openkernels
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (A : GCAmbien (p := p) (Γ := Γ) s hs)
    (Hopen : A.OpenkernelFinalgPostruncations) :
    A.DiscretecontTopofinAlgpostrun := by
  intro m hm T
  have hker_open :
      IsOpen ((RingHom.ker T.probeMap : Ideal A.completedGroupAlgebra) :
        Set A.completedGroupAlgebra) :=
    Hopen hm T
  have HTop : T.DiscreteContTopo :=
    T.discrete_conttopo_openker hker_open
  exact ⟨HTop⟩

lemma GCAmbien.fincont_postruncations_algtopo
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (A : GCAmbien (p := p) (Γ := Γ) s hs)
    (Halg : A.FinAlgposAugtruncations)
    (Htop : A.DiscretecontTopofinAlgpostrun) :
    A.FinContposAugtruncations := by
  intro m hm
  rcases Halg hm with ⟨Talg⟩
  rcases Htop hm Talg with ⟨HTop⟩
  let Tcont : A.FCAugtru m :=
    Talg.fin_cont_augtrunc HTop
  have hnonempty : Nonempty (A.FCAugtru m) := ⟨Tcont⟩
  exact hnonempty

lemma GCAmbien.open_posaug_powerslevelwise
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (A : GCAmbien (p := p) (Γ := Γ) s hs)
    (Hlevel :
      ∀ {m : ℕ}, 1 < m → A.OpenAugPower m) :
    A.OpenPosAugpowers := by
  intro m hm
  have hopen : A.OpenAugPower m :=
    Hlevel hm
  exact hopen

lemma GCAmbien.nonemptycont_augpower_openaugpower
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {m : ℕ}
    (A : GCAmbien (p := p) (Γ := Γ) s hs)
    (hopen : A.OpenAugPower m) :
    Nonempty (A.ContAugPowerkernel m) := by
  have hopen_raw :
      IsOpen ((A.augmentationIdeal ^ m : Ideal A.completedGroupAlgebra) :
        Set A.completedGroupAlgebra) :=
    (A.openaug_poweriff_openaugpower
      (p := p) (Γ := Γ) (s := s) (hs := hs)).2 hopen
  exact
    A.contaug_powerkernel_openaugpower
      (p := p) (Γ := Γ) (s := s) (hs := hs) hopen_raw

def GCAmbien.AugPowerNhds
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (A : GCAmbien (p := p) (Γ := Γ) s hs)
    (m : ℕ) :
    Prop :=
  ((A.augmentationIdeal ^ m : Ideal A.completedGroupAlgebra) :
      Set A.completedGroupAlgebra) ∈ nhds (0 : A.completedGroupAlgebra)

def GCAmbien.OpenaddSubgroucontainInaugpower
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (A : GCAmbien (p := p) (Γ := Γ) s hs)
    (m : ℕ) :
    Prop :=
  ∃ U : AddSubgroup A.completedGroupAlgebra,
    IsOpen ((U : AddSubgroup A.completedGroupAlgebra) :
      Set A.completedGroupAlgebra) ∧
      ((U : AddSubgroup A.completedGroupAlgebra) :
        Set A.completedGroupAlgebra) ⊆
        ((A.augmentationIdeal ^ m : Ideal A.completedGroupAlgebra) :
          Set A.completedGroupAlgebra)

lemma GCAmbien.augpower_nhdsopen_addsubgcont
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {m : ℕ}
    (A : GCAmbien (p := p) (Γ := Γ) s hs)
    (H : A.OpenaddSubgroucontainInaugpower m) :
    A.AugPowerNhds m := by
  rcases H with ⟨U, hUopen, hUsubset⟩
  have hzeroU :
      (0 : A.completedGroupAlgebra) ∈
        ((U : AddSubgroup A.completedGroupAlgebra) :
          Set A.completedGroupAlgebra) := by
    exact U.zero_mem
  have hUnhds :
      ((U : AddSubgroup A.completedGroupAlgebra) :
        Set A.completedGroupAlgebra) ∈
        nhds (0 : A.completedGroupAlgebra) := by
    exact hUopen.mem_nhds hzeroU
  exact
    Filter.mem_of_superset hUnhds (by
      intro x hx
      exact hUsubset hx)

lemma GCAmbien.openaug_poweropen_addsubgcont
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {m : ℕ}
    (A : GCAmbien (p := p) (Γ := Γ) s hs)
    (H : A.OpenaddSubgroucontainInaugpower m) :
    A.OpenAugPower m := by
  have hnhds : A.AugPowerNhds m :=
    A.augpower_nhdsopen_addsubgcont
      (p := p) (Γ := Γ) (s := s) (hs := hs) H
  have hnhds_add :
      (((A.augmentationIdeal ^ m : Ideal A.completedGroupAlgebra).toAddSubgroup :
          AddSubgroup A.completedGroupAlgebra) :
        Set A.completedGroupAlgebra) ∈ nhds (0 : A.completedGroupAlgebra) := by
    simpa [GCAmbien.AugPowerNhds]
      using hnhds
  have hopen_raw :
      IsOpen ((A.augmentationIdeal ^ m : Ideal A.completedGroupAlgebra) :
        Set A.completedGroupAlgebra) := by
    have hopen_add :
        IsOpen
          ((((A.augmentationIdeal ^ m : Ideal A.completedGroupAlgebra).toAddSubgroup :
              AddSubgroup A.completedGroupAlgebra) :
            Set A.completedGroupAlgebra)) :=
      AddSubgroup.isOpen_of_mem_nhds
        ((A.augmentationIdeal ^ m : Ideal A.completedGroupAlgebra).toAddSubgroup)
        hnhds_add
    simpa using hopen_add
  exact
    (A.openaug_poweriff_openaugpower
      (p := p) (Γ := Γ) (s := s) (hs := hs)).1 hopen_raw

lemma GCAmbien.openadd_subgroupaug_powernhds
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {m : ℕ}
    (A : GCAmbien (p := p) (Γ := Γ) s hs)
    (hnhds : A.AugPowerNhds m) :
    A.OpenaddSubgroucontainInaugpower m := by
  have hnhds_raw :
      ((A.augmentationIdeal ^ m : Ideal A.completedGroupAlgebra) :
          Set A.completedGroupAlgebra) ∈ nhds (0 : A.completedGroupAlgebra) := by
    simpa [GCAmbien.AugPowerNhds]
      using hnhds
  rcases
      nhds_compact_disconnected
        (R := A.completedGroupAlgebra) hnhds_raw with
    ⟨U, hUopen, hUsubset⟩
  have hcontained :
      ((U : AddSubgroup A.completedGroupAlgebra) :
          Set A.completedGroupAlgebra) ⊆
        ((A.augmentationIdeal ^ m : Ideal A.completedGroupAlgebra) :
          Set A.completedGroupAlgebra) := by
    intro x hx
    exact hUsubset hx
  exact ⟨U, hUopen, hcontained⟩

lemma GCAmbien.openadd_subgroupopen_augpower
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {m : ℕ}
    (A : GCAmbien (p := p) (Γ := Γ) s hs)
    (hopen : A.OpenAugPower m) :
    A.OpenaddSubgroucontainInaugpower m := by
  have hopen_raw :
      IsOpen ((A.augmentationIdeal ^ m : Ideal A.completedGroupAlgebra) :
        Set A.completedGroupAlgebra) :=
    (A.openaug_poweriff_openaugpower
      (p := p) (Γ := Γ) (s := s) (hs := hs)).2 hopen
  have hzero :
      (0 : A.completedGroupAlgebra) ∈
        ((A.augmentationIdeal ^ m : Ideal A.completedGroupAlgebra) :
          Set A.completedGroupAlgebra) := by
    exact (A.augmentationIdeal ^ m).zero_mem
  have hnhds : A.AugPowerNhds m :=
    by
      simpa [GCAmbien.AugPowerNhds]
        using hopen_raw.mem_nhds hzero
  exact
    A.openadd_subgroupaug_powernhds
      (p := p) (Γ := Γ) (s := s) (hs := hs) hnhds

lemma GCAmbien.openadd_subgroupiff_augpowernhds
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {m : ℕ}
    (A : GCAmbien (p := p) (Γ := Γ) s hs) :
    A.OpenaddSubgroucontainInaugpower m ↔
      A.AugPowerNhds m := by
  constructor
  · intro HopenSubgroup
    exact
      A.augpower_nhdsopen_addsubgcont
        (p := p) (Γ := Γ) (s := s) (hs := hs) HopenSubgroup
  · intro hnhds
    exact
      A.openadd_subgroupaug_powernhds
        (p := p) (Γ := Γ) (s := s) (hs := hs) hnhds

lemma GCAmbien.openadd_subgroupiff_openaugpower
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {m : ℕ}
    (A : GCAmbien (p := p) (Γ := Γ) s hs) :
    A.OpenaddSubgroucontainInaugpower m ↔
      A.OpenAugPower m := by
  constructor
  · intro HopenSubgroup
    exact
      A.openaug_poweropen_addsubgcont
        (p := p) (Γ := Γ) (s := s) (hs := hs) HopenSubgroup
  · intro hopen
    exact
      A.openadd_subgroupopen_augpower
        (p := p) (Γ := Γ) (s := s) (hs := hs) hopen

lemma GCAmbien.augpower_nhdsopen_augpower
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {m : ℕ}
    (A : GCAmbien (p := p) (Γ := Γ) s hs)
    (hopen : A.OpenAugPower m) :
    A.AugPowerNhds m := by
  have hopen_raw :
      IsOpen ((A.augmentationIdeal ^ m : Ideal A.completedGroupAlgebra) :
        Set A.completedGroupAlgebra) :=
    (A.openaug_poweriff_openaugpower
      (p := p) (Γ := Γ) (s := s) (hs := hs)).2 hopen
  have hzero :
      (0 : A.completedGroupAlgebra) ∈
        ((A.augmentationIdeal ^ m : Ideal A.completedGroupAlgebra) :
          Set A.completedGroupAlgebra) := by
    exact (A.augmentationIdeal ^ m).zero_mem
  simpa [GCAmbien.AugPowerNhds]
    using hopen_raw.mem_nhds hzero

lemma GCAmbien.openaug_poweraug_powernhds
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {m : ℕ}
    (A : GCAmbien (p := p) (Γ := Γ) s hs)
    (hnhds : A.AugPowerNhds m) :
    IsOpen ((A.augmentationIdeal ^ m : Ideal A.completedGroupAlgebra) :
      Set A.completedGroupAlgebra) := by
  have hnhds_add :
      (((A.augmentationIdeal ^ m : Ideal A.completedGroupAlgebra).toAddSubgroup :
          AddSubgroup A.completedGroupAlgebra) :
        Set A.completedGroupAlgebra) ∈ nhds (0 : A.completedGroupAlgebra) := by
    simpa [GCAmbien.AugPowerNhds]
      using hnhds
  have hopen_add :
      IsOpen
        ((((A.augmentationIdeal ^ m : Ideal A.completedGroupAlgebra).toAddSubgroup :
            AddSubgroup A.completedGroupAlgebra) :
          Set A.completedGroupAlgebra)) :=
    AddSubgroup.isOpen_of_mem_nhds
      ((A.augmentationIdeal ^ m : Ideal A.completedGroupAlgebra).toAddSubgroup)
      hnhds_add
  simpa using hopen_add

lemma GCAmbien.openaug_poweriff_augpowernhds
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {m : ℕ}
    (A : GCAmbien (p := p) (Γ := Γ) s hs) :
    A.OpenAugPower m ↔ A.AugPowerNhds m := by
  constructor
  · intro hopen
    exact
      A.augpower_nhdsopen_augpower
        (p := p) (Γ := Γ) (s := s) (hs := hs) hopen
  · intro hnhds
    have hopen_raw :
        IsOpen ((A.augmentationIdeal ^ m : Ideal A.completedGroupAlgebra) :
          Set A.completedGroupAlgebra) :=
      A.openaug_poweraug_powernhds
        (p := p) (Γ := Γ) (s := s) (hs := hs) hnhds
    exact
      (A.openaug_poweriff_openaugpower
        (p := p) (Γ := Γ) (s := s) (hs := hs)).1 hopen_raw

lemma GCAmbien.contpos_augpower_kernelslevelwi
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (A : GCAmbien (p := p) (Γ := Γ) s hs)
    (Hlevel :
      ∀ {m : ℕ}, 1 < m → Nonempty (A.ContAugPowerkernel m)) :
    A.ContPosaugPowerkernels := by
  intro m hm
  have hlevel :
      Nonempty (A.ContAugPowerkernel m) :=
    Hlevel hm
  exact hlevel

lemma GCAmbien.closedpos_auglevelwise_contkernels
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (A : GCAmbien (p := p) (Γ := Γ) s hs)
    (Hlevel :
      ∀ {m : ℕ}, 1 < m → Nonempty (A.ContAugPowerkernel m)) :
    A.ClosedPosAugpowers := by
  intro m hm
  have hkernel :
      Nonempty (A.ContAugPowerkernel m) :=
    Hlevel hm
  rcases hkernel with ⟨K⟩
  have hclosed : A.ClosedAugPower m :=
    A.closed_augpower_contkernel K
  exact hclosed

lemma GCAmbien.nonemptyfin_contaug_openaugpower
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (A : GCAmbien (p := p) (Γ := Γ) s hs)
    (hopen : A.OpenAugPower n) :
    Nonempty (A.FCAugtru n) := by
  have hopen_raw :
      IsOpen ((A.augmentationIdeal ^ n : Ideal A.completedGroupAlgebra) :
        Set A.completedGroupAlgebra) := by
    exact
      (A.openaug_poweriff_openaugpower
        (p := p) (Γ := Γ) (s := s) (hs := hs)).2 hopen
  exact
    A.existsfin_contaug_openaugpower
      (p := p) (Γ := Γ) (s := s) (hs := hs) hopen_raw

lemma GCAmbien.nonemptycont_augpower_finconttrunc
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (A : GCAmbien (p := p) (Γ := Γ) s hs)
    (hT : Nonempty (A.FCAugtru n)) :
    Nonempty (A.ContAugPowerkernel n) := by
  rcases hT with ⟨T⟩
  let K : A.ContAugPowerkernel n :=
    T.cont_aug_powerkernel
  have hK : Nonempty (A.ContAugPowerkernel n) := ⟨K⟩
  exact hK

lemma GCAmbien.closedaug_powernonempty_finconttrunc
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (A : GCAmbien (p := p) (Γ := Γ) s hs)
    (hT : Nonempty (A.FCAugtru n)) :
    A.ClosedAugPower n := by
  have hK : Nonempty (A.ContAugPowerkernel n) :=
    A.nonemptycont_augpower_finconttrunc
      (p := p) (Γ := Γ) (s := s) (hs := hs) hT
  have hclosed : A.ClosedAugPower n :=
    A.closedaug_powernonempty_contkernel hK
  exact hclosed

end Submission
