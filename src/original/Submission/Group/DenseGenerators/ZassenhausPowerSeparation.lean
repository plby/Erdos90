import Mathlib
import Submission.Group.DenseGenerators.ZassenhausPowerSubgroup


open scoped Topology Pointwise

noncomputable section

namespace Submission

universe u
universe v w z

/-- If a Zassenhaus term contains an open prime-power subgroup, then it is closed.

This isolates the formal topological part of the Nikolov-Segal route: the remaining hard input is
openness of the relevant power subgroup. -/
lemma filtration_closed_open
    {p : ℕ}
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {n j : ℕ}
    (hle : n ≤ p ^ j)
    (hopen : IsOpen ((powerSubgroup G (p ^ j) : Subgroup G) : Set G)) :
    IsClosed ((zassenhausFiltration p G n : Subgroup G) : Set G) := by
  let P : Subgroup G := powerSubgroup G (p ^ j)
  let D : Subgroup G := zassenhausFiltration p G n
  have hPD : P ≤ D := by
    simpa [P, D] using
      power_filtration_pow
        (p := p) (G := G) (n := n) (j := j) hle
  have hPopen : IsOpen (P : Set G) := by
    simpa [P] using hopen
  have hDnhds : (D : Set G) ∈ 𝓝 (1 : G) := by
    exact Filter.mem_of_superset (hPopen.mem_nhds P.one_mem) (by
      intro x hx
      exact hPD hx)
  have hDopen : IsOpen (D : Set G) := by
    exact Subgroup.isOpen_of_mem_nhds D hDnhds
  simpa [D] using D.isClosed_of_isOpen hDopen

/-- Closedness plus finite dense power-subgroup quotients give finite-quotient separation for
`D_n`.

This is the formal reduction from the target to the two power-subgroup inputs: closedness of
`Γ^m` and finiteness of the dense subgroup in `Γ / Γ^m`, for `1 < m`. -/
lemma dense_separates_data
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} (s : Fin d → Γ)
    (hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤)
    (hclosed :
      ∀ m : ℕ, 1 < m →
        IsClosed ((powerSubgroup Γ m : Subgroup Γ) : Set Γ))
    (hfinite_dense :
      ∀ m : ℕ, 1 < m →
        IsClosed ((powerSubgroup Γ m : Subgroup Γ) : Set Γ) →
        letI : (powerSubgroup Γ m).Normal := powerSubgroup_normal Γ m
        Finite
          (Subgroup.closure
            (Set.range
              (fun i : Fin d =>
                QuotientGroup.mk' (powerSubgroup Γ m) (s i))) :
            Subgroup (Γ ⧸ powerSubgroup Γ m)))
    {n : ℕ}
    (hn : 1 < n)
    {g : Γ}
    (hg : g ∉ zassenhausFiltration p Γ n) :
    ∃ N : OpenNormalSubgroup Γ,
      QuotientGroup.mk' N.toSubgroup g ∉
        zassenhausFiltration p (Γ ⧸ N.toSubgroup) n := by
  rcases exists_pow_ge p n with ⟨j, hjn⟩
  have hm : 1 < p ^ j := lt_of_lt_of_le hn hjn
  have hclosed_m : IsClosed ((powerSubgroup Γ (p ^ j) : Subgroup Γ) : Set Γ) :=
    hclosed (p ^ j) hm
  rcases
      dense_open_closed
        (Γ := Γ)
        s
        hs
        (p ^ j)
        hclosed_m
        (hfinite_dense (p ^ j) hm hclosed_m) with
    ⟨N, hN⟩
  exact
    ⟨N,
      separates_open_subgroup
        (p := p)
        (Γ := Γ)
        (n := n)
        (j := j)
        hjn
        N
        hN
        (g := g)
        hg⟩
/-- Closed power subgroups plus bounded-exponent Burnside imply finite-quotient separation for
`D_n`. -/
lemma
    separates_closed_burnside
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} (s : Fin d → Γ)
    (hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤)
    (hclosed :
      ∀ m : ℕ, 1 < m →
        IsClosed ((powerSubgroup Γ m : Subgroup Γ) : Set Γ))
    (hBurnside :
      ∀ m : ℕ, 1 < m →
        ∀ (G : Type u) [Group G],
          Group.FG G → (∀ x : G, x ^ m = 1) → Finite G)
    {n : ℕ}
    (hn : 1 < n)
    {g : Γ}
    (hg : g ∉ zassenhausFiltration p Γ n) :
    ∃ N : OpenNormalSubgroup Γ,
      QuotientGroup.mk' N.toSubgroup g ∉
        zassenhausFiltration p (Γ ⧸ N.toSubgroup) n := by
  exact
    dense_separates_data
      (p := p)
      (Γ := Γ)
      s
      hs
      hclosed
      (by
        intro m hm _hclosed_m
        exact
          bounded_exponent_burnside
            (Γ := Γ) s m (hBurnside m hm))
      hn
      (g := g)
      hg
/-- Closed power subgroups plus Burnside for groups with separating finite quotients imply
finite-quotient separation for `D_n`. -/
lemma
    gens_separating_burnside
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} (s : Fin d → Γ)
    (hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤)
    (hclosed :
      ∀ m : ℕ, 1 < m →
        IsClosed ((powerSubgroup Γ m : Subgroup Γ) : Set Γ))
    (hBurnside :
      ∀ m : ℕ, 1 < m →
        ∀ (G : Type u) [Group G],
          SFQuotie G →
            Group.FG G → (∀ x : G, x ^ m = 1) → Finite G)
    {n : ℕ}
    (hn : 1 < n)
    {g : Γ}
    (hg : g ∉ zassenhausFiltration p Γ n) :
    ∃ N : OpenNormalSubgroup Γ,
      QuotientGroup.mk' N.toSubgroup g ∉
        zassenhausFiltration p (Γ ⧸ N.toSubgroup) n := by
  exact
    dense_separates_data
      (p := p)
      (Γ := Γ)
      s
      hs
      hclosed
      (by
        intro m hm hclosed_m
        letI : (powerSubgroup Γ m).Normal := powerSubgroup_normal Γ m
        exact
          dense_separating_burnside
            (Γ := Γ)
            s
            m
            (dense_normal_separated
              (Γ := Γ)
              s
              m
              (separated_quotients_closed
                (Γ := Γ)
                (K := powerSubgroup Γ m)
                hclosed_m))
            (hBurnside m hm))
      hn
      (g := g)
      hg
/-- Closed power subgroups, residual finiteness of the power quotients, and the residually finite
bounded-exponent Burnside input imply finite-quotient separation for `D_n`. -/
lemma
    closed_residually_burnside
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} (s : Fin d → Γ)
    (hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤)
    (hclosed :
      ∀ m : ℕ, 1 < m →
        IsClosed ((powerSubgroup Γ m : Subgroup Γ) : Set Γ))
    (hRF :
      ∀ m : ℕ, 1 < m →
        IsClosed ((powerSubgroup Γ m : Subgroup Γ) : Set Γ) →
        letI : (powerSubgroup Γ m).Normal := powerSubgroup_normal Γ m
        Group.ResiduallyFinite (Γ ⧸ powerSubgroup Γ m))
    (hBurnside :
      ∀ m : ℕ, 1 < m →
        ∀ (G : Type u) [Group G] [Group.ResiduallyFinite G],
          Group.FG G → (∀ x : G, x ^ m = 1) → Finite G)
    {n : ℕ}
    (hn : 1 < n)
    {g : Γ}
    (hg : g ∉ zassenhausFiltration p Γ n) :
    ∃ N : OpenNormalSubgroup Γ,
      QuotientGroup.mk' N.toSubgroup g ∉
        zassenhausFiltration p (Γ ⧸ N.toSubgroup) n := by
  exact
    dense_separates_data
      (p := p)
      (Γ := Γ)
      s
      hs
      hclosed
      (by
        intro m hm hclosed_m
        exact
          residually_exponent_burnside
            (Γ := Γ) s m (hRF m hm hclosed_m) (hBurnside m hm))
      hn
      (g := g)
      hg
/-- Closed power subgroups and the residually finite bounded-exponent Burnside input imply
finite-quotient separation for `D_n`; residual finiteness of the power quotients is supplied by
closedness and profiniteness. -/
lemma
    gens_residually_burnside
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} (s : Fin d → Γ)
    (hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤)
    (hclosed :
      ∀ m : ℕ, 1 < m →
        IsClosed ((powerSubgroup Γ m : Subgroup Γ) : Set Γ))
    (hquot :
      ∀ m : ℕ, 1 < m →
        IsClosed ((powerSubgroup Γ m : Subgroup Γ) : Set Γ) →
        letI : (powerSubgroup Γ m).Normal := powerSubgroup_normal Γ m
        TotallyDisconnectedSpace (Γ ⧸ powerSubgroup Γ m))
    (hBurnside :
      ∀ m : ℕ, 1 < m →
        ∀ (G : Type u) [Group G] [Group.ResiduallyFinite G],
          Group.FG G → (∀ x : G, x ^ m = 1) → Finite G)
    {n : ℕ}
    (hn : 1 < n)
    {g : Γ}
    (hg : g ∉ zassenhausFiltration p Γ n) :
    ∃ N : OpenNormalSubgroup Γ,
      QuotientGroup.mk' N.toSubgroup g ∉
        zassenhausFiltration p (Γ ⧸ N.toSubgroup) n := by
  exact
    closed_residually_burnside
      (p := p)
      (Γ := Γ)
      s
      hs
      hclosed
      (by
        intro m hm hclosed_m
        exact
          power_residually_closed
            (Γ := Γ) m hclosed_m (hquot m hm hclosed_m))
      hBurnside
      hn
      (g := g)
      hg
/-- Finite-width power subgroups plus Burnside for groups with separating finite quotients imply
finite-quotient separation for `D_n`. -/
lemma
    width_separating_burnside
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ] [T2Space Γ]
    {d : ℕ} (s : Fin d → Γ)
    (hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤)
    (hwidth : ∀ m : ℕ, 1 < m → powerSubgroupWidth Γ m)
    (hBurnside :
      ∀ m : ℕ, 1 < m →
        ∀ (G : Type u) [Group G],
          SFQuotie G →
            Group.FG G → (∀ x : G, x ^ m = 1) → Finite G)
    {n : ℕ}
    (hn : 1 < n)
    {g : Γ}
    (hg : g ∉ zassenhausFiltration p Γ n) :
    ∃ N : OpenNormalSubgroup Γ,
      QuotientGroup.mk' N.toSubgroup g ∉
        zassenhausFiltration p (Γ ⧸ N.toSubgroup) n := by
  exact
    gens_separating_burnside
      (p := p)
      (Γ := Γ)
      s
      hs
      (closed_family_width (Γ := Γ) hwidth)
      hBurnside
      hn
      (g := g)
      hg
/-- Finite-width power subgroups plus bounded-exponent Burnside imply finite-quotient separation
for `D_n`, in the Hausdorff topological-group setting where finite width gives closedness. -/
lemma
    dense_gens_burnside
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ] [T2Space Γ]
    {d : ℕ} (s : Fin d → Γ)
    (hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤)
    (hwidth : ∀ m : ℕ, 1 < m → powerSubgroupWidth Γ m)
    (hBurnside :
      ∀ m : ℕ, 1 < m →
        ∀ (G : Type u) [Group G],
          Group.FG G → (∀ x : G, x ^ m = 1) → Finite G)
    {n : ℕ}
    (hn : 1 < n)
    {g : Γ}
    (hg : g ∉ zassenhausFiltration p Γ n) :
    ∃ N : OpenNormalSubgroup Γ,
      QuotientGroup.mk' N.toSubgroup g ∉
        zassenhausFiltration p (Γ ⧸ N.toSubgroup) n := by
  exact
    separates_closed_burnside
      (p := p)
      (Γ := Γ)
      s
      hs
      (closed_family_width (Γ := Γ) hwidth)
      hBurnside
      hn
      (g := g)
      hg
/-- Finite-width power subgroups, residual finiteness of the power quotients, and residually finite
bounded-exponent Burnside imply finite-quotient separation for `D_n`. -/
lemma
    gens_width_burnside
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ] [T2Space Γ]
    {d : ℕ} (s : Fin d → Γ)
    (hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤)
    (hwidth : ∀ m : ℕ, 1 < m → powerSubgroupWidth Γ m)
    (hRF :
      ∀ m : ℕ, 1 < m →
        IsClosed ((powerSubgroup Γ m : Subgroup Γ) : Set Γ) →
        letI : (powerSubgroup Γ m).Normal := powerSubgroup_normal Γ m
        Group.ResiduallyFinite (Γ ⧸ powerSubgroup Γ m))
    (hBurnside :
      ∀ m : ℕ, 1 < m →
        ∀ (G : Type u) [Group G] [Group.ResiduallyFinite G],
          Group.FG G → (∀ x : G, x ^ m = 1) → Finite G)
    {n : ℕ}
    (hn : 1 < n)
    {g : Γ}
    (hg : g ∉ zassenhausFiltration p Γ n) :
    ∃ N : OpenNormalSubgroup Γ,
      QuotientGroup.mk' N.toSubgroup g ∉
        zassenhausFiltration p (Γ ⧸ N.toSubgroup) n := by
  exact
    closed_residually_burnside
      (p := p)
      (Γ := Γ)
      s
      hs
      (closed_family_width (Γ := Γ) hwidth)
      hRF
      hBurnside
      hn
      (g := g)
      hg
/-- Finite-width power subgroups and residually finite bounded-exponent Burnside imply
finite-quotient separation for `D_n`; closed power-subgroup quotients are residually finite. -/
lemma
    width_residually_burnside
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ] [T2Space Γ]
    {d : ℕ} (s : Fin d → Γ)
    (hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤)
    (hwidth : ∀ m : ℕ, 1 < m → powerSubgroupWidth Γ m)
    (hquot :
      ∀ m : ℕ, 1 < m →
        IsClosed ((powerSubgroup Γ m : Subgroup Γ) : Set Γ) →
        letI : (powerSubgroup Γ m).Normal := powerSubgroup_normal Γ m
        TotallyDisconnectedSpace (Γ ⧸ powerSubgroup Γ m))
    (hBurnside :
      ∀ m : ℕ, 1 < m →
        ∀ (G : Type u) [Group G] [Group.ResiduallyFinite G],
          Group.FG G → (∀ x : G, x ^ m = 1) → Finite G)
    {n : ℕ}
    (hn : 1 < n)
    {g : Γ}
    (hg : g ∉ zassenhausFiltration p Γ n) :
    ∃ N : OpenNormalSubgroup Γ,
      QuotientGroup.mk' N.toSubgroup g ∉
        zassenhausFiltration p (Γ ⧸ N.toSubgroup) n := by
  exact
    gens_residually_burnside
      (p := p)
      (Γ := Γ)
      s
      hs
      (closed_family_width (Γ := Γ) hwidth)
      hquot
      hBurnside
      hn
      (g := g)
      hg
/-- Openness of prime-power subgroups implies finite-quotient separation for `D_n`. -/
lemma filtration_separates_open
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ]
    {n : ℕ}
    (hopen :
      ∀ j : ℕ, IsOpen ((powerSubgroup Γ (p ^ j) : Subgroup Γ) : Set Γ))
    {g : Γ}
    (hg : g ∉ zassenhausFiltration p Γ n) :
    ∃ N : OpenNormalSubgroup Γ,
      QuotientGroup.mk' N.toSubgroup g ∉
        zassenhausFiltration p (Γ ⧸ N.toSubgroup) n := by
  rcases
      open_normal_filtration
        (p := p) (Γ := Γ) (n := n) hopen with
    ⟨N, hN⟩
  exact
    ⟨N,
      filtration_separates_normal
        (p := p) (Γ := Γ) (n := n) N hN hg⟩
/-- Openness of `D_n` plus the self-quotient algebra calculation gives the desired separator. -/
lemma separates_topology_data
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ]
    {n : ℕ}
    (Htop : STData p Γ n)
    {g : Γ}
    (hg : g ∉ zassenhausFiltration p Γ n) :
    ∃ N : OpenNormalSubgroup Γ,
      QuotientGroup.mk' N.toSubgroup g ∉
        zassenhausFiltration p (Γ ⧸ N.toSubgroup) n := by
  let N : OpenNormalSubgroup Γ :=
    { toOpenSubgroup :=
        { toSubgroup := zassenhausFiltration p Γ n
          isOpen' := Htop.isOpen_zassenhaus }
      isNormal' := zassenhausFiltration_normal p Γ n }
  refine ⟨N, ?_⟩
  exact
    filtration_separates_normal
      (p := p)
      (Γ := Γ)
      (n := n)
      N
      (by intro x hx; simpa [N] using hx)
      hg
/-- Closed finite-index data for `D_n` gives finite-quotient separation. -/
lemma separates_closed_index
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ]
    {n : ℕ}
    (H : DCInput p Γ n)
    {g : Γ}
    (hg : g ∉ zassenhausFiltration p Γ n) :
    ∃ N : OpenNormalSubgroup Γ,
      QuotientGroup.mk' N.toSubgroup g ∉
        zassenhausFiltration p (Γ ⧸ N.toSubgroup) n := by
  exact
    separates_topology_data
      (p := p) (Γ := Γ) H.toTopologyData hg
end Submission
