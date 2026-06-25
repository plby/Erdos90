import Mathlib
import Submission.Group.DenseGenerators.ZassenhausClosed
import Submission.Group.DenseGenerators.ZassenhausQuotient
import Submission.Group.PowerWidth.OpenNormal



open scoped Topology Pointwise

noncomputable section

namespace Submission

universe u
universe v w z

/-- If an open normal subgroup lies inside `D_n`, then its quotient detects every point outside
`D_n`.

This is the formal endgame for the Nikolov-Segal power-subgroup route: once a sufficiently large
open normal power subgroup is known to be contained in `D_n(Γ)`, no additional topology is needed.
-/
lemma filtration_open_normal
    {p : ℕ}
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ]
    {n : ℕ}
    (N : OpenNormalSubgroup Γ)
    (hND : N.toSubgroup ≤ zassenhausFiltration p Γ n)
    {g : Γ}
    (hg : g ∉ zassenhausFiltration p Γ n) :
    QuotientGroup.mk' N.toSubgroup g ∉
      zassenhausFiltration p (Γ ⧸ N.toSubgroup) n := by
  intro hgq
  have hsurj : Function.Surjective (QuotientGroup.mk' N.toSubgroup) :=
    QuotientGroup.mk'_surjective N.toSubgroup
  have hgmap :
      QuotientGroup.mk' N.toSubgroup g ∈
        Subgroup.map (QuotientGroup.mk' N.toSubgroup)
          (zassenhausFiltration p Γ n) :=
    zassenhaus_filtration_surjective
      (p := p) (n := n) (f := QuotientGroup.mk' N.toSubgroup) hsurj hgq
  rcases hgmap with ⟨d, hdD, hd_eq_g⟩
  have hdiffN : d⁻¹ * g ∈ N.toSubgroup := by
    rw [← QuotientGroup.eq_one_iff (N := N.toSubgroup) (d⁻¹ * g)]
    calc
      QuotientGroup.mk' N.toSubgroup (d⁻¹ * g) =
          (QuotientGroup.mk' N.toSubgroup d)⁻¹ *
            QuotientGroup.mk' N.toSubgroup g := by
        simp
      _ = 1 := by
        rw [hd_eq_g]
        simp
  have hdiffD : d⁻¹ * g ∈ zassenhausFiltration p Γ n :=
    hND hdiffN
  have hgD : g ∈ zassenhausFiltration p Γ n := by
    have hmul :
        d * (d⁻¹ * g) ∈ zassenhausFiltration p Γ n :=
      (zassenhausFiltration p Γ n).mul_mem hdD hdiffD
    simpa [mul_assoc] using hmul
  exact hg hgD
/-- Finite-quotient separation follows from the existence of one open normal subgroup inside
`D_n`. -/
lemma separates_open_normal
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    {n : ℕ}
    (hN :
      ∃ N : OpenNormalSubgroup Γ,
        N.toSubgroup ≤ zassenhausFiltration p Γ n)
    {g : Γ}
    (hg : g ∉ zassenhausFiltration p Γ n) :
    ∃ N : OpenNormalSubgroup Γ,
      QuotientGroup.mk' N.toSubgroup g ∉
        zassenhausFiltration p (Γ ⧸ N.toSubgroup) n := by
  rcases hN with ⟨N, hNle⟩
  exact
    ⟨N,
      filtration_open_normal
        (p := p) (Γ := Γ) (n := n) N hNle hg⟩
/-- Openness of the prime-power subgroup supplies an open normal subgroup inside `D_n`. -/
lemma open_filtration_subgroup
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ]
    (n : ℕ)
    (hopen :
      IsOpen ((powerSubgroup Γ (p ^ n) : Subgroup Γ) : Set Γ)) :
    ∃ N : OpenNormalSubgroup Γ,
      N.toSubgroup ≤ zassenhausFiltration p Γ n := by
  let P : Subgroup Γ := powerSubgroup Γ (p ^ n)
  have hPnormal : P.Normal := by
    dsimp [P]
    infer_instance
  let N : OpenNormalSubgroup Γ :=
    { toSubgroup := P
      isOpen' := by
        simpa [P] using hopen
      isNormal' := hPnormal }
  refine ⟨N, ?_⟩
  have hlepow : n ≤ p ^ n :=
    nat_pow_self (Fact.out : Nat.Prime p).two_le
  simpa [N, P] using
    power_filtration_pow
      (G := Γ) (p := p) (n := n) (j := n) hlepow
/-- Conditional finite-quotient separation from the eventual prime-power subgroup openness input. -/
theorem dense_separates_open
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} (_s : Fin d → Γ)
    (_hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range _s)) = ⊤)
    {n : ℕ}
    (_hn : 1 < n)
    (hopen :
      IsOpen ((powerSubgroup Γ (p ^ n) : Subgroup Γ) : Set Γ))
    {g : Γ}
    (hg : g ∉ zassenhausFiltration p Γ n) :
    ∃ N : OpenNormalSubgroup Γ,
      QuotientGroup.mk' N.toSubgroup g ∉
        zassenhausFiltration p (Γ ⧸ N.toSubgroup) n := by
  exact
    separates_open_normal
      (p := p) (Γ := Γ) (n := n)
      (open_filtration_subgroup
        (p := p) (Γ := Γ) n hopen)
      hg
/-- Conditional finite-quotient separation from uniform finite quotient width/index bounds.

This packages the remaining Nikolov--Segal/RBT route into explicit finite and profinite bridge
inputs, then reuses the power-subgroup-open reduction above. -/
theorem
    gens_width_bound
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} (s : Fin d → Γ)
    (hs : Subgroup.topologicalClosure
            (Subgroup.closure (Set.range s)) = ⊤)
    {n : ℕ}
    (hn : 1 < n)
    {k B : ℕ}
    (hdet : OpenClosedDetection Γ)
    (hfinite : BoundedOpenQuotients Γ)
    (hQ :
      ∀ N : OpenNormalSubgroup Γ,
        HPWidth (Γ ⧸ N.toSubgroup) (p ^ n) k ∧
          Nat.card
            ((Γ ⧸ N.toSubgroup) ⧸
              powerSubgroup (Γ ⧸ N.toSubgroup) (p ^ n)) ≤ B)
    {g : Γ}
    (hg : g ∉ zassenhausFiltration p Γ n) :
    ∃ N : OpenNormalSubgroup Γ,
      QuotientGroup.mk' N.toSubgroup g ∉
        zassenhausFiltration p (Γ ⧸ N.toSubgroup) n := by
  letI : T2Space Γ := t_space_disconnected Γ
  have hopen :
      IsOpen ((powerSubgroup Γ (p ^ n) : Subgroup Γ) : Set Γ) :=
    width_index_bound
      (Γ := Γ) (m := p ^ n) (k := k) (B := B)
      hdet hfinite hQ
  exact
    dense_separates_open
      (p := p) (Γ := Γ) s hs hn hopen hg
/-- Conditional finite-quotient separation from the finite power-width/index package plus the
explicit topological bridge properties. -/
theorem
    separates_width_bound
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} (s : Fin d → Γ)
    (hs : Subgroup.topologicalClosure
            (Subgroup.closure (Set.range s)) = ⊤)
    {n : ℕ}
    (hn : 1 < n)
    {k B : ℕ}
    (hdet : OpenClosedDetection Γ)
    (hfinite : BoundedOpenQuotients Γ)
    (hfin : WIBound.{u} d (p ^ n) k B)
    (hdisc :
      ∀ N : OpenNormalSubgroup Γ,
        DiscreteTopology (Γ ⧸ N.toSubgroup))
    (hfiniteQ :
      ∀ N : OpenNormalSubgroup Γ,
        Finite (Γ ⧸ N.toSubgroup))
    (hcont :
      ∀ N : OpenNormalSubgroup Γ,
        Continuous
          (fun x : Γ => QuotientGroup.mk' N.toSubgroup x))
    {g : Γ}
    (hg : g ∉ zassenhausFiltration p Γ n) :
    ∃ N : OpenNormalSubgroup Γ,
      QuotientGroup.mk' N.toSubgroup g ∉
        zassenhausFiltration p (Γ ⧸ N.toSubgroup) n := by
  exact
    gens_width_bound
      (p := p) (Γ := Γ) s hs hn
      hdet hfinite
      (open_width_bound
        (Γ := Γ) (d := d) (m := p ^ n) (k := k) (B := B)
        s hs hfin hdisc hfiniteQ hcont)
      hg
/-- Conditional finite-quotient separation from finite power-width/index bounds and the remaining
bounded-open-normal-quotient compactness bridge. -/
theorem
    gens_width_quotients
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} (s : Fin d → Γ)
    (hs : Subgroup.topologicalClosure
            (Subgroup.closure (Set.range s)) = ⊤)
    {n : ℕ}
    (hn : 1 < n)
    {k B : ℕ}
    (hfinite : BoundedOpenQuotients Γ)
    (hfin : WIBound.{u} d (p ^ n) k B)
    {g : Γ}
    (hg : g ∉ zassenhausFiltration p Γ n) :
    ∃ N : OpenNormalSubgroup Γ,
      QuotientGroup.mk' N.toSubgroup g ∉
        zassenhausFiltration p (Γ ⧸ N.toSubgroup) n := by
  have hopen :
      IsOpen ((powerSubgroup Γ (p ^ n) : Subgroup Γ) : Set Γ) :=
    compact_totally_disconnected
      (Γ := Γ) (d := d) (m := p ^ n) (k := k) (B := B)
      s hs hfinite hfin
  exact
    dense_separates_open
      (p := p) (Γ := Γ) s hs hn hopen hg
/-- Conditional finite-quotient separation from the prime-power finite NS/RBT package and the
remaining bounded-open-normal-quotient compactness bridge. -/
theorem
    gens_nsrbt_quotients
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} (s : Fin d → Γ)
    (hs : Subgroup.topologicalClosure
            (Subgroup.closure (Set.range s)) = ⊤)
    {n : ℕ}
    (hn : 1 < n)
    (hfinite : BoundedOpenQuotients Γ)
    (hNS : NPPower.{u} d p n)
    {g : Γ}
    (hg : g ∉ zassenhausFiltration p Γ n) :
    ∃ N : OpenNormalSubgroup Γ,
      QuotientGroup.mk' N.toSubgroup g ∉
        zassenhausFiltration p (Γ ⧸ N.toSubgroup) n := by
  rcases hNS with ⟨k, B, hfin⟩
  exact
    gens_width_quotients
      (p := p) (Γ := Γ) s hs hn
      (k := k) (B := B)
      hfinite hfin hg
/-- Conditional finite-quotient separation from only the finite prime-power NS/RBT package. -/
theorem
    dense_separates_nsrbt
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} (s : Fin d → Γ)
    (hs : Subgroup.topologicalClosure
            (Subgroup.closure (Set.range s)) = ⊤)
    {n : ℕ}
    (hn : 1 < n)
    (hNS : NPPower.{u} d p n)
    {g : Γ}
    (hg : g ∉ zassenhausFiltration p Γ n) :
    ∃ N : OpenNormalSubgroup Γ,
      QuotientGroup.mk' N.toSubgroup g ∉
        zassenhausFiltration p (Γ ⧸ N.toSubgroup) n := by
  exact
    gens_nsrbt_quotients
      (p := p) (Γ := Γ) s hs hn
      (quotients_totally_disconnected (Γ := Γ))
      hNS hg
/-- The finite-quotient separation theorem is proved for profinite groups generated by at most one
element. -/
theorem
    dense_filtration_separates
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} (s : Fin d → Γ)
    (hs : Subgroup.topologicalClosure
            (Subgroup.closure (Set.range s)) = ⊤)
    (hd : d ≤ 1)
    {n : ℕ}
    (hn : 1 < n)
    {g : Γ}
    (hg : g ∉ zassenhausFiltration p Γ n) :
    ∃ N : OpenNormalSubgroup Γ,
      QuotientGroup.mk' N.toSubgroup g ∉
        zassenhausFiltration p (Γ ⧸ N.toSubgroup) n := by
  exact
    dense_separates_nsrbt
      (p := p) (Γ := Γ) s hs hn
      (nsrbt_generators_one (p := p) (e := n) hd)
      hg
end Submission
