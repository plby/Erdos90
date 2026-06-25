import Mathlib
import Submission.Group.PowerWidth.PowerSubgroups
import Submission.Group.DenseGenerators.ZassenhausCompact
import Submission.Topology.OpenNormal

/-!
# Lightweight topology for pro-p presentations

This file isolates the elementary compact-group facts used by the pro-`p`
presentation layer.  It deliberately avoids the power-width, Nikolov-Segal,
and restricted-Burnside packages.
-/

open scoped Topology Pointwise

noncomputable section

namespace Submission

universe u

/-- A closed overgroup contains the topological closure. -/
lemma pro_topological_closed
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {H K : Subgroup G}
    (hHK : H ≤ K)
    (hK : IsClosed ((K : Subgroup G) : Set G)) :
    Subgroup.topologicalClosure H ≤ K := by
  exact H.topologicalClosure_minimal hHK hK

/-- Dense generation descends through a continuous surjection to a finite
discrete target. -/
lemma pro_generated_image
    {Γ Q : Type u}
    [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [Group Q] [TopologicalSpace Q] [DiscreteTopology Q]
    {d : ℕ} (s : Fin d → Γ)
    (hs : Subgroup.topologicalClosure
            (Subgroup.closure (Set.range s)) = ⊤)
    (φ : Γ →* Q)
    (hφcont : Continuous (fun x : Γ => φ x))
    (hφsurj : Function.Surjective φ) :
    GeneratedBy (fun i : Fin d => φ (s i)) := by
  let K : Subgroup Q :=
    Subgroup.closure (Set.range (fun i : Fin d => φ (s i)))
  have hle : Subgroup.closure (Set.range s) ≤ K.comap φ := by
    apply (Subgroup.closure_le _).mpr
    rintro x ⟨i, rfl⟩
    exact Subgroup.subset_closure ⟨i, rfl⟩
  have hKclosed : IsClosed ((K : Subgroup Q) : Set Q) := by
    exact isClosed_discrete _
  have hpreclosed : IsClosed (((K.comap φ : Subgroup Γ) : Set Γ)) := by
    change IsClosed ((fun x : Γ => φ x) ⁻¹' ((K : Subgroup Q) : Set Q))
    exact hKclosed.preimage hφcont
  have htop_pre : (⊤ : Subgroup Γ) ≤ K.comap φ := by
    have hclosure :
        Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) ≤
          K.comap φ :=
      pro_topological_closed hle hpreclosed
    simpa [hs] using hclosure
  have htop : (⊤ : Subgroup Q) ≤ K := by
    intro y _hy
    rcases hφsurj y with ⟨x, rfl⟩
    exact htop_pre trivial
  exact top_unique htop

/-- Finite dense generators remain dense after quotienting by a normal
subgroup. -/
lemma pro_dense_generators
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    {Hq : Subgroup Γ} [Hq.Normal]
    {d : ℕ} (s : Fin d → Γ)
    (hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤) :
    closure
        (((Subgroup.closure
          (Set.range
            (fun i : Fin d =>
              QuotientGroup.mk' Hq (s i)))) :
            Subgroup (Γ ⧸ Hq)) :
          Set (Γ ⧸ Hq)) =
      Set.univ := by
  let q : Γ →* Γ ⧸ Hq := QuotientGroup.mk' Hq
  let H : Subgroup Γ := Subgroup.closure (Set.range s)
  let K : Subgroup (Γ ⧸ Hq) :=
    Subgroup.closure (Set.range fun i : Fin d => q (s i))
  have hq_cont : Continuous (fun g : Γ => q g) := by
    dsimp [q]
    change Continuous (QuotientGroup.mk : Γ → Γ ⧸ Hq)
    exact QuotientGroup.continuous_mk
  have hq_dense : DenseRange (fun g : Γ => q g) :=
    (QuotientGroup.mk'_surjective Hq).denseRange
  have hH_closure :
      closure ((H : Subgroup Γ) : Set Γ) = Set.univ := by
    simpa [H, Subgroup.topologicalClosure_coe] using
      congrArg (fun L : Subgroup Γ => (L : Set Γ)) hs
  have hH_dense : Dense ((H : Subgroup Γ) : Set Γ) := by
    rw [dense_iff_closure_eq]
    exact hH_closure
  have hqH_dense :
      Dense (q '' ((H : Subgroup Γ) : Set Γ)) :=
    hq_dense.dense_image hq_cont hH_dense
  have himage_subset :
      q '' ((H : Subgroup Γ) : Set Γ) ⊆ (K : Set (Γ ⧸ Hq)) := by
    rintro y ⟨x, hx, rfl⟩
    change q x ∈ K
    change x ∈ H at hx
    dsimp [H] at hx
    refine Subgroup.closure_induction (k := Set.range s) ?mem ?one ?mul ?inv hx
    · intro x hx
      rcases hx with ⟨i, rfl⟩
      exact Subgroup.subset_closure ⟨i, rfl⟩
    · simpa only [map_one] using K.one_mem
    · intro x y _hx _hy hxK hyK
      simpa using K.mul_mem hxK hyK
    · intro x _hx hxK
      simpa using K.inv_mem hxK
  simpa [K, q] using (hqH_dense.mono himage_subset).closure_eq

/-- In a compact totally disconnected topological group, open-normal
quotients separate closed sets from exterior points. -/
lemma separate_sets_disconnected
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    ⦃C : Set Γ⦄
    (hC : IsClosed C)
    (g : Γ)
    (hgC : g ∉ C) :
    ∃ N : OpenNormalSubgroup Γ,
      QuotientGroup.mk' N.toSubgroup g ∉
        (QuotientGroup.mk' N.toSubgroup) '' C := by
  let U : Set Γ := {x : Γ | g * x ∉ C}
  have hU : U ∈ nhds (1 : Γ) := by
    have hCcompl : Cᶜ ∈ nhds g :=
      hC.isOpen_compl.mem_nhds hgC
    have hCcompl' : Cᶜ ∈ nhds ((fun x : Γ => g * x) (1 : Γ)) := by
      simpa using hCcompl
    have hpre :
        (fun x : Γ => g * x) ⁻¹' Cᶜ ∈ nhds (1 : Γ) :=
      ((continuous_const.mul continuous_id).continuousAt) hCcompl'
    simpa [U] using hpre
  rcases mem_nhds_iff.mp hU with ⟨V, hVU, hVopen, h1V⟩
  rcases
      ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one
        (G := Γ) hVopen h1V with
    ⟨N, hNV⟩
  refine ⟨N, ?_⟩
  rintro ⟨c, hcC, hcq⟩
  have hq :
      QuotientGroup.mk' N.toSubgroup (g⁻¹ * c) = 1 := by
    calc
      QuotientGroup.mk' N.toSubgroup (g⁻¹ * c) =
          (QuotientGroup.mk' N.toSubgroup g)⁻¹ *
            QuotientGroup.mk' N.toSubgroup c := by
              simp
      _ = 1 := by
              simp [hcq]
  have hmem : g⁻¹ * c ∈ N.toSubgroup :=
    (QuotientGroup.eq_one_iff (N := N.toSubgroup) (g⁻¹ * c)).mp hq
  have hnotC : g * (g⁻¹ * c) ∉ C :=
    hVU (hNV hmem)
  exact hnotC (by simpa [mul_assoc] using hcC)

/-- An open-normal quotient is discrete. -/
lemma pro_discrete_topology
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    (N : OpenNormalSubgroup Γ) :
    DiscreteTopology (Γ ⧸ N.toSubgroup) := by
  exact QuotientGroup.discreteTopology N.isOpen

/-- An open-normal quotient of a compact topological group is finite. -/
lemma pro_p_open
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ]
    (N : OpenNormalSubgroup Γ) :
    Finite (Γ ⧸ N.toSubgroup) := by
  exact N.toSubgroup.quotient_finite_of_isOpen N.isOpen

/-- The quotient map to an open-normal quotient is continuous. -/
lemma pro_open_continuous
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ]
    (N : OpenNormalSubgroup Γ) :
    Continuous (fun x : Γ => QuotientGroup.mk' N.toSubgroup x) := by
  change Continuous (QuotientGroup.mk : Γ → Γ ⧸ N.toSubgroup)
  exact QuotientGroup.continuous_mk

/-- A continuous homomorphism to a discrete group has open kernel. -/
lemma pro_monoid_discrete
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

end Submission
