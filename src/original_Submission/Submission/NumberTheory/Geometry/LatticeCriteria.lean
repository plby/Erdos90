import Mathlib.Algebra.Module.ZLattice.Basic
import Mathlib.Topology.DiscreteSubset


/-!
# Milne, Algebraic Number Theory, Lemma 4.14 and Proposition 4.15

This file records the topological criteria for a subgroup of a finite-dimensional real vector
space to be discrete, and the resulting algebraic description by a finite real-linearly-independent
set of generators.
-/

open Module Submodule

namespace Submission.NumberTheory.Milne

section DiscreteCriteria

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V]

/-- Milne's condition (b): zero is isolated in the subgroup. -/
def OpenZeroNeighborhood (L : Submodule ℤ V) : Prop :=
  ∃ U : Set V, IsOpen U ∧ U ∩ (L : Set V) = {0}

/-- Milne's condition (c): compact sets meet the subgroup in finite sets. -/
def CompactInterFinite (L : Submodule ℤ V) : Prop :=
  ∀ C : Set V, IsCompact C → (C ∩ (L : Set V)).Finite

/-- Milne's condition (d): bounded sets meet the subgroup in finite sets. -/
def BoundedInterFinite (L : Submodule ℤ V) : Prop :=
  ∀ S : Set V, Bornology.IsBounded S → (S ∩ (L : Set V)).Finite

omit [NormedSpace ℝ V] [FiniteDimensional ℝ V] in
/-- Lemma 4.14(a) ⇔ (b): a subgroup is discrete iff zero has an isolating open
neighborhood in the ambient vector space. -/
theorem discrete_topology_neighborhood (L : Submodule ℤ V) :
    DiscreteTopology L ↔ OpenZeroNeighborhood L := by
  rw [discreteTopology_iff_isOpen_singleton_zero, isOpen_induced_iff]
  simp only [OpenZeroNeighborhood, Set.preimage]
  constructor
  · rintro ⟨U, hU, hpre⟩
    refine ⟨U, hU, ?_⟩
    ext x
    constructor
    · rintro ⟨hxU, hxL⟩
      have hx : (⟨x, hxL⟩ : L) ∈ ({0} : Set L) := by
        rw [← hpre]
        exact hxU
      simpa using congrArg Subtype.val (Set.mem_singleton_iff.mp hx)
    · intro hx
      subst x
      refine ⟨?_, L.zero_mem⟩
      exact (Set.ext_iff.mp hpre (0 : L)).mpr (Set.mem_singleton 0)
  · rintro ⟨U, hU, hinter⟩
    refine ⟨U, hU, ?_⟩
    ext x
    simp only [Set.mem_singleton_iff, Subtype.ext_iff]
    have hx := Set.ext_iff.mp hinter x
    simpa using hx

/-- Lemma 4.14(a) ⇔ (d): a subgroup is discrete iff every bounded set meets it in a
finite set. -/
theorem discrete_topology_inter (L : Submodule ℤ V) :
    DiscreteTopology L ↔ BoundedInterFinite L := by
  constructor
  · intro hL
    letI : DiscreteTopology L := hL
    intro S hS
    change (S ∩ (L.toAddSubgroup : Set V)).Finite
    exact Metric.finite_isBounded_inter_isClosed DiscreteTopology.isDiscrete hS
      AddSubgroup.isClosed_of_discrete
  · intro hL
    apply Continuous.discrete_of_tendsto_cofinite_cocompact continuous_subtype_val
    rw [tendsto_cofinite_cocompact_iff]
    intro K hK
    have hfinite : (K ∩ (L : Set V)).Finite := hL K hK.isBounded
    have hp : Set.Finite (((↑) : L → V) ⁻¹' (K ∩ (L : Set V))) :=
      Set.Finite.preimage Subtype.val_injective.injOn hfinite
    convert hp using 1
    ext x
    simp

/-- Lemma 4.14(a) ⇔ (c): a subgroup is discrete iff every compact set meets it in a
finite set. -/
theorem topology_compact_inter (L : Submodule ℤ V) :
    DiscreteTopology L ↔ CompactInterFinite L := by
  constructor
  · intro hL C hC
    exact (discrete_topology_inter L).mp hL C hC.isBounded
  · intro hL
    apply Continuous.discrete_of_tendsto_cofinite_cocompact continuous_subtype_val
    rw [tendsto_cofinite_cocompact_iff]
    intro K hK
    have hfinite : (K ∩ (L : Set V)).Finite := hL K hK
    have hp : Set.Finite (((↑) : L → V) ⁻¹' (K ∩ (L : Set V))) :=
      Set.Finite.preimage Subtype.val_injective.injOn hfinite
    convert hp using 1
    ext x
    simp

/-- Lemma 4.14, with all four conditions displayed together. -/
theorem discrete_equivalent_conditions (L : Submodule ℤ V) :
    (DiscreteTopology L ↔ OpenZeroNeighborhood L) ∧
      (DiscreteTopology L ↔ CompactInterFinite L) ∧
      (DiscreteTopology L ↔ BoundedInterFinite L) := by
  exact ⟨discrete_topology_neighborhood L,
    topology_compact_inter L,
    discrete_topology_inter L⟩

end DiscreteCriteria

section LatticeCriterion

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V]

/-- Milne's (not necessarily full) notion of a lattice: a subgroup generated over `ℤ` by a
finite set which is linearly independent over `ℝ`. -/
def IsLattice (L : Submodule ℤ V) : Prop :=
  ∃ s : Set V, s.Finite ∧ LinearIndepOn ℝ id s ∧ span ℤ s = L

omit [FiniteDimensional ℝ V] in
/-- A finite real-linearly-independent set generates a discrete subgroup. -/
theorem IsLattice.discreteTopology {L : Submodule ℤ V} (hL : IsLattice L) :
    DiscreteTopology L := by
  rcases hL with ⟨s, hs, hsli, rfl⟩
  let v : s → V := fun x ↦ x.1
  have hv : LinearIndependent ℝ v := by
    simpa only [LinearIndepOn, id_eq] using hsli
  have hrange : Set.range v = s := by
    ext x
    simp [v]
  rw [← hrange]
  let W : Submodule ℝ V := span ℝ (Set.range v)
  let b : Basis s ℝ W := Basis.span hv
  let L₀ : Submodule ℤ W :=
    comap ((W.restrictScalars ℤ).subtype) (span ℤ (Set.range v))
  letI : Finite s := hs.to_subtype
  have hL₀ : L₀ = span ℤ (Set.range b) := by
    let g : W →ₗ[ℤ] V := (W.restrictScalars ℤ).subtype
    have himage : g '' Set.range b = Set.range v := by
      ext x
      constructor
      · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
        refine ⟨i, ?_⟩
        change v i = ((Basis.span hv i : W) : V)
        exact (Basis.coe_span_apply hv i).symm
      · rintro ⟨i, rfl⟩
        refine ⟨b i, ⟨i, rfl⟩, ?_⟩
        change ((Basis.span hv i : W) : V) = v i
        exact Basis.coe_span_apply hv i
    change comap g (span ℤ (Set.range v)) = span ℤ (Set.range b)
    apply map_injective_of_injective (f := g) (injective_subtype _)
    rw [map_comap_eq_self, map_span, himage]
    have hg : g.range = W.restrictScalars ℤ := by
      exact range_subtype (W.restrictScalars ℤ)
    rw [hg]
    exact span_le_restrictScalars ℤ ℝ (Set.range v)
  have hbdisc : DiscreteTopology (span ℤ (Set.range b)) :=
    ZSpan.instDiscreteTopologySubtypeMemSubmoduleIntSpanRangeCoeBasisRealOfFinite b
  haveI : DiscreteTopology L₀ := by
    rw [hL₀]
    exact hbdisc
  let f : L₀ ≃ₗ[ℤ] span ℤ (Set.range v) :=
    Submodule.comapSubtypeEquivOfLe
      (span_le_restrictScalars ℤ ℝ (Set.range v))
  have hf : Isometry f := fun _ _ ↦ rfl
  have hfi : Isometry f.symm := fun _ _ ↦ rfl
  let e : L₀ ≃L[ℤ] span ℤ (Set.range v) :=
    { f with
      continuous_toFun := hf.continuous
      continuous_invFun := hfi.continuous }
  exact e.toHomeomorph.discreteTopology

/-- A discrete subgroup admits a finite real-linearly-independent set of generators. -/
theorem discrete_topology (L : Submodule ℤ V) (hL : DiscreteTopology L) :
    IsLattice L := by
  letI : DiscreteTopology L := hL
  let b₀ := Module.Free.chooseBasis ℤ L
  let κ := Module.Free.ChooseBasisIndex ℤ L
  let b : κ → V := Subtype.val ∘ b₀
  have hbℤ : LinearIndependent ℤ b :=
    LinearIndependent.map' b₀.linearIndependent L.subtype (ker_subtype L)
  have hspan : span ℤ (Set.range b) = L := by
    convert congrArg (map (Submodule.subtype L)) b₀.span_eq
    · rw [map_span, Set.range_comp]
      rfl
    · exact (map_subtype_top L).symm
  haveI : Fintype κ := Fintype.ofFinite κ
  have hbℝ : LinearIndependent ℝ b := by
    rw [linearIndependent_iff_card_eq_finrank_span]
    rw [Real.finrank_eq_int_finrank_of_discrete (hspan ▸ hL)]
    exact linearIndependent_iff_card_eq_finrank_span.mp hbℤ
  refine ⟨Set.range b, Set.toFinite _, ?_, hspan⟩
  rwa [linearIndepOn_id_range_iff (Subtype.val_injective.comp b₀.injective)]

/-- Proposition 4.15: a subgroup of a finite-dimensional real vector space is a lattice in
Milne's sense if and only if it is discrete. -/
theorem lattice_topology (L : Submodule ℤ V) :
    IsLattice L ↔ DiscreteTopology L :=
  ⟨IsLattice.discreteTopology, discrete_topology L⟩

end LatticeCriterion

end Submission.NumberTheory.Milne
