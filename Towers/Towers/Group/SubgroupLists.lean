import Towers.Group.GolodShafarevichCore


open Filter
open scoped Pointwise Topology

noncomputable section

universe u v

namespace Towers

section FiniteSubgroupLists

variable {G : Type u} [Group G]

lemma closure_subtype_range (H : Subgroup G) :
    Subgroup.closure (Set.range ((↑) : H → G)) = H := by
  apply le_antisymm
  · exact (Subgroup.closure_le H).2 (by
      rintro x ⟨xH, rfl⟩
      exact xH.property)
  · intro x hx
    exact Subgroup.subset_closure ⟨⟨x, hx⟩, rfl⟩

lemma subgroup_closure_mono {L M : List G}
    (hLM : ∀ {x : G}, x ∈ L → x ∈ M) :
    Subgroup.closure ({x : G | x ∈ L} : Set G) ≤
      Subgroup.closure ({x : G | x ∈ M} : Set G) := by
  exact (Subgroup.closure_le _).2 (by
    intro x hx
    exact Subgroup.subset_closure (hLM hx))

lemma subgroup_closure_bind
    {ι : Type v} {is : List ι} {L : ι → List G} {i : ι}
    (hi : i ∈ is) :
    Subgroup.closure ({x : G | x ∈ L i} : Set G) ≤
      Subgroup.closure ({x : G | x ∈ is.flatMap L} : Set G) := by
  apply subgroup_closure_mono
  intro x hx
  simpa [List.mem_flatMap] using ⟨i, hi, hx⟩

/-- All elements of `H \ K`, as a finite list, generate `H` modulo `K`. -/
lemma list_generating_mod
    (H K : Subgroup G) [Finite H] :
    ∃ L : List G,
      (∀ x ∈ L, x ∈ H ∧ x ∉ K) ∧
      ∀ ⦃x : G⦄, x ∈ H →
        x ∈ Subgroup.closure ({y : G | y ∈ L} : Set G) ⊔ K := by
  classical
  letI : Fintype H := Fintype.ofFinite H
  let S : Finset G :=
    ((Finset.univ : Finset H).filter (fun x : H => (x : G) ∉ K)).image
      (fun x : H => (x : G))
  refine ⟨S.toList, ?_, ?_⟩
  · intro x hx
    have hxS : x ∈ S := by
      simpa using hx
    rcases Finset.mem_image.mp hxS with ⟨xH, hxH, rfl⟩
    exact ⟨xH.property, (Finset.mem_filter.mp hxH).2⟩
  · intro x hxH
    by_cases hxK : x ∈ K
    · exact
        (show K ≤ Subgroup.closure ({y : G | y ∈ S.toList} : Set G) ⊔ K from
          le_sup_right) hxK
    · exact
        (show Subgroup.closure ({y : G | y ∈ S.toList} : Set G) ≤
            Subgroup.closure ({y : G | y ∈ S.toList} : Set G) ⊔ K from le_sup_left)
          (Subgroup.subset_closure (by
        change x ∈ S.toList
        have hxS : x ∈ S := by
          refine Finset.mem_image.mpr ?_
          refine ⟨⟨x, hxH⟩, ?_, rfl⟩
          simp [hxK]
        simpa using hxS))

/-- Finite subgroup generator list, excluding `1`. -/
lemma list_ne_closure
    (H : Subgroup G) [Finite H] :
    ∃ L : List G,
      (∀ x ∈ L, x ∈ H ∧ x ≠ 1) ∧
      Subgroup.closure ({x : G | x ∈ L} : Set G) = H := by
  classical
  obtain ⟨L, hL, hgen⟩ :=
    list_generating_mod (G := G) H (⊥ : Subgroup G)
  refine ⟨L, ?_, ?_⟩
  · intro x hx
    have hx' := hL x hx
    refine ⟨hx'.1, ?_⟩
    intro hx1
    exact hx'.2 (by simp [hx1])
  · apply le_antisymm
    · exact (Subgroup.closure_le H).2 (by
        intro x hx
        exact (hL x hx).1)
    · intro x hx
      have hx' :
          x ∈ Subgroup.closure ({y : G | y ∈ L} : Set G) ⊔
            (⊥ : Subgroup G) :=
        hgen hx
      simpa using hx'

end FiniteSubgroupLists

section ZassenhausLayerLists

variable {p : ℕ} [Fact p.Prime]
variable {Q : Type u} [Group Q] [Finite Q]

omit [Fact (Nat.Prime p)] in
lemma list_generating_filtration (i : ℕ) :
    ∃ L : List Q,
      (∀ x ∈ L, x ∈ zassenhausFiltration p Q i ∧ x ≠ 1) ∧
      Subgroup.closure ({x : Q | x ∈ L} : Set Q) =
        zassenhausFiltration p Q i := by
  exact list_ne_closure (G := Q)
    (zassenhausFiltration p Q i)

omit [Fact (Nat.Prime p)] in
/-- Exact representatives for the layer `D_i / D_(i+1)`. -/
lemma generating_mod_succ (i : ℕ) :
    ∃ L : List Q,
      (∀ x ∈ L,
        x ∈ zassenhausFiltration p Q i ∧
        x ∉ zassenhausFiltration p Q (i + 1)) ∧
      ∀ ⦃x : Q⦄, x ∈ zassenhausFiltration p Q i →
        x ∈ Subgroup.closure ({y : Q | y ∈ L} : Set Q) ⊔
          zassenhausFiltration p Q (i + 1) := by
  exact list_generating_mod (G := Q)
    (zassenhausFiltration p Q i)
    (zassenhausFiltration p Q (i + 1))

omit [Fact (Nat.Prime p)] in
/-- Simultaneous exact layer-generator lists for positive layers `1, ..., n`. -/
lemma mod_succ_lists (n : ℕ) :
    ∃ L : (i : Fin n) → List Q,
      ∀ i : Fin n,
        (∀ x ∈ L i,
          x ∈ zassenhausFiltration p Q (i.1 + 1) ∧
          x ∉ zassenhausFiltration p Q ((i.1 + 1) + 1)) ∧
        ∀ ⦃x : Q⦄, x ∈ zassenhausFiltration p Q (i.1 + 1) →
          x ∈ Subgroup.closure ({y : Q | y ∈ L i} : Set Q) ⊔
            zassenhausFiltration p Q ((i.1 + 1) + 1) := by
  classical
  choose L hL using
    (fun i : Fin n =>
      generating_mod_succ
        (p := p) (Q := Q) (i.1 + 1))
  exact ⟨L, hL⟩

omit [Fact (Nat.Prime p)] in
/-- Top layer version when `D_(n+1) = ⊥`: exact top-layer elements generate `D_n`. -/
lemma generating_top_bot
    {n : ℕ}
    (hbot : zassenhausFiltration p Q (n + 1) = ⊥) :
    ∃ L : List Q,
      (∀ x ∈ L,
        x ∈ zassenhausFiltration p Q n ∧
        x ∉ zassenhausFiltration p Q (n + 1)) ∧
      Subgroup.closure ({x : Q | x ∈ L} : Set Q) =
        zassenhausFiltration p Q n := by
  classical
  obtain ⟨L, hL, hgen⟩ :=
    generating_mod_succ (p := p) (Q := Q) n
  refine ⟨L, hL, ?_⟩
  apply le_antisymm
  · exact (Subgroup.closure_le (zassenhausFiltration p Q n)).2 (by
      intro x hx
      exact (hL x hx).1)
  · intro x hx
    have hx' :
        x ∈ Subgroup.closure ({y : Q | y ∈ L} : Set Q) ⊔
          zassenhausFiltration p Q (n + 1) :=
      hgen hx
    simpa [hbot] using hx'

end ZassenhausLayerLists

end Towers
