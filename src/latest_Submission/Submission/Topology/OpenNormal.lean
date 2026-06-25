import Mathlib


open Filter
open scoped Pointwise EuclideanGeometry Topology

noncomputable section

open NumberField

namespace Submission

def topOpenSubgroup (Γ : Type*) [Group Γ] [TopologicalSpace Γ] :
    OpenNormalSubgroup Γ where
  toOpenSubgroup := ⊤
  isNormal' := Subgroup.normal_top

instance instTopOpen (Γ : Type*) [Group Γ] [TopologicalSpace Γ] :
    OrderTop (OpenNormalSubgroup Γ) where
  top := topOpenSubgroup Γ
  le_top _ := Set.subset_univ _

section Quotient

variable {Γ : Type*} [Group Γ] [TopologicalSpace Γ]

/-- Equality of quotient classes implies that the corresponding relative difference lies in the
subgroup. -/
theorem inv_mul_quotient {N : OpenNormalSubgroup Γ} {x y : Γ}
    (hxy : (x : Γ ⧸ (N : Subgroup Γ)) = y) : x⁻¹ * y ∈ (N : Subgroup Γ) := by
  refine (QuotientGroup.eq_one_iff (N := (N : Subgroup Γ)) (x⁻¹ * y)).mp ?_
  change ((x : Γ ⧸ (N : Subgroup Γ))⁻¹ * (y : Γ ⧸ (N : Subgroup Γ))) = 1
  simpa using
    (congrArg
      (fun z : Γ ⧸ (N : Subgroup Γ) =>
        (x : Γ ⧸ (N : Subgroup Γ))⁻¹ * z) hxy).symm

end Quotient

section Profinite

variable {Γ : Type*} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
  [CompactSpace Γ] [TotallyDisconnectedSpace Γ]

/-- Any nontrivial element of a profinite group is excluded by some open normal subgroup. -/
theorem open_normal_not {g : Γ} (hg : g ≠ 1) :
    ∃ N : OpenNormalSubgroup Γ, g ∉ N := by
  obtain ⟨N, hN⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one
    (G := Γ) (U := ({g} : Set Γ)ᶜ) isOpen_compl_singleton <| by
      simpa [Set.mem_compl_iff, Set.mem_singleton_iff] using hg.symm
  refine ⟨N, ?_⟩
  intro hgN
  simpa using hN hgN

/-- A finite family of elements in a profinite group can be separated in a finite
quotient by an open normal subgroup. -/
theorem open_normal_injective :
    ∀ {n : ℕ} (f : Fin n ↪ Γ),
      ∃ N : OpenNormalSubgroup Γ,
        Function.Injective (fun i : Fin n => ((f i : Γ) : Γ ⧸ (N : Subgroup Γ)))
  | 0, f => ⟨topOpenSubgroup Γ, fun i => Fin.elim0 i⟩
  | n + 1, f => by
      let g : Fin n ↪ Γ := Fin.Embedding.init f
      let a : Γ := f (Fin.last n)
      have ha : a ∉ Set.range g := by
        rintro ⟨i, hi⟩
        apply Fin.castSucc_ne_last i
        apply f.injective
        simp [g, a, Fin.Embedding.init, Fin.init] at hi
      obtain ⟨N₀, hN₀⟩ := open_normal_injective g
      have hga : ∀ i : Fin n, (g i)⁻¹ * a ≠ (1 : Γ) := by
        intro i h
        apply ha
        refine ⟨i, ?_⟩
        have h' := congrArg (fun x : Γ => g i * x) h
        simpa [mul_assoc] using h'.symm
      choose M hM using fun i : Fin n =>
        open_normal_not (Γ := Γ) (g := (g i)⁻¹ * a) (hga i)
      let K : OpenNormalSubgroup Γ := Finset.univ.inf M
      refine ⟨N₀ ⊓ K, ?_⟩
      intro i j hij
      have hmem :
          (f i)⁻¹ * f j ∈ (((N₀ ⊓ K : OpenNormalSubgroup Γ) : Subgroup Γ)) :=
        inv_mul_quotient (N := N₀ ⊓ K) hij
      rcases Fin.eq_castSucc_or_eq_last i with ⟨i', rfl⟩ | rfl
      · rcases Fin.eq_castSucc_or_eq_last j with ⟨j', rfl⟩ | rfl
        · have hmem₀ : (g i')⁻¹ * g j' ∈ (N₀ : Subgroup Γ) := by
            exact
              (show
                (((N₀ ⊓ K : OpenNormalSubgroup Γ) : Subgroup Γ) ≤
                  (N₀ : Subgroup Γ)) from
                inf_le_left) <| by
                  simpa [g, Fin.Embedding.init] using hmem
          have hij₀ : ((g i' : Γ) : Γ ⧸ (N₀ : Subgroup Γ)) = g j' := by
            have hq :
                (((g i')⁻¹ * g j' : Γ) : Γ ⧸ (N₀ : Subgroup Γ)) = 1 :=
              (QuotientGroup.eq_one_iff (N := (N₀ : Subgroup Γ)) ((g i')⁻¹ * g j')).2 hmem₀
            change ((g i' : Γ ⧸ (N₀ : Subgroup Γ))⁻¹ *
                (g j' : Γ ⧸ (N₀ : Subgroup Γ))) = 1 at hq
            exact inv_mul_eq_one.mp hq
          have hij' : i' = j' := hN₀ hij₀
          simp [hij']
        · have hmemM : (g i')⁻¹ * a ∈ (M i' : Subgroup Γ) := by
            have hKle : K ≤ M i' := by
              dsimp [K]
              exact Finset.inf_le (Finset.mem_univ i')
            exact
              (show
                (((N₀ ⊓ K : OpenNormalSubgroup Γ) : Subgroup Γ) ≤
                  (M i' : Subgroup Γ)) from
                le_trans inf_le_right hKle) <| by
                  simpa [g, a, Fin.Embedding.init, Fin.init] using hmem
          exact (hM i' hmemM).elim
      · rcases Fin.eq_castSucc_or_eq_last j with ⟨j', rfl⟩ | rfl
        · have hmemM : a⁻¹ * g j' ∈ (M j' : Subgroup Γ) := by
            have hKle : K ≤ M j' := by
              dsimp [K]
              exact Finset.inf_le (Finset.mem_univ j')
            exact
              (show
                (((N₀ ⊓ K : OpenNormalSubgroup Γ) : Subgroup Γ) ≤
                  (M j' : Subgroup Γ)) from
                le_trans inf_le_right hKle) <| by
                  simpa [g, a, Fin.Embedding.init, Fin.init] using hmem
          have hmemM' : (g j')⁻¹ * a ∈ (M j' : Subgroup Γ) := by
            simpa using (M j').inv_mem hmemM
          exact (hM j' hmemM').elim
        · rfl

variable [Infinite Γ]

/-- Open normal subgroups of an infinite profinite group have unbounded finite index. -/
theorem open_normal_index (n : ℕ) :
    ∃ N : OpenNormalSubgroup Γ, n ≤ (N : Subgroup Γ).index := by
  let f : Fin n ↪ Γ := Fin.valEmbedding.trans (Infinite.natEmbedding Γ)
  obtain ⟨N, hN⟩ := open_normal_injective (Γ := Γ) f
  refine ⟨N, ?_⟩
  have hcard := Nat.card_le_card_of_injective
    (fun i : Fin n => ((f i : Γ) : Γ ⧸ (N : Subgroup Γ))) hN
  simpa [Subgroup.index_eq_card] using hcard

/-- Lemma 5 from `Lemma5.tex`: an infinite profinite group has a descending sequence of open
normal subgroups whose indices tend to infinity. -/
theorem descending_subgroups_tendsto :
    ∃ Γs : ℕ → OpenNormalSubgroup Γ,
      Γs 0 = topOpenSubgroup Γ ∧
      (∀ j, Γs (j + 1) ≤ Γs j) ∧
      Tendsto (fun j => (Γs j : Subgroup Γ).index) atTop atTop := by
  choose U hU using fun j : ℕ => open_normal_index (Γ := Γ) (j + 1)
  let Γs : ℕ → OpenNormalSubgroup Γ :=
    Nat.rec (topOpenSubgroup Γ) (fun j Hj => Hj ⊓ U j)
  refine ⟨Γs, ?_, ?_, ?_⟩
  · simp [Γs]
  · intro j
    simp [Γs]
  · have hΓs : ∀ j, j ≤ (Γs j).toSubgroup.index := by
      intro j
      induction j with
      | zero =>
          exact Nat.zero_le _
      | succ j ih =>
          have hle : (Γs (j + 1)).toSubgroup ≤ (U j).toSubgroup := by
            have hle' : Γs (j + 1) ≤ U j := by
              simp [Γs]
            exact hle'
          haveI : ((Γs (j + 1)).toSubgroup).FiniteIndex :=
            Subgroup.finiteIndex_of_finite_quotient
          exact le_trans (hU j) (Subgroup.index_antitone hle)
    refine tendsto_atTop.2 ?_
    intro n
    refine Filter.eventually_atTop.2 ⟨n, ?_⟩
    intro j hj
    exact le_trans hj (hΓs j)

end Profinite

end Submission
