import Mathlib
import Towers.Group.DenseGenerators.ZassenhausCompact
import Towers.Group.PowerWidth.PowerSubgroups


open scoped Topology Pointwise

noncomputable section

namespace Towers

universe u
universe v w z

/-- The bounded power-word map is continuous in a topological group. -/
lemma continuous_power_word
    {Γ : Type*} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    (m : ℕ) :
    ∀ k : ℕ, Continuous (powerWordMap Γ m k)
  | 0 => by
      simpa [powerWordMap] using continuous_const
  | k + 1 => by
      have hdrop :
          Continuous
            (fun x : Fin (k + 1) → Γ =>
              fun i : Fin k => x i.castSucc) :=
        continuous_pi fun i => continuous_apply i.castSucc
      have hprev :
          Continuous
            (fun x : Fin (k + 1) → Γ =>
              powerWordMap Γ m k (fun i : Fin k => x i.castSucc)) :=
        (continuous_power_word (Γ := Γ) m k).comp hdrop
      have hlast :
          Continuous
            (fun x : Fin (k + 1) → Γ =>
              x (Fin.last k) ^ m) :=
        (continuous_apply (Fin.last k)).pow m
      simpa [powerWordMap] using hprev.mul hlast
/-- A bounded-width power subgroup is closed in a compact Hausdorff topological group. -/
lemma subgroup_closed_width
    {Γ : Type*} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [T2Space Γ]
    {m k : ℕ}
    (hwidth : HPWidth Γ m k) :
    IsClosed ((powerSubgroup Γ m : Subgroup Γ) : Set Γ) := by
  rw [power_range_width hwidth]
  simpa [Set.image_univ] using
    (isCompact_univ.image (continuous_power_word (Γ := Γ) m k)).isClosed
/-- A bounded-width power subgroup is closed in a compact totally disconnected topological group. -/
lemma closed_totally_disconnected
    {Γ : Type*} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {m k : ℕ}
    (hwidth : HPWidth Γ m k) :
    IsClosed ((powerSubgroup Γ m : Subgroup Γ) : Set Γ) := by
  letI : T2Space Γ := t_space_disconnected Γ
  exact subgroup_closed_width (Γ := Γ) hwidth
/-- Bounded width plus finite quotient makes a power subgroup open. -/
lemma power_open_width
    {Γ : Type*} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [T2Space Γ]
    {m k : ℕ}
    (hwidth : HPWidth Γ m k)
    [Finite (Γ ⧸ powerSubgroup Γ m)] :
    IsOpen ((powerSubgroup Γ m : Subgroup Γ) : Set Γ) := by
  let P : Subgroup Γ := powerSubgroup Γ m
  have hclosed : IsClosed (P : Set Γ) := by
    simpa [P] using
      (subgroup_closed_width (Γ := Γ) hwidth)
  have hfiniteIndex : P.FiniteIndex := by
    change (powerSubgroup Γ m).FiniteIndex
    exact Subgroup.finiteIndex_of_finite_quotient
  letI : P.FiniteIndex := hfiniteIndex
  exact P.isOpen_of_isClosed_of_finiteIndex hclosed
/-- Bounded width plus finite quotient makes a power subgroup open under the profinite-style
`CompactSpace`/`TotallyDisconnectedSpace` hypotheses used by the Zassenhaus separation theorem. -/
lemma width_totally_disconnected
    {Γ : Type*} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {m k : ℕ}
    (hwidth : HPWidth Γ m k)
    [Finite (Γ ⧸ powerSubgroup Γ m)] :
    IsOpen ((powerSubgroup Γ m : Subgroup Γ) : Set Γ) := by
  letI : T2Space Γ := t_space_disconnected Γ
  exact power_open_width (Γ := Γ) hwidth
end Towers
