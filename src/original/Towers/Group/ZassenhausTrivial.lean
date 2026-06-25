import Towers.Group.GolodShafarevichCore


open Filter
open scoped Pointwise Topology

noncomputable section

universe u v

namespace Towers

section TrivialZassenhausPGroup

variable {p : ℕ} [Fact p.Prime]
variable {Q : Type u} [Group Q]

omit [Fact (Nat.Prime p)] in
/-- Lower-central terms sit in the corresponding Zassenhaus terms. -/
lemma lower_filtration_succ (i : ℕ) :
    Subgroup.lowerCentralSeries Q i ≤ zassenhausFiltration p Q (i + 1) := by
  intro x hx
  apply Subgroup.subset_closure
  refine ⟨i, 0, x, hx, ?_, ?_⟩
  · rw [pow_zero, mul_one]
  · simp

/-- If a positive Zassenhaus term is trivial, then every element has `p`-power order. -/
lemma p_filtration_bot
    {m : ℕ}
    (hbot : zassenhausFiltration p Q m = ⊥) :
    IsPGroup p Q := by
  intro g
  refine ⟨m, ?_⟩
  have hm : m ≤ p ^ m :=
    (m.lt_two_pow_self).le.trans
      (Nat.pow_le_pow_left (Nat.Prime.two_le (Fact.out : Nat.Prime p)) m)
  have hgD : g ^ p ^ m ∈ zassenhausFiltration p Q m :=
    Subgroup.subset_closure
      ⟨0, m, g, by simp, by simpa using hm, rfl⟩
  have hgbot : g ^ p ^ m ∈ (⊥ : Subgroup Q) := by
    simpa [hbot] using hgD
  exact Subgroup.mem_bot.mp hgbot

/-- Under a trivial Zassenhaus term, the finite group has prime-power cardinality. -/
lemma card_filtration_bot
    {m : ℕ}
    [Finite Q]
    (hbot : zassenhausFiltration p Q m = ⊥) :
    ∃ k : ℕ, Nat.card Q = p ^ k := by
  exact
    IsPGroup.iff_card.mp
      (p_filtration_bot
        (p := p) (Q := Q) hbot)

omit [Fact (Nat.Prime p)] in
/-- A trivial Zassenhaus term above `D₁` makes the group nilpotent. -/
lemma nilpotent_filtration_bot
    {m : ℕ}
    (hm : 1 < m)
    (hbot : zassenhausFiltration p Q m = ⊥) :
    Group.IsNilpotent Q := by
  have hlower :
      Subgroup.lowerCentralSeries Q (m - 1) ≤ zassenhausFiltration p Q m := by
    simpa [Nat.sub_add_cancel (le_of_lt hm)] using
      (lower_filtration_succ
        (p := p) (Q := Q) (i := m - 1))
  have hlower_bot : Subgroup.lowerCentralSeries Q (m - 1) = ⊥ := by
    rw [eq_bot_iff, ← hbot]
    exact hlower
  exact (Subgroup.nilpotent_iff_lowerCentralSeries).2 ⟨m - 1, hlower_bot⟩

end TrivialZassenhausPGroup

end Towers
