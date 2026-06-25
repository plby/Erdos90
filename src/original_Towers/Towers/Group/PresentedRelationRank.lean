import Towers.Group.PresentedHilbert


open Filter
open scoped Pointwise EuclideanGeometry Topology BigOperators

noncomputable section

namespace Towers
namespace TBluepr

theorem hilbert_sequence_zero
    {p d r : ℕ} [Fact p.Prime]
    (rels : Fin r → FreeGroup (Fin d)) :
    presentedHilbertSequence (p := p) rels 0 = 1 := by
  let G : Type := PresentedGroup (Set.range rels)
  simpa [presentedHilbertSequence, G] using
    augmentation_finrank_one (p := p) G

theorem full_inequality_recursion
    {d r : ℕ} {A : ℕ → ℕ} {depth : Fin r → ℕ}
    (hrec :
      ∀ n : ℕ,
        d * A n ≤
          A (n + 1) +
            ∑ i : Fin r,
              if depth i ≤ n + 1 then A (n + 1 - depth i) else 0) :
    ∀ n, GShafar.fullCoefficientInequality d A depth n := by
  intro n
  cases n with
  | zero =>
      exact full_coefficient_inequality
  | succ n =>
      unfold GShafar.fullCoefficientInequality
      rw [full_nat_pos (b := A) (by omega)]
      unfold GShafar.fullRelatorTerm
      simpa [Nat.succ_eq_add_one] using hrec n

theorem presented_gs_recursion
    {p d r : ℕ} [Fact p.Prime]
    (rels : Fin r → FreeGroup (Fin d))
    (depth : Fin r → ℕ)
    (hdepth :
      ∀ i, rels i ∈ zassenhausFiltration p (FreeGroup (Fin d)) (depth i))
    (hdepth2 : ∀ i, 2 ≤ depth i)
    [Finite (PresentedGroup (Set.range rels))]
    [Nontrivial (PresentedGroup (Set.range rels))]
    (hPGroup : IsPGroup p (PresentedGroup (Set.range rels)))
    (hrec :
      ∀ n : ℕ,
        d * presentedHilbertSequence (p := p) rels n ≤
          presentedHilbertSequence (p := p) rels (n + 1) +
            ∑ i : Fin r,
              if depth i ≤ n + 1 then
                presentedHilbertSequence (p := p) rels (n + 1 - depth i)
              else 0)
    {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    0 < GShafar.relatorExpression d r depth t := by
  exact
    gs_full_inequalities
      (p := p) (d := d) (r := r) rels depth hdepth hdepth2 hPGroup
      (full_inequality_recursion (A :=
        presentedHilbertSequence (p := p) rels) (depth := depth) hrec)
      ht0 ht1

set_option synthInstance.maxHeartbeats 80000 in
-- The presented-source quotient requires deeper finite-module synthesis.
theorem finrank_presented_high
    {p d r : ℕ} [Fact p.Prime]
    (rels : Fin r → FreeGroup (Fin d)) (depth : Fin r → ℕ) (n : ℕ)
    [Finite (PresentedGroup (Set.range rels))] :
    Module.finrank (ZMod p)
        (pHSrc (p := p) rels depth n) =
      ∑ i, if depth i ≤ n then
        presentedHilbertSequence (p := p) rels (n - depth i)
      else 0 := by
  classical
  have hactive :
      (∑ i : pARelato depth n,
          presentedHilbertSequence (p := p) rels (n - depth i.1)) =
        ∑ i, if depth i ≤ n then
          presentedHilbertSequence (p := p) rels (n - depth i)
        else 0 :=
    presented_active_relators depth n
      (fun i => presentedHilbertSequence (p := p) rels (n - depth i))
  simp [pHSrc, finrank_presented_layer,
    Module.finrank_pi_fintype, hactive]

theorem high_numeric_rank
    {p d r : ℕ} [Fact p.Prime]
    (rels : Fin r → FreeGroup (Fin d))
    (depth : Fin r → ℕ)
    [Finite (PresentedGroup (Set.range rels))]
    (n : ℕ)
    (hrank :
      Module.finrank (ZMod p)
          (pGTarget (p := p) rels n) ≤
        Module.finrank (ZMod p)
            (pALayer (p := p) rels n) +
          Module.finrank (ZMod p)
            (pHSrc (p := p) rels depth n)) :
    d * presentedHilbertSequence (p := p) rels (n - 1) ≤
      presentedHilbertSequence (p := p) rels n +
        ∑ i, if depth i ≤ n then
          presentedHilbertSequence (p := p) rels (n - depth i)
        else 0 := by
  classical
  calc
    d * presentedHilbertSequence (p := p) rels (n - 1) =
        Module.finrank (ZMod p)
          (pGTarget (p := p) rels n) := by
      rw [finrank_high_target (p := p) rels n]
    _ ≤
        Module.finrank (ZMod p)
            (pALayer (p := p) rels n) +
          Module.finrank (ZMod p)
            (pHSrc (p := p) rels depth n) :=
      hrank
    _ =
      presentedHilbertSequence (p := p) rels n +
        ∑ i, if depth i ≤ n then
          presentedHilbertSequence (p := p) rels (n - depth i)
        else 0 := by
      rw [finrank_presented_layer,
        finrank_presented_high (p := p) rels depth n]

theorem full_inequality_bounds
    {p d r : ℕ} [Fact p.Prime]
    (rels : Fin r → FreeGroup (Fin d))
    (depth : Fin r → ℕ)
    (hdepth :
      ∀ i, rels i ∈ zassenhausFiltration p (FreeGroup (Fin d)) (depth i))
    (hdepth2 : ∀ i, 2 ≤ depth i)
    [Finite (PresentedGroup (Set.range rels))]
    [Nontrivial (PresentedGroup (Set.range rels))]
    (hPGroup : IsPGroup p (PresentedGroup (Set.range rels)))
    (hrank :
      ∀ n, 2 ≤ n →
        Module.finrank (ZMod p)
            (pGTarget (p := p) rels n) ≤
          Module.finrank (ZMod p)
              (pALayer (p := p) rels n) +
            Module.finrank (ZMod p)
              (pHSrc (p := p) rels depth n)) :
    ∀ n, GShafar.fullCoefficientInequality d
      (presentedHilbertSequence (p := p) rels) depth n := by
  intro n
  by_cases hn0 : n = 0
  · subst n
    exact full_coefficient_inequality
  by_cases hn1 : n = 1
  · subst n
    exact
      presented_full_inequality
        rels depth hdepth hdepth2 hPGroup
  have hn2 : 2 ≤ n := by omega
  exact
    full_inequality_high
      (b := presentedHilbertSequence (p := p) rels)
      (depth := depth)
      (n := n)
      (by omega)
      (high_numeric_rank
        rels depth n (hrank n hn2))

theorem gs_rank_bounds
    {p d r : ℕ} [Fact p.Prime]
    (rels : Fin r → FreeGroup (Fin d))
    (depth : Fin r → ℕ)
    (hdepth :
      ∀ i, rels i ∈ zassenhausFiltration p (FreeGroup (Fin d)) (depth i))
    (hdepth2 : ∀ i, 2 ≤ depth i)
    [Finite (PresentedGroup (Set.range rels))]
    [Nontrivial (PresentedGroup (Set.range rels))]
    (hPGroup : IsPGroup p (PresentedGroup (Set.range rels)))
    (hrank :
      ∀ n, 2 ≤ n →
        Module.finrank (ZMod p)
            (pGTarget (p := p) rels n) ≤
          Module.finrank (ZMod p)
              (pALayer (p := p) rels n) +
            Module.finrank (ZMod p)
              (pHSrc (p := p) rels depth n))
    {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    0 < GShafar.relatorExpression d r depth t := by
  exact
    gs_full_inequalities
      (p := p) (d := d) (r := r) rels depth hdepth hdepth2 hPGroup
      (full_inequality_bounds
        rels depth hdepth hdepth2 hPGroup hrank)
      ht0 ht1
end TBluepr

end Towers
