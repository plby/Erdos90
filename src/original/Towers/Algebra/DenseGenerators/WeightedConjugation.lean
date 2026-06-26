import Towers.Algebra.DenseGenerators.WeightedFiltration


open scoped Topology Pointwise commutatorElement

noncomputable section

namespace Towers

universe u

/-- Every old weighted element remains in the corresponding cyclic extension. -/
lemma cyclic_j_old
    {p : ℕ} [Fact p.Prime]
    {G : Type u} [Group G]
    (W : WFilt p G)
    {x : G} {w r : ℕ}
    {a : denseGroupAlgebra p G}
    (ha : a ∈ W.J r) :
    a ∈ cyclicExtendJ W.J x w r := by
  let e0 : Fin p := ⟨0, (Fact.out : Nat.Prime p).pos⟩
  have hmem :
      a * groupAlgebraSub p G x ^ (e0 : ℕ) ∈
        cyclicExtendJ W.J x w r :=
    extend_j
      (p := p) (G := G) (J := W.J) W.anti
      (x := x) (w := w) (m := r) (s := r) (e := e0)
      ha (by simp [e0])
  simpa [e0] using hmem

/-- The newly adjoined augmentation letter has its assigned weight. -/
lemma cyclic_extend_j
    {p : ℕ} [Fact p.Prime]
    {G : Type u} [Group G]
    (W : WFilt p G)
    {x : G} {w : ℕ} :
    groupAlgebraSub p G x ∈ cyclicExtendJ W.J x w w := by
  let e1 : Fin p := ⟨1, (Fact.out : Nat.Prime p).one_lt⟩
  have hmem :
      (1 : denseGroupAlgebra p G) *
          groupAlgebraSub p G x ^ (e1 : ℕ) ∈
        cyclicExtendJ W.J x w w :=
    extend_j
      (p := p) (G := G) (J := W.J) W.anti
      (x := x) (w := w) (m := w) (s := 0) (e := e1)
      W.one_mem (by simp [e1])
  simpa [e1] using hmem

namespace WFilt

/-- Natural powers multiply weight inside a multiplicative weight filtration. -/
lemma pow_mem
    {p : ℕ} [Fact p.Prime]
    {G : Type u} [Group G]
    (W : WFilt p G)
    {r : ℕ}
    {a : denseGroupAlgebra p G}
    (ha : a ∈ W.J r)
    (n : ℕ) :
    a ^ n ∈ W.J (n * r) := by
  induction n with
  | zero =>
      simpa using W.one_mem
  | succ n ih =>
      simpa [pow_succ, Nat.succ_mul] using W.mul_mem ih ha

/-- A deeper error between two letters propagates to all natural powers. -/
lemma pow_sub_mem
    {p : ℕ} [Fact p.Prime]
    {G : Type u} [Group G]
    (W : WFilt p G)
    {r w : ℕ}
    {a b : denseGroupAlgebra p G}
    (ha : a ∈ W.J r)
    (hb : b ∈ W.J r)
    (hab : a - b ∈ W.J (w + r))
    (n : ℕ) :
    a ^ n - b ^ n ∈ W.J (w + n * r) := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      have hleft :
          a ^ n * (a - b) ∈ W.J (w + (n + 1) * r) := by
        simpa [Nat.succ_mul, add_assoc, add_comm, add_left_comm] using
          W.mul_mem (W.pow_mem ha n) hab
      have hright :
          (a ^ n - b ^ n) * b ∈ W.J (w + (n + 1) * r) := by
        simpa [Nat.succ_mul, add_assoc, add_comm, add_left_comm] using
          W.mul_mem ih hb
      have hsum :
          a ^ n * (a - b) + (a ^ n - b ^ n) * b ∈
            W.J (w + (n + 1) * r) :=
        (W.J (w + (n + 1) * r)).add_mem hleft hright
      have heq :
          a ^ (n + 1) - b ^ (n + 1) =
            a ^ n * (a - b) + (a ^ n - b ^ n) * b := by
        rw [pow_succ, pow_succ]
        noncomm_ring
      rw [heq]
      exact hsum

end WFilt

/-- Conjugating an augmentation letter changes it by the commutator letter times the original
group-basis element. -/
lemma conj_ga_algebra
    {p : ℕ} [Fact p.Prime]
    {G : Type u} [Group G]
    (x y : G) :
    conjGA p G x (groupAlgebraSub p G y) -
        groupAlgebraSub p G y =
      groupAlgebraSub p G ⁅x, y⁆ * ga p G y := by
  have hconj : x * y * x⁻¹ = ⁅x, y⁆ * y := by
    simp only [commutatorElement_def]
    group
  have hinv :
      denseGeneratorsElement p G x *
          denseGeneratorsElement p G x⁻¹ =
        (1 : denseGroupAlgebra p G) := by
    simp 
  simp only [conjGA, groupAlgebraSub, ga]
  rw [mul_sub, sub_mul]
  simp only [mul_one]
  rw [← dense_element_mul,
    ← dense_element_mul,
    ← dense_element_mul]
  rw [hconj]
  simp only [dense_element_mul]
  rw [hinv]
  noncomm_ring

/-- A conjugation error estimate propagates through one certified cyclic extension.

The old-prefix estimate handles coefficients. The second hypothesis handles the newly adjoined
letter. Multiplicativity and the power-difference lemma then collect every cyclic normal-form
component at the expected increased weight. -/
lemma conj_ga_extension
    {p : ℕ} [Fact p.Prime]
    {G : Type u} [Group G]
    {W : WFilt p G}
    (S : CEDataa p G W)
    {x : G} {wx r : ℕ}
    (herrorOld :
      ∀ {s : ℕ} {a : denseGroupAlgebra p G},
        a ∈ W.J s →
          conjGA p G x a - a ∈ W.J (s + wx))
    (herrorY :
      conjGA p G x (groupAlgebraSub p G S.x) -
          groupAlgebraSub p G S.x ∈
        S.next.J (S.w + wx))
    {a : denseGroupAlgebra p G}
    (ha : a ∈ S.next.J r) :
    conjGA p G x a - a ∈ S.next.J (r + wx) := by
  let Y : denseGroupAlgebra p G :=
    groupAlgebraSub p G S.x
  change a ∈ cyclicExtendJ W.J S.x S.w r at ha
  change
    conjGA p G x a - a ∈
      cyclicExtendJ W.J S.x S.w (r + wx)
  dsimp [cyclicExtendJ] at ha
  refine
    Submodule.iSup_induction
      (fun e : Fin p =>
        (W.J (r - (e : ℕ) * S.w)).map
          (rightMulLinear (Y ^ (e : ℕ))))
      (motive := fun a =>
        conjGA p G x a - a ∈
          cyclicExtendJ W.J S.x S.w (r + wx))
      ha
      ?mem
      ?zero
      ?add
  · intro e z hz
    rcases Submodule.mem_map.mp hz with ⟨u, hu, rfl⟩
    have herrorU :
        conjGA p G x u - u ∈ W.J ((r - (e : ℕ) * S.w) + wx) :=
      herrorOld hu
    have hconjU :
        conjGA p G x u ∈ W.J (r - (e : ℕ) * S.w) :=
      conj_ga_error W hu herrorU
    have hY :
        Y ∈ S.next.J S.w := by
      change
        groupAlgebraSub p G S.x ∈
          cyclicExtendJ W.J S.x S.w S.w
      exact cyclic_extend_j W
    have herrorY' :
        conjGA p G x Y - Y ∈ S.next.J (wx + S.w) := by
      simpa [Y, add_comm] using herrorY
    have hconjY :
        conjGA p G x Y ∈ S.next.J S.w :=
      conj_ga_error S.next hY (by
        simpa [add_comm] using herrorY')
    have herrorUV :
        conjGA p G x u - u ∈
          S.next.J ((r - (e : ℕ) * S.w) + wx) := by
      change
        conjGA p G x u - u ∈
          cyclicExtendJ W.J S.x S.w ((r - (e : ℕ) * S.w) + wx)
      exact cyclic_j_old W herrorU
    have huV :
        u ∈ S.next.J (r - (e : ℕ) * S.w) := by
      change
        u ∈ cyclicExtendJ W.J S.x S.w (r - (e : ℕ) * S.w)
      exact cyclic_j_old W hu
    have hconjYPow :
        conjGA p G x Y ^ (e : ℕ) ∈ S.next.J ((e : ℕ) * S.w) :=
      S.next.pow_mem hconjY (e : ℕ)
    have herrorYPow :
        conjGA p G x Y ^ (e : ℕ) - Y ^ (e : ℕ) ∈
          S.next.J (wx + (e : ℕ) * S.w) :=
      S.next.pow_sub_mem hconjY hY herrorY' (e : ℕ)
    have hterm1Raw :
        (conjGA p G x u - u) * conjGA p G x Y ^ (e : ℕ) ∈
          S.next.J (((r - (e : ℕ) * S.w) + wx) + (e : ℕ) * S.w) :=
      S.next.mul_mem herrorUV hconjYPow
    have hterm2Raw :
        u * (conjGA p G x Y ^ (e : ℕ) - Y ^ (e : ℕ)) ∈
          S.next.J ((r - (e : ℕ) * S.w) + (wx + (e : ℕ) * S.w)) :=
      S.next.mul_mem huV herrorYPow
    have hle :
        r + wx ≤ (r - (e : ℕ) * S.w) + (wx + (e : ℕ) * S.w) :=
      nat_add_sub r wx (e : ℕ) S.w
    have hterm1 :
        (conjGA p G x u - u) * conjGA p G x Y ^ (e : ℕ) ∈
          S.next.J (r + wx) :=
      S.next.anti (by simpa [add_assoc] using hle) hterm1Raw
    have hterm2 :
        u * (conjGA p G x Y ^ (e : ℕ) - Y ^ (e : ℕ)) ∈
          S.next.J (r + wx) :=
      S.next.anti hle hterm2Raw
    have hsum :
        (conjGA p G x u - u) * conjGA p G x Y ^ (e : ℕ) +
            u * (conjGA p G x Y ^ (e : ℕ) - Y ^ (e : ℕ)) ∈
          S.next.J (r + wx) :=
      (S.next.J (r + wx)).add_mem hterm1 hterm2
    have hgoalEq :
        conjGA p G x (rightMulLinear (Y ^ (e : ℕ)) u) -
            rightMulLinear (Y ^ (e : ℕ)) u =
          (conjGA p G x u - u) * conjGA p G x Y ^ (e : ℕ) +
            u * (conjGA p G x Y ^ (e : ℕ) - Y ^ (e : ℕ)) := by
      change
        conjGA p G x (u * Y ^ (e : ℕ)) - u * Y ^ (e : ℕ) =
          (conjGA p G x u - u) * conjGA p G x Y ^ (e : ℕ) +
            u * (conjGA p G x Y ^ (e : ℕ) - Y ^ (e : ℕ))
      rw [conjGA_mul, conjGA_pow]
      noncomm_ring
    change
      conjGA p G x (rightMulLinear (Y ^ (e : ℕ)) u) -
          rightMulLinear (Y ^ (e : ℕ)) u ∈
        cyclicExtendJ W.J S.x S.w (r + wx)
    rw [hgoalEq]
    exact hsum
  · simp [conjGA]
  · intro a b ha' hb'
    have hsum :
        (conjGA p G x a - a) + (conjGA p G x b - b) ∈
          cyclicExtendJ W.J S.x S.w (r + wx) :=
      (cyclicExtendJ W.J S.x S.w (r + wx)).add_mem ha' hb'
    have hgoalEq :
        conjGA p G x (a + b) - (a + b) =
          (conjGA p G x a - a) + (conjGA p G x b - b) := by
      rw [conjGA_add]
      noncomm_ring
    rw [hgoalEq]
    exact hsum

end Towers
