import Mathlib
import Submission.Algebra.DenseGenerators.JenningsDegreeOne


open scoped Topology Pointwise

noncomputable section

namespace Submission

universe u
universe v w z

/-- The ordinary group-algebra element `[g] - 1`.

This is a short local alias for the finite group-algebra canonical element already used
throughout this file. -/
abbrev groupAlgebraSub
    (p : ℕ) [Fact p.Prime]
    (G : Type u) [Group G]
    (g : G) :
    denseGroupAlgebra p G :=
  denseGeneratorsElement p G g - 1

/-- Short notation for the group-basis element `[g]` in the ordinary finite group algebra. -/
abbrev ga
    (p : ℕ) [Fact p.Prime]
    (G : Type u) [Group G]
    (g : G) :
    denseGroupAlgebra p G :=
  denseGeneratorsElement p G g

@[simp]
lemma ga_one
    {p : ℕ} [Fact p.Prime]
    {G : Type u} [Group G] :
    ga p G (1 : G) = (1 : denseGroupAlgebra p G) := by
  simp [ga]

@[simp]
lemma ga_mul
    {p : ℕ} [Fact p.Prime]
    {G : Type u} [Group G]
    (x y : G) :
    ga p G (x * y) = ga p G x * ga p G y := by
  simp [ga]

@[simp]
lemma ga_inv_mul
    {p : ℕ} [Fact p.Prime]
    {G : Type u} [Group G]
    (x : G) :
    ga p G x⁻¹ * ga p G x = (1 : denseGroupAlgebra p G) := by
  rw [← ga_mul]
  simp

@[simp]
lemma ga_mul_inv
    {p : ℕ} [Fact p.Prime]
    {G : Type u} [Group G]
    (x : G) :
    ga p G x * ga p G x⁻¹ = (1 : denseGroupAlgebra p G) := by
  rw [← ga_mul]
  simp

/-- Conjugation by a group-basis unit in the ordinary finite group algebra. -/
def conjGA
    (p : ℕ) [Fact p.Prime]
    (G : Type u) [Group G]
    (x : G)
    (a : denseGroupAlgebra p G) :
    denseGroupAlgebra p G :=
  ga p G x * a * ga p G x⁻¹

/-- Conjugation by a group-basis element preserves products. -/
lemma conjGA_mul
    {p : ℕ} [Fact p.Prime]
    {G : Type u} [Group G]
    (x : G)
    (a b : denseGroupAlgebra p G) :
    conjGA p G x (a * b) = conjGA p G x a * conjGA p G x b := by
  have hinv :
      ga p G x⁻¹ * ga p G x =
        (1 : denseGroupAlgebra p G) :=
    ga_inv_mul x
  calc
    conjGA p G x (a * b) =
        ga p G x * a * (b * ga p G x⁻¹) := by
          simp [conjGA, mul_assoc]
    _ =
        ga p G x * a *
          (ga p G x⁻¹ * (ga p G x * (b * ga p G x⁻¹))) := by
          rw [← mul_assoc (ga p G x⁻¹) (ga p G x) (b * ga p G x⁻¹), hinv]
          simp
    _ = conjGA p G x a * conjGA p G x b := by
          simp only [conjGA]
          ac_rfl

/-- Conjugation by a group-basis element preserves sums. -/
lemma conjGA_add
    {p : ℕ} [Fact p.Prime]
    {G : Type u} [Group G]
    (x : G)
    (a b : denseGroupAlgebra p G) :
    conjGA p G x (a + b) = conjGA p G x a + conjGA p G x b := by
  simp [conjGA, add_mul, mul_add]

/-- Conjugation by a group-basis element preserves natural powers. -/
lemma conjGA_pow
    {p : ℕ} [Fact p.Prime]
    {G : Type u} [Group G]
    (x : G)
    (a : denseGroupAlgebra p G)
    (n : ℕ) :
    conjGA p G x (a ^ n) = conjGA p G x a ^ n := by
  induction n with
  | zero =>
      simp [conjGA]
  | succ n ih =>
      rw [pow_succ, conjGA_mul, ih, pow_succ]

/-- A commuting group element fixes the corresponding augmentation letter under conjugation. -/
lemma ga_self_commute
    {p : ℕ} [Fact p.Prime]
    {G : Type u} [Group G]
    {x y : G}
    (hxy : Commute x y) :
    conjGA p G x (groupAlgebraSub p G y) =
      groupAlgebraSub p G y := by
  have hconj : x * y * x⁻¹ = y := by
    calc
      x * y * x⁻¹ = y * x * x⁻¹ := by rw [hxy.eq]
      _ = y := by simp
  simp only [conjGA, groupAlgebraSub, ga]
  rw [mul_sub, sub_mul]
  simp only [mul_one]
  rw [← dense_element_mul,
    ← dense_element_mul]
  simp [hconj]

/-- Moving a new augmentation letter past an old group-algebra element.

This is the algebraic identity driving the cyclic-extension collection step:
`([x] - 1) a = ([x] a [x⁻¹]) ([x] - 1) + ([x] a [x⁻¹] - a)`. -/
lemma sub_ga_add
    {p : ℕ} [Fact p.Prime]
    {G : Type u} [Group G]
    (x : G)
    (a : denseGroupAlgebra p G) :
    groupAlgebraSub p G x * a =
      conjGA p G x a * groupAlgebraSub p G x +
        (conjGA p G x a - a) := by
  simp only [groupAlgebraSub, conjGA, ga]
  have hright :
      denseGeneratorsElement p G x⁻¹ *
          denseGeneratorsElement p G x =
        (1 : denseGroupAlgebra p G) := by
    rw [← dense_element_mul]
    simp
  noncomm_ring [hright]

/-- Right multiplication by a fixed group-algebra element, as a `ZMod p`-linear map. -/
def rightMulLinear
    {p : ℕ} [Fact p.Prime]
    {G : Type u} [Group G]
    (a : denseGroupAlgebra p G) :
    denseGroupAlgebra p G →ₗ[ZMod p]
      denseGroupAlgebra p G where
  toFun b := b * a
  map_add' := by
    intro b c
    simp [add_mul]
  map_smul' := by
    intro r b
    simp

/-- One cyclic-extension step for a Jennings-style weight filtration.

If `J m` is the old span of terms of weight at least `m`, then adjoining a new letter
`Y = [x] - 1` of weight `w` gives the span of terms `a * Y^e`, with
`a ∈ J (m - e*w)` and `0 ≤ e < p`. -/
def cyclicExtendJ
    {p : ℕ} [Fact p.Prime]
    {G : Type u} [Group G]
    (J : ℕ → Submodule (ZMod p) (denseGroupAlgebra p G))
    (x : G) (w m : ℕ) :
    Submodule (ZMod p) (denseGroupAlgebra p G) :=
  ⨆ e : Fin p,
    (J (m - (e : ℕ) * w)).map
      (rightMulLinear ((groupAlgebraSub p G x) ^ (e : ℕ)))

/-- A component term belongs to the cyclic extension at every compatible weight. -/
lemma extend_j
    {p : ℕ} [Fact p.Prime]
    {G : Type u} [Group G]
    {J : ℕ → Submodule (ZMod p) (denseGroupAlgebra p G)}
    (hanti : Antitone J)
    {x : G} {w m s : ℕ} {e : Fin p}
    {a : denseGroupAlgebra p G}
    (ha : a ∈ J s)
    (hm : m ≤ s + (e : ℕ) * w) :
    a * (groupAlgebraSub p G x) ^ (e : ℕ) ∈
      cyclicExtendJ J x w m := by
  have hsub : m - (e : ℕ) * w ≤ s := by
    exact Nat.sub_le_iff_le_add.mpr (by simpa [add_comm, add_left_comm, add_assoc] using hm)
  have ha' : a ∈ J (m - (e : ℕ) * w) :=
    hanti hsub ha
  have hmap :
      a * (groupAlgebraSub p G x) ^ (e : ℕ) ∈
        (J (m - (e : ℕ) * w)).map
          (rightMulLinear ((groupAlgebraSub p G x) ^ (e : ℕ))) := by
    exact ⟨a, ha', rfl⟩
  exact Submodule.mem_iSup_of_mem e hmap

/-- The cyclic-extension construction remains antitone in the target weight. -/
lemma extend_j_antitone
    {p : ℕ} [Fact p.Prime]
    {G : Type u} [Group G]
    {J : ℕ → Submodule (ZMod p) (denseGroupAlgebra p G)}
    (hanti : Antitone J)
    (x : G) (w : ℕ) :
    Antitone (cyclicExtendJ J x w) := by
  intro m n hmn
  dsimp [cyclicExtendJ]
  refine iSup_le ?_
  intro e
  exact
    (Submodule.map_mono
      (hanti (Nat.sub_le_sub_right hmn ((e : ℕ) * w)))).trans
        (le_iSup
          (fun e : Fin p =>
            (J (m - (e : ℕ) * w)).map
              (rightMulLinear ((groupAlgebraSub p G x) ^ (e : ℕ)))) e)

/-- An abstract multiplicative weight filtration on the finite group algebra.

The later Jennings construction will build such filtrations by adjoining one weighted cyclic
generator at a time. -/
structure WFilt
    (p : ℕ) [Fact p.Prime]
    (G : Type u) [Group G] where
  J : ℕ → Submodule (ZMod p) (denseGroupAlgebra p G)
  anti : Antitone J
  one_mem : (1 : denseGroupAlgebra p G) ∈ J 0
  mul_mem :
    ∀ {r s : ℕ} {a b : denseGroupAlgebra p G},
      a ∈ J r →
      b ∈ J s →
        a * b ∈ J (r + s)

lemma nat_sub_succ
    (m e w : ℕ) :
    m + w ≤ (m - e * w) + (e + 1) * w := by
  by_cases hle : e * w ≤ m
  · have hcancel : m - e * w + e * w = m :=
      Nat.sub_add_cancel hle
    calc
      m + w = (m - e * w + e * w) + w := by rw [hcancel]
      _ = (m - e * w) + (e * w + w) := by omega
      _ ≤ (m - e * w) + (e + 1) * w := by
        rw [Nat.succ_mul]
  · have hlt : m < e * w := Nat.lt_of_not_ge hle
    have hmw : m + w ≤ e * w + w :=
      Nat.add_le_add_right hlt.le w
    have htarget :
        e * w + w ≤ (m - e * w) + (e + 1) * w := by
      have hzero : m - e * w = 0 :=
        Nat.sub_eq_zero_of_le hlt.le
      rw [hzero, zero_add, Nat.succ_mul]
    exact le_trans hmw htarget

lemma nat_sub_weight
    (m e w : ℕ) :
    m + w ≤ ((m - e * w) + w) + e * w := by
  by_cases hle : e * w ≤ m
  · have hcancel : m - e * w + e * w = m :=
      Nat.sub_add_cancel hle
    omega
  · have hlt : m < e * w := Nat.lt_of_not_ge hle
    have hzero : m - e * w = 0 :=
      Nat.sub_eq_zero_of_le hlt.le
    omega

lemma nat_sub_mul
    (r m e w : ℕ) :
    r + m ≤ (r + (m - e * w)) + e * w := by
  by_cases hle : e * w ≤ m
  · have hcancel : m - e * w + e * w = m :=
      Nat.sub_add_cancel hle
    omega
  · have hlt : m < e * w := Nat.lt_of_not_ge hle
    have hzero : m - e * w = 0 :=
      Nat.sub_eq_zero_of_le hlt.le
    omega

lemma nat_add_sub
    (r s e w : ℕ) :
    r + s ≤ (r - e * w) + (s + e * w) := by
  by_cases hle : e * w ≤ r
  · have hcancel : r - e * w + e * w = r :=
      Nat.sub_add_cancel hle
    omega
  · have hlt : r < e * w := Nat.lt_of_not_ge hle
    have hzero : r - e * w = 0 :=
      Nat.sub_eq_zero_of_le hlt.le
    omega

/-- In a cyclic extension, right multiplication by the new letter raises weight by its weight. -/
lemma cyclic_j_y
    {p : ℕ} [Fact p.Prime]
    {G : Type u} [Group G]
    (W : WFilt p G)
    {x : G} {w m : ℕ}
    (hpow :
      (groupAlgebraSub p G x) ^ p ∈ W.J (p * w))
    {a : denseGroupAlgebra p G}
    (ha : a ∈ cyclicExtendJ W.J x w m) :
    a * groupAlgebraSub p G x ∈ cyclicExtendJ W.J x w (m + w) := by
  let Y : denseGroupAlgebra p G := groupAlgebraSub p G x
  dsimp [cyclicExtendJ] at ha ⊢
  refine
    Submodule.iSup_induction
      (fun e : Fin p =>
        (W.J (m - (e : ℕ) * w)).map
          (rightMulLinear (Y ^ (e : ℕ))))
      (motive := fun a =>
        a * groupAlgebraSub p G x ∈ cyclicExtendJ W.J x w (m + w))
      ha
      ?mem
      ?zero
      ?add
  · intro e z hz
    rcases (Submodule.mem_map.mp hz) with ⟨u, hu, rfl⟩
    by_cases hlt : (e : ℕ) + 1 < p
    · let e' : Fin p := ⟨(e : ℕ) + 1, hlt⟩
      have hweight :
          m + w ≤ (m - (e : ℕ) * w) + (e' : ℕ) * w := by
        simpa [e'] using
          nat_sub_succ m (e : ℕ) w
      have hmem :
          u * Y ^ (e' : ℕ) ∈
            ⨆ e : Fin p,
              (W.J (m + w - (e : ℕ) * w)).map
                (rightMulLinear (Y ^ (e : ℕ))) :=
        extend_j
          (p := p) (G := G) (J := W.J) W.anti
          (x := x) (w := w) (m := m + w)
          (s := m - (e : ℕ) * w) (e := e') hu hweight
      simpa [rightMulLinear, Y, e', pow_succ, mul_assoc] using hmem
    · have heq : (e : ℕ) + 1 = p := by
        omega
      let e0 : Fin p := ⟨0, (Fact.out : Nat.Prime p).pos⟩
      have hupow : u * Y ^ p ∈ W.J ((m - (e : ℕ) * w) + p * w) := by
        exact W.mul_mem hu (by simpa [Y] using hpow)
      have hweight :
          m + w ≤ ((m - (e : ℕ) * w) + p * w) + (e0 : ℕ) * w := by
        simpa [e0, heq] using
          nat_sub_succ m (e : ℕ) w
      have hmem :
          (u * Y ^ p) * Y ^ (e0 : ℕ) ∈
            ⨆ e : Fin p,
              (W.J (m + w - (e : ℕ) * w)).map
                (rightMulLinear (Y ^ (e : ℕ))) :=
        extend_j
          (p := p) (G := G) (J := W.J) W.anti
          (x := x) (w := w) (m := m + w)
          (s := (m - (e : ℕ) * w) + p * w) (e := e0) hupow hweight
      have hpowe : Y ^ (e : ℕ) * Y = Y ^ p := by
        rw [← pow_succ, heq]
      simpa [cyclicExtendJ, rightMulLinear, Y, e0, hpowe, mul_assoc] using hmem
  · simp
  · intro a b ha' hb'
    simpa [add_mul] using
      (cyclicExtendJ W.J x w (m + w)).add_mem ha' hb'

/-- In a cyclic extension, left multiplication by the new letter raises weight by its weight,
provided conjugation preserves the old filtration and its error raises weight. -/
lemma cyclic_extend_y
    {p : ℕ} [Fact p.Prime]
    {G : Type u} [Group G]
    (W : WFilt p G)
    {x : G} {w m : ℕ}
    (hpow :
      (groupAlgebraSub p G x) ^ p ∈ W.J (p * w))
    (hconj :
      ∀ {r : ℕ} {a : denseGroupAlgebra p G},
        a ∈ W.J r →
          conjGA p G x a ∈ W.J r)
    (herror :
      ∀ {r : ℕ} {a : denseGroupAlgebra p G},
        a ∈ W.J r →
          conjGA p G x a - a ∈ W.J (r + w))
    {a : denseGroupAlgebra p G}
    (ha : a ∈ cyclicExtendJ W.J x w m) :
    groupAlgebraSub p G x * a ∈ cyclicExtendJ W.J x w (m + w) := by
  let Y : denseGroupAlgebra p G := groupAlgebraSub p G x
  dsimp [cyclicExtendJ] at ha
  refine
    Submodule.iSup_induction
      (fun e : Fin p =>
        (W.J (m - (e : ℕ) * w)).map
          (rightMulLinear (Y ^ (e : ℕ))))
      (motive := fun a =>
        groupAlgebraSub p G x * a ∈ cyclicExtendJ W.J x w (m + w))
      ha
      ?mem
      ?zero
      ?add
  · intro e z hz
    rcases (Submodule.mem_map.mp hz) with ⟨u, hu, rfl⟩
    have hmove :
        Y * u = conjGA p G x u * Y + (conjGA p G x u - u) := by
      simpa [Y] using
        sub_ga_add
          (p := p) (G := G) x u
    have hmain :
        (conjGA p G x u * Y) * Y ^ (e : ℕ) ∈
          cyclicExtendJ W.J x w (m + w) := by
      by_cases hlt : (e : ℕ) + 1 < p
      · let e' : Fin p := ⟨(e : ℕ) + 1, hlt⟩
        have hweight :
            m + w ≤ (m - (e : ℕ) * w) + (e' : ℕ) * w := by
          simpa [e'] using
            nat_sub_succ m (e : ℕ) w
        have hmem :
            conjGA p G x u * Y ^ (e' : ℕ) ∈
              cyclicExtendJ W.J x w (m + w) :=
          extend_j
            (p := p) (G := G) (J := W.J) W.anti
            (x := x) (w := w) (m := m + w)
            (s := m - (e : ℕ) * w) (e := e') (hconj hu) hweight
        simpa [Y, e', pow_succ', mul_assoc] using hmem
      · have heq : (e : ℕ) + 1 = p := by
          omega
        let e0 : Fin p := ⟨0, (Fact.out : Nat.Prime p).pos⟩
        have hconjpow :
            conjGA p G x u * Y ^ p ∈ W.J ((m - (e : ℕ) * w) + p * w) := by
          exact W.mul_mem (hconj hu) (by simpa [Y] using hpow)
        have hweight :
            m + w ≤ ((m - (e : ℕ) * w) + p * w) + (e0 : ℕ) * w := by
          simpa [e0, heq] using
            nat_sub_succ m (e : ℕ) w
        have hmem :
            (conjGA p G x u * Y ^ p) * Y ^ (e0 : ℕ) ∈
              cyclicExtendJ W.J x w (m + w) :=
          extend_j
            (p := p) (G := G) (J := W.J) W.anti
            (x := x) (w := w) (m := m + w)
            (s := (m - (e : ℕ) * w) + p * w) (e := e0) hconjpow hweight
        have hpowe : Y * Y ^ (e : ℕ) = Y ^ p := by
          rw [← pow_succ', heq]
        simpa [Y, e0, hpowe, mul_assoc] using hmem
    have herrorTerm :
        (conjGA p G x u - u) * Y ^ (e : ℕ) ∈
          cyclicExtendJ W.J x w (m + w) := by
      have hweight :
          m + w ≤ ((m - (e : ℕ) * w) + w) + (e : ℕ) * w := by
        simpa using nat_sub_weight m (e : ℕ) w
      exact
        extend_j
          (p := p) (G := G) (J := W.J) W.anti
          (x := x) (w := w) (m := m + w)
          (s := (m - (e : ℕ) * w) + w) (e := e)
          (herror hu) hweight
    have hsum :
        (conjGA p G x u * Y) * Y ^ (e : ℕ) +
            (conjGA p G x u - u) * Y ^ (e : ℕ) ∈
          cyclicExtendJ W.J x w (m + w) :=
      (cyclicExtendJ W.J x w (m + w)).add_mem hmain herrorTerm
    have hgoal_eq :
        groupAlgebraSub p G x * (rightMulLinear (Y ^ (e : ℕ)) u) =
          (conjGA p G x u * Y) * Y ^ (e : ℕ) +
            (conjGA p G x u - u) * Y ^ (e : ℕ) := by
      calc
        groupAlgebraSub p G x * (rightMulLinear (Y ^ (e : ℕ)) u)
            = Y * (u * Y ^ (e : ℕ)) := by
              simp [rightMulLinear, Y]
        _ = (Y * u) * Y ^ (e : ℕ) := by
              rw [← mul_assoc]
        _ = (conjGA p G x u * Y + (conjGA p G x u - u)) * Y ^ (e : ℕ) := by
              rw [hmove]
        _ = (conjGA p G x u * Y) * Y ^ (e : ℕ) +
              (conjGA p G x u - u) * Y ^ (e : ℕ) := by
              rw [add_mul]
    exact hgoal_eq.symm ▸ hsum
  · simp
  · intro a b ha' hb'
    simpa [mul_add] using
      (cyclicExtendJ W.J x w (m + w)).add_mem ha' hb'

/-- Repeated left multiplication by the new letter raises weight by the expected multiple. -/
lemma extend_j_y
    {p : ℕ} [Fact p.Prime]
    {G : Type u} [Group G]
    (W : WFilt p G)
    {x : G} {w m k : ℕ}
    (hpow :
      (groupAlgebraSub p G x) ^ p ∈ W.J (p * w))
    (hconj :
      ∀ {r : ℕ} {a : denseGroupAlgebra p G},
        a ∈ W.J r →
          conjGA p G x a ∈ W.J r)
    (herror :
      ∀ {r : ℕ} {a : denseGroupAlgebra p G},
        a ∈ W.J r →
          conjGA p G x a - a ∈ W.J (r + w))
    {a : denseGroupAlgebra p G}
    (ha : a ∈ cyclicExtendJ W.J x w m) :
    (groupAlgebraSub p G x) ^ k * a ∈
      cyclicExtendJ W.J x w (m + k * w) := by
  let Y : denseGroupAlgebra p G := groupAlgebraSub p G x
  induction k with
  | zero =>
      simpa [Y] using ha
  | succ k ih =>
      have hstep :
          groupAlgebraSub p G x * (Y ^ k * a) ∈
            cyclicExtendJ W.J x w ((m + k * w) + w) :=
        cyclic_extend_y
          (p := p) (G := G) W
          (x := x) (w := w) (m := m + k * w)
          hpow hconj herror ih
      simpa [Y, pow_succ', mul_assoc, Nat.succ_mul, add_assoc] using hstep

/-- Left multiplication by an old weighted element raises the target weight additively. -/
lemma extend_j_old
    {p : ℕ} [Fact p.Prime]
    {G : Type u} [Group G]
    (W : WFilt p G)
    {x : G} {w r m : ℕ}
    {b a : denseGroupAlgebra p G}
    (hb : b ∈ W.J r)
    (ha : a ∈ cyclicExtendJ W.J x w m) :
    b * a ∈ cyclicExtendJ W.J x w (r + m) := by
  let Y : denseGroupAlgebra p G := groupAlgebraSub p G x
  dsimp [cyclicExtendJ] at ha
  refine
    Submodule.iSup_induction
      (fun e : Fin p =>
        (W.J (m - (e : ℕ) * w)).map
          (rightMulLinear (Y ^ (e : ℕ))))
      (motive := fun a =>
        b * a ∈ cyclicExtendJ W.J x w (r + m))
      ha
      ?mem
      ?zero
      ?add
  · intro e z hz
    rcases (Submodule.mem_map.mp hz) with ⟨u, hu, rfl⟩
    have hbu : b * u ∈ W.J (r + (m - (e : ℕ) * w)) :=
      W.mul_mem hb hu
    have hweight :
        r + m ≤ (r + (m - (e : ℕ) * w)) + (e : ℕ) * w := by
      exact nat_sub_mul r m (e : ℕ) w
    have hmem :
        (b * u) * Y ^ (e : ℕ) ∈ cyclicExtendJ W.J x w (r + m) :=
      extend_j
        (p := p) (G := G) (J := W.J) W.anti
        (x := x) (w := w) (m := r + m)
        (s := r + (m - (e : ℕ) * w)) (e := e) hbu hweight
    simpa [rightMulLinear, Y, mul_assoc] using hmem
  · simp
  · intro a c ha' hc'
    simpa [mul_add] using
      (cyclicExtendJ W.J x w (r + m)).add_mem ha' hc'

/-- The cyclic extension is multiplicative when the new letter is compatible with the old
filtration. -/
lemma extend_j_mul
    {p : ℕ} [Fact p.Prime]
    {G : Type u} [Group G]
    (W : WFilt p G)
    {x : G} {w r s : ℕ}
    (hpow :
      (groupAlgebraSub p G x) ^ p ∈ W.J (p * w))
    (hconj :
      ∀ {r : ℕ} {a : denseGroupAlgebra p G},
        a ∈ W.J r →
          conjGA p G x a ∈ W.J r)
    (herror :
      ∀ {r : ℕ} {a : denseGroupAlgebra p G},
        a ∈ W.J r →
          conjGA p G x a - a ∈ W.J (r + w))
    {a b : denseGroupAlgebra p G}
    (ha : a ∈ cyclicExtendJ W.J x w r)
    (hb : b ∈ cyclicExtendJ W.J x w s) :
    a * b ∈ cyclicExtendJ W.J x w (r + s) := by
  let Y : denseGroupAlgebra p G := groupAlgebraSub p G x
  dsimp [cyclicExtendJ] at ha
  refine
    Submodule.iSup_induction
      (fun e : Fin p =>
        (W.J (r - (e : ℕ) * w)).map
          (rightMulLinear (Y ^ (e : ℕ))))
      (motive := fun a =>
        a * b ∈ cyclicExtendJ W.J x w (r + s))
      ha
      ?mem
      ?zero
      ?add
  · intro e z hz
    rcases (Submodule.mem_map.mp hz) with ⟨u, hu, rfl⟩
    have hYb :
        Y ^ (e : ℕ) * b ∈
          cyclicExtendJ W.J x w (s + (e : ℕ) * w) := by
      simpa [Y, add_comm, add_left_comm, add_assoc] using
        extend_j_y
          (p := p) (G := G) W
          (x := x) (w := w) (m := s) (k := (e : ℕ))
          hpow hconj herror hb
    have huYb :
        u * (Y ^ (e : ℕ) * b) ∈
          cyclicExtendJ W.J x w ((r - (e : ℕ) * w) + (s + (e : ℕ) * w)) :=
      extend_j_old
        (p := p) (G := G) W
        (x := x) (w := w) (r := r - (e : ℕ) * w)
        (m := s + (e : ℕ) * w)
        hu hYb
    have hle :
        r + s ≤ (r - (e : ℕ) * w) + (s + (e : ℕ) * w) :=
      nat_add_sub r s (e : ℕ) w
    exact
      extend_j_antitone (p := p) (G := G) W.anti x w hle
        (by simpa [rightMulLinear, Y, mul_assoc] using huYb)
  · simp
  · intro a c ha' hc'
    simpa [add_mul] using
      (cyclicExtendJ W.J x w (r + s)).add_mem ha' hc'

/-- A compatible cyclic extension of a weight filtration is again a weight filtration. -/
def cyclic_extend_filtration
    {p : ℕ} [Fact p.Prime]
    {G : Type u} [Group G]
    (W : WFilt p G)
    (x : G) (w : ℕ)
    (hpow :
      (groupAlgebraSub p G x) ^ p ∈ W.J (p * w))
    (hconj :
      ∀ {r : ℕ} {a : denseGroupAlgebra p G},
        a ∈ W.J r →
          conjGA p G x a ∈ W.J r)
    (herror :
      ∀ {r : ℕ} {a : denseGroupAlgebra p G},
        a ∈ W.J r →
          conjGA p G x a - a ∈ W.J (r + w)) :
    WFilt p G where
  J := cyclicExtendJ W.J x w
  anti := extend_j_antitone (p := p) (G := G) W.anti x w
  one_mem := by
    let Y : denseGroupAlgebra p G := groupAlgebraSub p G x
    let e0 : Fin p := ⟨0, (Fact.out : Nat.Prime p).pos⟩
    have hmap :
        (1 : denseGroupAlgebra p G) ∈
          (W.J (0 - (e0 : ℕ) * w)).map
            (rightMulLinear (Y ^ (e0 : ℕ))) := by
      refine ⟨1, ?_, ?_⟩
      · simpa [e0] using W.one_mem
      · simp [rightMulLinear, e0, Y]
    exact Submodule.mem_iSup_of_mem e0 hmap
  mul_mem := by
    intro r s a b ha hb
    exact
      extend_j_mul
        (p := p) (G := G) W
        (x := x) (w := w) (r := r) (s := s)
        hpow hconj herror ha hb

/-- The leading weight filtration before any cyclic letters are adjoined: scalars in weight `0`
and zero in positive weight. -/
def baseJ
    (p : ℕ) [Fact p.Prime]
    (G : Type u) [Group G]
    (m : ℕ) :
    Submodule (ZMod p) (denseGroupAlgebra p G) :=
  if m = 0 then
    (ZMod p) ∙ (1 : denseGroupAlgebra p G)
  else
    ⊥

lemma baseJ_antitone
    {p : ℕ} [Fact p.Prime]
    {G : Type u} [Group G] :
    Antitone (baseJ p G) := by
  intro m n hmn
  by_cases hm : m = 0
  · by_cases hn : n = 0
    · simp [baseJ, hm, hn]
    · simp [baseJ, hm, hn]
  · have hn : n ≠ 0 := by omega
    simp [baseJ, hm, hn]

lemma scalar_span_mul
    {p : ℕ} [Fact p.Prime]
    {G : Type u} [Group G]
    {a b : denseGroupAlgebra p G}
    (ha : a ∈ (ZMod p) ∙ (1 : denseGroupAlgebra p G))
    (hb : b ∈ (ZMod p) ∙ (1 : denseGroupAlgebra p G)) :
    a * b ∈ (ZMod p) ∙ (1 : denseGroupAlgebra p G) := by
  rcases Submodule.mem_span_singleton.mp ha with ⟨ca, hca⟩
  rcases Submodule.mem_span_singleton.mp hb with ⟨cb, hcb⟩
  refine Submodule.mem_span_singleton.mpr ⟨ca * cb, ?_⟩
  rw [← hca, ← hcb]
  simp [smul_smul, mul_comm]

lemma base_j_mul
    {p : ℕ} [Fact p.Prime]
    {G : Type u} [Group G]
    {r s : ℕ}
    {a b : denseGroupAlgebra p G}
    (ha : a ∈ baseJ p G r)
    (hb : b ∈ baseJ p G s) :
    a * b ∈ baseJ p G (r + s) := by
  by_cases hr : r = 0
  · by_cases hs : s = 0
    · have ha_scalar :
          a ∈ (ZMod p) ∙ (1 : denseGroupAlgebra p G) := by
        simpa [baseJ, hr] using ha
      have hb_scalar :
          b ∈ (ZMod p) ∙ (1 : denseGroupAlgebra p G) := by
        simpa [baseJ, hs] using hb
      simpa [baseJ, hr, hs] using
        scalar_span_mul (p := p) (G := G) ha_scalar hb_scalar
    · have hb_zero : b = 0 := by
        have hb_bot : b ∈ (⊥ : Submodule (ZMod p) (denseGroupAlgebra p G)) := by
          simpa [baseJ, hs] using hb
        simpa using hb_bot
      subst b
      simp [baseJ]
  · have ha_zero : a = 0 := by
      have ha_bot : a ∈ (⊥ : Submodule (ZMod p) (denseGroupAlgebra p G)) := by
        simpa [baseJ, hr] using ha
      simpa using ha_bot
    subst a
    simp [baseJ]

/-- The base scalar filtration as a `WFilt`. -/
def base_weightFiltration
    (p : ℕ) [Fact p.Prime]
    (G : Type u) [Group G] :
    WFilt p G where
  J := baseJ p G
  anti := baseJ_antitone (p := p) (G := G)
  one_mem := by
    exact Submodule.mem_span_singleton_self (1 : denseGroupAlgebra p G)
  mul_mem := by
    intro r s a b ha hb
    exact base_j_mul (p := p) (G := G) ha hb

/-- Conjugation fixes every element of the scalar base filtration pointwise. -/
lemma ga_self_j
    {p : ℕ} [Fact p.Prime]
    {G : Type u} [Group G]
    (x : G)
    {r : ℕ}
    {a : denseGroupAlgebra p G}
    (ha : a ∈ baseJ p G r) :
    conjGA p G x a = a := by
  by_cases hr : r = 0
  · have ha_scalar :
        a ∈ (ZMod p) ∙ (1 : denseGroupAlgebra p G) := by
      simpa [baseJ, hr] using ha
    rcases Submodule.mem_span_singleton.mp ha_scalar with ⟨c, rfl⟩
    simp [conjGA]
  · have ha_zero : a = 0 := by
      have ha_bot :
          a ∈ (⊥ : Submodule (ZMod p) (denseGroupAlgebra p G)) := by
        simpa [baseJ, hr] using ha
      simpa using ha_bot
    subst a
    simp [conjGA]

/-- If `x` commutes with the adjoined letter `y`, then conjugation by `x` fixes the first cyclic
extension of the scalar filtration pointwise. -/
lemma ga_j_commute
    {p : ℕ} [Fact p.Prime]
    {G : Type u} [Group G]
    {x y : G}
    {w r : ℕ}
    (hxy : Commute x y)
    {a : denseGroupAlgebra p G}
    (ha : a ∈ cyclicExtendJ (baseJ p G) y w r) :
    conjGA p G x a = a := by
  dsimp [cyclicExtendJ] at ha
  refine
    Submodule.iSup_induction
      (fun e : Fin p =>
        (baseJ p G (r - (e : ℕ) * w)).map
          (rightMulLinear ((groupAlgebraSub p G y) ^ (e : ℕ))))
      (motive := fun a => conjGA p G x a = a)
      ha
      ?mem
      ?zero
      ?add
  · intro e z hz
    rcases Submodule.mem_map.mp hz with ⟨u, hu, rfl⟩
    change
      conjGA p G x (u * groupAlgebraSub p G y ^ (e : ℕ)) =
        u * groupAlgebraSub p G y ^ (e : ℕ)
    rw [conjGA_mul, ga_self_j x hu, conjGA_pow,
      ga_self_commute hxy]
  · simp [conjGA]
  · intro a b ha' hb'
    rw [conjGA_add, ha', hb']

/-- The data needed to adjoin one weighted cyclic letter to an already-built prefix
filtration. -/
structure CEDataa
    (p : ℕ) [Fact p.Prime]
    (G : Type u) [Group G]
    (W : WFilt p G) where
  x : G
  w : ℕ
  pow_mem :
    (groupAlgebraSub p G x) ^ p ∈ W.J (p * w)
  conj_mem :
    ∀ {r : ℕ} {a : denseGroupAlgebra p G},
      a ∈ W.J r →
        conjGA p G x a ∈ W.J r
  error_mem :
    ∀ {r : ℕ} {a : denseGroupAlgebra p G},
      a ∈ W.J r →
        conjGA p G x a - a ∈ W.J (r + w)

/-- A deeper conjugation error implies preservation of the original weight cutoff. -/
lemma conj_ga_error
    {p : ℕ} [Fact p.Prime]
    {G : Type u} [Group G]
    (W : WFilt p G)
    {x : G}
    {w r : ℕ}
    {a : denseGroupAlgebra p G}
    (ha : a ∈ W.J r)
    (herror : conjGA p G x a - a ∈ W.J (r + w)) :
    conjGA p G x a ∈ W.J r := by
  have herror' : conjGA p G x a - a ∈ W.J r :=
    W.anti (Nat.le_add_right r w) herror
  have hadd : (conjGA p G x a - a) + a ∈ W.J r :=
    (W.J r).add_mem herror' ha
  simpa using hadd

/-- Construct one cyclic-extension certificate from the overflow estimate and the genuinely
group-theoretic conjugation-error estimate.

The separate conjugation-preservation field is a formal consequence: the deeper error lies in the
old cutoff by antitonicity. -/
def cyclic_extension_error
    {p : ℕ} [Fact p.Prime]
    {G : Type u} [Group G]
    (W : WFilt p G)
    (x : G)
    (w : ℕ)
    (hpow :
      (groupAlgebraSub p G x) ^ p ∈ W.J (p * w))
    (herror :
      ∀ {r : ℕ} {a : denseGroupAlgebra p G},
        a ∈ W.J r →
          conjGA p G x a - a ∈ W.J (r + w)) :
    CEDataa p G W where
  x := x
  w := w
  pow_mem := hpow
  conj_mem := by
    intro r a ha
    exact conj_ga_error W ha (herror ha)
  error_mem := herror

/-- In characteristic `p`, an augmentation letter attached to an element of exponent dividing
`p` has zero `p`th power. -/
lemma algebra_sub_zero
    {p : ℕ} [Fact p.Prime]
    {G : Type u} [Group G]
    {x : G}
    (hx : x ^ p = 1) :
    groupAlgebraSub p G x ^ p = 0 := by
  have hpow :
      groupAlgebraSub p G x ^ p =
        groupAlgebraSub p G (x ^ p) := by
    change
      (denseGeneratorsElement p G x - 1) ^ p =
        denseGeneratorsElement p G (x ^ p) - 1
    simpa [pow_one] using
      (dense_generators_element
        (p := p) (Λ := G) (j := 1) (x := x)).symm
  rw [hpow, hx]
  simp [groupAlgebraSub]

/-- The first cyclic-extension certificate: a letter of exponent dividing `p` can be adjoined to
the scalar base filtration.

This is the anchor for the descending-weight Jennings collection. The characteristic-`p`
identity turns `x ^ p = 1` into `([x] - 1) ^ p = 0`; the conjugation fields hold because the
previous filtration contains only scalars. -/
def base_cyclic_extension
    {p : ℕ} [Fact p.Prime]
    {G : Type u} [Group G]
    (x : G)
    (w : ℕ)
    (hx : x ^ p = 1) :
    CEDataa p G (base_weightFiltration p G) where
  x := x
  w := w
  pow_mem := by
    have hzero :=
      algebra_sub_zero
        (p := p) (G := G) hx
    rw [hzero]
    exact Submodule.zero_mem _
  conj_mem := by
    intro r a ha
    change a ∈ baseJ p G r at ha
    change conjGA p G x a ∈ baseJ p G r
    rw [ga_self_j x ha]
    exact ha
  error_mem := by
    intro r a ha
    change a ∈ baseJ p G r at ha
    change conjGA p G x a - a ∈ baseJ p G (r + w)
    rw [ga_self_j x ha]
    simp

/-- The next prefix filtration obtained by adjoining one certified cyclic letter. -/
def CEDataa.next
    {p : ℕ} [Fact p.Prime]
    {G : Type u} [Group G]
    {W : WFilt p G}
    (S : CEDataa p G W) :
    WFilt p G :=
  cyclic_extend_filtration
    (p := p) (G := G) W S.x S.w
    S.pow_mem S.conj_mem S.error_mem

/-- After adjoining one scalar-base letter, a commuting second letter of exponent dividing `p`
can be adjoined as another cyclic extension. -/
def cyclic_next_commute
    {p : ℕ} [Fact p.Prime]
    {G : Type u} [Group G]
    (x y : G)
    (wx wy : ℕ)
    (hx : x ^ p = 1)
    (hy : y ^ p = 1)
    (hxy : Commute x y) :
    CEDataa p G
      (base_cyclic_extension y wy hy).next := by
  apply
    cyclic_extension_error
      (base_cyclic_extension y wy hy).next x wx
  · have hzero :
        groupAlgebraSub p G x ^ p = 0 :=
      algebra_sub_zero hx
    rw [hzero]
    exact Submodule.zero_mem _
  · intro r a ha
    change a ∈ cyclicExtendJ (baseJ p G) y wy r at ha
    change
      conjGA p G x a - a ∈
        cyclicExtendJ (baseJ p G) y wy (r + wx)
    rw [ga_j_commute hxy ha]
    simp

/-- Prefix filtrations obtained from the scalar base by repeatedly adjoining certified weighted
cyclic letters. -/
inductive PWFilt
    (p : ℕ) [Fact p.Prime]
    (G : Type u) [Group G] :
    WFilt p G → Type u where
  | base :
      PWFilt p G (base_weightFiltration p G)
  | extend {W : WFilt p G}
      (hW : PWFilt p G W)
      (S : CEDataa p G W) :
      PWFilt p G S.next

/-- The underlying submodule family of a certified prefix filtration. -/
abbrev prefixJ
    {p : ℕ} [Fact p.Prime]
    {G : Type u} [Group G]
    {W : WFilt p G}
    (_hW : PWFilt p G W) :
    ℕ → Submodule (ZMod p) (denseGroupAlgebra p G) :=
  W.J

lemma prefixJ_antitone
    {p : ℕ} [Fact p.Prime]
    {G : Type u} [Group G]
    {W : WFilt p G}
    (hW : PWFilt p G W) :
    Antitone (prefixJ hW) :=
  W.anti

/-- Every certified prefix filtration is multiplicative. -/
lemma prefix_j_mul
    {p : ℕ} [Fact p.Prime]
    {G : Type u} [Group G]
    {W : WFilt p G}
    (hW : PWFilt p G W)
    {r s : ℕ}
    {a b : denseGroupAlgebra p G}
    (ha : a ∈ prefixJ hW r)
    (hb : b ∈ prefixJ hW s) :
    a * b ∈ prefixJ hW (r + s) :=
  W.mul_mem ha hb

/-- The `n`th finite augmentation-ideal power as a `ZMod p`-submodule.

The ideal power itself is an ideal of `ZMod p[G]`; for linear separation we view the same carrier
as a vector subspace over the coefficient field. -/
abbrev augmentationIdealPower
    (p : ℕ) [Fact p.Prime]
    (G : Type u) [Group G]
    (n : ℕ) :
    Submodule (ZMod p) (denseGroupAlgebra p G) :=
  ((denseGeneratorsIdeal p G) ^ n).restrictScalars (ZMod p)

/-- Ordered product of augmented group elements. -/
noncomputable def augmentationWord
    (p : ℕ) [Fact p.Prime]
    (G : Type u) [Group G] :
    List G → denseGroupAlgebra p G :=
  fun w => (w.map fun g => groupAlgebraSub p G g).prod

/-- A word of augmented length `n` lies in the `n`th finite augmentation power. -/
lemma augmentation_ideal_power
    {p : ℕ} [Fact p.Prime]
    {G : Type u} [Group G]
    (w : List G) :
    augmentationWord p G w ∈ augmentationIdealPower p G w.length := by
  have hmem :
      (w.map fun g =>
          denseGeneratorsElement p G g - 1).prod ∈
        denseGeneratorsIdeal p G ^ w.length :=
    dense_generators_factors
      (p := p) (Λ := G) w
  simpa [augmentationWord, groupAlgebraSub, augmentationIdealPower] using
    (Submodule.restrictScalars_mem (ZMod p)
      (denseGeneratorsIdeal p G ^ w.length)
      ((w.map fun g =>
          denseGeneratorsElement p G g - 1).prod)).mpr hmem

/-- A product of augmentation letters lies in a multiplicative weight filtration at the sum of
the individual letter weights. -/
lemma aug_prod_filtration
    {p : ℕ} [Fact p.Prime]
    {G : Type u} [Group G]
    (W : WFilt p G)
    (weight : G → ℕ)
    (hletter :
      ∀ x : G, groupAlgebraSub p G x ∈ W.J (weight x))
    (xs : List G) :
    augmentationWord p G xs ∈ W.J ((xs.map weight).sum) := by
  induction xs with
  | nil =>
      simpa [augmentationWord] using W.one_mem
  | cons x xs ih =>
      have hx : groupAlgebraSub p G x ∈ W.J (weight x) :=
        hletter x
      have htail : augmentationWord p G xs ∈ W.J ((xs.map weight).sum) :=
        ih
      have hmul :
          groupAlgebraSub p G x * augmentationWord p G xs ∈
            W.J (weight x + (xs.map weight).sum) :=
        W.mul_mem hx htail
      simpa [augmentationWord] using hmul

/-- Fixed-length augmentation-word spans lie in any weight filtration containing every basic
augmentation letter in weight `1`. -/
lemma dense_generators_filtration
    {p : ℕ} [Fact p.Prime]
    {G : Type u} [Group G]
    (W : WFilt p G)
    (hletter :
      ∀ x : G, groupAlgebraSub p G x ∈ W.J 1)
    (n : ℕ) :
    (denseGeneratorsSpan p G n :
      Set (denseGroupAlgebra p G)) ⊆
      (W.J n : Set (denseGroupAlgebra p G)) := by
  let T : Set (denseGroupAlgebra p G) :=
    { y | ∃ w : List.Vector G n,
        denseGeneratorsGenerator p G w = y }
  intro y hy
  have hyspan : y ∈ Submodule.span (ZMod p) T := by
    simpa [denseGeneratorsSpan, T] using hy
  refine Submodule.span_induction
    (s := T)
    (p := fun z _ => z ∈ W.J n)
    ?mem ?zero ?add ?smul hyspan
  · rintro z ⟨w, rfl⟩
    have hprod :
        augmentationWord p G w.toList ∈
          W.J ((w.toList.map fun _ : G => 1).sum) :=
      aug_prod_filtration
        (p := p) (G := G) W (fun _ : G => 1) hletter w.toList
    have hsum : (w.toList.map fun _ : G => 1).sum = n := by
      simp
    simpa [
      denseGeneratorsGenerator,
      augmentationWord,
      groupAlgebraSub,
      hsum
    ] using hprod
  · exact (W.J n).zero_mem
  · intro x y _hx _hy hx_mem hy_mem
    exact (W.J n).add_mem hx_mem hy_mem
  · intro c x _hx hx_mem
    exact (W.J n).smul_mem c hx_mem

/-- Positive augmentation powers are contained in any weight filtration containing all basic
augmentation letters in weight `1`. -/
lemma augmentation_ideal_filtration
    {p : ℕ} [Fact p.Prime]
    {G : Type u} [Group G]
    (W : WFilt p G)
    (hletter :
      ∀ x : G, groupAlgebraSub p G x ∈ W.J 1)
    (n : ℕ) :
    augmentationIdealPower p G (n + 1) ≤ W.J (n + 1) := by
  intro y hy
  have hyI :
      y ∈ denseGeneratorsIdeal p G ^ (n + 1) := by
    exact
      (Submodule.restrictScalars_mem (ZMod p)
        (denseGeneratorsIdeal p G ^ (n + 1)) y).mp
        (by simpa [augmentationIdealPower] using hy)
  have hyWord :
      y ∈ denseGeneratorsSpan p G (n + 1) :=
    dense_succ_span
      (p := p) (Λ := G) n hyI
  exact
    dense_generators_filtration
      (p := p) (G := G) W hletter (n + 1) hyWord

/-- A functional killing `I^(m+1)` kills every ordered augmentation word of length `m+1`. -/
lemma linear_kills_words
    {p : ℕ} [Fact p.Prime]
    {G : Type u} [Group G]
    {m : ℕ}
    (φ : denseGroupAlgebra p G →ₗ[ZMod p] ZMod p)
    (hφ :
      ∀ a,
        a ∈ augmentationIdealPower p G (m + 1) →
          φ a = 0)
    (w : List G)
    (hw : w.length = m + 1) :
    φ (augmentationWord p G w) = 0 := by
  apply hφ
  simpa [hw] using
    augmentation_ideal_power (p := p) (G := G) w

/-- A functional killing `I^(m+1)` kills the local fixed-length word-span model for `I^(m+1)`. -/
lemma linear_kills_span
    {p : ℕ} [Fact p.Prime]
    {G : Type u} [Group G]
    {m : ℕ}
    (φ : denseGroupAlgebra p G →ₗ[ZMod p] ZMod p)
    (hφ :
      ∀ a,
        a ∈ augmentationIdealPower p G (m + 1) →
          φ a = 0)
    {z : denseGroupAlgebra p G}
    (hz :
      z ∈ denseGeneratorsSpan p G (m + 1)) :
    φ z = 0 := by
  apply hφ
  have hzI :
      z ∈ denseGeneratorsIdeal p G ^ (m + 1) :=
    dense_span_pow
      (p := p) (Λ := G) (m + 1) hz
  change z ∈ augmentationIdealPower p G (m + 1)
  exact
    (Submodule.restrictScalars_mem (ZMod p)
      (denseGeneratorsIdeal p G ^ (m + 1)) z).mpr hzI

end Submission
