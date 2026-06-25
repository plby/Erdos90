import Submission.Group.Filtration
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.Algebra.Module.ZMod
import Mathlib.Algebra.Module.Equiv.Defs
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.LinearAlgebra.Dimension.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Algebra.Field.ZMod
import Mathlib.LinearAlgebra.Dimension.Finrank

open scoped commutatorElement

/-!
# Restricted N-series interface

A small structure for descending normal filtrations equipped with the two laws used
for mod-`p` Zassenhaus filtrations: positive-index commutators add depths, and
`p`th powers multiply depth by `p`.
-/

namespace Submission

/-- A descending filtration satisfying the restricted N-series laws at the prime/characteristic
parameter `p`.  We keep the positivity hypotheses explicit for the commutator law because the
project's filtrations also expose index `0`. -/
structure RNSeries (p : ℕ) (G : Type*) [Group G] extends DFilt G where
  commutator_le' : ∀ {m n : ℕ}, m ≠ 0 → n ≠ 0 → ⁅term m, term n⁆ ≤ term (m + n)
  pow_mem' : ∀ {n : ℕ} {g : G}, g ∈ term n → g ^ p ∈ term (n * p)

namespace RNSeries

variable {p : ℕ} {G : Type*} [Group G]

instance : CoeFun (RNSeries p G) (fun _ => ℕ → Subgroup G) :=
  ⟨fun F => F.term⟩

/-- Forget a restricted series to its underlying descending filtration. -/
def toDescending (F : RNSeries p G) : DFilt G := F.toDFilt

@[simp] theorem toDescending_term (F : RNSeries p G) (n : ℕ) :
    F.toDescending n = F n := rfl

@[simp] theorem one_eq_top (F : RNSeries p G) : F 1 = ⊤ := F.one_eq_top'

/-- The zeroth term of a restricted series is top. -/
@[simp] theorem zero_eq_top (F : RNSeries p G) : F 0 = ⊤ := by
  change F.toDescending 0 = ⊤
  exact DFilt.zero_eq_top F.toDescending

/-- Any term of index at most one is top. -/
theorem eq_top_of (F : RNSeries p G) {n : ℕ} (hn : n ≤ 1) :
    F n = ⊤ := by
  change F.toDescending n = ⊤
  exact DFilt.eq_top_of F.toDescending hn

theorem antitone (F : RNSeries p G) : Antitone F.term := F.antitone'

/-- Later terms are contained in earlier terms. -/
theorem mono_membership (F : RNSeries p G) {m n : ℕ} (h : m ≤ n) :
    F n ≤ F m := by
  change F.toDescending n ≤ F.toDescending m
  exact DFilt.mono_membership F.toDescending h

/-- Elementwise form of monotonicity for restricted-series terms. -/
theorem mem_of_le (F : RNSeries p G) {m n : ℕ} (h : m ≤ n) {g : G}
    (hg : g ∈ F n) : g ∈ F m :=
  F.mono_membership h hg

/-- Membership in a term can always be weakened to the zeroth term. -/
theorem mem_zero_mem (F : RNSeries p G) {n : ℕ} {g : G} (hg : g ∈ F n) :
    g ∈ F 0 :=
  F.mem_of_le (Nat.zero_le n) hg

/-- Every element lies in the zeroth restricted-series term. -/
theorem mem_zero (F : RNSeries p G) (g : G) : g ∈ F 0 := by
  rw [zero_eq_top]
  trivial

/-- Every element lies in the first restricted-series term. -/
theorem mem_one (F : RNSeries p G) (g : G) : g ∈ F 1 := by
  rw [one_eq_top]
  trivial

/-- The identity lies in every restricted-series term. -/
theorem one_mem (F : RNSeries p G) (n : ℕ) : (1 : G) ∈ F n :=
  (F n).one_mem

/-- Products preserve membership in a common restricted-series term. -/
theorem mul_mem (F : RNSeries p G) {n : ℕ} {g h : G}
    (hg : g ∈ F n) (hh : h ∈ F n) : g * h ∈ F n :=
  (F n).mul_mem hg hh

/-- Inverses preserve membership in a restricted-series term. -/
theorem inv_mem (F : RNSeries p G) {n : ℕ} {g : G} (hg : g ∈ F n) :
    g⁻¹ ∈ F n :=
  (F n).inv_mem hg

/-- Conjugation preserves membership in a restricted-series term. -/
theorem conj_mem (F : RNSeries p G) {n : ℕ} {g x : G} (hg : g ∈ F n) :
    x * g * x⁻¹ ∈ F n :=
  (F.normal' n).conj_mem g hg x

/-- Division preserves membership in a common restricted-series term. -/
theorem div_mem (F : RNSeries p G) {n : ℕ} {g h : G}
    (hg : g ∈ F n) (hh : h ∈ F n) : g / h ∈ F n := by
  simpa [div_eq_mul_inv] using F.mul_mem hg (F.inv_mem hh)

/-- The inverse-conjugation convention also preserves term membership. -/
theorem conj_inv_mem (F : RNSeries p G) {n : ℕ} {g x : G} (hg : g ∈ F n) :
    x⁻¹ * g * x ∈ F n := by
  simpa using F.conj_mem (x := x⁻¹) hg

/-- Intersections of restricted-series terms are the term at the larger index. -/
theorem term_inf_max (F : RNSeries p G) (m n : ℕ) :
    F m ⊓ F n = F (max m n) := by
  change F.toDescending m ⊓ F.toDescending n = F.toDescending (max m n)
  exact DFilt.term_inf_max F.toDescending m n

/-- Joins of restricted-series terms are the term at the smaller index. -/
theorem term_sup_min (F : RNSeries p G) (m n : ℕ) :
    F m ⊔ F n = F (min m n) := by
  change F.toDescending m ⊔ F.toDescending n = F.toDescending (min m n)
  exact DFilt.term_sup_min F.toDescending m n

instance term_normal (F : RNSeries p G) (n : ℕ) : (F n).Normal := F.normal' n

/-- Comparable-intersection orientation for restricted-series terms. -/
theorem term_inf_right (F : RNSeries p G) {m n : ℕ} (h : m ≤ n) :
    F m ⊓ F n = F n := by
  change F.toDescending m ⊓ F.toDescending n = F.toDescending n
  exact DFilt.term_inf_right F.toDescending h

/-- Symmetric comparable-intersection orientation for restricted-series terms. -/
theorem term_inf_left (F : RNSeries p G) {m n : ℕ} (h : n ≤ m) :
    F m ⊓ F n = F m := by
  change F.toDescending m ⊓ F.toDescending n = F.toDescending m
  exact DFilt.term_inf_left F.toDescending h

/-- Comparable-join orientation for restricted-series terms. -/
theorem term_sup_left (F : RNSeries p G) {m n : ℕ} (h : m ≤ n) :
    F m ⊔ F n = F m := by
  change F.toDescending m ⊔ F.toDescending n = F.toDescending m
  exact DFilt.term_sup_left F.toDescending h

/-- Symmetric comparable-join orientation for restricted-series terms. -/
theorem term_sup_right (F : RNSeries p G) {m n : ℕ} (h : n ≤ m) :
    F m ⊔ F n = F n := by
  change F.toDescending m ⊔ F.toDescending n = F.toDescending n
  exact DFilt.term_sup_right F.toDescending h

/-- Elementwise commutator law. -/
theorem commutator_mem {F : RNSeries p G} {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0)
    {g h : G} (hg : g ∈ F m) (hh : h ∈ F n) : ⁅g, h⁆ ∈ F (m + n) := by
  exact (Subgroup.commutator_le.mp (F.commutator_le' hm hn)) g hg h hh

/-- Subgroup commutator law. -/
theorem commutator_le (F : RNSeries p G) {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) :
    ⁅F m, F n⁆ ≤ F (m + n) :=
  F.commutator_le' hm hn

/-- Elementwise `p`th-power law. -/
theorem pow_mem (F : RNSeries p G) {n : ℕ} {g : G} (hg : g ∈ F n) :
    g ^ p ∈ F (n * p) :=
  F.pow_mem' hg

/-- Predicate notation for an element having certified depth at least `n` in a series. -/
def HasDepth (F : RNSeries p G) (g : G) (n : ℕ) : Prop := g ∈ F n

@[simp] theorem hasDepth_iff (F : RNSeries p G) {g : G} {n : ℕ} :
    F.HasDepth g n ↔ g ∈ F n := Iff.rfl

/-- Every element has depth at least zero. -/
theorem hasDepth_zero (F : RNSeries p G) (g : G) : F.HasDepth g 0 := by
  change g ∈ F 0
  rw [zero_eq_top]
  trivial

/-- Every element has depth at least one, by normalization of restricted series. -/
theorem hasDepth_one (F : RNSeries p G) (g : G) : F.HasDepth g 1 := by
  change g ∈ F 1
  rw [one_eq_top]
  trivial

/-- Every element has depth at any index bounded by one. -/
theorem depth_one (F : RNSeries p G) {n : ℕ} (hn : n ≤ 1) (g : G) :
    F.HasDepth g n := by
  change g ∈ F n
  rw [eq_top_of F hn]
  trivial

/-- A depth certificate can be weakened to a smaller index. -/
theorem HasDepth.of_le {F : RNSeries p G} {g : G} {m n : ℕ}
    (hmn : m ≤ n) (hg : F.HasDepth g n) : F.HasDepth g m :=
  F.antitone hmn hg

/-- The identity element has every certified depth. -/
theorem depth_one_element (F : RNSeries p G) (n : ℕ) : F.HasDepth 1 n := by
  change (1 : G) ∈ F n
  exact (F n).one_mem

/-- Products of elements at the same depth stay at that depth. -/
theorem HasDepth.mul {F : RNSeries p G} {g h : G} {n : ℕ}
    (hg : F.HasDepth g n) (hh : F.HasDepth h n) : F.HasDepth (g * h) n :=
  (F n).mul_mem hg hh

/-- Inverses preserve depth. -/
theorem HasDepth.inv {F : RNSeries p G} {g : G} {n : ℕ}
    (hg : F.HasDepth g n) : F.HasDepth g⁻¹ n :=
  (F n).inv_mem hg

/-- Division preserves a common depth. -/
theorem HasDepth.div {F : RNSeries p G} {g h : G} {n : ℕ}
    (hg : F.HasDepth g n) (hh : F.HasDepth h n) : F.HasDepth (g / h) n := by
  simpa [div_eq_mul_inv] using hg.mul hh.inv

/-- If the denominator has at least as much depth, a quotient has the numerator depth. -/
theorem HasDepth.div_le_right {F : RNSeries p G} {g h : G} {m n : ℕ}
    (hmn : m ≤ n) (hg : F.HasDepth g m) (hh : F.HasDepth h n) :
    F.HasDepth (g / h) m := by
  simpa [div_eq_mul_inv] using hg.mul (hh.of_le hmn).inv

/-- If the numerator has at least as much depth, a quotient has the denominator depth. -/
theorem HasDepth.div_le_lefta {F : RNSeries p G} {g h : G} {m n : ℕ}
    (hmn : m ≤ n) (hg : F.HasDepth g n) (hh : F.HasDepth h m) :
    F.HasDepth (g / h) m := by
  simpa [div_eq_mul_inv] using (hg.of_le hmn).mul hh.inv

/-- Quotients of elements with possibly different depths have at least the minimum depth. -/
theorem HasDepth.div_min {F : RNSeries p G} {g h : G} {m n : ℕ}
    (hg : F.HasDepth g m) (hh : F.HasDepth h n) : F.HasDepth (g / h) (min m n) := by
  simpa [div_eq_mul_inv] using
    (hg.of_le (Nat.min_le_left _ _)).mul ((hh.of_le (Nat.min_le_right _ _)).inv)

/-- Left multiplication by an inverse preserves a common depth. -/
theorem HasDepth.inv_mul {F : RNSeries p G} {g h : G} {n : ℕ}
    (hg : F.HasDepth g n) (hh : F.HasDepth h n) : F.HasDepth (g⁻¹ * h) n :=
  hg.inv.mul hh

/-- Conjugation preserves depth, since every term is normal. -/
theorem HasDepth.conj {F : RNSeries p G} {g x : G} {n : ℕ}
    (hg : F.HasDepth g n) : F.HasDepth (x * g * x⁻¹) n := by
  exact (F.term_normal n).conj_mem g hg x

/-- The opposite conjugation convention also preserves depth. -/
theorem HasDepth.conj_inv {F : RNSeries p G} {g x : G} {n : ℕ}
    (hg : F.HasDepth g n) : F.HasDepth (x⁻¹ * g * x) n := by
  simpa using (hg.conj (x := x⁻¹))

/-- If the right factor has at least as much depth, a product has the left depth. -/
theorem HasDepth.mul_le_righta {F : RNSeries p G} {g h : G} {m n : ℕ}
    (hmn : m ≤ n) (hg : F.HasDepth g m) (hh : F.HasDepth h n) :
    F.HasDepth (g * h) m :=
  hg.mul (hh.of_le hmn)

/-- If the left factor has at least as much depth, a product has the right depth. -/
theorem HasDepth.mul_le_lefta {F : RNSeries p G} {g h : G} {m n : ℕ}
    (hmn : m ≤ n) (hg : F.HasDepth g n) (hh : F.HasDepth h m) :
    F.HasDepth (g * h) m :=
  (hg.of_le hmn).mul hh

/-- Products of elements with possibly different depths have at least the minimum depth. -/
theorem HasDepth.mul_min {F : RNSeries p G} {g h : G} {m n : ℕ}
    (hg : F.HasDepth g m) (hh : F.HasDepth h n) : F.HasDepth (g * h) (min m n) := by
  exact (hg.of_le (Nat.min_le_left _ _)).mul (hh.of_le (Nat.min_le_right _ _))

/-- Natural powers preserve a fixed depth. -/
theorem HasDepth.pow {F : RNSeries p G} {g : G} {n k : ℕ}
    (hg : F.HasDepth g n) : F.HasDepth (g ^ k) n := by
  induction k with
  | zero =>
      simp [HasDepth]
  | succ k ih =>
      simpa [pow_succ] using ih.mul hg

/-- Products of a list of elements all having a fixed depth still have that depth. -/
theorem HasDepth.list_prod {F : RNSeries p G} {n : ℕ} (L : List G)
    (h : ∀ g ∈ L, F.HasDepth g n) : F.HasDepth L.prod n := by
  induction L with
  | nil =>
      exact F.depth_one_element n
  | cons x xs ih =>
      have hx : F.HasDepth x n := h x (by simp)
      have hxs : ∀ g ∈ xs, F.HasDepth g n := by
        intro g hg
        exact h g (by simp [hg])
      simpa using hx.mul (ih hxs)

/-- Integer powers preserve a fixed depth. -/
theorem HasDepth.zpow {F : RNSeries p G} {g : G} {n : ℕ}
    (hg : F.HasDepth g n) (k : ℤ) : F.HasDepth (g ^ k) n := by
  change g ^ k ∈ F n
  exact Subgroup.zpow_mem (F n) hg k

/-- Commutators add positive depths. -/
theorem HasDepth.commutator {F : RNSeries p G} {m n : ℕ} (hm : m ≠ 0)
    (hn : n ≠ 0) {g h : G} (hg : F.HasDepth g m) (hh : F.HasDepth h n) :
    F.HasDepth ⁅g, h⁆ (m + n) :=
  commutator_mem hm hn hg hh

/-- Inverting the left commutator input preserves the same positive-depth bound. -/
theorem HasDepth.commutator_inv_left {F : RNSeries p G} {m n : ℕ}
    (hm : m ≠ 0) (hn : n ≠ 0) {g h : G}
    (hg : F.HasDepth g m) (hh : F.HasDepth h n) :
    F.HasDepth ⁅g⁻¹, h⁆ (m + n) :=
  hg.inv.commutator hm hn hh

/-- Inverting the right commutator input preserves the same positive-depth bound. -/
theorem HasDepth.commutator_inv_right {F : RNSeries p G} {m n : ℕ}
    (hm : m ≠ 0) (hn : n ≠ 0) {g h : G}
    (hg : F.HasDepth g m) (hh : F.HasDepth h n) :
    F.HasDepth ⁅g, h⁻¹⁆ (m + n) :=
  hg.commutator hm hn hh.inv

/-- Inverting both commutator inputs preserves the same positive-depth bound. -/
theorem HasDepth.commutator_inv_inv {F : RNSeries p G} {m n : ℕ}
    (hm : m ≠ 0) (hn : n ≠ 0) {g h : G}
    (hg : F.HasDepth g m) (hh : F.HasDepth h n) :
    F.HasDepth ⁅g⁻¹, h⁻¹⁆ (m + n) :=
  hg.inv.commutator hm hn hh.inv

/-- Swapping the two commutator inputs gives the same additive depth bound. -/
theorem HasDepth.commutator_swap {F : RNSeries p G} {m n : ℕ}
    (hm : m ≠ 0) (hn : n ≠ 0) {g h : G}
    (hg : F.HasDepth g m) (hh : F.HasDepth h n) :
    F.HasDepth ⁅h, g⁆ (m + n) := by
  simpa [Nat.add_comm] using hh.commutator hn hm hg

/-- The inverse of a commutator has the same additive depth bound. -/
theorem HasDepth.commutator_inv {F : RNSeries p G} {m n : ℕ}
    (hm : m ≠ 0) (hn : n ≠ 0) {g h : G}
    (hg : F.HasDepth g m) (hh : F.HasDepth h n) :
    F.HasDepth (⁅g, h⁆⁻¹) (m + n) :=
  (hg.commutator hm hn hh).inv

/-- A commutator of positive-depth elements may be weakened to any smaller target depth. -/
theorem HasDepth.commutator_of_le {F : RNSeries p G} {m n k : ℕ}
    (hm : m ≠ 0) (hn : n ≠ 0) (hk : k ≤ m + n) {g h : G}
    (hg : F.HasDepth g m) (hh : F.HasDepth h n) :
    F.HasDepth ⁅g, h⁆ k :=
  (hg.commutator hm hn hh).of_le hk

/-- Commuting a positive-depth element with an arbitrary element raises depth by one. -/
theorem HasDepth.commutator_right_any {F : RNSeries p G} {n : ℕ}
    (hn : n ≠ 0) {g : G} (hg : F.HasDepth g n) (h : G) :
    F.HasDepth ⁅g, h⁆ (n + 1) := by
  have hh : F.HasDepth h 1 := by
    change h ∈ F 1
    simp [F.one_eq_top]
  simpa using hg.commutator hn (by decide : (1 : ℕ) ≠ 0) hh

/-- Commuting an arbitrary element with a positive-depth element raises depth by one. -/
theorem HasDepth.commutator_left_any {F : RNSeries p G} {n : ℕ}
    (hn : n ≠ 0) (h : G) {g : G} (hg : F.HasDepth g n) :
    F.HasDepth ⁅h, g⁆ (1 + n) := by
  have hh : F.HasDepth h 1 := by
    change h ∈ F 1
    simp [F.one_eq_top]
  simpa using hh.commutator (by decide : (1 : ℕ) ≠ 0) hn hg


/-- The distinguished `p`th power multiplies depth by `p`. -/
theorem HasDepth.pow_p {F : RNSeries p G} {n : ℕ} {g : G}
    (hg : F.HasDepth g n) : F.HasDepth (g ^ p) (n * p) :=
  F.pow_mem hg

/-- Left-multiplication orientation for the distinguished `p`th-power depth bound. -/
theorem HasDepth.pow_p_left {F : RNSeries p G} {n : ℕ} {g : G}
    (hg : F.HasDepth g n) : F.HasDepth (g ^ p) (p * n) := by
  simpa [Nat.mul_comm] using hg.pow_p

/-- Applying the distinguished `p`th power to an inverse preserves the expected depth bound. -/
theorem HasDepth.inv_pow_p {F : RNSeries p G} {n : ℕ} {g : G}
    (hg : F.HasDepth g n) : F.HasDepth ((g⁻¹) ^ p) (n * p) :=
  hg.inv.pow_p

/-- Left-oriented form for the distinguished `p`th power of an inverse. -/
theorem HasDepth.inv_pow_pleft {F : RNSeries p G} {n : ℕ} {g : G}
    (hg : F.HasDepth g n) : F.HasDepth ((g⁻¹) ^ p) (p * n) :=
  hg.inv.pow_p_left

/-- Iterating the distinguished `p`th-power operation multiplies depth by `p^k`. -/
theorem HasDepth.pow_p_iterate {F : RNSeries p G} {n : ℕ} {g : G}
    (hg : F.HasDepth g n) (k : ℕ) :
    F.HasDepth (g ^ (p ^ k)) (n * (p ^ k)) := by
  induction k with
  | zero => simpa using hg
  | succ k ih =>
      have hpow := ih.pow_p
      simpa [pow_succ, Nat.mul_assoc, pow_mul] using hpow

/-- Left-multiplication orientation for iterated distinguished `p`th powers. -/
theorem HasDepth.pow_p_iterateleft {F : RNSeries p G} {n : ℕ} {g : G}
    (hg : F.HasDepth g n) (k : ℕ) :
    F.HasDepth (g ^ (p ^ k)) ((p ^ k) * n) := by
  simpa [Nat.mul_comm] using hg.pow_p_iterate k

/-- Iterated distinguished powers of an inverse have the expected depth bound. -/
theorem HasDepth.inv_pow_piterate {F : RNSeries p G} {n : ℕ} {g : G}
    (hg : F.HasDepth g n) (k : ℕ) :
    F.HasDepth ((g⁻¹) ^ (p ^ k)) (n * (p ^ k)) :=
  hg.inv.pow_p_iterate k

/-- Left-oriented iterated distinguished powers of an inverse. -/
theorem HasDepth.inv_powp_iterateleft {F : RNSeries p G} {n : ℕ} {g : G}
    (hg : F.HasDepth g n) (k : ℕ) :
    F.HasDepth ((g⁻¹) ^ (p ^ k)) ((p ^ k) * n) :=
  hg.inv.pow_p_iterateleft k

/-- Iterated distinguished powers, weakened to any smaller target depth. -/
theorem HasDepth.pow_p_iteratele {F : RNSeries p G} {n k r : ℕ} {g : G}
    (hg : F.HasDepth g n) (hr : r ≤ n * (p ^ k)) :
    F.HasDepth (g ^ (p ^ k)) r :=
  (hg.pow_p_iterate k).of_le hr

/-- Left-oriented iterated distinguished powers, weakened to any smaller target depth. -/
theorem HasDepth.pow_piterate_leftle {F : RNSeries p G} {n k r : ℕ} {g : G}
    (hg : F.HasDepth g n) (hr : r ≤ (p ^ k) * n) :
    F.HasDepth (g ^ (p ^ k)) r :=
  (hg.pow_p_iterateleft k).of_le hr

end RNSeries
end Submission

namespace Submission
namespace RNSeries

open scoped commutatorElement

variable {p : ℕ} {G : Type*} [Group G]

/-- Positive layers of a restricted N-series are abelian: commutators of two elements
in the `n`th layer vanish modulo the next term. -/
theorem layer_commutator_pos (F : RNSeries p G) {n : ℕ}
    (hn : 1 ≤ n) {q r : G ⧸ (F (n + 1))}
    (hq : q ∈ DFilt.lKern F.toDescending n)
    (hr : r ∈ DFilt.lKern F.toDescending n) : ⁅q, r⁆ = 1 := by
  refine QuotientGroup.induction_on q ?_ hq
  intro g hgq
  refine QuotientGroup.induction_on r ?_ hr
  intro h hhr
  have hg : g ∈ F n := (DFilt.layer_kernel_mk F.toDescending n g).1 hgq
  have hh : h ∈ F n := (DFilt.layer_kernel_mk F.toDescending n h).1 hhr
  change QuotientGroup.mk' (F (n + 1)) ⁅g, h⁆ = 1
  apply (QuotientGroup.eq_one_iff ⁅g, h⁆).mpr
  have hc : ⁅g, h⁆ ∈ F (n + n) := commutator_mem (F := F) (by omega) (by omega) hg hh
  exact F.antitone (by omega : n + 1 ≤ n + n) hc

/-- All layer kernels of a restricted N-series are abelian; the zero layer is trivial
because `F₁ = ⊤`. -/
theorem layer_commutator_one (F : RNSeries p G) {n : ℕ}
    {q r : G ⧸ (F (n + 1))}
    (hq : q ∈ DFilt.lKern F.toDescending n)
    (hr : r ∈ DFilt.lKern F.toDescending n) : ⁅q, r⁆ = 1 := by
  cases n with
  | zero =>
      have hq1 : q = 1 := by
        refine QuotientGroup.induction_on q ?_
        intro g
        change QuotientGroup.mk' (F 1) g = 1
        apply (QuotientGroup.eq_one_iff g).mpr
        simp [F.one_eq_top]
      have hr1 : r = 1 := by
        refine QuotientGroup.induction_on r ?_
        intro g
        change QuotientGroup.mk' (F 1) g = 1
        apply (QuotientGroup.eq_one_iff g).mpr
        simp [F.one_eq_top]
      simp [hq1, hr1]
  | succ k =>
      exact layer_commutator_pos F (Nat.succ_pos k) hq hr

/-- Multiplicative commutativity form for elements of a restricted-series layer kernel. -/
theorem layer_kernel_comm (F : RNSeries p G) (n : ℕ)
    (a b : DFilt.lKern F.toDescending n) : a * b = b * a := by
  apply (commutatorElement_eq_one_iff_mul_comm).1
  ext
  exact layer_commutator_one F a.property b.property

/-- Layer kernels of a restricted series are commutative groups. -/
noncomputable instance layer_comm_group (F : RNSeries p G) (n : ℕ) :
    CommGroup (DFilt.lKern F.toDescending n) :=
{ (inferInstance : Group (DFilt.lKern F.toDescending n)) with
  mul_comm := fun a b => layer_kernel_comm F n a b }

end RNSeries
end Submission

namespace Submission
namespace RNSeries

variable {p : ℕ} {G : Type*} [Group G]

/-- If the series parameter is at least two, every layer element has `p`th power
trivial in the next quotient. -/
theorem layer_kernel_two (F : RNSeries p G) (hp : 2 ≤ p)
    {n : ℕ} {q : G ⧸ (F (n + 1))}
    (hq : q ∈ DFilt.lKern F.toDescending n) : q ^ p = 1 := by
  cases n with
  | zero =>
      refine QuotientGroup.induction_on q ?_ hq
      intro g _
      change QuotientGroup.mk' (F 1) (g ^ p) = 1
      apply (QuotientGroup.eq_one_iff (g ^ p)).mpr
      simp [F.one_eq_top]
  | succ k =>
      refine QuotientGroup.induction_on q ?_ hq
      intro g hgq
      have hg : g ∈ F (Nat.succ k) :=
        (DFilt.layer_kernel_mk F.toDescending (Nat.succ k) g).1 hgq
      change QuotientGroup.mk' (F (Nat.succ k + 1)) (g ^ p) = 1
      apply (QuotientGroup.eq_one_iff (g ^ p)).mpr
      have hpw : g ^ p ∈ F (Nat.succ k * p) := F.pow_mem hg
      have hle : Nat.succ k + 1 ≤ Nat.succ k * p := by
        have h1 : Nat.succ k + 1 ≤ Nat.succ k * 2 := by omega
        have h2 : Nat.succ k * 2 ≤ Nat.succ k * p := Nat.mul_le_mul_left (Nat.succ k) hp
        exact le_trans h1 h2
      exact F.antitone hle hpw

/-- Any multiple of `p` also kills an element of a restricted-series layer kernel. -/
theorem layer_pow_two (F : RNSeries p G) (hp : 2 ≤ p)
    {n : ℕ} {q : G ⧸ (F (n + 1))}
    (hq : q ∈ DFilt.lKern F.toDescending n) (k : ℕ) :
    q ^ (p * k) = 1 := by
  rw [pow_mul]
  simp [layer_kernel_two F hp hq]

/-- Right-multiple orientation for the exponent-`p` layer-kernel bound. -/
theorem layer_right_two (F : RNSeries p G) (hp : 2 ≤ p)
    {n : ℕ} {q : G ⧸ (F (n + 1))}
    (hq : q ∈ DFilt.lKern F.toDescending n) (k : ℕ) :
    q ^ (k * p) = 1 := by
  rw [Nat.mul_comm k p]
  exact layer_pow_two F hp hq k

/-- Additive notation: `p` annihilates a restricted-series layer kernel. -/
theorem layer_nsmul_two (F : RNSeries p G) (hp : 2 ≤ p)
    (n : ℕ) (a : Additive (DFilt.lKern F.toDescending n)) :
    p • a = 0 := by
  cases a with
  | ofMul x =>
      change Additive.ofMul (x ^ p) =
        Additive.ofMul (1 : DFilt.lKern F.toDescending n)
      congr
      ext
      exact layer_kernel_two F hp x.property

/-- The additive layer kernel is canonically a `ZMod p`-module when `2 ≤ p`.
This is packaged as a reducible definition rather than a global instance, so callers can
activate it locally with `letI`. -/
@[reducible] noncomputable def zModModule (F : RNSeries p G)
    (hp : 2 ≤ p) (n : ℕ) :
    Module (ZMod p) (Additive (DFilt.lKern F.toDescending n)) :=
  AddCommGroup.zmodModule (n := p)
    (fun a => layer_nsmul_two F hp n a)

/-- Scalar multiplication in the local `ZMod p` layer-kernel module is represented by
powering by the chosen residue representative. -/
@[simp] theorem zmod_smul_mul (F : RNSeries p G)
    (hp : 2 ≤ p) (n : ℕ) (c : ZMod p)
    (a : DFilt.lKern F.toDescending n) :
    letI := zModModule F hp n
    c • (Additive.ofMul a : Additive (DFilt.lKern F.toDescending n)) =
      Additive.ofMul (a ^ c.val) := by
  letI := zModModule F hp n
  cases p with
  | zero => omega
  | succ p' => rfl

end RNSeries
end Submission

namespace Submission
namespace RNSeries

variable {p : ℕ} {G : Type*} [Group G]

/-- The concrete consecutive-term quotient attached to a restricted series. -/
abbrev nextQuotient (F : RNSeries p G) (n : ℕ) : Type _ :=
  F.toDescending n ⧸ DFilt.nextTermSubgroup F.toDescending n

/-- Finiteness transfers from a concrete consecutive quotient to its layer kernel. -/
theorem layer_next_quotient (F : RNSeries p G) (n : ℕ)
    [Finite (F.nextQuotient n)] :
    Finite (DFilt.lKern F.toDescending n) :=
  Finite.of_equiv (F.nextQuotient n)
    (DFilt.layerNextEquiv F.toDescending n).toEquiv

/-- Finiteness transfers from a layer kernel to the concrete consecutive quotient. -/
theorem next_layer_kernel (F : RNSeries p G) (n : ℕ)
    [Finite (DFilt.lKern F.toDescending n)] :
    Finite (F.nextQuotient n) :=
  Finite.of_equiv (DFilt.lKern F.toDescending n)
    (DFilt.layerNextEquiv F.toDescending n).symm.toEquiv

/-- Cardinalities of a finite consecutive quotient and its layer kernel agree. -/
theorem card_next_kernel (F : RNSeries p G) (n : ℕ)
    [Fintype (F.nextQuotient n)]
    [Fintype (DFilt.lKern F.toDescending n)] :
    Fintype.card (F.nextQuotient n) =
      Fintype.card (DFilt.lKern F.toDescending n) :=
  Fintype.card_congr (DFilt.layerNextEquiv F.toDescending n).toEquiv

/-- Concrete consecutive-term quotients of a restricted series are abelian. -/
theorem next_quotient_comm (F : RNSeries p G) (n : ℕ)
    (a b : F.nextQuotient n) : a * b = b * a := by
  let e := DFilt.layerNextEquiv F.toDescending n
  apply e.injective
  change e (a * b) = e (b * a)
  rw [map_mul, map_mul]
  exact RNSeries.layer_kernel_comm F n (e a) (e b)

/-- The group structure on a consecutive-term quotient is commutative for a restricted series. -/
noncomputable instance next_comm_group (F : RNSeries p G) (n : ℕ) :
    CommGroup (F.nextQuotient n) :=
{ (inferInstance : Group (F.nextQuotient n)) with
  mul_comm := next_quotient_comm F n }

/-- If `2 ≤ p`, every element of a concrete consecutive-term quotient has `p`th power one. -/
theorem next_quotient_two (F : RNSeries p G) (hp : 2 ≤ p)
    (n : ℕ) (a : F.nextQuotient n) : a ^ p = 1 := by
  let e := DFilt.layerNextEquiv F.toDescending n
  apply e.injective
  rw [map_pow, map_one]
  ext
  exact layer_kernel_two F hp (e a).property

/-- Any left multiple of `p` kills an element of a consecutive-term quotient. -/
theorem next_pow_two (F : RNSeries p G) (hp : 2 ≤ p)
    (n k : ℕ) (a : F.nextQuotient n) : a ^ (p * k) = 1 := by
  rw [pow_mul]
  simp [next_quotient_two F hp n a]

/-- Any right multiple of `p` kills an element of a consecutive-term quotient. -/
theorem next_right_two (F : RNSeries p G) (hp : 2 ≤ p)
    (n k : ℕ) (a : F.nextQuotient n) : a ^ (k * p) = 1 := by
  rw [Nat.mul_comm k p]
  exact next_pow_two F hp n k a

/-- Additive notation: `p` annihilates a consecutive-term quotient. -/
theorem next_nsmul_two (F : RNSeries p G) (hp : 2 ≤ p)
    (n : ℕ) (a : Additive (F.nextQuotient n)) : p • a = 0 := by
  cases a with
  | ofMul x =>
      change Additive.ofMul (x ^ p) = Additive.ofMul (1 : F.nextQuotient n)
      rw [next_quotient_two F hp n x]

/-- The additive consecutive quotient is canonically a `ZMod p`-module when `2 ≤ p`.
This reducible definition can be installed locally with `letI`. -/
@[reducible] noncomputable def nextZModule (F : RNSeries p G)
    (hp : 2 ≤ p) (n : ℕ) : Module (ZMod p) (Additive (F.nextQuotient n)) :=
  AddCommGroup.zmodModule (n := p)
    (fun a => next_nsmul_two F hp n a)

/-- Scalar multiplication in the local `ZMod p` consecutive-quotient module is represented
by powering by the chosen residue representative. -/
@[simp] theorem next_zmod_smul (F : RNSeries p G)
    (hp : 2 ≤ p) (n : ℕ) (c : ZMod p) (a : F.nextQuotient n) :
    letI := nextZModule F hp n
    c • (Additive.ofMul a : Additive (F.nextQuotient n)) = Additive.ofMul (a ^ c.val) := by
  letI := nextZModule F hp n
  cases p with
  | zero => omega
  | succ p' => rfl

/-- The standard equivalence between the concrete consecutive quotient and the layer kernel,
viewed as a `ZMod p`-linear equivalence under the local torsion module structures.
Use the reducible `letI`s in the type/body to keep these module structures opt-in. -/
noncomputable def nextLinearEquiv (F : RNSeries p G)
    (hp : 2 ≤ p) (n : ℕ) :
    letI := nextZModule F hp n
    letI := zModModule F hp n
    Additive (F.nextQuotient n) ≃ₗ[ZMod p]
      Additive (DFilt.lKern F.toDescending n) := by
  letI := nextZModule F hp n
  letI := zModModule F hp n
  let e : F.nextQuotient n ≃* DFilt.lKern F.toDescending n :=
    DFilt.layerNextEquiv F.toDescending n
  let ea : Additive (F.nextQuotient n) ≃+
      Additive (DFilt.lKern F.toDescending n) :=
    MulEquiv.toAdditive e
  refine { (ea.toAddMonoidHom.toZModLinearMap p) with
    invFun := ea.symm
    left_inv := ea.left_inv
    right_inv := ea.right_inv }

/-- Inverse orientation of the linearized layer/quotient equivalence. -/
noncomputable def layerNextLinear (F : RNSeries p G)
    (hp : 2 ≤ p) (n : ℕ) :
    letI := zModModule F hp n
    letI := nextZModule F hp n
    Additive (DFilt.lKern F.toDescending n) ≃ₗ[ZMod p]
      Additive (F.nextQuotient n) := by
  letI := nextZModule F hp n
  letI := zModModule F hp n
  exact (nextLinearEquiv F hp n).symm

/-- Pointwise formula for the inverse-oriented linearized layer equivalence. -/
@[simp] theorem layer_next_linear (F : RNSeries p G)
    (hp : 2 ≤ p) (n : ℕ)
    (b : DFilt.lKern F.toDescending n) :
    letI := zModModule F hp n
    letI := nextZModule F hp n
    layerNextLinear F hp n (Additive.ofMul b) =
      Additive.ofMul ((DFilt.layerNextEquiv F.toDescending n).symm b) := by
  dsimp [layerNextLinear, nextLinearEquiv]
  rfl

/-- Pointwise formula for the linearized quotient-to-layer equivalence. -/
@[simp] theorem next_linear_equiv (F : RNSeries p G)
    (hp : 2 ≤ p) (n : ℕ) (a : F.nextQuotient n) :
    letI := nextZModule F hp n
    letI := zModModule F hp n
    nextLinearEquiv F hp n (Additive.ofMul a) =
      Additive.ofMul (DFilt.layerNextEquiv F.toDescending n a) := by
  dsimp [nextLinearEquiv]
  rfl

/-- Pointwise formula for the inverse of the linearized quotient-to-layer equivalence. -/
@[simp] theorem next_linear_symm (F : RNSeries p G)
    (hp : 2 ≤ p) (n : ℕ)
    (b : DFilt.lKern F.toDescending n) :
    letI := nextZModule F hp n
    letI := zModModule F hp n
    (nextLinearEquiv F hp n).symm (Additive.ofMul b) =
      Additive.ofMul ((DFilt.layerNextEquiv F.toDescending n).symm b) := by
  dsimp [nextLinearEquiv]
  rfl

/-- The `ZMod p` ranks of the linearized consecutive quotient and layer kernel agree. -/
theorem next_rank_kernel (F : RNSeries p G)
    (hp : 2 ≤ p) (n : ℕ) :
    letI := nextZModule F hp n
    letI := zModModule F hp n
    Module.rank (ZMod p) (Additive (F.nextQuotient n)) =
      Module.rank (ZMod p) (Additive (DFilt.lKern F.toDescending n)) := by
  letI := nextZModule F hp n
  letI := zModModule F hp n
  exact LinearEquiv.rank_eq (nextLinearEquiv F hp n)

/-- Finrank version of the linearized layer/quotient dimension equality when `p` is prime. -/
theorem next_finrank_kernel (F : RNSeries p G)
    (hp : 2 ≤ p) [Fact p.Prime] (n : ℕ) :
    letI := nextZModule F hp n
    letI := zModModule F hp n
    Module.finrank (ZMod p) (Additive (F.nextQuotient n)) =
      Module.finrank (ZMod p) (Additive (DFilt.lKern F.toDescending n)) := by
  letI := nextZModule F hp n
  letI := zModModule F hp n
  exact LinearEquiv.finrank_eq (nextLinearEquiv F hp n)



/-- Reverse orientation of the rank equality for the linearized layer/quotient equivalence. -/
theorem layer_rank_next (F : RNSeries p G)
    (hp : 2 ≤ p) (n : ℕ) :
    letI := zModModule F hp n
    letI := nextZModule F hp n
    Module.rank (ZMod p)
        (Additive (DFilt.lKern F.toDescending n)) =
      Module.rank (ZMod p) (Additive (F.nextQuotient n)) := by
  letI := nextZModule F hp n
  letI := zModModule F hp n
  exact (next_rank_kernel F hp n).symm

/-- Reverse orientation of the finrank equality for prime restricted layers. -/
theorem layer_finrank_next (F : RNSeries p G)
    (hp : 2 ≤ p) [Fact p.Prime] (n : ℕ) :
    letI := zModModule F hp n
    letI := nextZModule F hp n
    Module.finrank (ZMod p)
        (Additive (DFilt.lKern F.toDescending n)) =
      Module.finrank (ZMod p) (Additive (F.nextQuotient n)) := by
  letI := nextZModule F hp n
  letI := zModModule F hp n
  exact (next_finrank_kernel F hp n).symm

/-- Module-finiteness over `ZMod p` is transported by the linearized quotient/layer
identification.  This version avoids installing a global module instance: both local
`ZMod p`-module structures are activated only inside the statement. -/
theorem next_module_kernel (F : RNSeries p G)
    (hp : 2 ≤ p) (n : ℕ) :
    letI := nextZModule F hp n
    letI := zModModule F hp n
    Module.Finite (ZMod p) (Additive (F.nextQuotient n)) ↔
      Module.Finite (ZMod p)
        (Additive (DFilt.lKern F.toDescending n)) := by
  letI := nextZModule F hp n
  letI := zModModule F hp n
  constructor
  · intro h
    exact Module.Finite.equiv (nextLinearEquiv F hp n)
  · intro h
    exact Module.Finite.equiv (layerNextLinear F hp n)

/-- Forward transport of module-finiteness from a consecutive quotient to its layer kernel. -/
theorem layer_module_next (F : RNSeries p G)
    (hp : 2 ≤ p) (n : ℕ)
    (h : letI := nextZModule F hp n
      Module.Finite (ZMod p) (Additive (F.nextQuotient n))) :
    letI := zModModule F hp n
    Module.Finite (ZMod p)
      (Additive (DFilt.lKern F.toDescending n)) := by
  letI := nextZModule F hp n
  letI := zModModule F hp n
  exact (next_module_kernel F hp n).1 h

/-- Backward transport of module-finiteness from a layer kernel to the consecutive quotient. -/
theorem next_module_layer (F : RNSeries p G)
    (hp : 2 ≤ p) (n : ℕ)
    (h : letI := zModModule F hp n
      Module.Finite (ZMod p)
        (Additive (DFilt.lKern F.toDescending n))) :
    letI := nextZModule F hp n
    Module.Finite (ZMod p) (Additive (F.nextQuotient n)) := by
  letI := nextZModule F hp n
  letI := zModModule F hp n
  exact (next_module_kernel F hp n).2 h


/-- A finite consecutive quotient is finitely generated as a module over the local `ZMod p`
structure. -/
theorem next_module_finite (F : RNSeries p G) (hp : 2 ≤ p)
    (n : ℕ) [Finite (F.nextQuotient n)] :
    letI := nextZModule F hp n
    Module.Finite (ZMod p) (Additive (F.nextQuotient n)) := by
  letI := nextZModule F hp n
  infer_instance

/-- A finite layer kernel is finitely generated as a module over the local `ZMod p` structure. -/
theorem layer_module_finite (F : RNSeries p G) (hp : 2 ≤ p)
    (n : ℕ) [Finite (DFilt.lKern F.toDescending n)] :
    letI := zModModule F hp n
    Module.Finite (ZMod p)
      (Additive (DFilt.lKern F.toDescending n)) := by
  letI := zModModule F hp n
  infer_instance

/-- Finiteness of the concrete quotient gives module-finiteness of the corresponding layer. -/
theorem module_next_quotient (F : RNSeries p G)
    (hp : 2 ≤ p) (n : ℕ) [Finite (F.nextQuotient n)] :
    letI := zModModule F hp n
    Module.Finite (ZMod p)
      (Additive (DFilt.lKern F.toDescending n)) := by
  letI := zModModule F hp n
  haveI : Finite (DFilt.lKern F.toDescending n) :=
    layer_next_quotient F n
  infer_instance

/-- Finiteness of a layer kernel gives module-finiteness of the concrete quotient. -/
theorem next_quotient_module (F : RNSeries p G)
    (hp : 2 ≤ p) (n : ℕ)
    [Finite (DFilt.lKern F.toDescending n)] :
    letI := nextZModule F hp n
    Module.Finite (ZMod p) (Additive (F.nextQuotient n)) := by
  letI := nextZModule F hp n
  haveI : Finite (F.nextQuotient n) := next_layer_kernel F n
  infer_instance


/-- Over a prime field `ZMod p`, finite-dimensionality is invariant under the linearized
quotient/layer identification. -/
theorem next_dimensional_kernel
    (F : RNSeries p G) (hp : 2 ≤ p) [Fact p.Prime] (n : ℕ) :
    letI := nextZModule F hp n
    letI := zModModule F hp n
    FiniteDimensional (ZMod p) (Additive (F.nextQuotient n)) ↔
      FiniteDimensional (ZMod p)
        (Additive (DFilt.lKern F.toDescending n)) := by
  letI := nextZModule F hp n
  letI := zModModule F hp n
  constructor
  · intro h
    exact (nextLinearEquiv F hp n).finiteDimensional
  · intro h
    exact (layerNextLinear F hp n).finiteDimensional

/-- Forward finite-dimensionality transport across the quotient-to-layer equivalence. -/
theorem layer_dimensional_next
    (F : RNSeries p G) (hp : 2 ≤ p) [Fact p.Prime] (n : ℕ)
    (h : letI := nextZModule F hp n
      FiniteDimensional (ZMod p) (Additive (F.nextQuotient n))) :
    letI := zModModule F hp n
    FiniteDimensional (ZMod p)
      (Additive (DFilt.lKern F.toDescending n)) := by
  letI := nextZModule F hp n
  letI := zModModule F hp n
  exact (next_dimensional_kernel F hp n).1 h

/-- Backward finite-dimensionality transport across the layer-to-quotient equivalence. -/
theorem next_dimensional_layer
    (F : RNSeries p G) (hp : 2 ≤ p) [Fact p.Prime] (n : ℕ)
    (h : letI := zModModule F hp n
      FiniteDimensional (ZMod p)
        (Additive (DFilt.lKern F.toDescending n))) :
    letI := nextZModule F hp n
    FiniteDimensional (ZMod p) (Additive (F.nextQuotient n)) := by
  letI := nextZModule F hp n
  letI := zModModule F hp n
  exact (next_dimensional_kernel F hp n).2 h


/-- A finite consecutive quotient is finite-dimensional over the prime field `ZMod p`. -/
theorem next_finite_dimensional (F : RNSeries p G)
    (hp : 2 ≤ p) [Fact p.Prime] (n : ℕ) [Finite (F.nextQuotient n)] :
    letI := nextZModule F hp n
    FiniteDimensional (ZMod p) (Additive (F.nextQuotient n)) := by
  letI := nextZModule F hp n
  infer_instance

/-- A finite layer kernel is finite-dimensional over the prime field `ZMod p`. -/
theorem layer_kernel_dimensional (F : RNSeries p G)
    (hp : 2 ≤ p) [Fact p.Prime] (n : ℕ)
    [Finite (DFilt.lKern F.toDescending n)] :
    letI := zModModule F hp n
    FiniteDimensional (ZMod p)
      (Additive (DFilt.lKern F.toDescending n)) := by
  letI := zModModule F hp n
  infer_instance

/-- A finite concrete quotient makes the corresponding layer finite-dimensional over `ZMod p`. -/
theorem dimensional_next_quotient
    (F : RNSeries p G) (hp : 2 ≤ p) [Fact p.Prime] (n : ℕ)
    [Finite (F.nextQuotient n)] :
    letI := zModModule F hp n
    FiniteDimensional (ZMod p)
      (Additive (DFilt.lKern F.toDescending n)) := by
  letI := zModModule F hp n
  haveI : Finite (DFilt.lKern F.toDescending n) :=
    layer_next_quotient F n
  infer_instance

/-- A finite layer kernel makes the concrete quotient finite-dimensional over `ZMod p`. -/
theorem next_quotient_dimensional
    (F : RNSeries p G) (hp : 2 ≤ p) [Fact p.Prime] (n : ℕ)
    [Finite (DFilt.lKern F.toDescending n)] :
    letI := nextZModule F hp n
    FiniteDimensional (ZMod p) (Additive (F.nextQuotient n)) := by
  letI := nextZModule F hp n
  haveI : Finite (F.nextQuotient n) := next_layer_kernel F n
  infer_instance

end RNSeries
end Submission
