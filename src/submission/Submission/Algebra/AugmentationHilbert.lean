import Submission.Algebra.Augmentation
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Finsupp.VectorSpace

/-!
# Hilbert-rank bookkeeping for augmentation layers

This file keeps the purely algebraic finite-support consequences of nilpotence of
augmentation powers separate from the presentation/GS coefficient layer.
-/

namespace Submission
namespace GroupAlgebra

noncomputable section

variable (K G : Type*) [Field K] [Group G]

/-- The (possibly zero for infinite-dimensional spaces, in mathlib's `finrank`
convention) rank of the successive augmentation layer `I^n/I^(n+1)`. -/
def augmentationLayerRank (n : ℕ) : ℕ :=
  Module.finrank K (augmentationLayer K G n)

omit [Group G] in
/-- For a finite group, the group algebra has dimension equal to the number of group elements. -/
theorem finrank_monoid_fintype [Fintype G] :
    Module.finrank K (MonoidAlgebra K G) = Fintype.card G := by
  change Module.finrank K (G →₀ K) = Fintype.card G
  simp

/-- Any augmentation-power submodule of a finite group algebra has rank bounded by `|G|`. -/
theorem augmentation_submodule_card [Fintype G] (n : ℕ) :
    Module.finrank K (augmentationPowerSubmodule K G n) ≤ Fintype.card G := by
  calc
    Module.finrank K (augmentationPowerSubmodule K G n) ≤
        Module.finrank K (MonoidAlgebra K G) :=
      Submodule.finrank_le (augmentationPowerSubmodule K G n)
    _ = Fintype.card G := finrank_monoid_fintype (K := K) (G := G)

/-- Each augmentation layer of a finite group algebra has rank bounded by `|G|`. -/
theorem layer_rank_card [Fintype G] (n : ℕ) :
    augmentationLayerRank K G n ≤ Fintype.card G := by
  unfold augmentationLayerRank
  calc
    Module.finrank K (augmentationLayer K G n) ≤
        Module.finrank K (augmentationPowerSubmodule K G n) :=
      Submodule.finrank_quotient_le (augmentationLayerDenom K G n)
    _ ≤ Fintype.card G := augmentation_submodule_card (K := K) (G := G) n

/-- If `I^N = 0`, every layer in degree at least `N` has rank zero. -/
theorem layer_rank_bot {N n : ℕ}
    (hN : augmentationPowerSubmodule K G N = ⊥) (hNn : N ≤ n) :
    augmentationLayerRank K G n = 0 := by
  unfold augmentationLayerRank
  haveI : Subsingleton (augmentationLayer K G n) :=
    subsingleton_augmentation_bot (R := K) (G := G) hN hNn
  exact Module.finrank_zero_of_subsingleton

/-- Support-bound form: if `I^(B+1)=0`, layer ranks vanish strictly above `B`. -/
theorem augmentation_rank_bot {B n : ℕ}
    (hB : augmentationPowerSubmodule K G (B + 1) = ⊥) (hn : B < n) :
    augmentationLayerRank K G n = 0 :=
  layer_rank_bot (K := K) (G := G) hB (Nat.succ_le_iff.mpr hn)

/-- If a later augmentation power is zero, the rank sequence is eventually zero
from that stage onward. -/
theorem rank_eventually_bot {N : ℕ}
    (hN : augmentationPowerSubmodule K G N = ⊥) :
    ∀ n, N ≤ n → augmentationLayerRank K G n = 0 := by
  intro n hn
  exact layer_rank_bot (K := K) (G := G) hN hn


/-- Augmentation-power submodule ranks are invariant under relabeling the group by an
isomorphism. -/
theorem submodule_finrank_equiv {H : Type*} [Group H]
    (e : G ≃* H) (n : ℕ) :
    Module.finrank K (augmentationPowerSubmodule K G n) =
      Module.finrank K (augmentationPowerSubmodule K H n) := by
  exact (augmentationPowerEquiv (R := K) (G := G) e n).finrank_eq

/-- Augmentation-layer ranks are invariant under relabeling the group by an isomorphism. -/
theorem augmentation_rank_equiv {H : Type*} [Group H] (e : G ≃* H) (n : ℕ) :
    augmentationLayerRank K G n = augmentationLayerRank K H n := by
  unfold augmentationLayerRank
  exact (augmentationLayerEquiv (R := K) (G := G) e n).finrank_eq

/-- Reverse-orientation form of invariance of augmentation-layer ranks under group
isomorphism. -/
theorem layer_rank_symm {H : Type*} [Group H] (e : G ≃* H) (n : ℕ) :
    augmentationLayerRank K H n = augmentationLayerRank K G n :=
  (augmentation_rank_equiv (K := K) (G := G) e n).symm

/-- Function-valued form of augmentation-layer rank invariance under group isomorphism. -/
theorem augmentation_rank_fun {H : Type*} [Group H] (e : G ≃* H) :
    (fun n : ℕ => augmentationLayerRank K G n) =
      fun n : ℕ => augmentationLayerRank K H n := by
  funext n
  exact augmentation_rank_equiv (K := K) (G := G) e n

/-- Vanishing of a single layer rank transports forward across a group isomorphism. -/
theorem augmentation_layer_rank {H : Type*} [Group H]
    (e : G ≃* H) {n : ℕ} (h : augmentationLayerRank K H n = 0) :
    augmentationLayerRank K G n = 0 := by
  rw [augmentation_rank_equiv (K := K) (G := G) e n]
  exact h

/-- Vanishing of a single layer rank transports backward across a group isomorphism. -/
theorem augmentation_rank_symm {H : Type*} [Group H]
    (e : G ≃* H) {n : ℕ} (h : augmentationLayerRank K G n = 0) :
    augmentationLayerRank K H n = 0 := by
  rw [← augmentation_rank_equiv (K := K) (G := G) e n]
  exact h

/-- Rank bounds for finite group algebras transport across group isomorphisms. -/
theorem augmentation_rank_card {H : Type*} [Group H] [Fintype H]
    (e : G ≃* H) (n : ℕ) :
    augmentationLayerRank K G n ≤ Fintype.card H := by
  rw [augmentation_rank_equiv (K := K) (G := G) e n]
  exact layer_rank_card (K := K) (G := H) n

/-- Reverse transported finite-cardinality bound for layer ranks. -/
theorem rank_card_symm {H : Type*} [Group H] [Fintype G]
    (e : G ≃* H) (n : ℕ) :
    augmentationLayerRank K H n ≤ Fintype.card G := by
  rw [← augmentation_rank_equiv (K := K) (G := G) e n]
  exact layer_rank_card (K := K) (G := G) n


/-- The zeroth truncation has dimension zero. -/
theorem augmentation_finrank_zero :
    Module.finrank K (augmentationTruncation K G 0) = 0 := by
  haveI := augmentation_truncation_subsingleton (R := K) (G := G)
  exact Module.finrank_zero_of_subsingleton

/-- A finite group algebra quotient truncation has dimension bounded by `|G|`. -/
theorem augmentation_finrank_card [Fintype G] (n : ℕ) :
    Module.finrank K (augmentationTruncation K G n) ≤ Fintype.card G := by
  calc
    Module.finrank K (augmentationTruncation K G n) ≤
        Module.finrank K (MonoidAlgebra K G) := by
      change Module.finrank K ((MonoidAlgebra K G) ⧸
          (Submodule.restrictScalars K (augmentationPower K G n))) ≤
        Module.finrank K (MonoidAlgebra K G)
      exact Submodule.finrank_quotient_le
        (Submodule.restrictScalars K (augmentationPower K G n))
    _ = Fintype.card G := finrank_monoid_fintype (K := K) (G := G)


/-- Truncation dimensions are invariant under relabeling the group by an isomorphism. -/
theorem truncation_finrank_equiv {H : Type*} [Group H]
    (e : G ≃* H) (n : ℕ) :
    Module.finrank K (augmentationTruncation K G n) =
      Module.finrank K (augmentationTruncation K H n) := by
  exact (truncationLinear (R := K) (G := G) e n).finrank_eq

/-- Reverse-orientation form of truncation-dimension invariance. -/
theorem finrank_equiv_symm {H : Type*} [Group H]
    (e : G ≃* H) (n : ℕ) :
    Module.finrank K (augmentationTruncation K H n) =
      Module.finrank K (augmentationTruncation K G n) :=
  (truncation_finrank_equiv (K := K) (G := G) e n).symm

/-- Function-valued form of truncation-dimension invariance. -/
theorem truncation_finrank_fun {H : Type*} [Group H]
    (e : G ≃* H) :
    (fun n : ℕ => Module.finrank K (augmentationTruncation K G n)) =
      fun n : ℕ => Module.finrank K (augmentationTruncation K H n) := by
  funext n
  exact truncation_finrank_equiv (K := K) (G := G) e n

/-- Finite-cardinality bound for truncation dimensions transported across a group isomorphism. -/
theorem augmentation_truncation_card {H : Type*} [Group H] [Fintype H]
    (e : G ≃* H) (n : ℕ) :
    Module.finrank K (augmentationTruncation K G n) ≤ Fintype.card H := by
  rw [truncation_finrank_equiv (K := K) (G := G) e n]
  exact augmentation_finrank_card (K := K) (G := H) n

/-- Reverse transported finite-cardinality bound for truncation dimensions. -/
theorem truncation_finrank_symm {H : Type*} [Group H]
    [Fintype G] (e : G ≃* H) (n : ℕ) :
    Module.finrank K (augmentationTruncation K H n) ≤ Fintype.card G := by
  rw [← truncation_finrank_equiv (K := K) (G := G) e n]
  exact augmentation_finrank_card (K := K) (G := G) n

/-- The first truncation `K[G]/I` has dimension one over the coefficient field. -/
theorem truncation_finrank_one :
    Module.finrank K (augmentationTruncation K G 1) = 1 := by
  calc
    Module.finrank K (augmentationTruncation K G 1) = Module.finrank K K :=
      (augmentationLinearEquiv K G).finrank_eq
    _ = 1 := Module.finrank_self K

/-- The linear kernel of the successive truncation map has the same dimension as the
corresponding augmentation layer. -/
theorem augmentation_linear_finrank (n : ℕ) :
    Module.finrank K (LinearMap.ker (augmentationLinear K G (Nat.le_succ n))) =
      augmentationLayerRank K G n := by
  unfold augmentationLayerRank
  exact (augmentationLinearKer K G n).finrank_eq.symm

/-- The ring-kernel submodule presentation of the successive truncation kernel has the
same dimension as the corresponding augmentation layer. -/
theorem augmentation_submodule_finrank (n : ℕ) :
    Module.finrank K (augmentationTruncationSubmodule K G n) =
      augmentationLayerRank K G n := by
  unfold augmentationLayerRank
  exact (augmentationLayerTruncation K G n).finrank_eq.symm

/-- Rank-nullity for a successive truncation map whose source is finite-dimensional. -/
theorem augmentation_truncation_module
    (n : ℕ) [Module.Finite K (augmentationTruncation K G (n + 1))] :
    Module.finrank K (augmentationTruncation K G n) +
        Module.finrank K
          (LinearMap.ker (augmentationLinear K G (Nat.le_succ n))) =
      Module.finrank K (augmentationTruncation K G (n + 1)) := by
  let f := augmentationLinear K G (Nat.le_succ n)
  letI : Module.Finite K (augmentationTruncation K G n) :=
    Module.Finite.of_surjective f
      (augmentation_linear_surjective K G (Nat.le_succ n))
  have h := f.finrank_range_add_finrank_ker
  have hr : Module.finrank K (LinearMap.range f) =
      Module.finrank K (augmentationTruncation K G n) := by
    rw [truncation_range_top (R := K) (G := G) (Nat.le_succ n)]
    simp
  rw [hr] at h
  simpa [f, Nat.succ_eq_add_one] using h

/-- Rank-nullity for the successive truncation map, in finite group algebras. -/
theorem truncation_finrank_kernel [Finite G] (n : ℕ) :
    Module.finrank K (augmentationTruncation K G n) +
        Module.finrank K
          (LinearMap.ker (augmentationLinear K G (Nat.le_succ n))) =
      Module.finrank K (augmentationTruncation K G (n + 1)) :=
  augmentation_truncation_module
    (K := K) (G := G) n

/-- Rank-nullity rewritten with the new augmentation-layer rank. -/
theorem finrank_rank_module
    (n : ℕ) [Module.Finite K (augmentationTruncation K G (n + 1))] :
    Module.finrank K (augmentationTruncation K G n) + augmentationLayerRank K G n =
      Module.finrank K (augmentationTruncation K G (n + 1)) := by
  rw [← augmentation_linear_finrank (K := K) (G := G) n]
  exact augmentation_truncation_module
    (K := K) (G := G) n

/-- Rank-nullity rewritten with the augmentation-layer rank for the successive kernel. -/
theorem augmentation_truncation_rank [Finite G] (n : ℕ) :
    Module.finrank K (augmentationTruncation K G n) + augmentationLayerRank K G n =
      Module.finrank K (augmentationTruncation K G (n + 1)) := by
  rw [← augmentation_linear_finrank (K := K) (G := G) n]
  exact truncation_finrank_kernel (K := K) (G := G) n

/-- Symmetric orientation under finite-dimensionality of the larger truncation. -/
theorem truncation_succ_module
    (n : ℕ) [Module.Finite K (augmentationTruncation K G (n + 1))] :
    Module.finrank K (augmentationTruncation K G (n + 1)) =
      Module.finrank K (augmentationTruncation K G n) + augmentationLayerRank K G n :=
  (finrank_rank_module (K := K) (G := G) n).symm

/-- Symmetric orientation of the finite-dimensional successive truncation rank formula. -/
theorem augmentation_succ_finrank [Finite G] (n : ℕ) :
    Module.finrank K (augmentationTruncation K G (n + 1)) =
      Module.finrank K (augmentationTruncation K G n) + augmentationLayerRank K G n :=
  (augmentation_truncation_rank (K := K) (G := G) n).symm

/-- A successive truncation has unchanged finite rank exactly when the new layer has rank zero. -/
theorem truncation_finrank_self [Finite G] {n : ℕ} :
    Module.finrank K (augmentationTruncation K G (n + 1)) =
        Module.finrank K (augmentationTruncation K G n) ↔
      augmentationLayerRank K G n = 0 := by
  rw [augmentation_succ_finrank (K := K) (G := G) n]
  omega

/-- Forward orientation of successor-rank stabilization. -/
theorem rank_truncation_self [Finite G]
    {n : ℕ}
    (h : Module.finrank K (augmentationTruncation K G (n + 1)) =
        Module.finrank K (augmentationTruncation K G n)) :
    augmentationLayerRank K G n = 0 :=
  (truncation_finrank_self (K := K) (G := G) (n := n)).mp h

/-- Reverse orientation of successor-rank stabilization. -/
theorem truncation_self_rank [Finite G]
    {n : ℕ} (h : augmentationLayerRank K G n = 0) :
    Module.finrank K (augmentationTruncation K G (n + 1)) =
      Module.finrank K (augmentationTruncation K G n) :=
  (truncation_finrank_self (K := K) (G := G) (n := n)).mpr h

/-- Successive truncation finrank strictly increases exactly when the new layer rank is positive. -/
theorem truncation_succ_finrank [Finite G] {n : ℕ} :
    Module.finrank K (augmentationTruncation K G n) <
        Module.finrank K (augmentationTruncation K G (n + 1)) ↔
      0 < augmentationLayerRank K G n := by
  rw [augmentation_succ_finrank (K := K) (G := G) n]
  omega

/-- Strict growth of truncation dimensions from positivity of the new layer. -/
theorem truncation_rank_pos [Finite G] {n : ℕ}
    (h : 0 < augmentationLayerRank K G n) :
    Module.finrank K (augmentationTruncation K G n) <
      Module.finrank K (augmentationTruncation K G (n + 1)) :=
  (truncation_succ_finrank (K := K) (G := G) (n := n)).2 h

/-- Positivity of the new layer from strict growth of truncation dimensions. -/
theorem pos_truncation_finrank [Finite G] {n : ℕ}
    (h : Module.finrank K (augmentationTruncation K G n) <
      Module.finrank K (augmentationTruncation K G (n + 1))) :
    0 < augmentationLayerRank K G n :=
  (truncation_succ_finrank (K := K) (G := G) (n := n)).1 h

/-- Finite-group truncation dimensions are partial sums of augmentation-layer ranks. -/
theorem truncation_finrank_rank [Finite G] (n : ℕ) :
    Module.finrank K (augmentationTruncation K G n) =
      ∑ i ∈ Finset.range n, augmentationLayerRank K G i := by
  induction n with
  | zero =>
      rw [augmentation_finrank_zero]
      simp
  | succ n ih =>
      rw [augmentation_succ_finrank (K := K) (G := G) n, ih,
        Finset.sum_range_succ]

/-- Truncation dimensions are partial sums whenever every truncation is finite-dimensional. -/
theorem truncation_rank_module
    (hfinite : ∀ n, Module.Finite K (augmentationTruncation K G n))
    (n : ℕ) :
    Module.finrank K (augmentationTruncation K G n) =
      ∑ i ∈ Finset.range n, augmentationLayerRank K G i := by
  induction n with
  | zero =>
      rw [augmentation_finrank_zero]
      simp
  | succ n ih =>
      letI := hfinite (n + 1)
      rw [truncation_succ_module
        (K := K) (G := G) n, ih, Finset.sum_range_succ]

/-- Reverse orientation of the partial-sum formula for truncation dimensions. -/
theorem rank_truncation_finrank [Finite G] (n : ℕ) :
    (∑ i ∈ Finset.range n, augmentationLayerRank K G i) =
      Module.finrank K (augmentationTruncation K G n) :=
  (truncation_finrank_rank (K := K) (G := G) n).symm

/-- Reverse orientation under finite-dimensionality of every truncation. -/
theorem truncation_finrank_module
    (hfinite : ∀ n, Module.Finite K (augmentationTruncation K G n))
    (n : ℕ) :
    (∑ i ∈ Finset.range n, augmentationLayerRank K G i) =
      Module.finrank K (augmentationTruncation K G n) :=
  (truncation_rank_module
    (K := K) (G := G) hfinite n).symm

/-- Successor recursion for partial sums of augmentation-layer ranks. -/
theorem sum_layer_succ (n : ℕ) :
    (∑ i ∈ Finset.range (n + 1), augmentationLayerRank K G i) =
      (∑ i ∈ Finset.range n, augmentationLayerRank K G i) +
        augmentationLayerRank K G n := by
  simp [Finset.sum_range_succ]

/-- The empty partial sum of layer ranks is zero. -/
@[simp] theorem sum_rank_zero :
    (∑ i ∈ Finset.range 0, augmentationLayerRank K G i) = 0 := by
  simp

/-- The first partial sum of layer ranks is the zeroth layer rank. -/
@[simp] theorem layer_rank_one :
    (∑ i ∈ Finset.range 1, augmentationLayerRank K G i) =
      augmentationLayerRank K G 0 := by
  simp

/-- Partial sums of layer ranks are invariant under relabeling the group. -/
theorem sum_rank_equiv {H : Type*} [Group H] (e : G ≃* H) (n : ℕ) :
    (∑ i ∈ Finset.range n, augmentationLayerRank K G i) =
      ∑ i ∈ Finset.range n, augmentationLayerRank K H i := by
  apply Finset.sum_congr rfl
  intro i hi
  exact augmentation_rank_equiv (K := K) (G := G) e i

/-- Reverse-orientation form of partial-sum invariance. -/
theorem sum_layer_symm {H : Type*} [Group H] (e : G ≃* H) (n : ℕ) :
    (∑ i ∈ Finset.range n, augmentationLayerRank K H i) =
      ∑ i ∈ Finset.range n, augmentationLayerRank K G i :=
  (sum_rank_equiv (K := K) (G := G) e n).symm

/-- Partial sums of layer ranks are bounded by the group order for finite groups. -/
theorem sum_layer_card [Fintype G] (n : ℕ) :
    (∑ i ∈ Finset.range n, augmentationLayerRank K G i) ≤ Fintype.card G := by
  rw [rank_truncation_finrank (K := K) (G := G) n]
  exact augmentation_finrank_card (K := K) (G := G) n

/-- Transported bound for partial sums of layer ranks across a group isomorphism. -/
theorem sum_rank_card {H : Type*} [Group H] [Fintype H]
    (e : G ≃* H) (n : ℕ) :
    (∑ i ∈ Finset.range n, augmentationLayerRank K G i) ≤ Fintype.card H := by
  letI : Fintype G := Fintype.ofEquiv H e.toEquiv.symm
  rw [rank_truncation_finrank (K := K) (G := G) n,
    truncation_finrank_equiv (K := K) (G := G) e n]
  exact augmentation_finrank_card (K := K) (G := H) n

/-- Reverse transported bound for partial sums of layer ranks across a group isomorphism. -/
theorem sum_rank_symm {H : Type*} [Group H] [Fintype G]
    (e : G ≃* H) (n : ℕ) :
    (∑ i ∈ Finset.range n, augmentationLayerRank K H i) ≤ Fintype.card G := by
  letI : Fintype H := Fintype.ofEquiv G e.toEquiv
  rw [rank_truncation_finrank (K := K) (G := H) n,
    ← truncation_finrank_equiv (K := K) (G := G) e n]
  exact augmentation_finrank_card (K := K) (G := G) n

/-- A layer rank is the successive difference of truncation dimensions for finite groups. -/
theorem rank_truncation_sub [Finite G] (n : ℕ) :
    augmentationLayerRank K G n =
      Module.finrank K (augmentationTruncation K G (n + 1)) -
        Module.finrank K (augmentationTruncation K G n) := by
  rw [augmentation_succ_finrank (K := K) (G := G) n]
  exact (Nat.add_sub_cancel_left _ _).symm

/-- Truncation dimensions are monotone in the cutoff for finite group algebras. -/
theorem truncation_finrank_succ [Finite G] (n : ℕ) :
    Module.finrank K (augmentationTruncation K G n) ≤
      Module.finrank K (augmentationTruncation K G (n + 1)) := by
  rw [augmentation_succ_finrank (K := K) (G := G) n]
  exact Nat.le_add_right _ _

/-- Truncation dimensions are monotone in the cutoff for finite group algebras. -/
theorem truncation_finrank_mono [Finite G] {m n : ℕ} (hmn : m ≤ n) :
    Module.finrank K (augmentationTruncation K G m) ≤
      Module.finrank K (augmentationTruncation K G n) := by
  induction hmn with
  | refl => rfl
  | step hmn ih =>
      exact le_trans ih (truncation_finrank_succ (K := K) (G := G) _)

/-- Every positive truncation cutoff has positive dimension for finite group algebras. -/
theorem truncation_finrank_pos [Finite G] {n : ℕ} (hn : 0 < n) :
    0 < Module.finrank K (augmentationTruncation K G n) := by
  have h1n : 1 ≤ n := Nat.succ_le_iff.mpr hn
  have hmono := truncation_finrank_mono (K := K) (G := G) h1n
  rw [truncation_finrank_one (K := K) (G := G)] at hmono
  exact lt_of_lt_of_le Nat.zero_lt_one hmono

/-- In particular, the `(B+1)`-st truncation has positive dimension. -/
theorem truncation_pos_succ [Finite G] (B : ℕ) :
    0 < Module.finrank K (augmentationTruncation K G (B + 1)) :=
  truncation_finrank_pos (K := K) (G := G) (Nat.succ_pos B)

/-- Extending a layer-rank partial sum by one term cannot decrease it. -/
theorem layer_rank_succ (n : ℕ) :
    (∑ i ∈ Finset.range n, augmentationLayerRank K G i) ≤
      ∑ i ∈ Finset.range (n + 1), augmentationLayerRank K G i := by
  rw [sum_layer_succ (K := K) (G := G) n]
  omega

/-- Extending by a positive layer strictly increases the partial sum. -/
theorem rank_succ_pos {n : ℕ}
    (h : 0 < augmentationLayerRank K G n) :
    (∑ i ∈ Finset.range n, augmentationLayerRank K G i) <
      ∑ i ∈ Finset.range (n + 1), augmentationLayerRank K G i := by
  rw [sum_layer_succ (K := K) (G := G) n]
  omega

/-- Partial sums of layer ranks are monotone in the cutoff, purely because the
summands are natural numbers. -/
theorem rank_mono_nat {m n : ℕ} (hmn : m ≤ n) :
    (∑ i ∈ Finset.range m, augmentationLayerRank K G i) ≤
      ∑ i ∈ Finset.range n, augmentationLayerRank K G i := by
  classical
  exact Finset.sum_le_sum_of_subset_of_nonneg (by
    intro x hx
    exact Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hx) hmn)) (by
    intro x hx hnot
    exact Nat.zero_le _)

/-- Partial sums of layer ranks are monotone in the cutoff for finite groups. -/
theorem sum_rank_mono [Finite G] {m n : ℕ} (hmn : m ≤ n) :
    (∑ i ∈ Finset.range m, augmentationLayerRank K G i) ≤
      ∑ i ∈ Finset.range n, augmentationLayerRank K G i := by
  rw [rank_truncation_finrank (K := K) (G := G) m,
    rank_truncation_finrank (K := K) (G := G) n]
  exact truncation_finrank_mono (K := K) (G := G) hmn

/-- Every nonempty partial sum of layer ranks is positive for finite groups. -/
theorem sum_pos_succ [Finite G] (n : ℕ) :
    0 < (∑ i ∈ Finset.range (n + 1), augmentationLayerRank K G i) := by
  rw [rank_truncation_finrank (K := K) (G := G) (n + 1)]
  exact truncation_pos_succ (K := K) (G := G) n

/-- Partial sums at a positive cutoff are positive for finite groups. -/
theorem layer_rank_pos [Finite G] {n : ℕ} (hn : 0 < n) :
    0 < (∑ i ∈ Finset.range n, augmentationLayerRank K G i) := by
  rcases Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn) with ⟨m, rfl⟩
  exact sum_pos_succ (K := K) (G := G) m

/-- Nonempty partial sums are at least one. -/
theorem sum_rank_succ [Finite G] (n : ℕ) :
    1 ≤ (∑ i ∈ Finset.range (n + 1), augmentationLayerRank K G i) :=
  Nat.succ_le_iff.mpr (sum_pos_succ (K := K) (G := G) n)

/-- Positivity of nonempty partial sums transported across a group isomorphism. -/
theorem rank_pos_succ {H : Type*} [Group H] [Finite H]
    (e : G ≃* H) (n : ℕ) :
    0 < (∑ i ∈ Finset.range (n + 1), augmentationLayerRank K G i) := by
  rw [sum_rank_equiv (K := K) (G := G) e (n + 1)]
  exact sum_pos_succ (K := K) (G := H) n

/-- Positive-cutoff form of transported partial-sum positivity. -/
theorem sum_rank_pos {H : Type*} [Group H] [Finite H]
    (e : G ≃* H) {n : ℕ} (hn : 0 < n) :
    0 < (∑ i ∈ Finset.range n, augmentationLayerRank K G i) := by
  rw [sum_rank_equiv (K := K) (G := G) e n]
  exact layer_rank_pos (K := K) (G := H) hn


/-- Once an augmentation power vanishes, finite-group truncation dimensions stabilize
at the next step in every later degree. -/
theorem truncation_succ_bot [Finite G]
    {N n : ℕ} (hN : augmentationPowerSubmodule K G N = ⊥) (hNn : N ≤ n) :
    Module.finrank K (augmentationTruncation K G (n + 1)) =
      Module.finrank K (augmentationTruncation K G n) := by
  rw [augmentation_succ_finrank (K := K) (G := G) n,
    layer_rank_bot (K := K) (G := G) hN hNn,
    add_zero]

/-- Support-bound version of stabilization: if `I^(B+1)=0`, truncation dimensions
stabilize after degree `B`. -/
theorem truncation_finrank_bot [Finite G]
    {B n : ℕ} (hB : augmentationPowerSubmodule K G (B + 1) = ⊥) (hn : B < n) :
    Module.finrank K (augmentationTruncation K G (n + 1)) =
      Module.finrank K (augmentationTruncation K G n) :=
  truncation_succ_bot (K := K) (G := G) hB
    (Nat.succ_le_iff.mpr hn)

/-- Once `I^N` vanishes, all later truncation dimensions are equal. -/
theorem augmentation_truncation_finrank [Finite G]
    {N m n : ℕ} (hN : augmentationPowerSubmodule K G N = ⊥)
    (hm : N ≤ m) (hmn : m ≤ n) :
    Module.finrank K (augmentationTruncation K G n) =
      Module.finrank K (augmentationTruncation K G m) := by
  induction hmn with
  | refl => rfl
  | step hmn ih =>
      rw [truncation_succ_bot
        (K := K) (G := G) hN (le_trans hm hmn)]
      exact ih

/-- Once `I^N` vanishes, any two truncation dimensions at cutoffs at least `N`
are equal. -/
theorem truncation_power_bot [Finite G]
    {N m n : ℕ} (hN : augmentationPowerSubmodule K G N = ⊥)
    (hm : N ≤ m) (hn : N ≤ n) :
    Module.finrank K (augmentationTruncation K G m) =
      Module.finrank K (augmentationTruncation K G n) := by
  rcases le_total m n with hmn | hnm
  · exact (augmentation_truncation_finrank
      (K := K) (G := G) hN hm hmn).symm
  · exact augmentation_truncation_finrank
      (K := K) (G := G) hN hn hnm

/-- Support-bound version: if `I^(B+1)=0`, all truncation dimensions at cutoffs
`m,n` strictly past `B` agree. -/
theorem augmentation_truncation_bot [Finite G]
    {B m n : ℕ} (hB : augmentationPowerSubmodule K G (B + 1) = ⊥)
    (hm : B < m) (hmn : m ≤ n) :
    Module.finrank K (augmentationTruncation K G n) =
      Module.finrank K (augmentationTruncation K G m) :=
  augmentation_truncation_finrank (K := K) (G := G) hB
    (Nat.succ_le_iff.mpr hm) hmn

/-- Unordered support-bound version: any two cutoffs strictly past `B` have the
same truncation dimension once `I^(B+1)=0`. -/
theorem augmentation_truncation_bot₂ [Finite G]
    {B m n : ℕ} (hB : augmentationPowerSubmodule K G (B + 1) = ⊥)
    (hm : B < m) (hn : B < n) :
    Module.finrank K (augmentationTruncation K G m) =
      Module.finrank K (augmentationTruncation K G n) :=
  truncation_power_bot (K := K) (G := G) hB
    (Nat.succ_le_iff.mpr hm) (Nat.succ_le_iff.mpr hn)

/-- Each layer rank is bounded by the next truncation dimension. -/
theorem rank_truncation_succ [Finite G] (n : ℕ) :
    augmentationLayerRank K G n ≤
      Module.finrank K (augmentationTruncation K G (n + 1)) := by
  rw [augmentation_succ_finrank (K := K) (G := G) n]
  exact Nat.le_add_left _ _

/-- Successive truncation kernels are bounded by the group order when the group is finite. -/
theorem truncation_finrank_card [Fintype G] (n : ℕ) :
    Module.finrank K (LinearMap.ker (augmentationLinear K G (Nat.le_succ n))) ≤
      Fintype.card G := by
  rw [augmentation_linear_finrank (K := K) (G := G) n]
  exact layer_rank_card (K := K) (G := G) n

/-- Ring-kernel-submodule form of the finite-cardinality bound for successive kernels. -/
theorem submodule_finrank_card [Fintype G] (n : ℕ) :
    Module.finrank K (augmentationTruncationSubmodule K G n) ≤ Fintype.card G := by
  rw [augmentation_submodule_finrank (K := K) (G := G) n]
  exact layer_rank_card (K := K) (G := G) n

/-- Successive linear-kernel dimensions are invariant under relabeling the group. -/
theorem truncation_linear_finrank {H : Type*} [Group H]
    (e : G ≃* H) (n : ℕ) :
    Module.finrank K (LinearMap.ker (augmentationLinear K G (Nat.le_succ n))) =
      Module.finrank K (LinearMap.ker (augmentationLinear K H (Nat.le_succ n))) := by
  rw [augmentation_linear_finrank (K := K) (G := G) n,
    augmentation_linear_finrank (K := K) (G := H) n]
  exact augmentation_rank_equiv (K := K) (G := G) e n

/-- Successive ring-kernel-submodule dimensions are invariant under relabeling the group. -/
theorem augmentation_truncation_submodule {H : Type*} [Group H]
    (e : G ≃* H) (n : ℕ) :
    Module.finrank K (augmentationTruncationSubmodule K G n) =
      Module.finrank K (augmentationTruncationSubmodule K H n) := by
  rw [augmentation_submodule_finrank (K := K) (G := G) n,
    augmentation_submodule_finrank (K := K) (G := H) n]
  exact augmentation_rank_equiv (K := K) (G := G) e n

/-- Reverse-orientation form of successive linear-kernel dimension invariance. -/
theorem augmentation_finrank_symm {H : Type*} [Group H]
    (e : G ≃* H) (n : ℕ) :
    Module.finrank K (LinearMap.ker (augmentationLinear K H (Nat.le_succ n))) =
      Module.finrank K (LinearMap.ker (augmentationLinear K G (Nat.le_succ n))) :=
  (truncation_linear_finrank (K := K) (G := G) e n).symm

/-- Function-valued form of successive linear-kernel dimension invariance. -/
theorem augmentation_truncation_fun {H : Type*} [Group H]
    (e : G ≃* H) :
    (fun n : ℕ => Module.finrank K
        (LinearMap.ker (augmentationLinear K G (Nat.le_succ n)))) =
      fun n : ℕ => Module.finrank K
        (LinearMap.ker (augmentationLinear K H (Nat.le_succ n))) := by
  funext n
  exact truncation_linear_finrank (K := K) (G := G) e n

/-- Reverse-orientation form of successive ring-kernel-submodule dimension invariance. -/
theorem submodule_finrank_symm {H : Type*} [Group H]
    (e : G ≃* H) (n : ℕ) :
    Module.finrank K (augmentationTruncationSubmodule K H n) =
      Module.finrank K (augmentationTruncationSubmodule K G n) :=
  (augmentation_truncation_submodule (K := K) (G := G) e n).symm

/-- Function-valued form of successive ring-kernel-submodule dimension invariance. -/
theorem truncation_submodule_fun {H : Type*} [Group H]
    (e : G ≃* H) :
    (fun n : ℕ => Module.finrank K (augmentationTruncationSubmodule K G n)) =
      fun n : ℕ => Module.finrank K (augmentationTruncationSubmodule K H n) := by
  funext n
  exact augmentation_truncation_submodule (K := K) (G := G) e n

/-- Transported finite-cardinality bound for successive linear kernels. -/
theorem augmentation_truncation_linear {H : Type*} [Group H]
    [Fintype H] (e : G ≃* H) (n : ℕ) :
    Module.finrank K (LinearMap.ker (augmentationLinear K G (Nat.le_succ n))) ≤
      Fintype.card H := by
  rw [truncation_linear_finrank (K := K) (G := G) e n]
  exact truncation_finrank_card (K := K) (G := H) n

/-- Reverse transported finite-cardinality bound for successive linear kernels. -/
theorem augmentation_truncation_symm {H : Type*}
    [Group H] [Fintype G] (e : G ≃* H) (n : ℕ) :
    Module.finrank K (LinearMap.ker (augmentationLinear K H (Nat.le_succ n))) ≤
      Fintype.card G := by
  rw [← truncation_linear_finrank (K := K) (G := G) e n]
  exact truncation_finrank_card (K := K) (G := G) n

/-- Transported finite-cardinality bound for successive ring-kernel submodules. -/
theorem truncation_submodule_finrank {H : Type*}
    [Group H] [Fintype H] (e : G ≃* H) (n : ℕ) :
    Module.finrank K (augmentationTruncationSubmodule K G n) ≤ Fintype.card H := by
  rw [augmentation_truncation_submodule (K := K) (G := G) e n]
  exact submodule_finrank_card (K := K) (G := H) n

/-- Reverse transported finite-cardinality bound for successive ring-kernel submodules. -/
theorem truncation_submodule_symm {H : Type*}
    [Group H] [Fintype G] (e : G ≃* H) (n : ℕ) :
    Module.finrank K (augmentationTruncationSubmodule K H n) ≤ Fintype.card G := by
  rw [← augmentation_truncation_submodule (K := K) (G := G) e n]
  exact submodule_finrank_card (K := K) (G := G) n

/-- The zeroth augmentation-layer rank is one. -/
theorem augmentation_rank_zero : augmentationLayerRank K G 0 = 1 := by
  unfold augmentationLayerRank
  calc
    Module.finrank K (augmentationLayer K G 0) = Module.finrank K K :=
      (augmentationZeroEquiv K G).finrank_eq
    _ = 1 := Module.finrank_self K

/-- The first partial sum of layer ranks is one. -/
theorem sum_rank_one :
    (∑ i ∈ Finset.range 1, augmentationLayerRank K G i) = 1 := by
  simp [augmentation_rank_zero (K := K) (G := G)]

/-- The first partial sum is positive. -/
theorem sum_layer_pos :
    0 < (∑ i ∈ Finset.range 1, augmentationLayerRank K G i) := by
  rw [sum_rank_one]
  norm_num

/-- Lower-bound form of the first partial sum. -/
theorem sum_layer_rank :
    1 ≤ (∑ i ∈ Finset.range 1, augmentationLayerRank K G i) := by
  rw [sum_rank_one]

/-- Any nonempty partial sum of layer ranks is positive, without finiteness assumptions. -/
theorem sum_pos_nat {n : ℕ} (hn : 0 < n) :
    0 < (∑ i ∈ Finset.range n, augmentationLayerRank K G i) := by
  have h1n : 1 ≤ n := Nat.succ_le_iff.mpr hn
  have hmono := rank_mono_nat (K := K) (G := G) h1n
  exact lt_of_lt_of_le (sum_layer_pos (K := K) (G := G)) hmono

/-- Succ-indexed nonempty partial sums are positive, without finiteness assumptions. -/
theorem pos_succ_nat (n : ℕ) :
    0 < (∑ i ∈ Finset.range (n + 1), augmentationLayerRank K G i) :=
  sum_pos_nat (K := K) (G := G) (Nat.succ_pos n)

/-- Succ-indexed lower-bound form for nonempty partial sums, without finiteness assumptions. -/
theorem rank_succ_nat (n : ℕ) :
    1 ≤ (∑ i ∈ Finset.range (n + 1), augmentationLayerRank K G i) :=
  Nat.succ_le_iff.mpr (pos_succ_nat (K := K) (G := G) n)

/-- Lower-bound form for any nonempty partial sum of layer ranks. -/
theorem rank_pos_nat {n : ℕ} (hn : 0 < n) :
    1 ≤ (∑ i ∈ Finset.range n, augmentationLayerRank K G i) :=
  Nat.succ_le_iff.mpr (sum_pos_nat (K := K) (G := G) hn)

/-- Positivity of the zeroth augmentation-layer rank. -/
theorem augmentation_rank_pos : 0 < augmentationLayerRank K G 0 := by
  rw [augmentation_rank_zero]
  norm_num

/-- Lower bound form of the zeroth augmentation-layer rank. -/
theorem layer_rank_zero : 1 ≤ augmentationLayerRank K G 0 := by
  rw [augmentation_rank_zero]


/-- The first successive linear kernel (for `K[G]/I → K[G]/I^0`) has dimension one. -/
theorem truncation_finrank_zero :
    Module.finrank K (LinearMap.ker (augmentationLinear K G (Nat.le_succ 0))) = 1 := by
  rw [augmentation_linear_finrank (K := K) (G := G) 0,
    augmentation_rank_zero]

/-- The first successive ring-kernel submodule has dimension one. -/
theorem submodule_finrank_zero :
    Module.finrank K (augmentationTruncationSubmodule K G 0) = 1 := by
  rw [augmentation_submodule_finrank (K := K) (G := G) 0,
    augmentation_rank_zero]

end
end GroupAlgebra
end Submission
