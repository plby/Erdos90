import Towers.Algebra.AugmentationHilbert
import Towers.Group.GSBookkeeping
import Towers.Group.PresentedFox

/-!
# Bridge from augmentation-layer Hilbert ranks to GS sequence support

This small module connects abstract nilpotence of augmentation powers to the
finite-support predicate used by the formal GS coefficient bookkeeping.
-/

namespace Towers
namespace GroupAlgebra

noncomputable section

variable (K G : Type*) [Field K] [_root_.Group G]

/-- If `I^(B+1)=0`, the augmentation-layer rank sequence is supported in degrees
at most `B` in the sense used by the GS bookkeeping layer. -/
theorem rank_support_bot {B : ℕ}
    (hB : augmentationPowerSubmodule K G (B + 1) = ⊥) :
    FPres.SSBound (augmentationLayerRank K G) B := by
  intro n hn
  exact augmentation_rank_bot (K := K) (G := G) hB hn

/-- Under a nilpotence bound, truncating the augmentation-layer rank sequence at
the bound does not change it. -/
theorem truncate_succ_bot {B : ℕ}
    (hB : augmentationPowerSubmodule K G (B + 1) = ⊥) :
    FPres.truncateSeq (augmentationLayerRank K G) B =
      augmentationLayerRank K G := by
  funext n
  by_cases hn : n ≤ B
  · exact FPres.truncate_apply_le (augmentationLayerRank K G) hn
  · have hgt : B < n := Nat.lt_of_not_ge hn
    rw [FPres.truncate_seq (augmentationLayerRank K G) hgt]
    exact (augmentation_rank_bot
      (K := K) (G := G) hB hgt).symm

/-- Pointwise form of truncation invariance at a nilpotence bound. -/
theorem truncate_seq_rank {B n : ℕ}
    (hB : augmentationPowerSubmodule K G (B + 1) = ⊥) :
    FPres.truncateSeq (augmentationLayerRank K G) B n =
      augmentationLayerRank K G n := by
  exact congrFun
    (truncate_succ_bot (K := K) (G := G) hB) n

/-- For augmentation-layer ranks, truncation identity at a cutoff is equivalent to the
GS support-bound predicate at that cutoff. -/
theorem truncate_seq_bound {B : ℕ} :
    FPres.truncateSeq (augmentationLayerRank K G) B =
        augmentationLayerRank K G ↔
      FPres.SSBound (augmentationLayerRank K G) B :=
  FPres.truncate_support_bound

/-- Truncating at any later cutoff also leaves nilpotent augmentation-layer ranks unchanged. -/
theorem truncate_rank_bot {B M : ℕ}
    (hB : augmentationPowerSubmodule K G (B + 1) = ⊥) (hBM : B ≤ M) :
    FPres.truncateSeq (augmentationLayerRank K G) M =
      augmentationLayerRank K G := by
  exact FPres.truncate_self_bound
    (rank_support_bot (K := K) (G := G) hB) hBM

/-- Pointwise form of truncation invariance at any later cutoff. -/
theorem truncate_seq_bot {B M n : ℕ}
    (hB : augmentationPowerSubmodule K G (B + 1) = ⊥) (hBM : B ≤ M) :
    FPres.truncateSeq (augmentationLayerRank K G) M n =
      augmentationLayerRank K G n := by
  exact congrFun
    (truncate_rank_bot
      (K := K) (G := G) hB hBM) n

/-- Prefix mass of augmentation-layer ranks is the dimension of the corresponding
truncation, for finite groups.  This is the GS-bookkeeping orientation of the
partial-sum formula. -/
theorem mass_truncation_finrank [Finite G] (B : ℕ) :
    (∑ k ∈ Finset.range (B + 1), augmentationLayerRank K G k) =
      Module.finrank K (augmentationTruncation K G (B + 1)) :=
  rank_truncation_finrank (K := K) (G := G) (B + 1)

/-- Forward orientation of the prefix-mass/truncation-dimension identity. -/
theorem rank_prefix_mass [Finite G] (B : ℕ) :
    Module.finrank K (augmentationTruncation K G (B + 1)) =
      ∑ k ∈ Finset.range (B + 1), augmentationLayerRank K G k :=
  (mass_truncation_finrank (K := K) (G := G) B).symm

/-- The degree-zero augmentation prefix mass is one. -/
@[simp] theorem prefix_mass_zero :
    (∑ k ∈ Finset.range (0 + 1), augmentationLayerRank K G k) = 1 := by
  simp [augmentation_rank_zero (K := K) (G := G)]

/-- The finite prefix mass through degree `B` is positive: the zeroth layer has rank one. -/
theorem augmentation_mass_pos (B : ℕ) :
    0 < ∑ k ∈ Finset.range (B + 1), augmentationLayerRank K G k := by
  apply FPres.mass_pos_zero
  simp [augmentation_rank_zero (K := K) (G := G)]

/-- Prefix masses grow with the cutoff.  This wrapper uses the `B+1`
indexing convention common in the GS layer. -/
theorem prefix_mass_mono {B C : ℕ} (hBC : B ≤ C) :
    (∑ k ∈ Finset.range (B + 1), augmentationLayerRank K G k) ≤
      ∑ k ∈ Finset.range (C + 1), augmentationLayerRank K G k :=
  FPres.nat_mass_mono (b := augmentationLayerRank K G) hBC

/-- Every augmentation prefix mass is at least one (the degree-zero layer). -/
theorem augmentation_prefix_mass (B : ℕ) :
    1 ≤ ∑ k ∈ Finset.range (B + 1), augmentationLayerRank K G k :=
  FPres.prefix_nat_mass (B := B) (by
    simp [augmentation_rank_zero (K := K) (G := G)])

/-- Successor recursion for the GS-style prefix mass. -/
theorem augmentation_mass_succ (B : ℕ) :
    (∑ k ∈ Finset.range ((B + 1) + 1), augmentationLayerRank K G k) =
      (∑ k ∈ Finset.range (B + 1), augmentationLayerRank K G k) +
        augmentationLayerRank K G (B + 1) :=
  FPres.prefix_nat_succ (b := augmentationLayerRank K G) B

/-- Extending the augmentation prefix by one degree cannot decrease its mass. -/
theorem rank_mass_succ (B : ℕ) :
    (∑ k ∈ Finset.range (B + 1), augmentationLayerRank K G k) ≤
      ∑ k ∈ Finset.range ((B + 1) + 1), augmentationLayerRank K G k :=
  FPres.nat_mass_succ (b := augmentationLayerRank K G) B

/-- If the next augmentation layer has positive rank, the next prefix is strictly larger. -/
theorem prefix_mass_pos {B : ℕ}
    (hpos : 0 < augmentationLayerRank K G (B + 1)) :
    (∑ k ∈ Finset.range (B + 1), augmentationLayerRank K G k) <
      ∑ k ∈ Finset.range ((B + 1) + 1), augmentationLayerRank K G k :=
  FPres.mass_succ_pos (b := augmentationLayerRank K G) hpos

/-- One-step augmentation prefix stabilization is equivalent to vanishing of the new layer. -/
theorem rank_mass_self {B : ℕ} :
    ((∑ k ∈ Finset.range ((B + 1) + 1), augmentationLayerRank K G k) =
      ∑ k ∈ Finset.range (B + 1), augmentationLayerRank K G k) ↔
        augmentationLayerRank K G (B + 1) = 0 :=
  FPres.mass_succ_self
    (b := augmentationLayerRank K G) (B := B)

/-- Forward form: a stabilized one-step prefix forces the new augmentation layer rank to vanish. -/
theorem prefix_mass_self {B : ℕ}
    (h : (∑ k ∈ Finset.range ((B + 1) + 1), augmentationLayerRank K G k) =
      ∑ k ∈ Finset.range (B + 1), augmentationLayerRank K G k) :
    augmentationLayerRank K G (B + 1) = 0 :=
  (rank_mass_self (K := K) (G := G) (B := B)).mp h

/-- For finite groups, one-step prefix stabilization is the same as stabilization of the
corresponding successive truncation dimension. -/
theorem mass_self_finrank [Finite G]
    {B : ℕ} :
    ((∑ k ∈ Finset.range ((B + 1) + 1), augmentationLayerRank K G k) =
      ∑ k ∈ Finset.range (B + 1), augmentationLayerRank K G k) ↔
      Module.finrank K (augmentationTruncation K G ((B + 1) + 1)) =
        Module.finrank K (augmentationTruncation K G (B + 1)) := by
  constructor
  · intro h
    have hz : augmentationLayerRank K G (B + 1) = 0 :=
      (rank_mass_self (K := K) (G := G) (B := B)).mp h
    exact (truncation_finrank_self
      (K := K) (G := G) (n := B + 1)).mpr hz
  · intro h
    have hz : augmentationLayerRank K G (B + 1) = 0 :=
      (truncation_finrank_self
        (K := K) (G := G) (n := B + 1)).mp h
    exact (rank_mass_self
      (K := K) (G := G) (B := B)).mpr hz

/-- Reverse orientation of prefix-mass positivity, convenient after rewriting a
truncation dimension to a prefix sum. -/
theorem truncation_pos_prefix [Finite G] (B : ℕ) :
    0 < Module.finrank K (augmentationTruncation K G (B + 1)) :=
  truncation_pos_succ (K := K) (G := G) B

/-- Once `I^(B+1)` vanishes, finite prefix masses through any two bounds at least
`B` agree. -/
theorem rank_mass_bot
    {B M N : ℕ} (hB : augmentationPowerSubmodule K G (B + 1) = ⊥)
    (hM : B ≤ M) (hN : B ≤ N) :
    (∑ k ∈ Finset.range (M + 1), augmentationLayerRank K G k) =
      ∑ k ∈ Finset.range (N + 1), augmentationLayerRank K G k :=
  FPres.sum_support_bound
    (rank_support_bot (K := K) (G := G) hB)
    hM hN

/-- Stabilization of prefix mass at the nilpotence bound. -/
theorem prefix_mass_bot
    {B M : ℕ} (hB : augmentationPowerSubmodule K G (B + 1) = ⊥) (hM : B ≤ M) :
    (∑ k ∈ Finset.range (M + 1), augmentationLayerRank K G k) =
      ∑ k ∈ Finset.range (B + 1), augmentationLayerRank K G k :=
  rank_mass_bot (K := K) (G := G) hB hM
    (le_rfl)


/-- Prefix mass of a truncated augmentation-rank sequence before the cutoff is
unchanged. -/
theorem rank_mass_truncate {M N : ℕ}
    (hMN : M ≤ N) :
    (∑ k ∈ Finset.range (M + 1),
        FPres.truncateSeq (augmentationLayerRank K G) N k) =
      ∑ k ∈ Finset.range (M + 1), augmentationLayerRank K G k := by
  exact FPres.truncate_seq_prefix
    (augmentationLayerRank K G) hMN

/-- Prefix mass of a truncated augmentation-rank sequence after the cutoff is
its prefix mass at the cutoff. -/
theorem prefix_mass_truncate {N M : ℕ}
    (hNM : N ≤ M) :
    (∑ k ∈ Finset.range (M + 1),
        FPres.truncateSeq (augmentationLayerRank K G) N k) =
      ∑ k ∈ Finset.range (N + 1), augmentationLayerRank K G k := by
  exact FPres.sum_truncate_seq
    (augmentationLayerRank K G) hNM

/-- Uniform min-cutoff form for prefix masses of truncated augmentation ranks. -/
theorem prefix_mass_min (M N : ℕ) :
    (∑ k ∈ Finset.range (M + 1),
        FPres.truncateSeq (augmentationLayerRank K G) N k) =
      ∑ k ∈ Finset.range (min M N + 1), augmentationLayerRank K G k := by
  exact FPres.truncate_seq_min
    (augmentationLayerRank K G) M N


/-- For finite groups, the prefix mass of a truncated augmentation-rank sequence
is the dimension of the truncation at the smaller cutoff (with the usual `+1`
conversion between layer prefixes and quotient cutoffs). -/
theorem mass_truncate_min [Finite G]
    (M N : ℕ) :
    (∑ k ∈ Finset.range (M + 1),
        FPres.truncateSeq (augmentationLayerRank K G) N k) =
      Module.finrank K (augmentationTruncation K G (min M N + 1)) := by
  rw [prefix_mass_min (K := K) (G := G) M N]
  exact rank_truncation_finrank
    (K := K) (G := G) (min M N + 1)


/-- Finrank form of the prefix-before-cutoff truncation identity. -/
theorem mass_truncate_finrank
    [Finite G] {M N : ℕ} (hMN : M ≤ N) :
    (∑ k ∈ Finset.range (M + 1),
        FPres.truncateSeq (augmentationLayerRank K G) N k) =
      Module.finrank K (augmentationTruncation K G (M + 1)) := by
  rw [rank_mass_truncate
    (K := K) (G := G) hMN]
  exact rank_truncation_finrank
    (K := K) (G := G) (M + 1)

/-- Finrank form of the prefix-after-cutoff truncation identity. -/
theorem mass_truncate_cutoff
    [Finite G] {N M : ℕ} (hNM : N ≤ M) :
    (∑ k ∈ Finset.range (M + 1),
        FPres.truncateSeq (augmentationLayerRank K G) N k) =
      Module.finrank K (augmentationTruncation K G (N + 1)) := by
  rw [prefix_mass_truncate
    (K := K) (G := G) hNM]
  exact rank_truncation_finrank
    (K := K) (G := G) (N + 1)


/-- Every prefix of a truncated augmentation-rank sequence has positive mass:
the zeroth truncated coefficient is still one. -/
theorem rank_mass_pos (M N : ℕ) :
    0 < ∑ k ∈ Finset.range (M + 1),
      FPres.truncateSeq (augmentationLayerRank K G) N k := by
  classical
  apply FPres.mass_pos_zero (B := M)
  rw [FPres.truncate_apply_le]
  · simp [augmentation_rank_zero (K := K) (G := G)]
  · exact Nat.zero_le N

/-- Every prefix of a truncated augmentation-rank sequence has mass at least one. -/
theorem augmentation_mass_truncate (M N : ℕ) :
    1 ≤ ∑ k ∈ Finset.range (M + 1),
      FPres.truncateSeq (augmentationLayerRank K G) N k :=
  Nat.succ_le_iff.mpr
    (rank_mass_pos (K := K) (G := G) M N)

/-- Truncated augmentation prefix masses are monotone in the prefix cutoff. -/
theorem mass_truncate_mono {M₁ M₂ N : ℕ} (h : M₁ ≤ M₂) :
    (∑ k ∈ Finset.range (M₁ + 1),
      FPres.truncateSeq (augmentationLayerRank K G) N k) ≤
    ∑ k ∈ Finset.range (M₂ + 1),
      FPres.truncateSeq (augmentationLayerRank K G) N k :=
  FPres.nat_mass_mono
    (b := FPres.truncateSeq (augmentationLayerRank K G) N) h

/-- Successor recursion for truncated augmentation prefix masses. -/
theorem prefix_mass_succ (M N : ℕ) :
    (∑ k ∈ Finset.range ((M + 1) + 1),
      FPres.truncateSeq (augmentationLayerRank K G) N k) =
    (∑ k ∈ Finset.range (M + 1),
      FPres.truncateSeq (augmentationLayerRank K G) N k) +
      FPres.truncateSeq (augmentationLayerRank K G) N (M + 1) :=
  FPres.prefix_nat_succ
    (b := FPres.truncateSeq (augmentationLayerRank K G) N) M

/-- Extending a truncated augmentation prefix by one degree cannot decrease it. -/
theorem mass_truncate_succ (M N : ℕ) :
    (∑ k ∈ Finset.range (M + 1),
      FPres.truncateSeq (augmentationLayerRank K G) N k) ≤
    ∑ k ∈ Finset.range ((M + 1) + 1),
      FPres.truncateSeq (augmentationLayerRank K G) N k :=
  FPres.nat_mass_succ
    (b := FPres.truncateSeq (augmentationLayerRank K G) N) M

/-- A positive next truncated coefficient makes the truncated prefix strictly grow. -/
theorem mass_truncate_pos {M N : ℕ}
    (hpos : 0 < FPres.truncateSeq (augmentationLayerRank K G) N (M + 1)) :
    (∑ k ∈ Finset.range (M + 1),
      FPres.truncateSeq (augmentationLayerRank K G) N k) <
    ∑ k ∈ Finset.range ((M + 1) + 1),
      FPres.truncateSeq (augmentationLayerRank K G) N k :=
  FPres.mass_succ_pos
    (b := FPres.truncateSeq (augmentationLayerRank K G) N) hpos

/-- One-step stabilization of a truncated augmentation prefix is equivalent to vanishing
of the next truncated coefficient. -/
theorem mass_truncate_self {M N : ℕ} :
    ((∑ k ∈ Finset.range ((M + 1) + 1),
      FPres.truncateSeq (augmentationLayerRank K G) N k) =
      ∑ k ∈ Finset.range (M + 1),
        FPres.truncateSeq (augmentationLayerRank K G) N k) ↔
      FPres.truncateSeq (augmentationLayerRank K G) N (M + 1) = 0 :=
  FPres.mass_succ_self
    (b := FPres.truncateSeq (augmentationLayerRank K G) N) (B := M)

/-- A stabilized truncated augmentation prefix forces the next truncated coefficient to vanish. -/
theorem truncate_mass_self {M N : ℕ}
    (h : (∑ k ∈ Finset.range ((M + 1) + 1),
      FPres.truncateSeq (augmentationLayerRank K G) N k) =
      ∑ k ∈ Finset.range (M + 1),
        FPres.truncateSeq (augmentationLayerRank K G) N k) :
    FPres.truncateSeq (augmentationLayerRank K G) N (M + 1) = 0 :=
  (mass_truncate_self
    (K := K) (G := G) (M := M) (N := N)).mp h

/-- More general support bound from nilpotence at stage `N`: the rank sequence is
supported in degrees `< N` (written as bound `N-1`). -/
theorem support_bound_bot {N : ℕ}
    (hNpos : 0 < N) (hN : augmentationPowerSubmodule K G N = ⊥) :
    FPres.SSBound (augmentationLayerRank K G) (N - 1) := by
  intro n hn
  have hNn : N ≤ n := by omega
  exact layer_rank_bot (K := K) (G := G) hN hNn

end
end GroupAlgebra
end Towers

namespace Towers
namespace FPres

noncomputable section

variable {p : ℕ} (FP : FPres p)
variable (K G : Type*) [Field K] [_root_.Group G]

/-- Package a nilpotent augmentation-layer rank sequence as finite GS coefficient data,
once the GS inequalities themselves are supplied.  This is the bookkeeping object that
future Fox/Jennings bridges should construct. -/
def gs_sequence_nilpotent
    [Fintype FP.toPresentation.Relator] {B : ℕ}
    (hB : GroupAlgebra.augmentationPowerSubmodule K G (B + 1) = ⊥)
    (hineq : FP.gsCoefficientInequalities (GroupAlgebra.augmentationLayerRank K G)) :
    FiniteGSSequence (p := p) FP where
  coeff := GroupAlgebra.augmentationLayerRank K G
  bound := B
  support := GroupAlgebra.rank_support_bot
    (K := K) (G := G) hB
  coeff_zero_pos := by
    simp [GroupAlgebra.augmentation_rank_zero (K := K) (G := G)]
  inequalities := hineq

/-- Nonempty packaging form of `gs_sequence_nilpotent`. -/
theorem nonempty_sequence_nilpotent
    [Fintype FP.toPresentation.Relator] {B : ℕ}
    (hB : GroupAlgebra.augmentationPowerSubmodule K G (B + 1) = ⊥)
    (hineq : FP.gsCoefficientInequalities (GroupAlgebra.augmentationLayerRank K G)) :
    Nonempty (FiniteGSSequence (p := p) FP) :=
  ⟨FP.gs_sequence_nilpotent (K := K) (G := G) hB hineq⟩

/-- Jennings-Fox bridge from a filtered presentation with certified relator
depths at least two to the filtered GS coefficient inequalities for the cumulative
augmentation-layer Hilbert sequence of its presented group.

A `FPres` stores certified Zassenhaus-depth lower bounds; the
additional hypothesis says that no relator has a degree-zero or degree-one part.

For a filtered, rather than graded, presentation the classical Vinberg form of
the Golod--Shafarevich inequality applies to `Hilb_A(t) / (1 - t)`. Its
coefficients are the prefix sums of the augmentation-layer ranks below. -/
theorem gs_jennings_fox
    [Fact p.Prime] [Finite FP.Gen] [Fintype FP.toPresentation.Relator]
    (hsilent : FP.depths.degreeOneSilent) :
    FP.gsCoefficientInequalities
      (fun n =>
        ∑ k ∈ Finset.range (n + 1),
          GroupAlgebra.augmentationLayerRank (ZMod p) FP.Group k) := by
  letI := Fintype.ofFinite FP.Gen
  classical
  let d := Fintype.card FP.Gen
  let r := Fintype.card FP.toPresentation.Relator
  let egen : Fin d ≃ FP.Gen := (Fintype.equivFin FP.Gen).symm
  let erel : Fin r ≃ FP.toPresentation.Relator :=
    (Fintype.equivFin FP.toPresentation.Relator).symm
  let eg : FreeGroup (Fin d) ≃* FP.Free := FreeGroup.freeGroupCongr egen
  let rels : Fin r → FreeGroup (Fin d) := fun i => eg.symm (erel i : FP.Free)
  let depth : Fin r → ℕ := fun i => FP.relatorDepth (erel i)
  have hrange : eg '' Set.range rels = FP.toPresentation.rels := by
    ext x
    constructor
    · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
      simp [rels]
    · intro hx
      refine ⟨eg.symm x, ?_, by simp⟩
      exact ⟨erel.symm ⟨x, hx⟩, by simp [rels]⟩
  have hrange' :
      FreeGroup.freeGroupCongr egen '' Set.range rels =
        FP.toPresentation.rels := by
    simpa [eg] using hrange
  let eGroup : PresentedGroup (Set.range rels) ≃* FP.Group := by
    change PresentedGroup (Set.range rels) ≃* PresentedGroup FP.toPresentation.rels
    exact cast
      (congrArg
        (fun s : Set (FreeGroup FP.Gen) =>
          PresentedGroup (Set.range rels) ≃* PresentedGroup s)
        hrange')
      (PresentedGroup.equivPresentedGroup (Set.range rels) egen)
  have hdepthZ :
      ∀ i, GroupAlgebra.zassenhausDepthLeast
        p (FreeGroup (Fin d)) (rels i) (depth i) := by
    intro i
    simpa [rels, depth] using
      (GroupAlgebra.depth_least_symm
        (p := p) (G := FreeGroup (Fin d)) eg
        (FP.relatorDepth (erel i)) (erel i : FP.Free)).2
          (FP.relator_mem_depth (erel i))
  have hdepth :
      ∀ i,
        (MonoidAlgebra.of (ZMod p) (FreeGroup (Fin d)) (rels i) - 1 :
          MonoidAlgebra (ZMod p) (FreeGroup (Fin d))) ∈
            (GroupAlgebra.augmentationIdeal
              (ZMod p) (FreeGroup (Fin d))) ^ depth i := by
    intro i
    exact hdepthZ i
  have hdepth2 : ∀ i, 2 ≤ depth i := by
    intro i
    exact hsilent (erel i)
  let b : ℕ → ℕ := fun n =>
    ∑ k ∈ Finset.range (n + 1),
      GroupAlgebra.augmentationLayerRank (ZMod p) FP.Group k
  have hb (n : ℕ) :
      b n =
        Module.finrank (ZMod p)
          (TBluepr.presentedAugmentationTruncation
            (p := p) rels (n + 1)) := by
    dsimp [b]
    calc
      (∑ k ∈ Finset.range (n + 1),
          GroupAlgebra.augmentationLayerRank (ZMod p) FP.Group k) =
          ∑ k ∈ Finset.range (n + 1),
            GroupAlgebra.augmentationLayerRank
              (ZMod p) (PresentedGroup (Set.range rels)) k := by
            apply Finset.sum_congr rfl
            intro k _hk
            exact (GroupAlgebra.augmentation_rank_equiv
              (K := ZMod p) (G := PresentedGroup (Set.range rels))
              eGroup k).symm
      _ = Module.finrank (ZMod p)
          (TBluepr.presentedAugmentationTruncation
            (p := p) rels (n + 1)) :=
        TBluepr.rank_presented_truncation
          (p := p) rels (n + 1)
  change FP.gsCoefficientInequalities b
  intro m
  cases m with
  | zero =>
      simp [gsCoefficientInequality, generatorShiftContribution]
  | succ n =>
      rw [FP.gs_inequality_succ]
      have hconv :
          FP.relatorDepthConvolution b (n + 1) =
            ∑ i, if depth i ≤ n + 1 then
              Module.finrank (ZMod p)
                (TBluepr.presentedAugmentationTruncation
                  (p := p) rels (n + 1 - depth i + 1))
            else 0 := by
        unfold relatorDepthConvolution relatorWeightedSum
        calc
          (∑ rr : FP.toPresentation.Relator,
              if FP.depths.depth rr ≤ n + 1 then
                b (n + 1 - FP.depths.depth rr)
              else 0) =
              ∑ i : Fin r, if FP.depths.depth (erel i) ≤ n + 1 then
                b (n + 1 - FP.depths.depth (erel i))
              else 0 := by
                symm
                apply Fintype.sum_equiv erel
                intro i
                rfl
          _ = ∑ i, if depth i ≤ n + 1 then
              Module.finrank (ZMod p)
                (TBluepr.presentedAugmentationTruncation
                  (p := p) rels (n + 1 - depth i + 1))
            else 0 := by
              apply Finset.sum_congr rfl
              intro i _hi
              dsimp [depth, relatorDepth]
              split_ifs
              · rw [hb]
                rfl
              · rfl
      rw [hb n, hb (n + 1), hconv]
      rw [show FP.generatorCount = d by
        simp [generatorCount, d, Nat.card_eq_fintype_card]]
      exact
        TBluepr.presented_gs_succ
          (p := p) rels depth hdepth hdepth2 n

/-- Any rational certificate already rules out the GS inequalities for a finite
truncation of the augmentation-layer rank sequence: the zeroth layer has rank one. -/
theorem inequalities_truncate_certificate
    [Fintype FP.toPresentation.Relator] (C : FP.RGCert) (B : ℕ) :
    ¬ FP.gsCoefficientInequalities
      (truncateSeq (GroupAlgebra.augmentationLayerRank K G) B) := by
  apply FP.inequalities_seq_certificate C
  simp [GroupAlgebra.augmentation_rank_zero (K := K) (G := G)]

/-- Depth-two quadratic obstruction for a finite truncation of augmentation-layer ranks. -/
theorem inequalities_truncate_quadratic
    [Fintype FP.toPresentation.Relator] {B d r : ℕ}
    (hd2 : 2 < d)
    (hgen : d ≤ FP.generatorCount)
    (hD : ∀ x : FP.toPresentation.Relator, 2 ≤ FP.depths.depth x)
    (hcount : Nat.card FP.toPresentation.Relator ≤ r)
    (hquad : 4 * r < d * d) :
    ¬ FP.gsCoefficientInequalities
      (truncateSeq (GroupAlgebra.augmentationLayerRank K G) B) := by
  apply FP.inequalities_truncate_seq
    (d := d) (r := r)
  · simp [GroupAlgebra.augmentation_rank_zero (K := K) (G := G)]
  · exact hd2
  · exact hgen
  · exact hD
  · exact hcount
  · exact hquad

/-- Explicit failing degree for a truncated augmentation-layer rank sequence under a certificate. -/
theorem failure_truncate_certificate
    [Fintype FP.toPresentation.Relator] (C : FP.RGCert) (B : ℕ) :
    ∃ n ∈ Finset.range (B + FP.maxRelatorDepth + 2),
      ¬ FP.gsCoefficientInequality
        (truncateSeq (GroupAlgebra.augmentationLayerRank K G) B) n := by
  apply FP.failure_seq_certificate C
  simp [GroupAlgebra.augmentation_rank_zero (K := K) (G := G)]

/-- Explicit failing degree for the depth-two quadratic truncated augmentation obstruction. -/
theorem failure_truncate_quadratic
    [Fintype FP.toPresentation.Relator] {B d r : ℕ}
    (hd2 : 2 < d)
    (hgen : d ≤ FP.generatorCount)
    (hD : ∀ x : FP.toPresentation.Relator, 2 ≤ FP.depths.depth x)
    (hcount : Nat.card FP.toPresentation.Relator ≤ r)
    (hquad : 4 * r < d * d) :
    ∃ n ∈ Finset.range (B + FP.maxRelatorDepth + 2),
      ¬ FP.gsCoefficientInequality
        (truncateSeq (GroupAlgebra.augmentationLayerRank K G) B) n := by
  let C := RGCert.depth_two_quadraticbounda FP d r hd2 hgen hD hcount hquad
  exact FP.failure_truncate_certificate (K := K) (G := G) C B

/-- Depth-two quadratic numerical obstruction, specialized to a nilpotent augmentation
Hilbert rank sequence via the finite-sequence package. -/
theorem gs_inequalities_nilpotent
    [Fintype FP.toPresentation.Relator] {B d r : ℕ}
    (hB : GroupAlgebra.augmentationPowerSubmodule K G (B + 1) = ⊥)
    (hd2 : 2 < d)
    (hgen : d ≤ FP.generatorCount)
    (hD : ∀ x : FP.toPresentation.Relator, 2 ≤ FP.depths.depth x)
    (hcount : Nat.card FP.toPresentation.Relator ≤ r)
    (hquad : 4 * r < d * d) :
    ¬ FP.gsCoefficientInequalities (GroupAlgebra.augmentationLayerRank K G) := by
  intro hineq
  have hno := FP.no_sequence_bound
    (d := d) (r := r) hd2 hgen hD hcount hquad
  exact hno (FP.nonempty_sequence_nilpotent
    (K := K) (G := G) hB hineq)

/-- Any finite truncation of the augmentation-layer rank sequence is finite GS data,
once the truncated inequalities are supplied. -/
def sequence_truncate_rank
    [Fintype FP.toPresentation.Relator] (B : ℕ)
    (hineq : FP.gsCoefficientInequalities
      (truncateSeq (GroupAlgebra.augmentationLayerRank K G) B)) :
    FiniteGSSequence (p := p) FP :=
  FP.gs_sequence_truncate (b := GroupAlgebra.augmentationLayerRank K G) B
    (by simp [GroupAlgebra.augmentation_rank_zero (K := K) (G := G)]) hineq

/-- Nonempty packaging form for truncated augmentation-layer ranks. -/
theorem nonempty_truncate_rank
    [Fintype FP.toPresentation.Relator] (B : ℕ)
    (hineq : FP.gsCoefficientInequalities
      (truncateSeq (GroupAlgebra.augmentationLayerRank K G) B)) :
    Nonempty (FiniteGSSequence (p := p) FP) :=
  ⟨FP.sequence_truncate_rank (K := K) (G := G) B hineq⟩

/-- Explicit-argument variant of the certificate obstruction for inequalities on a
finite truncation of augmentation ranks. -/
theorem inequalities_truncate_explicit
    [Fintype FP.toPresentation.Relator] (C : FP.RGCert) (B : ℕ) :
    ¬ FP.gsCoefficientInequalities
      (truncateSeq (GroupAlgebra.augmentationLayerRank K G) B) :=
  FP.inequalities_seq_certificate C
    (b := GroupAlgebra.augmentationLayerRank K G) (N := B)
    (by simp [GroupAlgebra.augmentation_rank_zero (K := K) (G := G)])

/-- A rational GS certificate rules out GS coefficient inequalities for an
augmentation-layer rank sequence once a nilpotence bound supplies finite support
and the finite prefix has positive mass.  This is the abstract assembly point
before proving the actual Fox/Jennings coefficient inequalities. -/
theorem inequalities_certificate_nilpotent
    [Fintype FP.toPresentation.Relator] (C : FP.RGCert) {B : ℕ}
    (hB : GroupAlgebra.augmentationPowerSubmodule K G (B + 1) = ⊥)
    (hmass : 0 < ∑ k ∈ Finset.range (B + 1),
      GroupAlgebra.augmentationLayerRank K G k) :
    ¬ FP.gsCoefficientInequalities (GroupAlgebra.augmentationLayerRank K G) := by
  have hsupp := GroupAlgebra.rank_support_bot
    (K := K) (G := G) hB
  exact FP.inequalities_certificate_mass C hsupp hmass

/-- Under nilpotence, truncating the augmentation-layer rank sequence at the
nilpotence bound does not change any GS balance. -/
theorem gs_balance_nilpotent
    [Fintype FP.toPresentation.Relator] {B n : ℕ}
    (hB : GroupAlgebra.augmentationPowerSubmodule K G (B + 1) = ⊥) :
    FP.gsCoefficientBalance
        (truncateSeq (GroupAlgebra.augmentationLayerRank K G) B) n =
      FP.gsCoefficientBalance (GroupAlgebra.augmentationLayerRank K G) n := by
  rw [GroupAlgebra.truncate_succ_bot
    (K := K) (G := G) hB]

/-- Under nilpotence, truncating at any later cutoff does not change GS balances. -/
theorem balance_truncate_nilpotent
    [Fintype FP.toPresentation.Relator] {B M n : ℕ}
    (hB : GroupAlgebra.augmentationPowerSubmodule K G (B + 1) = ⊥) (hBM : B ≤ M) :
    FP.gsCoefficientBalance
        (truncateSeq (GroupAlgebra.augmentationLayerRank K G) M) n =
      FP.gsCoefficientBalance (GroupAlgebra.augmentationLayerRank K G) n := by
  rw [GroupAlgebra.truncate_rank_bot
    (K := K) (G := G) hB hBM]

/-- Under nilpotence, truncating the augmentation-layer rank sequence at the
nilpotence bound does not change any individual GS inequality. -/
theorem gs_inequality_truncate
    [Fintype FP.toPresentation.Relator] {B n : ℕ}
    (hB : GroupAlgebra.augmentationPowerSubmodule K G (B + 1) = ⊥) :
    FP.gsCoefficientInequality
        (truncateSeq (GroupAlgebra.augmentationLayerRank K G) B) n ↔
      FP.gsCoefficientInequality (GroupAlgebra.augmentationLayerRank K G) n := by
  rw [FP.inequality_balance_nonneg,
    FP.inequality_balance_nonneg,
    FP.gs_balance_nilpotent
      (K := K) (G := G) hB]

/-- Under nilpotence, truncating at the bound preserves the full GS-inequality predicate. -/
theorem gs_inequalities_truncate
    [Fintype FP.toPresentation.Relator] {B : ℕ}
    (hB : GroupAlgebra.augmentationPowerSubmodule K G (B + 1) = ⊥) :
    FP.gsCoefficientInequalities
        (truncateSeq (GroupAlgebra.augmentationLayerRank K G) B) ↔
      FP.gsCoefficientInequalities (GroupAlgebra.augmentationLayerRank K G) := by
  constructor
  · intro h n
    exact (FP.gs_inequality_truncate
      (K := K) (G := G) (B := B) (n := n) hB).1 (h n)
  · intro h n
    exact (FP.gs_inequality_truncate
      (K := K) (G := G) (B := B) (n := n) hB).2 (h n)

/-- Under nilpotence, truncating at any later cutoff preserves each GS inequality. -/
theorem inequality_truncate_nilpotent
    [Fintype FP.toPresentation.Relator] {B M n : ℕ}
    (hB : GroupAlgebra.augmentationPowerSubmodule K G (B + 1) = ⊥) (hBM : B ≤ M) :
    FP.gsCoefficientInequality
        (truncateSeq (GroupAlgebra.augmentationLayerRank K G) M) n ↔
      FP.gsCoefficientInequality (GroupAlgebra.augmentationLayerRank K G) n := by
  rw [FP.inequality_balance_nonneg,
    FP.inequality_balance_nonneg,
    FP.balance_truncate_nilpotent
      (K := K) (G := G) hB hBM]

/-- Under nilpotence, truncating at any later cutoff preserves the full GS predicate. -/
theorem inequalities_truncate_nilpotent
    [Fintype FP.toPresentation.Relator] {B M : ℕ}
    (hB : GroupAlgebra.augmentationPowerSubmodule K G (B + 1) = ⊥) (hBM : B ≤ M) :
    FP.gsCoefficientInequalities
        (truncateSeq (GroupAlgebra.augmentationLayerRank K G) M) ↔
      FP.gsCoefficientInequalities (GroupAlgebra.augmentationLayerRank K G) := by
  exact FP.gs_inequalities_seq
    (GroupAlgebra.rank_support_bot
      (K := K) (G := G) hB) hBM

/-- Certificate wrapper using positivity of the corresponding truncation dimension
instead of spelling the prefix mass explicitly. -/
theorem inequalities_certificate_pos
    [Fintype FP.toPresentation.Relator] [Finite G] (C : FP.RGCert) {B : ℕ}
    (hB : GroupAlgebra.augmentationPowerSubmodule K G (B + 1) = ⊥)
    (hpos : 0 < Module.finrank K (GroupAlgebra.augmentationTruncation K G (B + 1))) :
    ¬ FP.gsCoefficientInequalities (GroupAlgebra.augmentationLayerRank K G) := by
  apply FP.inequalities_certificate_nilpotent
    (K := K) (G := G) C hB
  rw [GroupAlgebra.mass_truncation_finrank (K := K) (G := G) B]
  exact hpos

/-- Finite-group version of the truncation-positivity certificate wrapper; the
positivity hypothesis is automatic for any positive truncation cutoff. -/
theorem inequalities_certificate_auto
    [Fintype FP.toPresentation.Relator] [Finite G] (C : FP.RGCert) {B : ℕ}
    (hB : GroupAlgebra.augmentationPowerSubmodule K G (B + 1) = ⊥) :
    ¬ FP.gsCoefficientInequalities (GroupAlgebra.augmentationLayerRank K G) := by
  exact
    FP.inequalities_certificate_pos
    (K := K) (G := G) C hB
    (GroupAlgebra.truncation_pos_succ (K := K) (G := G) B)

/-- Same assembly wrapper, using positivity of the zeroth augmentation-layer rank
instead of an explicit finite-prefix mass proof. -/
theorem inequalities_nilpotent_pos
    [Fintype FP.toPresentation.Relator] (C : FP.RGCert) {B : ℕ}
    (hB : GroupAlgebra.augmentationPowerSubmodule K G (B + 1) = ⊥)
    (h0 : 0 < GroupAlgebra.augmentationLayerRank K G 0) :
    ¬ FP.gsCoefficientInequalities (GroupAlgebra.augmentationLayerRank K G) := by
  apply FP.inequalities_certificate_nilpotent
    (K := K) (G := G) C hB
  exact mass_pos_zero (b := GroupAlgebra.augmentationLayerRank K G) (B := B) h0

/-- Bounded failing-degree version for truncated augmentation-layer rank sequences. -/
theorem failure_certificate_pos
    [Fintype FP.toPresentation.Relator] (C : FP.RGCert) {B : ℕ}
    (_hB : GroupAlgebra.augmentationPowerSubmodule K G (B + 1) = ⊥)
    (h0 : 0 < GroupAlgebra.augmentationLayerRank K G 0) :
    ∃ n ∈ Finset.range (B + FP.maxRelatorDepth + 2),
      ¬ FP.gsCoefficientInequality
        (truncateSeq (GroupAlgebra.augmentationLayerRank K G) B) n := by
  have hmass : 0 < ∑ k ∈ Finset.range (B + 1),
      GroupAlgebra.augmentationLayerRank K G k :=
    mass_pos_zero (b := GroupAlgebra.augmentationLayerRank K G) (B := B) h0
  exact FP.failure_certificate_mass C hmass

/-- Bounded-failure wrapper using positivity of the corresponding truncation dimension. -/
theorem failure_truncate_pos
    [Fintype FP.toPresentation.Relator] [Finite G] (C : FP.RGCert) {B : ℕ}
    (_hB : GroupAlgebra.augmentationPowerSubmodule K G (B + 1) = ⊥)
    (hpos : 0 < Module.finrank K (GroupAlgebra.augmentationTruncation K G (B + 1))) :
    ∃ n ∈ Finset.range (B + FP.maxRelatorDepth + 2),
      ¬ FP.gsCoefficientInequality
        (truncateSeq (GroupAlgebra.augmentationLayerRank K G) B) n := by
  have hmass : 0 < ∑ k ∈ Finset.range (B + 1),
      GroupAlgebra.augmentationLayerRank K G k := by
    rw [GroupAlgebra.mass_truncation_finrank (K := K) (G := G) B]
    exact hpos
  exact FP.failure_certificate_mass C hmass

/-- Finite-group bounded-failure wrapper with automatic truncation-dimension positivity. -/
theorem failure_certificate_auto
    [Fintype FP.toPresentation.Relator] [Finite G] (C : FP.RGCert) {B : ℕ}
    (hB : GroupAlgebra.augmentationPowerSubmodule K G (B + 1) = ⊥) :
    ∃ n ∈ Finset.range (B + FP.maxRelatorDepth + 2),
      ¬ FP.gsCoefficientInequality
        (truncateSeq (GroupAlgebra.augmentationLayerRank K G) B) n := by
  exact FP.failure_truncate_pos
    (K := K) (G := G) C hB
    (GroupAlgebra.truncation_pos_succ (K := K) (G := G) B)

/-- `≤`-indexed finite-group bounded-failure wrapper with automatic positivity. -/
theorem failure_truncate_auto
    [Fintype FP.toPresentation.Relator] [Finite G] (C : FP.RGCert) {B : ℕ}
    (hB : GroupAlgebra.augmentationPowerSubmodule K G (B + 1) = ⊥) :
    ∃ n, n ≤ B + FP.maxRelatorDepth + 1 ∧
      ¬ FP.gsCoefficientInequality
        (truncateSeq (GroupAlgebra.augmentationLayerRank K G) B) n := by
  rcases FP.failure_certificate_auto
    (K := K) (G := G) C hB with ⟨n, hn, hfail⟩
  refine ⟨n, ?_, hfail⟩
  have hlt : n < B + FP.maxRelatorDepth + 2 := Finset.mem_range.mp hn
  omega

/-- Fully normalized nilpotent augmentation-layer wrapper: the zeroth layer has
rank one automa, so no separate positivity hypothesis is needed. -/
theorem inequalities_certificate_normalized
    [Fintype FP.toPresentation.Relator] (C : FP.RGCert) {B : ℕ}
    (hB : GroupAlgebra.augmentationPowerSubmodule K G (B + 1) = ⊥) :
    ¬ FP.gsCoefficientInequalities (GroupAlgebra.augmentationLayerRank K G) := by
  apply FP.inequalities_nilpotent_pos
    (K := K) (G := G) C hB
  simp [GroupAlgebra.augmentation_rank_zero (K := K) (G := G)]

/-- Normalized bounded-failure wrapper for truncated augmentation-layer ranks. -/
theorem failure_certificate_normalized
    [Fintype FP.toPresentation.Relator] (C : FP.RGCert) {B : ℕ}
    (hB : GroupAlgebra.augmentationPowerSubmodule K G (B + 1) = ⊥) :
    ∃ n ∈ Finset.range (B + FP.maxRelatorDepth + 2),
      ¬ FP.gsCoefficientInequality
        (truncateSeq (GroupAlgebra.augmentationLayerRank K G) B) n := by
  apply FP.failure_certificate_pos
    (K := K) (G := G) C hB
  simp [GroupAlgebra.augmentation_rank_zero (K := K) (G := G)]

/-- `≤`-indexed form of the normalized bounded-failure wrapper. -/
theorem failure_truncate_normalized
    [Fintype FP.toPresentation.Relator] (C : FP.RGCert) {B : ℕ}
    (hB : GroupAlgebra.augmentationPowerSubmodule K G (B + 1) = ⊥) :
    ∃ n, n ≤ B + FP.maxRelatorDepth + 1 ∧
      ¬ FP.gsCoefficientInequality
        (truncateSeq (GroupAlgebra.augmentationLayerRank K G) B) n := by
  rcases FP.failure_certificate_normalized
    (K := K) (G := G) C hB with ⟨n, hn, hfail⟩
  refine ⟨n, ?_, hfail⟩
  have hlt : n < B + FP.maxRelatorDepth + 2 := Finset.mem_range.mp hn
  omega

/-- Package a nilpotent augmentation-layer Hilbert sequence as a finite GS
sequence, once the (future Fox/Jennings) coefficient inequalities are supplied.
This is the explicit seam between the structural theorem and the certificate
obstruction layer. -/
def gsSequenceNilpotent
    [Fintype FP.toPresentation.Relator] {B : ℕ}
    (hB : GroupAlgebra.augmentationPowerSubmodule K G (B + 1) = ⊥)
    (hineq : FP.gsCoefficientInequalities (GroupAlgebra.augmentationLayerRank K G)) :
    FP.FiniteGSSequence :=
  { coeff := GroupAlgebra.augmentationLayerRank K G
    bound := B
    support := GroupAlgebra.rank_support_bot
      (K := K) (G := G) hB
    coeff_zero_pos := by
      simp [GroupAlgebra.augmentation_rank_zero (K := K) (G := G)]
    inequalities := hineq }

/-- Contrapositive seam: under a rational certificate and nilpotence, the future
Fox/Jennings coefficient inequalities cannot hold for the augmentation-layer
Hilbert sequence.  This is phrased via `FiniteGSSequence` for consumers that use
that compact package. -/
theorem sequence_certificate_nilpotent
    [Fintype FP.toPresentation.Relator] (C : FP.RGCert) {B : ℕ}
    (hB : GroupAlgebra.augmentationPowerSubmodule K G (B + 1) = ⊥) :
    ¬ FP.gsCoefficientInequalities (GroupAlgebra.augmentationLayerRank K G) := by
  intro hineq
  have S : Nonempty FP.FiniteGSSequence :=
    ⟨FP.gsSequenceNilpotent (K := K) (G := G) hB hineq⟩
  exact (FP.no_gs_certificate C) S

/-- Under a nilpotence bound, checking the augmentation-layer GS inequalities is
equivalent to checking only the explicit finite interval ending at
`B + maxRelatorDepth + 1`.  This is the `≤`-indexed finite-check form. -/
theorem gs_forall_nilpotent
    [Fintype FP.toPresentation.Relator] {B : ℕ}
    (hB : GroupAlgebra.augmentationPowerSubmodule K G (B + 1) = ⊥) :
    FP.gsCoefficientInequalities (GroupAlgebra.augmentationLayerRank K G) ↔
      ∀ n, n ≤ B + FP.maxRelatorDepth + 1 →
        FP.gsCoefficientInequality (GroupAlgebra.augmentationLayerRank K G) n := by
  exact FP.gs_inequalities_forall
    (GroupAlgebra.rank_support_bot
      (K := K) (G := G) hB)

/-- Finite-range version of the nilpotent augmentation-layer finite-check
criterion. -/
theorem inequalities_forall_nilpotent
    [Fintype FP.toPresentation.Relator] {B : ℕ}
    (hB : GroupAlgebra.augmentationPowerSubmodule K G (B + 1) = ⊥) :
    FP.gsCoefficientInequalities (GroupAlgebra.augmentationLayerRank K G) ↔
      ∀ n ∈ Finset.range (B + FP.maxRelatorDepth + 2),
        FP.gsCoefficientInequality (GroupAlgebra.augmentationLayerRank K G) n := by
  exact FP.gs_inequalities_bound
    (GroupAlgebra.rank_support_bot
      (K := K) (G := G) hB)

/-- Build the finite GS-sequence package from the `≤`-indexed finite check forced
by a nilpotence bound. -/
def sequenceNilpotentCheck
    [Fintype FP.toPresentation.Relator] {B : ℕ}
    (hB : GroupAlgebra.augmentationPowerSubmodule K G (B + 1) = ⊥)
    (hcheck : ∀ n, n ≤ B + FP.maxRelatorDepth + 1 →
      FP.gsCoefficientInequality (GroupAlgebra.augmentationLayerRank K G) n) :
    FP.FiniteGSSequence :=
  FP.gsSequenceNilpotent (K := K) (G := G) hB
    ((FP.gs_forall_nilpotent
      (K := K) (G := G) hB).2 hcheck)

/-- Build the finite GS-sequence package from only the finite range of
augmentation-layer inequalities forced by a nilpotence bound. -/
def gsNilpotentCheck
    [Fintype FP.toPresentation.Relator] {B : ℕ}
    (hB : GroupAlgebra.augmentationPowerSubmodule K G (B + 1) = ⊥)
    (hcheck : ∀ n ∈ Finset.range (B + FP.maxRelatorDepth + 2),
      FP.gsCoefficientInequality (GroupAlgebra.augmentationLayerRank K G) n) :
    FP.FiniteGSSequence :=
  FP.gsSequenceNilpotent (K := K) (G := G) hB
    ((FP.inequalities_forall_nilpotent
      (K := K) (G := G) hB).2 hcheck)

/-- Certificate obstruction, phrased directly as failure of the `≤`-indexed
finite check under a nilpotence bound. -/
theorem not_certificate_nilpotent
    [Fintype FP.toPresentation.Relator] (C : FP.RGCert) {B : ℕ}
    (hB : GroupAlgebra.augmentationPowerSubmodule K G (B + 1) = ⊥) :
    ¬ (∀ n, n ≤ B + FP.maxRelatorDepth + 1 →
      FP.gsCoefficientInequality (GroupAlgebra.augmentationLayerRank K G) n) := by
  intro hcheck
  have hineq : FP.gsCoefficientInequalities (GroupAlgebra.augmentationLayerRank K G) :=
    (FP.gs_forall_nilpotent
      (K := K) (G := G) hB).2 hcheck
  exact FP.sequence_certificate_nilpotent
    (K := K) (G := G) C hB hineq

/-- Certificate obstruction, phrased directly as failure of the finite range of
augmentation-layer inequalities under a nilpotence bound. -/
theorem forall_certificate_nilpotent
    [Fintype FP.toPresentation.Relator] (C : FP.RGCert) {B : ℕ}
    (hB : GroupAlgebra.augmentationPowerSubmodule K G (B + 1) = ⊥) :
    ¬ (∀ n ∈ Finset.range (B + FP.maxRelatorDepth + 2),
      FP.gsCoefficientInequality (GroupAlgebra.augmentationLayerRank K G) n) := by
  intro hcheck
  have hineq : FP.gsCoefficientInequalities (GroupAlgebra.augmentationLayerRank K G) :=
    (FP.inequalities_forall_nilpotent
      (K := K) (G := G) hB).2 hcheck
  exact FP.sequence_certificate_nilpotent
    (K := K) (G := G) C hB hineq

/-- Explicit failing degree form of the finite-range certificate obstruction for
nilpotent augmentation-layer ranks. -/
theorem inequality_certificate_nilpotent
    [Fintype FP.toPresentation.Relator] (C : FP.RGCert) {B : ℕ}
    (hB : GroupAlgebra.augmentationPowerSubmodule K G (B + 1) = ⊥) :
    ∃ n ∈ Finset.range (B + FP.maxRelatorDepth + 2),
      ¬ FP.gsCoefficientInequality (GroupAlgebra.augmentationLayerRank K G) n := by
  classical
  have hnot := FP.forall_certificate_nilpotent
    (K := K) (G := G) C hB
  by_contra hnone
  apply hnot
  intro n hn
  by_contra hnineq
  exact hnone ⟨n, hn, hnineq⟩

/-- `≤`-indexed explicit failing-degree form of the same obstruction. -/
theorem not_inequality_nilpotent
    [Fintype FP.toPresentation.Relator] (C : FP.RGCert) {B : ℕ}
    (hB : GroupAlgebra.augmentationPowerSubmodule K G (B + 1) = ⊥) :
    ∃ n, n ≤ B + FP.maxRelatorDepth + 1 ∧
      ¬ FP.gsCoefficientInequality (GroupAlgebra.augmentationLayerRank K G) n := by
  classical
  rcases
    FP.inequality_certificate_nilpotent
    (K := K) (G := G) C hB with ⟨n, hnmem, hnfail⟩
  refine ⟨n, ?_, hnfail⟩
  have hnlt : n < B + FP.maxRelatorDepth + 2 := Finset.mem_range.mp hnmem
  omega




/-- Degree-one-silent alias for the depth-two quadratic nilpotent obstruction on
augmentation-layer GS inequalities. -/
theorem inequalities_silent_nilpotent
    [Fintype FP.toPresentation.Relator] {B d r : ℕ}
    (hB : GroupAlgebra.augmentationPowerSubmodule K G (B + 1) = ⊥)
    (hd2 : 2 < d)
    (hgen : d ≤ FP.generatorCount)
    (hsilent : FP.depths.degreeOneSilent)
    (hcount : Nat.card FP.toPresentation.Relator ≤ r)
    (hquad : 4 * r < d * d) :
    ¬ FP.gsCoefficientInequalities (GroupAlgebra.augmentationLayerRank K G) := by
  exact FP.gs_inequalities_nilpotent
    (K := K) (G := G) hB hd2 hgen hsilent hcount hquad

/-! The next wrappers specialize the preceding certificate-form nilpotent
obstructions to the classical depth-two quadratic numerical criterion.  They
are deliberately phrased in the finite-check and explicit-failing-degree forms
used by downstream nilpotence arguments, avoiding repeated construction of the
rational certificate at call sites. -/

/-- Under the depth-two quadratic hypothesis and a nilpotence bound, the finite
range of augmentation-layer GS inequalities cannot all hold. -/
theorem not_forall_nilpotent
    [Fintype FP.toPresentation.Relator] {B d r : ℕ}
    (hB : GroupAlgebra.augmentationPowerSubmodule K G (B + 1) = ⊥)
    (hd2 : 2 < d)
    (hgen : d ≤ FP.generatorCount)
    (hD : ∀ x : FP.toPresentation.Relator, 2 ≤ FP.depths.depth x)
    (hcount : Nat.card FP.toPresentation.Relator ≤ r)
    (hquad : 4 * r < d * d) :
    ¬ (∀ n ∈ Finset.range (B + FP.maxRelatorDepth + 2),
      FP.gsCoefficientInequality (GroupAlgebra.augmentationLayerRank K G) n) := by
  let C := RGCert.depth_two_quadraticbounda FP d r hd2 hgen hD hcount hquad
  exact FP.forall_certificate_nilpotent
    (K := K) (G := G) C hB

/-- `≤`-indexed finite-check version of the depth-two quadratic nilpotent
obstruction. -/
theorem forall_quadratic_nilpotent
    [Fintype FP.toPresentation.Relator] {B d r : ℕ}
    (hB : GroupAlgebra.augmentationPowerSubmodule K G (B + 1) = ⊥)
    (hd2 : 2 < d)
    (hgen : d ≤ FP.generatorCount)
    (hD : ∀ x : FP.toPresentation.Relator, 2 ≤ FP.depths.depth x)
    (hcount : Nat.card FP.toPresentation.Relator ≤ r)
    (hquad : 4 * r < d * d) :
    ¬ (∀ n, n ≤ B + FP.maxRelatorDepth + 1 →
      FP.gsCoefficientInequality (GroupAlgebra.augmentationLayerRank K G) n) := by
  let C := RGCert.depth_two_quadraticbounda FP d r hd2 hgen hD hcount hquad
  exact FP.not_certificate_nilpotent
    (K := K) (G := G) C hB

/-- Explicit failing degree in the finite range for the depth-two quadratic
nilpotent augmentation obstruction. -/
theorem
  gs_inequality_nilpotent
    [Fintype FP.toPresentation.Relator] {B d r : ℕ}
    (hB : GroupAlgebra.augmentationPowerSubmodule K G (B + 1) = ⊥)
    (hd2 : 2 < d)
    (hgen : d ≤ FP.generatorCount)
    (hD : ∀ x : FP.toPresentation.Relator, 2 ≤ FP.depths.depth x)
    (hcount : Nat.card FP.toPresentation.Relator ≤ r)
    (hquad : 4 * r < d * d) :
    ∃ n ∈ Finset.range (B + FP.maxRelatorDepth + 2),
      ¬ FP.gsCoefficientInequality (GroupAlgebra.augmentationLayerRank K G) n := by
  let C := RGCert.depth_two_quadraticbounda FP d r hd2 hgen hD hcount hquad
  exact
    FP.inequality_certificate_nilpotent
    (K := K) (G := G) C hB

/-- `≤`-indexed explicit failing degree for the depth-two quadratic nilpotent
augmentation obstruction. -/
theorem
  inequality_quadratic_nilpotent
    [Fintype FP.toPresentation.Relator] {B d r : ℕ}
    (hB : GroupAlgebra.augmentationPowerSubmodule K G (B + 1) = ⊥)
    (hd2 : 2 < d)
    (hgen : d ≤ FP.generatorCount)
    (hD : ∀ x : FP.toPresentation.Relator, 2 ≤ FP.depths.depth x)
    (hcount : Nat.card FP.toPresentation.Relator ≤ r)
    (hquad : 4 * r < d * d) :
    ∃ n, n ≤ B + FP.maxRelatorDepth + 1 ∧
      ¬ FP.gsCoefficientInequality (GroupAlgebra.augmentationLayerRank K G) n := by
  let C := RGCert.depth_two_quadraticbounda FP d r hd2 hgen hD hcount hquad
  exact FP.not_inequality_nilpotent
    (K := K) (G := G) C hB



/-- Degree-one-silent finite-range version of the quadratic nilpotent obstruction. -/
theorem silent_quadratic_nilpotent
    [Fintype FP.toPresentation.Relator] {B d r : ℕ}
    (hB : GroupAlgebra.augmentationPowerSubmodule K G (B + 1) = ⊥)
    (hd2 : 2 < d)
    (hgen : d ≤ FP.generatorCount)
    (hsilent : FP.depths.degreeOneSilent)
    (hcount : Nat.card FP.toPresentation.Relator ≤ r)
    (hquad : 4 * r < d * d) :
    ¬ (∀ n ∈ Finset.range (B + FP.maxRelatorDepth + 2),
      FP.gsCoefficientInequality (GroupAlgebra.augmentationLayerRank K G) n) := by
  exact FP.not_forall_nilpotent
    (K := K) (G := G) hB hd2 hgen hsilent hcount hquad

/-- Degree-one-silent explicit finite-range failing degree for the quadratic
nilpotent augmentation obstruction. -/
theorem
fail_silent_nilpotent
    [Fintype FP.toPresentation.Relator] {B d r : ℕ}
    (hB : GroupAlgebra.augmentationPowerSubmodule K G (B + 1) = ⊥)
    (hd2 : 2 < d)
    (hgen : d ≤ FP.generatorCount)
    (hsilent : FP.depths.degreeOneSilent)
    (hcount : Nat.card FP.toPresentation.Relator ≤ r)
    (hquad : 4 * r < d * d) :
    ∃ n ∈ Finset.range (B + FP.maxRelatorDepth + 2),
      ¬ FP.gsCoefficientInequality (GroupAlgebra.augmentationLayerRank K G) n := by
  let C := RGCert.depth_two_quadraticbounda FP d r hd2 hgen hsilent hcount hquad
  exact
    FP.inequality_certificate_nilpotent
      (K := K) (G := G) C hB

/-- Degree-one-silent `≤`-indexed finite-check version of the quadratic nilpotent obstruction. -/
theorem forall_silent_nilpotent
    [Fintype FP.toPresentation.Relator] {B d r : ℕ}
    (hB : GroupAlgebra.augmentationPowerSubmodule K G (B + 1) = ⊥)
    (hd2 : 2 < d)
    (hgen : d ≤ FP.generatorCount)
    (hsilent : FP.depths.degreeOneSilent)
    (hcount : Nat.card FP.toPresentation.Relator ≤ r)
    (hquad : 4 * r < d * d) :
    ¬ (∀ n, n ≤ B + FP.maxRelatorDepth + 1 →
      FP.gsCoefficientInequality (GroupAlgebra.augmentationLayerRank K G) n) := by
  exact FP.forall_quadratic_nilpotent
    (K := K) (G := G) hB hd2 hgen hsilent hcount hquad

/-- Degree-one-silent `≤`-indexed explicit failing degree for the quadratic
nilpotent obstruction. -/
theorem fail_silent_quadratic
    [Fintype FP.toPresentation.Relator] {B d r : ℕ}
    (hB : GroupAlgebra.augmentationPowerSubmodule K G (B + 1) = ⊥)
    (hd2 : 2 < d)
    (hgen : d ≤ FP.generatorCount)
    (hsilent : FP.depths.degreeOneSilent)
    (hcount : Nat.card FP.toPresentation.Relator ≤ r)
    (hquad : 4 * r < d * d) :
    ∃ n, n ≤ B + FP.maxRelatorDepth + 1 ∧
      ¬ FP.gsCoefficientInequality (GroupAlgebra.augmentationLayerRank K G) n := by
  exact
    FP.inequality_quadratic_nilpotent
    (K := K) (G := G) hB hd2 hgen hsilent hcount hquad

end
end FPres
end Towers
