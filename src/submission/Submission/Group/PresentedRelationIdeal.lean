import Submission.Group.PresentedRelationRank
import Submission.Group.PresentedFox
import Submission.Algebra.Linear.FiniteRankMaps


open Filter
open scoped Pointwise EuclideanGeometry Topology BigOperators

noncomputable section

namespace Submission
namespace TBluepr

/--
The exact piece of relation-ideal data needed in one high degree.
-/
structure PHDatum
    {p d r : ℕ} [Fact p.Prime]
    (rels : Fin r → FreeGroup (Fin d))
    (depth : Fin r → ℕ)
    (n : ℕ)
    (hn : 2 ≤ n) where
  relatorToGenerator :
    pHSrc (p := p) rels depth n →ₗ[ZMod p]
      pGTarget (p := p) rels n
  coversKernel :
    presentedHighPresentation (p := p) rels n hn ≤
      LinearMap.range relatorToGenerator

namespace PHDatum

/-- A relation-ideal datum gives pointwise lifts of homogeneous kernel elements. -/
theorem pointwise_lifts
    {p d r : ℕ} [Fact p.Prime]
    {rels : Fin r → FreeGroup (Fin d)}
    {depth : Fin r → ℕ}
    {n : ℕ}
    {hn : 2 ≤ n}
    (D : PHDatum
      (p := p) rels depth n hn) :
    ∀ x : presentedHighPresentation (p := p) rels n hn,
      ∃ y : pHSrc (p := p) rels depth n,
        D.relatorToGenerator y =
          (x : pGTarget (p := p) rels n) := by
  intro x
  have hx :
      (x : pGTarget (p := p) rels n) ∈
        LinearMap.range D.relatorToGenerator :=
    D.coversKernel x.2
  exact hx

/-- A relation-ideal datum gives the numerical kernel bound. -/
theorem kernel_finrank_le
    {p d r : ℕ} [Fact p.Prime]
    {rels : Fin r → FreeGroup (Fin d)}
    {depth : Fin r → ℕ}
    [Finite (PresentedGroup (Set.range rels))]
    {n : ℕ}
    {hn : 2 ≤ n}
    (D : PHDatum
      (p := p) rels depth n hn) :
    Module.finrank (ZMod p)
        (LinearMap.ker
          (presentedHighMultiplication
            (p := p) rels n (by omega))) ≤
      Module.finrank (ZMod p)
        (pHSrc (p := p) rels depth n) := by
  classical
  let β :=
    presentedHighMultiplication
      (p := p) rels n (by omega)
  have hcoverage : LinearMap.ker β ≤
      LinearMap.range D.relatorToGenerator := by
    simpa [β, presentedHighPresentation] using
      D.coversKernel
  letI : Module (ZMod p)
      (∀ i : pARelato depth n,
        (↥(presentedAugmentationSubmodule
          (p := p) rels (n - depth i.1))) ⧸
          presentedAugmentationKernel (p := p) rels (n - depth i.1)) := by
    infer_instance
  exact
    linear_finrank_range
      (K := ZMod p)
      (G := pGTarget (p := p) rels n)
      (T := pALayer (p := p) rels n)
      (R := ∀ i : pARelato depth n,
        (↥(presentedAugmentationSubmodule
          (p := p) rels (n - depth i.1))) ⧸
          presentedAugmentationKernel (p := p) rels (n - depth i.1))
      β D.relatorToGenerator hcoverage

end PHDatum

/--
A numerical kernel bound is enough to manufacture the one-degree
relation-ideal datum noncanonically.

The filtered algebra still has to supply the bound; this lemma only packages
the finite-dimensional linear algebra that turns such a bound into a map whose
range contains the homogeneous generator kernel.
-/
theorem presented_high_datum
    {p d r : ℕ} [Fact p.Prime]
    (rels : Fin r → FreeGroup (Fin d))
    (depth : Fin r → ℕ)
    [Finite (PresentedGroup (Set.range rels))]
    (n : ℕ)
    (hn : 2 ≤ n)
    (hker_dim :
      Module.finrank (ZMod p)
          (LinearMap.ker
            (presentedHighMultiplication
              (p := p) rels n (by omega))) ≤
        Module.finrank (ZMod p)
          (pHSrc (p := p) rels depth n)) :
    Nonempty (PHDatum (p := p) rels depth n hn) := by
  classical
  let β :=
    presentedHighMultiplication
      (p := p) rels n (by omega)
  have hker_dim' :
      Module.finrank (ZMod p) (LinearMap.ker β) ≤
        Module.finrank (ZMod p)
          (pHSrc (p := p) rels depth n) := by
    simpa [β] using hker_dim
  letI : Module (ZMod p)
      (∀ i : pARelato depth n,
        (↥(presentedAugmentationSubmodule
          (p := p) rels (n - depth i.1))) ⧸
          presentedAugmentationKernel (p := p) rels (n - depth i.1)) := by
    infer_instance
  letI : Module.Free (ZMod p)
      (∀ i : pARelato depth n,
        (↥(presentedAugmentationSubmodule
          (p := p) rels (n - depth i.1))) ⧸
          presentedAugmentationKernel (p := p) rels (n - depth i.1)) :=
    Module.Free.of_divisionRing
      (ZMod p)
      (∀ i : pARelato depth n,
        (↥(presentedAugmentationSubmodule
          (p := p) rels (n - depth i.1))) ⧸
          presentedAugmentationKernel (p := p) rels (n - depth i.1))
  rcases linear_cover_finrank
      (K := ZMod p)
      (G := pGTarget (p := p) rels n)
      (T := pALayer (p := p) rels n)
      (R := ∀ i : pARelato depth n,
        (↥(presentedAugmentationSubmodule
          (p := p) rels (n - depth i.1))) ⧸
          presentedAugmentationKernel (p := p) rels (n - depth i.1))
      β hker_dim' with
    ⟨α, hα⟩
  refine
    ⟨{
      relatorToGenerator := α
      coversKernel := ?_
    }⟩
  simpa [β, presentedHighPresentation] using hα

/--
Free-side filtered strictness of the relator-difference ideal supplies the
concrete filtered Fox spanning statement in one degree.

The strictness hypothesis says that every filtered element of the free
relation ideal has, modulo the next augmentation power, an expansion in the
chosen relator differences with the expected shifted coefficients.  Applying
the Fox derivative lowers the error degree by one and gives the asserted
associated-graded spanning statement.
-/
theorem presented_derivative_exactness
    {p d r : ℕ} [Fact p.Prime]
    (rels : Fin r → FreeGroup (Fin d))
    (depth : Fin r → ℕ)
    (hdepth :
      ∀ i, rels i ∈ zassenhausFiltration p (FreeGroup (Fin d)) (depth i))
    (hdepth2 : ∀ i, 2 ≤ depth i)
    (hstrict : PresentedFilteredStrictness (p := p) rels depth)
    [Finite (PresentedGroup (Set.range rels))]
    (n : ℕ)
    (hn : 2 ≤ n) :
    presentedHighDerivative (p := p) rels n ≤
      LinearMap.range
        (presentedHighFox
          (p := p) rels depth hdepth hdepth2 n) := by
  classical
  intro x hx
  let F := FreeGroup (Fin d)
  let AF := MonoidAlgebra (ZMod p) F
  let IF : Ideal AF :=
    GShafar.augmentationIdeal (R := ZMod p) (G := F)
  let A := presentedGroupAlgebra (p := p) rels
  let I : Ideal A := presentedAugmentationIdeal (p := p) rels
  let qmap : AF →+* A :=
    GShafar.presentedAlgebra
      (R := ZMod p) (Set.range rels)
  rcases hx with ⟨B, hBmem, hqB, y, hyD, rfl⟩
  rcases hstrict n hn B hBmem hqB with ⟨aF, hBstrict⟩
  let aP : ∀ i : pARelato depth n,
      presentedAugmentationSubmodule (p := p) rels (n - depth i.1) :=
    fun i =>
      ⟨qmap (aF i : AF), by
        have hmap :
            qmap (aF i : AF) ∈
              (presentedAugmentationIdeal (p := p) rels) ^
                (n - depth i.1) := by
          have hfree : (aF i : AF) ∈ IF ^ (n - depth i.1) := by
            simp [IF]
          simpa [qmap, I, presentedAugmentationIdeal, F, A] using
            GShafar.presented_algebra_pow
              (R := ZMod p)
              (α := Fin d)
              (rels := Set.range rels)
              hfree
        simpa [I, presentedAugmentationSubmodule] using hmap⟩
  let c : pHSrc (p := p) rels depth n :=
    fun i =>
      (presentedAugmentationKernel
        (p := p) rels (n - depth i.1)).mkQ (aP i)
  refine ⟨c, ?_⟩
  rw [show c =
      fun i =>
        (presentedAugmentationKernel
          (p := p) rels (n - depth i.1)).mkQ (aP i) by rfl]
  rw [presented_fox_mk]
  funext j
  let Rsum : AF :=
    ∑ i : pARelato depth n,
      (aF i : AF) * augmentationDifference (ZMod p) F (rels i.1)
  let C : AF := B - Rsum
  have hCmem : C ∈ IF ^ (n + 1) := by
    simpa [C, Rsum, F, AF, IF, qmap] using hBstrict
  have hDfree :
      freeFoxDerivative (ZMod p) (Fin d) j C ∈ IF ^ n := by
    have hpred :=
      fox_derivative_pred
        (ZMod p) (Fin d) j (n := n + 1) hCmem
    simpa [IF] using hpred
  have hDpresent :
      qmap (freeFoxDerivative (ZMod p) (Fin d) j C) ∈
        I ^ n := by
    simpa [qmap, I, presentedAugmentationIdeal, F, A] using
      GShafar.presented_algebra_pow
        (R := ZMod p)
        (α := Fin d)
        (rels := Set.range rels)
        hDfree
  have hDR :
      qmap (freeFoxDerivative (ZMod p) (Fin d) j Rsum) =
        ∑ i : pARelato depth n,
          (aP i : A) *
            presentedFoxCoefficient (p := p) rels i.1 j := by
    dsimp [Rsum]
    rw [map_sum]
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i _hi
    have haug_rel :
        GShafar.augmentationHom (ZMod p) F
            (augmentationDifference (ZMod p) F (rels i.1)) = 0 := by
      simp [augmentationDifference, GShafar.augmentationHom,
        GShafar.augmentationCharacter, F]
    have hDrel :
        qmap
            (freeFoxDerivative (ZMod p) (Fin d) j
              (augmentationDifference (ZMod p) F (rels i.1))) =
          presentedFoxCoefficient (p := p) rels i.1 j := by
      simp [qmap, F, presentedFoxCoefficient,
        GShafar.presentedAlgebra,
        MonoidAlgebra.mapDomainRingHom, augmentationDifference,
        free_derivative_single]
    calc
      qmap
          (freeFoxDerivative (ZMod p) (Fin d) j
            ((aF i : AF) * augmentationDifference (ZMod p) F (rels i.1))) =
          qmap
            ((aF i : AF) *
              freeFoxDerivative (ZMod p) (Fin d) j
                (augmentationDifference (ZMod p) F (rels i.1))) := by
            rw [algebra_fox_derivative]
            simp [haug_rel, F]
      _ =
          qmap (aF i : AF) *
            qmap
              (freeFoxDerivative (ZMod p) (Fin d) j
                (augmentationDifference (ZMod p) F (rels i.1))) := by
            rw [map_mul]
      _ =
          (aP i : A) *
            presentedFoxCoefficient (p := p) rels i.1 j := by
            rw [hDrel]
  have hDC :
      qmap (freeFoxDerivative (ZMod p) (Fin d) j C) =
        (y j : A) -
          ∑ i : pARelato depth n,
            (aP i : A) *
              presentedFoxCoefficient (p := p) rels i.1 j := by
    dsimp [C]
    rw [map_sub, map_sub, hyD j, hDR]
  have htarget :
      (y j : A) -
          ∑ i : pARelato depth n,
            (aP i : A) *
              presentedFoxCoefficient (p := p) rels i.1 j ∈
        I ^ n := by
    rw [← hDC]
    exact hDpresent
  have htarget' :
      (∑ i : pARelato depth n,
            (aP i : A) *
              presentedFoxCoefficient (p := p) rels i.1 j) -
          (y j : A) ∈
        I ^ n := by
    rw [← neg_sub]
    exact (I ^ n).neg_mem htarget
  apply
    (Submodule.Quotient.eq
      (presentedAugmentationKernel (p := p) rels (n - 1))).mpr
  have hpow : n - 1 + 1 = n := by omega
  simpa [I, presentedAugmentationKernel, hpow,
    presentedAugmentationSubmodule,
    presented_augmentation_mul] using htarget'

theorem presented_datum_derivative
    {p d r : ℕ} [Fact p.Prime]
    (rels : Fin r → FreeGroup (Fin d))
    (depth : Fin r → ℕ)
    (hdepth :
      ∀ i, rels i ∈ zassenhausFiltration p (FreeGroup (Fin d)) (depth i))
    (hdepth2 : ∀ i, 2 ≤ depth i)
    [Finite (PresentedGroup (Set.range rels))]
    (n : ℕ)
    (hn : 2 ≤ n)
    (hspan :
      presentedHighDerivative (p := p) rels n ≤
        LinearMap.range
          (presentedHighFox
            (p := p) rels depth hdepth hdepth2 n)) :
    Nonempty (PHDatum (p := p) rels depth n hn) := by
  refine
    ⟨{
      relatorToGenerator :=
        presentedHighFox
          (p := p) rels depth hdepth hdepth2 n
      coversKernel := ?_
    }⟩
  exact
    le_trans
      (presented_presentation_derivative
        (p := p) rels n hn)
      hspan

theorem presented_rank_coverage
    {p d r : ℕ} [Fact p.Prime]
    (rels : Fin r → FreeGroup (Fin d))
    (depth : Fin r → ℕ)
    [Finite (PresentedGroup (Set.range rels))]
    (n : ℕ)
    (hn : 2 ≤ n)
    (α :
      pHSrc (p := p) rels depth n →ₗ[ZMod p]
        pGTarget (p := p) rels n)
    (hker :
      LinearMap.ker
          (presentedHighMultiplication
            (p := p) rels n (by omega)) ≤
        LinearMap.range α) :
    Module.finrank (ZMod p)
        (pGTarget (p := p) rels n) ≤
      Module.finrank (ZMod p)
          (pALayer (p := p) rels n) +
        Module.finrank (ZMod p)
          (pHSrc (p := p) rels depth n) := by
  classical
  let β :=
    presentedHighMultiplication
      (p := p) rels n (by omega)
  have hβ : Function.Surjective β :=
    presented_high_multiplication
      (p := p) rels n (by omega)
  have hker' : LinearMap.ker β ≤ LinearMap.range α := by
    simpa [β] using hker
  rcases linear_coprod_range
      β α hβ hker' with
    ⟨Ψ, hΨ⟩
  have hle :=
    Module.finrank_le_finrank_of_rank_le_rank
      (LinearMap.lift_rank_le_of_surjective Ψ hΨ)
      (Module.rank_lt_aleph0 (ZMod p)
      (pALayer (p := p) rels n ×
          pHSrc (p := p) rels depth n))
  simpa [Module.finrank_prod] using hle

/--
A numerical bound on the homogeneous generator-kernel manufactures the
relator-covering map needed for the rank estimate.
-/
theorem presented_rank_finrank
    {p d r : ℕ} [Fact p.Prime]
    (rels : Fin r → FreeGroup (Fin d))
    (depth : Fin r → ℕ)
    [Finite (PresentedGroup (Set.range rels))]
    (n : ℕ)
    (hn : 2 ≤ n)
    (hker_dim :
      Module.finrank (ZMod p)
          (LinearMap.ker
            (presentedHighMultiplication
              (p := p) rels n (by omega))) ≤
        Module.finrank (ZMod p)
          (pHSrc (p := p) rels depth n)) :
    Module.finrank (ZMod p)
        (pGTarget (p := p) rels n) ≤
      Module.finrank (ZMod p)
          (pALayer (p := p) rels n) +
        Module.finrank (ZMod p)
          (pHSrc (p := p) rels depth n) := by
  classical
  let β :=
    presentedHighMultiplication
      (p := p) rels n (by omega)
  have hker_dim' :
      Module.finrank (ZMod p) (LinearMap.ker β) ≤
        Module.finrank (ZMod p)
          (pHSrc (p := p) rels depth n) := by
    simpa [β] using hker_dim
  letI : Module (ZMod p)
      (∀ i : pARelato depth n,
        (↥(presentedAugmentationSubmodule
          (p := p) rels (n - depth i.1))) ⧸
          presentedAugmentationKernel (p := p) rels (n - depth i.1)) := by
    infer_instance
  letI : Module.Free (ZMod p)
      (∀ i : pARelato depth n,
        (↥(presentedAugmentationSubmodule
          (p := p) rels (n - depth i.1))) ⧸
          presentedAugmentationKernel (p := p) rels (n - depth i.1)) :=
    Module.Free.of_divisionRing
      (ZMod p)
      (∀ i : pARelato depth n,
        (↥(presentedAugmentationSubmodule
          (p := p) rels (n - depth i.1))) ⧸
          presentedAugmentationKernel (p := p) rels (n - depth i.1))
  rcases linear_cover_finrank
      (K := ZMod p)
      (G := pGTarget (p := p) rels n)
      (T := pALayer (p := p) rels n)
      (R := ∀ i : pARelato depth n,
        (↥(presentedAugmentationSubmodule
          (p := p) rels (n - depth i.1))) ⧸
          presentedAugmentationKernel (p := p) rels (n - depth i.1))
      β hker_dim' with
    ⟨α, hα⟩
  exact
    presented_rank_coverage
      (p := p) rels depth n hn α (by simpa [β] using hα)

/--
A one-degree filtered relation-ideal datum is enough for the rank bound in
that degree.
-/
theorem presented_rank_datum
    {p d r : ℕ} [Fact p.Prime]
    (rels : Fin r → FreeGroup (Fin d))
    (depth : Fin r → ℕ)
    [Finite (PresentedGroup (Set.range rels))]
    (n : ℕ)
    (hn : 2 ≤ n)
    (D : PHDatum (p := p) rels depth n hn) :
    Module.finrank (ZMod p)
        (pGTarget (p := p) rels n) ≤
      Module.finrank (ZMod p)
          (pALayer (p := p) rels n) +
        Module.finrank (ZMod p)
          (pHSrc (p := p) rels depth n) := by
  exact
    presented_rank_finrank
      (p := p) rels depth n hn
      (PHDatum.kernel_finrank_le
        (p := p) (rels := rels) (depth := depth) (n := n) (hn := hn) D)

theorem presented_gs_coverages
    {p d r : ℕ} [Fact p.Prime]
    (rels : Fin r → FreeGroup (Fin d))
    (depth : Fin r → ℕ)
    (hdepth :
      ∀ i, rels i ∈ zassenhausFiltration p (FreeGroup (Fin d)) (depth i))
    (hdepth2 : ∀ i, 2 ≤ depth i)
    [Finite (PresentedGroup (Set.range rels))]
    [Nontrivial (PresentedGroup (Set.range rels))]
    (hPGroup : IsPGroup p (PresentedGroup (Set.range rels)))
    (hcoverage :
      ∀ n (hn : 2 ≤ n),
        ∃ α :
          pHSrc (p := p) rels depth n →ₗ[ZMod p]
            pGTarget (p := p) rels n,
          LinearMap.ker
              (presentedHighMultiplication
                (p := p) rels n (by omega)) ≤
            LinearMap.range α)
    {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    0 < GShafar.relatorExpression d r depth t := by
  classical
  refine
    gs_rank_bounds
      (p := p) (d := d) (r := r)
      rels depth hdepth hdepth2 hPGroup ?_ ht0 ht1
  intro n hn
  rcases hcoverage n hn with ⟨α, hα⟩
  exact
    presented_rank_coverage
      (p := p) rels depth n hn α hα

/--
The remaining Zassenhaus-only algebra can be isolated as a kernel-dimension
bound in every degree `n ≥ 2`.
-/
theorem presented_gs_bounds
    {p d r : ℕ} [Fact p.Prime]
    (rels : Fin r → FreeGroup (Fin d))
    (depth : Fin r → ℕ)
    (hdepth :
      ∀ i, rels i ∈ zassenhausFiltration p (FreeGroup (Fin d)) (depth i))
    (hdepth2 : ∀ i, 2 ≤ depth i)
    [Finite (PresentedGroup (Set.range rels))]
    [Nontrivial (PresentedGroup (Set.range rels))]
    (hPGroup : IsPGroup p (PresentedGroup (Set.range rels)))
    (hker_dim :
      ∀ n (hn : 2 ≤ n),
        Module.finrank (ZMod p)
            (LinearMap.ker
              (presentedHighMultiplication
                (p := p) rels n (by omega))) ≤
          Module.finrank (ZMod p)
            (pHSrc (p := p) rels depth n))
    {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    0 < GShafar.relatorExpression d r depth t := by
  classical
  refine
    gs_rank_bounds
      (p := p) (d := d) (r := r)
      rels depth hdepth hdepth2 hPGroup ?_ ht0 ht1
  intro n hn
  exact
    presented_rank_finrank
      (p := p) rels depth n hn (hker_dim n hn)

/--
If the filtered relation ideal supplies the one-degree datum in every high
degree, the Zassenhaus-depth GS positivity conclusion follows.
-/
theorem presented_gs_data
    {p d r : ℕ} [Fact p.Prime]
    (rels : Fin r → FreeGroup (Fin d))
    (depth : Fin r → ℕ)
    (hdepth :
      ∀ i, rels i ∈ zassenhausFiltration p (FreeGroup (Fin d)) (depth i))
    (hdepth2 : ∀ i, 2 ≤ depth i)
    [Finite (PresentedGroup (Set.range rels))]
    [Nontrivial (PresentedGroup (Set.range rels))]
    (hPGroup : IsPGroup p (PresentedGroup (Set.range rels)))
    (hdata :
      ∀ n (hn : 2 ≤ n),
        Nonempty (PHDatum (p := p) rels depth n hn))
    {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    0 < GShafar.relatorExpression d r depth t := by
  classical
  refine
    gs_rank_bounds
      (p := p) (d := d) (r := r)
      rels depth hdepth hdepth2 hPGroup ?_ ht0 ht1
  intro n hn
  rcases hdata n hn with ⟨D⟩
  exact
    presented_rank_datum
      (p := p) rels depth n hn D

/--
If the associated graded relation module is generated by the actual relator
Fox relations with shifted augmentation-layer coefficients, then the usual
Hilbert-series Golod--Shafarevich conclusion follows.
-/
theorem
associated_graded_generation
    {p d r : ℕ} [Fact p.Prime]
    (rels : Fin r → FreeGroup (Fin d))
    (depth : Fin r → ℕ)
    (hdepth :
      ∀ i, rels i ∈ zassenhausFiltration p (FreeGroup (Fin d)) (depth i))
    (hdepth2 : ∀ i, 2 ≤ depth i)
    [Finite (PresentedGroup (Set.range rels))]
    [Nontrivial (PresentedGroup (Set.range rels))]
    (hPGroup : IsPGroup p (PresentedGroup (Set.range rels)))
    (hgraded :
      PresentedGradedGeneration
        (p := p) rels depth hdepth hdepth2)
    {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    0 < GShafar.relatorExpression d r depth t := by
  classical
  refine
    presented_gs_bounds
      (p := p) (d := d) (r := r)
      rels depth hdepth hdepth2 hPGroup ?_ ht0 ht1
  intro n hn
  simpa [presentedHighPresentation] using
    finrank_relation_surjective
      (p := p) rels depth hdepth hdepth2 n hn (hgraded n hn)

/--
Free-side filtered strictness of the relator-difference ideal is enough for
the Hilbert-series Golod--Shafarevich conclusion.
-/
theorem gs_filtered_strictness
    {p d r : ℕ} [Fact p.Prime]
    (rels : Fin r → FreeGroup (Fin d))
    (depth : Fin r → ℕ)
    (hdepth :
      ∀ i, rels i ∈ zassenhausFiltration p (FreeGroup (Fin d)) (depth i))
    (hdepth2 : ∀ i, 2 ≤ depth i)
    [Finite (PresentedGroup (Set.range rels))]
    [Nontrivial (PresentedGroup (Set.range rels))]
    (hPGroup : IsPGroup p (PresentedGroup (Set.range rels)))
    (hstrict : PresentedFilteredStrictness
      (p := p) rels depth)
    {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    0 < GShafar.relatorExpression d r depth t := by
  exact
    associated_graded_generation
      (p := p) (d := d) (r := r)
      rels depth hdepth hdepth2 hPGroup
      (generation_filtered_strictness
        (p := p) rels depth hdepth hdepth2 hstrict)
      ht0 ht1

/--
If every derivative layer is spanned by the actual relator Fox derivatives with
coefficients in the shifted augmentation layers, then the Zassenhaus-depth GS
positivity conclusion follows.
-/
theorem gs_derivative_spanning
    {p d r : ℕ} [Fact p.Prime]
    (rels : Fin r → FreeGroup (Fin d))
    (depth : Fin r → ℕ)
    (hdepth :
      ∀ i, rels i ∈ zassenhausFiltration p (FreeGroup (Fin d)) (depth i))
    (hdepth2 : ∀ i, 2 ≤ depth i)
    [Finite (PresentedGroup (Set.range rels))]
    [Nontrivial (PresentedGroup (Set.range rels))]
    (hPGroup : IsPGroup p (PresentedGroup (Set.range rels)))
    (hspan :
      ∀ n (_hn : 2 ≤ n),
        presentedHighDerivative (p := p) rels n ≤
          LinearMap.range
            (presentedHighFox
              (p := p) rels depth hdepth hdepth2 n))
    {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    0 < GShafar.relatorExpression d r depth t := by
  classical
  refine
    presented_gs_data
      (p := p) (d := d) (r := r)
      rels depth hdepth hdepth2 hPGroup ?_ ht0 ht1
  intro n hn
  exact
    presented_datum_derivative
      (p := p) rels depth hdepth hdepth2 n hn (hspan n hn)
end TBluepr

end Submission
