import Mathlib
import Submission.Group.PresentedHighDegree
import Submission.Group.PresentedHilbert
import Submission.Group.PresentedAugmentationBridge
import Submission.Group.PresentedAugmentationQuotient
import Submission.Group.GolodShafarevichCore


open Filter
open scoped Pointwise EuclideanGeometry Topology BigOperators

noncomputable section

namespace Submission

universe u
universe v w z


namespace TBluepr

/--
Finite-dimensional submodule comparison in the direction needed for the
associated-graded Fox complex.

If `U ≤ W` and the two submodules have the same finite dimension, then the
reverse inclusion holds.  This is the pure linear-algebra step that converts a
rank count into exactness of the associated-graded Fox complex.
-/
theorem submodule_finrank
    {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [Module.Finite K V]
    (U W : Submodule K V)
    (hUW : U ≤ W)
    (hfin : Module.finrank K U = Module.finrank K W) :
    W ≤ U := by
  classical
  by_contra hWU
  have hlt : U < W := lt_iff_le_not_ge.mpr ⟨hUW, hWU⟩
  have hfin_lt : Module.finrank K U < Module.finrank K W :=
    Submodule.finrank_lt_finrank_of_lt hlt
  exact (ne_of_lt hfin_lt) hfin

/--
Finite-dimensional linear algebra in the direction used by the
range-quotient frontier.

If the target has dimension at most the source, then there is a surjective
linear map from the source to the target.  The construction chooses linear
coordinates on both spaces, projects `K^n` onto the first `m` coordinates, and
transports the projection back across the coordinate equivalences.
-/
theorem surjective_linear_finrank
    {K V W : Type*} [Field K]
    [AddCommGroup V] [Module K V] [Module.Finite K V] [Module.Free K V]
    [AddCommGroup W] [Module K W] [Module.Finite K W] [Module.Free K W]
    (hfin : Module.finrank K W ≤ Module.finrank K V) :
    ∃ f : V →ₗ[K] W, Function.Surjective f := by
  classical
  let n := Module.finrank K V
  let m := Module.finrank K W
  have hmn : m ≤ n := by
    simpa [m, n] using hfin
  let coordProjection : (Fin n → K) →ₗ[K] (Fin m → K) :=
    { toFun := fun v j => v ⟨j.1, lt_of_lt_of_le j.2 hmn⟩
      map_add' := by
        intro x y
        ext j
        rfl
      map_smul' := by
        intro c x
        ext j
        rfl }
  have hcoordProjection :
      Function.Surjective coordProjection := by
    intro w
    let lifted : Fin n → K := fun i =>
      if hi : i.1 < m then w ⟨i.1, hi⟩ else 0
    refine ⟨lifted, ?_⟩
    ext j
    have hj :
        ((⟨j.1, lt_of_lt_of_le j.2 hmn⟩ : Fin n).1) < m := j.2
    simp [coordProjection, lifted, hj]
  have hVcoord :
      Module.finrank K V = Module.finrank K (Fin n → K) := by
    simp [n]
  have hWcoord :
      Module.finrank K W = Module.finrank K (Fin m → K) := by
    simp [m]
  rcases
      FiniteDimensional.nonempty_linearEquiv_of_finrank_eq
        (R := K) (M := V) (M' := Fin n → K) hVcoord with
    ⟨eV⟩
  rcases
      FiniteDimensional.nonempty_linearEquiv_of_finrank_eq
        (R := K) (M := W) (M' := Fin m → K) hWcoord with
    ⟨eW⟩
  let f : V →ₗ[K] W :=
    eW.symm.toLinearMap.comp (coordProjection.comp eV.toLinearMap)
  refine ⟨f, ?_⟩
  intro w
  rcases hcoordProjection (eW w) with ⟨v, hv⟩
  refine ⟨eV.symm v, ?_⟩
  change eW.symm (coordProjection (eV (eV.symm v))) = w
  simp [hv]

/--
The lower-bound part of the relator-depth bookkeeping.

This records only a choice of filtered depths for the defining relators,
pointwise above the declared depths in the final theorem.  It deliberately does
not include any relation-module exactness or Hilbert-series consequence.
-/
structure PDData
    {p d r : ℕ} [Fact p.Prime]
    (rels : Fin r → FreeGroup (Fin d))
    (declaredDepth : Fin r → ℕ) where
  chosenDepth : Fin r → ℕ
  declared_le_chosen : ∀ i, declaredDepth i ≤ chosenDepth i
  chosen_mem :
    ∀ i, rels i ∈ zassenhausFiltration p (FreeGroup (Fin d)) (chosenDepth i)
  chosen_two_le : ∀ i, 2 ≤ chosenDepth i

/--
The declared depths themselves form valid filtered-depth data.

This is a small sanity check on the bookkeeping: the final theorem's
hypotheses already give one depth datum.  Later, the relation-module theorem is
free to use this datum or a deeper one, but no algebra is hidden in this lemma.
-/
theorem presented_declared_depths
    {p d r : ℕ} [Fact p.Prime]
    (rels : Fin r → FreeGroup (Fin d))
    (depth : Fin r → ℕ)
    (hdepth :
      ∀ i, rels i ∈ zassenhausFiltration p (FreeGroup (Fin d)) (depth i))
    (hdepth2 : ∀ i, 2 ≤ depth i) :
    Nonempty (PDData (p := p) rels depth) := by
  classical
  refine ⟨{
    chosenDepth := depth
    declared_le_chosen := ?_
    chosen_mem := ?_
    chosen_two_le := ?_
  }⟩
  · intro i
    exact le_rfl
  · intro i
    exact hdepth i
  · intro i
    exact hdepth2 i

/--
A refinement of declared relator depths to the degrees at which the
relation-module argument is actually run.

The declared depth in the final theorem is only a lower bound: a relator may
lie deeper in the Zassenhaus filtration.  The associated-graded Fox map should
be formed at depths where the relators genuinely contribute.  This package
records such refined depths, their comparison with the declared depths, and
the high-degree surjections supplied by the classical relation-module proof.
-/
structure PresentedDepthRefinement
    {p d r : ℕ} [Fact p.Prime]
    (rels : Fin r → FreeGroup (Fin d))
    (depth : Fin r → ℕ) where
  refinedDepth : Fin r → ℕ
  depth_le_refined : ∀ i, depth i ≤ refinedDepth i
  refined_mem :
    ∀ i, rels i ∈ zassenhausFiltration p (FreeGroup (Fin d)) (refinedDepth i)
  refined_two_le : ∀ i, 2 ≤ refinedDepth i
  highDegree_surjective :
    ∀ n, 2 ≤ n →
      ∃ Ψ :
        _root_.Submission.TBluepr.presentedHighDegree
            (p := p) (d := d) (r := r) rels refinedDepth n →ₗ[ZMod p]
          _root_.Submission.TBluepr.pGTarget
            (p := p) (d := d) (r := r) rels n,
        Function.Surjective Ψ

/--
The relation-module maps attached to a fixed filtered-depth datum.

This isolates the algebraic output of the filtered Fox relation module from
the choice and comparison of depths.  The target is intentionally the same
split source used by `U0.lean` for the high-degree dimension count.
-/
def PDData.HighDegreerelModulemaps
    {p d r : ℕ} [Fact p.Prime]
    {rels : Fin r → FreeGroup (Fin d)}
    {declaredDepth : Fin r → ℕ}
    (D : PDData (p := p) rels declaredDepth) : Prop :=
  ∀ n, 2 ≤ n →
    ∃ Ψ :
      _root_.Submission.TBluepr.presentedHighDegree
          (p := p) (d := d) (r := r) rels D.chosenDepth n →ₗ[ZMod p]
        _root_.Submission.TBluepr.pGTarget
          (p := p) (d := d) (r := r) rels n,
      Function.Surjective Ψ

/--
The generator half of the high-degree relation-module construction is already
formalized in `U0.lean`.

This lemma repackages it for a `PDData`.  Notice that it
does not use the relators' depths at all: the degree-one images of the
presentation generators generate the augmentation graded algebra.
-/
theorem PDData.generatorMap_surjective
    {p d r : ℕ} [Fact p.Prime]
    {rels : Fin r → FreeGroup (Fin d)}
    {declaredDepth : Fin r → ℕ}
    (_D : PDData (p := p) rels declaredDepth)
    [Finite (PresentedGroup (Set.range rels))]
    (n : ℕ) (hn : 2 ≤ n) :
    Function.Surjective
      (_root_.Submission.TBluepr.presentedHighMultiplication
        (p := p) rels n (by omega)) := by
  classical
  have hn' : 1 ≤ n := by
    omega
  exact
    presented_high_multiplication
      (p := p) rels n hn'

/--
Package a filtered-depth datum and its high-degree relation-module maps as the
refinement object consumed by the rest of the U1a proof.
-/
def presented_refinement_data
    {p d r : ℕ} [Fact p.Prime]
    {rels : Fin r → FreeGroup (Fin d)}
    {depth : Fin r → ℕ}
    (D : PDData (p := p) rels depth)
    (hD : D.HighDegreerelModulemaps) :
    PresentedDepthRefinement (p := p) rels depth := by
  classical
  exact {
    refinedDepth := D.chosenDepth
    depth_le_refined := D.declared_le_chosen
    refined_mem := D.chosen_mem
    refined_two_le := D.chosen_two_le
    highDegree_surjective := hD
  }

/--
The high-degree relation-module map obtained from a depth refinement.

This is now only unpacking the refinement package: the difficult algebraic
choice of the refined depths and the filtered Fox relation-module surjections
is kept in `finite_presented_p_group_relation_depth_refinement_exists`.
-/
theorem high_module_refinement
    {p d r : ℕ} [Fact p.Prime]
    (rels : Fin r → FreeGroup (Fin d))
    (depth : Fin r → ℕ)
    (R : PresentedDepthRefinement (p := p) rels depth)
    (n : ℕ) (hn : 2 ≤ n) :
    ∃ Ψ :
      _root_.Submission.TBluepr.presentedHighDegree
          (p := p) (d := d) (r := r) rels R.refinedDepth n →ₗ[ZMod p]
        _root_.Submission.TBluepr.pGTarget
          (p := p) (d := d) (r := r) rels n,
      Function.Surjective Ψ := by
  classical
  have hsurj :
      ∃ Ψ :
        _root_.Submission.TBluepr.presentedHighDegree
            (p := p) (d := d) (r := r) rels R.refinedDepth n →ₗ[ZMod p]
          _root_.Submission.TBluepr.pGTarget
            (p := p) (d := d) (r := r) rels n,
        Function.Surjective Ψ :=
    R.highDegree_surjective n hn
  exact hsurj

/--
Once the high-degree relation-module map is surjective, the coefficient bound
is only finite-dimensional linear algebra.

This lemma is deliberately separate from the algebraic construction above:
`U0.lean` already proves the dimension count for any surjective map from the
high-degree source to the generator target.
-/
theorem high_module_surjective
    {p d r : ℕ} [Fact p.Prime]
    (rels : Fin r → FreeGroup (Fin d))
    (depth : Fin r → ℕ)
    [Finite (PresentedGroup (Set.range rels))]
    (n : ℕ)
    (Ψ :
      _root_.Submission.TBluepr.presentedHighDegree
          (p := p) (d := d) (r := r) rels depth n →ₗ[ZMod p]
        _root_.Submission.TBluepr.pGTarget
          (p := p) (d := d) (r := r) rels n)
    (hΨ : Function.Surjective Ψ) :
    d * _root_.Submission.TBluepr.presentedHilbertSequence
        (p := p) rels (n - 1) ≤
      _root_.Submission.TBluepr.presentedHilbertSequence
          (p := p) rels n +
        ∑ i, if depth i ≤ n then
          _root_.Submission.TBluepr.presentedHilbertSequence
            (p := p) rels (n - depth i)
        else 0 := by
  classical
  exact
    _root_.Submission.TBluepr.high_bound_surjective
      (p := p) (d := d) (r := r)
      rels depth n Ψ hΨ

/--
The high-degree coefficient inequality at the refined relator depths.

The source dimensions are counted using `R.refinedDepth`, because those are the
degrees where the filtered relation-module map is actually formed.
-/
theorem presented_high_refinement
    {p d r : ℕ} [Fact p.Prime]
    (rels : Fin r → FreeGroup (Fin d))
    (depth : Fin r → ℕ)
    (R : PresentedDepthRefinement (p := p) rels depth)
    [Finite (PresentedGroup (Set.range rels))]
    (n : ℕ) (hn : 2 ≤ n) :
    d * _root_.Submission.TBluepr.presentedHilbertSequence
        (p := p) rels (n - 1) ≤
      _root_.Submission.TBluepr.presentedHilbertSequence
          (p := p) rels n +
        ∑ i, if R.refinedDepth i ≤ n then
          _root_.Submission.TBluepr.presentedHilbertSequence
            (p := p) rels (n - R.refinedDepth i)
        else 0 := by
  classical
  rcases
      high_module_refinement
        (p := p) (d := d) (r := r)
        rels depth R n hn with
    ⟨Ψ, hΨ⟩
  exact
    high_module_surjective
      (p := p) (d := d) (r := r)
      rels R.refinedDepth n Ψ hΨ

/--
The previous relation-module estimate is exactly the high-degree full
natural-number coefficient inequality for the concrete augmentation Hilbert
sequence.
-/
theorem full_inequality_refinement
    {p d r : ℕ} [Fact p.Prime]
    (rels : Fin r → FreeGroup (Fin d))
    (depth : Fin r → ℕ)
    (R : PresentedDepthRefinement (p := p) rels depth)
    [Finite (PresentedGroup (Set.range rels))]
    (n : ℕ) (hn : 2 ≤ n) :
    GShafar.fullCoefficientInequality d
      (_root_.Submission.TBluepr.presentedHilbertSequence
        (p := p) rels) R.refinedDepth n := by
  classical
  apply full_inequality_high
  · omega
  · exact
      presented_high_refinement
        (p := p) (d := d) (r := r)
        rels depth R n hn

/--
The concrete augmentation Hilbert sequence satisfies the coefficientwise
Golod--Shafarevich inequalities in every degree for the refined depths.

Degrees `0` and `1` are already formalized in `U0.lean`; the high-degree case
is the relation-module estimate above.
-/
theorem presented_inequality_refinement
    {p d r : ℕ} [Fact p.Prime]
    (rels : Fin r → FreeGroup (Fin d))
    (depth : Fin r → ℕ)
    (R : PresentedDepthRefinement (p := p) rels depth)
    [Finite (PresentedGroup (Set.range rels))]
    [Nontrivial (PresentedGroup (Set.range rels))]
    (hPGroup : IsPGroup p (PresentedGroup (Set.range rels))) :
    ∀ n, GShafar.fullCoefficientInequality d
      (_root_.Submission.TBluepr.presentedHilbertSequence
        (p := p) rels) R.refinedDepth n := by
  classical
  intro n
  by_cases hn0 : n = 0
  · subst n
    exact full_coefficient_inequality
  by_cases hn1 : n = 1
  · subst n
    simpa using
      _root_.Submission.TBluepr.presented_full_inequality
        (p := p) (d := d) (r := r)
        rels R.refinedDepth R.refined_mem R.refined_two_le hPGroup
  have hn2 : 2 ≤ n := by omega
  exact
    full_inequality_refinement
      (p := p) (d := d) (r := r)
      rels depth R n hn2

/--
The refined depths give the positive depth-counted GS expression.
-/
theorem presented_gs_refinement
    {p d r : ℕ} [Fact p.Prime]
    (rels : Fin r → FreeGroup (Fin d))
    (depth : Fin r → ℕ)
    (R : PresentedDepthRefinement (p := p) rels depth)
    [Finite (PresentedGroup (Set.range rels))]
    [Nontrivial (PresentedGroup (Set.range rels))]
    (hPGroup : IsPGroup p (PresentedGroup (Set.range rels)))
    {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    0 < GShafar.relatorExpression d r R.refinedDepth t := by
  classical
  have hfull :
      ∀ n, GShafar.fullCoefficientInequality d
        (_root_.Submission.TBluepr.presentedHilbertSequence
          (p := p) rels) R.refinedDepth n :=
    presented_inequality_refinement
      (p := p) (d := d) (r := r)
      rels depth R hPGroup
  exact
    gs_full_inequalities
      (p := p) (d := d) (r := r)
      rels R.refinedDepth R.refined_mem R.refined_two_le hPGroup hfull ht0 ht1

/--
On `(0, 1)`, increasing a natural exponent weakly decreases `t^n`.
-/
lemma real_pow_ioo
    {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1)
    {m n : ℕ} (hmn : m ≤ n) :
    t ^ n ≤ t ^ m := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
  have ht_nonneg : 0 ≤ t := le_of_lt ht0
  have hpow_le_one : t ^ k ≤ 1 := by
    simpa using
      (pow_le_one₀ (a := t) ht_nonneg ht1.le : t ^ k ≤ 1)
  have hbase_nonneg : 0 ≤ t ^ m := pow_nonneg ht_nonneg m
  calc
    t ^ (m + k) = t ^ m * t ^ k := by
      rw [pow_add]
    _ ≤ t ^ m * 1 := by
      exact mul_le_mul_of_nonneg_left hpow_le_one hbase_nonneg
    _ = t ^ m := by
      rw [mul_one]

/--
If `refinedDepth` is pointwise at least `depth`, the refined relation series is
bounded above by the declared relation series on `(0, 1)`.
-/
lemma relator_expression_depth
    {d r : ℕ} {depth refinedDepth : Fin r → ℕ}
    (hdepth_le : ∀ i, depth i ≤ refinedDepth i)
    {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    GShafar.relatorExpression d r refinedDepth t ≤
      GShafar.relatorExpression d r depth t := by
  classical
  unfold GShafar.relatorExpression
  have hsum :
      ∑ i, t ^ refinedDepth i ≤ ∑ i, t ^ depth i := by
    refine Finset.sum_le_sum ?_
    intro i _hi
    exact real_pow_ioo ht0 ht1 (hdepth_le i)
  linarith


end TBluepr

end Submission
