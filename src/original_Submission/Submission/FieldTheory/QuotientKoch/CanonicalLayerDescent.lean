import Submission.FieldTheory.QuotientKoch.CanonicalLayerSeparation
import Submission.Group.FiniteQuotientTower.KernelObstructions


open scoped Pointwise Topology commutatorElement

noncomputable section

namespace Submission
namespace TBluepr

open KPScaffo
open IGScaffo
open IRScaffo
open PCShadow
open PRFact
open RCFact

private instance initialThreeFact : Fact (Nat.Prime 3) :=
  ⟨Nat.prime_three⟩

namespace KRData

/--
A canonical Koch defect thread is a coherent canonical finite-layer relator
quotient thread killed in the actual initial Galois group but detected in one
finite canonical layer.
-/
abbrev KochDefectThread
    (D : KRData) :=
  Group.cSQuotie.DKThread
    D.ZassenhausRelatorSystem
    D.inverseLimitDescent

/--
The desired theorem fails exactly when one canonical Koch defect thread exists.
-/
lemma theorem_nonempty_thread
    (D : KRData) :
    ¬ D.KochFactorizationTheorem ↔
      Nonempty D.KochDefectThread := by
  rw [D.theorem_descent_injective]
  exact (Group.cSQuotie.detected_thread_injective
    D.ZassenhausRelatorSystem
    D.inverseLimitDescent).symm

/--
Unbundled canonical defect-thread form: failure is witnessed by one coherent
canonical thread killed in the actual quotient and nontrivial in one finite
canonical layer.
-/
lemma theorem_defect_thread
    (D : KRData) :
    ¬ D.KochFactorizationTheorem ↔
      ∃ y : D.RelatorInverseLimit,
        D.inverseLimitDescent y = 1 ∧
          ∃ n : ℕ,
            Group.inverseLimitProjection
                D.ZassenhausRelatorSystem n y ≠
              1 := by
  rw [D.theorem_descent_injective]
  simpa [MonoidHom.mem_ker] using
    (Group.cSQuotie.not_detected_level
      D.ZassenhausRelatorSystem
      D.inverseLimitDescent)

/--
Failure has a canonical first visible finite layer: a killed coherent thread
survives there and is invisible in every smaller canonical quotient layer.
-/
lemma not_detected_layer
    (D : KRData) :
    ¬ D.KochFactorizationTheorem ↔
      ∃ y : D.RelatorInverseLimit,
        D.inverseLimitDescent y = 1 ∧
          ∃ n : ℕ,
            Group.inverseLimitProjection
                D.ZassenhausRelatorSystem n y ≠
              1 ∧
              ∀ m : ℕ, m < n →
                Group.inverseLimitProjection
                    D.ZassenhausRelatorSystem m y =
                  1 := by
  constructor
  · intro hnot
    rcases (D.theorem_nonempty_thread.mp
      hnot) with ⟨W⟩
    exact ⟨W.thread, W.killed, W.firstDetectedDepth,
      W.detected_first_depth, fun m hm =>
        Group.cSQuotie.DKThread.projection_detected_depth
          D.ZassenhausRelatorSystem
          D.inverseLimitDescent
          W
          hm⟩
  · rintro ⟨y, hy, n, hyn, _hfirst⟩
    apply D.theorem_nonempty_thread.mpr
    exact ⟨{
      thread := y
      killed := hy
      depth := n
      detected := hyn
    }⟩

/--
Failure is equivalently one pair of canonical coherent finite-layer threads that
become equal in the actual initial Galois group while remaining distinct in one
finite canonical relator quotient layer.
-/
lemma
  theorem_fiber_counterexample
    (D : KRData) :
    ¬ D.KochFactorizationTheorem ↔
      ∃ x y : D.RelatorInverseLimit,
        D.inverseLimitDescent x =
            D.inverseLimitDescent y ∧
          ∃ n : ℕ,
            Group.inverseLimitProjection
                D.ZassenhausRelatorSystem n x ≠
              Group.inverseLimitProjection
                D.ZassenhausRelatorSystem n y := by
  rw [D.theorem_descent_injective]
  exact
    Group.cSQuotie.not_fiber_counterexample
    D.ZassenhausRelatorSystem
    D.inverseLimitDescent

/--
The desired theorem says exactly that each canonical finite relator quotient
projection descends uniquely through the actual initial Galois quotient of the
canonical inverse limit.
-/
lemma unique_through_descent
    (D : KRData) :
    D.KochFactorizationTheorem ↔
      ∀ n : ℕ,
        FactorsUniquelyThrough
          D.inverseLimitDescent
          (Group.inverseLimitProjection
            D.ZassenhausRelatorSystem n) := by
  rw [D.extra_projection_kernels]
  exact forall_congr' fun n =>
    (Group.cSQuotie.projection_unique_through
      D.ZassenhausRelatorSystem
      D.inverseLimitDescent
      D.limit_descent_surjective
      n).symm

/--
Failure is equivalently failure of one canonical finite relator quotient
projection to descend through the actual initial Galois quotient of the
canonical inverse limit.
-/
lemma not_through_descent
    (D : KRData) :
    ¬ D.KochFactorizationTheorem ↔
      ∃ n : ℕ,
        ¬ FactorsUniquelyThrough
          D.inverseLimitDescent
          (Group.inverseLimitProjection
            D.ZassenhausRelatorSystem n) := by
  rw [D.unique_through_descent]
  simp only [not_forall]

/--
Every finite canonical relator quotient projection from the canonical inverse
limit is onto.
-/
lemma limit_projection_surjective
    (D : KRData)
    (n : ℕ) :
    Function.Surjective
      (Group.inverseLimitProjection
        D.ZassenhausRelatorSystem n) := by
  intro y
  rcases (D.ZassenhausRelatorQuotient n).map_surjective y with
    ⟨x, rfl⟩
  exact ⟨D.zassenhausRelatorCompletion x, by
    simpa using congrArg
      (fun φ : initialKochFree.Carrier →*
          D.ZassenhausRelatorSystem.obj n =>
        φ x)
      (D.zassenhaus_relator_coordinate n)⟩

/--
Assuming the desired theorem, the actual initial Galois group maps canonically
onto the `n`th canonical finite relator quotient layer.
-/
def kochCanonicalTheorem
    (D : KRData)
    (hfactor : D.KochFactorizationTheorem)
    (n : ℕ) :
    initialGaloisGroup →*
      D.ZassenhausRelatorSystem.obj n :=
  PRFact.factorSurjective
    D.inverseLimitDescent
    (Group.inverseLimitProjection
      D.ZassenhausRelatorSystem n)
    D.limit_descent_surjective
    (by
      change D.kochLimitExtra ≤
        (Group.inverseLimitProjection
          D.ZassenhausRelatorSystem n).ker
      exact
        (D.extra_projection_kernels.mp
        hfactor) n)

/--
The theorem-induced canonical finite-layer factor really descends the
corresponding canonical inverse-limit projection.
-/
lemma theorem_comp_descent
    (D : KRData)
    (hfactor : D.KochFactorizationTheorem)
    (n : ℕ) :
    (D.kochCanonicalTheorem hfactor n).comp
        D.inverseLimitDescent =
      Group.inverseLimitProjection
        D.ZassenhausRelatorSystem n := by
  exact PRFact.factor_map_of
    D.inverseLimitDescent
    (Group.inverseLimitProjection
      D.ZassenhausRelatorSystem n)
    D.limit_descent_surjective
    (by
      change D.kochLimitExtra ≤
        (Group.inverseLimitProjection
          D.ZassenhausRelatorSystem n).ker
      exact
        (D.extra_projection_kernels.mp
        hfactor) n)

/--
The theorem-induced canonical finite-layer factor descends the ambient initial
Koch quotient map to the canonical finite relator quotient map.
-/
lemma factor_theorem_comp
    (D : KRData)
    (hfactor : D.KochFactorizationTheorem)
    (n : ℕ) :
    (D.kochCanonicalTheorem hfactor n).comp
        initialKochQuotient =
      (D.ZassenhausRelatorQuotient n).map := by
  rw [← D.limit_descent_comp,
    ← MonoidHom.comp_assoc,
    D.theorem_comp_descent,
    D.zassenhaus_relator_coordinate]

/--
Each theorem-induced canonical finite-layer factor is onto.
-/
lemma koch_theorem_surjective
    (D : KRData)
    (hfactor : D.KochFactorizationTheorem)
    (n : ℕ) :
    Function.Surjective
      (D.kochCanonicalTheorem hfactor n) := by
  intro y
  rcases D.limit_projection_surjective n y with
    ⟨x, rfl⟩
  exact ⟨D.inverseLimitDescent x, by
    simpa using congrArg
      (fun φ : D.RelatorInverseLimit →*
          D.ZassenhausRelatorSystem.obj n =>
        φ x)
      (D.theorem_comp_descent hfactor n)⟩

/--
The theorem-induced canonical finite-layer factors are compatible with the
canonical transition maps.
-/
lemma theorem_transition_comp
    (D : KRData)
    (hfactor : D.KochFactorizationTheorem)
    {m n : ℕ}
    (hmn : m ≤ n) :
    (D.ZassenhausRelatorSystem.map hmn).comp
        (D.kochCanonicalTheorem hfactor n) =
      D.kochCanonicalTheorem hfactor m := by
  apply MonoidHom.ext
  intro y
  rcases D.limit_descent_surjective y with ⟨x, rfl⟩
  have hn := congrArg
    (fun φ : D.RelatorInverseLimit →*
        D.ZassenhausRelatorSystem.obj n =>
      φ x)
    (D.theorem_comp_descent hfactor n)
  have hm := congrArg
    (fun φ : D.RelatorInverseLimit →*
        D.ZassenhausRelatorSystem.obj m =>
      φ x)
    (D.theorem_comp_descent hfactor m)
  change D.ZassenhausRelatorSystem.map hmn
      (D.kochCanonicalTheorem hfactor n
        (D.inverseLimitDescent x)) =
    D.kochCanonicalTheorem hfactor m
      (D.inverseLimitDescent x)
  change D.kochCanonicalTheorem hfactor n
      (D.inverseLimitDescent x) =
    Group.inverseLimitProjection
      D.ZassenhausRelatorSystem n x at hn
  change D.kochCanonicalTheorem hfactor m
      (D.inverseLimitDescent x) =
    Group.inverseLimitProjection
      D.ZassenhausRelatorSystem m x at hm
  rw [hn, hm]
  exact Group.limit_projection_compat
    D.ZassenhausRelatorSystem hmn x

/--
Assuming the desired theorem, the canonical `n`th finite relator quotient is a
continuous finite `3`-shadow of the actual initial Galois group.
-/
def kochShadowTheorem
    (D : KRData)
    (hfactor : D.KochFactorizationTheorem)
    (n : ℕ) :
    Shadow 3 initialGaloisGroup where
  Target := D.ZassenhausRelatorSystem.obj n
  map := D.kochCanonicalTheorem hfactor n
  map_continuous := by
    apply D.koch_limit_descent.continuous_iff.mpr
    change Continuous
      ((D.kochCanonicalTheorem hfactor n).comp
        D.inverseLimitDescent)
    rw [D.theorem_comp_descent]
    exact Group.tSQuotie.limit_projection_continuous
      D.RelatorTopologicalSystem n
  target_p_group :=
    (D.ZassenhausRelatorQuotient n).toRShadow.toShadow.target_p_group

lemma shadow_theorem_surjective
    (D : KRData)
    (hfactor : D.KochFactorizationTheorem)
    (n : ℕ) :
    Function.Surjective
      (D.kochShadowTheorem hfactor n).map := by
  exact D.koch_theorem_surjective hfactor n

/--
The finite layers descended from the canonical inverse limit assemble into the
canonical continuous factor cone from the actual initial Galois quotient.
-/
def continuousLimitDescent
    (D : KRData)
    (hfactor : D.KochFactorizationTheorem) :
    D.CRCone where
  factor := D.kochCanonicalTheorem hfactor
  factor_continuous := fun n =>
    (D.kochShadowTheorem hfactor n).map_continuous
  factor_comp_map := fun n =>
    D.factor_theorem_comp hfactor n

/--
The canonical inverse-limit descent produces the same unique continuous factor
cone as the direct quotient-map construction.
-/
lemma continuous_descent_existing
    (D : KRData)
    (hfactor : D.KochFactorizationTheorem) :
    D.continuousLimitDescent
        hfactor =
      D.continuousKochFactorization
        hfactor := by
  exact (CRCone.subsingleton D).elim _ _

/--
At each finite canonical layer, descent through the canonical inverse limit
recovers the earlier unique quotient-map factor.
-/
lemma koch_theorem_existing
    (D : KRData)
    (hfactor : D.KochFactorizationTheorem)
    (n : ℕ) :
    D.kochCanonicalTheorem hfactor n =
      (D.continuousKochFactorization
        hfactor).factor n := by
  simpa [continuousLimitDescent]
    using congrFun
      (congrArg
        (fun C : D.CRCone =>
          C.factor)
        (D.continuous_descent_existing
          hfactor))
      n

end KRData

end TBluepr
end Submission
