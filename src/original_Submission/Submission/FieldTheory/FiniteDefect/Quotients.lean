import Submission.FieldTheory.QuotientKoch.CanonicalLayerDescent
import Submission.Group.FiniteQuotientTower.FiniteDefectQuotients


open scoped Pointwise Topology commutatorElement

noncomputable section

namespace Submission
namespace TBluepr

open KPScaffo
open IGScaffo
open IRScaffo
open PCShadow

private instance initialThreeFact : Fact (Nat.Prime 3) :=
  ⟨Nat.prime_three⟩

namespace KRData

/--
The image in the `n`th canonical relator quotient layer of the extra kernel
still collapsed when descending to the actual initial Galois group.
-/
abbrev CanonicalDefectSubgroup
    (D : KRData)
    (n : ℕ) :=
  Group.cSQuotie.finiteDefectSubgroup
    D.ZassenhausRelatorSystem
    D.inverseLimitDescent
    n

/--
The quotient of the `n`th canonical relator quotient layer by the finite image
of the canonical inverse-limit extra kernel.
-/
abbrev CanonicalKochDefect
    (D : KRData)
    (n : ℕ) :=
  Group.cSQuotie.finiteDefectQuotient
    D.ZassenhausRelatorSystem
    D.inverseLimitDescent
    D.limit_projection_surjective
    n

/--
The quotient map from a canonical relator quotient layer to its finite defect
quotient.
-/
def canonicalKochDefect
    (D : KRData)
    (n : ℕ) :
    D.ZassenhausRelatorSystem.obj n →*
      D.CanonicalKochDefect n :=
  Group.cSQuotie.defectQuotient
    D.ZassenhausRelatorSystem
    D.inverseLimitDescent
    D.limit_projection_surjective
    n

/--
The actual initial Galois group always maps onto the `n`th canonical finite
defect quotient.
-/
def canonicalDefectFactor
    (D : KRData)
    (n : ℕ) :
    initialGaloisGroup →*
      D.CanonicalKochDefect n :=
  Group.cSQuotie.finiteDefectFactor
    D.ZassenhausRelatorSystem
    D.inverseLimitDescent
    D.limit_descent_surjective
    D.limit_projection_surjective
    n

/--
Canonical finite defect quotient factors descend the corresponding finite
defect quotient projection from the canonical inverse limit.
-/
lemma defect_comp_descent
    (D : KRData)
    (n : ℕ) :
    (D.canonicalDefectFactor n).comp
        D.inverseLimitDescent =
      Group.cSQuotie.finiteDefectProjection
        D.ZassenhausRelatorSystem
        D.inverseLimitDescent
        D.limit_projection_surjective
        n := by
  exact Group.cSQuotie.defect_factor_comp
    D.ZassenhausRelatorSystem
    D.inverseLimitDescent
    D.limit_descent_surjective
    D.limit_projection_surjective
    n

/--
Every canonical finite defect quotient is an actual finite quotient of the
actual initial Galois group.
-/
lemma canonical_defect_surjective
    (D : KRData)
    (n : ℕ) :
    Function.Surjective (D.canonicalDefectFactor n) := by
  exact Group.cSQuotie.defect_factor_surjective
    D.ZassenhausRelatorSystem
    D.inverseLimitDescent
    D.limit_descent_surjective
    D.limit_projection_surjective
    n

/--
Every canonical finite defect quotient is an unconditional continuous finite
`3`-shadow of the actual initial Galois group.
-/
def kochDefectShadow
    (D : KRData)
    (n : ℕ) :
    Shadow 3 initialGaloisGroup := by
  letI : TopologicalSpace (D.CanonicalKochDefect n) := ⊥
  letI : DiscreteTopology (D.CanonicalKochDefect n) := ⟨rfl⟩
  exact {
    Target := D.CanonicalKochDefect n
    map := D.canonicalDefectFactor n
    map_continuous := by
      apply D.koch_limit_descent.continuous_iff.mpr
      change Continuous
        ((D.canonicalDefectFactor n).comp
          D.inverseLimitDescent)
      rw [D.defect_comp_descent]
      change Continuous
        ((D.canonicalKochDefect n).comp
          (Group.inverseLimitProjection
            D.ZassenhausRelatorSystem n))
      have hquotientMapContinuous :
          Continuous (D.canonicalKochDefect n) :=
        continuous_of_discreteTopology
      exact hquotientMapContinuous.comp
        (Group.tSQuotie.limit_projection_continuous
          D.RelatorTopologicalSystem n)
    target_p_group :=
      (D.ZassenhausRelatorQuotient
        n).toRShadow.toShadow.target_p_group.of_surjective
        (D.canonicalKochDefect n)
        (Group.cSQuotie.defectNormalSubgroup
          D.ZassenhausRelatorSystem
          D.inverseLimitDescent
          D.limit_projection_surjective
          n).projection_surjective
  }

/--
Canonical finite defect shadows are actual quotient shadows of the initial
Galois group.
-/
lemma defect_shadow_surjective
    (D : KRData)
    (n : ℕ) :
    Function.Surjective (D.kochDefectShadow n).map := by
  exact D.canonical_defect_surjective n

/--
The compatible inverse system of canonical finite defect quotients of the
actual initial Galois quotient.
-/
abbrev CanonicalDefectSystem
    (D : KRData) :=
  Group.cSQuotie.finiteDefectSystem
    D.ZassenhausRelatorSystem
    D.inverseLimitDescent
    D.limit_projection_surjective

/--
The actual initial Galois group maps canonically to the inverse limit of its
canonical finite defect quotient shadows.
-/
def kochDefectComparison
    (D : KRData) :
    initialGaloisGroup →*
      Group.inverseLimit D.CanonicalDefectSystem :=
  Group.cSQuotie.finiteDefectComparison
    D.ZassenhausRelatorSystem
    D.inverseLimitDescent
    D.limit_descent_surjective
    D.limit_projection_surjective

/--
The coordinates of the canonical finite defect quotient comparison map are the
canonical finite defect quotient factors.
-/
lemma defect_comparison_coordinate
    (D : KRData)
    (n : ℕ) :
    (Group.inverseLimitProjection D.CanonicalDefectSystem n).comp
        D.kochDefectComparison =
      D.canonicalDefectFactor n := by
  exact Group.cSQuotie.finite_defect_comparison
    D.ZassenhausRelatorSystem
    D.inverseLimitDescent
    D.limit_descent_surjective
    D.limit_projection_surjective
    n

/--
After precomposition with canonical inverse-limit descent, the actual Galois
comparison map is the canonical finite defect quotient completion map.
-/
lemma defect_comparison_descent
    (D : KRData) :
    D.kochDefectComparison.comp
        D.inverseLimitDescent =
      Group.cSQuotie.finiteDefectCompletion
        D.ZassenhausRelatorSystem
        D.inverseLimitDescent
        D.limit_projection_surjective := by
  exact Group.cSQuotie.finite_defect_comp
    D.ZassenhausRelatorSystem
    D.inverseLimitDescent
    D.limit_descent_surjective
    D.limit_projection_surjective

/--
Under the finite quotient Koch theorem, canonical finite defect quotient
shadows separate the actual initial Galois group.
-/
lemma defect_comparison_theorem
    (D : KRData)
    (hfactor : D.KochFactorizationTheorem) :
    Function.Injective D.kochDefectComparison := by
  apply (Group.cSQuotie.fin_level_saturation
    D.ZassenhausRelatorSystem
    D.inverseLimitDescent
    D.limit_descent_surjective
    D.limit_projection_surjective).mpr
  have hdescent :
      Function.Injective D.inverseLimitDescent :=
    D.theorem_descent_injective.mp
      hfactor
  have hkernel :
      D.inverseLimitDescent.ker = ⊥ :=
    (MonoidHom.ker_eq_bot_iff
      D.inverseLimitDescent).mpr hdescent
  rw [hkernel]
  simpa [Group.cSQuotie.finiteLevelSaturation] using
    D.ZassenhausRelatorSystem.i_inf_kernels

/--
The finite quotient Koch theorem says exactly that every canonical finite
defect subgroup vanishes.
-/
lemma forall_defect_bot
    (D : KRData) :
    D.KochFactorizationTheorem ↔
      ∀ n : ℕ, D.CanonicalDefectSubgroup n = ⊥ := by
  rw [D.theorem_descent_injective]
  exact Group.cSQuotie.injective_forall_bot
    D.ZassenhausRelatorSystem
    D.inverseLimitDescent

/--
Failure of the finite quotient Koch theorem is detected by one nontrivial
finite image of the canonical inverse-limit extra kernel.
-/
lemma not_defect_bot
    (D : KRData) :
    ¬ D.KochFactorizationTheorem ↔
      ∃ n : ℕ, D.CanonicalDefectSubgroup n ≠ ⊥ := by
  rw [D.theorem_descent_injective]
  exact Group.cSQuotie.not_ne_bot
    D.ZassenhausRelatorSystem
    D.inverseLimitDescent

/--
The finite quotient Koch theorem says exactly that every canonical finite
defect quotient recovers its original canonical relator quotient layer.
-/
lemma
  theorem_forall_injective
    (D : KRData) :
    D.KochFactorizationTheorem ↔
      ∀ n : ℕ, Function.Injective (D.canonicalKochDefect n) := by
  rw [D.theorem_descent_injective]
  exact Group.cSQuotie.injective_forall_defect
    D.ZassenhausRelatorSystem
    D.inverseLimitDescent
    D.limit_projection_surjective

/--
Failure of the finite quotient Koch theorem is detected by one canonical finite
defect quotient that genuinely collapses its original finite layer.
-/
lemma not_koch_injective
    (D : KRData) :
    ¬ D.KochFactorizationTheorem ↔
      ∃ n : ℕ, ¬ Function.Injective (D.canonicalKochDefect n) := by
  rw [D.theorem_descent_injective]
  exact Group.cSQuotie.not_injective_quotient
    D.ZassenhausRelatorSystem
    D.inverseLimitDescent
    D.limit_projection_surjective

/--
For a failed finite quotient Koch theorem, the first canonical finite layer
where the extra kernel has nontrivial finite image.
-/
def canonicalDefectDepth
    (D : KRData)
    (hnot : ¬ D.KochFactorizationTheorem) :
    ℕ :=
  Group.cSQuotie.firstDefectDepth
    D.ZassenhausRelatorSystem
    D.inverseLimitDescent
    ((not_congr
      D.theorem_descent_injective).mp
      hnot)

/--
The first canonical finite defect depth has a nontrivial finite defect
subgroup.
-/
lemma ne_bot_depth
    (D : KRData)
    (hnot : ¬ D.KochFactorizationTheorem) :
    D.CanonicalDefectSubgroup
        (D.canonicalDefectDepth hnot) ≠
      ⊥ := by
  exact Group.cSQuotie.defect_ne_bot
    D.ZassenhausRelatorSystem
    D.inverseLimitDescent
    ((not_congr
      D.theorem_descent_injective).mp
      hnot)

/--
All earlier canonical finite layers are defect-free before the first canonical
finite defect depth.
-/
lemma defect_bot_depth
    (D : KRData)
    (hnot : ¬ D.KochFactorizationTheorem)
    {m : ℕ}
    (hm : m < D.canonicalDefectDepth hnot) :
    D.CanonicalDefectSubgroup m = ⊥ := by
  exact
    Group.cSQuotie.bot_first_depth
    D.ZassenhausRelatorSystem
    D.inverseLimitDescent
    ((not_congr
      D.theorem_descent_injective).mp
      hnot)
    hm

/--
At the first canonical finite defect depth, the canonical finite defect
quotient genuinely collapses its original finite layer.
-/
lemma canonical_defect_depth
    (D : KRData)
    (hnot : ¬ D.KochFactorizationTheorem) :
    ¬ Function.Injective
      (D.canonicalKochDefect
        (D.canonicalDefectDepth hnot)) := by
  exact Group.cSQuotie.fin_defect_depth
    D.ZassenhausRelatorSystem
    D.inverseLimitDescent
    D.limit_projection_surjective
    ((not_congr
      D.theorem_descent_injective).mp
      hnot)

/--
Before the first canonical finite defect depth, canonical finite defect
quotients still recover their original finite layers.
-/
lemma koch_defect_depth
    (D : KRData)
    (hnot : ¬ D.KochFactorizationTheorem)
    {m : ℕ}
    (hm : m < D.canonicalDefectDepth hnot) :
    Function.Injective (D.canonicalKochDefect m) := by
  exact Group.cSQuotie.fin_defect_injective
    D.ZassenhausRelatorSystem
    D.inverseLimitDescent
    D.limit_projection_surjective
    ((not_congr
      D.theorem_descent_injective).mp
      hnot)
    hm

/--
Assuming the finite quotient Koch theorem, the canonical finite defect quotient
at level `n` is canonically the original canonical relator quotient layer.
-/
def canonicalDefectTheorem
    (D : KRData)
    (hfactor : D.KochFactorizationTheorem)
    (n : ℕ) :
    D.ZassenhausRelatorSystem.obj n ≃*
      D.CanonicalKochDefect n :=
  Group.cSQuotie.finiteDefectBot
    D.ZassenhausRelatorSystem
    D.inverseLimitDescent
    D.limit_projection_surjective
    n
    ((D.forall_defect_bot.mp
      hfactor) n)

/--
Under the finite quotient Koch theorem, the finite defect quotient factor is
the theorem-induced canonical finite-layer factor followed by the canonical
defect-free finite-layer equivalence.
-/
lemma canonical_defect_theorem
    (D : KRData)
    (hfactor : D.KochFactorizationTheorem)
    (n : ℕ) :
    (D.canonicalDefectTheorem hfactor n).toMonoidHom.comp
        (D.kochCanonicalTheorem hfactor n) =
      D.canonicalDefectFactor n := by
  apply MonoidHom.ext
  intro y
  rcases D.limit_descent_surjective y with ⟨x, rfl⟩
  have hcanonical := congrArg
    (fun ψ : D.RelatorInverseLimit →*
        D.ZassenhausRelatorSystem.obj n =>
      ψ x)
    (D.theorem_comp_descent hfactor n)
  have hdefect := congrArg
    (fun ψ : D.RelatorInverseLimit →*
        D.CanonicalKochDefect n =>
      ψ x)
    (D.defect_comp_descent n)
  change D.kochCanonicalTheorem hfactor n
      (D.inverseLimitDescent x) =
    Group.inverseLimitProjection D.ZassenhausRelatorSystem n x
    at hcanonical
  change D.canonicalDefectFactor n
      (D.inverseLimitDescent x) =
    Group.cSQuotie.finiteDefectProjection
      D.ZassenhausRelatorSystem
      D.inverseLimitDescent
      D.limit_projection_surjective
      n x at hdefect
  change D.canonicalDefectTheorem hfactor n
      (D.kochCanonicalTheorem hfactor n
        (D.inverseLimitDescent x)) =
    D.canonicalDefectFactor n
      (D.inverseLimitDescent x)
  rw [hcanonical, hdefect]
  change D.canonicalDefectTheorem hfactor n
      (Group.inverseLimitProjection D.ZassenhausRelatorSystem n x) =
    D.canonicalKochDefect n
      (Group.inverseLimitProjection D.ZassenhausRelatorSystem n x)
  exact congrArg
    (fun ψ : D.ZassenhausRelatorSystem.obj n →*
        D.CanonicalKochDefect n =>
      ψ (Group.inverseLimitProjection D.ZassenhausRelatorSystem n x))
    (Group.cSQuotie.defect_bot_monoid
      D.ZassenhausRelatorSystem
      D.inverseLimitDescent
      D.limit_projection_surjective
      n
      ((D.forall_defect_bot.mp
        hfactor) n))

end KRData

end TBluepr
end Submission
