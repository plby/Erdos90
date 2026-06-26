import Towers.FieldTheory.FiniteDefect.Separation
import Towers.Group.FiniteQuotientTower.Equiv


open scoped Pointwise Topology commutatorElement

noncomputable section

namespace Towers
namespace TBluepr

open KPScaffo
open IGScaffo
open IRScaffo
open PCShadow
open PRFact
open ONCompar

private instance initialThreeFact : Fact (Nat.Prime 3) :=
  ⟨Nat.prime_three⟩

namespace KRData

/--
The finite-level equivalences from canonical finite defect quotients to honest
finite kernel-image quotients commute with every transition map, hence form a
compatible equivalence of finite quotient towers.
-/
def kochDefectSystem
    (D : KRData) :
    Group.cSQuotie.CMEquiv
      D.CanonicalDefectSystem
      InitialKochSystem where
  equiv := D.canonicalDefectImage
  equiv_comm := fun hnm =>
    D.kochCommutesTransition
      hnm

/--
The inverse limit of canonical finite defect quotient shadows is canonically
equivalent to the inverse limit of the honest finite kernel-image quotients.
-/
def kochDefectLimit
    (D : KRData) :
    Group.inverseLimit D.CanonicalDefectSystem ≃*
      InitialKochLimit :=
  D.kochDefectSystem.inverseLimitEquiv

/--
The inverse-limit equivalence is induced by applying the finite-level
defect/image equivalences coordinatewise.
-/
lemma kochLimitMonoid
    (D : KRData) :
    D.kochDefectLimit.toMonoidHom =
      D.kochDefectSystem.inverseLimitMap := by
  rfl

/--
At every finite depth, the inverse-limit defect/image equivalence is exactly
the finite-level defect/image equivalence on the corresponding coordinate.
-/
lemma kochLimitCoord
    (D : KRData)
    (n : ℕ) :
    (Group.inverseLimitProjection InitialKochSystem n).comp
        D.kochDefectLimit.toMonoidHom =
      (D.canonicalDefectImage
        n).toMonoidHom.comp
        (Group.inverseLimitProjection D.CanonicalDefectSystem n) := by
  exact D.kochDefectSystem.limitProjectionMonoid
    n

/--
The global defect/image inverse-limit equivalence carries the canonical finite
defect comparison map from the actual Galois group to the honest finite
kernel-image comparison map.
-/
lemma kochLimitComparison
    (D : KRData) :
    D.kochDefectLimit.toMonoidHom.comp
        D.kochDefectComparison =
      initialImageComparison := by
  apply MonoidHom.ext
  intro g
  apply Subtype.ext
  funext n
  have hglobal := DFunLike.congr_fun
    (D.kochLimitCoord
      n)
    (D.kochDefectComparison g)
  have hdefect := DFunLike.congr_fun
    (D.defect_comparison_coordinate n)
    g
  have hactual := DFunLike.congr_fun
    (initial_comparison_coordinate n)
    g
  have hfactor := DFunLike.congr_fun
    (D.defect_comp_factor
      n)
    g
  change Group.inverseLimitProjection InitialKochSystem n
      (D.kochDefectLimit
        (D.kochDefectComparison g)) =
    D.canonicalDefectImage n
      (Group.inverseLimitProjection D.CanonicalDefectSystem n
        (D.kochDefectComparison g)) at hglobal
  change Group.inverseLimitProjection D.CanonicalDefectSystem n
      (D.kochDefectComparison g) =
    D.canonicalDefectFactor n g at hdefect
  change Group.inverseLimitProjection InitialKochSystem n
      (initialImageComparison g) =
    initialKochFactor n g at hactual
  change D.canonicalDefectImage n
      (D.canonicalDefectFactor n g) =
    initialKochFactor n g at hfactor
  change Group.inverseLimitProjection InitialKochSystem n
      (D.kochDefectLimit
        (D.kochDefectComparison g)) =
    Group.inverseLimitProjection InitialKochSystem n
      (initialImageComparison g)
  rw [hglobal, hdefect, hfactor, hactual]

/--
The canonical defect/image inverse-limit equivalence is a continuous
isomorphism: through the actual Galois group it is the composite of the two
unconditional profinite completion identifications.
-/
def kochFinLimit
    (D : KRData) :
    Group.inverseLimit D.CanonicalDefectSystem ≃ₜ*
      InitialKochLimit :=
  D.defectComparisonContinuous.symm.trans
    D.initialComparisonContinuous

/--
The continuous defect/image inverse-limit equivalence is the same canonical
coordinatewise equivalence of inverse limits constructed from the finite
levels.
-/
lemma defectLimitMonoid
    (D : KRData) :
    D.kochFinLimit.toMulEquiv.toMonoidHom =
      D.kochDefectLimit.toMonoidHom := by
  apply MonoidHom.ext
  intro x
  rcases D.canonical_comparison_surjective x with ⟨g, rfl⟩
  have htransport := DFunLike.congr_fun
    (D.kochLimitComparison)
    g
  change initialImageComparison
      (D.canonicalDefectComparison.symm
        (D.kochDefectComparison g)) =
    D.kochDefectLimit
      (D.kochDefectComparison g)
  rw [← D.defect_comparison_monoid]
  change initialImageComparison
      (D.canonicalDefectComparison.symm
        (D.canonicalDefectComparison g)) =
    D.kochDefectLimit
      (D.canonicalDefectComparison g)
  rw [MulEquiv.symm_apply_apply]
  exact htransport.symm

/--
The older canonical relator-vs-kernel image comparisons already commute with
the canonical relator quotient transitions and the honest finite kernel-image
quotient transitions.
-/
lemma comparison_commutes_transition
    (D : KRData)
    {n m : ℕ}
    (hnm : n ≤ m) :
    (D.relatorImageComparison n).comp
        (D.ZassenhausRelatorSystem.map hnm) =
      (InitialKochSystem.map hnm).comp
        (D.relatorImageComparison m) := by
  apply MonoidHom.ext
  intro y
  rcases (D.ZassenhausRelatorQuotient m).map_surjective y with ⟨x, rfl⟩
  have hrelator := DFunLike.congr_fun
    (D.relator_transition_comp hnm)
    x
  have hactual := DFunLike.congr_fun
    (initial_koch_comp hnm)
    x
  have hn := DFunLike.congr_fun
    (D.image_comparison_comp
      n)
    x
  have hm := DFunLike.congr_fun
    (D.image_comparison_comp
      m)
    x
  change D.ZassenhausRelatorSystem.map hnm
      ((D.ZassenhausRelatorQuotient m).map x) =
    (D.ZassenhausRelatorQuotient n).map x at hrelator
  change InitialKochSystem.map hnm
      (initialKochImage m x) =
    initialKochImage n x at hactual
  change D.relatorImageComparison n
      ((D.ZassenhausRelatorQuotient n).map x) =
    initialKochImage n x at hn
  change D.relatorImageComparison m
      ((D.ZassenhausRelatorQuotient m).map x) =
    initialKochImage m x at hm
  change D.relatorImageComparison n
      (D.ZassenhausRelatorSystem.map hnm
        ((D.ZassenhausRelatorQuotient m).map x)) =
    InitialKochSystem.map hnm
      (D.relatorImageComparison m
        ((D.ZassenhausRelatorQuotient m).map x))
  rw [hrelator, hn, hm, hactual]

/--
Under the desired finite quotient Koch theorem, every canonical relator
quotient layer is already the corresponding honest finite kernel-image
quotient.
-/
def imageComparisonTheorem
    (D : KRData)
    (hfactor : D.KochFactorizationTheorem)
    (n : ℕ) :
    D.ZassenhausRelatorSystem.obj n ≃*
      InitialKochImage n :=
  MulEquiv.ofBijective
    (D.relatorImageComparison n)
    ⟨(MonoidHom.ker_eq_bot_iff
        (D.relatorImageComparison n)).mp
        ((D.forall_comparison_bot.mp
          hfactor)
          n),
      ONCompar.relator_comparison_surjective
        initialKochQuotient
        (initialTameRelator D.frobeniusLift)
        (zassenhausOpenSubgroup n)
        D.tameRelatorsKilled⟩

/--
The theorem-level relator/kernel-image equivalence is induced by the older
canonical relator-vs-kernel image comparison.
-/
lemma comparison_theorem_monoid
    (D : KRData)
    (hfactor : D.KochFactorizationTheorem)
    (n : ℕ) :
    (D.imageComparisonTheorem hfactor
        n).toMonoidHom =
      D.relatorImageComparison n := by
  rfl

/--
Under the desired theorem, the uncorrected canonical relator quotient tower
is compatibly equivalent to the honest finite kernel-image quotient tower.
-/
def finImageSystem
    (D : KRData)
    (hfactor : D.KochFactorizationTheorem) :
    Group.cSQuotie.CMEquiv
      D.ZassenhausRelatorSystem
      InitialKochSystem where
  equiv := D.imageComparisonTheorem hfactor
  equiv_comm := D.comparison_commutes_transition

/--
Under the desired theorem, the canonical relator quotient inverse limit is
canonically equivalent to the honest finite kernel-image quotient inverse
limit without first dividing by finite defects.
-/
def finKochLimit
    (D : KRData)
    (hfactor : D.KochFactorizationTheorem) :
    Group.inverseLimit D.ZassenhausRelatorSystem ≃*
      InitialKochLimit :=
  (D.finImageSystem
    hfactor).inverseLimitEquiv

/--
The theorem-level relator/kernel-image inverse-limit equivalence carries the
canonical relator quotient completion map to the honest actual finite quotient
comparison map after the actual Koch quotient.
-/
lemma finCompCompletion
    (D : KRData)
    (hfactor : D.KochFactorizationTheorem) :
    (D.finKochLimit
        hfactor).toMonoidHom.comp
        D.zassenhausRelatorCompletion =
      initialImageComparison.comp
        initialKochQuotient := by
  apply MonoidHom.ext
  intro x
  apply Subtype.ext
  funext n
  have hglobal := DFunLike.congr_fun
    ((D.finImageSystem
      hfactor).limitProjectionMonoid n)
    (D.zassenhausRelatorCompletion x)
  have hrelator := DFunLike.congr_fun
    (D.zassenhaus_relator_coordinate n)
    x
  have hcomparison := DFunLike.congr_fun
    (D.image_comparison_comp
      n)
    x
  have hactual := DFunLike.congr_fun
    (initial_comparison_coordinate n)
    (initialKochQuotient x)
  have hfiniteFactor := DFunLike.congr_fun
    (initial_image_comp n)
    x
  change Group.inverseLimitProjection InitialKochSystem n
      (D.finKochLimit
        hfactor
        (D.zassenhausRelatorCompletion x)) =
    D.relatorImageComparison n
      (Group.inverseLimitProjection D.ZassenhausRelatorSystem n
        (D.zassenhausRelatorCompletion x)) at hglobal
  change Group.inverseLimitProjection D.ZassenhausRelatorSystem n
      (D.zassenhausRelatorCompletion x) =
    (D.ZassenhausRelatorQuotient n).map x at hrelator
  change D.relatorImageComparison n
      ((D.ZassenhausRelatorQuotient n).map x) =
    initialKochImage n x at hcomparison
  change Group.inverseLimitProjection InitialKochSystem n
      (initialImageComparison
        (initialKochQuotient x)) =
    initialKochFactor n (initialKochQuotient x) at hactual
  change initialKochFactor n
      (initialKochQuotient x) =
    initialKochImage n x at hfiniteFactor
  change Group.inverseLimitProjection InitialKochSystem n
      (D.finKochLimit
        hfactor
        (D.zassenhausRelatorCompletion x)) =
    Group.inverseLimitProjection InitialKochSystem n
      (initialImageComparison
        (initialKochQuotient x))
  rw [hglobal, hrelator, hcomparison, hactual, hfiniteFactor]

/--
Under the desired theorem, the theorem-level relator/kernel-image
inverse-limit equivalence is continuously the canonical descent to the actual
Galois group followed by the honest finite quotient completion equivalence.
-/
def finInverseLimit
    (D : KRData)
    (hfactor : D.KochFactorizationTheorem) :
    Group.inverseLimit D.ZassenhausRelatorSystem ≃ₜ*
      InitialKochLimit :=
  D.limitDescentTheorem
      hfactor |>.trans
    D.initialComparisonContinuous

/--
The continuous theorem-level relator/kernel-image inverse-limit equivalence
is the same coordinatewise inverse-limit equivalence induced from the finite
levels.
-/
lemma finMonoidHom
    (D : KRData)
    (hfactor : D.KochFactorizationTheorem) :
    (D.finInverseLimit
        hfactor).toMulEquiv.toMonoidHom =
      (D.finKochLimit
        hfactor).toMonoidHom := by
  apply MonoidHom.ext
  intro y
  rcases D.zassenhaus_relator_surjective y with ⟨x, rfl⟩
  have hdescent := DFunLike.congr_fun
    (D.limit_descent_theorem
      hfactor)
    x
  have htransport := DFunLike.congr_fun
    (D.finCompCompletion
      hfactor)
    x
  change initialImageComparison
      (D.limitDescentTheorem
        hfactor
        (D.zassenhausRelatorCompletion x)) =
    D.finKochLimit
      hfactor
      (D.zassenhausRelatorCompletion x)
  change D.limitDescentTheorem
      hfactor
      (D.zassenhausRelatorCompletion x) =
    initialKochQuotient x at hdescent
  rw [hdescent]
  exact htransport.symm

end KRData

end TBluepr
end Towers
