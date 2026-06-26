import Submission.FieldTheory.FiniteDefect.RawQuotientBasis
import Submission.FieldTheory.QuotientKoch.CanonicalDescent
import Submission.Group.FiniteQuotientTower.SeparatedCompletion


open scoped Pointwise Topology commutatorElement

noncomputable section

namespace Submission
namespace TBluepr

open KPScaffo
open IGScaffo
open IRScaffo
open PCShadow
open PRFact
open PRQuotie
open RSFact
open TFFact

private instance initialThreeFact : Fact (Nat.Prime 3) :=
  ⟨Nat.prime_three⟩

namespace KRData
namespace CSCone

/--
The raw quotient shadow family kernel is the ambient kernel of the raw cone's
finite-level quotient maps.
-/
lemma shadow_family_ambient
    (D : KRData)
    (C : D.CSCone) :
    C.ShadowFamilyKernel D =
      D.ZassenhausRelatorSystem.ambientKernel C.factor := rfl

/--
The inverse-limit lift attached to a quotient-valued raw Zassenhaus cone.
-/
def quotientLimitLift
    (D : KRData)
    (C : D.CSCone) :
    initialGaloisGroup →* D.RelatorInverseLimit :=
  C.toCRCone.inverseLimitLift D

/--
Every coordinate of the raw quotient inverse-limit lift is the corresponding
raw quotient factor from the actual initial Galois group.
-/
lemma limit_lift_coordinate
    (D : KRData)
    (C : D.CSCone)
    (n : ℕ) :
    (Group.inverseLimitProjection D.ZassenhausRelatorSystem n).comp
        (C.quotientLimitLift D) =
      C.factor n := by
  exact C.toCRCone.inverse_limit_coordinate
    D
    n

/--
The raw quotient inverse-limit lift descends the ambient canonical relator
quotient completion map through the actual initial Koch quotient.
-/
lemma limit_lift_comp
    (D : KRData)
    (C : D.CSCone) :
    (C.quotientLimitLift D).comp initialKochQuotient =
      D.zassenhausRelatorCompletion := by
  exact
    C.toCRCone.inverse_limit_lift
    D

/--
The kernel of the raw quotient inverse-limit lift is exactly the common kernel
of the raw quotient shadows of the actual initial Galois group.
-/
lemma limit_shadow_family
    (D : KRData)
    (C : D.CSCone) :
    (C.quotientLimitLift D).ker =
      C.ShadowFamilyKernel D := by
  rw [quotientLimitLift]
  calc
    (C.toCRCone.inverseLimitLift D).ker =
        D.ZassenhausRelatorSystem.ambientKernel C.factor := by
      exact D.RelatorTopologicalSystem.inverse_limit_ambient
        C.factor
        (fun hnm => C.transition_comp_factor D hnm)
    _ = C.ShadowFamilyKernel D :=
      (C.shadow_family_ambient D).symm

/--
An actual initial Galois element dies in the raw quotient inverse limit exactly
when every raw quotient stage kills it.
-/
lemma limit_lift_kernel
    (D : KRData)
    (C : D.CSCone)
    (y : initialGaloisGroup) :
    y ∈ (C.quotientLimitLift D).ker ↔
      ∀ n : ℕ, C.factor n y = 1 := by
  rw [C.limit_shadow_family D,
    C.shadow_family_ambient D]
  exact D.ZassenhausRelatorSystem.mem_ambient_iff
    C.factor
    y

/--
The raw quotient inverse-limit lift is continuous because its raw quotient
coordinates are continuous.
-/
lemma limit_lift_continuous
    (D : KRData)
    (C : D.CSCone) :
    Continuous (C.quotientLimitLift D) := by
  exact D.RelatorTopologicalSystem.inverse_lift_continuous
    C.factor
    C.factor_continuous
    (fun hnm => C.transition_comp_factor D hnm)

/--
The raw quotient inverse-limit lift is onto because the actual initial Galois
group is compact and every raw quotient coordinate is onto.
-/
lemma limit_lift_surjective
    (D : KRData)
    (C : D.CSCone) :
    Function.Surjective (C.quotientLimitLift D) := by
  exact D.RelatorTopologicalSystem.limit_compact_space
    C.factor
    C.factor_continuous
    C.factor_surjective
    (fun hnm => C.transition_comp_factor D hnm)

/--
The raw quotient inverse-limit lift is injective because the raw quotient
shadow family is kernel-cofinal in the residually finite `3` actual group.
-/
lemma limit_lift_injective
    (D : KRData)
    (C : D.CSCone) :
    Function.Injective (C.quotientLimitLift D) := by
  apply (MonoidHom.ker_eq_bot_iff (C.quotientLimitLift D)).mp
  rw [C.limit_shadow_family D]
  exact C.shadow_family_bot D

/--
Every quotient-valued raw Zassenhaus cone reconstructs the actual initial
Galois group as the raw canonical relator quotient inverse limit.
-/
def inverseLimitContinuous
    (D : KRData)
    (C : D.CSCone) :
    initialGaloisGroup ≃ₜ*
      D.RelatorInverseLimit :=
  D.RelatorTopologicalSystem.continuousAmbientBot
    C.factor
    C.factor_continuous
    C.factor_surjective
    (fun hnm => C.transition_comp_factor D hnm)
    (by
      change D.ZassenhausRelatorSystem.ambientKernel C.factor = ⊥
      rw [← C.shadow_family_ambient D]
      exact C.shadow_family_bot D)

@[simp]
lemma limit_continuous_monoid
    (D : KRData)
    (C : D.CSCone) :
    (C.inverseLimitContinuous D).toMulEquiv.toMonoidHom =
      C.quotientLimitLift D := rfl

/--
The raw quotient inverse-limit equivalence still descends the ambient canonical
completion map through the actual initial Koch quotient.
-/
lemma limit_continuous_comp
    (D : KRData)
    (C : D.CSCone) :
    (C.inverseLimitContinuous D).toMulEquiv.toMonoidHom.comp
        initialKochQuotient =
      D.zassenhausRelatorCompletion := by
  exact C.limit_lift_comp D

/--
Under the desired theorem, every quotient-valued raw Zassenhaus cone gives the
same inverse-limit comparison map as the previously constructed canonical one.
-/
lemma limit_comparison_theorem
    (D : KRData)
    (C : D.CSCone)
    (hfactor : D.KochFactorizationTheorem) :
    C.quotientLimitLift D =
      (D.limitContinuousTheorem
        hfactor).toMulEquiv.toMonoidHom := by
  apply MonoidHom.ext
  intro y
  rcases initial_quotient_surjective y with ⟨x, rfl⟩
  have hcone := congrArg
    (fun φ : initialKochFree.Carrier →*
        D.RelatorInverseLimit => φ x)
    (C.limit_lift_comp D)
  have hcanonical := congrArg
    (fun φ : initialKochFree.Carrier →*
        D.RelatorInverseLimit => φ x)
    (D.limit_theorem_comp
      hfactor)
  exact hcone.trans hcanonical.symm

/--
The quotient-basis inverse-limit equivalence recovers the earlier canonical
inverse-limit equivalence under the desired theorem.
-/
lemma limit_continuous_theorem
    (D : KRData)
    (C : D.CSCone)
    (hfactor : D.KochFactorizationTheorem) :
    C.inverseLimitContinuous D =
      D.limitContinuousTheorem
        hfactor := by
  apply ContinuousMulEquiv.ext
  intro y
  exact DFunLike.congr_fun
    (C.limit_comparison_theorem
      D
      hfactor)
    y

/--
The unconditional canonical inverse-limit descent is a left inverse to every
raw quotient inverse-limit lift.
-/
lemma limit_descent_lift
    (D : KRData)
    (C : D.CSCone) :
    D.inverseLimitDescent.comp
        (C.quotientLimitLift D) =
      MonoidHom.id initialGaloisGroup := by
  apply MonoidHom.ext
  intro y
  rcases initial_quotient_surjective y with ⟨x, rfl⟩
  have hlift := congrArg
    (fun φ : initialKochFree.Carrier →*
        D.RelatorInverseLimit => φ x)
    (C.limit_lift_comp D)
  have hdescent := congrArg
    (fun φ : initialKochFree.Carrier →* initialGaloisGroup => φ x)
    D.limit_descent_comp
  change C.quotientLimitLift D (initialKochQuotient x) =
    D.zassenhausRelatorCompletion x at hlift
  change D.inverseLimitDescent
      (D.zassenhausRelatorCompletion x) =
    initialKochQuotient x at hdescent
  change D.inverseLimitDescent
      (C.quotientLimitLift D (initialKochQuotient x)) =
    initialKochQuotient x
  rw [hlift, hdescent]

/--
The unconditional canonical inverse-limit descent is also a right inverse to
every raw quotient inverse-limit lift.
-/
lemma limit_lift_descent
    (D : KRData)
    (C : D.CSCone) :
    (C.quotientLimitLift D).comp
        D.inverseLimitDescent =
      MonoidHom.id D.RelatorInverseLimit := by
  apply MonoidHom.ext
  intro z
  rcases C.limit_lift_surjective D z with ⟨y, rfl⟩
  have hdescent := DFunLike.congr_fun
    (C.limit_descent_lift D)
    y
  change D.inverseLimitDescent
      (C.quotientLimitLift D y) =
    y at hdescent
  change C.quotientLimitLift D
      (D.inverseLimitDescent
        (C.quotientLimitLift D y)) =
    C.quotientLimitLift D y
  rw [hdescent]

/--
The inverse of the quotient-basis inverse-limit equivalence is exactly the
unconditional canonical inverse-limit descent.
-/
lemma limit_monoid_descent
    (D : KRData)
    (C : D.CSCone) :
    (C.inverseLimitContinuous D).symm.toMulEquiv.toMonoidHom =
      D.inverseLimitDescent := by
  apply MonoidHom.ext
  intro z
  rcases C.limit_lift_surjective D z with ⟨y, rfl⟩
  have hto := DFunLike.congr_fun
    (C.limit_continuous_monoid D)
    y
  have hdescent := DFunLike.congr_fun
    (C.limit_descent_lift D)
    y
  change (C.inverseLimitContinuous D) y =
    C.quotientLimitLift D y at hto
  change D.inverseLimitDescent
      (C.quotientLimitLift D y) =
    y at hdescent
  change (C.inverseLimitContinuous D).symm
      (C.quotientLimitLift D y) =
    D.inverseLimitDescent
      (C.quotientLimitLift D y)
  calc
    (C.inverseLimitContinuous D).symm
        (C.quotientLimitLift D y) =
        (C.inverseLimitContinuous D).symm
          ((C.inverseLimitContinuous D) y) := by
          rw [hto]
    _ = y :=
      (C.inverseLimitContinuous D).symm_apply_apply y
    _ = D.inverseLimitDescent
        (C.quotientLimitLift D y) := hdescent.symm

/--
Any finite quotient of the actual initial Galois group that factors through one
raw quotient stage transports across the raw inverse-limit equivalence to a
finite quotient factoring through the corresponding inverse-limit projection.
-/
lemma surjec_conti_trans
    (D : KRData)
    (C : D.CSCone)
    (S : InitialKochQuotient)
    (n : ℕ)
    (hfactor : SFThroug (C.factor n) S.map) :
    SFThroug
      (Group.inverseLimitProjection D.ZassenhausRelatorSystem n)
      (S.map.comp
        (C.inverseLimitContinuous D).symm.toMulEquiv.toMonoidHom) := by
  rcases hfactor with ⟨β, hβcontinuous, hβsurjective, hβ⟩
  refine ⟨β, hβcontinuous, hβsurjective, ?_⟩
  apply MonoidHom.ext
  intro z
  rcases (C.inverseLimitContinuous D).surjective z with ⟨y, rfl⟩
  have hcoordinate := DFunLike.congr_fun
    (C.limit_lift_coordinate D n)
    y
  have hto := DFunLike.congr_fun
    (C.limit_continuous_monoid D)
    y
  have hβy := DFunLike.congr_fun hβ y
  change Group.inverseLimitProjection D.ZassenhausRelatorSystem n
      (C.quotientLimitLift D y) =
    C.factor n y at hcoordinate
  change (C.inverseLimitContinuous D) y =
    C.quotientLimitLift D y at hto
  change β (C.factor n y) = S.map y at hβy
  change β
      (Group.inverseLimitProjection D.ZassenhausRelatorSystem n
        ((C.inverseLimitContinuous D) y)) =
    S.map ((C.inverseLimitContinuous D).symm
      ((C.inverseLimitContinuous D) y))
  rw [hto, hcoordinate, hβy, ← hto,
    (C.inverseLimitContinuous D).symm_apply_apply]

/--
Every actual finite `3` quotient of the actual initial Galois group transports
to a quotient of one finite coordinate projection from the raw canonical
relator quotient inverse limit.
-/
lemma inverse_limit_projection
    (D : KRData)
    (C : D.CSCone)
    (S : InitialKochQuotient) :
    ∃ n : ℕ,
      SFThroug
        (Group.inverseLimitProjection D.ZassenhausRelatorSystem n)
        (S.map.comp
          (C.inverseLimitContinuous D).symm.toMulEquiv.toMonoidHom) := by
  rcases C.factor_surje_conti
      D
      S with
    ⟨n, hn⟩
  exact ⟨n, C.surjec_conti_trans
    D
    S
    n
    hn⟩

/--
A finite family of actual finite `3` quotients of the actual initial Galois
group transports to quotients of one common finite coordinate projection from
the raw canonical relator quotient inverse limit.
-/
lemma
  surjectively_continuously_through
    (D : KRData)
    (C : D.CSCone)
    (𝒮 : Finset InitialKochQuotient) :
    ∃ n : ℕ,
      ∀ S ∈ 𝒮,
        SFThroug
          (Group.inverseLimitProjection D.ZassenhausRelatorSystem n)
          (S.map.comp
            (C.inverseLimitContinuous D).symm.toMulEquiv.toMonoidHom) := by
  rcases C.surjec_conti_famil
      D
      𝒮 with
    ⟨n, hn⟩
  refine ⟨n, ?_⟩
  intro S hS
  exact C.surjec_conti_trans
    D
    S
    n
    (hn S hS)

end CSCone
end KRData

end TBluepr
end Submission
