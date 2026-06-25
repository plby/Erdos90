import Submission.FieldTheory.QuotientKoch.ProfiniteCompletion
import Submission.Group.FiniteProfiniteResidual


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
open RRQuot

private instance initialThreeFact : Fact (Nat.Prime 3) :=
  ⟨Nat.prime_three⟩

namespace KRData

/--
The actual initial Galois group is residually finite `3` for the continuous
finite discrete `3`-group shadow theory.
-/
lemma initial_galois_residually :
    RFP 3 initialGaloisGroup := by
  exact residually_pro_group initial_pro_three

/--
Every element invisible in all finite tame Koch relator `3`-shadows already
dies in the actual initial Koch quotient.
-/
lemma relator_koch_quotient
    (D : KRData) :
    relatorKernel 3 (initialTameRelator D.frobeniusLift) ≤
      initialKochQuotient.ker := by
  exact RRQuot.PQuot.relator_residually_target
    (initialTameRelator D.frobeniusLift)
    D.fiveRelatorPresented
    initial_galois_residually

/--
The desired finite quotient Koch theorem is the missing reverse containment in
the actual quotient kernel equality.
-/
lemma factorization_theorem_relator
    (D : KRData) :
    D.KochFactorizationTheorem ↔
      initialKochQuotient.ker =
        relatorKernel 3 (initialTameRelator D.frobeniusLift) := by
  constructor
  · intro hfactor
    apply le_antisymm
    · exact D.factorization_statement_relator.mp
        (D.factorization_theorem_statement.mp hfactor)
    · exact D.relator_koch_quotient
  · intro hkernel
    apply D.factorization_theorem_statement.mpr
    apply D.factorization_statement_relator.mpr
    rw [hkernel]

/--
The canonical relator quotient inverse-limit kernel is always contained in the
actual initial Koch kernel.
-/
lemma relator_initial_koch
    (D : KRData) :
    D.zassenhausRelatorCompletion.ker ≤
      initialKochQuotient.ker := by
  rw [D.relator_completion_kernel]
  exact D.relator_koch_quotient

/--
Equivalently, the desired finite quotient Koch theorem says that the actual
initial Koch kernel is exactly the canonical relator quotient inverse-limit
kernel.
-/
lemma fin_factorization_completion
    (D : KRData) :
    D.KochFactorizationTheorem ↔
      initialKochQuotient.ker =
        D.zassenhausRelatorCompletion.ker := by
  rw [D.factorization_theorem_relator,
    D.relator_completion_kernel]

/--
Under the desired finite quotient Koch theorem, the canonical residual
projection from the actual initial Galois group is injective as well as
surjective.
-/
lemma projection_theorem_injective
    (D : KRData)
    (hfactor : D.KochFactorizationTheorem) :
    Function.Injective (D.residualProjectionTheorem hfactor) := by
  apply (MonoidHom.ker_eq_bot_iff
    (D.residualProjectionTheorem hfactor)).mp
  apply le_antisymm
  · intro y hy
    rw [Subgroup.mem_bot]
    rcases initial_quotient_surjective y with
      ⟨x, rfl⟩
    have hxProjection :
        D.residualProjectionTheorem hfactor
            (initialKochQuotient x) = 1 :=
      MonoidHom.mem_ker.mp hy
    have hcomp := congrArg
      (fun φ : initialKochFree.Carrier →*
          relatorResidualQuotient
            (p := 3) (initialTameRelator D.frobeniusLift) =>
        φ x)
      (D.koch_projection_theorem hfactor)
    change D.residualProjectionTheorem hfactor
        (initialKochQuotient x) =
      residualQuotientMap (p := 3) (initialTameRelator D.frobeniusLift) x at hcomp
    have hxResidual :
        residualQuotientMap (p := 3) (initialTameRelator D.frobeniusLift) x = 1 :=
      hcomp.symm.trans hxProjection
    have hxRelator :
        x ∈ relatorKernel 3 (initialTameRelator D.frobeniusLift) := by
      have hxResidualKernel :
          x ∈ (residualQuotientMap
            (p := 3) (initialTameRelator D.frobeniusLift)).ker :=
        MonoidHom.mem_ker.mpr hxResidual
      simpa using hxResidualKernel
    have hxKernel : x ∈ initialKochQuotient.ker := by
      rw [D.factorization_theorem_relator.mp hfactor]
      exact hxRelator
    exact MonoidHom.mem_ker.mp hxKernel
  · exact bot_le

/--
Under the desired finite quotient Koch theorem, the canonical residual
projection from the actual initial Galois group is continuous.
-/
lemma projection_theorem_continuous
    (D : KRData)
    (hfactor : D.KochFactorizationTheorem) :
    Continuous (D.residualProjectionTheorem hfactor) := by
  have hkernel :
      initialKochQuotient.ker ≤
        (residualQuotientMap
          (p := 3) (initialTameRelator D.frobeniusLift)).ker := by
    rw [ker_residual_quotient]
    exact D.factorization_statement_relator.mp
      (D.factorization_theorem_statement.mp hfactor)
  simpa [residualProjectionTheorem] using
    (RCFact.factor_surjective_continuous
      initialKochQuotient
      (residualQuotientMap (p := 3) (initialTameRelator D.frobeniusLift))
      initial_koch
      (residual_quotient_continuous (p := 3) (initialTameRelator D.frobeniusLift))
      hkernel)

/--
Under the desired finite quotient Koch theorem, the canonical residual
projection from the actual initial Galois group is a homeomorphism.
-/
lemma projection_theorem_homeomorph
    (D : KRData)
    (hfactor : D.KochFactorizationTheorem) :
    IsHomeomorph (D.residualProjectionTheorem hfactor) := by
  apply isHomeomorph_iff_continuous_bijective.mpr
  exact ⟨D.projection_theorem_continuous hfactor,
    ⟨D.projection_theorem_injective hfactor,
      D.projection_theorem_surjective hfactor⟩⟩

/--
Under the desired finite quotient Koch theorem, the actual initial Galois
group is canonically isomorphic to the finite-`3` tame Koch relator residual
quotient.
-/
def kochProjectionTheorem
    (D : KRData)
    (hfactor : D.KochFactorizationTheorem) :
    initialGaloisGroup ≃*
      relatorResidualQuotient
        (p := 3) (initialTameRelator D.frobeniusLift) :=
  MulEquiv.ofBijective
    (D.residualProjectionTheorem hfactor)
    ⟨D.projection_theorem_injective hfactor,
      D.projection_theorem_surjective hfactor⟩

@[simp] lemma projection_theorem_monoid
    (D : KRData)
    (hfactor : D.KochFactorizationTheorem) :
    (D.kochProjectionTheorem hfactor).toMonoidHom =
      D.residualProjectionTheorem hfactor := rfl

/--
The residual quotient isomorphism descends the ambient relator residual
quotient map.
-/
lemma projection_theorem_comp
    (D : KRData)
    (hfactor : D.KochFactorizationTheorem) :
    (D.kochProjectionTheorem hfactor).toMonoidHom.comp
        initialKochQuotient =
      residualQuotientMap (p := 3) (initialTameRelator D.frobeniusLift) := by
  exact D.koch_projection_theorem hfactor

/--
Under the desired finite quotient Koch theorem, the actual initial Galois
group and the finite-`3` tame Koch relator residual quotient are canonically
continuously isomorphic.
-/
def projectionContinuousTheorem
    (D : KRData)
    (hfactor : D.KochFactorizationTheorem) :
    initialGaloisGroup ≃ₜ*
      relatorResidualQuotient
        (p := 3) (initialTameRelator D.frobeniusLift) where
  toMulEquiv :=
    D.kochProjectionTheorem hfactor
  continuous_toFun :=
    D.projection_theorem_continuous hfactor
  continuous_invFun := by
    let e := D.kochProjectionTheorem hfactor
    have hcontinuous :
        Continuous
          (e : initialGaloisGroup →
            relatorResidualQuotient
              (p := 3) (initialTameRelator D.frobeniusLift)) := by
      change Continuous (D.residualProjectionTheorem hfactor)
      exact D.projection_theorem_continuous hfactor
    exact hcontinuous.continuous_symm_of_equiv_compact_to_t2

/--
Under the desired finite quotient Koch theorem, the actual initial Galois
group is canonically isomorphic to the canonical Zassenhaus finite-layer
relator quotient inverse limit.
-/
def kochLimitTheorem
    (D : KRData)
    (hfactor : D.KochFactorizationTheorem) :
    initialGaloisGroup ≃* D.RelatorInverseLimit :=
  (D.kochProjectionTheorem hfactor).trans
    D.relatorInverseLimit

/--
The canonical inverse-limit isomorphism descends the ambient canonical
completion map.
-/
lemma koch_theorem_comp
    (D : KRData)
    (hfactor : D.KochFactorizationTheorem) :
    (D.kochLimitTheorem hfactor).toMonoidHom.comp
        initialKochQuotient =
      D.zassenhausRelatorCompletion := by
  change D.relatorInverseLimit.toMonoidHom.comp
      ((D.kochProjectionTheorem hfactor).toMonoidHom.comp
        initialKochQuotient) =
    D.zassenhausRelatorCompletion
  rw [D.projection_theorem_comp,
    D.relatorResidualComp]

/--
Under the desired finite quotient Koch theorem, the actual initial Galois
group and the canonical Zassenhaus finite-layer relator quotient inverse limit
are canonically continuously isomorphic.
-/
def limitContinuousTheorem
    (D : KRData)
    (hfactor : D.KochFactorizationTheorem) :
    initialGaloisGroup ≃ₜ* D.RelatorInverseLimit :=
  (D.projectionContinuousTheorem hfactor).trans
    D.relatorContinuousLimit

/--
The canonical continuous inverse-limit isomorphism descends the ambient
canonical completion map.
-/
lemma limit_theorem_comp
    (D : KRData)
    (hfactor : D.KochFactorizationTheorem) :
    (D.limitContinuousTheorem
      hfactor).toMulEquiv.toMonoidHom.comp
        initialKochQuotient =
      D.zassenhausRelatorCompletion := by
  exact D.koch_theorem_comp hfactor

/--
The theorem-induced canonical inverse-limit comparison map is bijective, not
merely surjective.
-/
lemma limit_theorem_bijective
    (D : KRData)
    (hfactor : D.KochFactorizationTheorem) :
    Function.Bijective
      (D.limitComparisonTheorem hfactor) := by
  change Function.Bijective
    (D.kochLimitTheorem hfactor).toMonoidHom
  exact (D.kochLimitTheorem hfactor).bijective

/--
Equivalently, the desired finite quotient Koch theorem is exactly the existence
of a compatible multiplicative equivalence from the actual initial Galois group
onto the canonical relator quotient inverse limit.
-/
lemma factorization_theorem_limit
    (D : KRData) :
    D.KochFactorizationTheorem ↔
      ∃ e : initialGaloisGroup ≃* D.RelatorInverseLimit,
        e.toMonoidHom.comp initialKochQuotient =
          D.zassenhausRelatorCompletion := by
  constructor
  · intro hfactor
    exact ⟨D.kochLimitTheorem hfactor,
      D.koch_theorem_comp hfactor⟩
  · rintro ⟨e, he⟩
    apply D.fin_koch_kernel.mpr
    exact ker_factors_through
      initialKochQuotient
      D.zassenhausRelatorCompletion
      ⟨e.toMonoidHom, he⟩

/--
Equivalently, the desired finite quotient Koch theorem is exactly the existence
of a compatible continuous multiplicative equivalence from the actual initial
Galois group onto the canonical relator quotient inverse limit.
-/
lemma fin_factorization_limit
    (D : KRData) :
    D.KochFactorizationTheorem ↔
      ∃ e : initialGaloisGroup ≃ₜ* D.RelatorInverseLimit,
        e.toMulEquiv.toMonoidHom.comp initialKochQuotient =
          D.zassenhausRelatorCompletion := by
  constructor
  · intro hfactor
    exact ⟨D.limitContinuousTheorem hfactor,
      D.limit_theorem_comp hfactor⟩
  · rintro ⟨e, he⟩
    apply D.factorization_theorem_limit.mpr
    exact ⟨e.toMulEquiv, he⟩

end KRData

end TBluepr
end Submission
