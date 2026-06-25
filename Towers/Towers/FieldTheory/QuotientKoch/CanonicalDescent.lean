import Towers.FieldTheory.QuotientKoch.CanonicalIdentification
import Towers.Group.FinitePRelator.ResidualDescent


open scoped Pointwise Topology commutatorElement

noncomputable section

namespace Towers
namespace TBluepr

open KPScaffo
open IGScaffo
open IRScaffo
open PRFact
open FPQuotie
open PRQuotie
open RCFact
open RRQuot
open RRDescen

private instance initialThreeFact : Fact (Nat.Prime 3) :=
  ⟨Nat.prime_three⟩

namespace KRData

/--
The universal finite-`3` tame Koch relator residual quotient, named at the
actual initial Koch presentation.
-/
abbrev TameKochRelator
    (D : KRData) :=
  relatorResidualQuotient
    (p := 3) (initialTameRelator D.frobeniusLift)

/--
The actual initial Galois group is always a quotient of the universal finite-`3`
tame Koch relator residual quotient.
-/
def finiteKochDescent
    (D : KRData) :
    D.TameKochRelator →*
      initialGaloisGroup :=
  Towers.RRDescen.PQuot.residualDescent
    (p := 3)
    D.fiveRelatorPresented
    initial_galois_residually

/--
Residual descent sends the universal residual class of an ambient free element
to its actual initial Koch quotient class.
-/
lemma koch_descent_comp
    (D : KRData) :
    D.finiteKochDescent.comp
        (residualQuotientMap
          (p := 3) (initialTameRelator D.frobeniusLift)) =
      initialKochQuotient := by
  exact Towers.RRDescen.PQuot.residualDescentComp
      (p := 3)
      D.fiveRelatorPresented
      initial_galois_residually

/--
The canonical residual descent to the actual initial Galois group is continuous.
-/
lemma koch_descent_continuous
    (D : KRData) :
    Continuous D.finiteKochDescent := by
  exact Towers.RRDescen.PQuot.residualDescent_continuous
    (p := 3)
    D.fiveRelatorPresented
    initial_galois_residually

/--
The canonical residual descent to the actual initial Galois group is onto.
-/
lemma koch_descent_surjective
    (D : KRData) :
    Function.Surjective D.finiteKochDescent := by
  exact Towers.RRDescen.PQuot.residualDescent_surjective
    (p := 3)
    D.fiveRelatorPresented
    initial_galois_residually

/--
The extra residual kernel is the remaining relation subgroup between the
universal finite-`3` tame Koch relator residual quotient and the actual target.
-/
def kochExtraResidual
    (D : KRData) :
    Subgroup D.TameKochRelator :=
  D.finiteKochDescent.ker

instance koch_extra_normal
    (D : KRData) :
    D.kochExtraResidual.Normal := by
  rw [kochExtraResidual]
  infer_instance

/--
Pulling the extra residual kernel back to the initial free pro-`3` group gives
exactly the actual initial Koch kernel.
-/
lemma koch_extra_comap
    (D : KRData) :
    D.kochExtraResidual.comap
        (residualQuotientMap
          (p := 3) (initialTameRelator D.frobeniusLift)) =
      initialKochQuotient.ker := by
  exact Towers.RRDescen.PQuot.extraResidualComap
      (p := 3)
      D.fiveRelatorPresented
      initial_galois_residually

/--
The extra residual kernel is closed inside the universal finite-`3` tame Koch
relator residual quotient.
-/
lemma koch_extra_closed
    (D : KRData) :
    IsClosed
      (((D.kochExtraResidual :
          Subgroup D.TameKochRelator) : Set
        D.TameKochRelator)) := by
  exact Towers.RRDescen.PQuot.extra_residual_closed
    (p := 3)
    D.fiveRelatorPresented
    initial_galois_residually

/--
Unconditionally, the actual initial Galois group is the quotient of the
universal finite-`3` tame Koch relator residual quotient by the extra residual
kernel.
-/
def kochResidualDescent
    (D : KRData) :
    D.TameKochRelator ⧸
        D.kochExtraResidual ≃*
      initialGaloisGroup := by
  change D.TameKochRelator ⧸
        D.finiteKochDescent.ker ≃*
      initialGaloisGroup
  exact QuotientGroup.quotientKerEquivOfSurjective
    D.finiteKochDescent
    D.koch_descent_surjective

/--
The finite quotient Koch theorem says exactly that residual descent to the
actual initial Galois group has no nontrivial kernel.
-/
lemma factorization_theorem_descent
    (D : KRData) :
    D.KochFactorizationTheorem ↔
      Function.Injective D.finiteKochDescent := by
  rw [D.factorization_theorem_relator]
  constructor
  · intro hkernel
    apply (Towers.RRDescen.PQuot.residual_descent_relator
        (p := 3)
        D.fiveRelatorPresented
        initial_galois_residually).mpr
    simpa using hkernel.le
  · intro hInjective
    apply le_antisymm
    · simpa using (Towers.RRDescen.PQuot.residual_descent_relator
          (p := 3)
          D.fiveRelatorPresented
          initial_galois_residually).mp hInjective
    · exact D.relator_koch_quotient

/--
Equivalently, the desired finite quotient Koch theorem is the vanishing of the
extra residual kernel.
-/
lemma factorization_theorem_extra
    (D : KRData) :
    D.KochFactorizationTheorem ↔
      D.kochExtraResidual = ⊥ := by
  rw [D.factorization_theorem_descent]
  exact (MonoidHom.ker_eq_bot_iff D.finiteKochDescent).symm

/--
Transporting residual descent across the canonical residual quotient/inverse
limit equivalence gives one unconditional map from the canonical finite-layer
relator quotient inverse limit onto the actual initial Galois group.
-/
def inverseLimitDescent
    (D : KRData) :
    D.RelatorInverseLimit →*
      initialGaloisGroup :=
  D.finiteKochDescent.comp
    D.relatorInverseLimit.symm.toMonoidHom

/--
The inverse of the canonical residual quotient/inverse-limit equivalence sends a
canonical coherent finite-layer thread back to its universal residual class.
-/
lemma relatorCompCompletion
    (D : KRData) :
    D.relatorInverseLimit.symm.toMonoidHom.comp
        D.zassenhausRelatorCompletion =
      residualQuotientMap
        (p := 3) (initialTameRelator D.frobeniusLift) := by
  apply MonoidHom.ext
  intro x
  have hcomp := congrArg
    (fun φ : initialKochFree.Carrier →*
        D.RelatorInverseLimit =>
      φ x)
    D.relatorResidualComp
  change D.relatorInverseLimit
      (residualQuotientMap (p := 3) (initialTameRelator D.frobeniusLift) x) =
    D.zassenhausRelatorCompletion x at hcomp
  change D.relatorInverseLimit.symm
      (D.zassenhausRelatorCompletion x) =
    residualQuotientMap (p := 3) (initialTameRelator D.frobeniusLift) x
  rw [← hcomp]
  exact D.relatorInverseLimit.symm_apply_apply _

/--
Canonical inverse-limit descent recovers the actual initial Koch quotient after
precomposition with the ambient canonical completion map.
-/
lemma limit_descent_comp
    (D : KRData) :
    D.inverseLimitDescent.comp
        D.zassenhausRelatorCompletion =
      initialKochQuotient := by
  rw [inverseLimitDescent, MonoidHom.comp_assoc,
    D.relatorCompCompletion,
    D.koch_descent_comp]

/--
Canonical inverse-limit descent to the actual initial Galois group is continuous.
-/
lemma limit_descent_continuous
    (D : KRData) :
    Continuous D.inverseLimitDescent := by
  change Continuous
    (D.finiteKochDescent.comp
      D.relatorInverseLimit.symm.toMonoidHom)
  exact D.koch_descent_continuous.comp
    D.relatorContinuousLimit.symm.continuous_toFun

/--
Canonical inverse-limit descent to the actual initial Galois group is onto.
-/
lemma limit_descent_surjective
    (D : KRData) :
    Function.Surjective D.inverseLimitDescent := by
  intro y
  rcases D.koch_descent_surjective y with ⟨z, rfl⟩
  exact ⟨D.relatorInverseLimit z, by
    simp [inverseLimitDescent]⟩

/--
Canonical inverse-limit descent is a topological quotient map onto the actual
initial Galois group.
-/
lemma koch_limit_descent
    (D : KRData) :
    Topology.IsQuotientMap D.inverseLimitDescent := by
  simpa [inverseLimitDescent, Function.comp_def] using
    (Towers.RRDescen.PQuot.residual_descent_quotient
      (p := 3)
      D.fiveRelatorPresented
      initial_galois_residually).comp
        D.relatorContinuousLimit.symm.toHomeomorph.isQuotientMap

/--
The canonical inverse-limit extra kernel is the precise relation subgroup still
collapsed when passing from the universal canonical finite-layer object to the
actual initial Galois group.
-/
def kochLimitExtra
    (D : KRData) :
    Subgroup D.RelatorInverseLimit :=
  D.inverseLimitDescent.ker

instance limit_extra_normal
    (D : KRData) :
    D.kochLimitExtra.Normal := by
  rw [kochLimitExtra]
  infer_instance

/--
The canonical inverse-limit extra kernel is the transport of the residual extra
kernel across the canonical residual quotient/inverse-limit equivalence.
-/
lemma limit_extra_residual
    (D : KRData) :
    D.kochLimitExtra =
      D.kochExtraResidual.map
        D.relatorInverseLimit.toMonoidHom := by
  change (D.finiteKochDescent.comp
      D.relatorInverseLimit.symm.toMonoidHom).ker =
    D.finiteKochDescent.ker.map
      D.relatorInverseLimit.toMonoidHom
  exact MonoidHom.ker_comp_mulEquiv
    D.finiteKochDescent
    D.relatorInverseLimit.symm

/--
Pulling the canonical inverse-limit extra kernel back along the ambient
completion map again recovers exactly the actual initial Koch kernel.
-/
lemma limit_extra_comap
    (D : KRData) :
    D.kochLimitExtra.comap
        D.zassenhausRelatorCompletion =
      initialKochQuotient.ker := by
  ext x
  rw [Subgroup.mem_comap, kochLimitExtra,
    MonoidHom.mem_ker, MonoidHom.mem_ker]
  rw [show D.inverseLimitDescent
      (D.zassenhausRelatorCompletion x) =
      initialKochQuotient x by
    exact congrArg
      (fun φ : initialKochFree.Carrier →* initialGaloisGroup => φ x)
      D.limit_descent_comp]

/--
The canonical inverse-limit extra kernel is closed inside the canonical
finite-layer relator quotient inverse limit.
-/
lemma limit_extra_closed
    (D : KRData) :
    IsClosed
      (((D.kochLimitExtra :
          Subgroup D.RelatorInverseLimit) : Set
        D.RelatorInverseLimit)) := by
  rw [kochLimitExtra]
  change IsClosed
    (D.inverseLimitDescent ⁻¹'
      ({1} : Set initialGaloisGroup))
  exact isClosed_singleton.preimage
    D.limit_descent_continuous

/--
Unconditionally, the actual initial Galois group is the quotient of the
canonical Zassenhaus finite-layer relator quotient inverse limit by its extra
kernel.
-/
def kochLimitDescent
    (D : KRData) :
    D.RelatorInverseLimit ⧸
        D.kochLimitExtra ≃*
      initialGaloisGroup := by
  change D.RelatorInverseLimit ⧸
        D.inverseLimitDescent.ker ≃*
      initialGaloisGroup
  exact QuotientGroup.quotientKerEquivOfSurjective
    D.inverseLimitDescent
    D.limit_descent_surjective

/--
The desired finite quotient Koch theorem is exactly injectivity of the
unconditional canonical inverse-limit descent onto the actual target.
-/
lemma theorem_descent_injective
    (D : KRData) :
    D.KochFactorizationTheorem ↔
      Function.Injective D.inverseLimitDescent := by
  rw [D.factorization_theorem_descent]
  constructor
  · intro hInjective
    exact hInjective.comp
      D.relatorInverseLimit.symm.injective
  · intro hInjective x y hxy
    apply D.relatorInverseLimit.injective
    apply hInjective
    simpa [inverseLimitDescent] using hxy

/--
Equivalently, the desired finite quotient Koch theorem is the vanishing of the
canonical inverse-limit extra kernel.
-/
lemma theorem_extra_bot
    (D : KRData) :
    D.KochFactorizationTheorem ↔
      D.kochLimitExtra = ⊥ := by
  rw [D.theorem_descent_injective]
  exact (MonoidHom.ker_eq_bot_iff D.inverseLimitDescent).symm

/--
Under the desired theorem, the canonical inverse-limit descent is the inverse
continuous multiplicative equivalence to the theorem-induced comparison map.
-/
def limitDescentTheorem
    (D : KRData)
    (hfactor : D.KochFactorizationTheorem) :
    D.RelatorInverseLimit ≃ₜ*
      initialGaloisGroup :=
  (D.limitContinuousTheorem hfactor).symm

/--
The theorem-induced inverse continuous equivalence descends the ambient
canonical completion map to the actual initial Koch quotient map.
-/
lemma limit_descent_theorem
    (D : KRData)
    (hfactor : D.KochFactorizationTheorem) :
    (D.limitDescentTheorem
        hfactor).toMulEquiv.toMonoidHom.comp
        D.zassenhausRelatorCompletion =
      initialKochQuotient := by
  apply MonoidHom.ext
  intro x
  have hcomp := congrArg
    (fun φ : initialKochFree.Carrier →*
        D.RelatorInverseLimit =>
      φ x)
    (D.limit_theorem_comp hfactor)
  change D.limitContinuousTheorem hfactor
      (initialKochQuotient x) =
    D.zassenhausRelatorCompletion x at hcomp
  change (D.limitContinuousTheorem hfactor).symm
      (D.zassenhausRelatorCompletion x) =
    initialKochQuotient x
  rw [← hcomp]
  exact (D.limitContinuousTheorem
    hfactor).symm_apply_apply _

/--
The desired finite quotient Koch theorem is equivalently the existence of a
compatible continuous multiplicative equivalence from the canonical inverse
limit onto the actual initial Galois group.
-/
lemma
  theorem_limit_descent
    (D : KRData) :
    D.KochFactorizationTheorem ↔
      ∃ e : D.RelatorInverseLimit ≃ₜ*
          initialGaloisGroup,
        e.toMulEquiv.toMonoidHom.comp
            D.zassenhausRelatorCompletion =
          initialKochQuotient := by
  constructor
  · intro hfactor
    exact ⟨D.limitDescentTheorem hfactor,
      D.limit_descent_theorem
        hfactor⟩
  · rintro ⟨e, he⟩
    apply D.fin_factorization_limit.mpr
    refine ⟨e.symm, ?_⟩
    apply MonoidHom.ext
    intro x
    have hcomp := congrArg
      (fun φ : initialKochFree.Carrier →* initialGaloisGroup =>
        φ x) he
    change e (D.zassenhausRelatorCompletion x) =
      initialKochQuotient x at hcomp
    change e.symm (initialKochQuotient x) =
      D.zassenhausRelatorCompletion x
    rw [← hcomp]
    exact e.symm_apply_apply _

end KRData

end TBluepr
end Towers
