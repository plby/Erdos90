import Towers.FieldTheory.QuotientKoch.CanonicalTower
import Towers.Group.InverseLimit


open scoped Pointwise Topology commutatorElement

noncomputable section

namespace Towers
namespace TBluepr

open KPScaffo
open IGScaffo
open IRScaffo
open PRFact
open PRQuotie

private instance initialThreeFact : Fact (Nat.Prime 3) :=
  ⟨Nat.prime_three⟩

namespace KRData

/--
The compatible inverse system of canonical Koch Zassenhaus finite-layer
relator quotients.
-/
def ZassenhausRelatorSystem
    (D : KRData) :
    Group.cSQuotie where
  obj := fun n => (D.ZassenhausRelatorQuotient n).Target
  group_obj := fun _n => inferInstance
  finite_obj := fun _n => inferInstance
  map := fun {_m _n} hmn => D.ZassenhausRelatorTransition hmn
  map_surjective := fun {_m _n} hmn =>
    D.relator_transition_surjective hmn
  map_id := D.relator_transition_refl
  map_comp := fun {_k _m _n} hkm hmn =>
    D.three_transition_comp hkm hmn

/--
The inverse limit of the canonical Koch Zassenhaus finite-layer relator quotient
tower.
-/
abbrev RelatorInverseLimit
    (D : KRData) :=
  Group.inverseLimit D.ZassenhausRelatorSystem

/--
The canonical map from the initial free pro-`3` group to the inverse limit of
its canonical Zassenhaus finite-layer relator quotients.
-/
def zassenhausRelatorCompletion
    (D : KRData) :
    initialKochFree.Carrier →* D.RelatorInverseLimit :=
  Group.inverseLimitLift
    D.ZassenhausRelatorSystem
    (fun n => (D.ZassenhausRelatorQuotient n).map)
    (fun hmn => D.relator_transition_comp hmn)

/--
The coordinates of the canonical relator quotient completion map are the
canonical finite-layer relator quotient maps.
-/
lemma zassenhaus_relator_coordinate
    (D : KRData)
    (n : ℕ) :
    (Group.inverseLimitProjection D.ZassenhausRelatorSystem n).comp
        D.zassenhausRelatorCompletion =
      (D.ZassenhausRelatorQuotient n).map := by
  exact Group.limit_projection_lift
    D.ZassenhausRelatorSystem
    (fun n => (D.ZassenhausRelatorQuotient n).map)
    (fun hmn => D.relator_transition_comp hmn)
    n

/--
An ambient element dies in the canonical relator quotient inverse limit exactly
when it dies in every canonical Zassenhaus finite-layer relator quotient.
-/
lemma zassenhaus_completion_kernel
    (D : KRData)
    (x : initialKochFree.Carrier) :
    x ∈ D.zassenhausRelatorCompletion.ker ↔
      ∀ n : ℕ, x ∈ (D.ZassenhausRelatorQuotient n).map.ker := by
  constructor
  · intro hx n
    change (D.ZassenhausRelatorQuotient n).map x = 1
    rw [← D.zassenhaus_relator_coordinate n]
    change Group.inverseLimitProjection D.ZassenhausRelatorSystem n
      (D.zassenhausRelatorCompletion x) = 1
    rw [show D.zassenhausRelatorCompletion x = 1 from hx]
    exact map_one _
  · intro hx
    change D.zassenhausRelatorCompletion x = 1
    apply Subtype.ext
    funext n
    exact hx n

/--
The canonical relator quotient inverse-limit map kills every displayed tame
Koch relator.
-/
lemma relator_kills_relators
    (D : KRData) :
    KillsRelators
      (initialTameRelator D.frobeniusLift)
      D.zassenhausRelatorCompletion := by
  intro i
  change initialTameRelator D.frobeniusLift i ∈
    D.zassenhausRelatorCompletion.ker
  rw [D.zassenhaus_completion_kernel]
  intro n
  exact (D.ZassenhausRelatorQuotient n).toRShadow.relator_killed i

/--
The kernel of the canonical relator quotient inverse-limit map is exactly the
finite-`3` tame Koch relator residual kernel.
-/
lemma relator_completion_kernel
    (D : KRData) :
    D.zassenhausRelatorCompletion.ker =
      relatorKernel 3 (initialTameRelator D.frobeniusLift) := by
  ext x
  rw [D.zassenhaus_completion_kernel]
  constructor
  · intro hx
    rw [mem_relator_iff]
    intro S
    let T : D.ThreeRelatorQuotient :=
      RQShadow.relatorShadowRange S
    rcases D.zassenhaus_relator_kernel
        T with
      ⟨n, hn⟩
    have hxT : x ∈ T.map.ker := hn (hx n)
    simpa [T] using hxT
  · intro hx n
    exact relator_kernel
      (D.ZassenhausRelatorQuotient n).toRShadow
      hx

/--
The concrete finite quotient Koch factorization theorem is exactly containment
of the initial Koch kernel in the kernel of the canonical relator quotient
inverse-limit map.
-/
lemma fin_koch_kernel
    (D : KRData) :
    D.KochFactorizationTheorem ↔
      initialKochQuotient.ker ≤
        D.zassenhausRelatorCompletion.ker := by
  calc
    D.KochFactorizationTheorem ↔
        D.KochFactorizationTheorem :=
      D.factorization_theorem_statement
    _ ↔ initialKochQuotient.ker ≤
        relatorKernel 3 (initialTameRelator D.frobeniusLift) :=
      D.factorization_statement_relator
    _ ↔ initialKochQuotient.ker ≤
        D.zassenhausRelatorCompletion.ker := by
      rw [D.relator_completion_kernel]

/--
The concrete finite quotient Koch factorization theorem is equivalent to unique
factorization of the canonical relator quotient inverse-limit map through the
actual initial Koch quotient.
-/
lemma koch_unique_through
    (D : KRData) :
    D.KochFactorizationTheorem ↔
      FactorsUniquelyThrough
        initialKochQuotient
        D.zassenhausRelatorCompletion := by
  rw [D.fin_koch_kernel]
  exact (uniquely_through_ker
    initialKochQuotient
    D.zassenhausRelatorCompletion
    initial_quotient_surjective).symm

namespace CRCone

/--
A continuous Koch factor cone induces one comparison map from the actual
initial Galois group into the canonical relator quotient inverse limit.
-/
def inverseLimitLift
    (D : KRData)
    (C : D.CRCone) :
    initialGaloisGroup →* D.RelatorInverseLimit :=
  Group.inverseLimitLift
    D.ZassenhausRelatorSystem
    C.factor
    (fun hnm => transition_comp_factor D C hnm)

/--
The coordinates of the inverse-limit comparison map induced by a continuous
Koch factor cone are the cone factors.
-/
lemma inverse_limit_coordinate
    (D : KRData)
    (C : D.CRCone)
    (n : ℕ) :
    (Group.inverseLimitProjection D.ZassenhausRelatorSystem n).comp
        (C.inverseLimitLift D) =
      C.factor n := by
  exact Group.limit_projection_lift
    D.ZassenhausRelatorSystem
    C.factor
    (fun hnm => transition_comp_factor D C hnm)
    n

/--
The inverse-limit comparison map induced by a continuous Koch factor cone
factors the canonical relator quotient completion map through the actual
initial Koch quotient.
-/
lemma inverse_limit_lift
    (D : KRData)
    (C : D.CRCone) :
    (C.inverseLimitLift D).comp initialKochQuotient =
      D.zassenhausRelatorCompletion := by
  apply MonoidHom.ext
  intro x
  apply Subtype.ext
  funext n
  exact DFunLike.congr_fun (C.factor_comp_map n) x

end CRCone

/--
Failure of the concrete finite quotient Koch factorization theorem is exactly
an initial Koch kernel element surviving in the canonical relator quotient
inverse limit.
-/
lemma not_fin_kernel
    (D : KRData) :
    ¬ D.KochFactorizationTheorem ↔
      ∃ x : initialKochFree.Carrier,
        x ∈ initialKochQuotient.ker ∧
          x ∉ D.zassenhausRelatorCompletion.ker := by
  rw [D.fin_koch_kernel]
  exact SetLike.not_le_iff_exists

end KRData

end TBluepr
end Towers
