import Towers.FieldTheory.QuotientKoch.CanonicalQuotients
import Towers.Group.OpenRelators.CanonicalTower


open scoped Pointwise Topology commutatorElement

noncomputable section

namespace Towers
namespace TBluepr

open KPScaffo
open IGScaffo
open IRScaffo
open PRFact
open RCFact
open OCTower

private instance initialThreeFact : Fact (Nat.Prime 3) :=
  ⟨Nat.prime_three⟩

namespace KRData

/--
The canonical transition from the deeper `m`th Koch Zassenhaus finite-layer
relator quotient to the shallower `n`th one.
-/
abbrev ZassenhausRelatorTransition
    (D : KRData)
    {n m : ℕ}
    (hnm : n ≤ m) :
    (D.ZassenhausRelatorQuotient m).Target →*
      (D.ZassenhausRelatorQuotient n).Target :=
  OCTower.zassenhausRelatorTransition
    (p := 3)
    (relator := initialTameRelator D.frobeniusLift)
    initialKochFree.isProP
    initialKochFree.generator
    initialKochFree.dense_generator
    hnm

/--
The kernels of the canonical Koch Zassenhaus finite-layer relator quotients
decrease with depth.
-/
lemma three_relator_kernel
    (D : KRData)
    {n m : ℕ}
    (hnm : n ≤ m) :
    (D.ZassenhausRelatorQuotient m).map.ker ≤
      (D.ZassenhausRelatorQuotient n).map.ker := by
  exact OCTower.relator_quotient_kernel
    initialKochFree.isProP
    initialKochFree.generator
    initialKochFree.dense_generator
    hnm

/--
The canonical Koch Zassenhaus relator quotient transition commutes with the
ambient quotient maps.
-/
lemma relator_transition_comp
    (D : KRData)
    {n m : ℕ}
    (hnm : n ≤ m) :
    (D.ZassenhausRelatorTransition hnm).comp
        (D.ZassenhausRelatorQuotient m).map =
      (D.ZassenhausRelatorQuotient n).map := by
  exact OCTower.zassenhaus_relator_comp
    initialKochFree.isProP
    initialKochFree.generator
    initialKochFree.dense_generator
    hnm

/--
The canonical Koch Zassenhaus relator quotient transition sends the image of
every ambient element at depth `m` to its image at depth `n`.
-/
lemma zassenhaus_relator_transition
    (D : KRData)
    {n m : ℕ}
    (hnm : n ≤ m)
    (x : initialKochFree.Carrier) :
    D.ZassenhausRelatorTransition hnm
        ((D.ZassenhausRelatorQuotient m).map x) =
      (D.ZassenhausRelatorQuotient n).map x := by
  have hcomp := congrArg
    (fun φ : initialKochFree.Carrier →*
        (D.ZassenhausRelatorQuotient n).Target => φ x)
    (D.relator_transition_comp hnm)
  exact hcomp

/--
Canonical Koch Zassenhaus relator quotient transitions compose along increasing
depths.
-/
lemma three_transition_comp
    (D : KRData)
    {n m k : ℕ}
    (hnm : n ≤ m)
    (hmk : m ≤ k) :
    (D.ZassenhausRelatorTransition hnm).comp
        (D.ZassenhausRelatorTransition hmk) =
      D.ZassenhausRelatorTransition
        (hnm.trans hmk) := by
  exact OCTower.quotient_transition_comp
    initialKochFree.isProP
    initialKochFree.generator
    initialKochFree.dense_generator
    hnm
    hmk

/--
The canonical Koch Zassenhaus relator quotient transition at one depth is the
identity.
-/
lemma relator_transition_refl
    (D : KRData)
    (n : ℕ) :
    D.ZassenhausRelatorTransition (Nat.le_refl n) =
      MonoidHom.id (D.ZassenhausRelatorQuotient n).Target := by
  exact OCTower.zassenhaus_transition_refl
    initialKochFree.isProP
    initialKochFree.generator
    initialKochFree.dense_generator
    n

/--
Canonical Koch Zassenhaus relator quotient transitions are surjective.
-/
lemma relator_transition_surjective
    (D : KRData)
    {n m : ℕ}
    (hnm : n ≤ m) :
    Function.Surjective (D.ZassenhausRelatorTransition hnm) := by
  exact OCTower.zassenhaus_transition_surjective
    initialKochFree.isProP
    initialKochFree.generator
    initialKochFree.dense_generator
    hnm

/--
A continuous factor cone from the actual initial Koch quotient to the
canonical Zassenhaus finite-layer relator quotient tower.
-/
structure CRCone
    (D : KRData) where
  factor :
    ∀ n : ℕ, initialGaloisGroup →*
      (D.ZassenhausRelatorQuotient n).Target
  factor_continuous :
    ∀ n : ℕ, Continuous (factor n)
  factor_comp_map :
    ∀ n : ℕ, (factor n).comp initialKochQuotient =
      (D.ZassenhausRelatorQuotient n).map

namespace CRCone

/--
A continuous Koch factor cone is determined by its factor homomorphisms.
-/
lemma ext
    (D : KRData)
    (C E : D.CRCone)
    (hfactor : C.factor = E.factor) :
    C = E := by
  cases C
  cases E
  cases hfactor
  rfl

/--
A continuous Koch factor cone is automa compatible with the canonical
Zassenhaus relator quotient transition maps.
-/
lemma transition_comp_factor
    (D : KRData)
    (C : D.CRCone)
    {n m : ℕ}
    (hnm : n ≤ m) :
    (D.ZassenhausRelatorTransition hnm).comp
        (C.factor m) =
      C.factor n := by
  apply MonoidHom.ext
  intro y
  rcases initial_quotient_surjective y with ⟨x, rfl⟩
  have hm := congrArg
    (fun φ : initialKochFree.Carrier →*
        (D.ZassenhausRelatorQuotient m).Target => φ x)
    (C.factor_comp_map m)
  have hn := congrArg
    (fun φ : initialKochFree.Carrier →*
        (D.ZassenhausRelatorQuotient n).Target => φ x)
    (C.factor_comp_map n)
  change C.factor m (initialKochQuotient x) =
    (D.ZassenhausRelatorQuotient m).map x at hm
  change C.factor n (initialKochQuotient x) =
    (D.ZassenhausRelatorQuotient n).map x at hn
  change D.ZassenhausRelatorTransition hnm
      (C.factor m (initialKochQuotient x)) =
    C.factor n (initialKochQuotient x)
  calc
    D.ZassenhausRelatorTransition hnm
        (C.factor m (initialKochQuotient x)) =
        D.ZassenhausRelatorTransition hnm
          ((D.ZassenhausRelatorQuotient m).map x) := by rw [hm]
    _ = (D.ZassenhausRelatorQuotient n).map x :=
      D.zassenhaus_relator_transition hnm x
    _ = C.factor n (initialKochQuotient x) := hn.symm

/--
There is at most one continuous Koch factor cone into the canonical
Zassenhaus relator quotient tower.
-/
lemma subsingleton
    (D : KRData) :
    Subsingleton D.CRCone := by
  constructor
  intro C E
  apply CRCone.ext D C E
  funext n
  apply MonoidHom.ext
  intro y
  rcases initial_quotient_surjective y with ⟨x, rfl⟩
  have hCx := congrArg
    (fun φ : initialKochFree.Carrier →*
        (D.ZassenhausRelatorQuotient n).Target => φ x)
    (C.factor_comp_map n)
  have hEx := congrArg
    (fun φ : initialKochFree.Carrier →*
        (D.ZassenhausRelatorQuotient n).Target => φ x)
    (E.factor_comp_map n)
  change C.factor n (initialKochQuotient x) =
    (D.ZassenhausRelatorQuotient n).map x at hCx
  change E.factor n (initialKochQuotient x) =
    (D.ZassenhausRelatorQuotient n).map x at hEx
  exact hCx.trans hEx.symm

end CRCone

/--
The concrete finite quotient Koch factorization theorem constructs the
canonical continuous factor cone into the Zassenhaus finite-layer relator
quotient tower.
-/
def continuousKochFactorization
    (D : KRData)
    (hfactor : D.KochFactorizationTheorem) :
    D.CRCone := by
  let hkernel :=
    D.fin_factorization_forall.mp
      hfactor
  exact {
    factor := fun n =>
      RCFact.continuousFactorQuotient
        initialKochQuotient
        (D.ZassenhausRelatorQuotient n).map
        initial_koch
        (hkernel n)
    factor_continuous := fun n =>
      RCFact.continuous_factor_quotient
        initialKochQuotient
        (D.ZassenhausRelatorQuotient n).map
        initial_koch
        (D.ZassenhausRelatorQuotient n).toRShadow.toShadow.map_continuous
        (hkernel n)
    factor_comp_map := fun n =>
      RCFact.continuous_quotient_comp
        initialKochQuotient
        (D.ZassenhausRelatorQuotient n).map
        initial_koch
        (hkernel n)
  }

/--
Any continuous factor cone into the canonical Zassenhaus finite-layer relator
quotient tower proves the concrete finite quotient Koch factorization theorem.
-/
lemma fin_koch_cone
    (D : KRData)
    (hcone : Nonempty D.CRCone) :
    D.KochFactorizationTheorem := by
  rcases hcone with ⟨C⟩
  apply D.fin_factorization_forall.mpr
  intro n
  exact ker_factors_through
    initialKochQuotient
    (D.ZassenhausRelatorQuotient n).map
    ⟨C.factor n, C.factor_comp_map n⟩

/--
The concrete finite quotient Koch factorization theorem is equivalent to
existence of the unique continuous factor cone into the canonical Zassenhaus
finite-layer relator quotient tower.
-/
lemma fin_factorization_cone
    (D : KRData) :
    D.KochFactorizationTheorem ↔
      Nonempty D.CRCone := by
  constructor
  · intro hfactor
    exact ⟨D.continuousKochFactorization
      hfactor⟩
  · exact D.fin_koch_cone

end KRData

end TBluepr
end Towers
