import Submission.FieldTheory.QuotientKoch.LayerWordObstructions
import Submission.Group.OpenRelators.ObstructionCofinality


open scoped Pointwise Topology commutatorElement

noncomputable section

namespace Submission
namespace TBluepr

open KPScaffo
open IGScaffo
open IRScaffo
open ONCompar
open ONObstr
open OOCofina

private instance initialThreeFact : Fact (Nat.Prime 3) :=
  ⟨Nat.prime_three⟩

namespace IRScaffo

universe u w

variable
    {F G : Type u}
    [Group F]
    [TopologicalSpace F]
    [IsTopologicalGroup F]
    [CompactSpace F]
    [Group G]
    {ι : Type w}
    {q : F →* G}
    {relator : ι → F}

omit [IsTopologicalGroup F] [CompactSpace F] in
/--
A canonical-radius relation-word obstruction in a coarser finite layer persists
in every finer finite layer.
-/
lemma layer_radius_obstruction
    {M N : OpenNormalSubgroup F}
    [Finite (ONCompar.OpenNormalLayer M)]
    [Finite (ONCompar.OpenNormalLayer N)]
    (hMN : (M : Subgroup F) ≤ N)
    (hN : LayerRadiusObstruction q relator N) :
    LayerRadiusObstruction q relator M := by
  apply (radius_image_element q relator M).mpr
  apply OOCofina.element_obstruction hMN
  exact (radius_image_element q relator N).mp hN

end IRScaffo

namespace KRData

/--
Deeper canonical Zassenhaus layers are finer open-normal quotients than shallower
canonical Zassenhaus layers.
-/
lemma zassenhaus_open_subgroup
    {n m : ℕ}
    (hnm : n ≤ m) :
    (zassenhausOpenSubgroup m : Subgroup initialKochFree.Carrier) ≤
      zassenhausOpenSubgroup n := by
  change zassenhausFiltration 3 initialKochFree.Carrier m ≤
    zassenhausFiltration 3 initialKochFree.Carrier n
  exact zassenhausFiltration_antitone 3 initialKochFree.Carrier hnm

/--
A canonical-radius tame Koch relation-word obstruction at one Zassenhaus depth
persists at every deeper canonical Zassenhaus depth.
-/
lemma zassenhaus_radius_obstruction
    (D : KRData)
    {n m : ℕ}
    (hnm : n ≤ m)
    (hN : D.RadiusImageObstruction n) :
    D.RadiusImageObstruction m := by
  letI : Finite (ONCompar.OpenNormalLayer
      (zassenhausOpenSubgroup n)) :=
    pro_p_open (zassenhausOpenSubgroup n)
  letI : Finite (ONCompar.OpenNormalLayer
      (zassenhausOpenSubgroup m)) :=
    pro_p_open (zassenhausOpenSubgroup m)
  exact layer_radius_obstruction
    (zassenhaus_open_subgroup hnm)
    hN

/--
If one actual candidate-kernel element survives a canonical Zassenhaus
algebraic relator quotient, then the same ambient element survives every deeper
canonical Zassenhaus algebraic relator quotient.
-/
lemma not_algebraic_relator
    (D : KRData)
    {n m : ℕ}
    (hnm : n ≤ m)
    {x : initialKochFree.Carrier}
    (hxN :
      x ∉ (ONFact.algebraicOpenNormal
        initialKochFree.isProP
        (zassenhausOpenSubgroup n)
        (relator := initialTameRelator D.frobeniusLift)).map.ker) :
    x ∉ (ONFact.algebraicOpenNormal
      initialKochFree.isProP
      (zassenhausOpenSubgroup m)
      (relator := initialTameRelator D.frobeniusLift)).map.ker := by
  exact OOCofina.not_algebraic_open
    initialKochFree.isProP
    (zassenhaus_open_subgroup hnm)
    hxN

/--
The concrete finite quotient Koch theorem fails exactly when canonical-radius
tame Koch relation-word obstructions persist from some Zassenhaus depth onward.
-/
lemma eventually_radius_obstruction
    (D : KRData) :
    ¬ D.KochFactorizationTheorem ↔
      ∃ n : ℕ, ∀ m : ℕ, n ≤ m → D.RadiusImageObstruction m := by
  constructor
  · intro hnot
    rcases (D.not_radius_obstruction).mp
      hnot with ⟨n, hN⟩
    exact ⟨n, fun m hnm => D.zassenhaus_radius_obstruction hnm hN⟩
  · rintro ⟨n, htail⟩
    exact (D.not_radius_obstruction).mpr
      ⟨n, htail n le_rfl⟩

/--
Failure of the concrete finite quotient Koch theorem is witnessed by one actual
candidate-kernel element that survives every sufficiently deep canonical
Zassenhaus algebraic finite-`3` relator quotient.
-/
lemma eventually_algebraic_counterexample
    (D : KRData) :
    ¬ D.KochFactorizationTheorem ↔
      ∃ n : ℕ, ∃ x : initialKochFree.Carrier,
        x ∈ initialKochQuotient.ker ∧
          ∀ m : ℕ, n ≤ m →
            x ∉ (ONFact.algebraicOpenNormal
              initialKochFree.isProP
              (zassenhausOpenSubgroup m)
              (relator := initialTameRelator D.frobeniusLift)).map.ker := by
  constructor
  · intro hnot
    rcases (D.not_algebraic_counterexample).mp
      hnot with ⟨n, x, hxker, hxN⟩
    exact ⟨n, x, hxker, fun m hnm =>
      D.not_algebraic_relator hnm hxN⟩
  · rintro ⟨n, x, hxker, htail⟩
    exact (D.not_algebraic_counterexample).mpr
      ⟨n, x, hxker, htail n le_rfl⟩

end KRData

end TBluepr
end Submission
