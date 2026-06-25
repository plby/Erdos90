import Submission.FieldTheory.QuotientKoch.LayerWordRadius
import Submission.Group.OpenRelators.Obstructions


open scoped Pointwise Topology commutatorElement

noncomputable section

namespace Submission
namespace TBluepr

open KPScaffo
open IGScaffo
open IRScaffo
open ONCompar
open ONObstr

private instance initialThreeFact : Fact (Nat.Prime 3) :=
  ⟨Nat.prime_three⟩

namespace IRScaffo

universe u w

variable
    {p : ℕ}
    {F G : Type u}
    [Group F]
    [TopologicalSpace F]
    [IsTopologicalGroup F]
    [Group G]
    {ι : Type w}
    {q : F →* G}
    {relator : ι → F}
    {N : OpenNormalSubgroup F}

/--
A candidate-kernel-image element in one finite layer that is still outside the
bounded relation-word value set at the canonical relation-word radius.
-/
def LayerRadiusObstruction
    (q : F →* G)
    (relator : ι → F)
    (N : OpenNormalSubgroup F)
    [Finite (ONCompar.OpenNormalLayer N)] :
    Prop :=
  ∃ z : ONCompar.kernelImage q N,
    (z : ONCompar.OpenNormalLayer N) ∉
      boundedRelationSet relator N (layerRelationRadius relator N)

omit [IsTopologicalGroup F] in
/--
A canonical-radius relation-word obstruction is exactly failure of
candidate-kernel-image coverage at that canonical finite-layer radius.
-/
lemma radius_image_not
    (q : F →* G)
    (relator : ι → F)
    (N : OpenNormalSubgroup F)
    [Finite (ONCompar.OpenNormalLayer N)] :
    LayerRadiusObstruction q relator N ↔
      ¬ KernelCoveredBound q relator N (layerRelationRadius relator N) := by
  classical
  constructor
  · rintro ⟨z, hznot⟩ hcover
    exact hznot (hcover z.property)
  · intro hnot
    rw [KernelCoveredBound] at hnot
    rcases Set.not_subset.mp hnot with ⟨z, hzker, hznot⟩
    exact ⟨⟨z, hzker⟩, hznot⟩

omit [IsTopologicalGroup F] in
/--
At the canonical finite-layer relation-word radius, relation-word
obstructions are exactly algebraic finite-layer relator-image obstructions.
-/
lemma radius_obstruction_element
    (q : F →* G)
    (relator : ι → F)
    (N : OpenNormalSubgroup F)
    [Finite (ONCompar.OpenNormalLayer N)] :
    LayerRadiusObstruction q relator N ↔
      ONObstr.ImageElementObstruction q relator N := by
  rw [LayerRadiusObstruction,
    ONObstr.ImageElementObstruction,
    bounded_set_radius]
  simp only [SetLike.mem_coe]

omit [IsTopologicalGroup F] in
/--
At the canonical finite-layer relation-word radius, relation-word
obstructions are exactly ambient candidate-kernel elements surviving in the
canonical finite-layer relator quotient.
-/
lemma radius_image_element
    (q : F →* G)
    (relator : ι → F)
    (N : OpenNormalSubgroup F)
    [Finite (ONCompar.OpenNormalLayer N)] :
    LayerRadiusObstruction q relator N ↔
      ONObstr.KernelElementObstruction q relator N := by
  exact
    (radius_obstruction_element q relator N).trans
      (ONObstr.image_element_obstruction
        q relator N)

omit [IsTopologicalGroup F] in
/--
In a finite quotient layer, algebraic candidate-kernel generation fails exactly
when a canonical-radius relation-word obstruction exists.
-/
lemma algebraically_radius_obstruction
    (q : F →* G)
    (relator : ι → F)
    (N : OpenNormalSubgroup F)
    [Finite (ONCompar.OpenNormalLayer N)] :
    ¬ ONFact.GeneratedAlgebraicallyOpen
        q relator N ↔
      LayerRadiusObstruction q relator N := by
  exact
    (ONObstr.algebraically_element_obstruction
      q relator N).trans
      (radius_obstruction_element q relator N).symm

omit [IsTopologicalGroup F] in
/--
For a relator-killing candidate quotient in one finite quotient layer, failure
of the canonical relator-vs-kernel comparison is exactly a canonical-radius
relation-word obstruction.
-/
lemma not_kills_relators
    (q : F →* G)
    (relator : ι → F)
    (N : OpenNormalSubgroup F)
    (hkill : Submission.PRFact.KillsRelators relator q)
    [Finite (ONCompar.OpenNormalLayer N)] :
    ¬ ONCompar.ImageComparisonIsomorphism
        q relator N hkill ↔
      LayerRadiusObstruction q relator N := by
  exact
    (ONObstr.obstruction_kills_relators
      q relator N hkill).trans
      (radius_obstruction_element q relator N).symm

/--
For a pro-`p` source, failure of finite relator quotient factorization is
equivalent to a canonical-radius relation-word obstruction in one open-normal
finite layer.
-/
lemma property_radius_pro
    [CompactSpace F]
    (hProP : ProP.ProPGroup p F)
    (q : F →* G)
    (relator : ι → F) :
    ¬ PRQuotie.QuotientFactorizationProperty p relator q ↔
      ∃ N : OpenNormalSubgroup F, LayerRadiusObstruction q relator N := by
  exact
    (ONObstr.property_image_pro
      hProP q relator).trans
      (exists_congr fun N =>
        (radius_obstruction_element
          q relator N).symm)

/--
For fixed finite layer, existence of a canonical-radius relation-word
obstruction is decidable by the bounded finite search already developed.
-/
def radiusImageDecidable
    (q : F →* G)
    (relator : ι → F)
    (N : OpenNormalSubgroup F)
    [Finite ι]
    [Finite (ONCompar.OpenNormalLayer N)]
    [Finite (ONCompar.kernelImage q N)] :
    Decidable (LayerRadiusObstruction q relator N) := by
  letI := coveredRadiusDecidable q relator N
  exact decidable_of_iff'
    (¬ KernelCoveredBound q relator N (layerRelationRadius relator N))
    (radius_image_not
      q relator N)

end IRScaffo

namespace KRData

/--
A canonical-radius tame Koch relation-word obstruction in the `n`th canonical
Zassenhaus finite layer.
-/
abbrev RadiusImageObstruction
    (D : KRData)
    (n : ℕ) :=
  LayerRadiusObstruction
    initialKochQuotient
    (initialTameRelator D.frobeniusLift)
    (zassenhausOpenSubgroup n)

/--
At one canonical Zassenhaus depth, failure of the canonical finite-layer
relator-vs-kernel comparison is exactly a canonical-radius tame Koch
relation-word obstruction.
-/
lemma isomorphism_radius_obstruction
    (D : KRData)
    (n : ℕ) :
    ¬ D.CanonicalComparisonIsomorphism n ↔
      D.RadiusImageObstruction n := by
  letI : Finite (ONCompar.OpenNormalLayer
      (zassenhausOpenSubgroup n)) :=
    pro_p_open (zassenhausOpenSubgroup n)
  exact not_kills_relators
    initialKochQuotient
    (initialTameRelator D.frobeniusLift)
    (zassenhausOpenSubgroup n)
    D.tameRelatorsKilled

/--
The concrete finite quotient Koch theorem fails exactly when one canonical
Zassenhaus finite layer has a canonical-radius tame Koch relation-word
obstruction.
-/
lemma not_radius_obstruction
    (D : KRData) :
    ¬ D.KochFactorizationTheorem ↔
      ∃ n : ℕ, D.RadiusImageObstruction n := by
  rw [D.fin_factorization_radius]
  simp only [not_forall]
  exact exists_congr fun n => by
    letI : Finite (ONCompar.OpenNormalLayer
        (zassenhausOpenSubgroup n)) :=
      pro_p_open (zassenhausOpenSubgroup n)
    exact (radius_image_not
      initialKochQuotient
      (initialTameRelator D.frobeniusLift)
      (zassenhausOpenSubgroup n)).symm

/--
The concrete finite quotient Koch theorem is equivalent to absence of
canonical-radius tame Koch relation-word obstructions in every canonical
Zassenhaus finite layer.
-/
lemma forall_radius_obstruction
    (D : KRData) :
    D.KochFactorizationTheorem ↔
      ∀ n : ℕ, ¬ D.RadiusImageObstruction n := by
  rw [D.fin_factorization_radius]
  exact forall_congr' fun n => by
    letI : Finite (ONCompar.OpenNormalLayer
        (zassenhausOpenSubgroup n)) :=
      pro_p_open (zassenhausOpenSubgroup n)
    constructor
    · intro hcover hobs
      exact (radius_image_not
        initialKochQuotient
        (initialTameRelator D.frobeniusLift)
        (zassenhausOpenSubgroup n)).mp hobs hcover
    · intro hno
      by_contra hnot
      exact hno ((radius_image_not
        initialKochQuotient
        (initialTameRelator D.frobeniusLift)
        (zassenhausOpenSubgroup n)).mpr hnot)

/--
Failure of the concrete finite quotient Koch theorem is witnessed by one actual
candidate-kernel element surviving in one canonical Zassenhaus algebraic
finite-`3` relator quotient.
-/
lemma not_algebraic_counterexample
    (D : KRData) :
    ¬ D.KochFactorizationTheorem ↔
      ∃ n : ℕ, ∃ x : initialKochFree.Carrier,
        x ∈ initialKochQuotient.ker ∧
          x ∉ (ONFact.algebraicOpenNormal
            initialKochFree.isProP
            (zassenhausOpenSubgroup n)
            (relator := initialTameRelator D.frobeniusLift)).map.ker := by
  constructor
  · intro hnot
    rcases (D.not_radius_obstruction).mp
      hnot with ⟨n, hobs⟩
    letI : Finite (ONCompar.OpenNormalLayer
        (zassenhausOpenSubgroup n)) :=
      pro_p_open (zassenhausOpenSubgroup n)
    have hkernelObs :
        ONObstr.KernelElementObstruction
          initialKochQuotient
          (initialTameRelator D.frobeniusLift)
          (zassenhausOpenSubgroup n) :=
      (radius_image_element
        initialKochQuotient
        (initialTameRelator D.frobeniusLift)
        (zassenhausOpenSubgroup n)).mp hobs
    rcases (ONObstr.element_obstruction_not
      initialKochFree.isProP
      initialKochQuotient
      (initialTameRelator D.frobeniusLift)
      (zassenhausOpenSubgroup n)).mp hkernelObs with
      ⟨x, hxker, hxnot⟩
    exact ⟨n, x, hxker, hxnot⟩
  · rintro ⟨n, x, hxker, hxnot⟩
    letI : Finite (ONCompar.OpenNormalLayer
        (zassenhausOpenSubgroup n)) :=
      pro_p_open (zassenhausOpenSubgroup n)
    have hkernelObs :
        ONObstr.KernelElementObstruction
          initialKochQuotient
          (initialTameRelator D.frobeniusLift)
          (zassenhausOpenSubgroup n) :=
      (ONObstr.element_obstruction_not
        initialKochFree.isProP
        initialKochQuotient
        (initialTameRelator D.frobeniusLift)
        (zassenhausOpenSubgroup n)).mpr ⟨x, hxker, hxnot⟩
    have hobs : D.RadiusImageObstruction n :=
      (radius_image_element
        initialKochQuotient
        (initialTameRelator D.frobeniusLift)
        (zassenhausOpenSubgroup n)).mpr hkernelObs
    exact (D.not_radius_obstruction).mpr
      ⟨n, hobs⟩

/--
For fixed canonical Zassenhaus depth, existence of a canonical-radius tame Koch
relation-word obstruction is a decidable finite search problem.
-/
def radiusObstructionDecidable
    (D : KRData)
    (n : ℕ) :
    Decidable (D.RadiusImageObstruction n) := by
  letI : Finite (ONCompar.OpenNormalLayer
      (zassenhausOpenSubgroup n)) :=
    pro_p_open (zassenhausOpenSubgroup n)
  letI : Finite (ZassenhausLayerImage n) := inferInstance
  exact radiusImageDecidable
    initialKochQuotient
    (initialTameRelator D.frobeniusLift)
    (zassenhausOpenSubgroup n)

end KRData

end TBluepr
end Submission
