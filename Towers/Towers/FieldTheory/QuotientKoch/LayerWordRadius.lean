import Towers.FieldTheory.QuotientKoch.LayerBoundedReachability


open scoped Pointwise Topology commutatorElement

noncomputable section

namespace Towers
namespace TBluepr

open KPScaffo
open IGScaffo
open IRScaffo
open ONCompar

private instance initialThreeFact : Fact (Nat.Prime 3) :=
  ⟨Nat.prime_three⟩

namespace IRScaffo

universe u w

variable
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
The least word-length bound at which bounded quotient-layer relation words have
already filled the whole algebraic relator image in one finite quotient layer.
-/
def layerRelationRadius
    (relator : ι → F)
    (N : OpenNormalSubgroup F)
    [Finite (ONCompar.OpenNormalLayer N)] :
    ℕ :=
  Nat.find (bound_set_image relator N)

omit [IsTopologicalGroup F] in
/--
At the canonical finite-layer relation-word radius, bounded quotient-layer
relation words equal the whole algebraic relator image.
-/
lemma bounded_set_radius
    (relator : ι → F)
    (N : OpenNormalSubgroup F)
    [Finite (ONCompar.OpenNormalLayer N)] :
    boundedRelationSet relator N (layerRelationRadius relator N) =
      (ONCompar.relatorImage relator N :
        Set (ONCompar.OpenNormalLayer N)) := by
  exact Nat.find_spec (bound_set_image relator N)

omit [IsTopologicalGroup F] in
/--
Any bound at which bounded quotient-layer relation words fill the algebraic
relator image is at least the canonical finite-layer relation-word radius.
-/
lemma radius_bounded_image
    (relator : ι → F)
    (N : OpenNormalSubgroup F)
    [Finite (ONCompar.OpenNormalLayer N)]
    {bound : ℕ}
    (hbound :
      boundedRelationSet relator N bound =
        (ONCompar.relatorImage relator N :
          Set (ONCompar.OpenNormalLayer N))) :
    layerRelationRadius relator N ≤ bound := by
  exact Nat.find_min'
    (bound_set_image relator N)
    hbound

omit [IsTopologicalGroup F] in
/--
The bounded quotient-layer relation-word value sets stabilize exactly at and
after the canonical finite-layer relation-word radius.
-/
lemma radius_set_image
    (relator : ι → F)
    (N : OpenNormalSubgroup F)
    [Finite (ONCompar.OpenNormalLayer N)]
    {bound : ℕ} :
    layerRelationRadius relator N ≤ bound ↔
      boundedRelationSet relator N bound =
        (ONCompar.relatorImage relator N :
          Set (ONCompar.OpenNormalLayer N)) := by
  constructor
  · intro hbound
    exact Set.Subset.antisymm
      (bounded_subset_image relator N bound)
      (by
        rw [← bounded_set_radius
          relator N]
        exact bounded_set_mono relator N hbound)
  · exact radius_bounded_image
      relator N

omit [IsTopologicalGroup F] in
/--
Candidate-kernel-image coverage at the canonical finite-layer relation-word
radius is exactly algebraic inclusion of the candidate-kernel image in the
relator image.
-/
lemma covered_radius_relator
    (q : F →* G)
    (relator : ι → F)
    (N : OpenNormalSubgroup F)
    [Finite (ONCompar.OpenNormalLayer N)] :
    KernelCoveredBound q relator N (layerRelationRadius relator N) ↔
      ONCompar.kernelImage q N ≤
        ONCompar.relatorImage relator N := by
  rw [KernelCoveredBound,
    bounded_set_radius]
  exact SetLike.coe_subset_coe

omit [IsTopologicalGroup F] in
/--
In a finite quotient layer, eventual bounded relation-word coverage of the
candidate-kernel image is already equivalent to coverage at the canonical
finite-layer relation-word radius.
-/
lemma bound_image_radius
    (q : F →* G)
    (relator : ι → F)
    (N : OpenNormalSubgroup F)
    [Finite (ONCompar.OpenNormalLayer N)] :
    (∃ bound : ℕ, KernelCoveredBound q relator N bound) ↔
      KernelCoveredBound q relator N (layerRelationRadius relator N) := by
  exact
    (bound_covered_relator q relator N).trans
      (covered_radius_relator
        q relator N).symm

omit [IsTopologicalGroup F] in
/--
In a finite quotient layer, algebraic candidate-kernel generation is equivalent
to coverage at the canonical finite-layer relation-word radius.
-/
lemma algebraically_open_radius
    (q : F →* G)
    (relator : ι → F)
    (N : OpenNormalSubgroup F)
    [Finite (ONCompar.OpenNormalLayer N)] :
    ONFact.GeneratedAlgebraicallyOpen
        q relator N ↔
      KernelCoveredBound q relator N (layerRelationRadius relator N) := by
  exact
    (generated_algebraically_covered
      q relator N).trans
      (bound_image_radius
        q relator N)

omit [IsTopologicalGroup F] in
/--
For a relator-killing candidate quotient in one finite quotient layer, the
canonical relator-vs-kernel comparison is an isomorphism exactly when the
candidate-kernel image is covered at the canonical relation-word radius.
-/
lemma radius_kills_relators
    (q : F →* G)
    (relator : ι → F)
    (N : OpenNormalSubgroup F)
    (hkill : Towers.PRFact.KillsRelators relator q)
    [Finite (ONCompar.OpenNormalLayer N)] :
    ONCompar.ImageComparisonIsomorphism
        q relator N hkill ↔
      KernelCoveredBound q relator N (layerRelationRadius relator N) := by
  exact
    (comparison_kills_relators
      q relator N hkill).trans
      (bound_image_radius
        q relator N)

/--
For a pro-`p` source and relator-killing candidate quotient, finite relator
quotient factorization is equivalent to coverage at one canonical finite bound
in every open-normal finite layer.
-/
lemma forall_kills_relators
    {p : ℕ}
    [CompactSpace F]
    (hProP : ProP.ProPGroup p F)
    (q : F →* G)
    (relator : ι → F)
    (hkill : Towers.PRFact.KillsRelators relator q) :
    PRQuotie.QuotientFactorizationProperty p relator q ↔
      ∀ N : OpenNormalSubgroup F,
        KernelCoveredBound q relator N (layerRelationRadius relator N) := by
  rw [property_forall_kills
    hProP q relator hkill]
  exact forall_congr' fun N =>
    bound_image_radius
      q relator N

/--
For fixed finite layer, the canonical relation-word-radius candidate-kernel
coverage problem is decidable by the bounded finite search already developed.
-/
def coveredRadiusDecidable
    (q : F →* G)
    (relator : ι → F)
    (N : OpenNormalSubgroup F)
    [Finite ι]
    [Finite (ONCompar.OpenNormalLayer N)]
    [Finite (ONCompar.kernelImage q N)] :
    Decidable
      (KernelCoveredBound q relator N (layerRelationRadius relator N)) := by
  exact kernelCoveredDecidable q relator N (layerRelationRadius relator N)

end IRScaffo

namespace KRData

/--
The canonical relation-word radius of actual tame Koch relators in the `n`th
canonical Zassenhaus finite layer.
-/
abbrev ZassenhausRelationRadius
    (D : KRData)
    (n : ℕ) :=
  layerRelationRadius
    (initialTameRelator D.frobeniusLift)
    (zassenhausOpenSubgroup n)

/--
The actual initial Koch candidate-kernel image is covered at the canonical tame
Koch relation-word radius in the `n`th canonical Zassenhaus finite layer.
-/
def ImageCoveredRadius
    (D : KRData)
    (n : ℕ) :
    Prop :=
  D.ImageCoveredBound n (D.ZassenhausRelationRadius n)

/--
Actual bounded tame Koch relation-word coverage in every canonical Zassenhaus
finite layer is equivalent to coverage at each layer's canonical tame Koch
relation-word radius.
-/
lemma coverage_covered_radius
    (D : KRData) :
    D.ImageBoundedCoverage ↔
      ∀ n : ℕ, D.ImageCoveredRadius n := by
  exact forall_congr' fun n => by
    letI : Finite (ONCompar.OpenNormalLayer
        (zassenhausOpenSubgroup n)) :=
      pro_p_open (zassenhausOpenSubgroup n)
    exact bound_image_radius
      initialKochQuotient
      (initialTameRelator D.frobeniusLift)
      (zassenhausOpenSubgroup n)

/--
At one canonical Zassenhaus depth, the canonical finite-layer relator-vs-
kernel comparison is an isomorphism exactly when the actual candidate-kernel
image is covered at that layer's canonical tame Koch relation-word radius.
-/
lemma isomorphism_covered_radius
    (D : KRData)
    (n : ℕ) :
    D.CanonicalComparisonIsomorphism n ↔
      D.ImageCoveredRadius n := by
  letI : Finite (ONCompar.OpenNormalLayer
      (zassenhausOpenSubgroup n)) :=
    pro_p_open (zassenhausOpenSubgroup n)
  exact radius_kills_relators
    initialKochQuotient
    (initialTameRelator D.frobeniusLift)
    (zassenhausOpenSubgroup n)
    D.tameRelatorsKilled

/--
The concrete finite quotient Koch theorem is equivalent to checking actual
candidate-kernel-image coverage at one canonical tame Koch relation-word radius
in every canonical Zassenhaus finite layer.
-/
lemma fin_factorization_radius
    (D : KRData) :
    D.KochFactorizationTheorem ↔
      ∀ n : ℕ, D.ImageCoveredRadius n := by
  exact D.factorization_theorem_coverage.trans
    D.coverage_covered_radius

/--
For fixed canonical Zassenhaus depth, coverage at the canonical tame Koch
relation-word radius is a decidable finite search problem.
-/
def imageCoveredDecidable
    (D : KRData)
    (n : ℕ) :
    Decidable (D.ImageCoveredRadius n) := by
  letI : Finite (ONCompar.OpenNormalLayer
      (zassenhausOpenSubgroup n)) :=
    pro_p_open (zassenhausOpenSubgroup n)
  letI : Finite (ZassenhausLayerImage n) := inferInstance
  exact coveredRadiusDecidable
    initialKochQuotient
    (initialTameRelator D.frobeniusLift)
    (zassenhausOpenSubgroup n)

end KRData

end TBluepr
end Towers
