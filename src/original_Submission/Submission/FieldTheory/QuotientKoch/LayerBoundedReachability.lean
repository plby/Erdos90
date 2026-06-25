import Submission.FieldTheory.QuotientKoch.LayerRelationWords


open scoped Pointwise Topology commutatorElement

noncomputable section

namespace Submission
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
The quotient-layer elements represented by relation words of length at most
`bound`.
-/
def boundedRelationSet
    (relator : ι → F)
    (N : OpenNormalSubgroup F)
    (bound : ℕ) :
    Set (ONCompar.OpenNormalLayer N) :=
  Set.range fun word :
      RWord.Bounded ι (ONCompar.OpenNormalLayer N) bound =>
    word.1.value (openLayerRelator relator N)

/--
The quotient-layer elements represented by arbitrary finite relation words.
-/
def layerRelationSet
    (relator : ι → F)
    (N : OpenNormalSubgroup F) :
    Set (ONCompar.OpenNormalLayer N) :=
  Set.range fun word :
      RWord ι (ONCompar.OpenNormalLayer N) =>
    word.value (openLayerRelator relator N)

omit [IsTopologicalGroup F] in
/--
Membership in the bounded quotient-layer relation-word value set is exactly
existence of one relation word with the displayed value and length bound.
-/
lemma bounded_relation_set
    (relator : ι → F)
    (N : OpenNormalSubgroup F)
    (bound : ℕ)
    (x : ONCompar.OpenNormalLayer N) :
    x ∈ boundedRelationSet relator N bound ↔
      ∃ word : RWord ι (ONCompar.OpenNormalLayer N),
        word.length ≤ bound ∧
          word.value (openLayerRelator relator N) = x := by
  constructor
  · rintro ⟨word, rfl⟩
    exact ⟨word.1, word.2, rfl⟩
  · rintro ⟨word, hlength, hvalue⟩
    exact ⟨⟨word, hlength⟩, hvalue⟩

omit [IsTopologicalGroup F] in
/--
Membership in the unbounded quotient-layer relation-word value set is exactly
existence of one finite relation word with the displayed value.
-/
lemma layer_relation_set
    (relator : ι → F)
    (N : OpenNormalSubgroup F)
    (x : ONCompar.OpenNormalLayer N) :
    x ∈ layerRelationSet relator N ↔
      ∃ word : RWord ι (ONCompar.OpenNormalLayer N),
        word.value (openLayerRelator relator N) = x := by
  rfl

omit [IsTopologicalGroup F] in
/--
Increasing the relation-word length bound can only enlarge the represented
quotient-layer value set.
-/
lemma bounded_set_mono
    (relator : ι → F)
    (N : OpenNormalSubgroup F)
    {lower upper : ℕ}
    (hbound : lower ≤ upper) :
    boundedRelationSet relator N lower ⊆
      boundedRelationSet relator N upper := by
  rintro x ⟨word, hword⟩
  exact ⟨⟨word.1, word.2.trans hbound⟩, hword⟩

omit [IsTopologicalGroup F] in
/--
Every bounded quotient-layer relation-word value is an unbounded
quotient-layer relation-word value.
-/
lemma bounded_set_subset
    (relator : ι → F)
    (N : OpenNormalSubgroup F)
    (bound : ℕ) :
    boundedRelationSet relator N bound ⊆
      layerRelationSet relator N := by
  rintro x ⟨word, hword⟩
  exact ⟨word.1, hword⟩

omit [IsTopologicalGroup F] in
/--
Every unbounded quotient-layer relation-word value already appears at the
length bound given by one representing word.
-/
lemma relation_set_bound
    (relator : ι → F)
    (N : OpenNormalSubgroup F)
    (x : ONCompar.OpenNormalLayer N) :
    x ∈ layerRelationSet relator N ↔
      ∃ bound : ℕ, x ∈ boundedRelationSet relator N bound := by
  constructor
  · rintro ⟨word, hword⟩
    exact ⟨word.length, ⟨⟨word, le_rfl⟩, hword⟩⟩
  · rintro ⟨bound, hbound⟩
    exact bounded_set_subset
      relator N bound hbound

omit [IsTopologicalGroup F] in
/--
The unbounded quotient-layer relation-word value set is the union of all
bounded relation-word value sets.
-/
lemma i_union_bounded
    (relator : ι → F)
    (N : OpenNormalSubgroup F) :
    layerRelationSet relator N =
      ⋃ bound : ℕ, boundedRelationSet relator N bound := by
  ext x
  constructor
  · intro hx
    rcases (relation_set_bound relator N x).mp hx with
      ⟨bound, hbound⟩
    exact Set.mem_iUnion.2 ⟨bound, hbound⟩
  · intro hx
    rcases Set.mem_iUnion.1 hx with ⟨bound, hbound⟩
    exact (relation_set_bound relator N x).mpr
      ⟨bound, hbound⟩

omit [IsTopologicalGroup F] in
/--
The algebraic relator image in one finite layer is the ordinary normal closure
of the displayed relator images inside that layer.
-/
lemma relator_image_subgroup
    (relator : ι → F)
    (N : OpenNormalSubgroup F) :
    ONCompar.relatorImage relator N =
      IGScaffo.relationSubgroup
        (openLayerRelator relator N) := by
  let qN : F →* ONCompar.OpenNormalLayer N :=
    ONCompar.openNormalLayer N
  change
    (Submission.PRFact.relationSubgroup relator).map qN =
      IGScaffo.relationSubgroup
        (openLayerRelator relator N)
  rw [Submission.PRFact.relationSubgroup,
    IGScaffo.relationSubgroup]
  rw [Subgroup.map_normalClosure (Set.range relator) qN
    (QuotientGroup.mk'_surjective (N : Subgroup F))]
  congr 1
  ext x
  constructor
  · rintro ⟨y, ⟨i, rfl⟩, rfl⟩
    exact ⟨i, rfl⟩
  · rintro ⟨i, rfl⟩
    exact ⟨relator i, ⟨i, rfl⟩, rfl⟩

omit [IsTopologicalGroup F] in
/--
Arbitrary finite quotient-layer relation words represent exactly the algebraic
relator image in that finite layer.
-/
lemma set_relator_image
    (relator : ι → F)
    (N : OpenNormalSubgroup F) :
    layerRelationSet relator N =
      (ONCompar.relatorImage relator N :
        Set (ONCompar.OpenNormalLayer N)) := by
  ext x
  constructor
  · rintro ⟨word, rfl⟩
    rw [relator_image_subgroup]
    exact word.value_relation (openLayerRelator relator N)
  · intro hx
    rw [relator_image_subgroup] at hx
    rcases RWord.value_relation_subgroup
        (openLayerRelator relator N) x hx with
      ⟨word, hword⟩
    exact ⟨word, hword⟩

omit [IsTopologicalGroup F] in
/--
Every bounded quotient-layer relation-word value lies in the algebraic relator
image in that finite layer.
-/
lemma bounded_subset_image
    (relator : ι → F)
    (N : OpenNormalSubgroup F)
    (bound : ℕ) :
    boundedRelationSet relator N bound ⊆
      (ONCompar.relatorImage relator N :
        Set (ONCompar.OpenNormalLayer N)) := by
  rw [← set_relator_image]
  exact bounded_set_subset
    relator N bound

omit [IsTopologicalGroup F] in
/--
Any finite subset of the unbounded quotient-layer relation-word value set is
already covered by one common relation-word length bound.
-/
lemma bound_subset_set
    (relator : ι → F)
    (N : OpenNormalSubgroup F)
    {S : Set (ONCompar.OpenNormalLayer N)}
    (hSfinite : S.Finite)
    (hS : S ⊆ layerRelationSet relator N) :
    ∃ bound : ℕ, S ⊆ boundedRelationSet relator N bound := by
  letI : Fintype S := hSfinite.fintype
  let boundFor : S → ℕ := fun z =>
    Classical.choose
      ((relation_set_bound relator N
        (z : ONCompar.OpenNormalLayer N)).mp
        (hS z.property))
  have hboundFor :
      ∀ z : S,
        (z : ONCompar.OpenNormalLayer N) ∈
          boundedRelationSet relator N (boundFor z) := by
    intro z
    exact Classical.choose_spec
      ((relation_set_bound relator N
        (z : ONCompar.OpenNormalLayer N)).mp
        (hS z.property))
  let bound : ℕ := Finset.univ.sup boundFor
  refine ⟨bound, ?_⟩
  intro x hx
  let z : S := ⟨x, hx⟩
  exact bounded_set_mono relator N
    (Finset.le_sup (f := boundFor) (Finset.mem_univ z))
    (hboundFor z)

omit [IsTopologicalGroup F] in
/--
In a finite quotient layer, the whole algebraic relator image is represented
by relation words of one uniform finite length bound.
-/
lemma bound_set_image
    (relator : ι → F)
    (N : OpenNormalSubgroup F)
    [Finite (ONCompar.OpenNormalLayer N)] :
    ∃ bound : ℕ,
      boundedRelationSet relator N bound =
        (ONCompar.relatorImage relator N :
          Set (ONCompar.OpenNormalLayer N)) := by
  have hrelatorImage :
      (ONCompar.relatorImage relator N :
        Set (ONCompar.OpenNormalLayer N)) ⊆
        layerRelationSet relator N := by
    rw [set_relator_image]
  have hrelatorImageFinite :
      (ONCompar.relatorImage relator N :
        Set (ONCompar.OpenNormalLayer N)).Finite :=
    Set.toFinite _
  rcases bound_subset_set
      relator N hrelatorImageFinite hrelatorImage with
    ⟨bound, hbound⟩
  exact ⟨bound, Set.Subset.antisymm
    (bounded_subset_image relator N bound)
    hbound⟩

/--
The candidate-kernel image in one finite layer is covered by quotient-layer
relation words of length at most `bound`.
-/
def KernelCoveredBound
    (q : F →* G)
    (relator : ι → F)
    (N : OpenNormalSubgroup F)
    (bound : ℕ) :
    Prop :=
  (ONCompar.kernelImage q N :
      Set (ONCompar.OpenNormalLayer N)) ⊆
    boundedRelationSet relator N bound

omit [IsTopologicalGroup F] in
/--
Increasing the word-length bound preserves candidate-kernel-image coverage.
-/
lemma covered_bound_mono
    (q : F →* G)
    (relator : ι → F)
    (N : OpenNormalSubgroup F)
    {lower upper : ℕ}
    (hbound : lower ≤ upper)
    (hcover : KernelCoveredBound q relator N lower) :
    KernelCoveredBound q relator N upper := by
  exact hcover.trans (bounded_set_mono relator N hbound)

omit [IsTopologicalGroup F] in
/--
Candidate-kernel-image coverage by one word-length bound is exactly existence
of one certifying bounded quotient-layer relation-word table.
-/
lemma covered_certifying_table
    (q : F →* G)
    (relator : ι → F)
    (N : OpenNormalSubgroup F)
    (bound : ℕ) :
    KernelCoveredBound q relator N bound ↔
      ∃ table : BoundedLayerTable (ι := ι) q N bound,
        RelationTableCertifies q relator N bound table := by
  constructor
  · intro hcover
    let table : BoundedLayerTable (ι := ι) q N bound :=
      fun z => Classical.choose (hcover z.property)
    exact ⟨table, fun z => Classical.choose_spec (hcover z.property)⟩
  · rintro ⟨table, htable⟩ x hx
    exact ⟨table ⟨x, hx⟩, htable ⟨x, hx⟩⟩

omit [IsTopologicalGroup F] in
/--
Candidate-kernel-image coverage by one word-length bound is exactly existence
of one bounded quotient-layer candidate-kernel-image relation-word
certificate.
-/
lemma covered_nonempty_certificate
    (q : F →* G)
    (relator : ι → F)
    (N : OpenNormalSubgroup F)
    (bound : ℕ) :
    KernelCoveredBound q relator N bound ↔
      Nonempty (BLCert q relator N bound) := by
  exact (covered_certifying_table
    q relator N bound).trans
      (nonempty_bounded_table
        q relator N bound).symm

omit [IsTopologicalGroup F] in
/--
In a finite quotient layer, eventual bounded relation-word coverage of the
candidate-kernel image is exactly inclusion of the candidate-kernel image in
the algebraic relator image.
-/
lemma bound_covered_relator
    (q : F →* G)
    (relator : ι → F)
    (N : OpenNormalSubgroup F)
    [Finite (ONCompar.OpenNormalLayer N)] :
    (∃ bound : ℕ, KernelCoveredBound q relator N bound) ↔
      ONCompar.kernelImage q N ≤
        ONCompar.relatorImage relator N := by
  constructor
  · rintro ⟨bound, hcover⟩ x hx
    exact bounded_subset_image relator N bound
      (hcover hx)
  · intro hkernel
    rcases bound_set_image relator N with
      ⟨bound, hbound⟩
    exact ⟨bound, fun x hx => hbound.symm ▸ hkernel hx⟩

omit [IsTopologicalGroup F] in
/--
In a finite quotient layer, algebraic kernel generation is exactly eventual
bounded relation-word coverage of the candidate-kernel image.
-/
lemma generated_algebraically_covered
    (q : F →* G)
    (relator : ι → F)
    (N : OpenNormalSubgroup F)
    [Finite (ONCompar.OpenNormalLayer N)] :
    ONFact.GeneratedAlgebraicallyOpen
        q relator N ↔
      ∃ bound : ℕ, KernelCoveredBound q relator N bound := by
  exact
    (ONCompar.algebraically_open_relator
      q relator N).trans
      (bound_covered_relator q relator N).symm

omit [IsTopologicalGroup F] in
/--
For a relator-killing candidate quotient in a finite quotient layer, the
canonical relator-vs-kernel comparison is an isomorphism exactly when the
candidate-kernel image is eventually covered by bounded quotient-layer
relation words.
-/
lemma comparison_kills_relators
    (q : F →* G)
    (relator : ι → F)
    (N : OpenNormalSubgroup F)
    (hkill : Submission.PRFact.KillsRelators relator q)
    [Finite (ONCompar.OpenNormalLayer N)] :
    ONCompar.ImageComparisonIsomorphism
        q relator N hkill ↔
      ∃ bound : ℕ, KernelCoveredBound q relator N bound := by
  exact
    (ONCompar.algebraically_iso_kills
      q relator N hkill).symm.trans
      (generated_algebraically_covered
        q relator N)

/--
For a pro-`p` source and relator-killing candidate quotient, finite relator
quotient factorization is exactly eventual bounded quotient-layer
relation-word coverage of the candidate-kernel image in every open-normal
finite layer.
-/
lemma property_forall_kills
    {p : ℕ}
    [CompactSpace F]
    (hProP : ProP.ProPGroup p F)
    (q : F →* G)
    (relator : ι → F)
    (hkill : Submission.PRFact.KillsRelators relator q) :
    PRQuotie.QuotientFactorizationProperty p relator q ↔
      ∀ N : OpenNormalSubgroup F,
        ∃ bound : ℕ, KernelCoveredBound q relator N bound := by
  rw [ONCompar.property_kills_relators
    hProP q relator hkill]
  exact forall_congr' fun N =>
    comparison_kills_relators
      q relator N hkill

/--
For fixed finite layer and fixed word-length bound, candidate-kernel-image
coverage is a decidable finite search problem.
-/
def kernelCoveredDecidable
    (q : F →* G)
    (relator : ι → F)
    (N : OpenNormalSubgroup F)
    (bound : ℕ)
    [Finite ι]
    [Finite (ONCompar.OpenNormalLayer N)]
    [Finite (ONCompar.kernelImage q N)] :
    Decidable (KernelCoveredBound q relator N bound) := by
  rw [covered_certifying_table]
  exact certifyingBoundedDecidable q relator N bound

end IRScaffo

namespace KRData

/--
The quotient-layer values represented by actual tame Koch relation words of
length at most `bound` in the `n`th canonical Zassenhaus finite layer.
-/
abbrev BoundedRelationSet
    (D : KRData)
    (n : ℕ)
    (bound : ℕ) :=
  boundedRelationSet
    (initialTameRelator D.frobeniusLift)
    (zassenhausOpenSubgroup n)
    bound

/--
The actual initial Koch candidate-kernel image is covered by tame Koch relation
words of length at most `bound` in the `n`th canonical Zassenhaus finite
layer.
-/
def ImageCoveredBound
    (D : KRData)
    (n : ℕ)
    (bound : ℕ) :
    Prop :=
  KernelCoveredBound
    initialKochQuotient
    (initialTameRelator D.frobeniusLift)
    (zassenhausOpenSubgroup n)
    bound

/--
The actual initial Koch candidate-kernel image is eventually covered by bounded
tame Koch relation words in every canonical Zassenhaus finite layer.
-/
def ImageBoundedCoverage
    (D : KRData) :
    Prop :=
  ∀ n : ℕ, ∃ bound : ℕ, D.ImageCoveredBound n bound

/--
At one canonical Zassenhaus depth, the canonical finite-layer relator-vs-
kernel comparison is an isomorphism exactly when bounded tame Koch relation
words eventually cover the actual candidate-kernel image.
-/
lemma comparison_isomorphism_covered
    (D : KRData)
    (n : ℕ) :
    D.CanonicalComparisonIsomorphism n ↔
      ∃ bound : ℕ, D.ImageCoveredBound n bound := by
  letI : Finite (ONCompar.OpenNormalLayer
      (zassenhausOpenSubgroup n)) :=
    pro_p_open (zassenhausOpenSubgroup n)
  exact comparison_kills_relators
    initialKochQuotient
    (initialTameRelator D.frobeniusLift)
    (zassenhausOpenSubgroup n)
    D.tameRelatorsKilled

/--
The concrete finite quotient Koch theorem is exactly eventual bounded tame
Koch relation-word coverage of the actual candidate-kernel image in every
canonical Zassenhaus finite layer.
-/
lemma factorization_theorem_coverage
    (D : KRData) :
    D.KochFactorizationTheorem ↔
      D.ImageBoundedCoverage := by
  rw [D.theorem_comparison_isomorphisms]
  exact forall_congr' fun n =>
    D.comparison_isomorphism_covered n

/--
For fixed canonical Zassenhaus depth and fixed word-length bound, actual tame
Koch candidate-kernel-image coverage is a decidable finite search problem.
-/
def coveredBoundDecidable
    (D : KRData)
    (n : ℕ)
    (bound : ℕ) :
    Decidable (D.ImageCoveredBound n bound) := by
  letI : Finite (ONCompar.OpenNormalLayer
      (zassenhausOpenSubgroup n)) :=
    pro_p_open (zassenhausOpenSubgroup n)
  letI : Finite (ZassenhausLayerImage n) := inferInstance
  exact kernelCoveredDecidable
    initialKochQuotient
    (initialTameRelator D.frobeniusLift)
    (zassenhausOpenSubgroup n)
    bound

end KRData

end TBluepr
end Submission
