import Towers.Group.FinitePRelator.Quotients


open scoped Topology

noncomputable section

namespace Towers
namespace PRQuotie

open PCShadow
open PRFact
open FPQuotie

universe u

/-- A continuous finite discrete `p`-group shadow that is actually surjective. -/
structure QShadow
    (p : ℕ)
    (F : Type u)
    [Group F]
    [TopologicalSpace F]
    extends Shadow p F where
  map_surjective : Function.Surjective toShadow.map

namespace QShadow

variable
    {p : ℕ}
    {F : Type u}
    [Group F]
    [TopologicalSpace F]

/--
Replace a finite `p`-shadow by the surjective quotient onto its image without
changing the kernel.
-/
def ofShadowRange
    (S : Shadow p F) :
    QShadow p F where
  toShadow := {
    Target := S.map.range
    map := S.map.rangeRestrict
    map_continuous := S.map_continuous.subtype_mk (fun x => ⟨x, rfl⟩)
    target_p_group := S.target_p_group.to_subgroup S.map.range
  }
  map_surjective := S.map.rangeRestrict_surjective

@[simp] lemma shadow_range_kernel
    (S : Shadow p F) :
    (ofShadowRange S).map.ker = S.map.ker := by
  exact MonoidHom.ker_rangeRestrict S.map

/--
Combine two finite `p`-group quotients into the quotient onto the image of
their product map.  The new quotient records both quotient tests at once.
-/
def inf
    [Fact p.Prime]
    (S T : QShadow p F) :
    QShadow p F :=
  ofShadowRange (S.toShadow.prod T.toShadow)

@[simp] lemma inf_kernel
    [Fact p.Prime]
    (S T : QShadow p F) :
    (inf S T).map.ker = S.map.ker ⊓ T.map.ker := by
  rw [inf, shadow_range_kernel, Shadow.prod_kernel]

lemma le_kernel_iff
    [Fact p.Prime]
    (S T : QShadow p F)
    (K : Subgroup F) :
    K ≤ (inf S T).map.ker ↔ K ≤ S.map.ker ∧ K ≤ T.map.ker := by
  rw [inf_kernel, le_inf_iff]

/--
The intersection of kernels of all surjective continuous finite `p`-shadows.
-/
def residualQuotientKernel
    (p : ℕ)
    (F : Type u)
    [Group F]
    [TopologicalSpace F] :
    Subgroup F :=
  sInf (Set.range fun S : QShadow p F => S.map.ker)

lemma quotient_kernel
    (S : QShadow p F) :
    residualQuotientKernel p F ≤ S.map.ker := by
  exact sInf_le ⟨S, rfl⟩

lemma residual_quotient :
    residualKernel p F ≤ residualQuotientKernel p F := by
  apply le_sInf
  rintro K ⟨S, rfl⟩
  exact residual_le_kernel S.toShadow

lemma residual_kernel :
    residualQuotientKernel p F ≤ residualKernel p F := by
  apply le_sInf
  rintro K ⟨S, rfl⟩
  have hrange :
      residualQuotientKernel p F ≤ (ofShadowRange S).map.ker :=
    quotient_kernel (ofShadowRange S)
  simpa using hrange

lemma residual_kernel_quotient :
    residualKernel p F = residualQuotientKernel p F := by
  apply le_antisymm
  · exact residual_quotient
  · exact residual_kernel

end QShadow

/--
A surjective continuous finite `p`-group quotient whose map kills a displayed
relator family.
-/
structure RQShadow
    (p : ℕ)
    (F : Type u)
    [Group F]
    [TopologicalSpace F]
    {ι : Type*}
    (relator : ι → F)
    extends RShadow p F relator where
  map_surjective : Function.Surjective toRShadow.map

namespace RQShadow

variable
    {p : ℕ}
    {F P : Type u}
    [Group F]
    [TopologicalSpace F]
    [IsTopologicalGroup F]
    [Group P]
    {ι : Type*}
    {relator : ι → F}

def toQShadow
    (S : RQShadow p F relator) :
    QShadow p F where
  toShadow := S.toRShadow.toShadow
  map_surjective := S.map_surjective

/-- Package an actual surjective continuous finite discrete `p`-group quotient. -/
def ofMap
    [TopologicalSpace P]
    [DiscreteTopology P]
    [Finite P]
    (α : F →* P)
    (hα : Continuous α)
    (hαsurj : Function.Surjective α)
    (hP : IsPGroup p P)
    (hkill : KillsRelators relator α) :
    RQShadow p F relator where
  toRShadow := RShadow.ofMap α hα hP hkill
  map_surjective := hαsurj

/--
Replace a relator-killing finite `p`-shadow by the surjective quotient onto
its image without changing the kernel or the relator equations.
-/
def relatorShadowRange
    (S : RShadow p F relator) :
    RQShadow p F relator where
  toRShadow := {
    toShadow := {
      Target := S.map.range
      map := S.map.rangeRestrict
      map_continuous := S.toShadow.map_continuous.subtype_mk (fun x => ⟨x, rfl⟩)
      target_p_group := S.toShadow.target_p_group.to_subgroup S.map.range
    }
    relator_killed := by
      intro i
      apply Subtype.ext
      exact S.relator_killed i
  }
  map_surjective := S.map.rangeRestrict_surjective

omit [IsTopologicalGroup F] in
@[simp] lemma relator_shadow_range
    (S : RShadow p F relator) :
    (relatorShadowRange S).map.ker = S.map.ker := by
  exact MonoidHom.ker_rangeRestrict S.map

/--
Combine two finite relator-killing `p`-group quotients into a common finite
relator-killing quotient whose kernel is their intersection.
-/
def inf
    [Fact p.Prime]
    (S T : RQShadow p F relator) :
    RQShadow p F relator :=
  relatorShadowRange (S.toRShadow.prod T.toRShadow)

omit [IsTopologicalGroup F] in
@[simp] lemma inf_kernel
    [Fact p.Prime]
    (S T : RQShadow p F relator) :
    (inf S T).map.ker = S.map.ker ⊓ T.map.ker := by
  rw [inf, relator_shadow_range, RShadow.prod_kernel]

omit [IsTopologicalGroup F] in
lemma le_kernel_iff
    [Fact p.Prime]
    (S T : RQShadow p F relator)
    (K : Subgroup F) :
    K ≤ (inf S T).map.ker ↔ K ≤ S.map.ker ∧ K ≤ T.map.ker := by
  rw [inf_kernel, le_inf_iff]

/-- The trivial finite relator-killing quotient, used as the empty refinement. -/
def trivial :
    RQShadow p F relator where
  toRShadow := {
    toShadow := {
      Target := PUnit
      map := 1
      map_continuous := continuous_const
      target_p_group := by
        apply IsPGroup.of_card (n := 0)
        simp
    }
    relator_killed := by
      intro i
      simp
  }
  map_surjective := by
    intro y
    exact ⟨1, Subsingleton.elim _ _⟩

omit [IsTopologicalGroup F] in
@[simp] lemma trivial_kernel :
    (trivial (p := p) (F := F) (relator := relator)).map.ker = ⊤ := by
  exact MonoidHom.ker_one

/--
Combine a finite list of finite relator-killing `p`-group quotients into one
common refinement.
-/
def infList
    [Fact p.Prime] :
    List (RQShadow p F relator) →
      RQShadow p F relator
  | [] => trivial
  | S :: shadows => inf S (infList shadows)

omit [IsTopologicalGroup F] in
lemma inf_list
    [Fact p.Prime]
    (shadows : List (RQShadow p F relator))
    (K : Subgroup F) :
    K ≤ (infList shadows).map.ker ↔
      ∀ S ∈ shadows, K ≤ S.map.ker := by
  induction shadows with
  | nil =>
      rw [infList, trivial_kernel]
      simp
  | cons S shadows ih =>
      rw [infList, inf_kernel, le_inf_iff, ih]
      simp [List.mem_cons]

omit [IsTopologicalGroup F] in
lemma inf_list_kernel
    [Fact p.Prime]
    (shadows : List (RQShadow p F relator))
    (S : RQShadow p F relator)
    (hS : S ∈ shadows) :
    (infList shadows).map.ker ≤ S.map.ker := by
  have hcommon :
      (infList shadows).map.ker ≤ (infList shadows).map.ker :=
    le_rfl
  exact (inf_list shadows (infList shadows).map.ker).mp hcommon S hS

omit [IsTopologicalGroup F] in
lemma exists_common_refinement
    [Fact p.Prime]
    (shadows : List (RQShadow p F relator)) :
    ∃ S : RQShadow p F relator,
      ∀ T ∈ shadows, S.map.ker ≤ T.map.ker := by
  exact ⟨infList shadows, fun T hT => inf_list_kernel shadows T hT⟩

end RQShadow

variable
    {p : ℕ}
    {F G P : Type u}
    [Group F]
    [TopologicalSpace F]
    [IsTopologicalGroup F]
    [Group G]
    [Group P]
    {ι : Type*}
    {relator : ι → F}
    {q : F →* G}
    {α : F →* P}

/--
The finite quotient form of the relator factorization property: every
surjective finite `p`-group quotient killing the relators kills the candidate
kernel.
-/
def QuotientFactorizationProperty
    (p : ℕ)
    {F G : Type u}
    [Group F]
    [TopologicalSpace F]
    [Group G]
    {ι : Type*}
    (relator : ι → F)
    (q : F →* G) :
    Prop :=
  ∀ S : RQShadow p F relator, q.ker ≤ S.map.ker

omit [IsTopologicalGroup F] in
/--
It is enough to test relator factorization on actual finite `p`-group
quotients: arbitrary finite `p`-group maps have the same kernel as their image
quotient.
-/
lemma factorization_property_quotient :
    FactorizationProperty p relator q ↔
      QuotientFactorizationProperty p relator q := by
  constructor
  · intro hfactor S
    exact hfactor S.toRShadow
  · intro hfactor S
    have hRange :
        q.ker ≤ (RQShadow.relatorShadowRange S).map.ker :=
      hfactor (RQShadow.relatorShadowRange S)
    simpa using hRange

omit [IsTopologicalGroup F] in
lemma factorization_property_relator :
    QuotientFactorizationProperty p relator q ↔ q.ker ≤ relatorKernel p relator := by
  rw [← factorization_property_quotient]
  exact factorization_property_kernel

lemma property_comap_residual :
    QuotientFactorizationProperty p relator q ↔
      q.ker ≤
        (residualKernel p (completedRelatorQuotient relator)).comap
          (quotientMap relator) := by
  rw [← factorization_property_quotient]
  exact factorization_property_comap

lemma
property_residually_p
    [Fact p.Prime]
    (hres : RFP p (completedRelatorQuotient relator)) :
    QuotientFactorizationProperty p relator q ↔
      q.ker ≤ completedRelationSubgroup relator := by
  rw [← factorization_property_quotient]
  exact
    factorization_property_residually
      hres

omit [IsTopologicalGroup F] in
lemma factorization_property_group
    [TopologicalSpace P]
    [DiscreteTopology P]
    [Finite P]
    (hfactor : QuotientFactorizationProperty p relator q)
    (hα : Continuous α)
    (hP : IsPGroup p P)
    (hkill : KillsRelators relator α) :
    q.ker ≤ α.ker := by
  let S : RShadow p F relator :=
    RShadow.ofMap α hα hP hkill
  have hRange :
      q.ker ≤ (RQShadow.relatorShadowRange S).map.ker :=
    hfactor (RQShadow.relatorShadowRange S)
  rw [RQShadow.relator_shadow_range] at hRange
  simpa [S, RShadow.ofMap] using hRange

omit [IsTopologicalGroup F] in
lemma uniquely_through_property
    [TopologicalSpace P]
    [DiscreteTopology P]
    [Finite P]
    (hq : Function.Surjective q)
    (hfactor : QuotientFactorizationProperty p relator q)
    (hα : Continuous α)
    (hP : IsPGroup p P)
    (hkill : KillsRelators relator α) :
    FactorsUniquelyThrough q α := by
  apply factors_uniquely_ker q α hq
  exact factorization_property_group
    hfactor hα hP hkill

omit [IsTopologicalGroup F] in
lemma property_quotients_uniquely
    (hq : Function.Surjective q) :
    QuotientFactorizationProperty p relator q ↔
      ∀ S : RQShadow p F relator,
        FactorsUniquelyThrough q S.map := by
  constructor
  · intro hfactor S
    exact factors_uniquely_ker q S.map hq (hfactor S)
  · intro hfactor S
    exact (uniquely_through_ker q S.map hq).mp (hfactor S)

end PRQuotie
end Towers
