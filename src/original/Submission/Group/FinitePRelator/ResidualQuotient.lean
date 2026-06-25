import Submission.Group.FinitePRelator.ContinuousFactorization


open scoped Topology

noncomputable section

namespace Submission
namespace RRQuot

open PCShadow
open PRFact
open FPQuotie
open PRQuotie
open RPQuotie
open RCFact

universe u

variable
    {p : ℕ}
    {F P : Type u}
    [Group F]
    [TopologicalSpace F]
    [IsTopologicalGroup F]
    [Group P]
    {ι : Type*}
    (relator : ι → F)

/--
The relator residual kernel is closed: it is the intersection of the closed
kernels of all continuous finite relator-killing `p`-shadows.
-/
instance relator_kernel_closed :
    IsClosed (((relatorKernel p relator : Subgroup F) : Set F)) := by
  rw [show ((relatorKernel p relator : Subgroup F) : Set F) =
      ⋂ S : RShadow p F relator, (S.map.ker : Set F) by
    ext x
    simp [mem_relator_iff]]
  exact isClosed_iInter fun S => S.toShadow.kernel_isClosed

/--
The canonical quotient visible to all continuous finite relator-killing
`p`-shadows.
-/
abbrev relatorResidualQuotient :=
  F ⧸ relatorKernel p relator

/-- The canonical map to the relator residual quotient. -/
def residualQuotientMap :
    F →* relatorResidualQuotient (p := p) relator :=
  QuotientGroup.mk' (relatorKernel p relator)

omit [IsTopologicalGroup F] in
lemma residual_quotient_surjective :
    Function.Surjective (residualQuotientMap (p := p) relator) := by
  exact QuotientGroup.mk'_surjective (relatorKernel p relator)

omit [IsTopologicalGroup F] in
lemma residual_quotient_continuous :
    Continuous (residualQuotientMap (p := p) relator) := by
  change Continuous (QuotientGroup.mk : F → relatorResidualQuotient (p := p) relator)
  exact QuotientGroup.continuous_mk

omit [IsTopologicalGroup F] in
lemma map_is_map :
    Topology.IsQuotientMap (residualQuotientMap (p := p) relator) := by
  exact QuotientGroup.isQuotientMap_mk (relatorKernel p relator)

omit [IsTopologicalGroup F] in
@[simp] lemma ker_residual_quotient :
    (residualQuotientMap (p := p) relator).ker = relatorKernel p relator := by
  exact QuotientGroup.ker_mk' (relatorKernel p relator)

@[simp] lemma residual_relator_one
    (i : ι) :
    residualQuotientMap (p := p) relator (relator i) = 1 := by
  apply (QuotientGroup.eq_one_iff (relator i)).mpr
  exact completed_relation_relator
    (relator_completed_subgroup relator i)

namespace RShadow

/--
Descend a finite relator-killing `p`-shadow to a finite `p`-shadow of the
relator residual quotient.
-/
def descendResidualQuotient
    (S : RShadow p F relator) :
    Shadow p (relatorResidualQuotient (p := p) relator) where
  Target := S.Target
  map := QuotientGroup.lift
    (relatorKernel p relator)
    S.map
    (relator_kernel S)
  map_continuous := by
    apply (map_is_map (p := p) relator).continuous_iff.mpr
    change Continuous
      (fun x : F => QuotientGroup.lift (relatorKernel p relator) S.map
        (relator_kernel S) (residualQuotientMap (p := p) relator x))
    simpa [Function.comp_def] using S.toShadow.map_continuous
  target_p_group := S.toShadow.target_p_group

omit [IsTopologicalGroup F] in
lemma descend_residual_comp
    (S : RShadow p F relator) :
    (descendResidualQuotient relator S).map.comp (residualQuotientMap (p := p) relator) =
      S.map := by
  exact QuotientGroup.lift_comp_mk'
    (relatorKernel p relator)
    S.map
    (relator_kernel S)

omit [IsTopologicalGroup F] in
lemma descend_residual_kernel
    (S : RShadow p F relator)
    (x : F) :
    residualQuotientMap (p := p) relator x ∈
        (descendResidualQuotient relator S).map.ker ↔
      x ∈ S.map.ker := by
  change (descendResidualQuotient relator S).map
      (residualQuotientMap (p := p) relator x) = 1 ↔
    S.map x = 1
  rw [show (descendResidualQuotient relator S).map
      (residualQuotientMap (p := p) relator x) =
      S.map x by
    exact congrArg (fun φ : F →* S.Target => φ x)
      (descend_residual_comp relator S)]
  rfl

end RShadow

namespace Shadow

/--
Pull a finite `p`-shadow of the relator residual quotient back to a finite
relator-killing `p`-shadow of the original group.
-/
def pullbackAlongResidual
    (S : Shadow p (relatorResidualQuotient (p := p) relator)) :
    RShadow p F relator where
  toShadow := S.pullback
    (residualQuotientMap (p := p) relator)
    (residual_quotient_continuous (p := p) relator)
  relator_killed := by
    intro i
    change S.map (residualQuotientMap (p := p) relator (relator i)) = 1
    rw [residual_relator_one (p := p) relator i]
    exact S.map.map_one

lemma pullback_along_quotient
    (S : Shadow p (relatorResidualQuotient (p := p) relator)) :
    (pullbackAlongResidual relator S).map =
      S.map.comp (residualQuotientMap (p := p) relator) := rfl

lemma pullback_along_residual
    (S : Shadow p (relatorResidualQuotient (p := p) relator))
    (x : F) :
    x ∈ (pullbackAlongResidual relator S).map.ker ↔
      residualQuotientMap (p := p) relator x ∈ S.map.ker := by
  exact S.pullback_kernel
    (residualQuotientMap (p := p) relator)
    (residual_quotient_continuous (p := p) relator)
    x

lemma descend_pullback_along
    (S : Shadow p (relatorResidualQuotient (p := p) relator)) :
    (RShadow.descendResidualQuotient relator
      (pullbackAlongResidual relator S)).map =
      S.map := by
  apply MonoidHom.ext
  intro y
  rcases residual_quotient_surjective (p := p) relator y with ⟨x, rfl⟩
  have hcomp :=
    RShadow.descend_residual_comp relator
      (pullbackAlongResidual relator S)
  have happ := congrArg (fun φ : F →* S.Target => φ x) hcomp
  change (RShadow.descendResidualQuotient relator
      (pullbackAlongResidual relator S)).map
      (residualQuotientMap (p := p) relator x) =
    (pullbackAlongResidual relator S).map x at happ
  simpa [pullback_along_quotient] using happ

end Shadow

/--
The relator residual kernel is exactly the pullback of the ordinary finite
`p` residual kernel of the relator residual quotient.
-/
lemma relator_comap_residual :
    relatorKernel p relator =
      (residualKernel p (relatorResidualQuotient (p := p) relator)).comap
        (residualQuotientMap (p := p) relator) := by
  ext x
  constructor
  · intro hx
    rw [Subgroup.mem_comap, residual_kernel_iff]
    intro S
    have hxPullback :
        x ∈ (Shadow.pullbackAlongResidual relator S).map.ker := by
      exact relator_kernel (Shadow.pullbackAlongResidual relator S) hx
    exact (Shadow.pullback_along_residual relator S x).mp hxPullback
  · intro hx
    rw [mem_relator_iff]
    intro S
    rw [Subgroup.mem_comap, residual_kernel_iff] at hx
    have hxDescend :
        residualQuotientMap (p := p) relator x ∈
          (RShadow.descendResidualQuotient relator S).map.ker :=
      hx (RShadow.descendResidualQuotient relator S)
    exact (RShadow.descend_residual_kernel
      relator S x).mp
      hxDescend

/-- The relator residual quotient is residually finite `p`. -/
lemma relator_residually_p :
    RFP p (relatorResidualQuotient (p := p) relator) := by
  apply le_antisymm
  · intro y hy
    rw [Subgroup.mem_bot]
    rcases residual_quotient_surjective (p := p) relator y with ⟨x, rfl⟩
    apply (QuotientGroup.eq_one_iff x).mpr
    rw [relator_comap_residual (p := p) relator]
    change residualQuotientMap (p := p) relator x ∈
      residualKernel p (relatorResidualQuotient (p := p) relator)
    exact hy
  · exact bot_le

/--
The completed relator quotient maps canonically onto the relator residual
quotient.
-/
def completedResidualProjection :
    completedRelatorQuotient relator →* relatorResidualQuotient (p := p) relator :=
  descendMap
    relator
    (residualQuotientMap (p := p) relator)
    (residual_quotient_continuous (p := p) relator)
    (by
      intro i
      exact residual_relator_one (p := p) relator i)

lemma completed_projection_comp :
    (completedResidualProjection (p := p) relator).comp
        (FPQuotie.quotientMap relator) =
      residualQuotientMap (p := p) relator := by
  exact descend_comp
    relator
    (residualQuotientMap (p := p) relator)
    (residual_quotient_continuous (p := p) relator)
    (by
      intro i
      exact residual_relator_one (p := p) relator i)

lemma completed_projection_continuous :
    Continuous (completedResidualProjection (p := p) relator) := by
  exact descendMap_continuous
    relator
    (residualQuotientMap (p := p) relator)
    (residual_quotient_continuous (p := p) relator)
    (by
      intro i
      exact residual_relator_one (p := p) relator i)

lemma completed_projection_surjective :
    Function.Surjective (completedResidualProjection (p := p) relator) := by
  intro y
  rcases residual_quotient_surjective (p := p) relator y with ⟨x, rfl⟩
  exact ⟨FPQuotie.quotientMap relator x, by
    simpa using congrArg
      (fun φ : F →* relatorResidualQuotient (p := p) relator => φ x)
      (completed_projection_comp (p := p) relator)⟩

lemma completed_residual_projection :
    (completedResidualProjection (p := p) relator).ker =
      residualKernel p (completedRelatorQuotient relator) := by
  ext y
  rcases FPQuotie.quotientMap_surjective relator y with ⟨x, rfl⟩
  have hcomp := congrArg
    (fun φ : F →* relatorResidualQuotient (p := p) relator => φ x)
    (completed_projection_comp (p := p) relator)
  change completedResidualProjection (p := p) relator
      (FPQuotie.quotientMap relator x) = 1 ↔
    FPQuotie.quotientMap relator x ∈
      residualKernel p (completedRelatorQuotient relator)
  change completedResidualProjection (p := p) relator
      (FPQuotie.quotientMap relator x) =
    residualQuotientMap (p := p) relator x at hcomp
  rw [hcomp]
  change x ∈ (residualQuotientMap (p := p) relator).ker ↔
    FPQuotie.quotientMap relator x ∈
      residualKernel p (completedRelatorQuotient relator)
  rw [ker_residual_quotient, kernel_comap_residual]
  rfl

lemma completed_projection_residually
    (hres : RFP p (completedRelatorQuotient relator)) :
    Function.Injective (completedResidualProjection (p := p) relator) := by
  apply (MonoidHom.ker_eq_bot_iff (completedResidualProjection (p := p) relator)).mp
  rw [completed_residual_projection, hres]

/--
If the completed relator quotient is already residually finite `p`, it is
canonically isomorphic to the relator residual quotient.
-/
noncomputable def completedResiduallyP
    (hres : RFP p (completedRelatorQuotient relator)) :
    completedRelatorQuotient relator ≃* relatorResidualQuotient (p := p) relator :=
  MulEquiv.ofBijective
    (completedResidualProjection (p := p) relator)
    ⟨completed_projection_residually
        (p := p) relator hres,
      completed_projection_surjective (p := p) relator⟩

omit [IsTopologicalGroup F] in
lemma residual_factorization_property :
    QuotientFactorizationProperty p relator (residualQuotientMap (p := p) relator) := by
  apply (factorization_property_relator).2
  rw [ker_residual_quotient]

/-- The relator residual quotient as a presented quotient candidate. -/
def relatorResidualPresented :
    PQuot
      (G := relatorResidualQuotient (p := p) relator)
      relator where
  quotientMap := residualQuotientMap (p := p) relator
  quotientMap_continuous := residual_quotient_continuous (p := p) relator
  quotientMap_surjective := residual_quotient_surjective (p := p) relator
  relator_killed := residual_relator_one (p := p) relator

lemma relator_presented_universal :
    (relatorResidualPresented (p := p) relator).FinitePUniversal p := by
  exact residual_factorization_property (p := p) relator

lemma relator_presented_topological :
    RCFact.PQuot.IsTopologicalQuotient
      (relatorResidualPresented (p := p) relator) := by
  exact map_is_map (p := p) relator

namespace PQuot

variable
    {G : Type u}
    [Group G]
    [TopologicalSpace G]
    [T1Space G]
    (Q : PQuot (G := G) relator)

namespace Shadow

/-- Pull a finite `p`-shadow of a presented quotient target back to a relator shadow of `F`. -/
def pullbackAlongPresented
    (S : Shadow p G) :
    RShadow p F relator where
  toShadow := S.pullback Q.quotientMap Q.quotientMap_continuous
  relator_killed := by
    intro i
    change S.map (Q.quotientMap (relator i)) = 1
    rw [Q.relator_killed i]
    exact S.map.map_one

lemma pullback_along_presented
    (S : Shadow p G)
    (x : F) :
    x ∈ (pullbackAlongPresented relator Q S).map.ker ↔
      Q.quotientMap x ∈ S.map.ker := by
  exact S.pullback_kernel Q.quotientMap Q.quotientMap_continuous x

end Shadow

/--
If the target presented quotient is residually finite `p`, every element
invisible to finite relator shadows already lies in the candidate kernel.
-/
lemma relator_residually_target
    (hres : RFP p G) :
    relatorKernel p relator ≤ Q.quotientMap.ker := by
  intro x hx
  rw [MonoidHom.mem_ker]
  have hxResidual : Q.quotientMap x ∈ residualKernel p G := by
    rw [residual_kernel_iff]
    intro S
    have hxPullback :
        x ∈ (Shadow.pullbackAlongPresented relator Q S).map.ker := by
      exact relator_kernel (Shadow.pullbackAlongPresented relator Q S) hx
    exact (Shadow.pullback_along_presented relator Q S x).mp hxPullback
  rw [hres] at hxResidual
  exact Subgroup.mem_bot.mp hxResidual

lemma residually_fin_target
    (hUniversal : Q.FinitePUniversal p)
    (hres : RFP p G) :
    Q.quotientMap.ker = relatorKernel p relator := by
  apply le_antisymm
  · exact (factorization_property_relator).mp hUniversal
  · exact relator_residually_target relator Q hres

lemma factors_unique_through :
    Q.FinitePUniversal p ↔
      FactorsUniquelyThrough Q.quotientMap (residualQuotientMap (p := p) relator) := by
  constructor
  · intro hUniversal
    apply factors_uniquely_ker
      Q.quotientMap
      (residualQuotientMap (p := p) relator)
      Q.quotientMap_surjective
    rw [ker_residual_quotient]
    exact (factorization_property_relator).mp hUniversal
  · intro hfactor
    apply (factorization_property_relator).2
    rw [← ker_residual_quotient]
    exact (uniquely_through_ker
      Q.quotientMap
      (residualQuotientMap (p := p) relator)
      Q.quotientMap_surjective).mp hfactor

/-- The canonical projection from a finite-`p` universal candidate to the
relator residual quotient. -/
noncomputable def residualProjection
    (hUniversal : Q.FinitePUniversal p) :
    G →* relatorResidualQuotient (p := p) relator :=
  factorSurjective
    Q.quotientMap
    (residualQuotientMap (p := p) relator)
    Q.quotientMap_surjective
    (by
      rw [ker_residual_quotient]
      exact (factorization_property_relator).mp hUniversal)

lemma projection_comp_quotient
    (hUniversal : Q.FinitePUniversal p) :
    (residualProjection relator Q hUniversal).comp Q.quotientMap =
      residualQuotientMap (p := p) relator := by
  exact factor_map_of
    Q.quotientMap
    (residualQuotientMap (p := p) relator)
    Q.quotientMap_surjective
    (by
      rw [ker_residual_quotient]
      exact (factorization_property_relator).mp hUniversal)

lemma residualProjection_surjective
    (hUniversal : Q.FinitePUniversal p) :
    Function.Surjective (residualProjection relator Q hUniversal) := by
  intro y
  rcases residual_quotient_surjective (p := p) relator y with ⟨x, rfl⟩
  exact ⟨Q.quotientMap x, by
    simpa using congrArg
      (fun φ : F →* relatorResidualQuotient (p := p) relator => φ x)
      (projection_comp_quotient relator Q hUniversal)⟩

lemma residualProjection_continuous
    (hquot : RCFact.PQuot.IsTopologicalQuotient Q)
    (hUniversal : Q.FinitePUniversal p) :
    Continuous (residualProjection relator Q hUniversal) := by
  exact continuous_factor_quotient
    Q.quotientMap
    (residualQuotientMap (p := p) relator)
    hquot
    (residual_quotient_continuous (p := p) relator)
    (by
      rw [ker_residual_quotient]
      exact (factorization_property_relator).mp hUniversal)

lemma residual_projection_relator
    (hUniversal : Q.FinitePUniversal p)
    (hker : Q.quotientMap.ker = relatorKernel p relator) :
    Function.Injective (residualProjection relator Q hUniversal) := by
  apply (MonoidHom.ker_eq_bot_iff (residualProjection relator Q hUniversal)).mp
  apply le_antisymm
  · intro y hy
    rw [Subgroup.mem_bot]
    rcases Q.quotientMap_surjective y with ⟨x, rfl⟩
    have hxResidual :
        residualQuotientMap (p := p) relator x = 1 := by
      have hxProjection :
          residualProjection relator Q hUniversal (Q.quotientMap x) = 1 :=
        MonoidHom.mem_ker.mp hy
      have hcomp := congrArg
        (fun φ : F →* relatorResidualQuotient (p := p) relator => φ x)
        (projection_comp_quotient relator Q hUniversal)
      change residualProjection relator Q hUniversal (Q.quotientMap x) =
        residualQuotientMap (p := p) relator x at hcomp
      exact hcomp.symm.trans hxProjection
    have hxRelator : x ∈ relatorKernel p relator :=
      (QuotientGroup.eq_one_iff x).mp hxResidual
    have hxKernel : x ∈ Q.quotientMap.ker := by
      rw [hker]
      exact hxRelator
    exact MonoidHom.mem_ker.mp hxKernel
  · exact bot_le

lemma residual_residually_target
    (hUniversal : Q.FinitePUniversal p)
    (hres : RFP p G) :
    Function.Injective (residualProjection relator Q hUniversal) := by
  exact residual_projection_relator
    relator
    Q
    hUniversal
    (residually_fin_target
      relator Q hUniversal hres)

/--
A finite-`p` universal residually finite `p` target is canonically isomorphic to
the relator residual quotient.
-/
noncomputable def projectionResiduallyP
    (hUniversal : Q.FinitePUniversal p)
    (hres : RFP p G) :
    G ≃* relatorResidualQuotient (p := p) relator :=
  MulEquiv.ofBijective
    (residualProjection relator Q hUniversal)
    ⟨residual_residually_target
        relator Q hUniversal hres,
      residualProjection_surjective relator Q hUniversal⟩

end PQuot

end RRQuot
end Submission
