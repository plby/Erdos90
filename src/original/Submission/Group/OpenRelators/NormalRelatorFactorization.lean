import Submission.Group.FinitePRelator.FiniteQuotients
import Submission.Group.ProPClosed


open scoped Topology

noncomputable section

namespace Submission
namespace ONFact

open PCShadow
open PRFact
open PRQuotie

universe u

variable
    {p : ℕ}
    {F G : Type u}
    [Group F]
    [TopologicalSpace F]
    [IsTopologicalGroup F]
    [CompactSpace F]
    [Group G]
    {ι : Type*}
    {relator : ι → F}

/--
An open-normal finite shadow after killing the image of the displayed relators
algebraically in that shadow.
-/
def algebraicOpenNormal
    (hProP : ProP.ProPGroup p F)
    (N : OpenNormalSubgroup F) :
    RQShadow p F relator := by
  let qN : F →* F ⧸ (N : Subgroup F) := QuotientGroup.mk' (N : Subgroup F)
  let RN : Subgroup (F ⧸ (N : Subgroup F)) :=
    (relationSubgroup relator).map qN
  letI : DiscreteTopology (F ⧸ (N : Subgroup F)) :=
    pro_discrete_topology N
  letI : Finite (F ⧸ (N : Subgroup F)) :=
    pro_p_open N
  letI : DiscreteTopology ((F ⧸ (N : Subgroup F)) ⧸ RN) :=
    QuotientGroup.discreteTopology (isOpen_discrete _)
  letI : Finite ((F ⧸ (N : Subgroup F)) ⧸ RN) :=
    Finite.of_surjective (QuotientGroup.mk' RN) (QuotientGroup.mk'_surjective RN)
  exact RQShadow.ofMap
    ((QuotientGroup.mk' RN).comp qN)
    ((QuotientGroup.continuous_mk).comp (pro_open_continuous N))
    ((QuotientGroup.mk'_surjective RN).comp (QuotientGroup.mk'_surjective (N : Subgroup F)))
    ((hProP N).to_quotient RN)
    (by
      intro i
      apply (QuotientGroup.eq_one_iff (N := RN) (qN (relator i))).2
      exact ⟨relator i, relator_relation_subgroup relator i, rfl⟩)

lemma algebraic_open_relator
    (hProP : ProP.ProPGroup p F)
    (N : OpenNormalSubgroup F)
    (x : F) :
    x ∈ (algebraicOpenNormal hProP N (relator := relator)).map.ker ↔
      QuotientGroup.mk' (N : Subgroup F) x ∈
        (relationSubgroup relator).map (QuotientGroup.mk' (N : Subgroup F)) := by
  change
    QuotientGroup.mk'
        ((relationSubgroup relator).map (QuotientGroup.mk' (N : Subgroup F)))
        (QuotientGroup.mk' (N : Subgroup F) x) = 1 ↔
      QuotientGroup.mk' (N : Subgroup F) x ∈
        (relationSubgroup relator).map (QuotientGroup.mk' (N : Subgroup F))
  exact QuotientGroup.eq_one_iff _

/-- The open-normal subgroup cut out by the kernel of a finite quotient shadow. -/
def kernelOpenSubgroup
    (S : RQShadow p F relator) :
    OpenNormalSubgroup F where
  toOpenSubgroup := ⟨S.map.ker, S.toRShadow.toShadow.kernel_isOpen⟩
  isNormal' := inferInstance

omit [IsTopologicalGroup F] [CompactSpace F] in
@[simp] lemma kernel_open_subgroup
    (S : RQShadow p F relator) :
    (kernelOpenSubgroup S : Subgroup F) = S.map.ker := rfl

/--
Algebraic relation-subgroup generation in one open-normal quotient: modulo
`N`, every candidate-kernel element lies in the image of the ordinary normal
closure of the displayed relators.
-/
def GeneratedAlgebraicallyOpen
    (q : F →* G)
    (relator : ι → F)
    (N : OpenNormalSubgroup F) :
    Prop :=
  ∀ x ∈ q.ker,
    QuotientGroup.mk' (N : Subgroup F) x ∈
      (relationSubgroup relator).map (QuotientGroup.mk' (N : Subgroup F))

/--
Algebraic relation-subgroup generation in every open-normal quotient.
-/
def GeneratedAlgebraicallyEvery
    (q : F →* G)
    (relator : ι → F) :
    Prop :=
  ∀ N : OpenNormalSubgroup F,
    GeneratedAlgebraicallyOpen q relator N

/--
The subgroup detected by algebraically killing the displayed relators in every
open-normal quotient.
-/
def algebraicOpenKernel
    (relator : ι → F) :
    Subgroup F :=
  ⨅ N : OpenNormalSubgroup F,
    ((relationSubgroup relator).map (QuotientGroup.mk' (N : Subgroup F))).comap
      (QuotientGroup.mk' (N : Subgroup F))

omit [IsTopologicalGroup F] [CompactSpace F] in
lemma algebraic_relator_kernel
    (relator : ι → F)
    (x : F) :
    x ∈ algebraicOpenKernel relator ↔
      ∀ N : OpenNormalSubgroup F,
        QuotientGroup.mk' (N : Subgroup F) x ∈
          (relationSubgroup relator).map (QuotientGroup.mk' (N : Subgroup F)) := by
  rw [algebraicOpenKernel, Subgroup.mem_iInf]
  rfl

omit [IsTopologicalGroup F] [CompactSpace F] in
lemma algebraically_every_relator
    (q : F →* G)
    (relator : ι → F) :
    GeneratedAlgebraicallyEvery q relator ↔
      q.ker ≤ algebraicOpenKernel relator := by
  constructor
  · intro hgen x hx
    rw [algebraic_relator_kernel]
    intro N
    exact hgen N x hx
  · intro hkernel N x hx
    exact (algebraic_relator_kernel relator x).mp (hkernel hx) N

/--
For a pro-`p` source, the finite-`p` relator residual kernel is exactly the
intersection of the algebraic relator kernels in all open-normal finite
layers.
-/
lemma relator_algebraic_pro
    (hProP : ProP.ProPGroup p F) :
    relatorKernel p relator = algebraicOpenKernel relator := by
  ext x
  constructor
  · intro hx
    rw [algebraic_relator_kernel]
    intro N
    exact (algebraic_open_relator hProP N x).mp
      (relator_kernel (algebraicOpenNormal hProP N).toRShadow hx)
  · intro hx
    rw [mem_relator_iff]
    intro S
    let T : RQShadow p F relator :=
      RQShadow.relatorShadowRange S
    let N : OpenNormalSubgroup F := kernelOpenSubgroup T
    rcases (algebraic_relator_kernel relator x).mp hx N with ⟨y, hyrel, hyx⟩
    have hyker : y ∈ T.map.ker :=
      (kills_relators_relation relator T.map).mp
        T.relator_killed hyrel
    have hdiff : y⁻¹ * x ∈ T.map.ker := by
      simpa [N] using (inv_mul_quotient (N := N) hyx)
    have hxT : x ∈ T.map.ker := by
      simpa [mul_assoc] using T.map.ker.mul_mem hyker hdiff
    simpa [T] using hxT

/--
For a pro-`p` source, testing the candidate kernel against all finite
relator-killing `p`-group quotients is equivalent to algebraic normal
generation modulo every open-normal quotient.
-/
lemma property_every_pro
    (hProP : ProP.ProPGroup p F)
    (q : F →* G) :
    QuotientFactorizationProperty p relator q ↔
      GeneratedAlgebraicallyEvery q relator := by
  constructor
  · intro hfactor N x hx
    exact (algebraic_open_relator hProP N x).mp
      (hfactor (algebraicOpenNormal hProP N) hx)
  · intro hgen S x hx
    let N : OpenNormalSubgroup F := kernelOpenSubgroup S
    rcases hgen N x hx with ⟨y, hyrel, hyx⟩
    have hyker : y ∈ S.map.ker :=
      (kills_relators_relation relator S.map).mp
        S.relator_killed hyrel
    have hdiff : y⁻¹ * x ∈ S.map.ker := by
      simpa [N] using (inv_mul_quotient (N := N) hyx)
    simpa [mul_assoc] using S.map.ker.mul_mem hyker hdiff

/--
The full finite-`p` map factorization property has the same open-normal
algebraic-shadow formulation.
-/
lemma property_algebraically_every
    (hProP : ProP.ProPGroup p F)
    (q : F →* G) :
    FactorizationProperty p relator q ↔
      GeneratedAlgebraicallyEvery q relator := by
  rw [factorization_property_quotient]
  exact property_every_pro
    hProP q

end ONFact
end Submission
