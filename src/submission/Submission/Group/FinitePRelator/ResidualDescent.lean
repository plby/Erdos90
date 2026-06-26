import Submission.Group.FinitePRelator.ResidualQuotient


open scoped Topology

noncomputable section

namespace Submission
namespace RRDescen

open PCShadow
open PRFact
open FPQuotie
open PRQuotie
open RPQuotie
open RCFact
open RRQuot
open RRQuot.PQuot

universe u

variable
    {p : ℕ}
    {F G : Type u}
    [Group F]
    [TopologicalSpace F]
    [IsTopologicalGroup F]
    [Group G]
    [TopologicalSpace G]
    [T1Space G]
    {ι : Type*}
    {relator : ι → F}
    (Q : PQuot (G := G) relator)

namespace PQuot

/--
Residual finiteness of the presented quotient target makes the universal
relator residual quotient kernel small enough to descend to that target.
-/
lemma residual_quotient_kernel
    (hres : RFP p G) :
    (residualQuotientMap (p := p) relator).ker ≤ Q.quotientMap.ker := by
  rw [ker_residual_quotient]
  exact relator_residually_target
    relator Q hres

/--
Every residually finite `p` presented quotient target receives one canonical
surjection from the universal finite-`p` relator residual quotient.
-/
def residualDescent
    (hres : RFP p G) :
    relatorResidualQuotient (p := p) relator →* G :=
  factorSurjective
    (residualQuotientMap (p := p) relator)
    Q.quotientMap
    (residual_quotient_surjective (p := p) relator)
    (residual_quotient_kernel (p := p) Q hres)

/--
The residual descent is the unique map carrying the universal residual quotient
class of an ambient element to its class in the presented quotient target.
-/
lemma residualDescentComp
    (hres : RFP p G) :
    (residualDescent (p := p) Q hres).comp
        (residualQuotientMap (p := p) relator) =
      Q.quotientMap := by
  exact factor_map_of
    (residualQuotientMap (p := p) relator)
    Q.quotientMap
    (residual_quotient_surjective (p := p) relator)
    (residual_quotient_kernel (p := p) Q hres)

/--
Residual descent is continuous: the universal residual quotient already carries
the quotient topology from the ambient source.
-/
lemma residualDescent_continuous
    (hres : RFP p G) :
    Continuous (residualDescent (p := p) Q hres) := by
  exact continuous_factor_quotient
    (residualQuotientMap (p := p) relator)
    Q.quotientMap
    (map_is_map (p := p) relator)
    Q.quotientMap_continuous
    (residual_quotient_kernel (p := p) Q hres)

/--
Residual descent is onto because both the ambient residual quotient map and the
presented quotient map are onto.
-/
lemma residualDescent_surjective
    (hres : RFP p G) :
    Function.Surjective (residualDescent (p := p) Q hres) := by
  intro y
  rcases Q.quotientMap_surjective y with ⟨x, rfl⟩
  exact ⟨residualQuotientMap (p := p) relator x, by
    simpa using congrArg
      (fun φ : F →* G => φ x)
      (residualDescentComp (p := p) Q hres)⟩

/--
For compact ambient source and Hausdorff target, residual descent is a
topological quotient map.
-/
lemma residual_descent_quotient
    [CompactSpace F]
    [T2Space G]
    (hres : RFP p G) :
    Topology.IsQuotientMap (residualDescent (p := p) Q hres) := by
  exact surjective_t_space
    (residualDescent (p := p) Q hres)
    (residualDescent_surjective (p := p) Q hres)
    (residualDescent_continuous (p := p) Q hres)

/--
The extra residual kernel measures the relations still killed after passing from
the universal finite-`p` relator residual quotient to a residually finite target.
-/
def extraResidualKernel
    (hres : RFP p G) :
    Subgroup (relatorResidualQuotient (p := p) relator) :=
  (residualDescent (p := p) Q hres).ker

@[simp] lemma extra_residual_kernel
    (hres : RFP p G) :
    extraResidualKernel (p := p) Q hres =
      (residualDescent (p := p) Q hres).ker := rfl

instance extra_residual_normal
    (hres : RFP p G) :
    (extraResidualKernel (p := p) Q hres).Normal := by
  rw [extra_residual_kernel]
  infer_instance

/--
Pulling the extra residual kernel back to the ambient source recovers exactly
the presented quotient kernel.
-/
lemma extraResidualComap
    (hres : RFP p G) :
    (extraResidualKernel (p := p) Q hres).comap
        (residualQuotientMap (p := p) relator) =
      Q.quotientMap.ker := by
  ext x
  rw [Subgroup.mem_comap, extra_residual_kernel, MonoidHom.mem_ker,
    MonoidHom.mem_ker]
  rw [show residualDescent (p := p) Q hres
      (residualQuotientMap (p := p) relator x) =
      Q.quotientMap x by
    exact congrArg
      (fun φ : F →* G => φ x)
      (residualDescentComp (p := p) Q hres)]

/--
The extra residual kernel is closed because it is the kernel of a continuous
map into a `T₁` target.
-/
lemma extra_residual_closed
    (hres : RFP p G) :
    IsClosed
      (((extraResidualKernel (p := p) Q hres :
          Subgroup (relatorResidualQuotient (p := p) relator)) : Set
        (relatorResidualQuotient (p := p) relator))) := by
  rw [extra_residual_kernel]
  change IsClosed
    ((residualDescent (p := p) Q hres) ⁻¹' ({1} : Set G))
  exact isClosed_singleton.preimage (residualDescent_continuous (p := p) Q hres)

/--
Residual descent is injective exactly when the presented quotient kills no more
than the universal finite-`p` relator residual kernel.
-/
lemma residual_descent_relator
    (hres : RFP p G) :
    Function.Injective (residualDescent (p := p) Q hres) ↔
      Q.quotientMap.ker ≤ relatorKernel p relator := by
  constructor
  · intro hInjective x hx
    rw [← ker_residual_quotient (p := p) relator, MonoidHom.mem_ker]
    apply hInjective
    have hxDescent :
        residualDescent (p := p) Q hres
            (residualQuotientMap (p := p) relator x) = 1 := by
      rw [show residualDescent (p := p) Q hres
          (residualQuotientMap (p := p) relator x) =
          Q.quotientMap x by
        exact congrArg
          (fun φ : F →* G => φ x)
          (residualDescentComp (p := p) Q hres)]
      exact MonoidHom.mem_ker.mp hx
    exact hxDescent.trans (residualDescent (p := p) Q hres).map_one.symm
  · intro hkernel
    apply (MonoidHom.ker_eq_bot_iff (residualDescent (p := p) Q hres)).mp
    apply le_antisymm
    · intro y hy
      rw [Subgroup.mem_bot]
      rcases residual_quotient_surjective (p := p) relator y with ⟨x, rfl⟩
      have hxKernel : x ∈ Q.quotientMap.ker := by
        rw [MonoidHom.mem_ker]
        have hxDescent : residualDescent (p := p) Q hres
            (residualQuotientMap (p := p) relator x) = 1 :=
          MonoidHom.mem_ker.mp hy
        rw [show residualDescent (p := p) Q hres
            (residualQuotientMap (p := p) relator x) =
            Q.quotientMap x by
          exact congrArg
            (fun φ : F →* G => φ x)
            (residualDescentComp (p := p) Q hres)] at hxDescent
        exact hxDescent
      apply (QuotientGroup.eq_one_iff x).mpr
      exact hkernel hxKernel
    · exact bot_le

/--
A residually finite target is finite-`p` universal exactly when residual descent
has no extra kernel.
-/
lemma descent_residually_target
    (hres : RFP p G) :
    Q.FinitePUniversal p ↔
      Function.Injective (residualDescent (p := p) Q hres) := by
  change QuotientFactorizationProperty p relator Q.quotientMap ↔
    Function.Injective (residualDescent (p := p) Q hres)
  rw [factorization_property_relator]
  exact (residual_descent_relator
    (p := p) Q hres).symm

/--
The finite-`p` universality defect of a residually finite target is exactly the
extra residual kernel.
-/
lemma extra_residually_target
    (hres : RFP p G) :
    Q.FinitePUniversal p ↔
      extraResidualKernel (p := p) Q hres = ⊥ := by
  rw [descent_residually_target
    (p := p) Q hres]
  exact (MonoidHom.ker_eq_bot_iff (residualDescent (p := p) Q hres)).symm

/--
Every residually finite presented quotient target is the quotient of the
universal relator residual quotient by its extra residual kernel.
-/
def residualDescentEquiv
    (hres : RFP p G) :
    relatorResidualQuotient (p := p) relator ⧸
        extraResidualKernel (p := p) Q hres ≃*
      G := by
  change relatorResidualQuotient (p := p) relator ⧸
        (residualDescent (p := p) Q hres).ker ≃*
      G
  exact QuotientGroup.quotientKerEquivOfSurjective
    (residualDescent (p := p) Q hres)
    (residualDescent_surjective (p := p) Q hres)

/--
When the target is finite-`p` universal, residual descent is the canonical
isomorphism from the universal relator residual quotient to the target.
-/
def residualDescentResidually
    (hUniversal : Q.FinitePUniversal p)
    (hres : RFP p G) :
    relatorResidualQuotient (p := p) relator ≃* G :=
  MulEquiv.ofBijective
    (residualDescent (p := p) Q hres)
    ⟨(descent_residually_target
        (p := p) Q hres).mp hUniversal,
      residualDescent_surjective (p := p) Q hres⟩

lemma descent_universal_residually
    (hUniversal : Q.FinitePUniversal p)
    (hres : RFP p G) :
    (residualDescentResidually
        (p := p) Q hUniversal hres).toMonoidHom.comp
        (residualQuotientMap (p := p) relator) =
      Q.quotientMap := by
  exact residualDescentComp (p := p) Q hres

/--
For compact ambient source and Hausdorff target, the universal finite-`p`
residual descent is a continuous multiplicative equivalence.
-/
def descentUniversalResidually
    [CompactSpace F]
    [T2Space G]
    (hUniversal : Q.FinitePUniversal p)
    (hres : RFP p G) :
    relatorResidualQuotient (p := p) relator ≃ₜ* G where
  toMulEquiv :=
    residualDescentResidually
      (p := p) Q hUniversal hres
  continuous_toFun :=
    residualDescent_continuous (p := p) Q hres
  continuous_invFun := by
    let e := residualDescentResidually
      (p := p) Q hUniversal hres
    have hcontinuous :
        Continuous (e : relatorResidualQuotient (p := p) relator → G) := by
      change Continuous (residualDescent (p := p) Q hres)
      exact residualDescent_continuous (p := p) Q hres
    exact hcontinuous.continuous_symm_of_equiv_compact_to_t2

end PQuot

end RRDescen
end Submission
