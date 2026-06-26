import Submission.ClassField.TateCohomology.IntegralGroupRing
import Submission.ClassField.Shifting.TransferBridge
import Submission.ClassField.ArtinReciprocity.Verlagerung

/-!
# Chapter V, Section 3, Theorem 3.19: Furtwaengler transfer

This file records the literal group-theoretic statement and the exact
augmentation-ideal gap in the currently available library.  No form of the
Furtwaengler theorem is introduced as a primitive.
-/

namespace Submission.CField.ARecip

open Finsupp
open Submission.CField.TCohomo
open Submission.CField.Shifting

noncomputable section

universe u

variable (G : Type u) [Group G] [Finite G]

local notation "H_" => commutator G

/-- The literal statement of Theorem V.3.19. -/
def FurtwaenglerTransferTheorem : Prop :=
  letI : (commutator G).FiniteIndex := Subgroup.finiteIndex_of_finite
  verlagerung H_ = 1

/-- Generatorwise form of Furtwaengler's theorem. -/
def PointwiseStatement : Prop :=
  letI : (commutator G).FiniteIndex := Subgroup.finiteIndex_of_finite
  ∀ g : G, transferToAbelianization H_ g = 1

/-- The literal theorem is exactly the pointwise vanishing of transfer on
representatives of the source abelianization. -/
theorem iff_pointwise :
    FurtwaenglerTransferTheorem G ↔ PointwiseStatement G := by
  letI : (commutator G).FiniteIndex := Subgroup.finiteIndex_of_finite
  constructor
  · intro h g
    have hg := DFunLike.congr_fun h (Abelianization.of g)
    simpa [FurtwaenglerTransferTheorem, PointwiseStatement] using hg
  · intro h
    apply MonoidHom.ext
    intro x
    refine QuotientGroup.induction_on x ?_
    intro g
    change verlagerung H_ (Abelianization.of g) = 1
    rw [verlagerung_apply_of]
    exact h g

/-- The explicit orbit-product appearing in Mathlib's transfer formula. -/
def transferOrbitProduct (g : G) : Abelianization H_ := by
  letI : (commutator G).FiniteIndex := Subgroup.finiteIndex_of_finite
  letI : Fintype (G ⧸ H_) := Subgroup.fintypeQuotientOfFiniteIndex
  letI : Fintype (Quotient (MulAction.orbitRel (Subgroup.zpowers g) (G ⧸ H_))) :=
    Fintype.ofFinite _
  exact
    ∏ q : Quotient (MulAction.orbitRel (Subgroup.zpowers g) (G ⧸ H_)),
      Abelianization.of
        ⟨q.out.out⁻¹ * g ^ Function.minimalPeriod (g • ·) q.out * q.out.out,
          QuotientGroup.out_conj_pow_minimalPeriod_mem H_ g q.out⟩

/-- Orbit-product form of Theorem V.3.19. -/
def OrbitProductStatement : Prop :=
  ∀ g : G, transferOrbitProduct G g = 1

theorem transfer_abelianization_product (g : G) :
    letI : (commutator G).FiniteIndex := Subgroup.finiteIndex_of_finite
    transferToAbelianization H_ g = transferOrbitProduct G g := by
  letI : (commutator G).FiniteIndex := Subgroup.finiteIndex_of_finite
  letI : Fintype (G ⧸ H_) := Subgroup.fintypeQuotientOfFiniteIndex
  letI : Fintype (Quotient (MulAction.orbitRel (Subgroup.zpowers g) (G ⧸ H_))) :=
    Fintype.ofFinite _
  exact MonoidHom.transfer_eq_prod_quotient_orbitRel_zpowers_quot
    (Abelianization.of : H_ →* Abelianization H_) g

theorem pointwise_orbit_product :
    PointwiseStatement G ↔ OrbitProductStatement G := by
  letI : (commutator G).FiniteIndex := Subgroup.finiteIndex_of_finite
  constructor <;> intro h g
  · rw [← transfer_abelianization_product G g]
    exact h g
  · rw [transfer_abelianization_product G g]
    exact h g

theorem iff_orbitProduct :
    FurtwaenglerTransferTheorem G ↔ OrbitProductStatement G :=
  (iff_pointwise G).trans
    (pointwise_orbit_product G)

/-! ## The two missing augmentation statements in Witt's proof -/

/-- The integral group-ring map induced by inclusion of a subgroup. -/
noncomputable def subgroupGroupRing (H : Subgroup G) :
    IntegralGroupRing H →ₗ[ℤ] IntegralGroupRing G :=
  (MonoidAlgebra.mapDomainAlgHom ℤ ℤ H.subtype).toLinearMap

omit [Finite G] in
@[simp]
theorem subgroup_ring_single (H : Subgroup G) (h : H) (n : ℤ) :
    subgroupGroupRing G H (single h n) = single (h : G) n := by
  change MonoidAlgebra.mapDomain H.subtype (single h n) = single (h : G) n
  simp

omit [Finite G] in
theorem subgroup_ring_injective (H : Subgroup G) :
    Function.Injective (subgroupGroupRing G H) := by
  exact MonoidAlgebra.mapDomain_injective H.subtype_injective

/-- `I_H`, embedded in `ℤ[G]`. -/
noncomputable def embeddedAugmentationIdeal (H : Subgroup G) :
    Submodule ℤ (IntegralGroupRing G) :=
  Submodule.map (subgroupGroupRing G H) (augmentationIdeal H)

/-- `I_H²`, embedded in `ℤ[G]`. -/
noncomputable def embeddedAugmentationSquare (H : Subgroup G) :
    Submodule ℤ (IntegralGroupRing G) :=
  Submodule.map (subgroupGroupRing G H)
    ((augmentationIdealSquare H).map (augmentationIdeal H).subtype)

/-- The relative product `I_H I_G`, presented as the span of products in
the ambient integral group ring. -/
noncomputable def relativeAugmentationProduct (H : Subgroup G) :
    Submodule ℤ (IntegralGroupRing G) :=
  Submodule.span ℤ {z | ∃ x : augmentationIdeal H, ∃ y : augmentationIdeal G,
    z = subgroupGroupRing G H x.1 * y.1}

/-- The relative augmentation intersection used after Witt's determinant
calculation: `I_H ∩ I_H I_G = I_H²`, for `H = G'`. -/
def WittIntersectionStatement : Prop :=
  embeddedAugmentationIdeal G H_ ⊓ relativeAugmentationProduct G H_ =
    embeddedAugmentationSquare G H_

/-- The element of `I_H` whose cotangent class is the transfer of `g`.
It is the sum of the right-coset correction terms `h - 1`. -/
noncomputable def transferAugmentationSum (g : G) : augmentationIdeal H_ := by
  letI : (commutator G).FiniteIndex := Subgroup.finiteIndex_of_finite
  letI : Fintype (G ⧸ H_) := Subgroup.fintypeQuotientOfFiniteIndex
  letI : Fintype (Quotient (QuotientGroup.rightRel H_)) :=
    QuotientGroup.fintypeQuotientRightRel
  exact ∑ q : Quotient (QuotientGroup.rightRel H_),
    augmentationClass H_ (Rep.rightCosetCorrection H_ (q.out * g))

/-- The same transfer sum embedded in the ambient group ring. -/
noncomputable def embeddedTransferSum (g : G) : IntegralGroupRing G :=
  subgroupGroupRing G H_ (transferAugmentationSum G g).1

/-- Under Lemma II.2.6, the transfer is represented by the explicit sum of
right-coset correction terms. -/
theorem abelianization_transfer_sum (g : G) :
    letI : (commutator G).FiniteIndex := Subgroup.finiteIndex_of_finite
    abelianizationAugmentationCotangent H_
        (Additive.ofMul (transferToAbelianization H_ g)) =
      (augmentationIdealSquare H_).mkQ (transferAugmentationSum G g) := by
  letI : (commutator G).FiniteIndex := Subgroup.finiteIndex_of_finite
  letI : Fintype (G ⧸ H_) := Subgroup.fintypeQuotientOfFiniteIndex
  letI : Fintype (Quotient (QuotientGroup.rightRel H_)) :=
    QuotientGroup.fintypeQuotientRightRel
  change abelianizationAugmentationCotangent H_
      (Additive.ofMul
        (MonoidHom.transfer (Abelianization.of : H_ →* Abelianization H_) g)) = _
  rw [transfer_coset_correction]
  rw [map_sum]
  change
    (∑ q : Quotient (QuotientGroup.rightRel H_),
      augmentationCotangentClass H_
        (Rep.rightCosetCorrection H_ (q.out * g))) = _
  simp only [transferAugmentationSum, map_sum, augmentationCotangentClass]

/-- Witt's missing determinant/norm lemma, isolated as a proposition.  The
element `μ` has the prescribed augmentation, annihilates
all `g-1` modulo `I_H I_G`, and its norm comparison puts the actual transfer
sum in the same relative product. -/
def WittDeterminantStatement : Prop :=
  ∃ μ : IntegralGroupRing G,
    augmentation G μ = (Nat.card (G ⧸ H_) : ℤ) ∧
    (∀ g : G,
      μ * (single g 1 - single 1 1) ∈ relativeAugmentationProduct G H_) ∧
    (∀ g : G,
      embeddedTransferSum G g -
          μ * (single g 1 - single 1 1) ∈
        relativeAugmentationProduct G H_)

theorem embedded_transfer_ideal (g : G) :
    embeddedTransferSum G g ∈ embeddedAugmentationIdeal G H_ := by
  refine ⟨(transferAugmentationSum G g).1,
    (transferAugmentationSum G g).2, ?_⟩
  rfl

/-- The two missing Witt statements put the transfer representative in
`I_H²`.  This is the exact algebraic point at which the determinant proof
would discharge the remaining obligation. -/
theorem transfer_square_witt
    (hinter : WittIntersectionStatement G)
    (hdet : WittDeterminantStatement G) (g : G) :
    transferAugmentationSum G g ∈ augmentationIdealSquare H_ := by
  rcases hdet with ⟨μ, _hμaugmentation, hμann, hμcomparison⟩
  have hprod : embeddedTransferSum G g ∈
      relativeAugmentationProduct G H_ := by
    have hadd := (relativeAugmentationProduct G H_).add_mem
      (hμcomparison g) (hμann g)
    have heq :
        (embeddedTransferSum G g -
            μ * (single g 1 - single 1 1)) +
            μ * (single g 1 - single 1 1) =
          embeddedTransferSum G g := by
      abel
    rw [← heq]
    exact hadd
  have hinf : embeddedTransferSum G g ∈
      embeddedAugmentationIdeal G H_ ⊓ relativeAugmentationProduct G H_ :=
    ⟨embedded_transfer_ideal G g, hprod⟩
  rw [hinter] at hinf
  change subgroupGroupRing G H_ (transferAugmentationSum G g).1 ∈
    embeddedAugmentationSquare G H_ at hinf
  rw [embeddedAugmentationSquare] at hinf
  rcases hinf with ⟨z, hz, hzmap⟩
  have hzEq : z = (transferAugmentationSum G g).1 :=
    subgroup_ring_injective G H_ hzmap
  rcases hz with ⟨x, hx, hxz⟩
  have hxval : x.1 = (transferAugmentationSum G g).1 := hxz.trans hzEq
  have hxeq : x = transferAugmentationSum G g := Subtype.ext hxval
  simpa [hxeq] using hx

/-- Witt's relative-intersection lemma and determinant/norm lemma imply the
literal Furtwaengler transfer theorem.  Both inputs are propositions defined
above, not primitive constants or hypotheses hidden in the source statement. -/
theorem of_wittAugmentation
    (hinter : WittIntersectionStatement G)
    (hdet : WittDeterminantStatement G) :
    FurtwaenglerTransferTheorem G := by
  rw [iff_pointwise]
  intro g
  apply Additive.ofMul.injective
  change Additive.ofMul (transferToAbelianization H_ g) = 0
  apply (abelianizationAugmentationCotangent H_).injective
  rw [map_zero]
  rw [abelianization_transfer_sum]
  exact (Submodule.Quotient.mk_eq_zero (augmentationIdealSquare H_)).2
    (transfer_square_witt G hinter hdet g)

end

end Submission.CField.ARecip
