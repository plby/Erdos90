import Submission.ClassField.Shifting.InducedCover
import Submission.ClassField.Shifting.TateShift
import Submission.ClassField.Shifting.BottomToTrivial

/-!
# Milne, Class Field Theory, Theorem II.3.10: exceptional cover shift

This file specializes the norm snake-lemma equivalence to Milne's induced
cover.  The exceptional vanishing of the restricted middle term is transported
from an induced module using naturality of the norm.
-/

namespace Submission.CField.Shifting

open CategoryTheory Rep

noncomputable section

universe u

variable {k G : Type u} [CommRing k] [Group G] [Fintype G]

/-- Norm injectivity transports backward across an isomorphism of
representations. -/
theorem coinvariants_injective_iso
    {A B : Rep.{u} k G} (e : A ≅ B)
    (hB : Function.Injective (normCoinvariantsInvariants B)) :
    Function.Injective (normCoinvariantsInvariants A) := by
  let F := Rep.coinvariantsFunctor.{u} k G
  let I := Rep.invariantsFunctor.{u} k G
  let v := normNatTrans (k := k) (G := G)
  have hnat (x : F.obj A) :
      v.app B (F.map e.hom x) = I.map e.hom (v.app A x) := by
    exact congrArg (fun f : F.obj A ⟶ I.obj B => f x) (v.naturality e.hom)
  intro x y hxy
  apply (F.mapIso e).toLinearEquiv.injective
  apply hB
  change v.app B (F.map e.hom x) = v.app B (F.map e.hom y)
  change v.app A x = v.app A y at hxy
  rw [hnat x, hnat y, hxy]

/-- Norm surjectivity transports backward across an isomorphism of
representations. -/
theorem coinvariants_invariants_iso
    {A B : Rep.{u} k G} (e : A ≅ B)
    (hB : Function.Surjective (normCoinvariantsInvariants B)) :
    Function.Surjective (normCoinvariantsInvariants A) := by
  let F := Rep.coinvariantsFunctor.{u} k G
  let I := Rep.invariantsFunctor.{u} k G
  let v := normNatTrans (k := k) (G := G)
  have hnat (x : F.obj B) :
      v.app A (F.map e.inv x) = I.map e.inv (v.app B x) := by
    exact congrArg (fun f : F.obj B ⟶ I.obj A => f x) (v.naturality e.inv)
  intro y
  obtain ⟨x, hx⟩ := hB (I.map e.hom y)
  refine ⟨F.map e.inv x, ?_⟩
  change v.app A (F.map e.inv x) = y
  change v.app B x = I.map e.hom y at hx
  rw [hnat x, hx]
  exact (I.mapIso e).toLinearEquiv.left_inv y

/-- Milne's exceptional dimension shift over the whole group:
`H_T⁻¹(G,A) ≅ H_T⁰(G,A')` for the kernel `A'` of the induced cover. -/
noncomputable def cover_shift_self [Finite G]
    (A : Rep.{u} k G) :
    tateCohomologyOne A ≃ₗ[k]
      tateCohomologyZero (coverSequence A).X₁ := by
  let B := Rep.res (⊥ : Subgroup G).subtype A
  letI : DecidableRel (QuotientGroup.rightRel (⊥ : Subgroup G)) :=
    Classical.decRel _
  let e : coverMiddle A ≅
      Rep.ind (⊥ : Subgroup G).subtype B :=
    (coverMiddleInduced A).symm
  have hnegInd : Subsingleton
      (tateCohomologyOne (Rep.ind (⊥ : Subgroup G).subtype B)) :=
    subsingleton_cohomology_induced B
  have hzeroInd : Subsingleton
      (tateCohomologyZero (Rep.ind (⊥ : Subgroup G).subtype B)) :=
    subsingleton_tate_induced B
  have hnegMiddle : Subsingleton
      (tateCohomologyOne (coverMiddle A)) :=
    (norm_coinvariants_invariants _).1
      (coinvariants_injective_iso e
        ((norm_coinvariants_invariants _).2 hnegInd))
  have hzeroMiddle : Subsingleton
      (tateCohomologyZero (coverMiddle A)) :=
    (coinvariants_invariants_surjective _).1
      (coinvariants_invariants_iso e
        ((coinvariants_invariants_surjective _).2 hzeroInd))
  exact isoShortExact
    (coverSequence A) (cover_sequence_short A)
    hnegMiddle hzeroMiddle

/-- Milne's exceptional dimension shift, uniformly after restriction to a
subgroup:
`H_T⁻¹(H,A) ≅ H_T⁰(H,A')` for the kernel `A'` of the induced cover. -/
noncomputable def coverTateShift [Finite G]
    (A : Rep.{u} k G) (H : Subgroup G) [Fintype H] :
    tateCohomologyOne (Rep.res H.subtype A) ≃ₗ[k]
      tateCohomologyZero
        (Rep.res H.subtype (coverSequence A).X₁) := by
  let B := Rep.trivial k (⊥ : Subgroup H)
    (↥((default : H.RightTransversal) : Set G) →₀ A)
  letI : DecidableRel (QuotientGroup.rightRel (⊥ : Subgroup H)) :=
    Classical.decRel _
  let e : Rep.res H.subtype (coverMiddle A) ≅
      Rep.ind (⊥ : Subgroup H).subtype B :=
    restrictCoverMiddle A H ≪≫ (Rep.indCoindIso B).symm
  have hnegInd : Subsingleton
      (tateCohomologyOne (Rep.ind (⊥ : Subgroup H).subtype B)) :=
    subsingleton_cohomology_induced B
  have hzeroInd : Subsingleton
      (tateCohomologyZero (Rep.ind (⊥ : Subgroup H).subtype B)) :=
    subsingleton_tate_induced B
  have hnegMiddle : Subsingleton
      (tateCohomologyOne
        (Rep.res H.subtype (coverMiddle A))) :=
    (norm_coinvariants_invariants _).1
      (coinvariants_injective_iso e
        ((norm_coinvariants_invariants _).2 hnegInd))
  have hzeroMiddle : Subsingleton
      (tateCohomologyZero
        (Rep.res H.subtype (coverMiddle A))) :=
    (coinvariants_invariants_surjective _).1
      (coinvariants_invariants_iso e
        ((coinvariants_invariants_surjective _).2 hzeroInd))
  exact isoShortExact
    ((coverSequence A).map (Rep.resFunctor H.subtype))
    (cover_short_exact A H)
    hnegMiddle hzeroMiddle

end

end Submission.CField.Shifting
