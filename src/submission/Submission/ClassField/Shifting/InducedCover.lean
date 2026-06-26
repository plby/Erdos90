import Submission.ClassField.CohomologyOps.IndMkOne
import Submission.ClassField.CohomologyOps.BotEquivFun
import Submission.ClassField.CohomologyOps.ZeroCoinducedSucc
import Submission.ClassField.CohomologyOps.DimensionShiftingIso

/-!
# Milne, Class Field Theory, Theorem II.3.10: induced cover

This file formalizes the exact sequence used to pass from nonnegative to
negative Tate degrees in Milne's proof:

`0 -> A' -> A_* -> A -> 0`,

where `A_*` is coinduced from the trivial subgroup (and hence isomorphic to
Milne's induced regular-tensor module).  We also prove that its restriction
to every subgroup is again coinduced from the trivial subgroup.
-/

namespace Submission.CField.Shifting

open CategoryTheory CategoryTheory.Limits Rep

noncomputable section

universe u

variable {k G : Type u} [CommRing k] [Group G]

/-- The induced middle term in Milne's negative dimension shift. -/
noncomputable abbrev coverMiddle (A : Rep.{u} k G) : Rep.{u} k G :=
  Rep.coind (⊥ : Subgroup G).subtype
    (Rep.res (⊥ : Subgroup G).subtype A)

/-- The trace/augmentation from the induced middle term onto `A`. -/
noncomputable def coverMap [Finite G] (A : Rep.{u} k G) :
    coverMiddle A ⟶ A :=
  COps.corestrictionTrace A (⊥ : Subgroup G)

/-- The kernel sequence `0 -> A' -> A_* -> A -> 0`. -/
noncomputable abbrev coverSequence [Finite G] (A : Rep.{u} k G) :
    ShortComplex (Rep.{u} k G) :=
  ShortComplex.kernelSequence (coverMap A)

/-- The augmentation of the induced cover is surjective. -/
theorem coverMap_surjective [Finite G] (A : Rep.{u} k G) :
    Function.Surjective (coverMap A).hom :=
  COps.corestriction_bot_surjective A

instance coverMap_epi [Finite G] (A : Rep.{u} k G) :
    Epi (coverMap A) :=
  (Rep.epi_iff_surjective _).2 (coverMap_surjective A)

/-- Milne's induced cover sequence is short exact. -/
theorem cover_sequence_short [Finite G] (A : Rep.{u} k G) :
    (coverSequence A).ShortExact where
  exact := ShortComplex.kernelSequence_exact (coverMap A)
  mono_f := inferInstance
  epi_g := coverMap_epi A

/-- The middle term is the module induced from the underlying representation
of the trivial subgroup. -/
noncomputable def coverMiddleInduced [Finite G] (A : Rep.{u} k G) :
    Rep.ind (⊥ : Subgroup G).subtype
        (Rep.res (⊥ : Subgroup G).subtype A) ≅
      coverMiddle A :=
  by
    letI := Classical.decRel (QuotientGroup.rightRel (⊥ : Subgroup G))
    exact Rep.indCoindIso (Rep.res (⊥ : Subgroup G).subtype A)

/-- The induced middle term has vanishing positive cohomology. -/
theorem cover_positive_acyclic
    (A : Rep.{u} k G) (n : ℕ) (hn : 0 < n) :
    IsZero (groupCohomology (coverMiddle A) n) :=
  COps.zero_cohomology_coinduced
    (Rep.res (⊥ : Subgroup G).subtype A) n hn

private noncomputable def bottomIsoTrivial (A : Rep.{u} k G) :
    Rep.res (⊥ : Subgroup G).subtype A ≅
      Rep.trivial k (⊥ : Subgroup G) A :=
  Rep.mkIso {
    toLinearEquiv := LinearEquiv.refl k A
    isIntertwining' := fun h => by
      obtain rfl : h = 1 := Subtype.ext (Subgroup.mem_bot.mp h.2)
      ext
      simp }

/-- After restriction to `H`, the induced middle term is again coinduced
from the trivial subgroup.  The coefficient module is indexed by a right
transversal for `H` in `G`, as in Remark II.1.3(b). -/
noncomputable def restrictCoverMiddle
    [Finite G] (A : Rep.{u} k G) (H : Subgroup G) :
    Rep.res H.subtype (coverMiddle A) ≅
      Rep.coind (⊥ : Subgroup H).subtype
        (Rep.trivial k (⊥ : Subgroup H)
          (↥((default : H.RightTransversal) : Set G) →₀ A)) :=
  (Rep.resFunctor H.subtype).mapIso
      ((Rep.coindFunctor k (⊥ : Subgroup G).subtype).mapIso
        (bottomIsoTrivial A) ≪≫
        COps.coindRegularTensor A) ≪≫
    COps.restrictRegularIso H default A ≪≫
    (COps.coindRegularTensor
      (↥((default : H.RightTransversal) : Set G) →₀ A)).symm

/-- The middle term remains acyclic in positive degrees after restriction
to every subgroup. -/
theorem cover_middle_acyclic
    [Finite G] (A : Rep.{u} k G) (H : Subgroup G)
    (n : ℕ) (hn : 0 < n) :
    IsZero (groupCohomology
      (Rep.res H.subtype (coverMiddle A)) n) := by
  let B := Rep.trivial k (⊥ : Subgroup H)
    (↥((default : H.RightTransversal) : Set G) →₀ A)
  have htarget : IsZero (groupCohomology
      (Rep.coind (⊥ : Subgroup H).subtype B) n) :=
    COps.zero_cohomology_coinduced B n hn
  exact htarget.of_iso
    ((groupCohomology.functor k H n).mapIso
      (restrictCoverMiddle A H))

/-- Restricting Milne's induced cover to a subgroup preserves short
exactness. -/
theorem cover_short_exact
    [Finite G] (A : Rep.{u} k G) (H : Subgroup G) :
    ((coverSequence A).map (Rep.resFunctor H.subtype)).ShortExact :=
  (cover_sequence_short A).map_of_exact
    (Rep.resFunctor H.subtype)

/-- The positive-degree part of Milne's dimension shift, uniformly after
restriction to every subgroup:
`H^r(H,A) ≅ H^(r+1)(H,A')` for `r > 0`. -/
noncomputable def coverCohomologyShift
    [Finite G] (A : Rep.{u} k G) (H : Subgroup G)
    (n : ℕ) (hn : 0 < n) :
    groupCohomology (Rep.res H.subtype A) n ≅
      groupCohomology
        (Rep.res H.subtype (coverSequence A).X₁) (n + 1) :=
  COps.dimensionShiftingIso
    (cover_short_exact A H)
    (fun q hq => cover_middle_acyclic A H q hq)
    n hn

end

end Submission.CField.Shifting
