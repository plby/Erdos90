import Towers.ClassField.CohomologyOps.RegularCoefficientTwist
import Towers.ClassField.Shifting.TateCover
import Towers.ClassField.Shifting.Augmentation

/-!
# Milne, Class Field Theory, Remark II.3.12: the regular tensor term

Tensoring Tate's four-term sequence with a representation `M` replaces its
regular middle term by `Z[G] ⊗ M`, with the diagonal action.  Milne's
coefficient-twisting isomorphism identifies this with a module induced from
the trivial subgroup.  This file proves, uniformly after restriction to every
subgroup, all four represented pieces of its Tate acyclicity.

The remaining ingredient in Remark II.3.12 is the separate homological
assertion that `Tor₁ᶻ(M, C) = 0` makes `M ⊗ C(φ)` Tate-acyclic.
-/

namespace Towers.CField.Shifting

open CategoryTheory CategoryTheory.Limits MonoidalCategory Rep

noncomputable section

variable {G : Type} [Group G] [Finite G]

local instance repIntModule (M : Rep ℤ G) : Module ℤ M := M.hV2

/-- The coefficient at the trivial subgroup which occurs after regrouping
the regular basis along the right cosets of `H`. -/
noncomputable def regularBottomCoefficient
    (M : Rep ℤ G) (H : Subgroup G) : Rep ℤ (⊥ : Subgroup H) :=
  @Rep.trivial ℤ (⊥ : Subgroup H) _ _
    (↥((default : H.RightTransversal) : Set G) →₀ M) _
    (Finsupp.module _ M)

/-- After restriction to `H`, the diagonal tensor of the integral regular
representation with `M` is coinduced from the trivial subgroup of `H`.
The coefficient module has one copy of the underlying module of `M` for each
right coset of `H` in `G`. -/
noncomputable def restrictRegularCoind
    (M : Rep ℤ G) (H : Subgroup G) :
    Rep.res H.subtype (Rep.leftRegular ℤ G ⊗ M) ≅
      Rep.coind (⊥ : Subgroup H).subtype
        (regularBottomCoefficient M H) :=
  ((Rep.resFunctor H.subtype).mapIso
      (COps.regularIsoDiagonal M).symm).trans <|
    (COps.restrictRegularIso H default M).trans <|
      (@COps.coindRegularTensor ℤ H _ _ _
        (↥((default : H.RightTransversal) : Set G) →₀ M) _
        (Finsupp.module _ M)).symm

/-- The restricted regular tensor has zero positive-degree cohomology. -/
theorem restrict_tensor_acyclic
    (M : Rep ℤ G) (H : Subgroup G) (n : ℕ) (hn : 0 < n) :
    IsZero (groupCohomology
      (Rep.res H.subtype (Rep.leftRegular ℤ G ⊗ M)) n) := by
  let B := regularBottomCoefficient M H
  have htarget : IsZero
      (groupCohomology (Rep.coind (⊥ : Subgroup H).subtype B) n) :=
    COps.zero_cohomology_coinduced B n hn
  exact htarget.of_iso
    ((groupCohomology.functor ℤ H n).mapIso
      (restrictRegularCoind M H))

/-- The restricted regular tensor has zero positive-degree homology. -/
theorem restrict_homology_acyclic
    (M : Rep ℤ G) (H : Subgroup G) (n : ℕ) (hn : 0 < n) :
    IsZero (groupHomology
      (Rep.res H.subtype (Rep.leftRegular ℤ G ⊗ M)) n) := by
  letI : Fintype H := Fintype.ofFinite H
  let B := regularBottomCoefficient M H
  letI : DecidableRel (QuotientGroup.rightRel (⊥ : Subgroup H)) :=
    Classical.decRel _
  let e : Rep.res H.subtype (Rep.leftRegular ℤ G ⊗ M) ≅
      Rep.ind (⊥ : Subgroup H).subtype B :=
    (restrictRegularCoind M H).trans (Rep.indCoindIso B).symm
  have htarget : IsZero
      (groupHomology (Rep.ind (⊥ : Subgroup H).subtype B) n) :=
    zero_homology_induced B n hn
  exact htarget.of_iso ((groupHomology.functor ℤ H n).mapIso e)

/-- Degree-minus-one Tate cohomology of the restricted regular tensor is
trivial. -/
theorem subsingleton_regular_tensor
    (M : Rep ℤ G) (H : Subgroup G) [Fintype H] :
    Subsingleton (tateCohomologyOne
      (Rep.res H.subtype (Rep.leftRegular ℤ G ⊗ M))) := by
  let B := regularBottomCoefficient M H
  letI : DecidableRel (QuotientGroup.rightRel (⊥ : Subgroup H)) :=
    Classical.decRel _
  let e : Rep.res H.subtype (Rep.leftRegular ℤ G ⊗ M) ≅
      Rep.ind (⊥ : Subgroup H).subtype B :=
    (restrictRegularCoind M H).trans (Rep.indCoindIso B).symm
  exact (norm_coinvariants_invariants _).1
    (coinvariants_injective_iso e
      ((norm_coinvariants_invariants _).2
        (subsingleton_cohomology_induced B)))

/-- Degree-zero Tate cohomology of the restricted regular tensor is
trivial. -/
theorem subsingleton_restrict_tensor
    (M : Rep ℤ G) (H : Subgroup G) [Fintype H] :
    Subsingleton (tateCohomologyZero
      (Rep.res H.subtype (Rep.leftRegular ℤ G ⊗ M))) := by
  let B := regularBottomCoefficient M H
  letI : DecidableRel (QuotientGroup.rightRel (⊥ : Subgroup H)) :=
    Classical.decRel _
  let e : Rep.res H.subtype (Rep.leftRegular ℤ G ⊗ M) ≅
      Rep.ind (⊥ : Subgroup H).subtype B :=
    (restrictRegularCoind M H).trans (Rep.indCoindIso B).symm
  exact (coinvariants_invariants_surjective _).1
    (coinvariants_invariants_iso e
      ((coinvariants_invariants_surjective _).2
        (subsingleton_tate_induced B)))

/-- The same positive-cohomology vanishing with the regular representation
in the right tensor factor. -/
theorem restrict_positive_acyclic
    (M : Rep ℤ G) (H : Subgroup G) (n : ℕ) (hn : 0 < n) :
    IsZero (groupCohomology
      (Rep.res H.subtype (M ⊗ Rep.leftRegular ℤ G)) n) := by
  let e := (Rep.resFunctor H.subtype).mapIso
    (β_ M (Rep.leftRegular ℤ G))
  exact (restrict_tensor_acyclic M H n hn).of_iso
    ((groupCohomology.functor ℤ H n).mapIso e)

/-- The same positive-homology vanishing with the regular representation in
the right tensor factor. -/
theorem regular_homology_acyclic
    (M : Rep ℤ G) (H : Subgroup G) (n : ℕ) (hn : 0 < n) :
    IsZero (groupHomology
      (Rep.res H.subtype (M ⊗ Rep.leftRegular ℤ G)) n) := by
  let e := (Rep.resFunctor H.subtype).mapIso
    (β_ M (Rep.leftRegular ℤ G))
  exact (restrict_homology_acyclic M H n hn).of_iso
    ((groupHomology.functor ℤ H n).mapIso e)

/-- Degree minus one also vanishes with the regular representation in the
right tensor factor. -/
theorem subsingleton_restrict_regular
    (M : Rep ℤ G) (H : Subgroup G) [Fintype H] :
    Subsingleton (tateCohomologyOne
      (Rep.res H.subtype (M ⊗ Rep.leftRegular ℤ G))) := by
  let e := (Rep.resFunctor H.subtype).mapIso
    (β_ M (Rep.leftRegular ℤ G))
  exact (norm_coinvariants_invariants _).1
    (coinvariants_injective_iso e
      ((norm_coinvariants_invariants _).2
        (subsingleton_regular_tensor M H)))

/-- Degree zero also vanishes with the regular representation in the right
tensor factor. -/
theorem subsingleton_tensor_regular
    (M : Rep ℤ G) (H : Subgroup G) [Fintype H] :
    Subsingleton (tateCohomologyZero
      (Rep.res H.subtype (M ⊗ Rep.leftRegular ℤ G))) := by
  let e := (Rep.resFunctor H.subtype).mapIso
    (β_ M (Rep.leftRegular ℤ G))
  exact (coinvariants_invariants_surjective _).1
    (coinvariants_invariants_iso e
      ((coinvariants_invariants_surjective _).2
        (subsingleton_restrict_tensor M H)))

end

end Towers.CField.Shifting
