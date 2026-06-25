import Submission.ClassField.CohomologyOps.DimensionShiftingIso
import Mathlib.Algebra.Homology.HomologySequenceLemmas
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Shapiro

/-!
# Chapter II, Example 1.27: functorial maps in group cohomology

Compatible maps of a group and a coefficient module induce maps on group
cohomology.  The principal examples are Shapiro evaluation, restriction,
inflation, and the map attached to an inner automorphism.
-/

namespace Submission.CField.COps

open CategoryTheory Rep

noncomputable section

universe u

variable {k G : Type u} [CommRing k] [Group G]

/-- The cohomology map associated to a compatible group homomorphism and
coefficient morphism. -/
noncomputable abbrev compatibleCohomologyMap
    {H : Type u} [Group H] (alpha : G →* H)
    (A : Rep k H) (B : Rep k G) (beta : res alpha A ⟶ B) (r : ℕ) :
    groupCohomology A r ⟶ groupCohomology B r :=
  groupCohomology.map alpha beta r

/-- **Example II.1.27(a).** Evaluation at the identity induces Shapiro's
isomorphism from a coinduced module.  Milne denotes this module by `Ind`. -/
noncomputable def shapiroEvaluationIso
    (H : Subgroup G) (A : Rep k H) (r : ℕ) :
    groupCohomology (coind H.subtype A) r ≅ groupCohomology A r :=
  groupCohomology.coindIso A r

/-- **Example II.1.27(b).** Restriction from `G` to a subgroup `H`. -/
noncomputable def functorialCohomologyRestriction
    (A : Rep k G) (H : Subgroup G) (r : ℕ) :
    groupCohomology A r ⟶ groupCohomology (res H.subtype A) r :=
  groupCohomology.map H.subtype (𝟙 _) r

/-- **Example II.1.27(c).** Inflation from a quotient by a normal subgroup. -/
noncomputable def functorialCohomologyInflation
    (A : Rep k G) (H : Subgroup G) [H.Normal] (r : ℕ) :
    groupCohomology (A.quotientToInvariants H) r ⟶ groupCohomology A r :=
  (groupCohomology.infNatTrans (k := k) H r).app A

/-- The compatible coefficient map in Example II.1.27(d): after conjugating
the group variable by `g₀`, act on coefficients by `g₀⁻¹`. -/
noncomputable def innerConjugationHom
    (A : Rep k G) (g₀ : G) :
    res (MulAut.conj g₀).toMonoidHom A ⟶ A :=
  Rep.ofHom
    { toLinearMap := A.ρ g₀⁻¹
      isIntertwining' := fun g ↦ by
        ext m
        change A.ρ g₀⁻¹ (A.ρ (g₀ * g * g₀⁻¹) m) =
          A.ρ g (A.ρ g₀⁻¹ m)
        simp only [← Module.End.mul_apply, ← map_mul]
        congr 1
        group }

/-- The endomorphism of cohomology induced by inner conjugation. -/
noncomputable def innerConjugationCohomology
    (A : Rep k G) (g₀ : G) (r : ℕ) :
    groupCohomology A r ⟶ groupCohomology A r :=
  groupCohomology.map (MulAut.conj g₀).toMonoidHom
    (innerConjugationHom A g₀) r

@[reassoc]
theorem inner_conjugation_naturality
    {A B : Rep k G} (f : A ⟶ B) (g₀ : G) :
    (Rep.resFunctor (MulAut.conj g₀).toMonoidHom).map f ≫
        innerConjugationHom B g₀ =
      innerConjugationHom A g₀ ≫ f := by
  ext a
  change B.ρ g₀⁻¹ (f.hom a) = f.hom (A.ρ g₀⁻¹ a)
  exact (hom_comm_apply f g₀⁻¹ a).symm

/-- Inner conjugation acts naturally on all three terms of a short complex,
and therefore defines an endomorphism of its cochain short complex. -/
noncomputable def cochainsShortComplex
    (X : ShortComplex (Rep k G)) (g₀ : G) :
    X.map (groupCohomology.cochainsFunctor k G) ⟶
      X.map (groupCohomology.cochainsFunctor k G) where
  τ₁ := groupCohomology.cochainsMap (MulAut.conj g₀).toMonoidHom
    (innerConjugationHom X.X₁ g₀)
  τ₂ := groupCohomology.cochainsMap (MulAut.conj g₀).toMonoidHom
    (innerConjugationHom X.X₂ g₀)
  τ₃ := groupCohomology.cochainsMap (MulAut.conj g₀).toMonoidHom
    (innerConjugationHom X.X₃ g₀)
  comm₁₂ := by
    change groupCohomology.cochainsMap (MulAut.conj g₀).toMonoidHom
        (innerConjugationHom X.X₁ g₀) ≫
          groupCohomology.cochainsMap (MonoidHom.id G) X.f =
      groupCohomology.cochainsMap (MonoidHom.id G) X.f ≫
        groupCohomology.cochainsMap (MulAut.conj g₀).toMonoidHom
          (innerConjugationHom X.X₂ g₀)
    rw [← groupCohomology.cochainsMap_comp,
      ← groupCohomology.cochainsMap_comp]
    simpa using congrArg
      (fun f ↦ groupCohomology.cochainsMap
        (MulAut.conj g₀).toMonoidHom f)
      (inner_conjugation_naturality X.f g₀).symm
  comm₂₃ := by
    change groupCohomology.cochainsMap (MulAut.conj g₀).toMonoidHom
        (innerConjugationHom X.X₂ g₀) ≫
          groupCohomology.cochainsMap (MonoidHom.id G) X.g =
      groupCohomology.cochainsMap (MonoidHom.id G) X.g ≫
        groupCohomology.cochainsMap (MulAut.conj g₀).toMonoidHom
          (innerConjugationHom X.X₃ g₀)
    rw [← groupCohomology.cochainsMap_comp,
      ← groupCohomology.cochainsMap_comp]
    simpa using congrArg
      (fun f ↦ groupCohomology.cochainsMap
        (MulAut.conj g₀).toMonoidHom f)
      (inner_conjugation_naturality X.g g₀).symm

/-- Naturality of the connecting homomorphism for inner conjugation. -/
theorem inner_delta_naturality
    {X : ShortComplex (Rep k G)} (hX : X.ShortExact)
    (g₀ : G) (r : ℕ) :
    groupCohomology.δ hX r (r + 1) rfl ≫
        innerConjugationCohomology X.X₁ g₀ (r + 1) =
      innerConjugationCohomology X.X₃ g₀ r ≫
        groupCohomology.δ hX r (r + 1) rfl := by
  exact HomologicalComplex.HomologySequence.δ_naturality
    (cochainsShortComplex X g₀)
    (groupCohomology.map_cochainsFunctor_shortExact hX)
    (groupCohomology.map_cochainsFunctor_shortExact hX) r (r + 1) rfl

/-- The degree-zero case of Example II.1.27(d): inner conjugation fixes
invariants.  This is the base case for Milne's dimension-shifting proof. -/
theorem inner_conjugation_cohomology
    (A : Rep k G) (g₀ : G) :
    innerConjugationCohomology A g₀ 0 = 𝟙 _ := by
  have hcoeff : (groupCohomology.shortComplexH0 A).f ≫
        (innerConjugationHom A g₀).toModuleCatHom =
      (groupCohomology.shortComplexH0 A).f := by
    ext x
    change A.ρ g₀⁻¹ ((show A.ρ.invariants from x).1) =
      (show A.ρ.invariants from x).1
    exact (show A.ρ.invariants from x).2 g₀⁻¹
  have hmap :
      (innerConjugationCohomology A g₀ 0 ≫
          (groupCohomology.H0Iso A).hom) ≫
        (groupCohomology.shortComplexH0 A).f =
      ((groupCohomology.H0Iso A).hom ≫
          (groupCohomology.shortComplexH0 A).f) ≫
        (innerConjugationHom A g₀).toModuleCatHom := by
    simpa only [innerConjugationCohomology, Category.assoc] using
      (groupCohomology.map_H0Iso_hom_f
        (f := (MulAut.conj g₀).toMonoidHom)
        (φ := innerConjugationHom A g₀))
  rw [← cancel_mono (groupCohomology.H0Iso A).hom]
  simp only [Category.id_comp]
  apply (cancel_mono (groupCohomology.shortComplexH0 A).f).mp
  have hrhs :
      ((groupCohomology.H0Iso A).hom ≫
          (groupCohomology.shortComplexH0 A).f) ≫
        (innerConjugationHom A g₀).toModuleCatHom =
      (groupCohomology.H0Iso A).hom ≫
        (groupCohomology.shortComplexH0 A).f := by
    simpa only [Category.assoc] using congrArg
      (fun q => (groupCohomology.H0Iso A).hom ≫ q) hcoeff
  exact hmap.trans hrhs

/-- **Example II.1.27(d), statement.** Inner automorphisms, paired with the
inverse action on coefficients, induce the identity on group cohomology. -/
def InnerActsTrivially : Prop :=
  ∀ (A : Rep k G) (g₀ : G) (r : ℕ),
    innerConjugationCohomology A g₀ r = 𝟙 _

/-- **Example II.1.27(d).** Inner automorphisms, paired with the inverse
action on coefficients, induce the identity in every degree.  This is
Milne's dimension-shifting proof: naturality of the connecting map reduces
degree `r + 1` to degree `r`, and the degree-zero case is invariance. -/
theorem innerActsTrivially :
    InnerActsTrivially (k := k) (G := G) := by
  intro A g₀ r
  induction r generalizing A with
  | zero => exact inner_conjugation_cohomology A g₀
  | succ r ih =>
      let X := dimensionShiftSequence A
      let hX := shift_sequence_short A
      have hnat := inner_delta_naturality hX g₀ r
      rw [ih X.X₃] at hnat
      haveI : Epi (groupCohomology.δ hX r (r + 1) rfl) := by
        cases r with
        | zero => exact shift_delta_epi A
        | succ r =>
            letI : IsIso (groupCohomology.δ hX (r + 1) (r + 1 + 1) rfl) :=
              groupCohomology.isIso_δ_of_isZero hX (r + 1)
                (shift_middle_acyclic A (r + 1)
                  (Nat.succ_pos r))
                (shift_middle_acyclic A (r + 1 + 1)
                  (Nat.succ_pos (r + 1)))
            infer_instance
      apply (cancel_epi (groupCohomology.δ hX r (r + 1) rfl)).mp
      simpa only [Category.comp_id] using hnat

end

end Submission.CField.COps
