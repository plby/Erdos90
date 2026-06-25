import Submission.ClassField.CohomologyOps.FunctorialMapsGroup
import Mathlib.RepresentationTheory.Rep.Res

/-!
# Chapter II, Remark 1.28: the quotient action on subgroup cohomology

If `H` is normal in `G` and `M` is a `G`-representation, conjugation and
the action on coefficients give a `G`-action on `H^r(H, M)`.  Inner
conjugation acts trivially on cohomology, so this action descends to `G/H`.
-/

namespace Submission.CField.COps

open CategoryTheory Rep

noncomputable section

universe u

variable {k G : Type u} [CommRing k] [Group G]

/-- Conjugation by an element of `G`, restricted to a normal subgroup `H`. -/
def normalConjugationHom (H : Subgroup G) [H.Normal] (g : G) : H →* H where
  toFun h := ⟨g * h * g⁻¹, (inferInstance : H.Normal).conj_mem h h.2 g⟩
  map_one' := by ext; simp
  map_mul' h₁ h₂ := by
    ext
    change g * ((h₁ : G) * h₂) * g⁻¹ =
      (g * h₁ * g⁻¹) * (g * h₂ * g⁻¹)
    group

@[simp]
theorem normal_conjugation_coe
    (H : Subgroup G) [H.Normal] (g : G) (h : H) :
    ((normalConjugationHom H g h : H) : G) = g * h * g⁻¹ :=
  rfl

theorem normal_conjugation_hom (H : Subgroup G) [H.Normal] :
    normalConjugationHom H 1 = MonoidHom.id H := by
  ext h
  simp

theorem normal_conjugation_mul
    (H : Subgroup G) [H.Normal] (g₁ g₂ : G) :
    normalConjugationHom H (g₁ * g₂) =
      (normalConjugationHom H g₁).comp (normalConjugationHom H g₂) := by
  ext h
  simp only [normal_conjugation_coe, MonoidHom.coe_comp,
    Function.comp_apply]
  group

/-- The coefficient map paired with conjugation by `g`: it sends `m` to
`g⁻¹ m`, exactly as in Example II.1.27(d). -/
noncomputable def normalConjugationCoefficient
    (M : Rep k G) (H : Subgroup G) [H.Normal] (g : G) :
    res (normalConjugationHom H g) (res H.subtype M) ⟶ res H.subtype M :=
  Rep.ofHom
    { toLinearMap := M.ρ g⁻¹
      isIntertwining' := fun h ↦ by
        ext m
        change M.ρ g⁻¹ (M.ρ (g * h * g⁻¹) m) =
          M.ρ h (M.ρ g⁻¹ m)
        simp only [← Module.End.mul_apply, ← map_mul]
        congr 1
        group }

/-- The raw cohomology map supplied by Milne's conjugation recipe. -/
noncomputable def normalConjugationCohomology
    (M : Rep k G) (H : Subgroup G) [H.Normal] (g : G) (r : ℕ) :
    groupCohomology (res H.subtype M) r ⟶
      groupCohomology (res H.subtype M) r :=
  groupCohomology.map (normalConjugationHom H g)
    (normalConjugationCoefficient M H g) r

theorem conjugation_cohomology_one
    (M : Rep k G) (H : Subgroup G) [H.Normal] (r : ℕ) :
    normalConjugationCohomology M H 1 r = 𝟙 _ := by
  change HomologicalComplex.homologyMap _ r = 𝟙 _
  rw [← HomologicalComplex.homologyMap_id]
  congr 1
  ext n φ h
  change M.ρ (1 : G)⁻¹ (φ ((normalConjugationHom H 1) ∘ h)) = φ h
  simp only [inv_one, map_one, Module.End.one_apply]
  congr 1
  funext i
  apply Subtype.ext
  simp

theorem normal_conjugation_cohomology
    (M : Rep k G) (H : Subgroup G) [H.Normal] (g₁ g₂ : G) (r : ℕ) :
    normalConjugationCohomology M H (g₁ * g₂) r =
      normalConjugationCohomology M H g₁ r ≫
        normalConjugationCohomology M H g₂ r := by
  change HomologicalComplex.homologyMap _ r =
    HomologicalComplex.homologyMap _ r ≫ HomologicalComplex.homologyMap _ r
  rw [← HomologicalComplex.homologyMap_comp]
  congr 1
  ext n φ h
  change M.ρ (g₁ * g₂)⁻¹ (φ ((normalConjugationHom H (g₁ * g₂)) ∘ h)) =
    M.ρ g₂⁻¹ (M.ρ g₁⁻¹
      (φ ((normalConjugationHom H g₁) ∘
        ((normalConjugationHom H g₂) ∘ h))))
  simp only [← Module.End.mul_apply, ← map_mul]
  congr 1
  · group
  · congr 1
    funext i
    apply Subtype.ext
    simp only [Function.comp_apply, normal_conjugation_coe]
    group

/-- The left `G`-representation on `H^r(H,M)`.  The inverse converts the
contravariance of the raw conjugation recipe into a left action. -/
noncomputable def subgroupConjugationRep
    (M : Rep k G) (H : Subgroup G) [H.Normal] (r : ℕ) : Rep k G :=
  Rep.of
    { toFun := fun g ↦
        (normalConjugationCohomology M H g⁻¹ r).hom
      map_one' := by
        ext x
        simpa using ConcreteCategory.congr_hom
          (conjugation_cohomology_one M H r) x
      map_mul' := fun g₁ g₂ ↦ by
        ext x
        have h := normal_conjugation_cohomology M H g₂⁻¹ g₁⁻¹ r
        have hx := ConcreteCategory.congr_hom h x
        simpa [Module.End.mul_apply] using hx }

/-- When the conjugating element belongs to `H`, the normal-subgroup recipe
is exactly the inner-conjugation map of Example II.1.27(d). -/
theorem conjugation_coe_inner
    (M : Rep k G) (H : Subgroup G) [H.Normal] (h : H) (r : ℕ) :
    normalConjugationCohomology M H (h : G) r =
      innerConjugationCohomology (res H.subtype M) h r := by
  change HomologicalComplex.homologyMap _ r =
    HomologicalComplex.homologyMap _ r
  congr 1

/-- The normal subgroup `H` acts trivially on its cohomology under the
conjugation action.  This is precisely Example II.1.27(d). -/
noncomputable instance conjugation_rep_trivial
    (M : Rep k G) (H : Subgroup G) [H.Normal] (r : ℕ) :
    Representation.IsTrivial
      ((subgroupConjugationRep M H r).ρ.comp H.subtype) where
  out h := by
    change (normalConjugationCohomology M H ((h : G))⁻¹ r).hom =
      LinearMap.id
    rw [show ((h : G))⁻¹ = ((h⁻¹ : H) : G) by rfl,
      conjugation_coe_inner,
      innerActsTrivially (k := k) (G := H) (res H.subtype M) h⁻¹ r]
    rfl

/-- **Remark II.1.28(b).** The action of `G` on `H^r(H,M)` obtained from
conjugation and the coefficient action factors through `G/H`. -/
noncomputable abbrev cohomologyConjugationRep
    (M : Rep k G) (H : Subgroup G) [H.Normal] (r : ℕ) : Rep k (G ⧸ H) :=
  (subgroupConjugationRep M H r).ofQuotient H

/-- On a coset represented by `g`, the quotient action is the cohomology map
attached to conjugation by `g⁻¹` and coefficient action by `g`. -/
theorem conjugation_rep_mk
    (M : Rep k G) (H : Subgroup G) [H.Normal] (r : ℕ)
    (g : G) (x : groupCohomology (res H.subtype M) r) :
    (cohomologyConjugationRep M H r).ρ
        (QuotientGroup.mk' H g) x =
      normalConjugationCohomology M H g⁻¹ r x := by
  rfl

end

end Submission.CField.COps
