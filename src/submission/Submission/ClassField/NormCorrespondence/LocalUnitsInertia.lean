import Submission.ClassField.NormCorrespondence.Main
import Submission.ClassField.NormCorrespondence.UnramifiedNormGroups


/-!
# Local units and finite-layer inertia under reciprocity

For a finite abelian layer, its reciprocity-theoretic inertia subgroup is the
image of the valuation-unit subgroup under the finite reciprocity map.  This
file proves that local units map onto that subgroup and packages the exact
character-cancellation statements needed in global-to-local arguments.

It also verifies the normalization on canonical unramified layers: valuation
units lie in their norm groups, hence finite reciprocity kills them there.
The identification of this reciprocity-theoretic subgroup with an inertia
subgroup defined from an integral model can be added independently.
-/

namespace Submission.CField.LFTheory

open ValuativeRel
open LBrauer

noncomputable section

universe u v

variable (K : Type u) [NontriviallyNormedField K]
  [IsUltrametricDist K] [ValuativeRel K]
  [IsNonarchimedeanLocalField K]
  [Valuation.Compatible (NormedField.valuation (K := K))]

/-- The finite-layer inertia subgroup defined by local reciprocity: the image
of the valuation-unit subgroup in the finite Galois group. -/
noncomputable def reciprocityInertiaSubgroup
    (rec : Kˣ →* AbsoluteAbelianGalois K)
    (L : FASubext K) :
    Subgroup Gal(L.finiteIntermediateField/K) :=
  (localUnitSubgroup K).map (finiteReciprocityHom rec L)

/-- The finite reciprocity map restricted and corestricted to the inertia
subgroup. -/
noncomputable def unitsReciprocityInertia
    (rec : Kˣ →* AbsoluteAbelianGalois K)
    (L : FASubext K) :
    localUnitSubgroup K →* reciprocityInertiaSubgroup K rec L :=
  (finiteReciprocityHom rec L).subgroupMap (localUnitSubgroup K)

omit [IsUltrametricDist K] [IsNonarchimedeanLocalField K]
  [Valuation.Compatible (NormedField.valuation (K := K))] in
@[simp]
theorem reciprocity_inertia_coe
    (rec : Kˣ →* AbsoluteAbelianGalois K)
    (L : FASubext K) (u : localUnitSubgroup K) :
    ((unitsReciprocityInertia K rec L u :
        reciprocityInertiaSubgroup K rec L) :
      Gal(L.finiteIntermediateField/K)) =
      finiteReciprocityHom rec L u :=
  rfl

omit [IsUltrametricDist K] [IsNonarchimedeanLocalField K]
  [Valuation.Compatible (NormedField.valuation (K := K))] in
/-- Local valuation units map onto finite-layer inertia. -/
theorem reciprocity_inertia_surjective
    (rec : Kˣ →* AbsoluteAbelianGalois K)
    (L : FASubext K) :
    Function.Surjective (unitsReciprocityInertia K rec L) :=
  (finiteReciprocityHom rec L).subgroupMap_surjective (localUnitSubgroup K)

omit [IsUltrametricDist K] [IsNonarchimedeanLocalField K]
  [Valuation.Compatible (NormedField.valuation (K := K))] in
/-- Equivalently, the restricted local-unit map has full range in inertia. -/
theorem reciprocity_inertia_range
    (rec : Kˣ →* AbsoluteAbelianGalois K)
    (L : FASubext K) :
    (unitsReciprocityInertia K rec L).range = ⊤ :=
  MonoidHom.range_eq_top.mpr
    (reciprocity_inertia_surjective K rec L)

omit [Valuation.Compatible (NormedField.valuation (K := K))] in
/-- The finite reciprocity map is surjective at every finite abelian layer. -/
theorem reciprocity_hom_surjective
    (rec : Kˣ →* AbsoluteAbelianGalois K)
    (hrec : IsReciprocityMap K rec)
    (L : FASubext K) :
    Function.Surjective (finiteReciprocityHom rec L) := by
  rcases hrec.2 L with ⟨e, he⟩
  intro sigma
  obtain ⟨q, rfl⟩ := e.surjective sigma
  obtain ⟨x, rfl⟩ :=
    QuotientGroup.mk'_surjective L.normGroup q
  exact ⟨x, (he x).symm⟩

omit [IsUltrametricDist K] [IsNonarchimedeanLocalField K]
  [Valuation.Compatible (NormedField.valuation (K := K))] in
/-- A character of the finite Galois group is trivial on inertia exactly
when its pullback along finite reciprocity is trivial on every local unit. -/
theorem trivial_inertia_units
    (rec : Kˣ →* AbsoluteAbelianGalois K)
    (L : FASubext K)
    {A : Type v} [Group A]
    (chi : Gal(L.finiteIntermediateField/K) →* A) :
    (∀ tau : reciprocityInertiaSubgroup K rec L,
        chi tau = 1) ↔
      ∀ u : localUnitSubgroup K,
        chi (finiteReciprocityHom rec L u) = 1 := by
  constructor
  · intro h u
    exact h (unitsReciprocityInertia K rec L u)
  · intro h tau
    obtain ⟨u, rfl⟩ :=
      reciprocity_inertia_surjective K rec L tau
    exact h u

omit [IsUltrametricDist K] [IsNonarchimedeanLocalField K]
  [Valuation.Compatible (NormedField.valuation (K := K))] in
/-- Two finite-layer characters agree on inertia exactly when their
pullbacks agree on all local valuation units. -/
theorem characters_inertia_units
    (rec : Kˣ →* AbsoluteAbelianGalois K)
    (L : FASubext K)
    {A : Type v} [Group A]
    (chi psi : Gal(L.finiteIntermediateField/K) →* A) :
    (∀ tau : reciprocityInertiaSubgroup K rec L,
        chi tau = psi tau) ↔
      ∀ u : localUnitSubgroup K,
        chi (finiteReciprocityHom rec L u) =
          psi (finiteReciprocityHom rec L u) := by
  constructor
  · intro h u
    exact h (unitsReciprocityInertia K rec L u)
  · intro h tau
    obtain ⟨u, rfl⟩ :=
      reciprocity_inertia_surjective K rec L tau
    exact h u

omit [IsUltrametricDist K]
  [Valuation.Compatible (NormedField.valuation (K := K))] in
/-- Every valuation unit lies in the normalized-order kernel modulo `n`. -/
theorem local_mod_ker
    (n : ℕ) [NeZero n] :
    localUnitSubgroup K ≤ (localOrderMod K n).ker := by
  intro x hx
  apply (mod_ker_dvd K n x).2
  have hxval : valuation K (x : K) = 1 :=
    (local_subgroup K x).1 hx
  have hxorder : localUnitOrder K (Additive.ofMul x) = 0 := by
    apply le_antisymm
    · have h := (local_order_valuation K x 1).2
          (by simp [hxval])
      simpa using h
    · have h := (local_order_valuation K 1 x).2
          (by simp [hxval])
      simpa using h
  rw [hxorder]
  exact dvd_zero (n : ℤ)

/-- Valuation units are norms from every canonical unramified layer. -/
theorem local_unramified_group
    (n : ℕ) [NeZero n] :
    localUnitSubgroup K ≤ (canonicalUnramifiedSubextension K n).normGroup := by
  rw [unramified_subextension_ker]
  exact local_mod_ker K n

/-- On a canonical unramified layer, finite local reciprocity kills every
valuation unit, as required by the units-to-inertia normalization. -/
theorem reciprocity_unramified_units
    (rec : Kˣ →* AbsoluteAbelianGalois K)
    (hrec : IsReciprocityMap K rec)
    (n : ℕ) [NeZero n] (u : localUnitSubgroup K) :
    finiteReciprocityHom rec (canonicalUnramifiedSubextension K n) u = 1 := by
  have huNorm : (u : Kˣ) ∈
      (canonicalUnramifiedSubextension K n).normGroup :=
    local_unramified_group K n u.property
  rw [← reciprocity_hom_ker rec hrec.2
    (canonicalUnramifiedSubextension K n)] at huNorm
  exact huNorm

/-- Thus the reciprocity-theoretic inertia subgroup of a canonical
unramified layer is trivial. -/
theorem reciprocity_inertia_bot
    (rec : Kˣ →* AbsoluteAbelianGalois K)
    (hrec : IsReciprocityMap K rec)
    (n : ℕ) [NeZero n] :
    reciprocityInertiaSubgroup K rec
      (canonicalUnramifiedSubextension K n) = ⊥ := by
  apply le_antisymm
  · rintro _ ⟨u, hu, rfl⟩
    rw [reciprocity_unramified_units
      K rec hrec n ⟨u, hu⟩]
    exact Subgroup.one_mem ⊥
  · exact bot_le

end

end Submission.CField.LFTheory
