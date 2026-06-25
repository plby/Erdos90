import Mathlib.RepresentationTheory.FiniteIndex
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Shapiro

/-!
# Milne, Class Field Theory, Example II.1.29

Let `H` be a finite-index subgroup of `G`.  Shapiro's lemma identifies the cohomology of `H`
with the cohomology of the coinduced `G`-module.  Because `H` has finite index, Mathlib's
`Rep.coindResAdjunction` makes coinduction also left adjoint to restriction; its counit is the
coefficient trace

`Coind_H^G (Res_H^G A) ⟶ A`.

The composite of inverse Shapiro with the map induced by this trace is Milne's corestriction
homomorphism in every degree.
-/

namespace Towers.CField.COps

open CategoryTheory Rep

universe u

variable {k G : Type u} [CommRing k] [Group G]

/-- The coefficient trace from the coinduced restricted representation to the original
representation.  In Milne's coset-representative description it sends `φ` to
`∑ s, s • φ(s⁻¹)`. -/
noncomputable def corestrictionTrace (A : Rep k G) (H : Subgroup G) [H.FiniteIndex] :
    coind H.subtype (res H.subtype A) ⟶ A :=
  letI := Classical.decRel (QuotientGroup.rightRel H)
  (coindResAdjunction k H).counit.app A

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

private lemma ind_res_counit
    (A : Rep k G) (H : Subgroup G) (g : G) (x : A) :
    ((indResAdjunction k H.subtype).counit.app A).hom
        (Representation.IndV.mk H.subtype (A.ρ.comp H.subtype) g x) =
      A.ρ g⁻¹ x := by
  change ((indResHomEquiv H.subtype (res H.subtype A) A).symm (𝟙 _)).hom
      (Representation.IndV.mk H.subtype (A.ρ.comp H.subtype) g x) =
        A.ρ g⁻¹ x
  simp [indResHomEquiv]

/-- The coefficient trace written as Milne's finite sum over right cosets.
For the representative `g = Quotient.out q`, the corresponding summand is
`g⁻¹ • f(g)`.  Replacing `g` by `s⁻¹` gives Milne's notation
`∑ s, s • f(s⁻¹)`. -/
theorem corestrictionTrace_apply
    (A : Rep k G) (H : Subgroup G) [H.FiniteIndex]
    (f : coind H.subtype (res H.subtype A)) :
    (corestrictionTrace A H).hom f =
      ∑ q : Quotient (QuotientGroup.rightRel H),
        A.ρ (Quotient.out q)⁻¹ (f.1 (Quotient.out q)) := by
  letI := Classical.decRel (QuotientGroup.rightRel H)
  rw [corestrictionTrace, coindResAdjunction_counit_app]
  change ((indResAdjunction k H.subtype).counit.app A).hom
      (coindToInd (res H.subtype A) f) = _
  rw [coindToInd_apply]
  change ((indResAdjunction k H.subtype).counit.app A).hom.toLinearMap
      (Finset.univ.sum fun q : Quotient (QuotientGroup.rightRel H) ↦ _) = _
  rw [map_sum]
  apply Fintype.sum_congr
  intro q
  conv_lhs =>
    rw [show q = Quotient.mk'' (Quotient.out q) from
      (Quotient.out_eq' q).symm]
  exact ind_res_counit A H
    (Quotient.out q) (f.1 (Quotient.out q))

/-- **Example II.1.29.** Cohomological corestriction for a finite-index subgroup, obtained by
inverse Shapiro followed by the map induced by the coefficient trace. -/
noncomputable def corestriction
    (A : Rep k G) (H : Subgroup G) [H.FiniteIndex] (n : ℕ) :
    groupCohomology (res H.subtype A) n ⟶ groupCohomology A n :=
  (groupCohomology.coindIso (res H.subtype A) n).inv ≫
    groupCohomology.map (MonoidHom.id G) (corestrictionTrace A H) n

/-- Restriction in group cohomology, recorded next to corestriction for use in Milne's
Proposition II.1.30. -/
noncomputable def restriction
    (A : Rep k G) (H : Subgroup G) (n : ℕ) :
    groupCohomology A n ⟶ groupCohomology (res H.subtype A) n :=
  groupCohomology.map H.subtype (𝟙 _) n

end Towers.CField.COps
