import Towers.ClassField.CyclicIdeles.ClassRestrictionComparison
import Towers.ClassField.CyclicIdeles.IdeleTateIndex
import Towers.ClassField.GlobalClass.RelativeH2
import Towers.ClassField.GlobalClass.GaloisNormLimitation

/-!
# The Tate-isomorphism input to global norm limitation

Milne obtains the Galois norm-index formula by applying Theorem II.3.11 to
the global fundamental class.  The arithmetic hypotheses of that theorem
are already expressed by Theorems VII.5.1 and VIII.4.7, and restriction to
a subgroup is already identified with the idèle-class representation over
its fixed field.

The implementation of Theorem II.3.11 currently lives only in universe
zero, whereas number fields in this project are universe-polymorphic.  This
file therefore isolates precisely its missing universe-polymorphic
degree-minus-two consequence and proves every remaining arithmetic and
group-theoretic step of the Galois norm-index formula.
-/

namespace Towers.CField.GClass

open AddSubgroup CategoryTheory Limits NumberField Representation
open Towers.CField.Shifting
open Towers.CField.Ideles
open Towers.CField.NIndex
open Towers.CField.CIdeles

noncomputable section

universe u

private abbrev IK (K : Type u) [Field K] [NumberField K] :=
  IdeleGroup (RingOfIntegers K) K

private abbrev normPrincipalSubgroup
    (K L : Type u) [Field K] [Field L]
    [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] : Subgroup (IK K) :=
  principalIdeles (RingOfIntegers K) K ⊔
    ideleNormSubgroup (K := K) (L := L)

/-- The universe-polymorphic degree-minus-two consequence of Tate's
Theorem II.3.11.  This is the exact pure group-cohomological input used in
the source proof of Theorem VIII.4.8. -/
def TateNegBridge : Prop :=
  ∀ (G : Type u) [Group G] [Fintype G]
    (C : Rep (ULift.{u} ℤ) G)
    (gamma : groupCohomology.H2 C),
    (∀ x : groupCohomology.H2 C, x ∈ zmultiples gamma) →
    (∀ H : Subgroup G,
      IsZero (groupCohomology.H1 (Rep.res H.subtype C))) →
    (∀ H : Subgroup G,
      Nat.card (groupCohomology.H2 (Rep.res H.subtype C)) =
        Nat.card H) →
    Nonempty
      (Additive (Abelianization G) ≃+ tateCohomologyZero C)

/-- The global Tate isomorphism immediately preceding norm limitation in
the text, stated for the actual idèle-class representation. -/
def GaloisTateIsomorphism : Prop :=
  ∀ (K L : Type u) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L],
    letI : Fintype Gal(L/K) := Fintype.ofFinite Gal(L/K)
    Nonempty
      (Additive (Abelianization Gal(L/K)) ≃+
        tateCohomologyZero (ideleCohomologyRepresentation K L))

/-- Theorem VII.5.1 and the invariant of Theorem VIII.4.7 discharge all
arithmetic hypotheses of Tate's theorem, including those over every fixed
field. -/
theorem isomorphism_previous_results
    (h51 : IdeleCohomologyClaims.{u})
    (h47 : RelativeInvariantGenerator.{u})
    (hTate : TateNegBridge.{u}) :
    GaloisTateIsomorphism.{u} := by
  intro K L _ _ _ _ _ _ _
  letI : Fintype Gal(L/K) := Fintype.ofFinite Gal(L/K)
  obtain ⟨inv, _, _⟩ := h47 K L
  let gamma : groupCohomology.H2
      (ideleCohomologyRepresentation K L) :=
    fundamentalClassInvariant inv
  apply hTate Gal(L/K)
      (ideleCohomologyRepresentation K L) gamma
  · intro x
    exact zmultiples_fundamental_invariant inv x
  · intro H
    let E := IntermediateField.fixedField H
    have hzero : IsZero (groupCohomology.H1
        (ideleCohomologyRepresentation E L)) :=
      (h51 E L).2.1
    let e := restrictedIdeleCohomology K L H 1
    letI : Subsingleton (groupCohomology.H1
        (ideleCohomologyRepresentation E L)) :=
      ModuleCat.subsingleton_of_isZero hzero
    letI : Subsingleton (groupCohomology.H1
        (Rep.res H.subtype
          (ideleCohomologyRepresentation K L))) :=
      e.symm.injective.subsingleton
    exact ModuleCat.isZero_of_subsingleton _
  · intro H
    let E := IntermediateField.fixedField H
    obtain ⟨invH, _, _⟩ := h47 E L
    calc
      Nat.card (groupCohomology.H2
          (Rep.res H.subtype
            (ideleCohomologyRepresentation K L))) =
          Nat.card (groupCohomology.H2
            (ideleCohomologyRepresentation E L)) :=
        (Nat.card_congr
          (restrictedIdeleCohomology K L H 2).toEquiv).symm
      _ = Module.finrank E L := nat_card_invariant invH
      _ = Nat.card H := IntermediateField.finrank_fixedField_eq_card H

/-- The Tate isomorphism has exactly the cardinality needed for the
abelianized global norm-index formula. -/
theorem galois_formula_isomorphism
    (hTate : GaloisTateIsomorphism.{u}) :
    GaloisIndexFormula.{u} := by
  intro K L _ _ _ _ _ _ _
  letI : Fintype Gal(L/K) := Fintype.ofFinite Gal(L/K)
  obtain ⟨e⟩ := hTate K L
  calc
    (canonicalIdeleNorm (K := K) (L := L)).range.index =
        (normPrincipalSubgroup K L).index := by
      rw [Subgroup.index_eq_card]
      exact nat_principal_index K L
    _ = Nat.card
        (tateCohomologyZero (ideleCohomologyRepresentation K L)) :=
      (nat_tate_index K L).symm
    _ = Nat.card (Abelianization Gal(L/K)) :=
      (Nat.card_congr e.toEquiv).symm

/-- The Galois case of norm limitation, now reduced only to the actual
global invariant and the universe-polymorphic form of Tate's already
formalized theorem. -/
theorem galois_previous_results
    (h51 : IdeleCohomologyClaims.{u})
    (h47 : RelativeInvariantGenerator.{u})
    (hTate : TateNegBridge.{u})
    (K L : Type u) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (M : IntermediateField K L)
    (hM : MaximalGaloisSubextension K L M) :
    (canonicalIdeleNorm (K := K) (L := L)).range =
      (canonicalIdeleNorm (K := K) (L := M)).range := by
  apply galois_of_index _ K L M hM
  apply galois_formula_isomorphism
  exact isomorphism_previous_results h51 h47 hTate

end

end Towers.CField.GClass
