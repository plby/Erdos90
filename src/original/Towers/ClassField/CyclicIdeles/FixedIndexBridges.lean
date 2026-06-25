import Towers.ClassField.CyclicIdeles.ClassRestrictionComparison
import Towers.ClassField.CyclicIdeles.Finiteness
import Towers.ClassField.CyclicIdeles.FixedFieldBridge
import Towers.ClassField.CyclicIdeles.IdeleTateIndex
import Towers.ClassField.CyclicIdeles.IdeleClassRep

/-!
# Chapter VII, Section 5, Lemma 5.3: fixed-field and index bridges

Lemma VII.4.1 and the concrete restriction comparison identify the Tate and
ordinary cohomology groups over a Sylow fixed field.  Together with the
abstract Sylow restriction results, this discharges all four bridges used by
the source reduction of Lemma 5.3.
-/

namespace Towers.CField.CIdeles

open CategoryTheory Limits
open IsDedekindDomain NumberField Representation
open Towers.CField.Shifting
open Towers.CField.Ideles
open Towers.CField.ICohomo
open Towers.CField.NIndex
open Towers.CField.HNorm

noncomputable section

universe u

private abbrev IK (K : Type u) [Field K] [NumberField K] :=
  IdeleGroup (NumberField.RingOfIntegers K) K

private abbrev normPrincipalSubgroup
    (K L : Type u) [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] : Subgroup (IK K) :=
  principalIdeles (NumberField.RingOfIntegers K) K ⊔
    ideleNormSubgroup (K := K) (L := L)

private abbrev ideleClassRep
    (K L : Type u) [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L] :
    Rep (ULift.{u} ℤ) Gal(L/K) :=
  ideleCohomologyRepresentation K L

set_option maxHeartbeats 5000000 in
-- Comparing literal norm quotients with Tate cohomology expands several
-- quotient constructions.
private theorem sylow_fixed_fields
    (K L : Type u) [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (hfinite : ∀ (p : ℕ) [Fact p.Prime] (P : Sylow p Gal(L/K)),
      Finite (IK (IntermediateField.fixedField
          (P : Subgroup Gal(L/K))) ⧸
        normPrincipalSubgroup
          (IntermediateField.fixedField (P : Subgroup Gal(L/K))) L)) :
    Finite (IK K ⧸ normPrincipalSubgroup K L) := by
  letI : Fintype Gal(L/K) := Fintype.ofFinite Gal(L/K)
  have hTate : Finite (tateCohomologyZero (ideleClassRep K L)) := by
    apply tate_cohomology_sylow (ideleClassRep K L)
    intro p _ P
    letI : Fintype P := Fintype.ofFinite P
    letI : IsGalois
        (IntermediateField.fixedField (P : Subgroup Gal(L/K))) L :=
      inferInstance
    letI : Finite (IK (IntermediateField.fixedField
        (P : Subgroup Gal(L/K))) ⧸ normPrincipalSubgroup
          (IntermediateField.fixedField (P : Subgroup Gal(L/K))) L) :=
      hfinite p P
    letI : Fintype Gal(L/IntermediateField.fixedField
        (P : Subgroup Gal(L/K))) :=
      Fintype.ofFinite Gal(L/IntermediateField.fixedField
        (P : Subgroup Gal(L/K)))
    have hfixed : Finite (tateCohomologyZero
        (ideleCohomologyRepresentation
        (IntermediateField.fixedField (P : Subgroup Gal(L/K))) L)) :=
      idele_class_tate
        (IntermediateField.fixedField (P : Subgroup Gal(L/K))) L
    apply Nat.finite_of_card_ne_zero
    rw [nat_restricted_fixed K L P]
    letI : Finite (tateCohomologyZero
        (ideleCohomologyRepresentation
          (IntermediateField.fixedField (P : Subgroup Gal(L/K))) L)) :=
      hfixed
    exact Nat.card_pos.ne'
  letI : Finite (tateCohomologyZero (ideleClassRep K L)) := hTate
  exact idele_tate_zero K L hTate

set_option maxHeartbeats 1000000 in
-- The bridge wrapper contains deeply nested idèle quotient types.
/-- Finiteness of the literal norm quotient is detected on all Sylow fixed
fields. -/
theorem ideleFinitenessBridge :
    IdeleFinitenessBridge.{u} := by
  intro K L _ _ _ _ _ _ _ hfinite
  exact sylow_fixed_fields K L hfinite

set_option maxHeartbeats 5000000 in
-- The primary-index comparison simultaneously unfolds Tate and idèle
-- quotient cardinalities.  Keeping the arithmetic implication separate
-- avoids reducing the deeply nested bridge record while checking the proof.
private theorem ideleIndexPrimary
    (K L : Type u) [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (p : ℕ) [Fact p.Prime] (P : Sylow p Gal(L/K))
    (hFinite : Finite (IK K ⧸ normPrincipalSubgroup K L))
    (hfixedDvd : (normPrincipalSubgroup
        (IntermediateField.fixedField (P : Subgroup Gal(L/K))) L).index ∣
      Nat.card P) :
    ordProj[p] (normPrincipalSubgroup K L).index ∣ Nat.card P := by
  letI : Finite (IK K ⧸ normPrincipalSubgroup K L) := hFinite
  letI : Fintype Gal(L/K) := Fintype.ofFinite Gal(L/K)
  letI : Fintype P := Fintype.ofFinite P
  let E := IntermediateField.fixedField (P : Subgroup Gal(L/K))
  letI : IsGalois E L := inferInstance
  letI : Fintype Gal(L/E) := Fintype.ofFinite Gal(L/E)
  have hambient : Finite (tateCohomologyZero (ideleClassRep K L)) :=
    idele_class_tate K L
  have hfixedNe : (normPrincipalSubgroup E L).index ≠ 0 := by
    intro hz
    exact Nat.card_pos.ne' (Nat.eq_zero_of_zero_dvd (hz ▸ hfixedDvd))
  letI : Finite (IK E ⧸ normPrincipalSubgroup E L) := by
    apply Nat.finite_of_card_ne_zero
    rw [← Subgroup.index_eq_card]
    exact hfixedNe
  have hfixedTate : Finite (tateCohomologyZero (ideleClassRep E L)) :=
    idele_class_tate E L
  have hprimary := ord_proj_dvd
    K L p P hambient hfixedTate
  rw [nat_tate_index K L,
    nat_tate_index E L] at hprimary
  exact hprimary.trans hfixedDvd

set_option maxHeartbeats 1000000 in
-- The universal wrapper now only packages the already checked pointwise data.
/-- The `p`-primary part of the ambient literal norm index injects into the
norm quotient over the Sylow fixed field. -/
theorem idelePrimaryBridge :
    IdelePrimaryBridge.{u} := by
  refine ⟨?_⟩
  intro K L _ _ _ _ _ _ _ p _ P
  exact ⟨ideleIndexPrimary K L p P⟩

end

end Towers.CField.CIdeles
