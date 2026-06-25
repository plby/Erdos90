import Submission.ClassField.NormIndex.CanonicalTateFormula
import Submission.ClassField.CyclicIdeles.ClassRestrictionComparison

/-!
# Idèle norm indices as Tate-degree-zero cardinalities

This is the noncyclic cardinality form of Corollary VII.4.4 used in the
Sylow reduction.
-/

namespace Submission.CField.CIdeles

open CategoryTheory Limits
open IsDedekindDomain NumberField Representation
open Submission.CField.Shifting
open Submission.CField.Ideles
open Submission.CField.ICohomo
open Submission.CField.NIndex
open Submission.CField.HNorm

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

set_option maxHeartbeats 3000000 in
-- The canonical fixed-class equivalence contains nested idèle quotients.
/-- Tate degree zero for the resized idèle-class representation has
cardinality equal to the literal idèle norm index, without a cyclicity
hypothesis. -/
theorem nat_tate_index
    (K L : Type u) [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L] :
    letI : Fintype Gal(L/K) := Fintype.ofFinite Gal(L/K)
    Nat.card (tateCohomologyZero (ideleClassRep K L)) =
      (normPrincipalSubgroup K L).index := by
  letI : Fintype Gal(L/K) := Fintype.ofFinite Gal(L/K)
  let E := canonicalExtensionData (K := K) (L := L)
  calc
    Nat.card (tateCohomologyZero (ideleClassRep K L)) =
        Nat.card (tateZero
          (classCokernelRepresentation (K := K) (L := L))) :=
      (Nat.card_congr
        (scalarResizingAdd K L).toEquiv).symm
    _ = (normPrincipalSubgroup K L).index :=
      tate_principal_index E
        (canonical_fixed_bijective
          (K := K) (L := L))
        (canonical_idele_compatible (K := K) (L := L))

/-- Finiteness of the literal norm quotient implies finiteness of Tate degree
zero for the idèle-class representation. -/
theorem idele_class_tate
    (K L : Type u) [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [Finite (IK K ⧸ normPrincipalSubgroup K L)] :
    letI : Fintype Gal(L/K) := Fintype.ofFinite Gal(L/K)
    Finite (tateCohomologyZero (ideleClassRep K L)) := by
  letI : Fintype Gal(L/K) := Fintype.ofFinite Gal(L/K)
  apply Nat.finite_of_card_ne_zero
  rw [nat_tate_index K L,
    Subgroup.index_eq_card]
  exact Nat.card_pos.ne'

/-- Finiteness of Tate degree zero implies finiteness of the literal idèle
norm quotient. -/
theorem idele_tate_zero
    (K L : Type u) [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L] :
    letI : Fintype Gal(L/K) := Fintype.ofFinite Gal(L/K)
    Finite (tateCohomologyZero (ideleClassRep K L)) →
      Finite (IK K ⧸ normPrincipalSubgroup K L) := by
  letI : Fintype Gal(L/K) := Fintype.ofFinite Gal(L/K)
  intro hfinite
  letI : Finite (tateCohomologyZero (ideleClassRep K L)) := hfinite
  apply Nat.finite_of_card_ne_zero
  rw [← Subgroup.index_eq_card,
    ← nat_tate_index K L]
  exact Nat.card_pos.ne'

end

end Submission.CField.CIdeles
