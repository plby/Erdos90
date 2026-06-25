import Towers.ClassField.Shifting.TransportAlongEquivalences
import Towers.ClassField.NormIndex.ClassCokernelComparison
import Towers.ClassField.CyclicIdeles.ZeroSylowRestriction
import Towers.ClassField.HasseNorm.ClassH1

/-!
# Idèle-class representations at a fixed field

Restriction of the idèle-class representation for `L/K` to a subgroup `H`
is the idèle-class representation for `L/Lᴴ`, after relabelling the Galois
group by the fundamental-theorem equivalence.
-/

namespace Towers.CField.CIdeles

open CategoryTheory Representation
open Towers.CField.Shifting
open Towers.CField.Ideles
open Towers.CField.NIndex
open Towers.CField.HNorm

noncomputable section

universe u

private noncomputable def restrictedExplicitIso
    (K L : Type u) [Field K] [Field L]
    [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (H : Subgroup Gal(L/K)) :
    let E := IntermediateField.fixedField H
    let eH := IntermediateField.subgroupEquivAlgEquiv H
    Rep.res eH.toMonoidHom
        (explicitIdeleRepresentation (K := E) (L := L)) ≅
      Rep.res H.subtype
        (explicitIdeleRepresentation (K := K) (L := L)) := by
  dsimp only
  apply Rep.mkIso
  refine
    { toLinearEquiv := LinearEquiv.refl ℤ
        (Additive (IdeleClassGroup (NumberField.RingOfIntegers L) L))
      isIntertwining' := ?_ }
  intro h
  apply LinearMap.ext
  intro c
  rfl

private noncomputable def restrictedIntegralIso
    (K L : Type u) [Field K] [Field L]
    [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (H : Subgroup Gal(L/K)) :
    let E := IntermediateField.fixedField H
    let eH := IntermediateField.subgroupEquivAlgEquiv H
    Rep.res eH.toMonoidHom
        (classCokernelRepresentation (K := E) (L := L)) ≅
      Rep.res H.subtype
        (classCokernelRepresentation (K := K) (L := L)) := by
  dsimp only
  let eH := IntermediateField.subgroupEquivAlgEquiv H
  exact
    (Rep.resFunctor eH.toMonoidHom).mapIso
        (cokernelIsoExplicit (K := IntermediateField.fixedField H)
          (L := L)) ≪≫
      restrictedExplicitIso K L H ≪≫
      ((Rep.resFunctor H.subtype).mapIso
        (cokernelIsoExplicit (K := K) (L := L))).symm

/-- Equivariant comparison of the resized representations after restriction
to an actual fixed-field subgroup. -/
noncomputable def restrictedCohomologyIso
    (K L : Type u) [Field K] [Field L]
    [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (H : Subgroup Gal(L/K)) :
    let E := IntermediateField.fixedField H
    let eH := IntermediateField.subgroupEquivAlgEquiv H
    Rep.res eH.toMonoidHom (ideleCohomologyRepresentation E L) ≅
      Rep.res H.subtype (ideleCohomologyRepresentation K L) := by
  dsimp only
  let E := IntermediateField.fixedField H
  let eH := IntermediateField.subgroupEquivAlgEquiv H
  letI : Fintype Gal(L/K) := Fintype.ofFinite Gal(L/K)
  letI : Fintype H := Fintype.ofFinite H
  letI : Fintype Gal(L/E) := Fintype.ofFinite Gal(L/E)
  exact
    (Rep.resFunctor eH.toMonoidHom).mapIso
        (intUIso E L).symm ≪≫
      uliftIntegralIso (restrictedIntegralIso K L H) ≪≫
      (Rep.resFunctor H.subtype).mapIso (intUIso K L)

/-- Cohomology of the restricted ambient idèle-class representation is
cohomology of the actual extension over the subgroup fixed field. -/
noncomputable def restrictedIdeleCohomology
    (K L : Type u) [Field K] [Field L]
    [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (H : Subgroup Gal(L/K)) (n : ℕ) :
    let E := IntermediateField.fixedField H
    groupCohomology (ideleCohomologyRepresentation E L) n ≃+
      groupCohomology
        (Rep.res H.subtype (ideleCohomologyRepresentation K L)) n := by
  dsimp only
  let E := IntermediateField.fixedField H
  let eH := IntermediateField.subgroupEquivAlgEquiv H
  exact
    (cohomologyMulIso eH
      (ideleCohomologyRepresentation E L) n).toLinearEquiv.toAddEquiv |>.trans
        (((groupCohomology.functor (ULift.{u} ℤ) H n).mapIso
          (restrictedCohomologyIso K L H)).toLinearEquiv.toAddEquiv)

/-- Tate degree zero has the same fixed-field restriction comparison. -/
noncomputable def restrictedIdeleTate
    (K L : Type u) [Field K] [Field L]
    [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (H : Subgroup Gal(L/K)) :
    let E := IntermediateField.fixedField H
    letI : Fintype Gal(L/K) := Fintype.ofFinite Gal(L/K)
    letI : Fintype H := Fintype.ofFinite H
    letI : Fintype Gal(L/E) := Fintype.ofFinite Gal(L/E)
    tateCohomologyZero (ideleCohomologyRepresentation E L) ≃+
      tateCohomologyZero
        (Rep.res H.subtype (ideleCohomologyRepresentation K L)) := by
  dsimp only
  let E := IntermediateField.fixedField H
  let eH := IntermediateField.subgroupEquivAlgEquiv H
  letI : Fintype Gal(L/K) := Fintype.ofFinite Gal(L/K)
  letI : Fintype H := Fintype.ofFinite H
  letI : Fintype Gal(L/E) := Fintype.ofFinite Gal(L/E)
  exact
    (tateCohomologyAdd eH
      (ideleCohomologyRepresentation E L)).trans
        (tateZeroIso
          (restrictedCohomologyIso K L H)).toAddEquiv

set_option maxHeartbeats 3000000 in
-- Keeping all three `Fintype` choices in one dependent `let` avoids an
-- expensive comparison between extensionally equal norm operators.
/-- Finiteness of Tate degree zero transports from the fixed-field extension
to the restricted ambient representation. -/
theorem restricted_fixed_field
    (K L : Type u) [Field K] [Field L]
    [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (H : Subgroup Gal(L/K)) :
    let E := IntermediateField.fixedField H
    letI : Fintype Gal(L/K) := Fintype.ofFinite Gal(L/K)
    letI : Fintype H := Fintype.ofFinite H
    letI : Fintype Gal(L/E) := Fintype.ofFinite Gal(L/E)
    Finite (tateCohomologyZero
        (ideleCohomologyRepresentation E L)) →
      Finite (tateCohomologyZero
        (Rep.res H.subtype (ideleCohomologyRepresentation K L))) := by
  dsimp only
  let E := IntermediateField.fixedField H
  letI : Fintype Gal(L/K) := Fintype.ofFinite Gal(L/K)
  letI : Fintype H := Fintype.ofFinite H
  letI : Fintype Gal(L/E) := Fintype.ofFinite Gal(L/E)
  intro hfinite
  letI : Finite (tateCohomologyZero
      (ideleCohomologyRepresentation E L)) := hfinite
  exact Finite.of_equiv _
    (restrictedIdeleTate K L H).toEquiv

set_option maxHeartbeats 1000000 in
-- As above, the dependent `let` fixes the norm operators definitionally.
/-- Tate degree zero has the same cardinality after fixed-field restriction. -/
theorem nat_restricted_fixed
    (K L : Type u) [Field K] [Field L]
    [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (H : Subgroup Gal(L/K)) :
    let E := IntermediateField.fixedField H
    letI : Fintype Gal(L/K) := Fintype.ofFinite Gal(L/K)
    letI : Fintype H := Fintype.ofFinite H
    letI : Fintype Gal(L/E) := Fintype.ofFinite Gal(L/E)
    Nat.card (tateCohomologyZero
        (Rep.res H.subtype (ideleCohomologyRepresentation K L))) =
      Nat.card (tateCohomologyZero
        (ideleCohomologyRepresentation E L)) := by
  dsimp only
  let E := IntermediateField.fixedField H
  letI : Fintype Gal(L/K) := Fintype.ofFinite Gal(L/K)
  letI : Fintype H := Fintype.ofFinite H
  letI : Fintype Gal(L/E) := Fintype.ofFinite Gal(L/E)
  exact (Nat.card_congr
    (restrictedIdeleTate K L H).toEquiv).symm

set_option maxHeartbeats 1000000 in
-- This packages the restriction theorem and both cardinal transports under
-- one coherent choice of the three finite group structures.
/-- The `p`-primary part of ambient Tate degree zero divides Tate degree zero
over the Sylow fixed field. -/
theorem ord_proj_dvd
    (K L : Type u) [Field K] [Field L]
    [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (p : ℕ) [Fact p.Prime] (P : Sylow p Gal(L/K)) :
    let E := IntermediateField.fixedField (P : Subgroup Gal(L/K))
    letI : Fintype Gal(L/K) := Fintype.ofFinite Gal(L/K)
    letI : Fintype P := Fintype.ofFinite P
    letI : Fintype Gal(L/E) := Fintype.ofFinite Gal(L/E)
    Finite (tateCohomologyZero
        (ideleCohomologyRepresentation K L)) →
      Finite (tateCohomologyZero
        (ideleCohomologyRepresentation E L)) →
      ordProj[p] (Nat.card (tateCohomologyZero
          (ideleCohomologyRepresentation K L))) ∣
        Nat.card (tateCohomologyZero
          (ideleCohomologyRepresentation E L)) := by
  dsimp only
  let E := IntermediateField.fixedField (P : Subgroup Gal(L/K))
  letI : Fintype Gal(L/K) := Fintype.ofFinite Gal(L/K)
  letI : Fintype P := Fintype.ofFinite P
  letI : Fintype Gal(L/E) := Fintype.ofFinite Gal(L/E)
  intro hambient hfixed
  letI : Finite (tateCohomologyZero
      (ideleCohomologyRepresentation K L)) := hambient
  letI : Finite (tateCohomologyZero
      (ideleCohomologyRepresentation E L)) := hfixed
  letI : Finite (tateCohomologyZero
      (Rep.res (P : Subgroup Gal(L/K)).subtype
        (ideleCohomologyRepresentation K L))) := by
    apply Nat.finite_of_card_ne_zero
    rw [nat_restricted_fixed K L P]
    exact Nat.card_pos.ne'
  have h := ord_proj_restriction
    (ideleCohomologyRepresentation K L) p P
  rw [nat_restricted_fixed K L P] at h
  exact h

end

end Towers.CField.CIdeles
