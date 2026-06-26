import Submission.ClassField.LocalReciprocity.MaximalIntermediate
import Submission.ClassField.NormIndex.IdeleTowerTransitivity
import Submission.ClassField.GlobalClass.MaximalAbelianSubextension

/-!
# The Galois case of the global norm limitation theorem

For a finite Galois extension, the maximal abelian subextension is the fixed
field of the commutator subgroup.  This file proves the maximality and norm
containment parts of Theorem VIII.4.8 for that literal field.  As in the
local proof of Theorem III.3.5, equality is then reduced to the genuine
cohomological input: the norm quotient has the cardinality of the
abelianized Galois group.
-/

namespace Submission.CField.GClass

open NumberField
open Submission.CField.LRecip
open Submission.CField.Ideles
open Submission.CField.NIndex
open scoped IsMulCommutative

noncomputable section

universe u

/-- In a finite Galois extension, the fixed field of the commutator is the
maximal abelian Galois intermediate field appearing in Theorem VIII.4.8. -/
theorem maximal_intermediate_field
    (K L : Type u) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] :
    MaximalGaloisSubextension K L
      (maximalAbelianIntermediate K L) := by
  refine ⟨inferInstance, inferInstance, ?_⟩
  intro F hFgal hFab
  letI : IsGalois K F := hFgal
  letI : IsMulCommutative Gal(F/K) := hFab
  exact maximal_abelian_field K L F

/-- The canonical idèle-class norm is transitive in a finite Galois tower. -/
theorem canonical_norm_trans
    {K E L : Type u} [Field K] [Field E] [Field L]
    [NumberField K] [NumberField E] [NumberField L]
    [Algebra K E] [Algebra E L] [Algebra K L] [IsScalarTower K E L]
    [FiniteDimensional K E] [FiniteDimensional E L]
    [IsGalois K E] [IsGalois E L] [IsGalois K L] :
    canonicalIdeleNorm (K := K) (L := L) =
      (canonicalIdeleNorm (K := K) (L := E)).comp
        (canonicalIdeleNorm (K := E) (L := L)) := by
  apply MonoidHom.ext
  intro c
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective
    (principalIdeles (RingOfIntegers L) L) c
  simp only [canonical_idele_mk]
  rw [ideleNorm_trans (K := K) (E := E) (L := L)]
  rfl

/-- Norm transitivity gives the easy containment for the maximal abelian
subextension in the Galois case of Theorem VIII.4.8. -/
theorem galois_norm_containment
    (K L : Type u) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] :
    (canonicalIdeleNorm (K := K) (L := L)).range ≤
      (canonicalIdeleNorm (K := K)
        (L := maximalAbelianIntermediate K L)).range := by
  let M := maximalAbelianIntermediate K L
  letI : IsGalois M L := inferInstance
  rw [canonical_norm_trans
    (K := K) (E := M) (L := L)]
  rintro _ ⟨c, rfl⟩
  exact ⟨canonicalIdeleNorm (K := M) (L := L) c, rfl⟩

/-- The cohomological cardinality input in the Galois case of global norm
limitation.  It is the global analogue of
`nat_card_abelianization`. -/
def GaloisIndexFormula : Prop :=
  ∀ (K L : Type u) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L],
    (canonicalIdeleNorm (K := K) (L := L)).range.index =
      Nat.card (Abelianization Gal(L/K))

/-- With the abelianized norm-index formula supplied, norm containment is an
equality for the canonical maximal abelian subextension. -/
theorem galois_canonical_index
    (hindex : GaloisIndexFormula.{u})
    (K L : Type u) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] :
    (canonicalIdeleNorm (K := K) (L := L)).range =
      (canonicalIdeleNorm (K := K)
        (L := maximalAbelianIntermediate K L)).range := by
  let M := maximalAbelianIntermediate K L
  let NL := (canonicalIdeleNorm (K := K) (L := L)).range
  let NM := (canonicalIdeleNorm (K := K) (L := M)).range
  have hNL : NL.index = Nat.card (Abelianization Gal(L/K)) :=
    hindex K L
  have hNM : NM.index = Nat.card (Abelianization Gal(M/K)) :=
    hindex K M
  have hcard : Nat.card (Abelianization Gal(L/K)) =
      Nat.card (Abelianization Gal(M/K)) := by
    calc
      Nat.card (Abelianization Gal(L/K)) = Nat.card Gal(M/K) :=
        Nat.card_congr (maximalAbelianGalois K L).toEquiv
      _ = Nat.card (Abelianization Gal(M/K)) :=
        Nat.card_congr (Abelianization.equivOfComm
          (H := Gal(M/K))).toEquiv
  letI : NL.FiniteIndex := Subgroup.finiteIndex_iff.mpr (by
    rw [hNL]
    exact Nat.card_pos.ne')
  exact subgroup_index
    (galois_norm_containment K L)
    (hNL.trans (hcard.trans hNM.symm))

/-- Galois-case form of Theorem VIII.4.8, with the maximal field allowed to
be presented by any intermediate field satisfying the source's maximality
property. -/
theorem galois_of_index
    (hindex : GaloisIndexFormula.{u})
    (K L : Type u) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (M : IntermediateField K L)
    (hM : MaximalGaloisSubextension K L M) :
    (canonicalIdeleNorm (K := K) (L := L)).range =
      (canonicalIdeleNorm (K := K) (L := M)).range := by
  letI : IsGalois K M := hM.1
  letI : IsMulCommutative Gal(M/K) := hM.2.1
  have hMcanonical : M = maximalAbelianIntermediate K L := by
    apply le_antisymm
    · exact maximal_abelian_field K L M
    · exact hM.2.2 (maximalAbelianIntermediate K L)
        inferInstance inferInstance
  subst M
  exact galois_canonical_index hindex K L

end

end Submission.CField.GClass
