import Submission.ClassField.Reciprocity.IdelicReciprocityLaw
import Submission.ClassField.NormIndex.HerbrandCardinalityBound

/-!
# The idèle-class norm quotient and the literal idèle index

This file isolates the group-theoretic part of Corollary VII.4.4.  The range
of the canonical norm on idèle classes is the image of the idèle norm
subgroup, so Noether's third isomorphism theorem identifies its quotient
with `I_K / (Kˣ · Nm(I_L))`.
-/

namespace Submission.CField.NIndex

open IsDedekindDomain NumberField
open Submission.CField.Ideles
open Submission.CField.Recip

noncomputable section

universe u

variable (K L : Type u) [Field K] [Field L]
  [NumberField K] [NumberField L] [Algebra K L]
  [FiniteDimensional K L]

private abbrev IK := IdeleGroup (RingOfIntegers K) K
private abbrev CK := IdeleClassGroup (RingOfIntegers K) K

/-- Quotienting `C_K` by the range of its canonical norm is the same as
quotienting `I_K` by the product of principal idèles and idèle norms. -/
noncomputable def ideleClassPrincipal :
    (CK K ⧸
        (canonicalIdeleNorm (K := K) (L := L)).range) ≃*
      (IK K ⧸
        (principalIdeles (RingOfIntegers K) K ⊔
          ideleNormSubgroup (K := K) (L := L))) :=
  (QuotientGroup.quotientMulEquivOfEq
      (canonical_idele_range (K := K) (L := L))).trans
    (ideleClassEquiv
      (K := K) (ideleNormSubgroup (K := K) (L := L)))

/-- Consequently the cardinality of the idèle-class norm quotient is the
literal subgroup index occurring in Corollary VII.4.4. -/
theorem nat_principal_index :
    Nat.card
        (CK K ⧸
          (canonicalIdeleNorm (K := K) (L := L)).range) =
      (principalIdeles (RingOfIntegers K) K ⊔
        ideleNormSubgroup (K := K) (L := L)).index := by
  rw [Subgroup.index_eq_card]
  exact Nat.card_congr
    (ideleClassPrincipal K L).toEquiv

end

end Submission.CField.NIndex
