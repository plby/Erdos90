import Submission.ClassField.Shifting.GroupPeriodicityOdd
import Submission.ClassField.LocalReciprocity.TateZeroQuotient
import Submission.ClassField.BrauerLocalization.Relative2Comparison

/-!
# Cyclic periodicity on the field side of Lemma VII.8.5

For a chosen generator of a finite cyclic Galois group, two-periodicity
gives the quotient map

`Kˣ → Kˣ / Nm(Lˣ) ≃ H²(Gal(L/K), Lˣ) ≃ Br(L/K)`.

This is the unconditional surjectivity input behind the converse direction
of Lemma VII.8.5.  Identifying this map with cup product by the boundary of
the corresponding injective character is the cup-periodicity comparison.
-/

namespace Submission.CField.RExist

open CategoryTheory Representation
open Submission.CField.LFTheory
open Submission.CField.Shifting
open Submission.CField.LRecip
open Submission.CField.BGroups
open Submission.CField.BLoc

noncomputable section

variable (K L : Type) [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

attribute [local instance] Units.mulDistribMulActionRight

set_option synthInstance.maxHeartbeats 200000 in
-- The Tate-zero quotient carries a deeply nested representation-module instance.
/-- The field-to-relative-Brauer map furnished by cyclic two-periodicity,
for a specified generator of `Gal(L/K)`. -/
noncomputable def cyclicBrauerPeriodicity
    [IsCyclic Gal(L/K)]
    (sigma : Gal(L/K))
    (hSigma : ∀ tau : Gal(L/K), tau ∈ Subgroup.zpowers sigma) :
    Additive Kˣ →+ Additive (relativeBrauerGroup K L) := by
  letI : CommGroup Gal(L/K) := IsCyclic.commGroup
  let q : Additive Kˣ →+ Additive (Kˣ ⧸ normSubgroup K L) :=
    MonoidHom.toAdditive (QuotientGroup.mk' (normSubgroup K L))
  exact (relativeBrauerCohomology K L).symm.toAddMonoidHom.comp
    ((tateCohomologyTwo
      (Rep.ofAlgebraAutOnUnits K L) sigma hSigma).toAddMonoidHom.comp
      ((galoisTateQuotient K L).symm.toAddMonoidHom.comp q))

set_option synthInstance.maxHeartbeats 200000 in
-- The proof elaborates the same Tate-zero quotient and its chain of equivalences.
/-- Cyclic two-periodicity is onto every relative Brauer class. -/
theorem cyclic_periodicity_surjective
    [IsCyclic Gal(L/K)]
    (sigma : Gal(L/K))
    (hSigma : ∀ tau : Gal(L/K), tau ∈ Subgroup.zpowers sigma) :
    Function.Surjective
      (cyclicBrauerPeriodicity K L sigma hSigma) := by
  letI : CommGroup Gal(L/K) := IsCyclic.commGroup
  exact (relativeBrauerCohomology K L).symm.surjective.comp
    ((tateCohomologyTwo
      (Rep.ofAlgebraAutOnUnits K L) sigma hSigma).surjective.comp
      ((galoisTateQuotient K L).symm.surjective.comp
        (QuotientGroup.mk'_surjective (normSubgroup K L))))

end

end Submission.CField.RExist
