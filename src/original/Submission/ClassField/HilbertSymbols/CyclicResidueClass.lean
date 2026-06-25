import Submission.ClassField.LocalReciprocity.TateZeroQuotient
import Submission.ClassField.HilbertSymbols.NormCriterion

/-!
# Milne, Class Field Theory, Section III.4, Step 1

For a finite cyclic Galois extension, a chosen generator identifies Tate
degree zero with ordinary degree two.  Composing this periodicity map with
the canonical description of Tate degree zero as base-field units modulo
norms gives Milne's class `(chi,b)'`.  Its vanishing is exactly the norm
condition.
-/

namespace Submission.CField.HSymbol

open Representation
open Submission.CField.LFTheory
open Submission.CField.Shifting
open Submission.CField.LRecip

noncomputable section

variable (K L : Type) [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L] [IsCyclic Gal(L/K)]

attribute [local instance] Units.mulDistribMulActionRight

/-- Milne's class `(chi,b)'` from Step 1, with `chi` represented by the
choice of the cyclic generator `sigma`.  The first equivalence regards the
class of `b` modulo field norms as Tate degree zero; the second is cyclic
two-periodicity normalized by `sigma`. -/
noncomputable def cyclicResidueClass
    (sigma : Gal(L/K))
    (hSigma : ∀ tau : Gal(L/K), tau ∈ Subgroup.zpowers sigma)
    (b : Kˣ) :
    letI : CommGroup Gal(L/K) := IsCyclic.commGroup
    groupCohomology.H2
      (Rep.ofMulDistribMulAction Gal(L/K) Lˣ) := by
  letI : CommGroup Gal(L/K) := IsCyclic.commGroup
  let hSigma' : ∀ tau : Gal(L/K), tau ∈ Subgroup.zpowers sigma := by
    simpa [IsCyclic.commGroup] using hSigma
  let t : tateCohomologyZero
      (Rep.ofMulDistribMulAction Gal(L/K) Lˣ) := by
    simpa [IsCyclic.commGroup] using
      ((galoisTateQuotient K L).symm
        (Additive.ofMul
          (QuotientGroup.mk' (normSubgroup K L) b)))
  exact tateCohomologyTwo
    (Rep.ofMulDistribMulAction Gal(L/K) Lˣ) sigma hSigma' t

set_option maxHeartbeats 2000000 in
-- The cyclic commutative-group instance creates a deep quotient-module telescope.
set_option synthInstance.maxHeartbeats 200000 in
/-- **Section III.4, Step 1.**  For a cyclic extension, Milne's degree-two
class attached to `b` vanishes if and only if `b` is a norm from `Lˣ`.
There are no local-field hypotheses in this statement, as in the source. -/
theorem cyclic_residue_zero
    (sigma : Gal(L/K))
    (hSigma : ∀ tau : Gal(L/K), tau ∈ Subgroup.zpowers sigma)
    (b : Kˣ) :
    letI : CommGroup Gal(L/K) := IsCyclic.commGroup
    cyclicResidueClass K L sigma hSigma b = 0 ↔
      b ∈ normSubgroup K L := by
  letI : CommGroup Gal(L/K) := IsCyclic.commGroup
  let hSigma' : ∀ tau : Gal(L/K), tau ∈ Subgroup.zpowers sigma := by
    simpa [IsCyclic.commGroup] using hSigma
  let e := tateCohomologyTwo
    (Rep.ofMulDistribMulAction Gal(L/K) Lˣ) sigma hSigma'
  let ht : tateCohomologyZero
      (Rep.ofMulDistribMulAction Gal(L/K) Lˣ) := by
    simpa [IsCyclic.commGroup] using
      ((galoisTateQuotient K L).symm
        (Additive.ofMul
          (QuotientGroup.mk' (normSubgroup K L) b)))
  have hclass : cyclicResidueClass K L sigma hSigma b = e ht := by
    simp [cyclicResidueClass, e, ht, IsCyclic.commGroup]
  rw [hclass]
  constructor
  · intro h
    have ht0 : ht = 0 :=
      e.injective (h.trans e.map_zero.symm)
    have htOrig0 :
        (galoisTateQuotient K L).symm
            (Additive.ofMul
              (QuotientGroup.mk' (normSubgroup K L) b)) = 0 := by
      simpa [ht, IsCyclic.commGroup] using ht0
    have hq0 : QuotientGroup.mk' (normSubgroup K L) b = 1 := by
      let q := QuotientGroup.mk' (normSubgroup K L) b
      let f := (galoisTateQuotient K L).symm
      have hAdd : Additive.ofMul q = 0 :=
        f.injective (htOrig0.trans f.map_zero.symm)
      exact congrArg Additive.toMul hAdd
    exact (QuotientGroup.eq_one_iff b).mp hq0
  · intro hb
    have hq0 : QuotientGroup.mk' (normSubgroup K L) b = 1 :=
      (QuotientGroup.eq_one_iff b).mpr hb
    have htOrig0 :
        (galoisTateQuotient K L).symm
            (Additive.ofMul
            (QuotientGroup.mk' (normSubgroup K L) b)) = 0 := by
      let q := QuotientGroup.mk' (normSubgroup K L) b
      let f := (galoisTateQuotient K L).symm
      have hAdd : Additive.ofMul q = 0 := by
        apply Additive.toMul.injective
        exact hq0
      calc
        f (Additive.ofMul q) = f 0 := congrArg f hAdd
        _ = 0 := f.map_zero
    have ht0 : ht = 0 := by
      simpa [ht, IsCyclic.commGroup] using htOrig0
    exact (congrArg e ht0).trans e.map_zero

end

end Submission.CField.HSymbol
