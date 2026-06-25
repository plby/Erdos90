import Mathlib.Algebra.DirectSum.Basic
import Towers.ClassField.LocalBrauer.DivisionAlgebraInvariant

/-!
# Direct-sum helpers for the absolute kernel argument in Theorem VIII.4.2

This file contains the algebraic part of the tailored finite-extension
argument.  A finite-support family of local invariants has a positive common
annihilator, and a family lying coordinatewise in specified subgroups lifts
uniquely to the direct sum of those subgroups.
-/

namespace Towers.CField.BLoc

open Towers.CField.LBrauer

noncomputable section

universe u v

/-- Every element of `Q/Z` has positive finite additive order. -/
theorem local_invariant_pos (x : LocalInvariant) :
    0 < addOrderOf x := by
  refine QuotientAddGroup.induction_on x ?_
  intro q
  have horder : addOrderOf (↑q : LocalInvariant) = q.den := by
    simpa using
      (AddCircle.addOrderOf_coe_rat (p := (1 : ℚ)) (q := q))
  rw [horder]
  exact q.den_pos

/-- The product of the coordinate orders is a common annihilator for a
finite-support family in `Q/Z`. -/
noncomputable def directInvariantAnnihilator
    {ι : Type u} (x : DirectSum ι (fun _ => LocalInvariant)) : ℕ := by
  classical
  exact ∏ i ∈ x.support, addOrderOf (x i)

/-- The common annihilator is positive. -/
theorem direct_annihilator_pos
    {ι : Type u} (x : DirectSum ι (fun _ => LocalInvariant)) :
    0 < directInvariantAnnihilator x := by
  classical
  unfold directInvariantAnnihilator
  exact Finset.prod_pos fun i _ => local_invariant_pos (x i)

/-- The common annihilator kills every coordinate, including coordinates
outside the support. -/
theorem direct_annihilator_nsmul
    {ι : Type u} (x : DirectSum ι (fun _ => LocalInvariant)) (i : ι) :
    directInvariantAnnihilator x • x i = 0 := by
  classical
  by_cases hi : i ∈ x.support
  · rw [← addOrderOf_dvd_iff_nsmul_eq_zero]
    exact Finset.dvd_prod_of_mem (fun j => addOrderOf (x j)) hi
  · have hxi : x i = 0 := by
      simpa only [DFinsupp.mem_support_toFun, not_ne_iff] using hi
    rw [hxi, smul_zero]

/-- A direct-sum family whose coordinates all lie in specified subgroups
lifts coordinatewise to the direct sum of those subgroups. -/
theorem direct_subtype_lift
    {ι : Type u} {A : ι → Type v} [∀ i, AddCommGroup (A i)]
    (S : ∀ i, AddSubgroup (A i))
    (x : DirectSum ι A)
    (hx : ∀ i, x i ∈ S i) :
    ∃ y : DirectSum ι (fun i => S i),
      DirectSum.map (fun i => (S i).subtype) y = x := by
  classical
  let y : DirectSum ι (fun i => S i) :=
    DFinsupp.mk x.support (fun i => ⟨x i, hx i⟩)
  refine ⟨y, ?_⟩
  ext i
  simp only [DirectSum.map_apply, AddSubgroup.coe_subtype]
  by_cases hi : i ∈ x.support
  · simp [y, DFinsupp.mk_apply, hi]
  · have hxi : x i = 0 := by
      simpa only [DFinsupp.mem_support_toFun, not_ne_iff] using hi
    simp [y, DFinsupp.mk_apply, hi, hxi]

/-- The direct-sum map induced by subgroup inclusions is injective.  Thus the
coordinatewise lift supplied above is unique. -/
theorem direct_subtype_injective
    {ι : Type u} {A : ι → Type v} [∀ i, AddCommGroup (A i)]
    (S : ∀ i, AddSubgroup (A i)) :
    Function.Injective (DirectSum.map (fun i => (S i).subtype)) := by
  rw [DirectSum.map_injective]
  exact fun _ x y h => Subtype.ext h

end

end Towers.CField.BLoc
