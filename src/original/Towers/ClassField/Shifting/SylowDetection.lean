import Mathlib.GroupTheory.Sylow
import Towers.ClassField.CohomologyOps.AllDegrees

/-!
# Milne, Class Field Theory, Theorem II.3.10: Sylow detection

This file formalizes the final Sylow-subgroup step in Milne's proof.  The
restriction map used here is the Shapiro-defined restriction from Proposition
II.1.30.  Its composite with corestriction is multiplication by the subgroup
index, which is all the detection argument needs.
-/

namespace Towers.CField.Shifting

open CategoryTheory Rep

noncomputable section

universe u

variable {k G : Type u} [CommRing k] [Group G] [Fintype G]

set_option linter.unusedFintypeInType false in
/-- A positive-degree cohomology class is zero if its Shapiro restriction to
every Sylow subgroup is zero.  Equivalently, vanishing on all Sylow subgroups
detects vanishing on the finite group. -/
theorem subsingleton_group_sylow
    (A : Rep k G) (n : ℕ)
    (hSylow : ∀ (p : ℕ) [Fact p.Prime] (P : Sylow p G),
      Subsingleton (groupCohomology (res P.1.subtype A) n)) :
    Subsingleton (groupCohomology A n) := by
  constructor
  intro x y
  by_contra hxy
  have hsub : x - y ≠ 0 := sub_ne_zero.mpr hxy
  have horder : addOrderOf (x - y) ≠ 1 := by
    simpa using hsub
  obtain ⟨p, hp, hpOrder⟩ := Nat.exists_prime_and_dvd horder
  letI : Fact p.Prime := ⟨hp⟩
  let P : Sylow p G := Classical.choice Sylow.nonempty
  letI : Subsingleton (groupCohomology (res P.1.subtype A) n) :=
    hSylow p P
  have htransfer :=
    COps.shapiro_restriction_corestriction A P.1 n
  have hrestricted :
      COps.shapiroRestriction A P.1 n (x - y) = 0 :=
    Subsingleton.elim _ _
  have hindex : P.1.index • (x - y) = 0 := by
    have happ := congrArg (fun f ↦ f (x - y)) htransfer
    simpa [hrestricted] using happ.symm
  have hOrderIndex : addOrderOf (x - y) ∣ P.1.index :=
    addOrderOf_dvd_iff_nsmul_eq_zero.mpr hindex
  exact P.not_dvd_index (hpOrder.trans hOrderIndex)

end

end Towers.CField.Shifting
