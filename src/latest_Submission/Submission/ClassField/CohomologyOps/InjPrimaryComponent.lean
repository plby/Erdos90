import Mathlib.GroupTheory.Sylow
import Mathlib.GroupTheory.Torsion
import Submission.ClassField.CohomologyOps.RestrictionCompatibility

/-!
# Milne, Class Field Theory, Corollary II.1.33

Restriction from a finite group to a Sylow `p`-subgroup is injective on the `p`-primary
component of group cohomology.  The proof is the transfer argument immediately following
Proposition II.1.30 in Milne.
-/

namespace Submission.CField.COps

open CategoryTheory Rep

universe u

variable {k G : Type u} [CommRing k] [Group G] [Finite G]

noncomputable section

/-- **Corollary II.1.33 (statement).** Restriction to a Sylow `p`-subgroup is injective on the
`p`-primary component of `H^r(G,A)`. -/
def ShapiroInjPrimary
    (A : Rep k G) (p : ℕ) [Fact p.Prime] (P : Sylow p G) (r : ℕ) :
    Prop :=
    Set.InjOn (restriction A P.1 r)
      (AddCommGroup.primaryComponent (groupCohomology A r) p)

/-- The Shapiro model of restriction is injective on the `p`-primary component.  This is the
entire transfer-and-Sylow argument in Milne's proof of Corollary II.1.33. -/
theorem shapiro_inj_primary
    (A : Rep k G) (p : ℕ) [Fact p.Prime] (P : Sylow p G) (r : ℕ) :
    Set.InjOn (shapiroRestriction A P.1 r)
      (AddCommGroup.primaryComponent (groupCohomology A r) p) := by
  intro x hx y hy hxy
  suffices x - y = 0 by exact sub_eq_zero.mp this
  let z : groupCohomology A r := x - y
  have hzprimary : z ∈ AddCommGroup.primaryComponent (groupCohomology A r) p :=
    (AddCommGroup.primaryComponent (groupCohomology A r) p).sub_mem hx hy
  have hreszero : shapiroRestriction A P.1 r z = 0 := by
    simp only [z, map_sub, hxy, sub_self]
  have htransfer := congrArg (fun f ↦ f z)
    (shapiro_restriction_corestriction A P.1 r)
  have hindex : P.1.index • z = 0 := by
    simpa [hreszero] using htransfer.symm
  have horderIndex : addOrderOf z ∣ P.1.index :=
    addOrderOf_dvd_iff_nsmul_eq_zero.mpr hindex
  obtain ⟨e, he⟩ := hzprimary
  by_cases hz : z = 0
  · exact hz
  have horderPow : addOrderOf z ∣ p ^ e :=
    addOrderOf_dvd_iff_nsmul_eq_zero.mpr he
  obtain ⟨k, _hk, horder⟩ :=
    (Nat.dvd_prime_pow (Fact.out : Nat.Prime p)).mp horderPow
  have hkzero : k ≠ 0 := by
    intro hk
    apply hz
    apply AddMonoid.addOrderOf_eq_one_iff.mp
    simp [horder, hk]
  have hpOrder : p ∣ addOrderOf z := by
    rw [horder]
    exact dvd_pow (dvd_refl p) hkzero
  exact (P.not_dvd_index (hpOrder.trans horderIndex)).elim

/-- The final formal implication in Corollary II.1.33: once cochain restriction is identified
with the Shapiro model, the book's stated restriction map is injective on the primary
component. -/
theorem restriction_inj_primary
    (A : Rep k G) (p : ℕ) [Fact p.Prime] (P : Sylow p G) (r : ℕ)
    (hcompat : restriction A P.1 r = shapiroRestriction A P.1 r) :
    ShapiroInjPrimary A p P r := by
  rw [ShapiroInjPrimary, hcompat]
  exact shapiro_inj_primary A p P r

/-- **Corollary II.1.33.** Restriction to a Sylow `p`-subgroup is injective
on the `p`-primary component of group cohomology. -/
theorem restriction_inj_component
    (A : Rep k G) (p : ℕ) [Fact p.Prime] (P : Sylow p G) (r : ℕ) :
    ShapiroInjPrimary A p P r :=
  restriction_inj_primary A p P r
    (restriction_shapiro A P.1 r)

end

end Submission.CField.COps
