import Mathlib.Data.Nat.PrimeFin
import Submission.ClassField.CohomologyOps.NatCardNsmul
import Submission.ClassField.CyclicIdeles.IdeleClassRep

/-!
# Chapter VII, Section 5, Lemma 5.3: finiteness from Sylow restrictions

The simultaneous restriction map from positive-degree cohomology to the
product of its restrictions at the Sylow subgroups is injective.  Only the
prime divisors of the order of the group are needed, so the product is
finite.  This proves the abstract finiteness bridge used in the source
reduction for Lemma 5.3.
-/

namespace Submission.CField.CIdeles

open CategoryTheory Representation
open Submission.CField.COps

noncomputable section

universe u

/-- Finiteness of `H²` is detected by restriction to all Sylow subgroups. -/
theorem hFinitenessBridge : HFinitenessBridge.{u} := by
  intro G _ _ A hfinite
  let I := {p : ℕ // p ∈ (Nat.card G).primeFactors}
  let primeFact (i : I) : Fact i.1.Prime :=
    ⟨Nat.prime_of_mem_primeFactors i.2⟩
  let P (i : I) : Sylow i.1 G := by
    letI : Fact i.1.Prime := primeFact i
    exact Classical.choice Sylow.nonempty
  let T (i : I) :=
    groupCohomology.H2
      (Rep.res ((P i : Sylow i.1 G) : Subgroup G).subtype A)
  letI (i : I) : Finite (T i) := by
    dsimp only [T]
    letI : Fact i.1.Prime := primeFact i
    exact hfinite i.1 (P i)
  let f : groupCohomology.H2 A → ∀ i : I, T i :=
    fun x i ↦ restriction A ((P i : Sylow i.1 G) : Subgroup G) 2 x
  have hf : Function.Injective f := by
    intro x y hxy
    suffices x - y = 0 by exact sub_eq_zero.mp this
    let z : groupCohomology.H2 A := x - y
    have horderCard : addOrderOf z ∣ Nat.card G :=
      addOrderOf_dvd_iff_nsmul_eq_zero.mpr
        (nat_nsmul_cohomology A 2 (by omega) z)
    by_contra hz
    have horder : addOrderOf z ≠ 1 := by
      simpa [z] using hz
    obtain ⟨p, hp, hpOrder⟩ := Nat.exists_prime_and_dvd horder
    have hpCard : p ∣ Nat.card G := hpOrder.trans horderCard
    have hpMem : p ∈ (Nat.card G).primeFactors :=
      hp.mem_primeFactors hpCard Nat.card_pos.ne'
    let i : I := ⟨p, hpMem⟩
    letI : Fact p.Prime := ⟨hp⟩
    let Q : Sylow p G := P i
    have hrestricted : restriction A (Q : Subgroup G) 2 z = 0 := by
      have hi := congrFun hxy i
      change restriction A (Q : Subgroup G) 2 x =
        restriction A (Q : Subgroup G) 2 y at hi
      simp [z, hi]
    have htransfer := congrArg (fun g ↦ g z)
      (restriction_corestriction_degrees A (Q : Subgroup G) 2)
    have hindex : (Q : Subgroup G).index • z = 0 := by
      simpa [hrestricted] using htransfer.symm
    have horderIndex : addOrderOf z ∣ (Q : Subgroup G).index :=
      addOrderOf_dvd_iff_nsmul_eq_zero.mpr hindex
    exact Q.not_dvd_index (hpOrder.trans horderIndex)
  exact Finite.of_injective f hf

end

end Submission.CField.CIdeles
