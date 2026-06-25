import Towers.ClassField.CohomologyOps.AllDegrees
import Mathlib.Algebra.Group.Subgroup.Finite
import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# Milne, Class Field Theory, Theorem II.3.11: restriction of the generator

The first step in Tate's proof is a finite cyclic-group argument.  If
corestriction after restriction sends a generator to its index multiple,
then the restricted class is again a generator.
-/

namespace Towers.CField.Shifting

open AddSubgroup

variable {A B : Type*} [AddCommGroup A] [AddCommGroup B] [Finite A] [Finite B]

/-- The order argument at the start of Theorem II.3.11.  Here `d` represents
the subgroup index, `A` the ambient `H²`, and `B` the subgroup `H²`. -/
theorem generator_corestriction_restriction
    (res : A →+ B) (cor : B →+ A) (d : ℕ) (hd : 0 < d)
    (hcard : Nat.card A = d * Nat.card B)
    (gamma : A) (hgamma : ∀ x : A, x ∈ zmultiples gamma)
    (hcorres : cor (res gamma) = d • gamma) :
    ∀ x : B, x ∈ zmultiples (res gamma) := by
  have hgammaOrder : addOrderOf gamma = Nat.card A :=
    addOrderOf_eq_card_of_forall_mem_zmultiples hgamma
  have hmultipleOrder : addOrderOf (d • gamma) = Nat.card B := by
    rw [addOrderOf_nsmul, hgammaOrder, hcard]
    simp [hd.ne']
  have hcard_dvd : Nat.card B ∣ addOrderOf (res gamma) := by
    rw [← hmultipleOrder, ← hcorres]
    exact addOrderOf_map_dvd cor (res gamma)
  have horder : addOrderOf (res gamma) = Nat.card B := by
    apply le_antisymm addOrderOf_le_card
    exact Nat.le_of_dvd (addOrderOf_pos (res gamma)) hcard_dvd
  have htop : zmultiples (res gamma) = ⊤ := by
    apply (card_eq_iff_eq_top _).mp
    rw [Nat.card_zmultiples, horder]
  intro x
  simp [htop]

/-- A homomorphism between cyclic additive groups is bijective if it sends a
generator to a generator and the source generator is annihilated by the order
of the target.  This is the finite-order argument used for the splitting
boundary in Theorem II.3.11. -/
theorem bijective_maps_generator
    {A B : Type*} [AddCommGroup A] [AddCommGroup B] [Finite B]
    (f : A →+ B) (a : A) (b : B)
    (ha : ∀ x : A, x ∈ zmultiples a)
    (hb : ∀ x : B, x ∈ zmultiples b)
    (hmap : f a = b) (hann : Nat.card B • a = 0) :
    Function.Bijective f := by
  have hbOrder : addOrderOf b = Nat.card B :=
    addOrderOf_eq_card_of_forall_mem_zmultiples hb
  constructor
  · intro x y hxy
    obtain ⟨z, hz⟩ := ha (x - y)
    change z • a = x - y at hz
    have hzb : z • b = 0 := by
      rw [← hmap, ← map_zsmul, hz, map_sub, hxy, sub_self]
    have hdvd : (Nat.card B : ℤ) ∣ z := by
      rw [← hbOrder]
      exact (addOrderOf_dvd_iff_zsmul_eq_zero).2 hzb
    obtain ⟨q, rfl⟩ := hdvd
    have hannz : (Nat.card B : ℤ) • a = 0 := by simpa using hann
    have hzero : ((Nat.card B : ℤ) * q) • a = 0 := by
      rw [mul_comm, mul_zsmul, hannz, smul_zero]
    exact sub_eq_zero.mp (hz.symm.trans hzero)
  · intro y
    obtain ⟨z, hz⟩ := hb y
    change z • b = y at hz
    refine ⟨z • a, ?_⟩
    rw [map_zsmul, hmap, hz]

/-- A surjective homomorphism from a cyclic group annihilated by the target's
order is automa injective when the target has a generator of that
order.  This version is suited to the long-exact-sequence proof of Theorem
II.3.11, where surjectivity of the boundary comes from exactness. -/
theorem bijective_surjective_annihilated
    {A B : Type*} [AddCommGroup A] [AddCommGroup B] [Finite B]
    (f : A →+ B) (a : A) (b : B)
    (ha : ∀ x : A, x ∈ zmultiples a)
    (hb : ∀ x : B, x ∈ zmultiples b)
    (hann : Nat.card B • a = 0) (hsurj : Function.Surjective f) :
    Function.Bijective f := by
  have hbOrder : addOrderOf b = Nat.card B :=
    addOrderOf_eq_card_of_forall_mem_zmultiples hb
  refine ⟨?_, hsurj⟩
  obtain ⟨c, hc⟩ := hsurj b
  obtain ⟨z, hz⟩ := ha c
  change z • a = c at hz
  intro x y hxy
  obtain ⟨w, hw⟩ := ha (x - y)
  change w • a = x - y at hw
  have hwfa : w • f a = 0 := by
    rw [← map_zsmul, hw, map_sub, hxy, sub_self]
  have hwb : w • b = 0 := by
    rw [← hc, ← hz, map_zsmul, smul_smul, mul_comm, ← smul_smul, hwfa, smul_zero]
  have hdvd : (Nat.card B : ℤ) ∣ w := by
    rw [← hbOrder]
    exact (addOrderOf_dvd_iff_zsmul_eq_zero).2 hwb
  obtain ⟨q, rfl⟩ := hdvd
  have hannz : (Nat.card B : ℤ) • a = 0 := by simpa using hann
  have hzero : ((Nat.card B : ℤ) * q) • a = 0 := by
    rw [mul_comm, mul_zsmul, hannz, smul_zero]
  exact sub_eq_zero.mp (hw.symm.trans hzero)

end Towers.CField.Shifting
