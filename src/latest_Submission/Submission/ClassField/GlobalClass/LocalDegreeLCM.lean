import Mathlib.GroupTheory.Exponent
import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# Chapter VIII, Section 4: least common multiples of local degrees

Milne's Lemma 4.1 identifies the degree of a cyclic extension with the least common multiple of
its local degrees.  The arithmetic input is surjectivity of the Artin map (or, equivalently for
this purpose, that the relevant Frobenius elements exhaust the Galois group).  The theorem below
formalizes the resulting finite-group argument.

Example 4.5 uses the complementary observation that a cyclic subgroup of a group killed by two
has order one or two.  This is the group-theoretic reason that the biquadratic example has no
completion of degree four; identifying the decomposition groups for
`Q(sqrt 13, sqrt 17) / Q` still requires the project's missing completion/decomposition-group
interface.
-/

namespace Submission.CField.GClass

open scoped BigOperators

/-- **Lemma 4.1, finite-group core.** If a finite family exhausts a finite cyclic group, the least
common multiple of the orders of its members is the order of the group.  Applied to Frobenius
elements, their orders are the unramified local degrees. -/
theorem lcm_order_card
    {ι G : Type*} [Fintype ι] [Group G] [Fintype G] [IsCyclic G]
    (frobenius : ι → G) (hfr : Function.Surjective frobenius) :
    Finset.univ.lcm (fun i ↦ orderOf (frobenius i)) = Fintype.card G := by
  apply Nat.dvd_antisymm
  · apply Finset.lcm_dvd
    intro i _
    exact orderOf_dvd_card
  · obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := G)
    obtain ⟨i, rfl⟩ := hfr g
    rw [← Nat.card_eq_fintype_card, ← hg]
    exact Finset.dvd_lcm (s := Finset.univ)
      (f := fun j ↦ orderOf (frobenius j)) (Finset.mem_univ i)

/-- If a family generates a finite cyclic group, every common multiple of
the orders of its members is a multiple of the group order.  Unlike
`lcm_order_card`, this formulation does not require the family
to be finite or to contain every group element; it is the exact group-theory
input supplied by Proposition VII.4.7. -/
theorem card_dvd_top
    {ι G : Type*} [Group G] [Finite G] [IsCyclic G]
    (frobenius : ι → G)
    (hgenerate : Subgroup.closure (Set.range frobenius) = ⊤)
    (m : ℕ) (hm : ∀ i, orderOf (frobenius i) ∣ m) :
    Nat.card G ∣ m := by
  letI : CommGroup G := IsCyclic.commGroup
  rw [← IsCyclic.exponent_eq_card]
  rw [Monoid.exponent_dvd_iff_forall_pow_eq_one]
  let H : Subgroup G :=
    { carrier := {g | g ^ m = 1}
      one_mem' := one_pow m
      mul_mem' := by
        intro a b ha hb
        change (a * b) ^ m = 1
        change a ^ m = 1 at ha
        change b ^ m = 1 at hb
        rw [mul_pow, ha, hb, one_mul]
      inv_mem' := by
        intro a ha
        change a⁻¹ ^ m = 1
        change a ^ m = 1 at ha
        rw [inv_pow, ha, inv_one] }
  intro g
  have htop : (⊤ : Subgroup G) ≤ H := by
    rw [← hgenerate]
    apply (Subgroup.closure_le H).mpr
    rintro _ ⟨i, rfl⟩
    exact (orderOf_dvd_iff_pow_eq_one.mp (hm i) : frobenius i ^ m = 1)
  exact htop (Subgroup.mem_top g)

/-- The lcm of the orders of all elements of a finite cyclic group is its cardinality. -/
theorem lcm_all_orders
    (G : Type*) [Group G] [Fintype G] [IsCyclic G] :
    Finset.univ.lcm (fun g : G ↦ orderOf g) = Fintype.card G :=
  lcm_order_card (fun g : G ↦ g) Function.surjective_id

/-- **Example 4.5, finite-group core.** A cyclic subgroup of a group whose elements are killed by
two has order one or two. -/
theorem cyclic_or_two
    {G : Type*} [Group G] [Finite G]
    (hG : ∀ g : G, g ^ 2 = 1) (H : Subgroup G) [IsCyclic H] :
    Nat.card H = 1 ∨ Nat.card H = 2 := by
  rw [← IsCyclic.exponent_eq_card]
  apply (Nat.dvd_prime Nat.prime_two).mp
  rw [Monoid.exponent_dvd_iff_forall_pow_eq_one]
  exact fun h ↦ Subtype.ext (hG h)

/-- In particular, the order of such a cyclic subgroup is at most two. -/
theorem cyclic_card_two
    {G : Type*} [Group G] [Finite G]
    (hG : ∀ g : G, g ^ 2 = 1) (H : Subgroup G) [IsCyclic H] :
    Nat.card H ≤ 2 := by
  rcases cyclic_or_two hG H with h | h <;> omega

end Submission.CField.GClass
