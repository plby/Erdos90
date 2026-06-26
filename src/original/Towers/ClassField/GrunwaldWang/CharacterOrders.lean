import Mathlib.GroupTheory.OrderOfElement

/-!
# Chapter VIII, Section 2: orders of local characters

Theorem 2.4 (Grunwald--Wang) extends finitely many continuous local characters
to an idele-class character, with a possible exceptional factor at powers of
two.  Continuous character groups and the required extension theorem are not
currently available in the project.

The order constraints in its statement are ordinary group theory: restriction
cannot increase order, and the order of a finite tuple of local characters is
the least common multiple of their orders.  These facts also underlie
Corollary 2.5.
-/

namespace Towers.CField.GWang

/-- Restricting a character along any homomorphism cannot increase its order.
This is the algebraic necessity behind each `n_v ∣ order(chi)`. -/
theorem order_restriction_dvd
    {G H : Type*} [Monoid G] [Monoid H]
    (restriction : G →* H) (chi : G) :
    orderOf (restriction chi) ∣ orderOf chi :=
  orderOf_map_dvd restriction chi

/-- The order of a finite family of local characters is the least common
multiple of their individual orders. -/
theorem order_character_family
    {ι : Type*} [Fintype ι] (A : ι → Type*) [∀ i, Monoid (A i)]
    (chi : ∀ i, A i) :
    orderOf chi = Finset.univ.lcm (fun i ↦ orderOf (chi i)) :=
  Pi.orderOf chi

/-- In particular, the order of every local component divides the lcm/order of
the complete family. -/
theorem character_dvd_family
    {ι : Type*} (A : ι → Type*) [∀ i, Monoid (A i)]
    (chi : ∀ i, A i) (v : ι) :
    orderOf (chi v) ∣ orderOf chi :=
  orderOf_apply_dvd_orderOf v

end Towers.CField.GWang
