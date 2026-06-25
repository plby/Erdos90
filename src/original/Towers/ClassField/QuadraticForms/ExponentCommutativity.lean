import Mathlib.Algebra.Group.Subgroup.Basic

/-!
# Appendix exercise A-1: inertia generators and genus theory

The arithmetic statements in A-1 require two interfaces not presently available
in Mathlib or the Milne layer: generation of an absolute Galois group by inertia
groups, and the assertion that `Q` has no nontrivial everywhere-unramified finite
extension.  The narrow class-field construction in part (b) is likewise beyond
the current class-group API.

The delicate finite-group step in Milne's solution is independent of that
arithmetic infrastructure.  Two inertia generators have square one, their
product lies in an elementary abelian `2`-subgroup, and hence their product also
has square one.  The lemmas below record exactly the resulting commutativity.
-/

namespace Towers.CField.QForms.ECommut

variable {G : Type*} [Group G]

/-- If two elements and their product are involutions, then the two elements
commute.  This is the group calculation at the heart of Exercise A-1(b). -/
theorem commute_sq_mul {sigma tau : G}
    (hsigma : sigma ^ 2 = 1) (htau : tau ^ 2 = 1)
    (hprod : (sigma * tau) ^ 2 = 1) : Commute sigma tau := by
  rw [pow_two] at hsigma htau hprod
  have hsigma_inv : sigma⁻¹ = sigma := inv_eq_of_mul_eq_one_right hsigma
  have htau_inv : tau⁻¹ = tau := inv_eq_of_mul_eq_one_right htau
  have hprod_inv : (sigma * tau)⁻¹ = sigma * tau :=
    inv_eq_of_mul_eq_one_right hprod
  simpa only [mul_inv_rev, hsigma_inv, htau_inv] using hprod_inv.symm

/-- The form used in the genus-theory argument: the product of the two
involutions belongs to a subgroup of exponent two. -/
theorem commute_exponent_two (N : Subgroup G) {sigma tau : G}
    (hsigma : sigma ^ 2 = 1) (htau : tau ^ 2 = 1)
    (hN : ∀ x : G, x ∈ N → x ^ 2 = 1) (hprod : sigma * tau ∈ N) :
    Commute sigma tau :=
  commute_sq_mul hsigma htau (hN _ hprod)

end Towers.CField.QForms.ECommut
