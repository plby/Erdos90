import Submission.ClassField.FormalGroups.LubinApproximationLimit
import Submission.ClassField.FormalGroups.LubinIntertwinerPredicate

/-!
# Class Field Theory, Chapter I, Lemma 2.11: existence

Milne's successive homogeneous approximants have errors of arbitrarily high
order.  Their stable diagonal is therefore an exact intertwiner with the
prescribed linear form.
-/

namespace Submission.CField.FGroups

open MvPowerSeries

noncomputable section

namespace LTApprox

variable {R sigma : Type*} [CommRing R] [IsDomain R] [IsLocalRing R]
    [Fintype sigma]

variable (pi : R) (hpi0 : pi ≠ 0) (hpi : ¬ IsUnit pi)
    (hfield : IsField (R ⧸ Ideal.span {pi}))
    [Fintype (R ⧸ Ideal.span {pi})]
    (f g : PowerSeries R)
    (hf : LubinSeries pi
      (Fintype.card (R ⧸ Ideal.span {pi})) f)
    (hg : LubinSeries pi
      (Fintype.card (R ⧸ Ideal.span {pi})) g)

/-- The stable diagonal of Milne's approximants is the canonical solution
of the existence half of Lemma 2.11. -/
theorem lubin_intertwiner_limit (a : sigma -> R) :
    LIntert f g a
      (limitSeries pi hpi0 hpi hfield f g hf hg a) := by
  refine ⟨limit_constant_coeff pi hpi0 hpi hfield f g hf hg a,
    homogeneous_component_limit pi hpi0 hpi hfield f g hf hg a,
    ?_⟩
  apply error_approximation_orders
  intro r
  exact (show (r + 1 : ℕ∞) <= r + 2 by exact_mod_cast (by omega : r + 1 <= r + 2)).trans
    (nat_error_approximation
      pi hpi0 hpi hfield f g hf hg a r)

include pi hpi0 hpi hfield hf hg in
/-- Existence in Lemma 2.11, stated independently of the canonical choice. -/
theorem lubin_intertwiner (a : sigma -> R) :
    ∃ phi : MvPowerSeries sigma R, LIntert f g a phi :=
  ⟨limitSeries pi hpi0 hpi hfield f g hf hg a,
    lubin_intertwiner_limit pi hpi0 hpi hfield f g hf hg a⟩

end LTApprox

end

end Submission.CField.FGroups
