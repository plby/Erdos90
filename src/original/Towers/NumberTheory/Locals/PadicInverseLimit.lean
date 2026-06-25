import Mathlib.NumberTheory.Padics.RingHoms

/-!
# The p-adic integers as an inverse limit

This is the universal-property formulation of Milne's Aside 7.30.  A
compatible family of reductions modulo `p ^ n` lifts uniquely to `ℤ_p`.
-/

namespace Towers.NumberTheory.Milne

variable {p : ℕ} [Fact p.Prime]

/-- Two p-adic integers are equal exactly when all of their reductions modulo
`p ^ n` agree. -/
theorem padic_int_reductions {x y : ℤ_[p]} :
    (∀ n, PadicInt.toZModPow n x = PadicInt.toZModPow n y) ↔ x = y :=
  PadicInt.ext_of_toZModPow

/-- Milne, Aside 7.30: the p-adic integers satisfy the universal property of
the inverse limit of the rings `ZMod (p ^ n)`. -/
theorem padic_limit_lift
    {R : Type*} [NonAssocSemiring R]
    (f : ∀ n : ℕ, R →+* ZMod (p ^ n))
    (hcompat : ∀ (m n : ℕ) (hmn : m ≤ n),
      (ZMod.castHom (pow_dvd_pow p hmn) (ZMod (p ^ m))).comp (f n) = f m) :
    ∃! g : R →+* ℤ_[p], ∀ n, (PadicInt.toZModPow n).comp g = f n := by
  refine ⟨PadicInt.lift hcompat, PadicInt.lift_spec hcompat, ?_⟩
  intro g hg
  exact (PadicInt.lift_unique hcompat g hg).symm

end Towers.NumberTheory.Milne
