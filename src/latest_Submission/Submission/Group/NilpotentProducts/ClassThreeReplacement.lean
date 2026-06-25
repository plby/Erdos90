import Mathlib


namespace Struik

/-- The five coordinates used for `F / F₄` in equations (43)--(45). -/
@[ext]
structure CTCoordi where
  c1 : ℤ
  c2 : ℤ
  c12 : ℤ
  c121 : ℤ
  c122 : ℤ
  deriving DecidableEq

namespace CTCoordi

/-- Change from the standard commutators in (43) to the replacement
commutators in (44). -/
def toReplacement (c : CTCoordi) :
    CTCoordi where
  c1 := c.c1
  c2 := c.c2
  c12 := c.c12 - 2 * c.c121 - 2 * c.c122
  c121 := c.c121
  c122 := c.c122

/-- The inverse coordinate change in equation (45). -/
def fromReplacement (γ : CTCoordi) :
    CTCoordi where
  c1 := γ.c1
  c2 := γ.c2
  c12 := γ.c12 + 2 * γ.c121 + 2 * γ.c122
  c121 := γ.c121
  c122 := γ.c122

@[simp]
theorem from_to_replacement (c : CTCoordi) :
    fromReplacement (toReplacement c) = c := by
  ext <;> simp [fromReplacement, toReplacement] ; ring

@[simp]
theorem to_from_replacement (γ : CTCoordi) :
    toReplacement (fromReplacement γ) = γ := by
  ext <;> simp [fromReplacement, toReplacement] ; ring

theorem fromReplacement_injective :
    Function.Injective fromReplacement := by
  intro γ δ h
  rw [← to_from_replacement γ,
    ← to_from_replacement δ, h]

/-- Equation (45) is an integral equivalence of coordinate systems. -/
def replacementEquiv :
    CTCoordi ≃ CTCoordi where
  toFun := toReplacement
  invFun := fromReplacement
  left_inv := from_to_replacement
  right_inv := to_from_replacement

/-- Transport an old multiplication table through the replacement basis. -/
def transportMul
    (oldMul : CTCoordi → CTCoordi →
      CTCoordi)
    (γ δ : CTCoordi) : CTCoordi :=
  toReplacement (oldMul (fromReplacement γ) (fromReplacement δ))

@[simp]
theorem replacement_transport_mul
    (oldMul : CTCoordi → CTCoordi →
      CTCoordi)
    (γ δ : CTCoordi) :
    fromReplacement (transportMul oldMul γ δ) =
      oldMul (fromReplacement γ) (fromReplacement δ) := by
  simp [transportMul]

/-- The observation following (45): associativity need not be checked again
after a basis substitution. -/
theorem transportMul_assoc
    (oldMul : CTCoordi → CTCoordi →
      CTCoordi)
    (hassoc : ∀ x y z, oldMul (oldMul x y) z = oldMul x (oldMul y z))
    (γ δ ε : CTCoordi) :
    transportMul oldMul (transportMul oldMul γ δ) ε =
      transportMul oldMul γ (transportMul oldMul δ ε) := by
  apply fromReplacement_injective
  simp only [replacement_transport_mul]
  exact hassoc _ _ _

theorem transport_left_identity
    (oldMul : CTCoordi → CTCoordi →
      CTCoordi)
    (one : CTCoordi)
    (hone : ∀ x, oldMul one x = x)
    (γ : CTCoordi) :
    transportMul oldMul (toReplacement one) γ = γ := by
  apply fromReplacement_injective
  simp [hone]

theorem transport_right_identity
    (oldMul : CTCoordi → CTCoordi →
      CTCoordi)
    (one : CTCoordi)
    (hone : ∀ x, oldMul x one = x)
    (γ : CTCoordi) :
    transportMul oldMul γ (toReplacement one) = γ := by
  apply fromReplacement_injective
  simp [hone]

end CTCoordi

end Struik
