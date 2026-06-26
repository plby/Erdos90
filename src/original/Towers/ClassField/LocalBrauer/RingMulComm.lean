import Mathlib.RingTheory.LittleWedderburn
import Towers.ClassField.BrauerGroups.CentralSimpleClosed

/-!
# Chapter IV, Section 4, Theorem 4.1

Milne begins the computation of Brauer groups of special fields with
Wedderburn's little theorem.  Mathlib contains the theorem as the instance
`littleWedderburn`.
-/

namespace Towers.CField.LBrauer

universe u

/-- Milne, Theorem IV.4.1 (Wedderburn): multiplication in a finite division
ring is commutative. -/
theorem division_ring_comm
    (D : Type u) [DivisionRing D] [Finite D] (x y : D) : x * y = y * x := by
  letI : Field D := littleWedderburn D
  exact mul_comm x y

/-- The finite-field consequence used immediately after Theorem IV.4.1: the
Brauer quotient of a finite field is trivial. -/
theorem brauer_group_subsingleton
    (k : Type u) [Field k] [Finite k] :
    Subsingleton (BrauerGroup.{u, u} k) :=
  BGroups.brauer_subsingleton_field k

end Towers.CField.LBrauer
