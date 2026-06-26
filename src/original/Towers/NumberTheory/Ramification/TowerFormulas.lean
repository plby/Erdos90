import Mathlib.NumberTheory.RamificationInertia.Inertia
import Mathlib.NumberTheory.RamificationInertia.Ramification

/-!
# Milne, Chapter 4, Exercise 2

Ramification indices and inertia degrees are multiplicative in a tower.  We state the result for
a tower of Dedekind domains; the exercise for rings of integers in a tower of number fields is the
standard special case.
-/

namespace Towers.NumberTheory.Milne

variable {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]
  [IsDomain A] [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
  [IsDedekindDomain B] [IsDedekindDomain C]
  [Module.IsTorsionFree A B] [Module.IsTorsionFree B C]

variable (p : Ideal A) (P : Ideal B) (Q : Ideal C)
  [p.IsMaximal] [P.IsMaximal] [Q.IsPrime] [P.LiesOver p] [Q.LiesOver P]

omit [p.IsMaximal] [P.IsMaximal] in
/-- Milne, Exercise 4-2: ramification indices are multiplicative in a tower. -/
theorem ramificationIdx_mul :
    P.ramificationIdx Q * p.ramificationIdx P = p.ramificationIdx Q := by
  simpa [mul_comm] using
    (Ideal.ramificationIdx_algebra_tower' (R := A) (S := B) (T := C) p P Q).symm

omit [IsDomain A] [IsDedekindDomain B] [IsDedekindDomain C]
  [Module.IsTorsionFree A B] [Module.IsTorsionFree B C] [Q.IsPrime] in
/-- Milne, Exercise 4-2: inertia degrees are multiplicative in a tower. -/
theorem inertiaDeg_mul :
    P.inertiaDeg Q * p.inertiaDeg P = p.inertiaDeg Q := by
  simpa [mul_comm] using
    (Ideal.inertiaDeg_algebra_tower (R := A) (S := B) (T := C) p P Q).symm

/-- Both tower identities from Milne, Chapter 4, Exercise 2. -/
theorem tower_identities :
    P.ramificationIdx Q * p.ramificationIdx P = p.ramificationIdx Q ∧
      P.inertiaDeg Q * p.inertiaDeg P = p.inertiaDeg Q :=
  ⟨ramificationIdx_mul p P Q, inertiaDeg_mul p P Q⟩

end Towers.NumberTheory.Milne
