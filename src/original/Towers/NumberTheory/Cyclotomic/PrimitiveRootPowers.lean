import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

/-!
# Powers of primitive roots

This file formalizes Lemma 6.1 of Milne's *Algebraic Number Theory* notes.  It
also records the general group-theoretic statement about the order of a power
that Milne uses in the proof.
-/

namespace Towers.NumberTheory.Milne

section CommMonoid

variable {G : Type*} [CommMonoid G]

/-- Milne, Lemma 6.1: a power of a primitive `n`th root is again primitive
exactly when its exponent is coprime to `n`. -/
theorem primitive_root_coprime {zeta : G} {m n : ℕ}
    (hzeta : IsPrimitiveRoot zeta n) (hn : 0 < n) :
    IsPrimitiveRoot (zeta ^ m) n ↔ m.Coprime n :=
  hzeta.pow_iff_coprime hn m

end CommMonoid

end Towers.NumberTheory.Milne
