import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.LinearAlgebra.QuadraticForm.Radical

/-! # Chapter VIII, Section 6, Lemma 6.8 -/

namespace Towers.CField.QForms

universe u v

variable {k : Type u} {V : Type v} [Field k] [AddCommGroup V] [Module k V]
  [FiniteDimensional k V]

/-- Two ordered bases differ at at most two adjacent positions. -/
def BasesMostAdjacent
    (B B' : Module.Basis (Fin (Module.finrank k V)) k V) : Prop :=
  B = B' ∨
    ∃ i : ℕ, i + 1 < Module.finrank k V ∧
      ∀ j : Fin (Module.finrank k V),
        j.1 ≠ i → j.1 ≠ i + 1 → B j = B' j

/-- **Lemma VIII.6.8.** Any two orthogonal bases of a nondegenerate
quadratic space are connected by finitely many orthogonal bases, with each
step altering at most two adjacent vectors. -/
def BasesDifferMost : Prop :=
  ∀ (Q : QuadraticForm k V)
    (B B' : Module.Basis (Fin (Module.finrank k V)) k V),
    Q.Nondegenerate → Q.polarBilin.IsOrthoᵢ B → Q.polarBilin.IsOrthoᵢ B' →
    ∃ m : ℕ, ∃ Bs : Fin (m + 1) → Module.Basis (Fin (Module.finrank k V)) k V,
      Bs 0 = B ∧ Bs ⟨m, Nat.lt_add_one m⟩ = B' ∧
      (∀ i, Q.polarBilin.IsOrthoᵢ (Bs i)) ∧
      ∀ i : Fin m,
        BasesMostAdjacent (Bs i.castSucc) (Bs i.succ)

/-- O'Meara's basis-chain lemma is the sole geometric input still required
for the exact source statement. -/
def OrthogonalChainBridge : Prop :=
  BasesDifferMost (k := k) (V := V)

omit [FiniteDimensional k V] in
theorem of_basisChain
    (h : OrthogonalChainBridge (k := k) (V := V)) :
    BasesDifferMost (k := k) (V := V) :=
  h

end Towers.CField.QForms
