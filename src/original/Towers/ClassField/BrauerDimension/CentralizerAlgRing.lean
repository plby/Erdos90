import Mathlib.RingTheory.SimpleModule.WedderburnArtin

/-!
# Chapter IV, Section 5, Theorem 5.3

For a finite semisimple module, its endomorphism algebra is a finite product
of matrix algebras over division algebras.  When an algebra `A` acts on `V`,
`Module.End A V` is the centralizer of that action in the endomorphisms of
the underlying vector space, so this is Milne's Theorem 5.3.
-/

namespace Towers.CField.BDim

universe u

variable (k A V : Type u) [Field k] [Ring A] [Algebra k A]
  [AddCommGroup V] [Module k V] [Module A V] [IsScalarTower k A V]
  [IsSemisimpleModule A V] [Module.Finite A V]

/-- Milne, Theorem IV.5.3, in the stronger Artin-Wedderburn form supplied by
Mathlib. -/
theorem centralizer_pi_matrix :
    ∃ (n : ℕ) (D : Fin n → Type u) (d : Fin n → ℕ)
      (_ : ∀ i, DivisionRing (D i)) (_ : ∀ i, Algebra k (D i)),
      (∀ i, NeZero (d i)) ∧
        Nonempty
          (Module.End A V ≃ₐ[k]
            ∀ i, Matrix (Fin (d i)) (Fin (d i)) (D i)) :=
  IsSemisimpleModule.exists_end_algEquiv_pi_matrix_divisionRing k A V

omit [Field k] [Algebra k A] [Module k V] [IsScalarTower k A V] in
/-- In particular, the centralizer algebra is semisimple. -/
theorem centralizer_semisimple_ring : IsSemisimpleRing (Module.End A V) :=
  IsSemisimpleRing.moduleEnd A V

end Towers.CField.BDim
