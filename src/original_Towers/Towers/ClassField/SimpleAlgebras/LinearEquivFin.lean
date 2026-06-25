import Towers.ClassField.SimpleAlgebras.LeftIdealsIsomorphic
import Mathlib.Algebra.Algebra.RestrictScalars
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finite

/-!
# Milne, Class Field Theory, Corollary IV.1.21

Every finite module over a finite-dimensional simple algebra is a finite direct
sum of copies of any fixed simple module. Equality of dimensions over the base
field therefore determines the module up to isomorphism.
-/

namespace Towers.CField.SAlgebr

universe u v w

variable (k : Type u) (A : Type v)
variable [Field k] [Ring A] [Algebra k A]
variable [Module.Finite k A] [IsSimpleRing A]

include k

/-- **Corollary IV.1.21, first part.** Every finite `A`-module is a finite
power of any chosen simple `A`-module. -/
theorem module_fin_simple
    (S : Type w) [AddCommGroup S] [Module A S] [IsSimpleModule A S]
    (V : Type w) [AddCommGroup V] [Module A V] [Module.Finite A V] :
    ∃ n : ℕ, Nonempty (V ≃ₗ[A] Fin n → S) := by
  letI : IsSemisimpleRing A := simple_semisimple_ring k A
  have htype : IsIsotypicOfType A V S := by
    intro T _
    exact simple_modules_isotypic A
      (IsSimpleRing.isIsotypic A A) T S
  exact htype.linearEquiv_fun

/-- **Corollary IV.1.21, second part.** Finite modules of the same dimension
over `k` are isomorphic as `A`-modules. -/
theorem modules_isomorphic_finrank
    (S : Type w) [AddCommGroup S] [Module k S] [Module A S]
    [IsScalarTower k A S] [IsSimpleModule A S] [Module.Finite k S]
    (V W : Type w) [AddCommGroup V] [AddCommGroup W]
    [Module k V] [Module k W] [Module A V] [Module A W]
    [IsScalarTower k A V] [IsScalarTower k A W]
    [Module.Finite A V] [Module.Finite A W]
    [Module.Finite k V] [Module.Finite k W]
    (hfin : Module.finrank k V = Module.finrank k W) :
    Nonempty (V ≃ₗ[A] W) := by
  obtain ⟨n, ⟨eV⟩⟩ :=
    module_fin_simple (k := k) (A := A) S V
  obtain ⟨m, ⟨eW⟩⟩ :=
    module_fin_simple (k := k) (A := A) S W
  have hVdim : Module.finrank k V = n * Module.finrank k S := by
    calc
      Module.finrank k V = Module.finrank k (Fin n → S) :=
        (eV.restrictScalars k).finrank_eq
      _ = n * Module.finrank k S := by
        rw [Module.finrank_pi_fintype]
        simp
  have hWdim : Module.finrank k W = m * Module.finrank k S := by
    calc
      Module.finrank k W = Module.finrank k (Fin m → S) :=
        (eW.restrictScalars k).finrank_eq
      _ = m * Module.finrank k S := by
        rw [Module.finrank_pi_fintype]
        simp
  letI : Nontrivial S := IsSimpleModule.nontrivial A S
  have hSmul : 0 < Module.finrank k S := Module.finrank_pos
  have hnm : n = m := Nat.eq_of_mul_eq_mul_right hSmul
    (hVdim.symm.trans (hfin.trans hWdim))
  subst m
  exact ⟨eV.trans eW.symm⟩

end Towers.CField.SAlgebr
