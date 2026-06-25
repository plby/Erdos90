import Mathlib.RingTheory.FiniteLength
import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Milne, Class Field Theory, Theorem IV.1.2

Every finite-dimensional algebra module admits a composition series, and the
Jordan--Holder theorem identifies the successive simple quotients of any two
such series up to permutation. Mathlib formulates this for finite-length
modules and composition series in the lattice of submodules.
-/

namespace Towers.CField.SAlgebr

universe u v w

variable {R : Type u} {M : Type v} [Ring R] [AddCommGroup M] [Module R M]

/-- The successive quotient attached to one step of a composition series. -/
abbrev compositionFactor (s : CompositionSeries (Submodule R M))
    (i : Fin s.length) :=
  s (Fin.succ i) ⧸
    (s (Fin.castSucc i)).comap (s (Fin.succ i)).subtype

/-- **Theorem IV.1.2, existence.** A finite-length module has a composition
series from `0` to the whole module, and every successive quotient is simple. -/
theorem composition_series_length
    (hM : IsFiniteLength R M) :
    ∃ s : CompositionSeries (Submodule R M),
      s.head = ⊥ ∧ s.last = ⊤ ∧
        ∀ i : Fin s.length, IsSimpleModule R (compositionFactor s i) := by
  obtain ⟨s, hs0, hs1⟩ :=
    isFiniteLength_iff_exists_compositionSeries.mp hM
  refine ⟨s, hs0, hs1, ?_⟩
  intro i
  exact (covBy_iff_quot_is_simple (le_of_lt (s.lt_succ i))).mp (s.step i)

/-- Milne's finite-dimensional hypothesis implies the finite-length
hypothesis used above, even when the acting algebra is noncommutative. -/
theorem composition_series_dimensional
    {k : Type w} {A : Type u} {V : Type v}
    [Field k] [Ring A] [Algebra k A]
    [AddCommGroup V] [Module k V] [Module A V] [IsScalarTower k A V]
    [FiniteDimensional k V] :
    ∃ s : CompositionSeries (Submodule A V),
      s.head = ⊥ ∧ s.last = ⊤ ∧
        ∀ i : Fin s.length, IsSimpleModule A (compositionFactor s i) := by
  letI : IsNoetherian A V :=
    isNoetherian_of_tower k (inferInstance : IsNoetherian k V)
  letI : IsArtinian A V :=
    isArtinian_of_tower k (inferInstance : IsArtinian k V)
  exact composition_series_length
    (isFiniteLength_iff_isNoetherian_isArtinian.mpr
      ⟨inferInstance, inferInstance⟩)

/-- **Theorem IV.1.2, uniqueness.** Two composition series with the same
endpoints have equivalent composition factors. `CompositionSeries.Equivalent`
contains the required permutation and the linear equivalence of each matched
pair of successive quotients. -/
theorem compositionSeries_equivalent
    (s t : CompositionSeries (Submodule R M))
    (hs0 : s.head = ⊥) (hs1 : s.last = ⊤)
    (ht0 : t.head = ⊥) (ht1 : t.last = ⊤) :
    s.Equivalent t :=
  s.jordan_holder t (hs0.trans ht0.symm) (hs1.trans ht1.symm)

/-- In particular, any two composition series have the same length. -/
theorem composition_length
    (s t : CompositionSeries (Submodule R M))
    (hs0 : s.head = ⊥) (hs1 : s.last = ⊤)
    (ht0 : t.head = ⊥) (ht1 : t.last = ⊤) :
    s.length = t.length :=
  (compositionSeries_equivalent s t hs0 hs1 ht0 ht1).length_eq

end Towers.CField.SAlgebr
