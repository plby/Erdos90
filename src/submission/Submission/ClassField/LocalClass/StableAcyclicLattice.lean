import Submission.NumberTheory.Locals.LocalUnramifiedDecomposition
import Submission.ClassField.LocalClass.RegularLatticeCore
import Submission.ClassField.LocalBrauer.FiniteLocalExtension

/-!
# Milne, Class Field Theory, Lemma III.2.3

This file specializes the integral normal-basis construction to an arbitrary
finite Galois extension of a nonarchimedean local field.  The extension is
equipped with its canonical spectral norm, so no compatibility assumption on
a separately chosen topology upstairs is needed.
-/

namespace Submission.CField.LClass

open CategoryTheory
open Submission.NumberTheory.Milne
open Submission.CField.LBrauer
open scoped NormedField Valued

noncomputable section

attribute [local instance] NormedField.toValued

universe u

/-- **Lemma III.2.3.** For a finite Galois extension `L/K` of a
nonarchimedean local field, an integral multiple of a normal basis spans an
open additive lattice in `O_L`.  The lattice is stable under `Gal(L/K)`, is
the regular `O_K`-representation, and consequently has zero cohomology in
every positive degree.

The norm and topology on the abstract extension field `L` in the conclusion
are the canonical spectral ones. -/
theorem stable_acyclic_lattice
    (K L : Type u)
    [NontriviallyNormedField K] [IsUltrametricDist K]
    [ValuativeRel K] [IsNonarchimedeanLocalField K]
    [Field L] [Algebra K L] [Module.Finite K L] [IsGalois K L] :
    letI : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.of_finite K L
    letI : NontriviallyNormedField L :=
      FLExt.nontriviallyNormedField K L
    letI : NormedAlgebra K L := spectralNorm.normedAlgebra K L
    letI : IsUltrametricDist L := IsUltrametricDist.of_normedAlgebra K
    let A := Valued.integer K
    let B := Valued.integer L
    ∃ (d : A) (hd : d ≠ 0),
      (integralNormalSpan A K L d hd : Set L) ⊆ B ∧
      IsOpen (integralNormalSpan A K L d hd : Set L) ∧
      (∀ g : Gal(L/K),
        integralNormalSpan A K L d hd ≤
          (integralNormalSpan A K L d hd).comap
            ((Rep.ofDistribMulAction A Gal(L/K) L).ρ g)) ∧
      Nonempty (Rep.leftRegular A Gal(L/K) ≅
        integralBasisRepresentation A K L d hd) ∧
      ∀ r : ℕ, 0 < r →
        Limits.IsZero (groupCohomology
          (integralBasisRepresentation A K L d hd) r) := by
  letI : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.of_finite K L
  letI : NontriviallyNormedField L :=
    FLExt.nontriviallyNormedField K L
  letI : NormedAlgebra K L := spectralNorm.normedAlgebra K L
  letI : IsUltrametricDist L := IsUltrametricDist.of_normedAlgebra K
  letI : (NormedField.valuation (K := K)).HasExtension
      (NormedField.valuation (K := L)) :=
    valuation_normed_algebra K L
  let A := Valued.integer K
  let B := Valued.integer L
  letI : IsIntegralClosure B A L := valued_integer_closure K L
  letI : Algebra.IsIntegral A B :=
    IsIntegralClosure.isIntegral_algebra A L
  obtain ⟨d, hd, hspan, hopen, ⟨ereg⟩⟩ :=
    open_regular_lattice A K L
  refine ⟨d, hd, ?_, hopen, ?_, ⟨ereg⟩, ?_⟩
  · intro x hx
    have hxint : IsIntegral A x :=
      (mem_integralClosure_iff A L).1 (hspan hx)
    obtain ⟨y, hy⟩ :=
      (IsIntegralClosure.isIntegral_iff (R := A) (A := B) (B := L)).1 hxint
    change (NormedField.valuation (K := L)) x ≤ 1
    rw [← hy]
    exact y.property
  · exact fun g ↦ integral_basis_stable A K L d hd g
  · intro r hr
    exact cohomology_iso_regular A
      (integralBasisRepresentation A K L d hd) ereg.symm r hr

end

end Submission.CField.LClass
