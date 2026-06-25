import Submission.ClassField.HerbrandQuotients.UnitLogMap

/-!
# The remaining logarithmic lattice in Proposition VII.3.1

The first lattice `N = Hom(T, ℤ)` and its Herbrand quotient are now fully
constructed.  This file isolates exactly the remaining arithmetic assertion
from Milne's proof: the logarithmic image of the `T`-units, enlarged by the
constant vector, is a stable full lattice and has quotient
`[L : K] * h(U(T))`.
-/

namespace Submission.CField.HQuotie

open IsDedekindDomain NumberField Representation
open Submission.NumberTheory.Milne
open Submission.CField.Ideles
open Submission.CField.ICohomo

noncomputable section

universe u

/-- The sole remaining arithmetic construction in the proof of Proposition
VII.3.1.  It is Milne's lattice `M = λ(U(T)) + ℤ e` in the already
constructed ambient space `Hom(T, ℝ)`. -/
def LogLatticeBridge : Prop :=
  ∀ (K L : Type u) [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [IsCyclic Gal(L/K)],
    letI : Fintype Gal(L/K) := Fintype.ofFinite Gal(L/K)
    letI : CommGroup Gal(L/K) := IsCyclic.commGroup
    ∀ (S : Finset (NumberFieldPlace K))
      (_hSinf : ∀ v : InfinitePlace K,
        (Sum.inr v : NumberFieldPlace K) ∈ S),
      ∃ (M : Submodule ℤ
          (upperPlacesAt (K := K) (L := L) S → ℝ))
        (hMstable : ∀ g x, x ∈ M →
          placeFunctionRepresentation (K := K) (L := L) S g x ∈ M),
        FullRealLattice M ∧
          ∀ q : ℚ,
            HerbrandQuotientValue
                (stableLatticeRepresentation
                  (placeFunctionRepresentation (K := K) (L := L) S)
                  M hMstable) q ↔
              ∃ qU : ℚ,
                HerbrandQuotientValue
                  (unitsPlacesRepresentation (K := K) (L := L) S) qU ∧
                q = (Module.finrank K L : ℚ) * qU

/-- Once Milne's logarithmic `T`-unit lattice is supplied, the already
formalized place lattice gives the exact arithmetic-lattices bridge used by
Proposition VII.3.1. -/
theorem arithmetic_lattices_lattice
    (hlog : LogLatticeBridge.{u}) :
    ArithmeticLatticesBridge.{u} := by
  intro K L _ _ _ _ _ _ _ _ S hSinf w
  letI : Fintype Gal(L/K) := Fintype.ofFinite Gal(L/K)
  letI : CommGroup Gal(L/K) := IsCyclic.commGroup
  obtain ⟨M, hMstable, hMfull, hM_units⟩ := hlog K L S hSinf
  let V : ModuleCat.{u} ℝ :=
    ModuleCat.of ℝ (upperPlacesAt (K := K) (L := L) S → ℝ)
  let N := upperPlaceLattice (K := K) (L := L) S
  let hNstable := upper_lattice_stable (K := K) (L := L) S
  refine ⟨V,
    placeFunctionRepresentation (K := K) (L := L) S,
    M, N, hMstable, hNstable, hMfull,
    upper_lattice_real (K := K) (L := L) S,
    ?_, hM_units⟩
  exact upper_lattice_herbrand
    (K := K) (L := L) S w

end

end Submission.CField.HQuotie
