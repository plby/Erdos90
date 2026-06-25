import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Towers.ClassField.LocalBrauer.UnramifiedExtensionGalois

/-!
# Chapter IV, Section 4: unramified levels in a fixed separable closure

Milne chooses every finite unramified extension inside one fixed algebraic
closure.  The Hensel construction gives an abstract cyclic Galois extension;
this file embeds it into `SeparableClosure K` and retains its degree and cyclic
Galois group.
-/

namespace Towers.CField.LBrauer

noncomputable section

universe u

variable (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K]
  [ValuativeRel K] [IsNonarchimedeanLocalField K]
  [Valuation.Compatible (NormedField.valuation (K := K))]

/-- Every positive degree occurs among the finite cyclic Galois subextensions
of the fixed separable closure which arise from the unramified Hensel
construction. -/
theorem unramified_galois_intermediate
    (n : ℕ) [NeZero n] :
    ∃ E : FiniteGaloisIntermediateField K (SeparableClosure K),
      Module.finrank K E = n ∧
        IsCyclic Gal(E / K) ∧
        Nonempty (Multiplicative (ZMod n) ≃* Gal(E / K)) := by
  obtain ⟨L, hField, hAlgebra, hFinite, hGalois,
      hdegree, hcyclic, φ, hφorder⟩ :=
    cyclic_galois_extension K n
  letI : Field L := hField
  letI : Algebra K L := hAlgebra
  letI : Module.Finite K L := hFinite
  letI : IsGalois K L := hGalois
  let i : L →ₐ[K] SeparableClosure K := IsSepClosed.lift
  let E' : IntermediateField K (SeparableClosure K) := i.fieldRange
  let e : L ≃ₐ[K] E' := AlgEquiv.ofInjectiveField i
  letI : Module.Finite K E' := Module.Finite.equiv e.toLinearEquiv
  letI : IsGalois K E' := IsGalois.of_algEquiv e
  let E : FiniteGaloisIntermediateField K (SeparableClosure K) :=
    { E' with
      finiteDimensional := inferInstance
      isGalois := inferInstance }
  have hdegreeE : Module.finrank K E = n := by
    rw [show Module.finrank K E = Module.finrank K E' by rfl,
      ← e.toLinearEquiv.finrank_eq, hdegree]
  let eAut : Gal(L / K) ≃* Gal(E / K) := e.autCongr
  have hcyclicE : IsCyclic Gal(E / K) := eAut.isCyclic.mp hcyclic
  have hcard : Nat.card Gal(E / K) = n := by
    rw [IsGalois.card_aut_eq_finrank, hdegreeE]
  refine ⟨E, hdegreeE, hcyclicE, ?_⟩
  exact ⟨hcard ▸ zmodCyclicMulEquiv hcyclicE⟩

end

end Towers.CField.LBrauer
