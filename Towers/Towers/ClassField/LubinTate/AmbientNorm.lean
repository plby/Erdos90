import Towers.ClassField.LocalFields.NormSubgroups
import Towers.ClassField.LubinTate.RootFieldTower

/-!
# The uniformizer norm in the ambient Lubin--Tate tower

Theorem I.3.6(c) proves that the chosen uniformizer is a norm from the
distinguished root-field model.  This file transports that assertion to the
actual finite torsion fields inside the common algebraic closure.  It is the
condition used in the proof of claim I.1.14 to show that the global Artin
image of a prime acts trivially on every finite part of `K_pi`.
-/

namespace Towers.CField.LTate

noncomputable section

namespace LTDatum

open scoped NormedField
open Towers.CField.LFTheory

universe u v w

section UniformizerUnit

variable {A : Type u} [CommRing A] [IsDomain A]
  [IsDiscreteValuationRing A]
  (D : LTDatum A)
  (K : Type v) [Field K] [Algebra A K] [IsFractionRing A K]

/-- The chosen Lubin--Tate uniformizer, regarded as an element of `Kˣ`. -/
noncomputable def uniformizerUnit : Kˣ :=
  Units.mk0 (algebraMap A K D.pi)
    ((map_ne_zero_iff (algebraMap A K)
      (IsFractionRing.injective A K)).2 D.pi_irreducible.ne_zero)

end UniformizerUnit

section LocalField

variable (K : Type v) [NontriviallyNormedField K] [IsUltrametricDist K]
  [CompleteSpace K] [ProperSpace K] [ValuativeRel K]
  [IsNonarchimedeanLocalField K]
  [Valuation.Compatible (NormedField.valuation (K := K))]
  [IsDiscreteValuationRing
    (Valuation.integer (NormedField.valuation (K := K)))]
  (Omega : Type w) [Field Omega] [Algebra K Omega] [IsAlgClosure K Omega]

set_option maxHeartbeats 3000000 in
-- The concrete torsion level receives its finite module structure through
-- the cached splitting-field equivalence with the root-field model.
/-- The chosen uniformizer belongs to the norm subgroup of every concrete
finite Lubin--Tate torsion field. -/
theorem uniformizer_torsion_level
    (D : LTDatum
      (Valuation.integer (NormedField.valuation (K := K))))
    (hfield : IsField
      (Valuation.integer (NormedField.valuation (K := K)) ⧸
        Ideal.span {D.pi}))
    (n : ℕ) :
    D.uniformizerUnit K ∈
      normSubgroup K (D.torsionLevelField K Omega n) := by
  let A := Valuation.integer (NormedField.valuation (K := K))
  let E := D.RootField K n
  let T := D.torsionLevelField K Omega n
  let e : E ≃ₐ[K] T :=
    D.rootTorsionLevel K Omega hfield n
  letI : Module.Finite K T := Module.Finite.equiv e.toLinearEquiv
  rw [← norm_alg_equiv K E T e]
  obtain ⟨y, hy⟩ := D.norm_uniformizer K n
  have hy0 : y ≠ 0 := by
    intro hyzero
    rw [hyzero, Algebra.norm_zero] at hy
    have hpi0 : algebraMap A K D.pi ≠ 0 :=
      (map_ne_zero_iff (algebraMap A K)
        (IsFractionRing.injective A K)).2 D.pi_irreducible.ne_zero
    exact hpi0 hy.symm
  refine ⟨Units.mk0 y hy0, ?_⟩
  apply Units.ext
  exact hy

end LocalField

end LTDatum

end

end Towers.CField.LTate
