import Towers.ClassField.NormCorrespondence.Main
import Towers.ClassField.LubinTate.AmbientNorm
import Towers.ClassField.LubinTate.RootGaloisAction

/-!
# Finite Lubin--Tate levels as abelian subextensions

The finite Lubin--Tate root fields are Galois and their explicit
quotient-unit actions make them abelian.  We embed these finite separable
extensions into the chosen separable closure used by local reciprocity.
The uniformizer-norm assertion then gives the first restriction calculation
in the proof of claim I.1.14.
-/

namespace Towers.CField.LTate

noncomputable section

namespace LTDatum

open scoped NormedField
open Towers.CField.LFTheory

universe v

variable (K : Type v) [NontriviallyNormedField K] [IsUltrametricDist K]
  [CompleteSpace K] [ProperSpace K] [ValuativeRel K]
  [IsNonarchimedeanLocalField K]
  [Valuation.Compatible (NormedField.valuation (K := K))]
  [IsDiscreteValuationRing
    (Valuation.integer (NormedField.valuation (K := K)))]

set_option maxHeartbeats 5000000 in
-- Commutativity is transported from the explicit quotient-unit orbit on the
-- spectral root field.
set_option synthInstance.maxHeartbeats 300000 in
/-- The Galois group of a finite Lubin--Tate root field is abelian. -/
theorem root_aut_commutative
    (D : LTDatum
      (Valuation.integer (NormedField.valuation (K := K))))
    (hfield : IsField
      (Valuation.integer (NormedField.valuation (K := K)) ⧸
        Ideal.span {D.pi}))
    (n : ℕ) : IsMulCommutative Gal(D.RootField K n/K) := by
  let A := Valuation.integer (NormedField.valuation (K := K))
  let E := D.RootField K n
  letI : IsGalois K E := D.root_field_galois K hfield n
  letI : Finite (A ⧸ Ideal.span {D.pi}) := D.finiteResidue
  letI : Fintype (A ⧸ Ideal.span {D.pi}) := Fintype.ofFinite _
  obtain ⟨_, _, _, orbit, _⟩ :=
    D.root_unit_orbit K hfield n
  refine ⟨⟨fun sigma tau ↦ ?_⟩⟩
  obtain ⟨u, rfl⟩ := orbit.surjective sigma
  obtain ⟨v, rfl⟩ := orbit.surjective tau
  rw [← map_mul, ← map_mul, mul_comm]

set_option maxHeartbeats 5000000 in
-- Constructing the bundled extension replays the spectral root-field
-- Galois instances used by the preceding commutativity theorem.
set_option synthInstance.maxHeartbeats 300000 in
/-- The level-`n + 1` Lubin--Tate root field as an abstract finite abelian
extension of `K`. -/
noncomputable def rootAbelianExtension
    (D : LTDatum
      (Valuation.integer (NormedField.valuation (K := K))))
    (hfield : IsField
      (Valuation.integer (NormedField.valuation (K := K)) ⧸
        Ideal.span {D.pi}))
    (n : ℕ) : FAExt.{v, v} K := by
  let E := D.RootField K n
  letI : IsGalois K E := D.root_field_galois K hfield n
  letI : IsMulCommutative Gal(E/K) :=
    D.root_aut_commutative K hfield n
  exact
    { carrier := E
      field := inferInstance
      algebra := inferInstance
      finiteDimensional := inferInstance
      isGalois := inferInstance
      isAbelian := inferInstance }

/-- The finite root field embedded into the fixed separable closure from the
statement of local reciprocity. -/
noncomputable def rootAbelianSubextension
    (D : LTDatum
      (Valuation.integer (NormedField.valuation (K := K))))
    (hfield : IsField
      (Valuation.integer (NormedField.valuation (K := K)) ⧸
        Ideal.span {D.pi}))
    (n : ℕ) : FASubext K :=
  (D.rootAbelianExtension K hfield n).finiteAbelianSubextension

/-- The chosen uniformizer belongs to the norm group of the embedded finite
Lubin--Tate level. -/
theorem unifor_abeli_subex
    (D : LTDatum
      (Valuation.integer (NormedField.valuation (K := K))))
    (hfield : IsField
      (Valuation.integer (NormedField.valuation (K := K)) ⧸
        Ideal.span {D.pi}))
    (n : ℕ) :
    D.uniformizerUnit K ∈
      (D.rootAbelianSubextension K hfield n).normGroup := by
  change D.uniformizerUnit K ∈
    (D.rootAbelianExtension K hfield n).finiteAbelianSubextension.normGroup
  rw [← FAExt.norm_abelian_subextension]
  change D.uniformizerUnit K ∈ normSubgroup K (D.RootField K n)
  obtain ⟨y, hy⟩ := D.norm_uniformizer K n
  have hy0 : y ≠ 0 := by
    intro hyzero
    rw [hyzero, Algebra.norm_zero] at hy
    have hpi0 : algebraMap
        (Valuation.integer (NormedField.valuation (K := K))) K D.pi ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective _ _)).2
        D.pi_irreducible.ne_zero
    exact hpi0 hy.symm
  refine ⟨Units.mk0 y hy0, ?_⟩
  apply Units.ext
  exact hy

/-- A reciprocity map sends the chosen Lubin--Tate prime to the identity on
every embedded finite root-field level, because that prime is a norm. -/
theorem abelian_restriction_uniformizer
    (D : LTDatum
      (Valuation.integer (NormedField.valuation (K := K))))
    (hfield : IsField
      (Valuation.integer (NormedField.valuation (K := K)) ⧸
        Ideal.span {D.pi}))
    (phi : Kˣ →* AbsoluteAbelianGalois K)
    (hphi : ∀ L : FASubext K,
      InducesLocalReciprocity K phi L)
    (n : ℕ) :
    localAbelianRestriction
        (D.rootAbelianSubextension K hfield n)
        (phi (D.uniformizerUnit K)) = 1 :=
  (norm_abelian_restriction
    phi hphi (D.rootAbelianSubextension K hfield n)
      (D.uniformizerUnit K)).1
    (D.unifor_abeli_subex
      K hfield n)

end LTDatum

end

end Towers.CField.LTate
