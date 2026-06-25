import Towers.ClassField.LubinTate.RootGaloisAction
import Towers.ClassField.LubinTate.RootFieldRamification
import Towers.ClassField.LubinTate.RootFieldTower

/-!
# Class Field Theory, Chapter I, Summary 3.7

This file packages the finite-level conclusion of Milne's Lubin--Tate tower.
The companion root-field tower file supplies the compatible transition maps
and the ambient directed union. At each finite level, the Eisenstein degree
calculation and the explicit torsion action give generation by a primitive
root, total ramification, the quotient-unit Galois group, abelianity, and the
uniformizer norm assertion.
-/

namespace Towers.CField.LTate

noncomputable section

open Polynomial
open Towers.CField.FGroups
open scoped NormedField

universe v

/-- The finite-level content of Summary 3.7, indexed so that
`reducedLubinIterate f n` is Milne's level `n + 1` polynomial. -/
theorem lubinLevelSummary
    {A K E M : Type*} [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] [Field K] [Field E]
    [Algebra A K] [IsFractionRing A K] [Algebra K E]
    [FiniteDimensional K E] [IsGalois K E]
    [AddCommGroup M] [Module A M] [Finite (M ≃ₗ[A] M)]
    {pi : A} (hpi : Irreducible pi) {f : A[X]} {q : ℕ}
    (hf : f.Monic) (hq : f.natDegree = q) (hqgt : 1 < q)
    (hLT : LubinSeries pi q (f : PowerSeries A))
    (n : ℕ) (x : E)
    (hroot : Polynomial.aeval x
      ((reducedLubinIterate f n).map (algebraMap A K)) = 0)
    (point : M → E)
    (ρ : (E ≃ₐ[K] E) →* (M ≃ₗ[A] M))
    (hpoint : ∀ σ m, point (ρ σ m) = σ (point m))
    (hgen : Algebra.adjoin K (Set.range point) = ⊤)
    (hcard : Nat.card (M ≃ₗ[A] M) = (q - 1) * q ^ n) :
    Module.finrank K E = (q - 1) * q ^ n ∧
      IntermediateField.adjoin K {x} = ⊤ ∧
      Nonempty ((E ≃ₐ[K] E) ≃* (M ≃ₗ[A] M)) ∧
      ∃ y : E, Algebra.norm K y = algebraMap A K pi := by
  have hρ : Function.Injective ρ :=
    galois_action_generates point ρ hpoint hgen
  have hrootDegree :
      Module.finrank K (IntermediateField.adjoin K {x}) =
        (q - 1) * q ^ n :=
    reduced_lubin_iterate
      hpi hf hq hqgt hLT n x hroot
  have hsqueeze := action_cardinality_squeeze ρ hρ
    ((q - 1) * q ^ n) hcard x hrootDegree
  refine ⟨hsqueeze.1, hsqueeze.2, ?_, ?_⟩
  · exact ⟨galoisActionAut ρ hρ
      (hcard.trans hsqueeze.1.symm)⟩
  · exact algebra_uniformizer_generates
      hpi hf hq hqgt hLT n x hroot hsqueeze.2

namespace LTDatum

set_option maxHeartbeats 4000000 in
-- The statement combines the spectral local-field instance telescopes from
-- both the Galois-action and ideal-theoretic ramification theorems.
set_option synthInstance.maxHeartbeats 200000 in
/-- Summary I.3.7 at a concrete finite level, in the indexing where `n`
represents Milne's level `n + 1`.  The distinguished primitive torsion root
generates the whole field, the extension has the asserted degree, is Galois
and totally ramified, its Galois group is the quotient-unit group, and the
distinguished root generates the upstairs maximal ideal, while the base
uniformizer is a norm.

The stronger theorem `root_unit_orbit` identifies the
displayed multiplicative equivalence with the action `a * lambda = [a]_f(lambda)`
on the distinguished root. -/
theorem root_level_summary
    (K : Type v) [NontriviallyNormedField K] [IsUltrametricDist K]
    [CompleteSpace K] [ProperSpace K] [ValuativeRel K]
    [IsNonarchimedeanLocalField K]
    [Valuation.Compatible (NormedField.valuation (K := K))]
    [IsDiscreteValuationRing
      (Valuation.integer (NormedField.valuation (K := K)))]
    (D : LTDatum
      (Valuation.integer (NormedField.valuation (K := K))))
    (hfield : IsField
      (Valuation.integer (NormedField.valuation (K := K)) ⧸
        Ideal.span {D.pi}))
    (n : ℕ) :
    let A := Valuation.integer (NormedField.valuation (K := K))
    letI : Finite (A ⧸ Ideal.span {D.pi}) := D.finiteResidue
    letI : Fintype (A ⧸ Ideal.span {D.pi}) := Fintype.ofFinite _
    let E := D.RootField K n
    letI : Algebra.IsAlgebraic K E := Algebra.IsAlgebraic.of_finite K E
    letI : NontriviallyNormedField E :=
      spectralNorm.nontriviallyNormedField K E
    letI : NormedAlgebra K E := spectralNorm.normedAlgebra K E
    letI : IsUltrametricDist E := IsUltrametricDist.of_normedAlgebra K
    letI : ValuativeRel E :=
      LBrauer.FLExt.valuativeRel K E
    letI : IsNonarchimedeanLocalField E :=
      LBrauer.FLExt.nonarchimedeanLocalField K E
    letI : Valuation.Compatible (NormedField.valuation (K := E)) :=
      Valuation.Compatible.ofValuation (NormedField.valuation (K := E))
    letI : CompleteSpace E := spectralNorm.completeSpace K E
    letI : ProperSpace E := FiniteDimensional.proper K E
    letI : (NormedField.valuation (K := K)).HasExtension
        (NormedField.valuation (K := E)) :=
      LBrauer.spectralValuationExtension K E
    let B := Valuation.integer (NormedField.valuation (K := E))
    Module.finrank K E = (D.q - 1) * D.q ^ n ∧
      IntermediateField.adjoin K {D.root K n} = ⊤ ∧
      IsGalois K E ∧
      Towers.NumberTheory.Milne.TotallyRamified A B
        (IsLocalRing.maximalIdeal A) ∧
      Nonempty
        ((A ⧸ Ideal.span {D.pi ^ (n + 1)})ˣ ≃* (E ≃ₐ[K] E)) ∧
      (∀ σ τ : E ≃ₐ[K] E, Commute σ τ) ∧
      (∃ alpha : B, B.subtype alpha = D.root K n ∧
        IsLocalRing.maximalIdeal B = Ideal.span {alpha}) ∧
      ∃ y : E, Algebra.norm K y = algebraMap A K D.pi := by
  let A := Valuation.integer (NormedField.valuation (K := K))
  letI : Finite (A ⧸ Ideal.span {D.pi}) := D.finiteResidue
  letI : Fintype (A ⧸ Ideal.span {D.pi}) := Fintype.ofFinite _
  let E := D.RootField K n
  letI : Algebra.IsAlgebraic K E := Algebra.IsAlgebraic.of_finite K E
  letI : NontriviallyNormedField E :=
    spectralNorm.nontriviallyNormedField K E
  letI : NormedAlgebra K E := spectralNorm.normedAlgebra K E
  letI : IsUltrametricDist E := IsUltrametricDist.of_normedAlgebra K
  letI : ValuativeRel E :=
    LBrauer.FLExt.valuativeRel K E
  letI : IsNonarchimedeanLocalField E :=
    LBrauer.FLExt.nonarchimedeanLocalField K E
  letI : Valuation.Compatible (NormedField.valuation (K := E)) :=
    Valuation.Compatible.ofValuation (NormedField.valuation (K := E))
  letI : CompleteSpace E := spectralNorm.completeSpace K E
  letI : ProperSpace E := FiniteDimensional.proper K E
  letI : (NormedField.valuation (K := K)).HasExtension
      (NormedField.valuation (K := E)) :=
    LBrauer.spectralValuationExtension K E
  let B := Valuation.integer (NormedField.valuation (K := E))
  obtain ⟨y, hy, hyroot, orbit, horbit⟩ :=
    D.root_unit_orbit K hfield n
  refine ⟨D.finrank_rootField K n, D.adjoin_root_top K n,
    D.root_field_galois K hfield n,
    D.root_totally_ramified K hfield n, ?_, ?_,
    D.root_field_uniformizer K hfield n,
    D.norm_uniformizer K n⟩
  · exact ⟨orbit⟩
  · intro σ τ
    obtain ⟨u, rfl⟩ := orbit.surjective σ
    obtain ⟨v, rfl⟩ := orbit.surjective τ
    change orbit u * orbit v = orbit v * orbit u
    calc
      orbit u * orbit v = orbit (u * v) := (map_mul orbit u v).symm
      _ = orbit (v * u) := by rw [mul_comm]
      _ = orbit v * orbit u := map_mul orbit v u

end LTDatum

end

end Towers.CField.LTate
