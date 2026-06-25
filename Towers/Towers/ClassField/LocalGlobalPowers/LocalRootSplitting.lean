import Towers.ClassField.LocalGlobalPowers.RadicalExtensionData
import Towers.ClassField.Ideles.FinitePlaceCompletion

/-!
# Chapter VIII, Section 1, Theorem 1.1: the local splitting step

A local root of the radical polynomial, together with the primitive roots
of unity already in the ground field, makes every completed factor of the
radical extension have degree one.
-/

namespace Towers.CField.LGPowers

open AbsoluteValue IsDedekindDomain NumberField Polynomial
open Towers.NumberTheory.Milne
open Towers.CField.Ideles
open Towers.CField.ICohomo
open Towers.CField.NIndex

noncomputable section

universe u

private abbrev OK (K : Type u) [Field K] [NumberField K] :=
  NumberField.RingOfIntegers K

set_option maxHeartbeats 1000000 in
-- Typeclass synthesis for the two nested completion fields is expensive.
/-- The local-root-to-complete-splitting implication used in Theorem 1.1. -/
theorem local_splits_completely
    (n : ℕ) (K : Type u) [Field K] [NumberField K] (a : Kˣ)
    (data : REData K n a)
    (P : HeightOneSpectrum (OK K))
    (hroots : (primitiveRoots n K).Nonempty)
    (hlocal : ∃ x : P.adicCompletion K,
      x ^ n = algebraMap K (P.adicCompletion K) (a : K)) :
    data.SplitsCompletelyAt P := by
  letI : Field data.L := data.fieldL
  letI : NumberField data.L := data.numberFieldL
  letI : Algebra K data.L := data.algebraKL
  letI : FiniteDimensional K data.L := data.finiteDimensionalKL
  letI : IsGalois K data.L := data.isGaloisKL
  have hn : n ≠ 0 := by
    intro hn
    subst n
    simp [primitiveRoots_zero] at hroots
  let v := (FinitePlace.mk P).val
  let F := v.Completion
  letI : Fact v.IsNontrivial :=
    ⟨absolute_value_nontrivial P⟩
  letI : IsUltrametricDist F :=
    placeUltrametricDist P
  let eP : F ≃+* P.adicCompletion K :=
    placeCompletionAdic P
  obtain ⟨x, hx⟩ := hlocal
  let xF : F := eP.symm x
  have hxF : xF ^ n = completionEmbedding v (a : K) := by
    calc
      xF ^ n = eP.symm (x ^ n) := by
        exact (map_pow eP.symm.toRingHom x n).symm
      _ = eP.symm (algebraMap K (P.adicCompletion K) (a : K)) := by
        rw [hx]
      _ = completionEmbedding v (a : K) := by
        apply eP.injective
        rw [eP.apply_symm_apply]
        exact (finite_place_adic P (a : K)).symm
  let zetaF : F := completionEmbedding v hroots.choose
  have hzetaF : IsPrimitiveRoot zetaF n :=
    ((mem_primitiveRoots (Nat.pos_of_ne_zero hn)).mp hroots.choose_spec).map_of_injective
      (completionEmbedding v).injective
  let q : F[X] := X ^ n - C (completionEmbedding v (a : K))
  have hqsplit : q.Splits := by
    exact radical_splits_root hzetaF hxF
  have hq0 : q ≠ 0 :=
    (monic_X_pow_sub_C (completionEmbedding v (a : K)) hn).ne_zero
  intro w
  letI : Algebra F w.1.Completion :=
    (completionLies v w.1 w.2).toAlgebra
  letI : FiniteDimensional F w.1.Completion :=
    placeCompletionDimensional v w
  let y : w.1.Completion := completionEmbedding w.1 data.root
  have hbase (c : K) :
      algebraMap F w.1.Completion (completionEmbedding v c) =
        completionEmbedding w.1 (algebraMap K data.L c) := by
    exact RingHom.congr_fun (completion_lies_comp v w.1 w.2) c
  have hy : y ^ n =
      algebraMap F w.1.Completion (completionEmbedding v (a : K)) := by
    calc
      y ^ n = completionEmbedding w.1 (data.root ^ n) := by
        rw [map_pow]
      _ = completionEmbedding w.1 (algebraMap K data.L (a : K)) := by
        rw [data.root_pow]
      _ = algebraMap F w.1.Completion (completionEmbedding v (a : K)) :=
        (hbase (a : K)).symm
  have hqeval : aeval y q = 0 := by
    simp [q, hy]
  have hmindvd : minpoly F y ∣ q :=
    minpoly.dvd F y hqeval
  have hminsplit : (minpoly F y).Splits :=
    hqsplit.of_dvd hq0 hmindvd
  have hyint : IsIntegral F y := IsIntegral.of_finite F y
  have hmindeg : (minpoly F y).natDegree = 1 :=
    hminsplit.natDegree_eq_one_of_irreducible (minpoly.irreducible hyint)
  have hgen : Algebra.adjoin K {data.root} = ⊤ := by
    have h := congrArg IntermediateField.toSubalgebra data.adjoin_root_top
    simpa [IntermediateField.adjoin_toSubalgebra_of_isAlgebraic
      (fun z _ ↦ IsAlgebraic.of_finite K z)] using h
  let ew := completionAdjoinMinpoly v data.root
    hgen w
  calc
    Module.finrank F w.1.Completion =
        Module.finrank F (AdjoinRoot (minpoly F y)) :=
      ew.toLinearEquiv.finrank_eq.symm
    _ = (minpoly F y).natDegree := by
      let pbw := AdjoinRoot.powerBasis
        (show minpoly F y ≠ 0 from (minpoly.irreducible hyint).ne_zero)
      rw [pbw.finrank, AdjoinRoot.powerBasis_dim]
    _ = 1 := hmindeg

end

end Towers.CField.LGPowers
