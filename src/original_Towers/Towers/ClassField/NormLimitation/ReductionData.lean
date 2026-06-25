import Towers.ClassField.NormLimitation.ExistenceInterface
import Towers.ClassField.NormLimitation.NormLimitationBridge

/-!
# Chapter VII, Section 9, Theorem 9.5

The existence theorem is proved by strong induction on the index.  For a
proper open subgroup `U`, the prime-index construction of Lemma 9.3 (after
adjoining the required root of unity) supplies a finite overfield `K'` such
that the norm-preimage of `U` has strictly smaller index.  The induction
hypothesis applies over `K'`, and Lemma 9.4 descends the resulting norm group.
-/

namespace Towers.CField.NLimita

open NumberField
open Towers.CField.LFTheory
open Towers.CField.Ideles
open Towers.CField.Recip

noncomputable section

universe u

private abbrev CK (K : Type u) [Field K] [NumberField K] :=
  IdeleClassGroup (RingOfIntegers K) K

/-- The finite overfield produced in the proper induction step. -/
structure ReductionData
    (K : Type u) [Field K] [NumberField K]
    (U : Subgroup (CK K)) where
  K' : Type u
  fieldK' : Field K'
  numberFieldK' : NumberField K'
  algebraKK' : Algebra K K'
  finiteDimensionalKK' : FiniteDimensional K K'
  preimage_isOpen :
    letI : Field K' := fieldK'
    letI : NumberField K' := numberFieldK'
    letI : Algebra K K' := algebraKK'
    letI : FiniteDimensional K K' := finiteDimensionalKK'
    IsOpen (U.comap (canonicalIdeleNorm (K := K) (L := K')) :
      Set (CK K'))
  preimage_finiteIndex :
    letI : Field K' := fieldK'
    letI : NumberField K' := numberFieldK'
    letI : Algebra K K' := algebraKK'
    letI : FiniteDimensional K K' := finiteDimensionalKK'
    (U.comap (canonicalIdeleNorm (K := K) (L := K'))).FiniteIndex
  preimage_index_lt :
    letI : Field K' := fieldK'
    letI : NumberField K' := numberFieldK'
    letI : Algebra K K' := algebraKK'
    letI : FiniteDimensional K K' := finiteDimensionalKK'
    (U.comap (canonicalIdeleNorm (K := K) (L := K'))).index < U.index

/-- The trivial base case: the full idèle class group is the norm group of
the trivial extension. -/
def TopNormBridge : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K],
    IdeleNormGroup K (⊤ : Subgroup (CK K))

/-- The trivial subfield of the fixed separable closure, bundled as a
finite abelian subextension. -/
noncomputable def trivialSubextension
    (K : Type u) [Field K] : FASubext K := by
  let E₀ : IntermediateField K (SeparableClosure K) := ⊥
  letI : FiniteDimensional K E₀ := inferInstance
  letI : IsGalois K E₀ := inferInstance
  have hcard : Nat.card Gal(E₀/K) = 1 := by
    rw [IsGalois.card_aut_eq_finrank K E₀]
    exact
      (IntermediateField.botEquiv K
        (SeparableClosure K)).symm.toLinearEquiv.finrank_eq.symm.trans
          (Module.finrank_self K)
  letI : Subsingleton Gal(E₀/K) :=
    (Nat.card_eq_one_iff_unique.mp hcard).1
  letI : IsMulCommutative Gal(E₀/K) := inferInstance
  exact
    { finiteIntermediateField :=
        { E₀ with
          finiteDimensional := inferInstance
          isGalois := inferInstance }
      isAbelian := inferInstance }

/-- Lemma 9.1 makes the base case of the induction immediate: the full
idèle class group contains the norm group of the trivial extension. -/
theorem top_bridge_reciprocity
    (h91 : (∀ (K : Type u) [Field K] [NumberField K]
          (U V : Subgroup (IdeleClassGroup (RingOfIntegers K) K)),
          IdeleNormGroup K U → U ≤ V → IdeleNormGroup K V)) : TopNormBridge.{u} := by
  intro K _ _
  let L := trivialSubextension K
  apply h91 K (ideleClassSubgroup L) ⊤
  · exact ⟨L, rfl⟩
  · exact le_top

/-- The arithmetic prime-index reduction in the proof.  Its input explicitly
includes Lemma 9.3; its output is only the smaller-index overfield needed by
the induction, not the desired norm-group conclusion. -/
def ProperReductionBridge : Prop :=
  ExistenceStatementInterface.{u} →
  ∀ (K : Type u) [Field K] [NumberField K]
    (U : Subgroup (CK K)),
    IsOpen (U : Set (CK K)) → U.FiniteIndex → U ≠ ⊤ →
      Nonempty (ReductionData K U)

/-- Theorem VII.9.5 uses openness although the displayed sentence in the
source accidentally omits it; this is the corrected literal statement from
`ExistenceStatement`. -/
theorem reduction_induction_bridges
    (h93 : ExistenceStatementInterface.{u})
    (h94 : (∀ (K K' : Type u) [Field K] [NumberField K]
          [Field K'] [NumberField K'] [Algebra K K'] [FiniteDimensional K K']
          (U : Subgroup (CK K)),
          IsOpen (U : Set (CK K)) → U.FiniteIndex →
          IdeleNormGroup K'
            (U.comap (canonicalIdeleNorm (K := K) (L := K'))) →
          IdeleNormGroup K U))
    (htop : TopNormBridge.{u})
    (hstep : ProperReductionBridge.{u}) :
    ∀ (K : Type u) [Field K] [NumberField K]
      (U : Subgroup (CK K)),
      IsOpen (U : Set (CK K)) → U.FiniteIndex →
      IdeleNormGroup K U := by
  intro K _ _ U hUopen hUfinite
  induction hindex : U.index using Nat.strong_induction_on generalizing K with
  | h n ih =>
      by_cases htopU : U = ⊤
      · subst U
        exact htop K
      · obtain ⟨data⟩ := hstep h93 K U hUopen hUfinite htopU
        letI : Field data.K' := data.fieldK'
        letI : NumberField data.K' := data.numberFieldK'
        letI : Algebra K data.K' := data.algebraKK'
        letI : FiniteDimensional K data.K' := data.finiteDimensionalKK'
        let U' := U.comap
          (canonicalIdeleNorm (K := K) (L := data.K'))
        have hU'norm : IdeleNormGroup data.K' U' := by
          apply ih U'.index
          · simpa [hindex] using data.preimage_index_lt
          · exact data.preimage_isOpen
          · exact data.preimage_finiteIndex
          · rfl
        exact h94 K data.K' U hUopen hUfinite hU'norm

/-- The induction theorem with its base case discharged by Lemma 9.1 and
the trivial subextension. -/
theorem reduction_data
    (h91 : (∀ (K : Type u) [Field K] [NumberField K]
          (U V : Subgroup (IdeleClassGroup (RingOfIntegers K) K)),
          IdeleNormGroup K U → U ≤ V → IdeleNormGroup K V))
    (h93 : ExistenceStatementInterface.{u})
    (h94 : (∀ (K K' : Type u) [Field K] [NumberField K]
          [Field K'] [NumberField K'] [Algebra K K'] [FiniteDimensional K K']
          (U : Subgroup (CK K)),
          IsOpen (U : Set (CK K)) → U.FiniteIndex →
          IdeleNormGroup K'
            (U.comap (canonicalIdeleNorm (K := K) (L := K'))) →
          IdeleNormGroup K U))
    (hstep : ProperReductionBridge.{u}) :
    ∀ (K : Type u) [Field K] [NumberField K]
      (U : Subgroup (CK K)),
      IsOpen (U : Set (CK K)) → U.FiniteIndex →
      IdeleNormGroup K U :=
  reduction_induction_bridges
    h93 h94 (top_bridge_reciprocity h91) hstep

/-- The preceding induction theorem is the corrected source statement. -/
theorem of_induction_bridges
    (K : Type u) [Field K] [NumberField K]
    (h93 : ExistenceStatementInterface.{u})
    (h94 : (∀ (K K' : Type u) [Field K] [NumberField K]
          [Field K'] [NumberField K'] [Algebra K K'] [FiniteDimensional K K']
          (U : Subgroup (CK K)),
          IsOpen (U : Set (CK K)) → U.FiniteIndex →
          IdeleNormGroup K'
            (U.comap (canonicalIdeleNorm (K := K) (L := K'))) →
          IdeleNormGroup K U))
    (htop : TopNormBridge.{u})
    (hstep : ProperReductionBridge.{u}) :
    EveryIndexGroup K := by
  intro U hUopen hUfinite
  exact reduction_induction_bridges
    h93 h94 htop hstep K U hUopen hUfinite

end

end Towers.CField.NLimita
