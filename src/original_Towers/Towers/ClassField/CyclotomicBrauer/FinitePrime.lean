import Towers.NumberTheory.Galois.PlaceCompletionDegree
import Towers.ClassField.BrauerGroups.BaseChangeTower
import Towers.ClassField.Ideles.GlobalPlace
import Towers.ClassField.CyclotomicBrauer.Cyclotomic
import Towers.ClassField.CyclotomicBrauer.IdeleClassRepresentation

/-!
# Chapter VII, Section 7, Proposition 7.2

Every Brauer class over a number field is split by a finite cyclic
cyclotomic extension.  The conclusion is stated using the actual
`BrauerGroup` and `brauerBaseChange`; its identity element corresponds to
zero in Milne's additive `H²` notation.

This file packages the existential extension and proves the formal
combination of the two arithmetic inputs in the printed proof:

* finite support of the local invariants, their common annihilator, and the
  local invariant base-change formula;
* the cyclic cyclotomic extension with prescribed local-degree divisibility
  constructed in Lemma 7.3.

These inputs remain narrow bridges: the local-invariant calculation, the
global-to-local injectivity of Theorem 7.1, and Lemma 7.3's extension
construction.  Scalar extension through a field tower is handled by the
existing concrete Brauer base-change maps.
-/

namespace Towers.CField.CBrauer

open AbsoluteValue IsDedekindDomain NumberField
open Towers.NumberTheory.Milne
open Towers.CField.BGroups
open Towers.CField.Ideles
open Towers.CField.ICohomo

noncomputable section

universe u

/-- A finite prime of a number field, named locally to avoid depending on
the `SUnits` abbreviation from Section 6. -/
abbrev finitePrime
    (K : Type u) [Field K] [NumberField K] :=
  HeightOneSpectrum (NumberField.RingOfIntegers K)

/-- The underlying finite Galois number-field extension used in Proposition
7.2.  Putting the instances in data fields lets the existential extension
live in the same universe as the base field. -/
structure FEData
    (K : Type u) [Field K] [NumberField K] where
  L : Type u
  fieldL : Field L
  numberFieldL : NumberField L
  algebraKL : Algebra K L
  finiteDimensionalKL : FiniteDimensional K L
  isGaloisKL : IsGalois K L

/-- The extension is cyclic and cyclotomic in Milne's sense: its Galois
group is cyclic and it embeds over `K` into a genuine cyclotomic number
field `C = K[ζ]`. -/
def FEData.IsCyclicCyclotomic
    {K : Type u} [Field K] [NumberField K]
    (data : FEData K) : Prop :=
  letI : Field data.L := data.fieldL
  letI : NumberField data.L := data.numberFieldL
  letI : Algebra K data.L := data.algebraKL
  letI : FiniteDimensional K data.L := data.finiteDimensionalKL
  letI : IsGalois K data.L := data.isGaloisKL
  IsCyclic Gal(data.L/K) ∧
    ∃ (conductor : ℕ) (C : Type u)
      (_ : Field C) (_ : NumberField C)
      (_ : Algebra K C) (_ : Algebra data.L C)
      (_ : IsScalarTower K data.L C)
      (_ : IsCyclotomicExtension {conductor} K C),
      True

/-- The total-complexity condition supplied by Lemma 7.3.  It kills the
possible invariants at real places. -/
def FEData.IsTotallyComplex
    {K : Type u} [Field K] [NumberField K]
    (data : FEData K) : Prop :=
  letI : Field data.L := data.fieldL
  NumberField.IsTotallyComplex data.L

/-- The actual local-degree divisibility condition in Lemma 7.3.  For every
selected finite prime, one prolongation to `L` is chosen and the degree of
the induced extension of completions is divisible by `m`. -/
def FEData.LocalDegreesDvd
    {K : Type u} [Field K] [NumberField K]
    (data : FEData K)
    (S : Finset (finitePrime K)) (m : ℕ) : Prop :=
  letI : Field data.L := data.fieldL
  letI : NumberField data.L := data.numberFieldL
  letI : Algebra K data.L := data.algebraKL
  letI : FiniteDimensional K data.L := data.finiteDimensionalKL
  letI : IsGalois K data.L := data.isGaloisKL
  ∃ w : ∀ P : S,
      CompletionPlacesAbove (L := data.L) (FinitePlace.mk P.1).val,
    ∀ P : S,
      letI : Algebra (FinitePlace.mk P.1).val.Completion
          (w P).1.Completion :=
        (completionLies
          (FinitePlace.mk P.1).val (w P).1 (w P).2).toAlgebra
      m ∣ Module.finrank
        (FinitePlace.mk P.1).val.Completion (w P).1.Completion

/-- The actual assertion that `data.L` splits the Brauer class `beta`.
The identity `1` is zero in the additive `H²` convention of the source. -/
def FEData.Splits
    {K : Type u} [Field K] [NumberField K]
    (beta : BrauerGroup.{u, u} K)
    (data : FEData K) : Prop :=
  letI : Field data.L := data.fieldL
  letI : Algebra K data.L := data.algebraKL
  brauerBaseChange K data.L beta = 1

/-- The base-changed class is split at every completion of the extension
field.  This is the conclusion obtained from finite support, the local
invariant base-change formula, and the degree divisibilities in Lemma 7.3,
before Theorem 7.1 is applied. -/
def FEData.SplitsEveryComplete
    {K : Type u} [Field K] [NumberField K]
    (beta : BrauerGroup.{u, u} K)
    (data : FEData K) : Prop :=
  letI : Field data.L := data.fieldL
  letI : NumberField data.L := data.numberFieldL
  letI : Algebra K data.L := data.algebraKL
  ∀ place : NumberFieldPlace data.L,
    brauerBaseChange data.L (placeCompletion data.L place)
      (brauerBaseChange K data.L beta) = 1

/-- The existential output of Proposition 7.2: a finite cyclic cyclotomic
number-field extension whose actual Brauer base change kills `beta`. -/
structure SplittingExtensionData
    (K : Type u) [Field K] [NumberField K]
    (beta : BrauerGroup.{u, u} K) where
  extension : FEData K
  isCyclicCyclotomic : extension.IsCyclicCyclotomic
  splits : extension.Splits beta

/-- Scalar extension of Brauer classes is transitive: once a class is split
by `E`, it remains split over every field above `E`. -/
theorem brauer_change_tower
    (K E L : Type u) [Field K] [Field E] [Field L]
    [Algebra K E] [Algebra K L] [Algebra E L]
    [IsScalarTower K E L]
    (beta : BrauerGroup.{u, u} K)
    (hsplit : brauerBaseChange K E beta = 1) :
    brauerBaseChange K L beta = 1 := by
  rw [← base_change_tower K E L beta, hsplit, map_one]

/-- The precise local consequence of finite support and the local invariant
formula used in Proposition 7.2.

For `beta`, it supplies a finite set `S` of finite primes and one positive
integer `m` annihilating all relevant local invariants.  Any totally complex
finite extension whose completion degrees over `S` are divisible by `m`
then kills the base change of `beta` at every completion of the extension
field.  The passage from this local conclusion to global splitting is kept
separate as Theorem 7.1 below. -/
def SupportInvariantBridge : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K]
    (beta : BrauerGroup.{u, u} K),
    ∃ (S : Finset (finitePrime K)) (m : ℕ),
      0 < m ∧
        ∀ data : FEData K,
          data.IsCyclicCyclotomic →
          data.IsTotallyComplex →
          data.LocalDegreesDvd S m →
          data.SplitsEveryComplete beta

/-- **Theorem VII.7.1, Brauer-group consequence used in Proposition 7.2.**
A Brauer class over a number field which is split at every completion is
already the identity class. -/
def GlobalBrauerBridge : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K]
    (beta : BrauerGroup.{u, u} K),
    (∀ place : NumberFieldPlace K,
      brauerBaseChange K (placeCompletion K place) beta = 1) →
      beta = 1

/-- **Lemma VII.7.3, exact construction input.**  Given the finite set and
positive annihilator, it produces a totally complex cyclic cyclotomic
extension with the required divisibility of the actual completion degrees.
No Brauer class or splitting conclusion occurs in this bridge. -/
def FinitePrime : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K]
    (S : Finset (finitePrime K)) (m : ℕ),
    0 < m →
      ∃ data : FEData K,
        data.IsCyclicCyclotomic ∧
          data.IsTotallyComplex ∧
          data.LocalDegreesDvd S m

/-- Proposition 7.2 follows by applying Lemma 7.3 to the common annihilator
of the finitely supported local invariants. -/
theorem prime_statement_bridges
    (hlocal : SupportInvariantBridge.{u})
    (hglobal : GlobalBrauerBridge.{u})
    (hFinitePrimeStatement : FinitePrime.{u}) :
    (∀ (K : Type u) [Field K] [NumberField K]
          (beta : BrauerGroup.{u, u} K),
          Nonempty (SplittingExtensionData K beta)) := by
  intro K _ _ beta
  obtain ⟨S, m, hm, hkill⟩ := hlocal K beta
  obtain ⟨data, hcyclic, hcomplex, hdegrees⟩ :=
    hFinitePrimeStatement K S m hm
  refine ⟨⟨data, hcyclic, ?_⟩⟩
  letI : Field data.L := data.fieldL
  letI : NumberField data.L := data.numberFieldL
  letI : Algebra K data.L := data.algebraKL
  exact hglobal data.L (brauerBaseChange K data.L beta)
    (hkill data hcyclic hcomplex hdegrees)

end

end Towers.CField.CBrauer
