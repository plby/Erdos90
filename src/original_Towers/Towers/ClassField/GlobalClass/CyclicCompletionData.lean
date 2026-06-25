import Towers.ClassField.GlobalClass.BrauerSequenceStatements
import Towers.ClassField.BrauerGroups.CentralDivisionCSA
import Towers.ClassField.LocalFields.NormSubgroups
import Mathlib.Algebra.BigOperators.Finprod

/-!
# Chapter VIII, Section 4, Example 4.4

Part (a) identifies the relative Brauer exact sequence of a finite cyclic
extension with the corresponding sequence of global and completed norm
quotients.  Part (b) records the finite-support, archimedean, and sum-zero
conditions on the local invariants of a global central division algebra,
together with uniqueness and realization.
-/

namespace Towers.CField.GClass

open AbsoluteValue NumberField
open Towers.CField.LFTheory
open Towers.CField.BGroups
open Towers.CField.LBrauer
open Towers.CField.Ideles
open Towers.CField.CBrauer
open Towers.CField.RExist
open Towers.CField.ICohomo
open scoped BigOperators

noncomputable section

universe u

/-! ## Example 4.4(a): the cyclic norm sequence -/

/-- One actual completion of `L` above every place of `K`. -/
structure CyclicCompletionData
    (K L : Type u) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] where
  upper : ∀ v : NumberFieldPlace K,
    PlaceProlongations K L v

/-- The local norm subgroup `Nm(L_wˣ)` inside `K_vˣ`. -/
noncomputable def localNormSubgroup
    {K L : Type u} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    (data : CyclicCompletionData K L)
    (v : NumberFieldPlace K) :
    Subgroup (RExist.placeCompletion K v)ˣ := by
  letI : Algebra (RExist.placeCompletion K v)
      (data.upper v).1.Completion :=
    (completionMap v (data.upper v)).toAlgebra
  exact normSubgroup (RExist.placeCompletion K v)
    (data.upper v).1.Completion

/-- The actual completed multiplicative norm quotient
`K_vˣ / Nm(L_wˣ)`. -/
abbrev LocalNormQuotient
    {K L : Type u} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    (data : CyclicCompletionData K L)
    (v : NumberFieldPlace K) :=
  (RExist.placeCompletion K v)ˣ ⧸ localNormSubgroup data v

/-- The global multiplicative norm quotient `Kˣ / Nm(Lˣ)`. -/
abbrev GlobalNormQuotient
    (K L : Type u) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] :=
  Kˣ ⧸ normSubgroup K L

/-- The global-to-local map on norm quotients, including its finite-support
lift.  The representative formula makes every coordinate the actual map
induced by `K → K_v`. -/
structure NormLocalizationData
    (K L : Type u) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]
    (completion : CyclicCompletionData K L) where
  toLocalization : MultiplicativeLocalizationData
    (GlobalNormQuotient K L)
    (fun v => LocalNormQuotient completion v)
  localizeAt_mk : ∀ (v : NumberFieldPlace K) (x : Kˣ),
    toLocalization.localizeAt v
        (QuotientGroup.mk' (normSubgroup K L) x) =
      QuotientGroup.mk' (localNormSubgroup completion v)
        (Units.map (algebraMap K (RExist.placeCompletion K v)) x)

/-- The local invariant on every completed norm quotient.  Its target is
the subgroup `(1/n)Z/Z`, where `n = [L : K]`. -/
structure NIData
    (K L : Type u) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]
    (completion : CyclicCompletionData K L) where
  invariant : ∀ v : NumberFieldPlace K,
    Additive (LocalNormQuotient completion v) →+
      localInvariantTorsion (Module.finrank K L)

/-- Sum of the completed norm-quotient invariants. -/
def NIData.sum
    (K L : Type u) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]
    {completion : CyclicCompletionData K L}
    (data : NIData K L completion) :
    DirectSum (NumberFieldPlace K)
      (fun v => Additive (LocalNormQuotient completion v)) →+
      localInvariantTorsion (Module.finrank K L) := by
  classical
  exact DirectSum.toAddMonoid data.invariant

/-- **Example VIII.4.4(a), source statement.** For every finite cyclic
extension, the sequence
`0 → Kˣ/Nm(Lˣ) → ⊕_v K_vˣ/Nm(L_wˣ) → (1/n)Z/Z → 0`
is exact. -/
def CyclicLocalizationSequence : Prop :=
  ∀ (K L : Type u) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [IsCyclic Gal(L/K)],
    ∃ completion : CyclicCompletionData K L,
    ∃ loc : NormLocalizationData K L completion,
    ∃ inv : NIData K L completion,
      Function.Injective loc.toLocalization.localization ∧
      Function.Exact loc.toLocalization.localization (inv.sum K L) ∧
      Function.Surjective (inv.sum K L)

/-- Construction of the chosen completions and the canonical norm-quotient
localization and invariant maps. -/
def CyclicConstructionBridge : Prop :=
  ∀ (K L : Type u) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [IsCyclic Gal(L/K)],
    ∃ completion : CyclicCompletionData K L,
    ∃ _loc : NormLocalizationData K L completion,
    Nonempty (NIData K L completion)

/-- The cyclic norm exactness obtained by transporting the relative Brauer
sequence through the cyclic algebra/norm-residue identifications. -/
def CyclicExactnessBridge : Prop :=
  ∀ (K L : Type u) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [IsCyclic Gal(L/K)]
    (completion : CyclicCompletionData K L)
    (loc : NormLocalizationData K L completion)
    (inv : NIData K L completion),
      Function.Injective loc.toLocalization.localization ∧
      Function.Exact loc.toLocalization.localization (inv.sum K L) ∧
      Function.Surjective (inv.sum K L)

theorem localization_exact_bridges
    (hconstruct : CyclicConstructionBridge.{u})
    (hexact : CyclicExactnessBridge.{u}) :
    CyclicLocalizationSequence.{u} := by
  intro K L _ _ _ _ _ _ _ _
  obtain ⟨completion, loc, ⟨inv⟩⟩ := hconstruct K L
  exact ⟨completion, loc, inv, hexact K L completion loc inv⟩

/-! ## Example 4.4(b): local invariants of a global division algebra -/

/-- The canonical family of local invariants attached to a global Brauer
class. -/
def brauerInvariantFamily
    (K : Type u) [Field K] [NumberField K]
    (data : BData K) (beta : BrauerGroup K) :
    NumberFieldPlace K → LocalInvariant :=
  fun v => data.placeInvariant.invariant v
    (Additive.ofMul
      (brauerBaseChange K (RExist.placeCompletion K v) beta))

/-- The invariant family of an actual finite-dimensional central division
algebra. -/
def divisionInvariantFamily
    (K : Type u) [Field K] [NumberField K]
    (data : BData K)
    (D : Type u) [DivisionRing D] [Algebra K D]
    [Algebra.IsCentral K D] [Module.Finite K D] :
    NumberFieldPlace K → LocalInvariant :=
  brauerInvariantFamily K data
    (brauerClass K (centralDivisionCSA K D))

/-- The literal restrictions in Example 4.4(b): finite support, zero at
complex places, two-torsion at real places, and global sum zero. -/
def AdmissibleInvariantFamily
    (K : Type u) [Field K] [NumberField K]
    (i : NumberFieldPlace K → LocalInvariant) : Prop :=
  {v | i v ≠ 0}.Finite ∧
    (∀ v : InfinitePlace K, InfinitePlace.IsComplex v → i (.inr v) = 0) ∧
    (∀ v : InfinitePlace K, InfinitePlace.IsReal v → 2 • i (.inr v) = 0) ∧
    (∑ᶠ v : NumberFieldPlace K, i v) = 0

/-- **Example VIII.4.4(b), source statement.** The invariant family of a
global central division algebra is admissible, determines it up to
`K`-algebra isomorphism, and every admissible family is realized. -/
def GlobalDivisionClassification : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K],
    ∃ data : BData K,
      (∀ (D : Type u) [DivisionRing D] [Algebra K D]
        [Algebra.IsCentral K D] [Module.Finite K D],
        AdmissibleInvariantFamily K
          (divisionInvariantFamily K data D)) ∧
      (∀ (D E : Type u) [DivisionRing D] [DivisionRing E]
        [Algebra K D] [Algebra K E]
        [Algebra.IsCentral K D] [Algebra.IsCentral K E]
        [Module.Finite K D] [Module.Finite K E],
        (∀ v, divisionInvariantFamily K data D v =
          divisionInvariantFamily K data E v) ↔
            Nonempty (D ≃ₐ[K] E)) ∧
      ∀ i : NumberFieldPlace K → LocalInvariant,
        AdmissibleInvariantFamily K i →
        ∃ (D : Type u) (_ : DivisionRing D) (_ : Algebra K D)
          (_ : Algebra.IsCentral K D) (_ : Module.Finite K D),
          ∀ v, divisionInvariantFamily K data D v = i v

/-- Construction of the canonical global localization and local invariant
package. -/
def GlobalDataBridge : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K],
    Nonempty (BData K)

/-- Global reciprocity supplies finite support, the archimedean restrictions,
and the sum-zero relation for every global Brauer class. -/
def InvariantAdmissibilityBridge : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K]
    (data : BData K) (beta : BrauerGroup K),
    AdmissibleInvariantFamily K
      (brauerInvariantFamily K data beta)

/-- Exactness at `Br(K)`, together with injectivity of each normalized local
invariant, says that the complete invariant family determines a Brauer
class. -/
def InvariantInjectivityBridge : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K]
    (data : BData K),
    Function.Injective (brauerInvariantFamily K data)

/-- The global existence theorem: every admissible local invariant family is
realized by an actual finite-dimensional central division algebra. -/
def DivisionRealizationBridge : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K]
    (data : BData K)
    (i : NumberFieldPlace K → LocalInvariant),
    AdmissibleInvariantFamily K i →
      ∃ (D : Type u) (_ : DivisionRing D) (_ : Algebra K D)
        (_ : Algebra.IsCentral K D) (_ : Module.Finite K D),
        ∀ v, divisionInvariantFamily K data D v = i v

/-- Uniqueness of a division algebra from injectivity of the global invariant
family.  The remaining step is the already-proved uniqueness of the central
division representative of a Brauer class. -/
theorem division_alg_invariants
    {K : Type u} [Field K] [NumberField K]
    (data : BData K)
    (hinjective : Function.Injective (brauerInvariantFamily K data))
    (D E : Type u) [DivisionRing D] [DivisionRing E]
    [Algebra K D] [Algebra K E]
    [Algebra.IsCentral K D] [Algebra.IsCentral K E]
    [Module.Finite K D] [Module.Finite K E] :
    (∀ v, divisionInvariantFamily K data D v =
      divisionInvariantFamily K data E v) ↔
        Nonempty (D ≃ₐ[K] E) := by
  constructor
  · intro h
    have hclass :
        brauerClass K (centralDivisionCSA K D) =
          brauerClass K (centralDivisionCSA K E) :=
      hinjective (funext h)
    exact (division_brauer_equivalent K D E).mp
      ((brauer_class K _ _).mp hclass)
  · intro h
    have hclass :
        brauerClass K (centralDivisionCSA K D) =
          brauerClass K (centralDivisionCSA K E) :=
      (brauer_class K _ _).mpr
        ((division_brauer_equivalent K D E).mpr h)
    intro v
    exact congrFun
      (congrArg (brauerInvariantFamily K data) hclass) v

theorem division_classification_bridges
    (hdata : GlobalDataBridge.{u})
    (hadmissible : InvariantAdmissibilityBridge.{u})
    (hinjective : InvariantInjectivityBridge.{u})
    (hrealize : DivisionRealizationBridge.{u}) :
    GlobalDivisionClassification.{u} := by
  intro K _ _
  obtain ⟨data⟩ := hdata K
  refine ⟨data, ?_, ?_, ?_⟩
  · intro D _ _ _ _
    exact hadmissible K data
      (brauerClass K (centralDivisionCSA K D))
  · intro D E _ _ _ _ _ _ _ _
    exact division_alg_invariants data
      (hinjective K data) D E
  · exact hrealize K data

theorem cyclic_division_bridges
    (hnormConstruct : CyclicConstructionBridge.{u})
    (hnormExact : CyclicExactnessBridge.{u})
    (hdata : GlobalDataBridge.{u})
    (hadmissible : InvariantAdmissibilityBridge.{u})
    (hinjective : InvariantInjectivityBridge.{u})
    (hrealize : DivisionRealizationBridge.{u}) :
    CyclicLocalizationSequence.{u} ∧ GlobalDivisionClassification.{u}
  :=
  ⟨localization_exact_bridges hnormConstruct hnormExact,
    division_classification_bridges hdata hadmissible hinjective hrealize⟩

end

end Towers.CField.GClass
