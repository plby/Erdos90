import Submission.ClassField.LocalBrauer.LocalInvariantTorsion
import Submission.ClassField.Ideles.GlobalPlace
import Submission.ClassField.CyclotomicBrauer.LocalizationStatements
import Submission.ClassField.ReciprocityExistence.PlaceCompletion
import Submission.NumberTheory.Completions.TensorDecomposition

/-!
# The global Brauer invariant sequences

These predicates state Theorem VIII.4.2 and Corollary VIII.4.3 as exact
sequences.  Localization data includes the coordinate maps and the theorem
that every global Brauer class has finite local support.

For a non-Galois finite extension, the local relative term must mean the
kernel of restriction to the product of *all* completions above a place.  The
generic relative statement supports that corrected formulation.  A separate
specialization records the simpler single-completion notation valid for a
finite Galois extension.
-/

namespace Submission.CField.GClass

open Submission.CField.BGroups
open Submission.CField.LBrauer
open Submission.CField.Ideles
open Submission.CField.CBrauer

noncomputable section

universe u v w

private abbrev absolutePlaceCompletion
    (K : Type u) [Field K] [NumberField K]
    (v : NumberFieldPlace K) :=
  Submission.CField.RExist.placeCompletion K v

/-- The finite-support direct sum of the Brauer groups of all completions. -/
abbrev BrauerDirectSum
    (K : Type u) [Field K] [NumberField K] :=
  DirectSum (NumberFieldPlace K)
    (fun place ↦ Additive (BrauerGroup (Ideles.placeCompletion K place)))

/-- The canonical localization package expected in Theorem VIII.4.2. -/
abbrev GlobalLocalizationData
    (K : Type u) [Field K] [NumberField K] :=
  MultiplicativeLocalizationData (BrauerGroup K)
    (fun place : NumberFieldPlace K ↦
      BrauerGroup (Ideles.placeCompletion K place))

/-- The coordinates of the global localization package are the actual Brauer
scalar-extension maps to the completions. -/
def GlobalBrauerLocalization
    (K : Type u) [Field K] [NumberField K]
    (loc : GlobalLocalizationData K) : Prop :=
  ∀ (x : BrauerGroup K) (place : NumberFieldPlace K),
    loc.localizeAt place x =
      brauerBaseChange K (Ideles.placeCompletion K place) x

/-- Sum a finite-support family using the specified invariant at each place. -/
def sumLocalInvariant
    (K : Type u) [Field K] [NumberField K]
    (placeInvariant : ∀ place : NumberFieldPlace K,
      Additive (BrauerGroup (Ideles.placeCompletion K place)) →+
        LocalInvariant) :
    BrauerDirectSum K →+ LocalInvariant := by
  classical
  exact DirectSum.toAddMonoid placeInvariant

/-- **Theorem VIII.4.2.** For a number field `K`, localization followed by
the sum of local invariants gives the exact sequence
`0 → Br(K) → ⊕_v Br(K_v) → Q/Z → 0`. -/
def GlobalBrauerSequence
    (K : Type u) [Field K] [NumberField K]
    (loc : GlobalLocalizationData K)
    (placeInvariant : ∀ place : NumberFieldPlace K,
      Additive (BrauerGroup (Ideles.placeCompletion K place)) →+
        LocalInvariant) : Prop :=
  GlobalBrauerLocalization K loc ∧
    Function.Injective loc.localization ∧
    Function.Exact loc.localization (sumLocalInvariant K placeInvariant) ∧
    Function.Surjective (sumLocalInvariant K placeInvariant)

/-- **VIII.4.2 implies the localization injection of VII.7.1.**  Injectivity
of the global-to-local Brauer map is the first nontrivial exactness assertion
in the global invariant sequence. -/
theorem implies_localization_injectivity
    (K : Type u) [Field K] [NumberField K]
    (loc : GlobalLocalizationData K)
    (placeInvariant : ∀ place : NumberFieldPlace K,
      Additive (BrauerGroup (Ideles.placeCompletion K place)) →+
        LocalInvariant)
    (h : GlobalBrauerSequence K loc placeInvariant) :
    BrauerLocalizationInjectivity loc :=
  h.2.1

/-- `n₀` is the least common multiple of a possibly infinite, but bounded,
family of positive local degrees. -/
def LocalLCM {index : Type u}
    (localDegree : index → ℕ) (n₀ : ℕ) : Prop :=
  0 < n₀ ∧ (∀ v, 0 < localDegree v) ∧
    (∀ v, localDegree v ∣ n₀) ∧
    ∀ m, (∀ v, localDegree v ∣ m) → n₀ ∣ m

/-- **Corollary VIII.4.3, corrected general form.** Here `GlobalRelative` is
`Br(L/K)`, while `LocalRelative v` is the kernel of
`Br(K_v) → ∏_{w|v} Br(L_w)`.  For a Galois extension this kernel is the
relative Brauer group of any one completion above `v`. -/
def RelativeGlobalSequence
    {index : Type u} {GlobalRelative : Type v}
    (LocalRelative : index → Type w)
    [CommGroup GlobalRelative]
    [∀ place, CommGroup (LocalRelative place)]
    (localDegree : index → ℕ) (n₀ : ℕ)
    (loc : MultiplicativeLocalizationData GlobalRelative LocalRelative)
    (sumInvariant :
      DirectSum index (fun place ↦ Additive (LocalRelative place)) →+
        localInvariantTorsion n₀) : Prop :=
  LocalLCM localDegree n₀ ∧
    Function.Injective loc.localization ∧
    Function.Exact loc.localization sumInvariant ∧
    Function.Surjective sumInvariant

/-- The single-completion form of Corollary VIII.4.3 for a finite Galois
extension.  The local fields and localization package include chosen places
above each base place. -/
def BrauerInvariantSequence
    {index : Type u} {K L : Type v}
    [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (Kv Lv : index → Type v)
    [∀ place, Field (Kv place)] [∀ place, Field (Lv place)]
    [∀ place, Algebra (Kv place) (Lv place)]
    [∀ place, FiniteDimensional (Kv place) (Lv place)]
    [∀ place, IsGalois (Kv place) (Lv place)]
    (localDegree : index → ℕ) (n₀ : ℕ)
    (loc : MultiplicativeLocalizationData
      (relativeBrauerGroup K L)
      (fun place ↦ relativeBrauerGroup (Kv place) (Lv place)))
    (sumInvariant : DirectSum index
        (fun place ↦ Additive (relativeBrauerGroup (Kv place) (Lv place))) →+
      localInvariantTorsion n₀) : Prop :=
  RelativeGlobalSequence
    (fun place ↦ relativeBrauerGroup (Kv place) (Lv place))
    localDegree n₀ loc sumInvariant

/-! ## Literal source statements -/

open AbsoluteValue
open NumberField
open Submission.NumberTheory.Milne
open Submission.CField.ICohomo
open Submission.CField.RExist

/-- **Theorem VIII.4.2 (source statement).** The localization data, local
invariants, and finite-support theorem are existential rather than extra
hypotheses.  `BData` fixes their canonical normalization. -/
def GlobalLocalizationSequence : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K],
    ∃ data : BData K,
      Function.Injective data.localization.localization ∧
      Function.Exact data.localization.localization
        (BData.sumInvariant K data) ∧
      Function.Surjective (BData.sumInvariant K data)

/-- Construction of the canonical local invariant maps and the finite-support
global localization map. -/
def BrauerConstructionBridge : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K],
    Nonempty (BData K)

/-- The exactness input in the fundamental global Brauer sequence. -/
def ExactnessBridge : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K]
    (data : BData K),
    Function.Injective data.localization.localization ∧
    Function.Exact data.localization.localization
      (BData.sumInvariant K data) ∧
    Function.Surjective (BData.sumInvariant K data)

/-- Theorem 4.2 from construction of its canonical maps and exactness. -/
theorem global_localization_bridges
    (hdata : BrauerConstructionBridge.{u})
    (hexact : ExactnessBridge.{u}) :
    GlobalLocalizationSequence.{u} := by
  intro K _ _
  obtain ⟨data⟩ := hdata K
  exact ⟨data, hexact K data⟩

/-- The normalized absolute value underlying a finite or infinite number-field
place.  Its completion is definitionally the completion model used by
`BData`. -/
def globalSequenceStatements
    (K : Type u) [Field K] [NumberField K] :
    NumberFieldPlace K → AbsoluteValue K ℝ
  | .inl P => (FinitePlace.mk P).val
  | .inr v => v.1

/-- All prolongations to `L` of one place of `K`.  Keeping every
prolongation is essential for the non-Galois statement of Corollary 4.3. -/
abbrev PlaceProlongations
    (K L : Type u) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    (v : NumberFieldPlace K) :=
  ICohomo.CompletionPlacesAbove (L := L)
    (globalSequenceStatements K v)

/-- The canonical embedding between the actual completions belonging to
`w | v`. -/
noncomputable def completionMap
    {K L : Type u} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    (v : NumberFieldPlace K)
    (w : PlaceProlongations K L v) :
    absolutePlaceCompletion K v →+* w.1.Completion := by
  cases v with
  | inl P =>
      exact completionLies (FinitePlace.mk P).val w.1 w.2
  | inr v =>
      exact completionLies v.1 w.1 w.2

/-- The completed scalar-extension map on Brauer groups. -/
noncomputable def globalStatementsChange
    {K L : Type u} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    (v : NumberFieldPlace K)
    (w : PlaceProlongations K L v) :
    BrauerGroup (absolutePlaceCompletion K v) →*
      BrauerGroup w.1.Completion := by
  letI : Algebra (absolutePlaceCompletion K v) w.1.Completion :=
    (completionMap v w).toAlgebra
  exact brauerBaseChange (absolutePlaceCompletion K v) w.1.Completion

/-- The local relative Brauer group for a possibly non-Galois extension:
the kernel of restriction to *every* completion above `v`. -/
noncomputable def localBrauerSubgroup
    (K L : Type u) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    (v : NumberFieldPlace K) :
    Subgroup (BrauerGroup (absolutePlaceCompletion K v)) where
  carrier beta := ∀ w : PlaceProlongations K L v,
    globalStatementsChange v w beta = 1
  one_mem' := fun w => map_one (globalStatementsChange v w)
  mul_mem' := by
    intro a b ha hb w
    rw [map_mul, ha w, hb w, one_mul]
  inv_mem' := by
    intro a ha w
    simpa using congrArg Inv.inv (ha w)

/-- The actual local relative Brauer group occurring in Corollary 4.3. -/
abbrev LocalRelativeBrauer
    (K L : Type u) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    (v : NumberFieldPlace K) :=
  localBrauerSubgroup K L v

/-- The degree `[L_w : K_v]` of an actual completed extension. -/
noncomputable def globalStatementsDegree
    {K L : Type u} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    (v : NumberFieldPlace K)
    (w : PlaceProlongations K L v) : ℕ := by
  letI : Algebra (absolutePlaceCompletion K v) w.1.Completion :=
    (completionMap v w).toAlgebra
  exact Module.finrank (absolutePlaceCompletion K v) w.1.Completion

/-- For a non-Galois extension, the local relative kernel is killed by the
greatest common divisor of the degrees of all completions above `v`.  In the
Galois case these degrees are equal, recovering the source's `n_v`. -/
def IsLocalDegree
    {K L : Type u} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    (v : NumberFieldPlace K) (n : ℕ) : Prop :=
  0 < n ∧
    (∀ w : PlaceProlongations K L v,
      n ∣ globalStatementsDegree v w) ∧
    ∀ m : ℕ,
      (∀ w : PlaceProlongations K L v,
        m ∣ globalStatementsDegree v w) → m ∣ n

/-- A relative localization package is canonical when each coordinate is
the scalar extension of the underlying global Brauer class. -/
def IsCanonicalLocalization
    (K L : Type u) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    (loc : MultiplicativeLocalizationData
      (relativeBrauerGroup K L)
      (fun v => LocalRelativeBrauer K L v)) : Prop :=
  ∀ (beta : relativeBrauerGroup K L) (v : NumberFieldPlace K),
    ((loc.localizeAt v beta : LocalRelativeBrauer K L v) :
        BrauerGroup (absolutePlaceCompletion K v)) =
      brauerBaseChange K (absolutePlaceCompletion K v)
        (beta : BrauerGroup K)

/-- The local invariant maps restricted to the relative kernels, with their
values exhibited in the `n₀`-torsion subgroup of `Q/Z`. -/
structure IData
    (K L : Type u) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    (global : BData K) (n₀ : ℕ) where
  invariant : ∀ v : NumberFieldPlace K,
    Additive (LocalRelativeBrauer K L v) →+
      localInvariantTorsion n₀
  coe_invariant : ∀ (v : NumberFieldPlace K)
    (beta : LocalRelativeBrauer K L v),
    ((invariant v (Additive.ofMul beta) : localInvariantTorsion n₀) :
        LocalInvariant) =
      global.placeInvariant.invariant v
        (Additive.ofMul
          (beta : BrauerGroup (absolutePlaceCompletion K v)))

/-- Sum of the canonical restricted local invariants. -/
def IData.sum
    (K L : Type u) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    {global : BData K} {n₀ : ℕ}
    (data : IData K L global n₀) :
    DirectSum (NumberFieldPlace K)
      (fun v => Additive (LocalRelativeBrauer K L v)) →+
      localInvariantTorsion n₀ := by
  classical
  exact DirectSum.toAddMonoid data.invariant

/-- **Corollary VIII.4.3 (source statement).** This is the literal assertion
for every finite extension of number fields.  The local group uses all
completions above a place; `n_v` is consequently their degree gcd, and `n₀`
is the lcm of these local indices. -/
def LocalizationExactSequence : Prop :=
  ∀ (K L : Type u) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L],
    ∃ localDegree : NumberFieldPlace K → ℕ,
      (∀ v, IsLocalDegree (K := K) (L := L) v (localDegree v)) ∧
    ∃ n₀ : ℕ, LocalLCM localDegree n₀ ∧
    ∃ global : BData K,
    ∃ loc : MultiplicativeLocalizationData
      (relativeBrauerGroup K L)
      (fun v => LocalRelativeBrauer K L v),
    ∃ inv : IData K L global n₀,
      IsCanonicalLocalization K L loc ∧
      Function.Injective loc.localization ∧
      Function.Exact loc.localization (inv.sum K L) ∧
      Function.Surjective (inv.sum K L)

/-- Construction of the actual local kernels, their degree gcd/lcm, and the
finite-support relative localization and invariant maps. -/
def LocalConstructionBridge : Prop :=
  ∀ (K L : Type u) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]
    (global : BData K),
    ∃ localDegree : NumberFieldPlace K → ℕ,
      (∀ v, IsLocalDegree (K := K) (L := L) v (localDegree v)) ∧
    ∃ n₀ : ℕ, LocalLCM localDegree n₀ ∧
    ∃ loc : MultiplicativeLocalizationData
      (relativeBrauerGroup K L)
      (fun v => LocalRelativeBrauer K L v),
    ∃ _inv : IData K L global n₀,
      IsCanonicalLocalization K L loc

/-- The snake-lemma exactness step after the canonical relative maps have
been constructed.  Its explicit `GlobalLocalizationSequence` argument records
the two fundamental exact sequences used in the printed proof. -/
def SnakeLemmaBridge : Prop :=
  GlobalLocalizationSequence.{u} →
  ∀ (K L : Type u) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]
    (localDegree : NumberFieldPlace K → ℕ) (n₀ : ℕ)
    (global : BData K)
    (loc : MultiplicativeLocalizationData
      (relativeBrauerGroup K L)
      (fun v => LocalRelativeBrauer K L v))
    (inv : IData K L global n₀),
    (∀ v, IsLocalDegree (K := K) (L := L) v (localDegree v)) →
    LocalLCM localDegree n₀ →
    IsCanonicalLocalization K L loc →
      Function.Injective loc.localization ∧
      Function.Exact loc.localization (inv.sum K L) ∧
      Function.Surjective (inv.sum K L)

/-- Corollary 4.3 from Theorem 4.2, construction of its canonical relative
maps, and the snake-lemma exactness step. -/
theorem localization_sequence_bridges
    (h42 : GlobalLocalizationSequence.{u})
    (hconstruct : LocalConstructionBridge.{u})
    (hsnake : SnakeLemmaBridge.{u}) :
    LocalizationExactSequence.{u} := by
  intro K L _ _ _ _ _ _
  obtain ⟨global, _⟩ := h42 K
  obtain ⟨localDegree, hdegree, n₀, hn₀, loc, inv, hloc⟩ :=
    hconstruct K L global
  exact ⟨localDegree, hdegree, n₀, hn₀, global, loc, inv, hloc,
    hsnake h42 K L localDegree n₀ global loc inv hdegree hn₀ hloc⟩

end

end Submission.CField.GClass
