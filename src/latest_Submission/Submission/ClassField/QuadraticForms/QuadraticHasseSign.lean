import Submission.ClassField.QuadraticForms.RealOrPlace
import Submission.ClassField.QuadraticForms.EquivalentPlace
import Submission.ClassField.KummerTheory.PowerClasses
import Mathlib.Algebra.BigOperators.Finprod

/-!
# Chapter VIII, Section 6, Theorem 6.12

The global realization criterion for a family of nondegenerate quadratic
forms over all completions of a number field.
-/

namespace Submission.CField.QForms

open scoped BigOperators
open NumberField
open QuadraticMap
open Submission.CField.Ideles
open Submission.CField.KTheory
open Submission.CField.HNorm

noncomputable section
universe u

/-- The Hasse sign of a diagonal coefficient list, using the concrete
quadratic Hilbert sign. -/
noncomputable def quadraticHasseSign
    {F : Type u} [Field F] : List Fˣ → ℤˣ
  | [] => 1
  | a :: as =>
      quadraticHilbertSign (a : F) (a : F) *
        (as.map fun b => quadraticHilbertSign (a : F) (b : F)).prod *
          quadraticHasseSign as

/-- One actual local quadratic form of rank `n`, together with an orthogonal
diagonalization used only to define its discriminant and Hasse invariant. -/
structure HSForm
    (K : Type u) [Field K] [NumberField K]
    (n : ℕ) (v : NumberFieldPlace K) where
  Space : Type u
  [spaceAddGroup : AddCommGroup Space]
  [moduleSpace : Module (placeCompletion K v) Space]
  [finiteDimensionalSpace : FiniteDimensional (placeCompletion K v) Space]
  form : QuadraticForm (placeCompletion K v) Space
  nondegenerate : form.Nondegenerate
  rank_eq : Module.finrank (placeCompletion K v) Space = n
  coefficient : Fin n → (placeCompletion K v)ˣ
  diagonalization : Nonempty
    (form.IsometryEquiv
      (weightedSumSquares (placeCompletion K v)
        (fun i => ((coefficient i : (placeCompletion K v)ˣ) :
          placeCompletion K v))))

attribute [instance]
  HSForm.spaceAddGroup
  HSForm.moduleSpace
  HSForm.finiteDimensionalSpace

/-- The local square-class discriminant of the chosen diagonalization. -/
noncomputable def HSForm.discriminant
    {K : Type u} [Field K] [NumberField K]
    {n : ℕ} {v : NumberFieldPlace K}
    (q : HSForm K n v) :
    PowerClassGroup (placeCompletion K v) 2 :=
  powerClass 2 (∏ i, q.coefficient i)

/-- The local Hasse invariant of the chosen diagonalization. -/
noncomputable def HSForm.hasse
    {K : Type u} [Field K] [NumberField K]
    {n : ℕ} {v : NumberFieldPlace K}
    (q : HSForm K n v) : ℤˣ :=
  quadraticHasseSign (List.ofFn q.coefficient)

/-- An actual global quadratic form of rank `n`. -/
structure GForm
    (K : Type u) [Field K] [NumberField K] (n : ℕ) where
  Space : Type u
  [spaceAddGroup : AddCommGroup Space]
  [moduleSpace : Module K Space]
  [finiteDimensionalSpace : FiniteDimensional K Space]
  form : QuadraticForm K Space
  nondegenerate : form.Nondegenerate
  rank_eq : Module.finrank K Space = n

attribute [instance]
  GForm.spaceAddGroup
  GForm.moduleSpace
  GForm.finiteDimensionalSpace

/-- The global form realizes the prescribed form at every actual completion. -/
def GForm.Realizes
    {K : Type u} [Field K] [NumberField K] {n : ℕ}
    (q₀ : GForm K n)
    (q : ∀ v : NumberFieldPlace K, HSForm K n v) : Prop :=
  ∀ v : NumberFieldPlace K,
    Nonempty ((quadraticFormPlace K q₀.Space q₀.form v).IsometryEquiv
      (q v).form)

/-- Condition (a): all local discriminants come from one global square
class, represented by an actual element `d₀ ∈ Kˣ`. -/
def DiscriminantCondition
    (K : Type u) [Field K] [NumberField K] (n : ℕ)
    (q : ∀ v : NumberFieldPlace K, HSForm K n v) : Prop :=
  ∃ d₀ : Kˣ, ∀ v : NumberFieldPlace K,
    powerClass 2 (Units.map (algebraMap K (placeCompletion K v)) d₀) =
      (q v).discriminant

/-- Condition (b): almost every local Hasse invariant is one and their
global product is one. -/
def HasseCondition
    (K : Type u) [Field K] [NumberField K] (n : ℕ)
    (q : ∀ v : NumberFieldPlace K, HSForm K n v) : Prop :=
  {v | (q v).hasse ≠ 1}.Finite ∧
    (∏ᶠ v : NumberFieldPlace K, (q v).hasse) = 1

/-- Necessity of the global discriminant condition.  This is isolated
because Mathlib has no basis-independent square-class discriminant for a
quadratic form on an arbitrary finite-dimensional module. -/
def DiscriminantCompatibilityBridge : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K] (n : ℕ)
    (q : ∀ v : NumberFieldPlace K, HSForm K n v)
    (q₀ : GForm K n),
    q₀.Realizes q → DiscriminantCondition K n q

/-- The narrow Hilbert product-formula input proving necessity of condition
(b) for a globally defined quadratic form. -/
def ProductFormulaBridge : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K] (n : ℕ)
    (q : ∀ v : NumberFieldPlace K, HSForm K n v)
    (q₀ : GForm K n),
    q₀.Realizes q → HasseCondition K n q

/-- The global existence direction constructed in the source from Lemma
6.13, weak approximation, and induction on the rank. -/
def HasseSignRealization : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K] (n : ℕ)
    (q : ∀ v : NumberFieldPlace K, HSForm K n v),
    DiscriminantCondition K n q →
    HasseCondition K n q →
      ∃ q₀ : GForm K n, q₀.Realizes q

/-- Theorem 6.12 from the separate discriminant, product-formula, and global
realization inputs. -/
theorem hasse_sign_bridges
    (hdisc : DiscriminantCompatibilityBridge.{u})
    (hproduct : ProductFormulaBridge.{u})
    (hrealize : HasseSignRealization.{u}) :
    ∀ (K : Type u) [Field K] [NumberField K] (n : ℕ)
    (q : ∀ v : NumberFieldPlace K, HSForm K n v),
    (∃ q₀ : GForm K n, q₀.Realizes q) ↔
      DiscriminantCondition K n q ∧
        HasseCondition K n q
  := by
  intro K _ _ n q
  constructor
  · rintro ⟨q₀, hq₀⟩
    exact ⟨hdisc K n q q₀ hq₀, hproduct K n q q₀ hq₀⟩
  · rintro ⟨hd, hs⟩
    exact hrealize K n q hd hs

/-- Theorem 6.3 gives uniqueness up to global isometry of a realization of
the same local family. -/
theorem global_realization_unique
    (h63 : (∀ (K V W : Type u) [Field K] [NumberField K]
          [AddCommGroup V] [Module K V] [FiniteDimensional K V]
          [AddCommGroup W] [Module K W] [FiniteDimensional K W]
          (Q : QuadraticForm K V) (Q' : QuadraticForm K W),
          (∀ v, QuadraticFormsEquivalent K V W Q Q' v) →
          Nonempty (Q.IsometryEquiv Q')))
    {K : Type u} [Field K] [NumberField K] {n : ℕ}
    (q : ∀ v : NumberFieldPlace K, HSForm K n v)
    (q₀ q₁ : GForm K n)
    (h₀ : q₀.Realizes q) (h₁ : q₁.Realizes q) :
    Nonempty (q₀.form.IsometryEquiv q₁.form) := by
  apply h63 K q₀.Space q₁.Space q₀.form q₁.form
  intro v
  obtain ⟨e₀⟩ := h₀ v
  obtain ⟨e₁⟩ := h₁ v
  exact ⟨e₀.trans e₁.symm⟩

end
end Submission.CField.QForms
