import Mathlib.Algebra.FiniteSupport.Basic
import Towers.ClassField.BrauerLocalization.ArchimedeanData

/-!
# Finite-support assembly for the global Brauer localization

This file separates the formal direct-sum construction from its arithmetic
input. A family of monoid homomorphisms whose value at every global element
has finite multiplicative support canonically determines
`MultiplicativeLocalizationData`. Applied to Brauer scalar extension, the
only remaining input is the theorem that a global Brauer class is locally
trivial at all but finitely many places.
-/

namespace Towers.CField.BLoc

open NumberField
open Towers.CField.BGroups
open Towers.CField.Ideles
open Towers.CField.CBrauer
open Towers.CField.RExist

noncomputable section

universe u v w

/-- The direct-sum element associated to a finitely supported family of
multiplicative coordinates. -/
private noncomputable def finiteSupportLocalization
    {index : Type u} {Global : Type v} {Local : index → Type w}
    [CommGroup Global] [∀ i, CommGroup (Local i)]
    (localizeAt : ∀ i, Global →* Local i)
    (hfinite : ∀ x, Set.Finite
      {i | localizeAt i x ≠ 1})
    (x : Global) :
    DirectSum index (fun i ↦ Additive (Local i)) := by
  classical
  let support := (hfinite x).toFinset
  exact DirectSum.mk (fun i ↦ Additive (Local i)) support
    (fun i ↦ Additive.ofMul (localizeAt i x))

/-- Every coordinate of `finiteSupportLocalization` is the prescribed
localization value, including outside the chosen support finset where both
sides are zero/one. -/
private theorem finite_support_localization
    {index : Type u} {Global : Type v} {Local : index → Type w}
    [CommGroup Global] [∀ i, CommGroup (Local i)]
    (localizeAt : ∀ i, Global →* Local i)
    (hfinite : ∀ x, Set.Finite
      {i | localizeAt i x ≠ 1})
    (x : Global) (i : index) :
    finiteSupportLocalization localizeAt hfinite x i =
      Additive.ofMul (localizeAt i x) := by
  classical
  by_cases hi : i ∈ (hfinite x).toFinset
  · rw [finiteSupportLocalization, DirectSum.mk_apply_of_mem hi]
  · rw [finiteSupportLocalization, DirectSum.mk_apply_of_notMem hi]
    have hi' : i ∉ {j | localizeAt j x ≠ 1} := by
      simpa using hi
    have hone : localizeAt i x = 1 := by simpa using hi'
    simp [hone]

/-- A finitely supported family of multiplicative homomorphisms assembles to
an additive homomorphism into the direct sum. -/
private noncomputable def supportLocalizationMonoid
    {index : Type u} {Global : Type v} {Local : index → Type w}
    [CommGroup Global] [∀ i, CommGroup (Local i)]
    (localizeAt : ∀ i, Global →* Local i)
    (hfinite : ∀ x, Set.Finite
      {i | localizeAt i x ≠ 1}) :
    Additive Global →+
      DirectSum index (fun i ↦ Additive (Local i)) where
  toFun x := finiteSupportLocalization localizeAt hfinite x.toMul
  map_zero' := by
    apply DirectSum.ext
    intro i
    rw [finite_support_localization]
    simp
  map_add' x y := by
    apply DirectSum.ext
    intro i
    change finiteSupportLocalization localizeAt hfinite (x + y).toMul i =
      finiteSupportLocalization localizeAt hfinite x.toMul i +
        finiteSupportLocalization localizeAt hfinite y.toMul i
    rw [finite_support_localization, finite_support_localization,
      finite_support_localization]
    simp

/-- Generic constructor for localization data from its finite-support
theorem. -/
noncomputable def multiplicativeLocalizationSupport
    {index : Type u} {Global : Type v} {Local : index → Type w}
    [CommGroup Global] [∀ i, CommGroup (Local i)]
    (localizeAt : ∀ i, Global →* Local i)
    (hfinite : ∀ x, Set.Finite
      {i | localizeAt i x ≠ 1}) :
    MultiplicativeLocalizationData Global Local where
  localizeAt := localizeAt
  localization :=
    supportLocalizationMonoid localizeAt hfinite
  localization_apply x i := by
    change finiteSupportLocalization localizeAt hfinite x i =
      Additive.ofMul (localizeAt i x)
    exact finite_support_localization localizeAt hfinite x i

/-- A class belonging to a finite Galois relative Brauer group has finite
global completion support as soon as the corresponding relative localization
package is available. This is the formal passage from the relative direct sum
to the absolute finite-support assertion. -/
theorem change_nonidentity_relative
    (K L : Type u) [Field K] [NumberField K] [Field L]
    [Algebra K L] [IsGalois K L]
    (Lv : NumberFieldPlace K → Type u)
    [∀ v, Field (Lv v)]
    [∀ v, Algebra (Towers.CField.RExist.placeCompletion K v) (Lv v)]
    [∀ v, IsGalois (Towers.CField.RExist.placeCompletion K v) (Lv v)]
    (loc : RelativeLocalizationData (K := K) (L := L)
      (fun v ↦ Towers.CField.RExist.placeCompletion K v) Lv)
    (beta : BrauerGroup K) (hbeta : beta ∈ relativeBrauerGroup K L) :
    Set.Finite {v : NumberFieldPlace K |
      brauerBaseChange K (Towers.CField.RExist.placeCompletion K v) beta ≠ 1} := by
  let x : relativeBrauerGroup K L := ⟨beta, hbeta⟩
  let y := loc.multiplicativeLocalizationData.localization
    (Additive.ofMul x)
  apply (DFinsupp.finite_support y).subset
  intro v hv
  have hcoord :
      ((y v).toMul : BrauerGroup (Towers.CField.RExist.placeCompletion K v)) =
        brauerBaseChange K (Towers.CField.RExist.placeCompletion K v) beta := by
    rw [show y v = Additive.ofMul
      (loc.multiplicativeLocalizationData.localizeAt v x) from
        loc.multiplicativeLocalizationData.localization_apply x v]
    exact loc.localizeAt_coe x v
  intro hyv
  apply hv
  rw [← hcoord, hyv]
  rfl

/-- The one arithmetic assertion still needed to construct the canonical
global Brauer localization map. -/
def GlobalChangeSupport
    (K : Type u) [Field K] [NumberField K] : Prop :=
  ∀ beta : BrauerGroup K, Set.Finite <|
    {v : NumberFieldPlace K |
      brauerBaseChange K (Towers.CField.RExist.placeCompletion K v) beta ≠ 1}

/-- Canonical global Brauer localization, conditional only on the named
finite-support theorem. -/
noncomputable def globalBrauerLocalization
    (K : Type u) [Field K] [NumberField K]
    (hfinite : GlobalChangeSupport K) :
    MultiplicativeLocalizationData (BrauerGroup K)
      (fun v : NumberFieldPlace K ↦
        BrauerGroup (Towers.CField.RExist.placeCompletion K v)) :=
  multiplicativeLocalizationSupport
    (fun v ↦ brauerBaseChange K (Towers.CField.RExist.placeCompletion K v)) hfinite

/-- `BData` constructed from the sole remaining finite-support
input. The place invariants are unconditional. -/
noncomputable def brauerDataSupport
    (K : Type u) [Field K] [NumberField K]
    (hfinite : GlobalChangeSupport K) :
    BData K where
  localization := globalBrauerLocalization K hfinite
  localizeAt_eq _ _ := rfl
  placeInvariant := placeInvariantData K

end

end Towers.CField.BLoc
