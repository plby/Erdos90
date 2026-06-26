import Towers.ClassField.LocalReciprocity.UniversePolymorphicArtin
import Towers.NumberTheory.Galois.PlaceCompletionDegree
import Towers.ClassField.Ideles.FinitePlaceCompletion
import Towers.ClassField.IdeleCohomology.CompletionProductAction
import Towers.ClassField.Reciprocity.UniversePlaceArtin

/-!
# The finite-place character formula in a global Galois layer

For a chosen place of a finite abelian number-field extension above a finite
place of the base, Proposition III.3.6 gives a canonical local Artin map.
This file transports its source to the prime-adic completion used by idèles
and its target into the global Galois group.
-/

namespace Towers.CField.RExist

open scoped IsMulCommutative
open AbsoluteValue IsDedekindDomain NumberField
open Towers.NumberTheory.Milne
open Towers.CField.LRecip
open Towers.CField.LBrauer
open Towers.CField.Ideles
open Towers.CField.Recip
open Towers.CField.ICohomo

noncomputable section

universe u

/-- The finite-place instance of the right square in Lemma VII.8.5. -/
structure CharacterFormulaData
    (K L : Type u) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [IsMulCommutative Gal(L/K)]
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K)) where
  artin : (P.adicCompletion K)ˣ →* Gal(L/K)
  cupInvariant :
    (P.adicCompletion K)ˣ →
      CharacterModule (Additive Gal(L/K)) → LocalInvariant
  formula : ∀ a chi,
    chi (Additive.ofMul (artin a)) = cupInvariant a chi

set_option maxHeartbeats 8000000 in
-- The completed local extension and its decomposition group elaborate in
-- the same instance context.
set_option synthInstance.maxHeartbeats 1000000 in
/-- Proposition III.3.6 at a chosen finite completion, with the source in
the prime-adic model used by the finite idèles and the target in the global
Galois group. -/
noncomputable def characterFormulaData
    (K L : Type u) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [IsMulCommutative Gal(L/K)]
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (w : CompletionPlacesAbove (L := L) (FinitePlace.mk P).val) :
    CharacterFormulaData K L P := by
  let D := characterFormulaUniverse K L P w
  exact
    { artin := D.artin
      cupInvariant := D.cupInvariant
      formula := D.formula }

end

end Towers.CField.RExist
