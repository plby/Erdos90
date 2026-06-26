import Towers.ClassField.Reciprocity.ArtinMapStatements
import Towers.ClassField.GlobalClass.MaximalAbelianSubextension

/-!
# Existential form of global norm limitation

Lemma VII.9.4 only needs the consequence that the norm image of an
arbitrary finite extension is the norm group of some finite abelian
extension of the base.  This is exactly Theorem VIII.4.8 after embedding
its maximal abelian subfield into the fixed separable closure.
-/

namespace Towers.CField.GClass

open NumberField
open Towers.CField.LFTheory
open Towers.CField.Ideles
open Towers.CField.Recip

noncomputable section

universe u

/-- Existential consequence of Theorem VIII.4.8 in the finite-layer format
used by the idèlic existence theorem. -/
def ExistentialNormLimitation : Prop :=
  ∀ (K E : Type u) [Field K] [NumberField K]
    [Field E] [NumberField E] [Algebra K E] [FiniteDimensional K E],
    ∃ M : FASubext K,
      ideleClassSubgroup M =
        (canonicalIdeleNorm (K := K) (L := E)).range

end

end Towers.CField.GClass
