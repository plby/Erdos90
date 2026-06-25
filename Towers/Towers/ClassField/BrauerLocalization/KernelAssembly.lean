import Towers.ClassField.BrauerLocalization.CokernelAssembly
import Towers.ClassField.GlobalClass.FiniteCompletion

/-!
# Lemma VIII.4.1 assembly

The Chapter VII norm and Frobenius arguments have been discharged through
Lemma VII.4.5.  The existing Chapter VIII bridge therefore gives Milne's
Lemma VIII.4.1 without any remaining hypotheses.
-/

namespace Towers.CField.BLoc

open Towers.CField.GClass

universe u

/-- **Lemma VIII.4.1.**  The unconditional local-degree/Frobenius statement
used in the proof of the global Brauer exact sequence. -/
theorem globalDegreeLcm :
    (∀ (K L : Type u) [Field K] [NumberField K]
          [Field L] [NumberField L] [Algebra K L]
          [FiniteDimensional K L] [IsGalois K L] [IsCyclic Gal(L/K)],
          LocalLCM
            (completionDegree (K := K) (L := L))
            (Module.finrank K L)) :=
  completion_statement_only cyclicSubextensionDegree

end Towers.CField.BLoc
