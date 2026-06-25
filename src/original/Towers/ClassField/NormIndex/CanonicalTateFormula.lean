import Towers.ClassField.NormIndex.TateZeroIndex
import Towers.ClassField.NormIndex.FixedIdeleDescent

/-!
# Canonical Tate-zero index formula

This file combines the concrete proof of Lemma VII.4.1 with the Tate-zero
comparison used in Corollary VII.4.4.  The two substantial developments are
kept in separate modules so Lean can compile their large dependent quotient
terms independently.
-/

namespace Towers.CField.NIndex

noncomputable section

universe u

/-- Unconditional canonical form of Lemma VII.4.1. -/
theorem canonicalTateFormula :
    TateIndexFormula.{u} := by
  intro K L _ _ _ _ _ _ _
  exact canonical_fixed_bijective
    (K := K) (L := L)

/-- The Tate-degree-zero index identity required by Corollary VII.4.4. -/
theorem tateIndexBridge :
    TateIndexBridge.{u} :=
  tate_bridge_fixed
    canonicalTateFormula

end

end Towers.CField.NIndex
