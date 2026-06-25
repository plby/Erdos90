import Towers.ClassField.CyclicIdeles.FixedField
import Towers.ClassField.CyclicIdeles.NormIndexTower
import Towers.ClassField.CyclicIdeles.NormalSubgroup
import Towers.ClassField.CyclicIdeles.TrivialExtension

/-!
# Chapter VII, Section 5, Lemma 5.4: assembly

The normal-subgroup, fixed-field, norm-index, and degree-one inputs are all
now unconditional, so the inflation--restriction induction gives the source
statement of Lemma VII.5.4.
-/

namespace Towers.CField.CIdeles

noncomputable section

universe u

/-- **Lemma VII.5.4.** The prime-cyclic cases of Theorem VII.5.1 imply its
cases for arbitrary finite `p`-groups. -/
theorem pCyclicCases : (PReductionBridge.{u}) :=
  p_reduction_bridge
    normalSubgroupBridge
    trivialExtensionBridge
    fixedFieldBridge
    indexTowerBridge

end

end Towers.CField.CIdeles
