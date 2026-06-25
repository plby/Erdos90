import Towers.ClassField.LocalExistence.ConcreteLocalExistence
import Towers.ClassField.LocalExistence.ValuationClassification

/-!
# Milne, Class Field Theory, Section III.5, Step 5

Every finite-index subgroup of `Kˣ` containing the local unit subgroup is the
norm group of a canonical unramified extension.  The public statements below
only assume that `K` is a nonarchimedean local field; the valuation relation
and compatibility instances used by the implementation are installed
canonically inside this file.
-/

namespace Towers.CField.LExist

open Towers.CField.LFTheory
open Towers.CField.LBrauer

noncomputable section

variable (K : Type) [NontriviallyNormedField K] [IsUltrametricDist K]

local instance unramifiedNormClassificationValuativeRel : ValuativeRel K :=
  ValuativeRel.ofValuation (NormedField.valuation (K := K))

local instance unramifiedNormClassificationValuationCompatible :
    Valuation.Compatible (NormedField.valuation (K := K)) :=
  Valuation.Compatible.ofValuation (NormedField.valuation (K := K))

variable [IsNonarchimedeanLocalField K]

/-- A natural number bundled with the positivity required of an unramified
extension degree in Step 5. -/
structure PositiveUnramifiedDegree where
  val : ℕ
  positive : 0 < val

instance (n : PositiveUnramifiedDegree) : NeZero n.val :=
  ⟨Nat.ne_of_gt n.positive⟩

/-- A finite-index subgroup containing `U_K` is explicitly the norm group of
the canonical unramified extension of some positive degree. -/
theorem canonical_unramified_subextension
    (I : Subgroup Kˣ) [I.FiniteIndex]
    (hUI : localUnitSubgroup K ≤ I) :
    ∃ n : PositiveUnramifiedDegree,
      I = (canonicalUnramifiedSubextension K n.val).normGroup := by
  have hker : (localUnitOrder K).ker ≤ I.toAddSubgroup := by
    intro x hx
    change x.toMul ∈ I
    apply hUI
    apply (local_subgroup K x.toMul).2
    have hxorder : localUnitOrder K x = 0 := hx
    apply le_antisymm
    · have hle : localUnitOrder K (Additive.ofMul (1 : Kˣ)) ≤
          localUnitOrder K x := by simp [hxorder]
      simpa using
        (local_order_valuation K (1 : Kˣ) x.toMul).1 hle
    · have hle : localUnitOrder K x ≤
          localUnitOrder K (Additive.ofMul (1 : Kˣ)) := by
        simp [hxorder]
      simpa using
        (local_order_valuation K x.toMul (1 : Kˣ)).1 hle
  letI : I.toAddSubgroup.FiniteIndex :=
    (Subgroup.finiteIndex_toAddSubgroup_iff (H := I)).2 inferInstance
  obtain ⟨m, hm, hI⟩ :=
    comap_zmultiples_ker
      (localUnitOrder K) (local_order_surjective K)
      I.toAddSubgroup hker
  letI : NeZero m := ⟨hm⟩
  have hsubgroup : I = (localOrderMod K m).ker := by
    ext x
    change Additive.ofMul x ∈ I.toAddSubgroup ↔
      x ∈ (localOrderMod K m).ker
    rw [hI, mod_ker_dvd]
    change localUnitOrder K (Additive.ofMul x) ∈
        AddSubgroup.zmultiples (m : ℤ) ↔ _
    rw [AddSubgroup.mem_zmultiples_iff]
    constructor
    · rintro ⟨k, hk⟩
      exact ⟨k, by simpa [smul_eq_mul, mul_comm] using hk.symm⟩
    · rintro ⟨k, hk⟩
      exact ⟨k, by simpa [smul_eq_mul, mul_comm] using hk.symm⟩
  let mpos : PositiveUnramifiedDegree :=
    ⟨m, Nat.pos_of_ne_zero hm⟩
  refine ⟨mpos, ?_⟩
  exact hsubgroup.trans
    (unramified_subextension_ker K m).symm

/-- **Section III.5, Step 5.**  The source assertion holds with no public
valuation-relation or valuation-compatibility assumptions. -/
theorem unramifiedNormClassification :
    ∀ I : Subgroup Kˣ, I.FiniteIndex → localUnitSubgroup K ≤ I →
    ∃ n : PositiveUnramifiedDegree,
      I = (canonicalUnramifiedSubextension K n.val).normGroup
  := by
  intro I hfinite hUI
  letI : I.FiniteIndex := hfinite
  exact canonical_unramified_subextension K I hUI

/-- The witnessed extension has the positive degree `n + 1`. -/
theorem positive_unramified_group
    (I : Subgroup Kˣ) [I.FiniteIndex]
    (hUI : localUnitSubgroup K ≤ I) :
    ∃ n : PositiveUnramifiedDegree,
      I = (canonicalUnramifiedSubextension K n.val).normGroup := by
  obtain ⟨n, hn⟩ :=
    canonical_unramified_subextension K I hUI
  exact ⟨n, hn⟩

end

end Towers.CField.LExist
