import Submission.ClassField.LocalBrauer.CanonicalCarryUnconditional

/-!
# Inflation of Frobenius-normalized carry classes at arbitrary levels

The canonical invariant is assembled on factorial levels, but base change
through an unramified extension naturally introduces products of arbitrary
degrees.  This file records the same inflation calculation for every
divisibility relation between canonical unramified levels.
-/

namespace Submission.CField.LBrauer

noncomputable section

universe u

open CProduca

variable (K : Type u)
  [NontriviallyNormedField K] [IsUltrametricDist K] [ValuativeRel K]
  [IsNonarchimedeanLocalField K]
  [Valuation.Compatible (NormedField.valuation (K := K))]

set_option maxHeartbeats 2000000 in
-- Comparing restriction with cyclic reduction unfolds two dependent levels.
set_option synthInstance.maxHeartbeats 200000 in
-- The comparison synthesizes both canonical-level Galois structures.
/-- Frobenius-normalized cyclic coordinates commute with restriction and
reduction between arbitrary canonical unramified levels. -/
theorem level_z_compatible
    {n m : ℕ} [NeZero n] [NeZero m] (hnm : n ∣ m)
    (z : Multiplicative (ZMod m)) :
    galoisRestrictionHom K
        (unramified_level K (NeZero.pos n) (NeZero.pos m) hnm)
        (levelZMod K m z) =
      levelZMod K n
        (CCarry.indexReduction hnm z) := by
  let oneM : Multiplicative (ZMod m) := Multiplicative.ofAdd 1
  have hz : z ∈ Subgroup.zpowers oneM := by
    refine ⟨(z.toAdd.val : ℤ), ?_⟩
    change oneM ^ (z.toAdd.val : ℤ) = z
    rw [zpow_natCast]
    apply Multiplicative.toAdd.injective
    simp [oneM]
  obtain ⟨i, hi⟩ := hz
  rw [← hi]
  simp only [map_zpow]
  rw [level_frobenius_z,
    arithmetic_frobenius_restrict K hnm,
    ← level_frobenius_z K n]
  apply congrArg (fun x ↦ x ^ i)
  apply congrArg (levelZMod K n)
  apply Multiplicative.toAdd.injective
  rw [CCarry.reduction_toAdd]
  exact (ZMod.cast_one hnm).symm

set_option maxHeartbeats 3000000 in
-- Inflation expands the cocycle formula across two dependent canonical levels.
set_option synthInstance.maxHeartbeats 300000 in
-- The cocycle comparison synthesizes the relative tower action instances.
/-- Inflation sends the Frobenius-normalized degree-`n` carry class to the
`(m / n)`-th power of the Frobenius-normalized degree-`m` carry class. -/
theorem inflation_frobenius_carry
    {n m : ℕ} [NeZero n] [NeZero m] (hnm : n ∣ m) (a : Kˣ) :
    let F := canonicalUnramifiedLevel K n
    let E := canonicalUnramifiedLevel K m
    let hFE : F ≤ E :=
      unramified_level K (NeZero.pos n) (NeZero.pos m) hnm
    inflationHom K hFE
        (MHTwo.mk
          (galoisCarryCocycle K
            (levelZMod K n) a)) =
      (MHTwo.mk
        (galoisCarryCocycle K
          (levelZMod K m) a)) ^
        (m / n) := by
  let F := canonicalUnramifiedLevel K n
  let E := canonicalUnramifiedLevel K m
  let hFE : F ≤ E :=
    unramified_level K (NeZero.pos n) (NeZero.pos m) hnm
  letI : Fact (F ≤ E) := ⟨hFE⟩
  let eF := levelZMod K n
  let eE := levelZMod K m
  let cF := galoisCarryCocycle K eF a
  have hcompat : ∀ z,
      galoisRestrictionHom K hFE (eE z) =
        eF (CCarry.indexReduction hnm z) := by
    intro z
    exact level_z_compatible
      K hnm z
  have hconcrete : MHTwo.mk
        (concreteInflationCocycle K hFE cF) =
      MHTwo.mk (galoisCarryCocycle K eE a) ^ (m / n) := by
    exact inflation_carry_cocycle
      K hnm hFE eF eE hcompat a
  exact
    (inflation_concrete_cocycle
      (K := K) (F := F) (E := E) cF).trans hconcrete

end

end Submission.CField.LBrauer
