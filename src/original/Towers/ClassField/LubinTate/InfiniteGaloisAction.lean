import Towers.ClassField.LubinTate.AmbientGaloisAction

/-!
# The unit action on the infinite Lubin--Tate extension

Compatible quotient-unit actions on the finite torsion fields glue over their
directed union.  This realizes the unit part of the action used in Summary
I.3.7 and in the construction preceding Theorem I.3.9.
-/

namespace Towers.CField.LTate

noncomputable section

namespace LTDatum

universe u v w

variable {A : Type u} [CommRing A] [IsDomain A]
  [IsDiscreteValuationRing A]
  (D : LTDatum A)
  (K : Type v) [Field K] [Algebra A K] [IsFractionRing A K]
  (Omega : Type w) [Field Omega] [Algebra K Omega]

/-- A base unit reduced modulo the level-`n + 1` Lubin--Tate conductor. -/
def unitQuotient (n : ℕ) :
    Aˣ →* (A ⧸ Ideal.span {D.pi ^ (n + 1)})ˣ :=
  Units.map
    (Ideal.Quotient.mk (Ideal.span {D.pi ^ (n + 1)})).toMonoidHom

@[simp]
theorem quotient_unit_reduction (n : ℕ) (a : Aˣ) :
    quotientUnitReduction D.pi n (D.unitQuotient (n + 1) a) =
      D.unitQuotient n a :=
  reduction_units_mk D.pi n a

/-- The action of a base unit on one finite torsion level, obtained by
reduction modulo `pi^(n+1)`. -/
def unitLevelAction
    (orbit : ∀ n,
      (A ⧸ Ideal.span {D.pi ^ (n + 1)})ˣ →*
        (D.torsionLevelField K Omega n ≃ₐ[K]
          D.torsionLevelField K Omega n))
    (n : ℕ) : Aˣ →* (D.torsionLevelField K Omega n ≃ₐ[K]
      D.torsionLevelField K Omega n) :=
  (orbit n).comp (D.unitQuotient n)

theorem action_compatible_succ
    (orbit : ∀ n,
      (A ⧸ Ideal.span {D.pi ^ (n + 1)})ˣ →*
        (D.torsionLevelField K Omega n ≃ₐ[K]
          D.torsionLevelField K Omega n))
    (hcompat : CompatibleTorsionActions D orbit)
    (n : ℕ) (a : Aˣ) (x : D.torsionLevelField K Omega n) :
    IntermediateField.inclusion
        (D.torsion_mono_succ K Omega n)
        (D.unitLevelAction K Omega orbit n a x) =
      D.unitLevelAction K Omega orbit (n + 1) a
        (IntermediateField.inclusion
          (D.torsion_mono_succ K Omega n) x) := by
  exact hcompat n (D.unitQuotient (n + 1) a) x

set_option maxHeartbeats 1000000 in
-- The induction compares nested subtype inclusions through a varying finite tower.
/-- Compatibility of the finite unit actions along every transition map, not
only a single successor. -/
theorem level_action_compatible
    (orbit : ∀ n,
      (A ⧸ Ideal.span {D.pi ^ (n + 1)})ˣ →*
        (D.torsionLevelField K Omega n ≃ₐ[K]
          D.torsionLevelField K Omega n))
    (hcompat : CompatibleTorsionActions D orbit)
    {n m : ℕ} (hnm : n ≤ m) (a : Aˣ)
    (x : D.torsionLevelField K Omega n) :
    IntermediateField.inclusion
        (D.torsion_level_mono K Omega hnm)
        (D.unitLevelAction K Omega orbit n a x) =
      D.unitLevelAction K Omega orbit m a
        (IntermediateField.inclusion
          (D.torsion_level_mono K Omega hnm) x) := by
  induction m, hnm using Nat.le_induction with
  | base => rfl
  | succ m hnm ih =>
      rw [← IntermediateField.inclusion_inclusion
        (D.torsion_level_mono K Omega hnm)
        (D.torsion_mono_succ K Omega m)]
      rw [ih]
      rw [D.action_compatible_succ K Omega orbit hcompat]
      rw [IntermediateField.inclusion_inclusion
        (D.torsion_level_mono K Omega hnm)
        (D.torsion_mono_succ K Omega m)]

/-- The action at one finite level, viewed as a map into the infinite torsion
field. -/
noncomputable def infiniteActionLevel
    (orbit : ∀ n,
      (A ⧸ Ideal.span {D.pi ^ (n + 1)})ˣ →*
        (D.torsionLevelField K Omega n ≃ₐ[K]
          D.torsionLevelField K Omega n))
    (a : Aˣ) (n : ℕ) :
    D.torsionLevelField K Omega n →ₐ[K]
      D.infiniteTorsionField K Omega :=
  (IntermediateField.inclusion
    (le_iSup (D.torsionLevelField K Omega) n)).comp
      (D.unitLevelAction K Omega orbit n a).toAlgHom

set_option maxHeartbeats 2000000 in
-- Comparing two level maps passes through their common maximum level.
theorem infinite_level_compatible
    (orbit : ∀ n,
      (A ⧸ Ideal.span {D.pi ^ (n + 1)})ˣ →*
        (D.torsionLevelField K Omega n ≃ₐ[K]
          D.torsionLevelField K Omega n))
    (hcompat : CompatibleTorsionActions D orbit)
    (a : Aˣ) (n m : ℕ)
    (h : (D.torsionLevelField K Omega n).toSubalgebra ≤
      (D.torsionLevelField K Omega m).toSubalgebra) :
    D.infiniteActionLevel K Omega orbit a n =
      (D.infiniteActionLevel K Omega orbit a m).comp
        (Subalgebra.inclusion h) := by
  apply AlgHom.ext
  intro x
  apply Subtype.ext
  let N := max n m
  have hn : n ≤ N := Nat.le_max_left n m
  have hm : m ≤ N := Nat.le_max_right n m
  have hxN :
      IntermediateField.inclusion
          (D.torsion_level_mono K Omega hn) x =
        IntermediateField.inclusion
          (D.torsion_level_mono K Omega hm)
          (Subalgebra.inclusion h x) := by
    apply Subtype.ext
    rfl
  calc
    (D.unitLevelAction K Omega orbit n a x : Omega) =
        (IntermediateField.inclusion
          (D.torsion_level_mono K Omega hn)
          (D.unitLevelAction K Omega orbit n a x) : Omega) := rfl
    _ = (D.unitLevelAction K Omega orbit N a
        (IntermediateField.inclusion
          (D.torsion_level_mono K Omega hn) x) : Omega) := by
      rw [D.level_action_compatible K Omega orbit hcompat hn]
    _ = (D.unitLevelAction K Omega orbit N a
        (IntermediateField.inclusion
          (D.torsion_level_mono K Omega hm)
          (Subalgebra.inclusion h x)) : Omega) := by
      rw [hxN]
    _ = (IntermediateField.inclusion
        (D.torsion_level_mono K Omega hm)
        (D.unitLevelAction K Omega orbit m a
          (Subalgebra.inclusion h x)) : Omega) := by
      rw [D.level_action_compatible K Omega orbit hcompat hm]
    _ = (D.unitLevelAction K Omega orbit m a
        (Subalgebra.inclusion h x) : Omega) := rfl

set_option maxHeartbeats 2000000 in
-- Elaborating the directed `iSup` lift expands all finite-level field inclusions.
/-- The algebra endomorphism of `K_pi` obtained by gluing the action of a
base unit on every finite torsion level. -/
noncomputable def infiniteActionHom
    (orbit : ∀ n,
      (A ⧸ Ideal.span {D.pi ^ (n + 1)})ˣ →*
        (D.torsionLevelField K Omega n ≃ₐ[K]
          D.torsionLevelField K Omega n))
    (hcompat : CompatibleTorsionActions D orbit)
    (a : Aˣ) :
    D.infiniteTorsionField K Omega →ₐ[K]
      D.infiniteTorsionField K Omega := by
  let S : ℕ → Subalgebra K Omega := fun n ↦
    (D.torsionLevelField K Omega n).toSubalgebra
  have hdir : Directed (· ≤ ·) S :=
    (D.torsion_level_mono K Omega).directed_le
  let f : ∀ n, S n →ₐ[K] D.infiniteTorsionField K Omega := fun n ↦
    D.infiniteActionLevel K Omega orbit a n
  have hf : ∀ (n m : ℕ) (h : S n ≤ S m),
      f n = (f m).comp (Subalgebra.inclusion h) := by
    exact D.infinite_level_compatible K Omega orbit hcompat a
  have htop : (D.infiniteTorsionField K Omega).toSubalgebra ≤ ⨆ n, S n := by
    rw [infiniteTorsionField,
      IntermediateField.toSubalgebra_iSup_of_directed
        (D.torsion_level_mono K Omega).directed_le]
  exact Subalgebra.iSupLift S hdir f hf
    (D.infiniteTorsionField K Omega).toSubalgebra htop

end LTDatum

end

end Towers.CField.LTate
