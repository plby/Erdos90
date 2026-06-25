import Submission.ClassField.LubinTate.InfiniteGaloisAction

/-!
# The infinite Lubin--Tate action on finite levels

This file caches the defining equation for the directed-limit unit action on
each finite torsion level.  Keeping the dependent `iSup` calculation in its
own module makes all downstream automorphism arguments inexpensive.
-/

namespace Submission.CField.LTate

noncomputable section

namespace LTDatum

universe u v w

variable {A : Type u} [CommRing A] [IsDomain A]
  [IsDiscreteValuationRing A]
  (D : LTDatum A)
  (K : Type v) [Field K] [Algebra A K] [IsFractionRing A K]
  (Omega : Type w) [Field Omega] [Algebra K Omega]

/-- The canonical inclusion of a finite Lubin--Tate torsion level into
their directed union `K_pi`.  Naming this dependent inclusion keeps the
infinite-action API small enough for later kernel checking. -/
noncomputable def torsionLevelInclusion (n : ℕ) :
    D.torsionLevelField K Omega n →ₐ[K]
      D.infiniteTorsionField K Omega :=
  IntermediateField.inclusion
    (le_iSup (D.torsionLevelField K Omega) n)

set_option maxHeartbeats 1000000 in
-- Unfolding the directed lift exposes its compatibility proof and ambient
-- subtype inclusions once; downstream results use this cached equation.
/-- On a finite torsion level, the glued infinite action is the prescribed
finite quotient-unit action. -/
@[simp]
theorem infinite_alg_level
    (orbit : ∀ n,
      (A ⧸ Ideal.span {D.pi ^ (n + 1)})ˣ →*
        (D.torsionLevelField K Omega n ≃ₐ[K]
          D.torsionLevelField K Omega n))
    (hcompat : CompatibleTorsionActions D orbit)
    (a : Aˣ) (n : ℕ) (x : D.torsionLevelField K Omega n) :
    D.infiniteActionHom K Omega orbit hcompat a
        (D.torsionLevelInclusion K Omega n x) =
      D.torsionLevelInclusion K Omega n
        (D.unitLevelAction K Omega orbit n a x) := by
  let S : ℕ → Subalgebra K Omega := fun m ↦
    (D.torsionLevelField K Omega m).toSubalgebra
  have hdir : Directed (· ≤ ·) S :=
    (D.torsion_level_mono K Omega).directed_le
  let f : ∀ m, S m →ₐ[K] D.infiniteTorsionField K Omega := fun m ↦
    D.infiniteActionLevel K Omega orbit a m
  have hf : ∀ (i j : ℕ) (h : S i ≤ S j),
      f i = (f j).comp (Subalgebra.inclusion h) := by
    exact D.infinite_level_compatible
      K Omega orbit hcompat a
  change Subalgebra.iSupLift S hdir f hf
      (D.infiniteTorsionField K Omega).toSubalgebra _
        (D.torsionLevelInclusion K Omega n x) = _
  change Subalgebra.iSupLift S hdir f hf
      (D.infiniteTorsionField K Omega).toSubalgebra _
        (IntermediateField.inclusion
          (le_iSup (D.torsionLevelField K Omega) n) x) = _
  exact Subalgebra.iSupLift_inclusion S x
    (le_iSup (D.torsionLevelField K Omega) n)

end LTDatum

end

end Submission.CField.LTate
