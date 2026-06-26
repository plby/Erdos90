import Submission.ClassField.LubinTate.InfiniteActionExt

/-! # The identity action on the infinite Lubin--Tate extension -/

namespace Submission.CField.LTate

noncomputable section

namespace LTDatum

universe u v w

variable {A : Type u} [CommRing A] [IsDomain A]
  [IsDiscreteValuationRing A]
  (D : LTDatum A)
  (K : Type v) [Field K] [Algebra A K] [IsFractionRing A K]
  (Omega : Type w) [Field Omega] [Algebra K Omega]

/-- The unit `1` acts identically on the infinite Lubin--Tate extension. -/
theorem infinite_action_alg
    (orbit : ∀ n,
      (A ⧸ Ideal.span {D.pi ^ (n + 1)})ˣ →*
        (D.torsionLevelField K Omega n ≃ₐ[K]
          D.torsionLevelField K Omega n))
    (hcompat : CompatibleTorsionActions D orbit) :
    D.infiniteActionHom K Omega orbit hcompat 1 =
      AlgHom.id K (D.infiniteTorsionField K Omega) := by
  apply D.infinite_torsion_ext K Omega
  intro n x
  calc
    D.infiniteActionHom K Omega orbit hcompat 1
        (D.torsionLevelInclusion K Omega n x) =
      D.torsionLevelInclusion K Omega n
        (D.unitLevelAction K Omega orbit n 1 x) :=
      D.infinite_alg_level K Omega orbit hcompat 1 n x
    _ = D.torsionLevelInclusion K Omega n x := by
      simp [unitLevelAction]
    _ = AlgHom.id K (D.infiniteTorsionField K Omega)
        (D.torsionLevelInclusion K Omega n x) := rfl

end LTDatum

end

end Submission.CField.LTate
