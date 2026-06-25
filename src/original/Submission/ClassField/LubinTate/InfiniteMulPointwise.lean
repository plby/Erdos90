import Submission.ClassField.LubinTate.InfiniteActionExt

/-! # Pointwise multiplicativity of the infinite Lubin--Tate action -/

namespace Submission.CField.LTate

noncomputable section

namespace LTDatum

universe u v w

variable {A : Type u} [CommRing A] [IsDomain A]
  [IsDiscreteValuationRing A]
  (D : LTDatum A)
  (K : Type v) [Field K] [Algebra A K] [IsFractionRing A K]
  (Omega : Type w) [Field Omega] [Algebra K Omega]

set_option maxHeartbeats 1000000 in
-- Three dependent finite-level inclusions occur in this comparison.
/-- Multiplication of base units is composition on each embedded finite
torsion level. -/
theorem infinite_action_level
    (orbit : ∀ n,
      (A ⧸ Ideal.span {D.pi ^ (n + 1)})ˣ →*
        (D.torsionLevelField K Omega n ≃ₐ[K]
          D.torsionLevelField K Omega n))
    (hcompat : CompatibleTorsionActions D orbit)
    (a b : Aˣ) (n : ℕ) (x : D.torsionLevelField K Omega n) :
    D.infiniteActionHom K Omega orbit hcompat (a * b)
        (D.torsionLevelInclusion K Omega n x) =
      D.infiniteActionHom K Omega orbit hcompat a
        (D.infiniteActionHom K Omega orbit hcompat b
          (D.torsionLevelInclusion K Omega n x)) := by
  have hlevel :
      D.unitLevelAction K Omega orbit n (a * b) x =
        D.unitLevelAction K Omega orbit n a
          (D.unitLevelAction K Omega orbit n b x) :=
    DFunLike.congr_fun
      (map_mul (D.unitLevelAction K Omega orbit n) a b) x
  calc
    D.infiniteActionHom K Omega orbit hcompat (a * b)
        (D.torsionLevelInclusion K Omega n x) =
      D.torsionLevelInclusion K Omega n
        (D.unitLevelAction K Omega orbit n (a * b) x) :=
      D.infinite_alg_level
        K Omega orbit hcompat (a * b) n x
    _ = D.torsionLevelInclusion K Omega n
        (D.unitLevelAction K Omega orbit n a
          (D.unitLevelAction K Omega orbit n b x)) :=
      congrArg (D.torsionLevelInclusion K Omega n) hlevel
    _ = D.infiniteActionHom K Omega orbit hcompat a
        (D.torsionLevelInclusion K Omega n
          (D.unitLevelAction K Omega orbit n b x)) :=
      (D.infinite_alg_level K Omega orbit hcompat a n
        (D.unitLevelAction K Omega orbit n b x)).symm
    _ = D.infiniteActionHom K Omega orbit hcompat a
        (D.infiniteActionHom K Omega orbit hcompat b
          (D.torsionLevelInclusion K Omega n x)) :=
      congrArg (D.infiniteActionHom K Omega orbit hcompat a)
        (D.infinite_alg_level
          K Omega orbit hcompat b n x).symm

end LTDatum

end

end Submission.CField.LTate
