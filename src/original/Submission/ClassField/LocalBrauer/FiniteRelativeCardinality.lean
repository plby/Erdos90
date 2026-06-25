import Submission.ClassField.CrossedProducts.IsMulCoboundary
import Submission.ClassField.LocalBrauer.InvariantBaseChange
import Submission.ClassField.LocalBrauer.LocalInvariantTorsion

/-!
# Universe-polymorphic finite local relative Brauer cardinality

The categorical `H²` presentation used in Chapter III is currently confined to
universe zero.  The relative Brauer group itself has no such restriction.
Once local invariant base change is known, its kernel is explicitly the
degree-torsion subgroup of `ℚ/ℤ`; this proves the needed cardinality in every
universe without resizing cohomology.
-/

namespace Submission.CField.LBrauer

noncomputable section

open BGroups CProduca

universe u

variable (K L : Type u)
  [NontriviallyNormedField K] [IsUltrametricDist K] [ValuativeRel K]
  [IsNonarchimedeanLocalField K]
  [Valuation.Compatible (NormedField.valuation (K := K))]
  [NontriviallyNormedField L] [IsUltrametricDist L] [ValuativeRel L]
  [IsNonarchimedeanLocalField L]
  [Valuation.Compatible (NormedField.valuation (K := L))]
  [Algebra K L] [FiniteDimensional K L]

/-- Local invariant base change identifies the relative Brauer group with
the subgroup of local invariants killed by the extension degree. -/
noncomputable def relativeTorsionChange
    (hbase : BCForm K L) :
    relativeBrauerGroup K L ≃*
      Multiplicative (localInvariantTorsion (Module.finrank K L)) := by
  let n := Module.finrank K L
  letI : NeZero n :=
    ⟨Nat.ne_of_gt (Module.finrank_pos (R := K) (M := L))⟩
  let invK := carryBrauerInvariant K
  let invL := carryBrauerInvariant L
  let toTorsion : relativeBrauerGroup K L →*
      Multiplicative (localInvariantTorsion n) :=
    { toFun := fun x ↦ ⟨invK x.1, by
          change n • (invK x.1).toAdd = 0
          have hx : (invK x.1) ^ n = 1 := by
            rw [← hbase, x.property, map_one]
          exact Multiplicative.toAdd.injective <| by simpa using hx
          ⟩
      map_one' := by
        apply Subtype.ext
        exact map_one invK
      map_mul' := by
        intro x y
        apply Subtype.ext
        exact map_mul invK x.1 y.1 }
  let fromTorsion : Multiplicative (localInvariantTorsion n) →
      relativeBrauerGroup K L := fun y ↦
    ⟨invK.symm y.toAdd.1, by
      rw [relative_brauer_group]
      apply invL.injective
      rw [hbase, map_one, invK.apply_symm_apply]
      change Multiplicative.ofAdd (y.toAdd.1) ^ n = 1
      exact Multiplicative.toAdd.injective <| by simp⟩
  exact
    { toFun := toTorsion
      invFun := fromTorsion
      left_inv := by
        intro x
        apply Subtype.ext
        exact invK.left_inv x.1
      right_inv := by
        intro y
        apply Multiplicative.toAdd.injective
        apply Subtype.ext
        exact invK.right_inv y.toAdd.1
      map_mul' := map_mul toTorsion }

/-- The relative Brauer group of a finite Galois local extension has order
equal to the extension degree, in every universe, conditional only on the
local invariant base-change formula. -/
theorem relative_brauer_change
    (hbase : BCForm K L) :
    Nat.card (relativeBrauerGroup K L) = Module.finrank K L := by
  let n := Module.finrank K L
  letI : NeZero n :=
    ⟨Nat.ne_of_gt (Module.finrank_pos (R := K) (M := L))⟩
  calc
    Nat.card (relativeBrauerGroup K L) =
        Nat.card (Multiplicative (localInvariantTorsion n)) :=
      Nat.card_congr
        (relativeTorsionChange K L hbase).toEquiv
    _ = Nat.card (localInvariantTorsion n) := rfl
    _ = Nat.card (ZMod n) :=
      Nat.card_congr (torsionZMod n).symm.toEquiv
    _ = n := Nat.card_zmod n

/-- Spectral form of the universe-polymorphic relative cardinality theorem.
The extension field receives its canonical finite-local-field structure
internally. -/
theorem relative_spectral_change
    (E : Type u) [Field E] [Algebra K E] [FiniteDimensional K E]
    (hbase : SpectralChangeFormula K E) :
    Nat.card (relativeBrauerGroup K E) = Module.finrank K E := by
  letI : Algebra.IsAlgebraic K E := Algebra.IsAlgebraic.of_finite K E
  letI : NontriviallyNormedField E :=
    FLExt.nontriviallyNormedField K E
  letI : NormedAlgebra K E := spectralNorm.normedAlgebra K E
  letI : IsUltrametricDist E := IsUltrametricDist.of_normedAlgebra K
  letI : ValuativeRel E := FLExt.valuativeRel K E
  letI : Valuation.Compatible (NormedField.valuation (K := E)) :=
    Valuation.Compatible.ofValuation (NormedField.valuation (K := E))
  letI : IsNonarchimedeanLocalField E :=
    FLExt.nonarchimedeanLocalField K E
  change BCForm K E at hbase
  exact relative_brauer_change K E hbase

end

end Submission.CField.LBrauer
