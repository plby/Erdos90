import Mathlib.RingTheory.Norm.Transitivity

/-!
# Norm groups

This file records the elementary norm-group facts used before local reciprocity
in Milne's Chapter I.  The norm group is the image of the algebra norm on unit
groups.  Norm transitivity reverses inclusions of extensions into inclusions of
norm groups.
-/

namespace Towers.CField.LFTheory

noncomputable section

variable (K L : Type*) [CommRing K] [Ring L] [Algebra K L]

/-- The algebra norm, restricted to the unit groups. -/
def normOnUnits : Lˣ →* Kˣ :=
  Units.map (Algebra.norm K)

/-- The norm group of an algebra extension `L/K`. -/
def normSubgroup : Subgroup Kˣ :=
  (normOnUnits K L).range

/-- The norm on units for the identity extension is the identity map. -/
theorem norm_units_self (K : Type*) [CommRing K] :
    normOnUnits K K = MonoidHom.id Kˣ := by
  ext u
  simp [normOnUnits, Algebra.norm_self]

/-- The norm group of the identity extension is the whole unit group. -/
@[simp]
theorem normSubgroup_self (K : Type*) [CommRing K] :
    normSubgroup K K = ⊤ := by
  rw [normSubgroup, norm_units_self]
  exact MonoidHom.range_eq_top.mpr Function.surjective_id

/-- In a tower `L/F/K`, every norm from `L` to `K` is already a norm from
`F` to `K`.  This is the elementary norm-group inclusion used in the proof of
Milne's Corollary 1.2. -/
theorem norm_subgroup_tower
    (F : Type*) [CommRing F] [Algebra K F] [Algebra F L]
    [IsScalarTower K F L]
    [Module.Free K F] [Module.Finite K F]
    [Module.Free F L] [Module.Finite F L] :
    normSubgroup K L ≤ normSubgroup K F := by
  rintro u ⟨v, rfl⟩
  refine ⟨normOnUnits F L v, ?_⟩
  apply Units.ext
  exact Algebra.norm_norm (R := K) (S := F) (A := L) (a := (v : L))

/-- Algebra-equivalent finite field extensions have the same norm subgroup. -/
theorem norm_alg_equiv
    (K : Type*) [Field K]
    (L E : Type*) [Field L] [Field E]
    [Algebra K L] [Algebra K E]
    [FiniteDimensional K L] [FiniteDimensional K E]
    (e : L ≃ₐ[K] E) :
    normSubgroup K L = normSubgroup K E := by
  ext x
  constructor
  · rintro ⟨u, rfl⟩
    refine ⟨Units.map e.toMonoidHom u, ?_⟩
    apply Units.ext
    exact Algebra.norm_eq_of_algEquiv e (u : L)
  · rintro ⟨u, rfl⟩
    refine ⟨Units.map e.symm.toMonoidHom u, ?_⟩
    apply Units.ext
    exact Algebra.norm_eq_of_algEquiv e.symm (u : E)

end

end Towers.CField.LFTheory
