import Towers.ClassField.BrauerGroups.FinrankSimpleSquare
import Towers.ClassField.CrossedProducts.SubalgebraField
import Towers.ClassField.CrossedProducts.EndRestrictScalars

/-!
# Chapter IV, Section 4: degrees of subfields of a division algebra

Milne uses that the degree of every commutative subfield of a central
division algebra divides the degree of the division algebra.  The proof is a
dimension calculation with the centralizer, regarded as a central simple
algebra over the subfield.
-/

namespace Towers.CField.LBrauer

noncomputable section

universe u

open BGroups CProduca

variable (K D : Type u) [Field K] [DivisionRing D] [Algebra K D]
  [Algebra.IsCentral K D] [Module.Finite K D]

/-- A commutative subfield of a central division algebra has degree dividing
the square root of the dimension of the algebra. -/
theorem commutative_subalgebra_sqrt
    (E : Subalgebra K D) (hcomm : ∀ x y : E, x * y = y * x) :
    Module.finrank K E ∣ Nat.sqrt (Module.finrank K D) := by
  let C := Subalgebra.centralizer K (E : Set D)
  letI : CommRing E := { (inferInstance : Ring E) with mul_comm := hcomm }
  letI : Module.Finite K E :=
    Module.Finite.of_injective E.val.toLinearMap Subtype.val_injective
  letI : IsDomain E :=
    Function.Injective.isDomain E.val.toRingHom Subtype.val_injective
  letI : Field E := fieldOfFiniteDimensional K E
  letI : IsSimpleRing E := inferInstance
  letI : Module.Finite K C :=
    Module.Finite.of_injective C.val.toLinearMap Subtype.val_injective
  letI : IsSimpleRing C := centralizer_simple_ring K D E
  have hEC : E ≤ C := by
    intro x hx
    rw [Subalgebra.mem_centralizer_iff]
    intro y hy
    exact congrArg Subtype.val (hcomm ⟨y, hy⟩ ⟨x, hx⟩)
  letI : Algebra E C :=
    (Subalgebra.inclusion hEC).toRingHom.toAlgebra' fun e c => by
      apply Subtype.ext
      exact Iff.mp (Subalgebra.mem_centralizer_iff K) c.2 e e.2
  letI : IsScalarTower K E C := IsScalarTower.of_algebraMap_eq fun x => by
    apply Subtype.ext
    rfl
  letI : Module.Finite E C :=
    Module.Finite.of_restrictScalars_finite K E C
  letI : Algebra.IsCentral E C := by
    constructor
    intro z hz
    rw [Subalgebra.mem_center_iff] at hz
    have hzdouble : (z : D) ∈ Subalgebra.centralizer K (C : Set D) := by
      rw [Subalgebra.mem_centralizer_iff]
      intro c hc
      exact congrArg Subtype.val (hz ⟨c, hc⟩)
    have hzE : (z : D) ∈ E := by
      rw [centralizer_centralizer_eq K D E] at hzdouble
      exact hzdouble
    rw [Algebra.mem_bot]
    refine ⟨⟨z, hzE⟩, ?_⟩
    apply Subtype.ext
    rfl
  obtain ⟨r, hr⟩ := finrank_simple_square E C
  have hKC : Module.finrank K C =
      Module.finrank K E * Module.finrank E C :=
    (Module.finrank_mul_finrank K E C).symm
  have hcentral : Module.finrank K E * Module.finrank K C =
      Module.finrank K D :=
    finrank_mul_centralizer K D E
  have hD : Module.finrank K D =
      (Module.finrank K E * r) ^ 2 := by
    calc
      Module.finrank K D = Module.finrank K E * Module.finrank K C :=
        hcentral.symm
      _ = Module.finrank K E *
          (Module.finrank K E * Module.finrank E C) := by rw [hKC]
      _ = Module.finrank K E * (Module.finrank K E * r ^ 2) := by rw [hr]
      _ = (Module.finrank K E * r) ^ 2 := by ring
  rw [hD, Nat.sqrt_eq']
  exact dvd_mul_right _ _

end

end Towers.CField.LBrauer
