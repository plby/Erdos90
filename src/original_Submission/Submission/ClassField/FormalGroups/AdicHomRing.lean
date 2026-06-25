import Mathlib.Algebra.Group.Hom.End
import Submission.ClassField.FormalGroups.AdicGroupHom
import Submission.ClassField.FormalGroups.HomGroupRing

/-!
# Class Field Theory, Chapter I: the evaluated endomorphism ring

Evaluation on an adic ideal respects the additive group structure on formal
homomorphisms.  For endomorphisms it also respects multiplication, since
both formal multiplication and multiplication of additive endomorphisms are
composition in the same order.
-/

namespace Submission.CField.FGroups

open Filter MvPowerSeries
open scoped MvPowerSeries.WithPiTopology

variable {R : Type*} [CommRing R] [UniformSpace R] [IsUniformAddGroup R]
  [IsTopologicalRing R] [T2Space R] [CompleteSpace R]

namespace FGLaw

noncomputable section

namespace Hom

variable {I : Ideal R} (hI : IsAdic I)
  {F G : FGLaw R}

/-- Evaluation sends the zero formal homomorphism to the zero additive
homomorphism. -/
@[simp]
theorem adicMap_zero : ((0 : Hom F G).adicMap hI) = 0 := by
  ext x
  rw [adicMap_apply]
  change (((0 : Hom F G).adicValue hI
    (APts.toIdeal hI F x) : I) : R) = 0
  rw [FGLaw.Hom.coe_adicValue]
  rw [zero_toSeries']
  change eval₂ (RingHom.id R)
      (fun _ ↦ (APts.toIdeal hI F x : R))
      ((0 : MvPolynomial (Fin 1) R) : UnarySeries R) = 0
  rw [eval₂_coe]
  simp

/-- Evaluation respects Milne's addition of formal homomorphisms. -/
@[simp]
theorem adicMap_add (f g : Hom F G) :
    (f + g).adicMap hI = f.adicMap hI + g.adicMap hI := by
  ext x
  rw [adicMap_apply]
  change (((f + g).adicValue hI
    (APts.toIdeal hI F x) : I) : R) =
      (((f.adicMap hI x + g.adicMap hI x : APts hI G) : I) : R)
  rw [FGLaw.Hom.coe_adicValue, add_toSeries',
    APts.coe_add, adicMap_apply, adicMap_apply,
    FGLaw.coe_adicValue]
  let a : Fin 1 → R := fun _ ↦ (APts.toIdeal hI F x : R)
  have ha : ∀ i, a i ∈ I := fun _ ↦ (APts.toIdeal hI F x).2
  have h := mv_series_eval₂_subst_of_forall_constantCoeff_zero_adic
    hI (Fin.cases f.toSeries (fun _ ↦ g.toSeries))
    (fun i ↦ Fin.cases f.constant_coeff_zero
      (fun _ ↦ g.constant_coeff_zero) i) a ha G.law
  change eval₂ (RingHom.id R) a
      (substitute G.law f.toSeries g.toSeries) = _ at h
  change eval₂ (RingHom.id R) a
      (substitute G.law f.toSeries g.toSeries) = _
  rw [h]
  congr 2
  funext i
  fin_cases i <;> rfl

/-- Evaluation of formal endomorphisms as a homomorphism into the ring of
additive endomorphisms of the adic formal group. -/
noncomputable def adicEndHom (F : FGLaw R) :
    Hom F F →+* AddMonoid.End (APts hI F) where
  toFun f := f.adicMap hI
  map_zero' := adicMap_zero hI
  map_one' := by
    change (Hom.id F).adicMap hI = AddMonoidHom.id _
    exact adicMap_id hI
  map_add' f g := adicMap_add hI f g
  map_mul' f g := by
    change (Hom.comp f g).adicMap hI =
      (f.adicMap hI).comp (g.adicMap hI)
    exact adicMap_comp hI f g

@[simp]
theorem adic_end_hom (F : FGLaw R) (f : Hom F F) :
    adicEndHom hI F f = f.adicMap hI := rfl

end Hom

end


end FGLaw

end Submission.CField.FGroups
