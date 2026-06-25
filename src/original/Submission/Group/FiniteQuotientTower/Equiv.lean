import Submission.Group.InverseLimit


noncomputable section

namespace Submission
namespace Group

universe u

namespace cSQuotie

/--
A levelwise multiplicative equivalence between two compatible finite quotient
towers, commuting with every transition map.
-/
structure CMEquiv
    (S T : cSQuotie.{u}) where
  equiv : ∀ n, S.obj n ≃* T.obj n
  equiv_comm :
    ∀ {m n : ℕ} (hmn : m ≤ n),
      (equiv m).toMonoidHom.comp (S.map hmn) =
        (T.map hmn).comp (equiv n).toMonoidHom

namespace CMEquiv

variable
    {S T U : cSQuotie.{u}}
    (E : CMEquiv S T)

/--
The identity compatible tower equivalence.
-/
def refl
    (S : cSQuotie.{u}) :
    CMEquiv S S where
  equiv := fun n => MulEquiv.refl (S.obj n)
  equiv_comm := by
    intro m n hmn
    ext x
    rfl

/--
Invert a compatible tower equivalence levelwise.
-/
def symm :
    CMEquiv T S where
  equiv := fun n => (E.equiv n).symm
  equiv_comm := by
    intro m n hmn
    ext x
    apply (E.equiv m).injective
    change E.equiv m ((E.equiv m).symm (T.map hmn x)) =
      E.equiv m (S.map hmn ((E.equiv n).symm x))
    rw [MulEquiv.apply_symm_apply]
    have hcomm := DFunLike.congr_fun (E.equiv_comm hmn) ((E.equiv n).symm x)
    change E.equiv m (S.map hmn ((E.equiv n).symm x)) =
      T.map hmn (E.equiv n ((E.equiv n).symm x)) at hcomm
    rw [MulEquiv.apply_symm_apply] at hcomm
    exact hcomm.symm

/--
Compose compatible tower equivalences levelwise.
-/
def trans
    (F : CMEquiv T U) :
    CMEquiv S U where
  equiv := fun n => (E.equiv n).trans (F.equiv n)
  equiv_comm := by
    intro m n hmn
    ext x
    change F.equiv m (E.equiv m (S.map hmn x)) =
      U.map hmn (F.equiv n (E.equiv n x))
    calc
      F.equiv m (E.equiv m (S.map hmn x)) =
          F.equiv m (T.map hmn (E.equiv n x)) := by
        exact congrArg (F.equiv m) (DFunLike.congr_fun (E.equiv_comm hmn) x)
      _ = U.map hmn (F.equiv n (E.equiv n x)) :=
        DFunLike.congr_fun (F.equiv_comm hmn) (E.equiv n x)

/--
The compatible map from the source inverse limit to the target inverse limit
obtained by applying the finite-level equivalences coordinatewise.
-/
def inverseLimitMap :
    inverseLimit S →* inverseLimit T :=
  inverseLimitLift
    T
    (fun n => (E.equiv n).toMonoidHom.comp (inverseLimitProjection S n))
    (by
      intro m n hmn
      ext x
      change T.map hmn (E.equiv n (inverseLimitProjection S n x)) =
        E.equiv m (inverseLimitProjection S m x)
      rw [← limit_projection_compat S hmn x]
      exact (DFunLike.congr_fun (E.equiv_comm hmn)
        (inverseLimitProjection S n x)).symm)

/--
Every target coordinate of the inverse-limit map is the source coordinate,
followed by the corresponding finite-level equivalence.
-/
lemma limit_projection_comp
    (n : ℕ) :
    (inverseLimitProjection T n).comp E.inverseLimitMap =
      (E.equiv n).toMonoidHom.comp (inverseLimitProjection S n) := by
  exact limit_projection_lift
    T
    (fun n => (E.equiv n).toMonoidHom.comp (inverseLimitProjection S n))
    (by
      intro m n hmn
      ext x
      change T.map hmn (E.equiv n (inverseLimitProjection S n x)) =
        E.equiv m (inverseLimitProjection S m x)
      rw [← limit_projection_compat S hmn x]
      exact (DFunLike.congr_fun (E.equiv_comm hmn)
        (inverseLimitProjection S n x)).symm)
    n

/--
Applying the inverse compatible tower equivalence after the forward
inverse-limit map is the identity.
-/
lemma symm_limit_comp :
    E.symm.inverseLimitMap.comp E.inverseLimitMap =
      MonoidHom.id (inverseLimit S) := by
  ext x n
  change (E.equiv n).symm (E.equiv n (inverseLimitProjection S n x)) =
    inverseLimitProjection S n x
  exact (E.equiv n).symm_apply_apply _

/--
Applying the forward compatible tower equivalence after the inverse
inverse-limit map is the identity.
-/
lemma limit_comp_symm :
    E.inverseLimitMap.comp E.symm.inverseLimitMap =
      MonoidHom.id (inverseLimit T) := by
  ext x n
  change E.equiv n ((E.equiv n).symm (inverseLimitProjection T n x)) =
    inverseLimitProjection T n x
  exact (E.equiv n).apply_symm_apply _

/--
A compatible levelwise multiplicative equivalence of finite quotient towers
induces a multiplicative equivalence of inverse limits.
-/
def inverseLimitEquiv :
    inverseLimit S ≃* inverseLimit T where
  toFun := E.inverseLimitMap
  invFun := E.symm.inverseLimitMap
  left_inv := by
    intro x
    exact DFunLike.congr_fun E.symm_limit_comp x
  right_inv := by
    intro x
    exact DFunLike.congr_fun E.limit_comp_symm x
  map_mul' x y := E.inverseLimitMap.map_mul x y

/--
The inverse-limit equivalence is induced by the coordinatewise inverse-limit
map.
-/
lemma inverse_limit_monoid :
    E.inverseLimitEquiv.toMonoidHom = E.inverseLimitMap := by
  rfl

/--
Inverse-limit equivalences transport every coordinate by the corresponding
finite-level equivalence.
-/
lemma limitProjectionMonoid
    (n : ℕ) :
    (inverseLimitProjection T n).comp E.inverseLimitEquiv.toMonoidHom =
      (E.equiv n).toMonoidHom.comp (inverseLimitProjection S n) := by
  rw [E.inverse_limit_monoid]
  exact E.limit_projection_comp n

end CMEquiv

end cSQuotie

end Group
end Submission
