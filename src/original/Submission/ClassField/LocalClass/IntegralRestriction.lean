import Submission.ClassField.CohomologyOps.BotEquivFun
import Submission.ClassField.CohomologyOps.ZeroCoinducedSucc
import Submission.ClassField.LocalClass.ExpUnitHom

/-!
# Integral restriction of regular lattices

The normal-basis lattice of Lemma III.2.3 remains cohomologically acyclic
after forgetting its `O_K`-module structure and retaining only the underlying
integral Galois module.  This is the coefficient-ring form needed for
Herbrand quotients of multiplicative groups.
-/

namespace Submission.CField.LClass

open CategoryTheory MonoidalCategory Rep
open scoped TensorProduct

noncomputable section

/-- Forget the coefficient ring of a representation down to its underlying
integral representation. -/
noncomputable abbrev Rep.intRestriction
    (A G : Type) [CommRing A] [Group G] (V : Rep A G) : Rep ℤ G :=
  Rep.of {
    toFun := fun g ↦ (V.ρ g).toAddMonoidHom.toIntLinearMap
    map_one' := by ext; simp
    map_mul' := by
      intro g h
      ext x
      simp [Module.End.mul_apply] }

@[simp]
theorem Rep.intRestriction_ρ_apply
    (A G : Type) [CommRing A] [Group G] (V : Rep A G)
    (g : G) (x : V) :
    (Rep.intRestriction A G V).ρ g x = V.ρ g x := rfl

/-- Restriction to integral coefficients preserves representation
isomorphisms. -/
noncomputable def Rep.intRestrictionIso
    (A G : Type) [CommRing A] [Group G] {V W : Rep A G}
    (e : V ≅ W) :
    Rep.intRestriction A G V ≅ Rep.intRestriction A G W := by
  let eA := Representation.equivOfIso e
  apply Rep.mkIso
  apply Representation.Equiv.mk eA.toAddEquiv.toIntLinearEquiv
  intro g
  apply LinearMap.ext
  intro x
  exact LinearMap.congr_fun (eA.toIntertwiningMap.2 g) x

/-- The integral restriction of the regular `A`-representation is
coinduced from the trivial subgroup, with coefficient group `A`. -/
noncomputable def Rep.intrestrict_leftregular_isocoind
    (A G : Type) [CommRing A] [Group G] [Finite G] :
    Rep.intRestriction A G (Rep.leftRegular A G) ≅
      Rep.coind (⊥ : Subgroup G).subtype
        (Rep.trivial ℤ (⊥ : Subgroup G) A) := by
  classical
  let T := Rep.leftRegular ℤ G ⊗ Rep.trivial ℤ G A
  let eF : T ≅ Rep.intRestriction A G (Rep.leftRegular A G) := by
    apply Rep.mkIso
    apply Representation.Equiv.mk
      (TensorProduct.finsuppScalarLeft ℤ A G)
    intro g
    apply LinearMap.ext
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul p a =>
        ext h
        simp [Representation.ofMulAction_apply,
          TensorProduct.finsuppScalarLeft_apply_tmul_apply]
    | add x y hx hy =>
        simpa only [map_add] using congrArg₂ (· + ·) hx hy
  exact eF.symm.trans
    (Submission.CField.COps.coindRegularTensor
      (k := ℤ) (G := G) A).symm

/-- Positive cohomology of an integral restriction of a regular
representation vanishes. -/
theorem cohomology_restriction_regular
    (A G : Type) [CommRing A] [Group G] [Finite G]
    (r : ℕ) (hr : 0 < r) :
    Limits.IsZero (groupCohomology
      (Rep.intRestriction A G (Rep.leftRegular A G)) r) := by
  let C := Rep.trivial ℤ (⊥ : Subgroup G) A
  have hC := Submission.CField.COps.zero_cohomology_coinduced C r hr
  exact hC.of_iso ((groupCohomology.functor ℤ G r).mapIso
    (Rep.intrestrict_leftregular_isocoind A G))

/-- The integral normal-basis lattice has zero positive-degree group
cohomology even after forgetting from `A`-modules to abelian groups. -/
theorem cohomology_basis_int
    (A K L : Type) [CommRing A] [IsDomain A]
    [Field K] [Field L] [Algebra A K] [IsFractionRing A K]
    [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    [FiniteDimensional K L] [IsGalois K L]
    (d : A) (hd : d ≠ 0) (r : ℕ) (hr : 0 < r) :
    Limits.IsZero (groupCohomology
      (Rep.intRestriction A Gal(L/K)
        (integralBasisRepresentation A K L d hd)) r) := by
  have hreg := cohomology_restriction_regular
    A Gal(L/K) r hr
  exact hreg.of_iso ((groupCohomology.functor ℤ Gal(L/K) r).mapIso
    (Rep.intRestrictionIso A Gal(L/K)
      (representationIsoRegular A K L d hd)).symm)

end

end Submission.CField.LClass
