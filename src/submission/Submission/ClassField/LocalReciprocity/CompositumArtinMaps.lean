import Mathlib.FieldTheory.Galois.GaloisClosure
import Submission.ClassField.LocalReciprocity.ProjectedNormSquare
import Submission.ClassField.LocalReciprocity.LiteralTowerTypes

/-!
# Canonical projected Artin maps for a local compositum tower

For a finite local tower `K ⊆ K' ⊆ M` and a normal abelian intermediate
field `E/K` inside `M`, this file constructs the two Artin homomorphisms in
the norm square directly from Lemma III.3.2.  No compatibility square is an
input: we put `M` in a normal closure over `K`, take the subgroup coming from
`Gal(Ω/K')`, and project the two abelianized Artin maps by restriction to
`E/K` and `M/K'`.

The construction is intentionally local.  The Chapter VII application can
transport it through the chosen finite completions.
-/

namespace Submission.CField.LRecip

open IntermediateField
open Submission.CField.LFTheory
open scoped IsMulCommutative

noncomputable section

/-- Restriction from the upper Galois group to the normal lower field in a
local compositum tower. -/
def localCompositumRestriction
    {K K' M : Type*} [Field K] [Field K'] [Field M]
    [Algebra K K'] [Algebra K' M] [Algebra K M]
    [IsScalarTower K K' M]
    (E : IntermediateField K M) [Normal K E] :
    Gal(M/K') →* Gal(E/K) :=
  (AlgEquiv.restrictNormalHom E).comp
    { toFun := fun sigma => sigma.restrictScalars K
      map_one' := rfl
      map_mul' := fun _ _ => rfl }

section LocalBase

variable (K : Type) [NontriviallyNormedField K] [IsUltrametricDist K]

local instance compositumArtinValuativeRel : ValuativeRel K :=
  ValuativeRel.ofValuation (NormedField.valuation (K := K))

local instance compositumArtinValuationCompatible :
    Valuation.Compatible (NormedField.valuation (K := K)) :=
  Valuation.Compatible.ofValuation (NormedField.valuation (K := K))

variable [IsNonarchimedeanLocalField K] [CharZero K]

/-- The canonical pair of local Artin maps obtained by projecting the norm
square of Lemma III.3.2 through a normal closure. -/
structure CAMaps
    (K' M : Type)
    [Field K'] [Field M]
    [Algebra K K'] [FiniteDimensional K K']
    [Algebra K' M] [Algebra K M] [IsScalarTower K K' M]
    [FiniteDimensional K' M] [IsGalois K' M]
    (E : IntermediateField K M)
    [FiniteDimensional K E] [IsGalois K E]
    [IsMulCommutative Gal(E/K)] [IsMulCommutative Gal(M/K')] where
  lower : Kˣ →* Gal(E/K)
  upper : K'ˣ →* Gal(M/K')
  lower_normalized : lower = abelianArtinHom K E
  projected_square : PSquare
    (normOnUnits K K') lower upper (localCompositumRestriction E)

set_option maxHeartbeats 3000000 in
-- Constructing the normal-closure restriction square unfolds several Galois towers.
set_option synthInstance.maxHeartbeats 500000 in
/-- Construct the canonical local compositum maps.  The ambient extension is
the normal closure of `M/K`; the subgroup is literally the range of scalar
restriction from `Gal(Ω/K')`. -/
noncomputable def CAMaps.canonical
    (K' M : Type)
    [Field K'] [Field M]
    [Algebra K K'] [FiniteDimensional K K']
    [Algebra K' M] [Algebra K M] [IsScalarTower K K' M]
    [FiniteDimensional K' M] [IsGalois K' M]
    (E : IntermediateField K M)
    [FiniteDimensional K E] [IsGalois K E]
    [IsMulCommutative Gal(E/K)] [IsMulCommutative Gal(M/K')] :
    CAMaps K K' M E := by
  letI : FiniteDimensional K M := FiniteDimensional.trans K K' M
  letI : Algebra.IsAlgebraic K M := Algebra.IsAlgebraic.of_finite K M
  letI : IsAlgClosure K (AlgebraicClosure M) := inferInstance
  letI : IsGalois K (AlgebraicClosure M) :=
    IsAlgClosure.isGalois K (AlgebraicClosure M)
  let Omega := IntermediateField.normalClosure K M (AlgebraicClosure M)
  letI : IsGalois K Omega :=
    IsGalois.normalClosure K M (AlgebraicClosure M)
  letI : FiniteDimensional K Omega :=
    normalClosure.is_finiteDimensional K M (AlgebraicClosure M)
  letI : FiniteDimensional M Omega := FiniteDimensional.right K M Omega
  letI : IsScalarTower K M Omega := inferInstance
  letI : IsScalarTower K E M := inferInstance
  letI : Algebra E Omega := inferInstance
  letI : IsScalarTower E M Omega := inferInstance
  letI : IsScalarTower K E Omega := inferInstance
  letI : Algebra K' Omega :=
    ((algebraMap M Omega).comp (algebraMap K' M)).toAlgebra
  letI : IsScalarTower K' M Omega := IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower K K' Omega := IsScalarTower.of_algebraMap_eq' (by
    apply RingHom.ext
    intro x
    change algebraMap K Omega x =
      algebraMap M Omega (algebraMap K' M (algebraMap K K' x))
    calc
      algebraMap K Omega x = algebraMap M Omega (algebraMap K M x) :=
        (IsScalarTower.algebraMap_apply K M Omega x).symm
      _ = algebraMap M Omega
          (algebraMap K' M (algebraMap K K' x)) := by
        rw [IsScalarTower.algebraMap_apply K K' M x])
  letI : FiniteDimensional K' Omega := FiniteDimensional.trans K' M Omega
  let r : Gal(Omega/K') →* Gal(Omega/K) :=
    { toFun := fun sigma => sigma.restrictScalars K
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  let H : Subgroup Gal(Omega/K) := r.range
  let B : IntermediateField K Omega :=
    (IsScalarTower.toAlgHom K K' Omega).fieldRange
  have hr_injective : Function.Injective r := by
    intro sigma tau h
    ext x
    exact congrArg Subtype.val (DFunLike.congr_fun h x)
  have hHB : H = B.fixingSubgroup := by
    ext sigma
    constructor
    · rintro ⟨tau, rfl⟩
      intro x
      have hx := x.2
      change (x : Omega) ∈
        Set.range (IsScalarTower.toAlgHom K K' Omega) at hx
      obtain ⟨y, hy⟩ := hx
      change (r tau) (x : Omega) = x
      rw [← hy]
      change tau (algebraMap K' Omega y) = algebraMap K' Omega y
      exact tau.commutes y
    · intro hsigma
      let tau : Gal(Omega/K') :=
        { sigma with
          commutes' := fun y => by
            have hy : algebraMap K' Omega y ∈ B := by
              change algebraMap K' Omega y ∈
                Set.range (IsScalarTower.toAlgHom K K' Omega)
              exact ⟨y, rfl⟩
            exact hsigma ⟨algebraMap K' Omega y, hy⟩ }
      exact ⟨tau, rfl⟩
  have hfixed : IntermediateField.fixedField H = B := by
    rw [hHB]
    exact IsGalois.fixedField_fixingSubgroup B
  let fB : K' →ₐ[K] Omega := IsScalarTower.toAlgHom K K' Omega
  let eB : K' ≃ₐ[K] B :=
    IntermediateField.topEquiv.symm |>.trans
      ((IntermediateField.equivMap (⊤ : IntermediateField K K') fB).trans
        (IntermediateField.equivOfEq (AlgHom.fieldRange_eq_map fB).symm))
  let eFixed : K' ≃ₐ[K] IntermediateField.fixedField H :=
    eB.trans (IntermediateField.equivOfEq hfixed.symm)
  let upperSource : K'ˣ ≃* (IntermediateField.fixedField H)ˣ :=
    Units.mapEquiv eFixed.toMulEquiv
  have hnorm : (MonoidHom.id Kˣ).comp (normOnUnits K K') =
      (normOnUnits K (IntermediateField.fixedField H)).comp
        upperSource.toMonoidHom := by
    apply MonoidHom.ext
    intro z
    apply Units.ext
    change Algebra.norm K (z : K') = Algebra.norm K (eFixed (z : K'))
    have he : (algebraMap K (IntermediateField.fixedField H)).comp
          (RingEquiv.refl K).toRingHom =
        eFixed.toRingEquiv.toRingHom.comp (algebraMap K K') := by
      apply RingHom.ext
      intro x
      exact eFixed.commutes x |>.symm
    simpa using Algebra.norm_eq_of_equiv_equiv
      (RingEquiv.refl K) eFixed.toRingEquiv he (z : K')
  let rRange : Gal(Omega/K') →* H := r.rangeRestrict
  have hrRange_bijective : Function.Bijective rRange := by
    refine ⟨?_, ?_⟩
    · intro sigma tau h
      apply hr_injective
      exact congrArg Subtype.val h
    · rintro ⟨sigma, ⟨tau, htau⟩⟩
      exact ⟨tau, Subtype.ext htau⟩
  let eH : Gal(Omega/K') ≃* H :=
    MulEquiv.ofBijective rRange hrRange_bijective
  let lowerRestriction : Gal(Omega/K) →* Gal(E/K) :=
    AlgEquiv.restrictNormalHom E
  let upperRestriction : H →* Gal(M/K') :=
    (AlgEquiv.restrictNormalHom M).comp eH.symm.toMonoidHom
  let target : Gal(M/K') →* Gal(E/K) :=
    localCompositumRestriction E
  have hrestriction : lowerRestriction.comp H.subtype =
      target.comp upperRestriction := by
    apply MonoidHom.ext
    intro sigma
    apply AlgEquiv.ext
    intro x
    change (AlgEquiv.restrictNormalHom E (sigma : Gal(Omega/K))) x =
      (AlgEquiv.restrictNormalHom E
        ((AlgEquiv.restrictNormalHom M (eH.symm sigma)).restrictScalars K)) x
    let tau : Gal(Omega/K') := eH.symm sigma
    have htau : r tau = sigma := by
      exact congrArg Subtype.val (eH.apply_symm_apply sigma)
    apply (algebraMap E Omega).injective
    change algebraMap E Omega
        ((sigma : Gal(Omega/K)).restrictNormal E x) =
      algebraMap E Omega
        (((tau.restrictNormal M).restrictScalars K).restrictNormal E x)
    rw [AlgEquiv.restrictNormal_commutes]
    rw [IsScalarTower.algebraMap_apply E M Omega]
    rw [IsScalarTower.algebraMap_apply E M Omega]
    rw [AlgEquiv.restrictNormal_commutes]
    change (sigma : Gal(Omega/K))
        (algebraMap M Omega (algebraMap E M x)) =
      algebraMap M Omega (tau.restrictNormal M (algebraMap E M x))
    rw [AlgEquiv.restrictNormal_commutes]
    rw [← htau]
    rfl
  let D : PNData K Omega H Gal(E/K) Gal(M/K') :=
    PNData.ofRestrictions H Gal(E/K) Gal(M/K')
      lowerRestriction upperRestriction target hrestriction
  let lower : Kˣ →* Gal(E/K) := D.lowerArtin
  let upper : K'ˣ →* Gal(M/K') :=
    D.upperArtin.comp upperSource.toMonoidHom
  refine ⟨lower, upper, ?_, ?_⟩
  · change D.lowerArtin = abelianArtinHom K E
    exact abelianized_restrict_normal K Omega E
  exact PSquare.of_equiv K Omega H D
    (MulEquiv.refl Kˣ) upperSource rfl rfl hnorm rfl

end LocalBase

end

end Submission.CField.LRecip
