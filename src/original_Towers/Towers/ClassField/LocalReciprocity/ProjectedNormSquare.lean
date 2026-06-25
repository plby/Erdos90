import Towers.ClassField.LocalReciprocity.ArtinTowerCompatibility

/-!
# Projected norm squares from Lemma III.3.2

The norm square in Lemma III.3.2 is naturally stated with targets the
abelianizations of an ambient finite Galois group and of a subgroup.  In
applications, including the compositum argument in VII.8.4(b), the two local
Artin maps are obtained by projecting those abelianizations to finite
abelian quotient extensions.  This file records that formal projection
step.
-/

namespace Towers.CField.LRecip

open Towers.CField.LFTheory

noncomputable section

variable (K L : Type)
  [NontriviallyNormedField K] [IsUltrametricDist K]

local instance projectedNormValuativeRel : ValuativeRel K :=
  ValuativeRel.ofValuation (NormedField.valuation (K := K))

local instance projectedNormValuationCompatible :
    Valuation.Compatible (NormedField.valuation (K := K)) :=
  Valuation.Compatible.ofValuation (NormedField.valuation (K := K))

variable [IsNonarchimedeanLocalField K]
  [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]

private abbrev F (H : Subgroup Gal(L/K)) :=
  IntermediateField.fixedField H

/-- A compatible pair of quotient maps out of the two abelianized Galois
groups in the norm square of Lemma III.3.2.  In the compositum application,
`lowerProjection` and `upperProjection` are restriction to the lower field
and its scalar extension, and `targetMap` is restriction between those two
finite layers. -/
structure PNData
    (H : Subgroup Gal(L/K)) (G G' : Type*)
    [CommGroup G] [CommGroup G'] where
  lowerProjection : Abelianization Gal(L/K) →* G
  upperProjection : Abelianization H →* G'
  targetMap : G' →* G
  projections_commute :
    lowerProjection.comp (abelianizedSubgroupInclusion H) =
      targetMap.comp upperProjection

/-- Construct the projected data from the ordinary restriction maps before
abelianization.  This is the form used by a Galois closure in the compositum
argument: the two raw maps are restriction to the lower and upper abelian
layers, and their displayed compatibility is just transitivity of
restriction. -/
noncomputable def PNData.ofRestrictions
    {K L : Type}
    [NontriviallyNormedField K] [IsUltrametricDist K]
    [IsNonarchimedeanLocalField K]
    [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (H : Subgroup Gal(L/K)) (G G' : Type*)
    [CommGroup G] [CommGroup G']
    (lowerRestriction : Gal(L/K) →* G)
    (upperRestriction : H →* G')
    (targetMap : G' →* G)
    (hrestriction : lowerRestriction.comp H.subtype =
      targetMap.comp upperRestriction) :
    PNData K L H G G' where
  lowerProjection := Abelianization.lift lowerRestriction
  upperProjection := Abelianization.lift upperRestriction
  targetMap := targetMap
  projections_commute := by
    apply MonoidHom.ext
    intro x
    obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective (commutator H) x
    change lowerRestriction h = targetMap (upperRestriction h)
    simpa only [MonoidHom.coe_comp, Function.comp_apply] using
      DFunLike.congr_fun hrestriction h

namespace PNData

variable {K L : Type}
  [NontriviallyNormedField K] [IsUltrametricDist K]
  [IsNonarchimedeanLocalField K]
  [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
  {H : Subgroup Gal(L/K)} {G G' : Type*}
  [CommGroup G] [CommGroup G']

/-- The upper local Artin map after projection to the desired finite
abelian layer. -/
noncomputable def upperArtin
    (D : PNData K L H G G') :
    (F K L H)ˣ →* G' :=
  D.upperProjection.comp (fixedArtinHom K L H)

/-- The lower local Artin map after projection to the desired finite
abelian layer. -/
noncomputable def lowerArtin
    (D : PNData K L H G G') :
    Kˣ →* G :=
  D.lowerProjection.comp (localArtinHom K L)

/-- Projecting the canonical norm square of III.3.2 gives the finite-layer
norm square used in the compositum argument. -/
theorem norm_commutes
    (D : PNData K L H G G') :
    D.targetMap.comp D.upperArtin =
      D.lowerArtin.comp (normOnUnits K (F K L H)) := by
  have h32 := (artinTowerCompatibility K L H).1
  unfold NormSquare at h32
  apply MonoidHom.ext
  intro x
  have hproj :
      D.lowerProjection
          (abelianizedSubgroupInclusion H (fixedArtinHom K L H x)) =
        D.targetMap (D.upperProjection (fixedArtinHom K L H x)) := by
    simpa only [MonoidHom.coe_comp, Function.comp_apply] using
      DFunLike.congr_fun D.projections_commute
        (fixedArtinHom K L H x)
  have hnorm :
      abelianizedSubgroupInclusion H (fixedArtinHom K L H x) =
        localArtinHom K L (normOnUnits K (F K L H) x) := by
    simpa only [MonoidHom.coe_comp, Function.comp_apply] using
      DFunLike.congr_fun h32 x
  change D.targetMap (D.upperProjection (fixedArtinHom K L H x)) =
    D.lowerProjection
      (localArtinHom K L (normOnUnits K (F K L H) x))
  rw [← hproj, hnorm]

end PNData

/-! ### Transported presentations -/

/-- A norm/Artin square is *canonically presented by III.3.2* when its
source groups are identified with the unit groups in one of the projected
norm squares above and all four arrows are the transported canonical
arrows.  This proposition is useful for completion models: their carrier
types rarely agree definitionally with the fixed-field model used in
`artinTowerCompatibility`, although the relevant multiplicative groups are canonically
equivalent. -/
inductive PSquare
    {A A' G G' : Type*}
    [CommGroup A] [CommGroup A'] [CommGroup G] [CommGroup G']
    (norm : A' →* A) (lower : A →* G) (upper : A' →* G')
    (targetMap : G' →* G) : Prop where
  | of_equiv
      (K L : Type)
      [NontriviallyNormedField K] [IsUltrametricDist K]
      [IsNonarchimedeanLocalField K]
      [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
      (H : Subgroup Gal(L/K))
      (D : PNData K L H G G')
      (lowerSource : A ≃* Kˣ)
      (upperSource : A' ≃* (F K L H)ˣ)
      (hlower : lower = D.lowerArtin.comp lowerSource.toMonoidHom)
      (hupper : upper = D.upperArtin.comp upperSource.toMonoidHom)
      (hnorm : lowerSource.toMonoidHom.comp norm =
        (normOnUnits K (F K L H)).comp upperSource.toMonoidHom)
      (htarget : targetMap = D.targetMap) :
      PSquare norm lower upper targetMap

namespace PSquare

variable {A A' G G' : Type*}
  [CommGroup A] [CommGroup A'] [CommGroup G] [CommGroup G']
  {norm : A' →* A} {lower : A →* G} {upper : A' →* G'}
  {targetMap : G' →* G}

/-- Every square possessing a transported III.3.2 presentation commutes. -/
theorem commutes
    (h : PSquare norm lower upper targetMap) :
    targetMap.comp upper = lower.comp norm := by
  cases h with
  | @of_equiv K L _ _ _ _ _ _ _ H D lowerSource upperSource
      hlower hupper hnorm htarget =>
      subst lower
      subst upper
      subst targetMap
      apply MonoidHom.ext
      intro x
      have hsquare :
          D.targetMap (D.upperArtin (upperSource x)) =
            D.lowerArtin (normOnUnits K (F K L H) (upperSource x)) := by
        simpa only [MonoidHom.coe_comp, Function.comp_apply] using
          DFunLike.congr_fun D.norm_commutes (upperSource x)
      have hnormx :
          lowerSource (norm x) =
            normOnUnits K (F K L H) (upperSource x) := by
        simpa only [MonoidHom.coe_comp, Function.comp_apply] using
          DFunLike.congr_fun hnorm x
      change D.targetMap (D.upperArtin (upperSource x)) =
        D.lowerArtin (lowerSource (norm x))
      rw [hsquare, hnormx]

/-- Postcompose both Artin maps with compatible homomorphisms of their
targets.  The resulting square still has a literal projected III.3.2
presentation; this is used to embed completion Galois groups into global
decomposition groups. -/
theorem postcompose
    {B B' : Type*} [CommGroup B] [CommGroup B']
    (h : PSquare norm lower upper targetMap)
    (lowerMap : G →* B) (upperMap : G' →* B')
    (newTarget : B' →* B)
    (hcompat : lowerMap.comp targetMap = newTarget.comp upperMap) :
    PSquare norm
      (lowerMap.comp lower) (upperMap.comp upper) newTarget := by
  cases h with
  | @of_equiv K L _ _ _ _ _ _ _ H D lowerSource upperSource
      hlower hupper hnorm htarget =>
      let D' : PNData K L H B B' :=
        { lowerProjection := lowerMap.comp D.lowerProjection
          upperProjection := upperMap.comp D.upperProjection
          targetMap := newTarget
          projections_commute := by
            rw [MonoidHom.comp_assoc, D.projections_commute,
              ← MonoidHom.comp_assoc, ← htarget, hcompat,
              MonoidHom.comp_assoc] }
      refine .of_equiv K L H D' lowerSource upperSource ?_ ?_ hnorm rfl
      · rw [hlower]
        rfl
      · rw [hupper]
        rfl

/-- Transport both source groups through multiplicative equivalences. -/
theorem precompose
    {B B' : Type*} [CommGroup B] [CommGroup B']
    (h : PSquare norm lower upper targetMap)
    (lowerSource : B ≃* A) (upperSource : B' ≃* A')
    (newNorm : B' →* B)
    (hnorm : lowerSource.toMonoidHom.comp newNorm =
      norm.comp upperSource.toMonoidHom) :
    PSquare newNorm
      (lower.comp lowerSource.toMonoidHom)
      (upper.comp upperSource.toMonoidHom) targetMap := by
  cases h with
  | @of_equiv K L _ _ _ _ _ _ _ H D oldLower oldUpper
      hlower hupper holdNorm htarget =>
      refine .of_equiv K L H D
        (lowerSource.trans oldLower) (upperSource.trans oldUpper)
        ?_ ?_ ?_ htarget
      · rw [hlower]
        rfl
      · rw [hupper]
        rfl
      · change oldLower.toMonoidHom.comp
            (lowerSource.toMonoidHom.comp newNorm) =
          (normOnUnits K (F K L H)).comp
            (oldUpper.toMonoidHom.comp upperSource.toMonoidHom)
        rw [hnorm, ← MonoidHom.comp_assoc, holdNorm,
          MonoidHom.comp_assoc]

end PSquare

end

end Towers.CField.LRecip
