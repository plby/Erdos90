import Towers.ClassField.LocalClass.IntegralRestriction
import Towers.ClassField.LocalClass.HerbrandTransfer
import Towers.ClassField.LocalClass.ValuationSequence
import Towers.ClassField.LocalExistence.ConcreteLocalExistence

/-!
# Open local-unit lattices and Herbrand transfer

This file carries out the compactness step in Lemma III.2.5.  A naturally
Galois-stable open subgroup near `1` is an integral representation, maps
into `U_L`, and has finite-index image because `U_L` is compact.
-/

namespace Towers.CField.LClass

open CategoryTheory CategoryTheory.Limits
open Towers.CField.LFTheory
open Towers.CField.LExist
open Towers.CField.LBrauer

noncomputable section

attribute [local instance] Units.mulDistribMulActionRight

universe u

/-- Restrict the natural Galois action on `Lˣ` to a stable subgroup. -/
@[implicit_reducible]
noncomputable def stableDistribAction
    (K L : Type u) [Field K] [Field L] [Algebra K L] [IsGalois K L]
    (U : Subgroup Lˣ)
    (hstable : ∀ (g : Gal(L/K)) (u : Lˣ), u ∈ U → g • u ∈ U) :
    MulDistribMulAction Gal(L/K) U where
  smul g u := ⟨g • (u : Lˣ), hstable g u u.2⟩
  one_smul u := Subtype.ext (one_smul Gal(L/K) (u : Lˣ))
  mul_smul g h u := Subtype.ext (mul_smul g h (u : Lˣ))
  smul_mul g u v := Subtype.ext (smul_mul' g (u : Lˣ) (v : Lˣ))
  smul_one g := Subtype.ext (smul_one g)

/-- The integral representation on a stable multiplicative subgroup. -/
noncomputable abbrev stableUnitRepresentation
    (K L : Type u) [Field K] [Field L] [Algebra K L] [IsGalois K L]
    (U : Subgroup Lˣ)
    (hstable : ∀ (g : Gal(L/K)) (u : Lˣ), u ∈ U → g • u ∈ U) :
    Rep ℤ Gal(L/K) :=
  let _ := stableDistribAction K L U hstable
  Rep.ofMulDistribMulAction Gal(L/K) U

/-- A unit lying at distance less than one from `1` has norm one. -/
theorem norm_one_ball
    (F : Type u) [NontriviallyNormedField F] [IsUltrametricDist F]
    (u : Fˣ) (hu : (u : F) ∈ Metric.ball 1 1) :
    ‖(u : F)‖ = 1 := by
  have hsmall : ‖(u : F) - 1‖ < 1 := by
    simpa only [Metric.mem_ball, dist_eq_norm] using hu
  have hne : ‖(u : F) - 1‖ ≠ ‖(1 : F)‖ := by
    simpa using ne_of_lt hsmall
  calc
    ‖(u : F)‖ = ‖((u : F) - 1) + 1‖ := by
      congr 1
      ring
    _ = max ‖(u : F) - 1‖ ‖(1 : F)‖ :=
      IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hne
    _ = 1 := by simp [max_eq_right (le_of_lt hsmall)]

/-- A subgroup contained in the unit ball around `1` lies in `U_L`. -/
noncomputable def extensionNearOne
    (K L : Type u)
    [NontriviallyNormedField K] [IsUltrametricDist K]
    [ValuativeRel K] [IsNonarchimedeanLocalField K]
    [Field L] [Algebra K L] [Module.Finite K L] [IsGalois K L]
    (U : Subgroup Lˣ) : Prop := by
  letI : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.of_finite K L
  letI : NontriviallyNormedField L :=
    FLExt.nontriviallyNormedField K L
  letI : NormedAlgebra K L := spectralNorm.normedAlgebra K L
  exact Units.val '' (U : Set Lˣ) ⊆ Metric.ball 1 1

/-- A subgroup contained in the unit ball around `1` lies in `U_L`. -/
theorem subgroup_extension_near
    (K L : Type u)
    [NontriviallyNormedField K] [IsUltrametricDist K]
    [ValuativeRel K] [IsNonarchimedeanLocalField K]
    [Field L] [Algebra K L] [Module.Finite K L] [IsGalois K L]
    (U : Subgroup Lˣ)
    (hnear : extensionNearOne K L U) :
    U ≤ extensionUnitSubgroup K L := by
  letI : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.of_finite K L
  letI : NontriviallyNormedField L :=
    FLExt.nontriviallyNormedField K L
  letI : NormedAlgebra K L := spectralNorm.normedAlgebra K L
  letI : IsUltrametricDist L := IsUltrametricDist.of_normedAlgebra K
  letI : ValuativeRel L := FLExt.valuativeRel K L
  letI : Valuation.Compatible (NormedField.valuation (K := L)) :=
    Valuation.Compatible.ofValuation (NormedField.valuation (K := L))
  letI : IsNonarchimedeanLocalField L :=
    FLExt.nonarchimedeanLocalField K L
  change Units.val '' (U : Set Lˣ) ⊆ Metric.ball 1 1 at hnear
  intro u hu
  apply (local_subgroup L u).2
  have hnorm := norm_one_ball L u (hnear ⟨u, hu, rfl⟩)
  have hnnnorm : ‖(u : L)‖₊ = 1 := NNReal.eq hnorm
  apply le_antisymm
  · change ValuativeRel.valuation L (u : L) ≤
        ValuativeRel.valuation L (1 : L)
    rw [← Valuation.Compatible.vle_iff_le]
    change ‖(u : L)‖₊ ≤ ‖(1 : L)‖₊
    simp [hnnnorm]
  · change ValuativeRel.valuation L (1 : L) ≤
        ValuativeRel.valuation L (u : L)
    rw [← Valuation.Compatible.vle_iff_le]
    change ‖(1 : L)‖₊ ≤ ‖(u : L)‖₊
    simp [hnnnorm]

/-- Inclusion of a stable near-one subgroup into the natural local-unit
representation. -/
noncomputable def stableUnitInclusion
    (K L : Type u)
    [NontriviallyNormedField K] [IsUltrametricDist K]
    [ValuativeRel K] [IsNonarchimedeanLocalField K]
    [Field L] [Algebra K L] [Module.Finite K L] [IsGalois K L]
    (U : Subgroup Lˣ)
    (hstable : ∀ (g : Gal(L/K)) (u : Lˣ), u ∈ U → g • u ∈ U)
    (hnear : extensionNearOne K L U) :
    stableUnitRepresentation K L U hstable ⟶
      localUnitRepresentation K L := by
  letI := stableDistribAction K L U hstable
  letI := localDistribAction K L
  let hle := subgroup_extension_near K L U hnear
  apply Rep.ofHom
  let i : Additive U →+ Additive (extensionUnitSubgroup K L) :=
    { toFun := fun u ↦ Additive.ofMul ⟨(u.toMul : Lˣ), hle u.toMul.2⟩
      map_zero' := rfl
      map_add' := fun _ _ ↦ rfl }
  refine ⟨i.toIntLinearMap, ?_⟩
  intro g
  apply LinearMap.ext
  intro u
  rfl

/-- The exponential equivalence of Lemma III.2.4 is an isomorphism after
forgetting the coefficient ring to `ℤ`. -/
noncomputable def restrictionIsoStable
    (A K L : Type) [CommRing A] [IsDomain A]
    [Field K] [Field L] [Algebra A K] [IsFractionRing A K]
    [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    [FiniteDimensional K L] [IsGalois K L]
    (d : A) (hd : d ≠ 0) (U : Subgroup Lˣ)
    (hstable : ∀ (g : Gal(L/K)) (u : Lˣ), u ∈ U → g • u ∈ U)
    (e : (integralBasisRepresentation A K L d hd : Type) ≃+ Additive U)
    (hequiv : ∀ (g : Gal(L/K)) (u : U),
      e ((integralBasisRepresentation A K L d hd).ρ g
          (e.symm (Additive.ofMul u))) =
        Additive.ofMul (⟨g • (u : Lˣ), hstable g (u : Lˣ) u.2⟩ : U)) :
    Rep.intRestriction A Gal(L/K)
        (integralBasisRepresentation A K L d hd) ≅
      stableUnitRepresentation K L U hstable := by
  letI := stableDistribAction K L U hstable
  apply Rep.mkIso
  apply Representation.Equiv.mk e.toIntLinearEquiv
  intro g
  apply LinearMap.ext
  intro x
  let u : U := (e x).toMul
  have h := hequiv g u
  simpa [u] using h

/-- The stable near-one subgroup has vanishing positive integral group
cohomology. -/
theorem cohomology_stable_subgroup
    (A K L : Type) [CommRing A] [IsDomain A]
    [Field K] [Field L] [Algebra A K] [IsFractionRing A K]
    [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    [FiniteDimensional K L] [IsGalois K L]
    (d : A) (hd : d ≠ 0) (U : Subgroup Lˣ)
    (hstable : ∀ (g : Gal(L/K)) (u : Lˣ), u ∈ U → g • u ∈ U)
    (e : (integralBasisRepresentation A K L d hd : Type) ≃+ Additive U)
    (hequiv : ∀ (g : Gal(L/K)) (u : U),
      e ((integralBasisRepresentation A K L d hd).ρ g
          (e.symm (Additive.ofMul u))) =
        Additive.ofMul (⟨g • (u : Lˣ), hstable g (u : Lˣ) u.2⟩ : U))
    (r : ℕ) (hr : 0 < r) :
    IsZero (groupCohomology
      (stableUnitRepresentation K L U hstable) r) := by
  have hzero := cohomology_basis_int
    A K L d hd r hr
  exact hzero.of_iso (((groupCohomology.functor ℤ Gal(L/K) r).mapIso
    (restrictionIsoStable A K L d hd U hstable e hequiv)).symm)

/-- Openness of a subgroup in the canonical spectral topology on `Lˣ`. -/
noncomputable def extensionUnitOpen
    (K L : Type u)
    [NontriviallyNormedField K] [IsUltrametricDist K]
    [ValuativeRel K] [IsNonarchimedeanLocalField K]
    [Field L] [Algebra K L] [Module.Finite K L] [IsGalois K L]
    (U : Subgroup Lˣ) : Prop := by
  letI : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.of_finite K L
  letI : NontriviallyNormedField L :=
    FLExt.nontriviallyNormedField K L
  letI : NormedAlgebra K L := spectralNorm.normedAlgebra K L
  exact IsOpen (U : Set Lˣ)

/-- An open near-one subgroup has finite quotient in the compact local-unit
group. -/
@[implicit_reducible]
noncomputable def localUnitQuotient
    (K L : Type u)
    [NontriviallyNormedField K] [IsUltrametricDist K]
    [ValuativeRel K] [IsNonarchimedeanLocalField K]
    [Field L] [Algebra K L] [Module.Finite K L] [IsGalois K L]
    (U : Subgroup Lˣ)
    (hopen : extensionUnitOpen K L U) :
    Finite ((extensionUnitSubgroup K L) ⧸
      U.subgroupOf (extensionUnitSubgroup K L)) := by
  letI : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.of_finite K L
  letI : NontriviallyNormedField L :=
    FLExt.nontriviallyNormedField K L
  letI : NormedAlgebra K L := spectralNorm.normedAlgebra K L
  letI : IsUltrametricDist L := IsUltrametricDist.of_normedAlgebra K
  letI : ValuativeRel L := FLExt.valuativeRel K L
  letI : Valuation.Compatible (NormedField.valuation (K := L)) :=
    Valuation.Compatible.ofValuation (NormedField.valuation (K := L))
  letI : IsNonarchimedeanLocalField L :=
    FLExt.nonarchimedeanLocalField K L
  change IsOpen (U : Set Lˣ) at hopen
  have hcompact : IsCompact
      (extensionUnitSubgroup K L : Set Lˣ) := by
    change IsCompact (localUnitSubgroup L : Set Lˣ)
    exact Towers.CField.LExist.local_unit_compact L
  letI : CompactSpace (extensionUnitSubgroup K L) :=
    isCompact_iff_compactSpace.mp hcompact
  let V := U.subgroupOf (extensionUnitSubgroup K L)
  have hopenV : IsOpen (V : Set (extensionUnitSubgroup K L)) :=
    (extensionUnitSubgroup K L).subgroupOf_isOpen U hopen
  exact V.quotient_finite_of_isOpen hopenV

/-- The inclusion of an open near-one subgroup has finite categorical
cokernel. -/
@[implicit_reducible]
noncomputable def cokernel_stable_inclusion
    (K L : Type u)
    [NontriviallyNormedField K] [IsUltrametricDist K]
    [ValuativeRel K] [IsNonarchimedeanLocalField K]
    [Field L] [Algebra K L] [Module.Finite K L] [IsGalois K L]
    (U : Subgroup Lˣ)
    (hstable : ∀ (g : Gal(L/K)) (u : Lˣ), u ∈ U → g • u ∈ U)
    (hnear : extensionNearOne K L U)
    (hopen : extensionUnitOpen K L U) :
    Finite ↑(cokernel (stableUnitInclusion K L U hstable hnear) :
      Rep ℤ Gal(L/K)) := by
  let f := stableUnitInclusion K L U hstable hnear
  let V := U.subgroupOf (extensionUnitSubgroup K L)
  letI : Finite ((extensionUnitSubgroup K L) ⧸ V) :=
    localUnitQuotient K L U hopen
  letI : Module ℤ (cokernel f : Rep ℤ Gal(L/K)) :=
    (cokernel f : Rep ℤ Gal(L/K)).hV2
  let π := cokernel.π f
  let φ : (extensionUnitSubgroup K L) →*
      Multiplicative (cokernel f : Rep ℤ Gal(L/K)) :=
    { toFun := fun u ↦ Multiplicative.ofAdd
        (π.hom (Additive.ofMul u))
      map_one' := by
        change Multiplicative.ofAdd (π.hom 0) = Multiplicative.ofAdd 0
        rw [map_zero]
      map_mul' := fun u v ↦ by
        apply Multiplicative.toAdd.injective
        change π.hom (Additive.ofMul u + Additive.ofMul v) =
          π.hom (Additive.ofMul u) + π.hom (Additive.ofMul v)
        exact π.hom.toAddMonoidHom.map_add _ _ }
  have hV : V ≤ φ.ker := by
    intro v hv
    let u : U := ⟨((v : extensionUnitSubgroup K L) : Lˣ), hv⟩
    have hc := congrArg
      (fun q : stableUnitRepresentation K L U hstable ⟶
          (cokernel f : Rep ℤ Gal(L/K)) ↦ q.hom (Additive.ofMul u))
      (cokernel.condition f)
    change π.hom (Additive.ofMul (v : extensionUnitSubgroup K L)) = 0 at hc
    change Multiplicative.ofAdd
      (π.hom (Additive.ofMul (v : extensionUnitSubgroup K L))) =
        Multiplicative.ofAdd 0
    exact congrArg Multiplicative.ofAdd hc
  let qφ := QuotientGroup.lift V φ hV
  have hsurj : Function.Surjective qφ := by
    intro y
    obtain ⟨x, hx⟩ :=
      (Rep.epi_iff_surjective π).1 (inferInstance : Epi π) y.toAdd
    refine ⟨QuotientGroup.mk' V x.toMul, ?_⟩
    apply Multiplicative.toAdd.injective
    exact hx
  exact Finite.of_surjective qφ hsurj

/-- The inclusion of a stable subgroup has finite (indeed trivial) kernel. -/
@[implicit_reducible]
noncomputable def stable_unit_inclusion
    (K L : Type u)
    [NontriviallyNormedField K] [IsUltrametricDist K]
    [ValuativeRel K] [IsNonarchimedeanLocalField K]
    [Field L] [Algebra K L] [Module.Finite K L] [IsGalois K L]
    (U : Subgroup Lˣ)
    (hstable : ∀ (g : Gal(L/K)) (u : Lˣ), u ∈ U → g • u ∈ U)
    (hnear : extensionNearOne K L U) :
    Finite ↑(kernel (stableUnitInclusion K L U hstable hnear) :
      Rep ℤ Gal(L/K)) := by
  let f := stableUnitInclusion K L U hstable hnear
  letI : Mono f := (Rep.mono_iff_injective f).2 fun x y hxy ↦
    Additive.toMul.injective (Subtype.ext
      (congrArg (fun z : Additive (extensionUnitSubgroup K L) ↦
        ((z.toMul : extensionUnitSubgroup K L) : Lˣ)) hxy))
  have hzero : IsZero (kernel f) := isZero_kernel_of_mono f
  letI : Subsingleton ↑(kernel f : Rep ℤ Gal(L/K)) := by
    constructor
    intro x y
    have hid : 𝟙 (kernel f) = 0 := hzero.eq_of_src _ _
    have hx := congrArg (fun q : kernel f ⟶ kernel f ↦ q.hom x) hid
    have hy := congrArg (fun q : kernel f ⟶ kernel f ↦ q.hom y) hid
    change x = 0 at hx
    change y = 0 at hy
    exact hx.trans hy.symm
  infer_instance

end

end Towers.CField.LClass
