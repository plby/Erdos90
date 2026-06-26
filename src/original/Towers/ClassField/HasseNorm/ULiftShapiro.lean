import Towers.ClassField.HasseNorm.GlobalComparison
import Towers.ClassField.IdeleCohomology.CompletionInducedModule
import Towers.NumberTheory.Locals.ArbitraryPlaceClassification

/-!
# Universe-resized completion-product Shapiro equivalence

This file rescales the Chapter VII completion-product representations from
`ℤ` to `ULift ℤ`.  The underlying additive groups and Galois actions are
unchanged.  It then applies the existing coinduction and Shapiro APIs in the
common universe required by ordinary group cohomology.
-/

namespace Towers.CField.HNorm

open CategoryTheory Representation
open IsDedekindDomain NumberField
open Towers.NumberTheory.Milne
open Towers.CField.ICohomo
open groupCohomology

noncomputable section

universe u

/-- Recover the additive action of an integral representation without
retaining its particular `ℤ`-module instance. -/
@[implicit_reducible]
private def additiveActionRepresentation
    {G : Type u} [Group G] (A : Rep.{u, 0, u} ℤ G) :
    DistribMulAction G A := by
  letI : Module ℤ A := A.hV2
  exact
    { smul := fun g x => A.ρ g x
      one_smul := fun x => by
        change A.ρ 1 x = x
        rw [map_one]
        rfl
      mul_smul := fun g h x => by
        change A.ρ (g * h) x = A.ρ g (A.ρ h x)
        rw [map_mul]
        rfl
      smul_zero := fun g => (A.ρ g).map_zero
      smul_add := fun g => (A.ρ g).map_add }

/-- An additive action made linear over the universe lift of `ℤ`. -/
private def uliftLinearRepresentation
    {G M : Type u} [Group G] [AddCommGroup M]
    [DistribMulAction G M] : Representation (ULift.{u} ℤ) G M where
  toFun g :=
    { toFun := fun x => g • x
      map_add' := smul_add g
      map_smul' := fun r x =>
        (Representation.ofDistribMulAction ℤ G M g).map_smul r.down x }
  map_one' := by
    ext x
    exact one_smul _ _
  map_mul' g h := by
    ext x
    exact mul_smul _ _ _

/-- Rescale an integral representation to `ULift ℤ`, preserving its
carrier and group action definitionally. -/
noncomputable def uliftIntegralRepresentation
    {G : Type u} [Group G] (A : Rep.{u, 0, u} ℤ G) :
    Rep (ULift.{u} ℤ) G := by
  letI : DistribMulAction G A := additiveActionRepresentation A
  exact Rep.of (uliftLinearRepresentation (G := G) (M := A))

/-- Rescaling is functorial on morphisms of integral representations. -/
noncomputable def uliftIntegralHom
    {G : Type u} [Group G] {A B : Rep.{u, 0, u} ℤ G}
    (f : A ⟶ B) :
    uliftIntegralRepresentation A ⟶ uliftIntegralRepresentation B := by
  let fAdd : A →+ B :=
    by
      letI : Module ℤ A := A.hV2
      letI : Module ℤ B := B.hV2
      exact
        { toFun := fun x => f.hom.toLinearMap.toFun x
          map_zero' := f.hom.toLinearMap.map_zero
          map_add' := f.hom.toLinearMap.map_add }
  exact Rep.ofHom
    { toLinearMap :=
        { toFun := fAdd
          map_add' := fAdd.map_add
          map_smul' := fun r x => by
            exact map_zsmul fAdd r.down x }
      isIntertwining' := fun g => by
        ext x
        change fAdd (A.ρ g x) = B.ρ g (fAdd x)
        dsimp only [fAdd]
        exact Rep.hom_comm_apply f g x }

/-- Rescaling preserves representation isomorphisms. -/
noncomputable def uliftIntegralIso
    {G : Type u} [Group G] {A B : Rep.{u, 0, u} ℤ G}
    (e : A ≅ B) :
    uliftIntegralRepresentation A ≅ uliftIntegralRepresentation B where
  hom := uliftIntegralHom e.hom
  inv := uliftIntegralHom e.inv
  hom_inv_id := by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro x
    change e.inv.hom (e.hom.hom x) = x
    exact Rep.inv_hom_apply (e := e) (x := x)
  inv_hom_id := by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro x
    change e.hom.hom (e.inv.hom x) = x
    exact Rep.hom_inv_apply (e := e) (x := x)

variable {K L : Type u} [Field K] [Field L] [Algebra K L]

/-- The `ULift ℤ` representation on the units of the product of all
completions above one absolute value. -/
noncomputable def uliftUnitsRepresentation
    (v : AbsoluteValue K ℝ) : Rep (ULift.{u} ℤ) Gal(L/K) :=
  uliftIntegralRepresentation
    (completionUnitsRepresentation (K := K) (L := L) v)

/-- The `ULift ℤ` representation on the units of one chosen completion,
with its place-stabilizer action. -/
noncomputable def uliftPlaceRepresentation
    (v : AbsoluteValue K ℝ)
    (w : CompletionPlacesAbove (L := L) v) :
    Rep (ULift.{u} ℤ) (CompletionPlaceStabilizer v w) :=
  uliftIntegralRepresentation
    (placeUnitsRepresentation (K := K) (L := L) v w)

/-- The completion product remains coinduced from one chosen completion
after rescaling the coefficient ring. -/
noncomputable def uliftInducedIso
    (v : AbsoluteValue K ℝ)
    (w : CompletionPlacesAbove (L := L) v)
    [MulAction.IsPretransitive Gal(L/K)
      (CompletionPlacesAbove (L := L) v)] :
    uliftUnitsRepresentation v ≅
      milneInducedModule (CompletionPlaceStabilizer v w)
        (uliftPlaceRepresentation v w) := by
  exact uliftIntegralIso
    (completionInducedIso (K := K) (L := L) v w)

/-- Universe-resized Proposition VII.2.3 for one completion product. -/
noncomputable def uliftShapiroIso
    (v : AbsoluteValue K ℝ)
    (w : CompletionPlacesAbove (L := L) v)
    [MulAction.IsPretransitive Gal(L/K)
      (CompletionPlacesAbove (L := L) v)]
    (r : ℕ) :
    groupCohomology
        (uliftUnitsRepresentation (K := K) (L := L) v) r ≅
      groupCohomology
        (uliftPlaceRepresentation (K := K) (L := L) v w) r :=
  (groupCohomology.functor (ULift.{u} ℤ) Gal(L/K) r).mapIso
      (uliftInducedIso (K := K) (L := L) v w) ≪≫
    shapiro
      (CompletionPlaceStabilizer (K := K) (L := L) v w)
      (uliftPlaceRepresentation (K := K) (L := L) v w) r

/-- The degree-two form used by the Hasse norm comparison. -/
noncomputable def uliftCompletionUnits
    (v : AbsoluteValue K ℝ)
    (w : CompletionPlacesAbove (L := L) v)
    [MulAction.IsPretransitive Gal(L/K)
      (CompletionPlacesAbove (L := L) v)] :
    H2 (uliftUnitsRepresentation (K := K) (L := L) v) ≃+
      H2 (uliftPlaceRepresentation (K := K) (L := L) v w) :=
  (uliftShapiroIso
    (K := K) (L := L) v w 2).toLinearEquiv.toAddEquiv

section FinitePlace

variable [NumberField K] [NumberField L]
  [FiniteDimensional K L] [IsGalois K L]

/-- At a finite number-field place, Galois transitivity supplies the
resized degree-two Shapiro equivalence without an additional hypothesis. -/
noncomputable def uliftUnitsH
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (w : CompletionPlacesAbove (L := L) (FinitePlace.mk P).val) :
    H2 (uliftUnitsRepresentation
        (K := K) (L := L) (FinitePlace.mk P).val) ≃+
      H2 (uliftPlaceRepresentation
        (K := K) (L := L) (FinitePlace.mk P).val w) := by
  letI : MulAction.IsPretransitive Gal(L/K)
      (CompletionPlacesAbove (L := L) (FinitePlace.mk P).val) :=
    completion_above_pretransitive P
  exact uliftCompletionUnits
    (K := K) (L := L) (FinitePlace.mk P).val w

end FinitePlace

section InfinitePlace

variable [NumberField K] [NumberField L]
  [FiniteDimensional K L] [IsGalois K L]

omit [FiniteDimensional K L] in
/-- Galois conjugation is transitive on the normalized absolute-value
extensions of an infinite place. -/
theorem places_above_pretransitive
    (v : InfinitePlace K) :
    MulAction.IsPretransitive Gal(L/K)
      (CompletionPlacesAbove (L := L) v.1) := by
  letI : Fact v.1.IsNontrivial := ⟨infinite_place_nontrivial v⟩
  constructor
  intro z w
  have extensionNontrivial
      (q : CompletionPlacesAbove (L := L) v.1) : q.1.IsNontrivial := by
    obtain ⟨x, hx0, hx1⟩ := infinite_place_nontrivial v
    have hxMap : algebraMap K L x ≠ 0 := by
      simpa using (algebraMap K L).injective.ne hx0
    refine ⟨algebraMap K L x, hxMap, ?_⟩
    have heq := DFunLike.congr_fun q.2.comp_eq x
    change q.1 (algebraMap K L x) = v.1 x at heq
    exact fun h => hx1 (heq.symm.trans h)
  have hzNontrivial : z.1.IsNontrivial :=
    extensionNontrivial z
  have hwNontrivial : w.1.IsNontrivial :=
    extensionNontrivial w
  have hzArch : ¬ IsNonarchimedean z.1 := by
    intro hz
    apply infinite_place_nonarchimedean v
    intro x y
    calc
      v.1 (x + y) = z.1 (algebraMap K L (x + y)) :=
        (DFunLike.congr_fun z.2.comp_eq (x + y)).symm
      _ = z.1 (algebraMap K L x + algebraMap K L y) := by rw [map_add]
      _ ≤ max (z.1 (algebraMap K L x)) (z.1 (algebraMap K L y)) :=
        hz _ _
      _ = max (v.1 x) (v.1 y) := by
        have hx := DFunLike.congr_fun z.2.comp_eq x
        have hy := DFunLike.congr_fun z.2.comp_eq y
        change z.1 (algebraMap K L x) = v.1 x at hx
        change z.1 (algebraMap K L y) = v.1 y at hy
        rw [hx, hy]
  have hwArch : ¬ IsNonarchimedean w.1 := by
    intro hw
    apply infinite_place_nonarchimedean v
    intro x y
    calc
      v.1 (x + y) = w.1 (algebraMap K L (x + y)) :=
        (DFunLike.congr_fun w.2.comp_eq (x + y)).symm
      _ = w.1 (algebraMap K L x + algebraMap K L y) := by rw [map_add]
      _ ≤ max (w.1 (algebraMap K L x)) (w.1 (algebraMap K L y)) :=
        hw _ _
      _ = max (v.1 x) (v.1 y) := by
        have hx := DFunLike.congr_fun w.2.comp_eq x
        have hy := DFunLike.congr_fun w.2.comp_eq y
        change w.1 (algebraMap K L x) = v.1 x at hx
        change w.1 (algebraMap K L y) = v.1 y at hy
        rw [hx, hy]
  obtain ⟨zInf, hzEquiv⟩ :=
    infinite_not_nonarchimedean
      z.1 hzNontrivial hzArch
  obtain ⟨wInf, hwEquiv⟩ :=
    infinite_not_nonarchimedean
      w.1 hwNontrivial hwArch
  have hzComap : zInf.comap (algebraMap K L) = v := by
    apply (InfinitePlace.eq_iff_isEquiv (K := K)).2
    intro x y
    change zInf.1 (algebraMap K L x) ≤ zInf.1 (algebraMap K L y) ↔
      v.1 x ≤ v.1 y
    calc
      zInf.1 (algebraMap K L x) ≤ zInf.1 (algebraMap K L y) ↔
          z.1 (algebraMap K L x) ≤ z.1 (algebraMap K L y) :=
        (hzEquiv _ _).symm
      _ ↔ v.1 x ≤ v.1 y := by
        have hx := DFunLike.congr_fun z.2.comp_eq x
        have hy := DFunLike.congr_fun z.2.comp_eq y
        change z.1 (algebraMap K L x) = v.1 x at hx
        change z.1 (algebraMap K L y) = v.1 y at hy
        rw [hx, hy]
  have hwComap : wInf.comap (algebraMap K L) = v := by
    apply (InfinitePlace.eq_iff_isEquiv (K := K)).2
    intro x y
    change wInf.1 (algebraMap K L x) ≤ wInf.1 (algebraMap K L y) ↔
      v.1 x ≤ v.1 y
    calc
      wInf.1 (algebraMap K L x) ≤ wInf.1 (algebraMap K L y) ↔
          w.1 (algebraMap K L x) ≤ w.1 (algebraMap K L y) :=
        (hwEquiv _ _).symm
      _ ↔ v.1 x ≤ v.1 y := by
        have hx := DFunLike.congr_fun w.2.comp_eq x
        have hy := DFunLike.congr_fun w.2.comp_eq y
        change w.1 (algebraMap K L x) = v.1 x at hx
        change w.1 (algebraMap K L y) = v.1 y at hy
        rw [hx, hy]
  obtain ⟨sigma, hsigma⟩ :=
    InfinitePlace.exists_smul_eq_of_comap_eq (hzComap.trans hwComap.symm)
  refine ⟨sigma, Subtype.ext ?_⟩
  have hconj : (sigma • z.1).IsEquiv (sigma • zInf).1 := by
    intro x y
    exact hzEquiv (sigma.symm x) (sigma.symm y)
  have hplace : (sigma • zInf).1 = wInf.1 :=
    congrArg (fun q : InfinitePlace L => q.1) hsigma
  rw [hplace] at hconj
  have hequiv : (sigma • z.1).IsEquiv w.1 :=
    hconj.trans hwEquiv.symm
  obtain ⟨c, hc, hpow⟩ :=
    AbsoluteValue.isEquiv_iff_exists_rpow_eq.mp hequiv
  obtain ⟨x, hx0, hx1⟩ := infinite_place_nontrivial v
  have hvx : 0 < v.1 x := v.1.pos hx0
  have hzBase := DFunLike.congr_fun (sigma • z).2.comp_eq x
  have hwBase := DFunLike.congr_fun w.2.comp_eq x
  change (sigma • z.1) (algebraMap K L x) = v.1 x at hzBase
  change w.1 (algebraMap K L x) = v.1 x at hwBase
  have hbase : v.1 x ^ c = v.1 x ^ (1 : ℝ) := by
    rw [Real.rpow_one]
    calc
      v.1 x ^ c = (sigma • z.1) (algebraMap K L x) ^ c := by
        exact congrArg (fun r : ℝ => r ^ c) hzBase.symm
      _ = w.1 (algebraMap K L x) := congrFun hpow _
      _ = v.1 x := hwBase
  have hc1 : c = 1 :=
    (Real.rpow_right_inj hvx hx1).mp hbase
  apply AbsoluteValue.ext
  intro y
  have hy := congrFun hpow y
  simpa [hc1] using hy

/-- At an infinite number-field place, transitivity likewise supplies the
resized degree-two Shapiro equivalence without an additional hypothesis. -/
noncomputable def uliftInfiniteUnits
    (v : InfinitePlace K)
    (w : CompletionPlacesAbove (L := L) v.1) :
    H2 (uliftUnitsRepresentation
        (K := K) (L := L) v.1) ≃+
      H2 (uliftPlaceRepresentation
        (K := K) (L := L) v.1 w) := by
  letI : MulAction.IsPretransitive Gal(L/K)
      (CompletionPlacesAbove (L := L) v.1) :=
    places_above_pretransitive v
  exact uliftCompletionUnits
    (K := K) (L := L) v.1 w

end InfinitePlace

end

end Towers.CField.HNorm
