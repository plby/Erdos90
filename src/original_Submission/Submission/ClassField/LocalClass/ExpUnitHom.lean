import Submission.ClassField.LocalClass.SmallLattice
import Submission.ClassField.LocalClass.EquivariantExponentialTransfer
import Submission.ClassField.LocalBrauer.FiniteExtensionNorm
import Mathlib.Topology.Algebra.IsOpenUnits

/-!
# Milne, Class Field Theory, Lemma III.2.4

In characteristic zero, the local exponential identifies a sufficiently
small additive normal-basis lattice with an open Galois-stable subgroup of
the local units.  This file constructs that subgroup and transfers the
positive-degree cohomology vanishing from the lattice.
-/

namespace Submission.CField.LClass

open CategoryTheory
open Submission.NumberTheory.Milne
open Submission.CField.LBrauer
open scoped NormedField Valued Topology

noncomputable section

attribute [local instance] NormedField.toValued
attribute [local instance] Units.mulDistribMulActionRight

universe u

/-- Exponential on an additive subgroup contained in the canonical local
source, valued in the unit group. -/
noncomputable def localExpHom
    (E : Type*) [NontriviallyNormedField E] [IsUltrametricDist E]
    [LocallyCompactSpace E] [CompleteSpace E] [CharZero E]
    (W : AddSubgroup E)
    (hW : (W : Set E) ⊆ (localExpHomeomorph E).source) :
    W →+ Additive Eˣ where
  toFun x := Additive.ofMul
    (NormedSpace.isUnit_exp_of_mem_ball
      (exp_homeomorph_ball E (hW x.2))).unit
  map_zero' := by
    apply Additive.toMul.injective
    apply Units.ext
    change NormedSpace.exp (0 : E) = 1
    simp
  map_add' x y := by
    apply Additive.toMul.injective
    apply Units.ext
    change NormedSpace.exp ((x : E) + (y : E)) =
      NormedSpace.exp (x : E) * NormedSpace.exp (y : E)
    exact local_exp_add E (hW x.2) (hW y.2)

@[simp]
theorem exp_unit_val
    (E : Type*) [NontriviallyNormedField E] [IsUltrametricDist E]
    [LocallyCompactSpace E] [CompleteSpace E] [CharZero E]
    (W : AddSubgroup E)
    (hW : (W : Set E) ⊆ (localExpHomeomorph E).source)
    (x : W) :
    (((localExpHom E W hW x).toMul : Eˣ) : E) = NormedSpace.exp (x : E) :=
  IsUnit.unit_spec _

/-- Exponential is injective on every subgroup contained in its canonical
local source. -/
theorem local_exp_injective
    (E : Type*) [NontriviallyNormedField E] [IsUltrametricDist E]
    [LocallyCompactSpace E] [CompleteSpace E] [CharZero E]
    (W : AddSubgroup E)
    (hW : (W : Set E) ⊆ (localExpHomeomorph E).source) :
    Function.Injective (localExpHom E W hW) := by
  intro x y hxy
  apply Subtype.ext
  apply exp_injective_source E (hW x.2) (hW y.2)
  simpa only [← exp_unit_val E W hW] using
    congrArg (fun u : Additive Eˣ ↦ ((u.toMul : Eˣ) : E)) hxy

/-- The two inherited additive-group structures on a submodule and on its
underlying additive subgroup are canonically equivalent. -/
def submoduleAddSubgroup
    {A M : Type*} [Ring A] [AddCommGroup M] [Module A M]
    (W : Submodule A M) : W ≃+ W.toAddSubgroup where
  toFun x := ⟨x, x.2⟩
  invFun x := ⟨x, x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

/-- The multiplicative subgroup obtained by exponentiating `W`. -/
noncomputable def localExpSubgroup
    (E : Type*) [NontriviallyNormedField E] [IsUltrametricDist E]
    [LocallyCompactSpace E] [CompleteSpace E] [CharZero E]
    (W : AddSubgroup E)
    (hW : (W : Set E) ⊆ (localExpHomeomorph E).source) :
    Subgroup Eˣ :=
  (localExpHom E W hW).range.toSubgroup

/-- Exponential is an additive equivalence from `W` onto its multiplicative
image (written additively). -/
noncomputable def localExpUnit
    (E : Type*) [NontriviallyNormedField E] [IsUltrametricDist E]
    [LocallyCompactSpace E] [CompleteSpace E] [CharZero E]
    (W : AddSubgroup E)
    (hW : (W : Set E) ⊆ (localExpHomeomorph E).source) :
    W ≃+ Additive (localExpSubgroup E W hW) := by
  let f := localExpHom E W hW
  let er : W ≃+ f.range := AddEquiv.ofBijective f.rangeRestrict
    ⟨fun _ _ h ↦ local_exp_injective E W hW
      (congrArg Subtype.val h), f.rangeRestrict_surjective⟩
  exact er.trans (AddEquiv.refl _)

@[simp]
theorem local_exp_val
    (E : Type*) [NontriviallyNormedField E] [IsUltrametricDist E]
    [LocallyCompactSpace E] [CompleteSpace E] [CharZero E]
    (W : AddSubgroup E)
    (hW : (W : Set E) ⊆ (localExpHomeomorph E).source)
    (x : W) :
    (((((localExpUnit E W hW x).toMul :
      localExpSubgroup E W hW) : Eˣ) : E)) =
      NormedSpace.exp (x : E) := by
  exact exp_unit_val E W hW x

/-- The exponential image of an open subgroup contained in the local source
is open in the unit group. -/
theorem open_exp_subgroup
    (E : Type*) [NontriviallyNormedField E] [IsUltrametricDist E]
    [LocallyCompactSpace E] [CompleteSpace E] [CharZero E]
    (W : AddSubgroup E)
    (hW : (W : Set E) ⊆ (localExpHomeomorph E).source)
    (hopen : IsOpen (W : Set E)) :
    IsOpen (localExpSubgroup E W hW : Set Eˣ) := by
  rw [IsOpenUnits.isOpenEmbedding_unitsVal.isOpen_iff_image_isOpen]
  have himage : Units.val '' (localExpSubgroup E W hW : Set Eˣ) =
      NormedSpace.exp '' (W : Set E) := by
    ext y
    constructor
    · rintro ⟨u, hu, rfl⟩
      let uu : localExpSubgroup E W hW := ⟨u, hu⟩
      let x : W := (localExpUnit E W hW).symm (Additive.ofMul uu)
      refine ⟨x, x.2, ?_⟩
      simpa [x, uu] using (local_exp_val E W hW x).symm
    · rintro ⟨x, hx, rfl⟩
      let xx : W := ⟨x, hx⟩
      let uu : localExpSubgroup E W hW :=
        (localExpUnit E W hW xx).toMul
      refine ⟨(uu : Eˣ), uu.2, ?_⟩
      simp [xx, uu]
  rw [himage]
  exact (localExpHomeomorph E).isOpen_image_of_subset_source
    hopen hW

/-- Transport a representation across an equivalence of its underlying
additive groups.  The target module structure is transported along the same
equivalence. -/
noncomputable def transportRepAlong
    (A G Y : Type*) [CommRing A] [Group G] [AddCommGroup Y]
    (V : Rep A G) (e : V ≃+ Y) :
    letI : Module A Y := e.symm.module A
    Rep A G := by
  letI : Module A Y := e.symm.module A
  let eLin : V ≃ₗ[A] Y := (e.symm.linearEquiv A).symm
  let rho : Representation A G Y := {
    toFun := fun g ↦ eLin.toLinearMap.comp
      ((V.ρ g).comp eLin.symm.toLinearMap)
    map_one' := by
      apply LinearMap.ext
      intro y
      simp
    map_mul' := by
      intro g h
      apply LinearMap.ext
      intro y
      simp [map_mul, Module.End.mul_apply] }
  exact Rep.of rho

/-- The source representation is isomorphic to its transport. -/
noncomputable def transportAlongIso
    (A G Y : Type*) [CommRing A] [Group G] [AddCommGroup Y]
    (V : Rep A G) (e : V ≃+ Y) :
    letI : Module A Y := e.symm.module A
    V ≅ transportRepAlong A G Y V e := by
  letI : Module A Y := e.symm.module A
  let eLin : V ≃ₗ[A] Y := (e.symm.linearEquiv A).symm
  apply Rep.mkIso
  apply Representation.Equiv.mk eLin
  intro g
  apply LinearMap.ext
  intro x
  simp [eLin]

set_option maxHeartbeats 800000 in
-- The proof assembles the canonical spectral topology, normal-basis lattice,
-- local inverse function theorem, and transported Galois representation.
/-- **Lemma III.2.4 (characteristic-zero case).**  A finite Galois extension
of nonarchimedean local fields in characteristic zero has an open
Galois-stable subgroup of local units whose cohomology vanishes in every
positive degree.  The subgroup lies in the open unit ball about `1`, so it is
a subgroup of principal local units. -/
theorem galois_stable_acyclic
    (K L : Type u)
    [NontriviallyNormedField K] [IsUltrametricDist K]
    [ValuativeRel K] [IsNonarchimedeanLocalField K] [CharZero K]
    [Field L] [Algebra K L] [Module.Finite K L] [IsGalois K L] :
    letI : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.of_finite K L
    letI : NontriviallyNormedField L :=
      FLExt.nontriviallyNormedField K L
    letI : NormedAlgebra K L := spectralNorm.normedAlgebra K L
    letI : IsUltrametricDist L := IsUltrametricDist.of_normedAlgebra K
    letI : CharZero L :=
      charZero_of_injective_algebraMap (algebraMap K L).injective
    letI : ValuativeRel L := FLExt.valuativeRel K L
    letI : IsNonarchimedeanLocalField L :=
      FLExt.nonarchimedeanLocalField K L
    let A := Valued.integer K
    ∃ (d : A) (hd : d ≠ 0),
      let W := integralNormalSpan A K L d hd
      ∃ (hsource : (W : Set L) ⊆
          (localExpHomeomorph L).source),
        let U' := localExpSubgroup L W.toAddSubgroup hsource
        IsOpen (U' : Set Lˣ) ∧
        Units.val '' (U' : Set Lˣ) ⊆ Metric.ball 1 1 ∧
        ∃ hstableU : (∀ (g : Gal(L/K)) (u : Lˣ), u ∈ U' → g • u ∈ U'),
        ∃ expEquiv : (integralBasisRepresentation A K L d hd : Type u) ≃+
            Additive U',
          letI : Module A (Additive U') := expEquiv.symm.module A
          let V := transportRepAlong A Gal(L/K) (Additive U')
            (integralBasisRepresentation A K L d hd) expEquiv
          (∀ (g : Gal(L/K)) (u : U'),
            expEquiv ((integralBasisRepresentation A K L d hd).ρ g
              (expEquiv.symm (Additive.ofMul u))) =
              Additive.ofMul
                (⟨g • (u : Lˣ), hstableU g (u : Lˣ) u.2⟩ : U')) ∧
          ∀ r : ℕ, 0 < r → Limits.IsZero (groupCohomology V r) := by
  letI : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.of_finite K L
  letI : NontriviallyNormedField L :=
    FLExt.nontriviallyNormedField K L
  letI : NormedAlgebra K L := spectralNorm.normedAlgebra K L
  letI : IsUltrametricDist L := IsUltrametricDist.of_normedAlgebra K
  letI : CharZero L :=
    charZero_of_injective_algebraMap (algebraMap K L).injective
  letI : ValuativeRel L := FLExt.valuativeRel K L
  letI : IsNonarchimedeanLocalField L :=
    FLExt.nonarchimedeanLocalField K L
  let A := Valued.integer K
  let eL := localExpHomeomorph L
  let N : Set L := eL.source ∩ NormedSpace.exp ⁻¹' Metric.ball 1 1
  have hNopen : IsOpen N := by
    exact eL.isOpen_inter_preimage Metric.isOpen_ball
  have h0N : (0 : L) ∈ N := by
    refine ⟨exp_partial_homeomorph L, ?_⟩
    simp [Metric.mem_ball]
  obtain ⟨d, hd, hopenW, hWN, hstable, _hreg, hzero⟩ :=
    stable_acyclic_subset K L N
      (hNopen.mem_nhds h0N)
  let W := integralNormalSpan A K L d hd
  have hsource : (W : Set L) ⊆ eL.source := fun x hx ↦ (hWN hx).1
  let U' := localExpSubgroup L W.toAddSubgroup hsource
  have hopenU : IsOpen (U' : Set Lˣ) :=
    open_exp_subgroup L W.toAddSubgroup hsource hopenW
  have hnear : Units.val '' (U' : Set Lˣ) ⊆ Metric.ball 1 1 := by
    rintro y ⟨u, hu, rfl⟩
    let uu : U' := ⟨u, hu⟩
    let x : W :=
      (localExpUnit L W.toAddSubgroup hsource).symm
        (Additive.ofMul uu)
    have hxN : (x : L) ∈ N := hWN x.2
    have hval := local_exp_val L W.toAddSubgroup hsource x
    have hux : (u : L) = NormedSpace.exp (x : L) := by
      simpa [x, uu] using hval
    simpa only [hux] using hxN.2
  have hstableU : ∀ (g : Gal(L/K)) (u : Lˣ), u ∈ U' → g • u ∈ U' := by
    intro g u hu
    change Additive.ofMul (g • u) ∈
      (localExpHom L W.toAddSubgroup hsource).range
    change Additive.ofMul u ∈
      (localExpHom L W.toAddSubgroup hsource).range at hu
    obtain ⟨x, hx⟩ := hu
    let gx : W := ⟨g • (x : L), hstable g x.2⟩
    refine ⟨gx, ?_⟩
    apply Additive.toMul.injective
    apply Units.ext
    rw [exp_unit_val]
    change NormedSpace.exp (g (x : L)) = g ((u : Lˣ) : L)
    have hxu : NormedSpace.exp (x : L) = ((u : Lˣ) : L) := by
      simpa only [exp_unit_val] using
        congrArg (fun z : Additive Lˣ ↦ ((z.toMul : Lˣ) : L)) hx
    rw [← hxu]
    have hgiso : Isometry (g : L → L) := by
      apply Isometry.of_dist_eq
      intro a b
      rw [dist_eq_norm, dist_eq_norm, ← map_sub]
      exact spectralNorm_eq_of_equiv g (a - b) |>.symm
    exact (NormedSpace.map_exp_of_mem_ball g hgiso.continuous (x : L)
      (exp_homeomorph_ball L
        (hsource x.2))).symm
  let expEquiv0 := localExpUnit L W.toAddSubgroup hsource
  let expEquiv : (integralBasisRepresentation A K L d hd : Type u) ≃+
      Additive U' := by
    change W ≃+ Additive U'
    exact (submoduleAddSubgroup W).trans expEquiv0
  refine ⟨d, hd, hsource, hopenU, hnear, hstableU, expEquiv, ?_, ?_⟩
  · intro g u
    letI : Module A (Additive U') := expEquiv.symm.module A
    let x : W := expEquiv.symm (Additive.ofMul u)
    apply Additive.toMul.injective
    change (expEquiv
      ((integralBasisRepresentation A K L d hd).ρ g
        (expEquiv.symm (Additive.ofMul u)))).toMul =
      (⟨g • (u : Lˣ), hstableU g (u : Lˣ) u.2⟩ : U')
    apply Subtype.ext
    apply Units.ext
    change NormedSpace.exp (g (x : L)) = g ((u : Lˣ) : L)
    have hxu : NormedSpace.exp (x : L) = ((u : Lˣ) : L) := by
      have hexp : (((((expEquiv x).toMul : U') : Lˣ) : L)) =
          NormedSpace.exp (x : L) := by
        change (((((expEquiv0 (⟨x, x.2⟩ : W.toAddSubgroup)).toMul : U') :
          Lˣ) : L)) = NormedSpace.exp (x : L)
        exact local_exp_val L W.toAddSubgroup hsource
          (⟨x, x.2⟩ : W.toAddSubgroup)
      calc
        NormedSpace.exp (x : L) =
            (((((expEquiv x).toMul : U') : Lˣ) : L)) :=
          hexp.symm
        _ = ((u : Lˣ) : L) := by
          have heq : expEquiv x = Additive.ofMul u := by
            dsimp [x]
            exact expEquiv.apply_symm_apply (Additive.ofMul u)
          exact congrArg
            (fun z : Additive U' ↦ ((((z.toMul : U') : Lˣ) : L))) heq
    rw [← hxu]
    have hgiso : Isometry (g : L → L) := by
      apply Isometry.of_dist_eq
      intro a b
      rw [dist_eq_norm, dist_eq_norm, ← map_sub]
      exact spectralNorm_eq_of_equiv g (a - b) |>.symm
    exact (NormedSpace.map_exp_of_mem_ball g hgiso.continuous (x : L)
      (exp_homeomorph_ball L
        (hsource x.2))).symm
  · intro r hr
    letI : Module A (Additive U') := expEquiv.symm.module A
    exact cohomology_equivariant_exp
      (integralBasisRepresentation A K L d hd)
      (transportRepAlong A Gal(L/K) (Additive U')
        (integralBasisRepresentation A K L d hd) expEquiv)
      (transportAlongIso A Gal(L/K) (Additive U')
        (integralBasisRepresentation A K L d hd) expEquiv)
      r (hzero r hr)

/-- Canonical-norm wrapper for Lemma III.2.4.  Here the valuative relation on
the base field is fixed internally to the one induced by its norm, so it is
not an exposed hypothesis of the source-facing statement. -/
theorem open_stable_acyclic
    (K L : Type u)
    [NontriviallyNormedField K] [IsUltrametricDist K] [CharZero K]
    (hK : letI : ValuativeRel K :=
      ValuativeRel.ofValuation (NormedField.valuation (K := K))
      IsNonarchimedeanLocalField K)
    [Field L] [Algebra K L] [Module.Finite K L] [IsGalois K L] :
    letI : ValuativeRel K :=
      ValuativeRel.ofValuation (NormedField.valuation (K := K))
    letI : IsNonarchimedeanLocalField K := hK
    letI : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.of_finite K L
    letI : NontriviallyNormedField L :=
      FLExt.nontriviallyNormedField K L
    letI : NormedAlgebra K L := spectralNorm.normedAlgebra K L
    letI : IsUltrametricDist L := IsUltrametricDist.of_normedAlgebra K
    letI : CharZero L :=
      charZero_of_injective_algebraMap (algebraMap K L).injective
    letI : ValuativeRel L := FLExt.valuativeRel K L
    letI : IsNonarchimedeanLocalField L :=
      FLExt.nonarchimedeanLocalField K L
    let A := Valued.integer K
    ∃ (d : A) (hd : d ≠ 0),
      let W := integralNormalSpan A K L d hd
      ∃ (hsource : (W : Set L) ⊆
          (localExpHomeomorph L).source),
        let U' := localExpSubgroup L W.toAddSubgroup hsource
        IsOpen (U' : Set Lˣ) ∧
        Units.val '' (U' : Set Lˣ) ⊆ Metric.ball 1 1 ∧
        ∃ hstableU : (∀ (g : Gal(L/K)) (u : Lˣ), u ∈ U' → g • u ∈ U'),
        ∃ expEquiv : (integralBasisRepresentation A K L d hd : Type u) ≃+
            Additive U',
          letI : Module A (Additive U') := expEquiv.symm.module A
          let V := transportRepAlong A Gal(L/K) (Additive U')
            (integralBasisRepresentation A K L d hd) expEquiv
          (∀ (g : Gal(L/K)) (u : U'),
            expEquiv ((integralBasisRepresentation A K L d hd).ρ g
              (expEquiv.symm (Additive.ofMul u))) =
              Additive.ofMul
                (⟨g • (u : Lˣ), hstableU g (u : Lˣ) u.2⟩ : U')) ∧
          ∀ r : ℕ, 0 < r → Limits.IsZero (groupCohomology V r) := by
  letI : ValuativeRel K :=
    ValuativeRel.ofValuation (NormedField.valuation (K := K))
  letI : IsNonarchimedeanLocalField K := hK
  exact galois_stable_acyclic K L

end

end Submission.CField.LClass
