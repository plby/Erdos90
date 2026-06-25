import Submission.ClassField.LocalClass.OpenUnitTransfer
import Submission.ClassField.HerbrandQuotients.HerbrandIsogeny
import Submission.ClassField.HerbrandQuotients.PermutationHerbrand
import Submission.ClassField.HasseNorm.ClassH1

/-!
# The finite-local Herbrand calculation in Proposition VII.2.7

This file gives the arbitrary-universe form of Lemma III.2.5 needed for
number-field completions.  The proof is the source proof: a sufficiently
small normal-basis lattice exponentiates to an open acyclic subgroup of the
local units; finite-index isogeny invariance gives `h(U_L)=1`; and the
valuation sequence then gives `h(L×)=[L:K]`.
-/

namespace Submission.CField.ICohomo

open CategoryTheory CategoryTheory.Limits MonoidalCategory Rep Representation
open Submission.CField.Shifting
open Submission.CField.LClass
open Submission.CField.LBrauer
open Submission.CField.HQuotie
open Submission.CField.HNorm
open scoped TensorProduct

noncomputable section

universe u

/-- Forget the coefficient ring of a representation while retaining the
same carrier and group action as an integral representation. -/
noncomputable def intRestriction
    (A G : Type u) [CommRing A] [Group G] (V : Rep A G) : Rep ℤ G :=
  Rep.of {
    toFun := fun g ↦ (V.ρ g).toAddMonoidHom.toIntLinearMap
    map_one' := by ext; simp
    map_mul' := by intro g h; ext x; simp [Module.End.mul_apply] }

@[simp]
theorem int_restriction_rho
    (A G : Type u) [CommRing A] [Group G] (V : Rep A G)
    (g : G) (x : V) :
    (intRestriction A G V).ρ g x = V.ρ g x :=
  rfl

/-- Integral restriction preserves equivariant isomorphisms. -/
noncomputable def intRestrictionIso
    (A G : Type u) [CommRing A] [Group G] {V W : Rep A G}
    (e : V ≅ W) :
    intRestriction A G V ≅
      intRestriction A G W := by
  let eA := Representation.equivOfIso e
  apply Rep.mkIso
  apply Representation.Equiv.mk eA.toAddEquiv.toIntLinearEquiv
  intro g
  apply LinearMap.ext
  intro x
  exact LinearMap.congr_fun (eA.toIntertwiningMap.2 g) x

/-- After resizing integral scalars to `ULift ℤ`, the underlying additive
regular representation is coinduced from the trivial subgroup. -/
noncomputable def regularIsoCoind
    (A G : Type u) [CommRing A] [Group G] [Finite G] :
    uliftIntegralRepresentation
        (intRestriction A G (Rep.leftRegular A G)) ≅
      Rep.coind (⊥ : Subgroup G).subtype
        (Rep.trivial (ULift.{u} ℤ) (⊥ : Subgroup G) A) := by
  classical
  let V := uliftIntegralRepresentation
    (intRestriction A G (Rep.leftRegular A G))
  let C := Rep.coind (⊥ : Subgroup G).subtype
    (Rep.trivial (ULift.{u} ℤ) (⊥ : Subgroup G) A)
  let f : V →ₗ[ULift.{u} ℤ] C :=
    { toFun := fun x ↦
        let x' : G →₀ A := x
        ⟨fun g ↦ x' g⁻¹, by
        intro h g
        have hh : h = (1 : (⊥ : Subgroup G)) :=
          Subtype.ext (Subgroup.mem_bot.mp h.2)
        subst hh
        simp⟩
      map_add' := fun _ _ ↦ by ext; rfl
      map_smul' := fun r x ↦ by
        apply Subtype.ext
        funext g
        let x' : G →₀ A := x
        change r.down • x' g⁻¹ = r.down • x' g⁻¹
        rfl }
  have hf : Function.Bijective f := by
    constructor
    · intro x y hxy
      change G →₀ A at x y
      apply Finsupp.ext
      intro g
      have h := congrArg (fun q : C ↦ q.1 g⁻¹) hxy
      change x ((g⁻¹)⁻¹) = y ((g⁻¹)⁻¹) at h
      simpa using h
    · intro q
      let x : G →₀ A := Finsupp.equivFunOnFinite.symm fun g ↦ q.1 g⁻¹
      refine ⟨x, Subtype.ext ?_⟩
      funext g
      simp [f, x, V, C]
  apply Rep.mkIso
  apply Representation.Equiv.mk (LinearEquiv.ofBijective f hf)
  intro g
  apply LinearMap.ext
  intro x
  change G →₀ A at x
  apply Subtype.ext
  funext h
  change ((Rep.leftRegular A G).ρ g x) h⁻¹ = x (h * g)⁻¹
  rw [Representation.ofMulAction_apply]
  simp

/-- Positive cohomology of the universe-resized underlying integral regular
representation vanishes. -/
theorem ulift_restriction_regular
    (A G : Type u) [CommRing A] [Group G] [Finite G]
    (r : ℕ) (hr : 0 < r) :
    IsZero (groupCohomology
      (uliftIntegralRepresentation
        (intRestriction A G (Rep.leftRegular A G))) r) := by
  let C := Rep.trivial (ULift.{u} ℤ) (⊥ : Subgroup G) A
  have hC :=
    Submission.CField.COps.zero_cohomology_coinduced
      C r hr
  exact hC.of_iso ((groupCohomology.functor (ULift.{u} ℤ) G r).mapIso
    (regularIsoCoind A G))

/-- The exponential equivalence identifies the underlying integral normal
basis lattice with the chosen stable subgroup of units. -/
noncomputable def intIsoStable
    (A K L : Type u) [CommRing A] [IsDomain A]
    [Field K] [Field L] [Algebra A K] [IsFractionRing A K]
    [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    [FiniteDimensional K L] [IsGalois K L]
    (d : A) (hd : d ≠ 0) (U : Subgroup Lˣ)
    (hstable : ∀ (g : Gal(L/K)) (x : Lˣ), x ∈ U → g • x ∈ U)
    (e : (integralBasisRepresentation A K L d hd : Type u) ≃+
      Additive U)
    (hequiv : ∀ (g : Gal(L/K)) (x : U),
      e ((integralBasisRepresentation A K L d hd).ρ g
          (e.symm (Additive.ofMul x))) =
        Additive.ofMul
          (⟨g • (x : Lˣ), hstable g (x : Lˣ) x.2⟩ : U)) :
    intRestriction A Gal(L/K)
        (integralBasisRepresentation A K L d hd) ≅
      stableUnitRepresentation K L U hstable := by
  letI := stableDistribAction K L U hstable
  apply Rep.mkIso
  apply Representation.Equiv.mk e.toIntLinearEquiv
  intro g
  apply LinearMap.ext
  intro x
  let ux : U := (e x).toMul
  have h := hequiv g ux
  simpa [ux] using h

/-- A stable unit subgroup obtained from the normal-basis exponential has
Herbrand quotient one in the arbitrary-universe low-Tate formulation. -/
theorem stable_herbrand_value
    (A K L : Type u) [CommRing A] [IsDomain A]
    [Field K] [Field L] [Algebra A K] [IsFractionRing A K]
    [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    [FiniteDimensional K L] [IsGalois K L]
    [Finite Gal(L/K)] [IsCyclic Gal(L/K)]
    (d : A) (hd : d ≠ 0) (U : Subgroup Lˣ)
    (hstable : ∀ (g : Gal(L/K)) (x : Lˣ), x ∈ U → g • x ∈ U)
    (e : (integralBasisRepresentation A K L d hd : Type u) ≃+
      Additive U)
    (hequiv : ∀ (g : Gal(L/K)) (x : U),
      e ((integralBasisRepresentation A K L d hd).ρ g
          (e.symm (Additive.ofMul x))) =
        Additive.ofMul
          (⟨g • (x : Lˣ), hstable g (x : Lˣ) x.2⟩ : U)) :
    letI : Fintype Gal(L/K) := Fintype.ofFinite Gal(L/K)
    letI : CommGroup Gal(L/K) := IsCyclic.commGroup
    HerbrandQuotientValue
      (stableUnitRepresentation K L U hstable) 1 := by
  let G := Gal(L/K)
  letI : Fintype G := Fintype.ofFinite G
  letI : CommGroup G := IsCyclic.commGroup
  let R := intRestriction A G
    (integralBasisRepresentation A K L d hd)
  let V := stableUnitRepresentation K L U hstable
  let eReg := intRestrictionIso A G
    (representationIsoRegular A K L d hd)
  let eExp := intIsoStable
    A K L d hd U hstable e hequiv
  let eUV : uliftIntegralRepresentation
      (intRestriction A G (Rep.leftRegular A G)) ≅
        uliftIntegralRepresentation V :=
    uliftIntegralIso (eReg.trans eExp)
  have h1 : IsZero (groupCohomology (uliftIntegralRepresentation V) 1) :=
    (ulift_restriction_regular A G 1 (by omega)).of_iso
      ((groupCohomology.functor (ULift.{u} ℤ) G 1).mapIso eUV).symm
  have h2 : IsZero (groupCohomology (uliftIntegralRepresentation V) 2) :=
    (ulift_restriction_regular A G 2 (by omega)).of_iso
      ((groupCohomology.functor (ULift.{u} ℤ) G 2).mapIso eUV).symm
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := G)
  let eZero : tateZero V ≃+
      groupCohomology (uliftIntegralRepresentation V) 2 :=
    (tateIntLift V).trans
      (tateCohomologyTwo
        (uliftIntegralRepresentation V) g hg).toAddEquiv
  let eNeg : tateNegOne V ≃+
      groupCohomology (uliftIntegralRepresentation V) 1 :=
    (tateULift V).trans
      (tateCohomologyNeg
        (uliftIntegralRepresentation V) g hg).toAddEquiv
  letI : Subsingleton (groupCohomology (uliftIntegralRepresentation V) 1) :=
    ModuleCat.subsingleton_of_isZero h1
  letI : Subsingleton (groupCohomology (uliftIntegralRepresentation V) 2) :=
    ModuleCat.subsingleton_of_isZero h2
  letI : Subsingleton (tateZero V) :=
    ⟨fun x y ↦ eZero.injective (Subsingleton.elim _ _)⟩
  letI : Subsingleton (tateNegOne V) :=
    ⟨fun x y ↦ eNeg.injective (Subsingleton.elim _ _)⟩
  letI : Finite (tateZero V) := inferInstance
  letI : Finite (tateNegOne V) := inferInstance
  refine ⟨inferInstance, inferInstance, ?_⟩
  rw [Nat.card_unique, Nat.card_unique]
  norm_num

/-- The local-unit group has Herbrand quotient one, with no universe
restriction on the local fields. -/
theorem local_herbrand_value
    (F E : Type u)
    [NontriviallyNormedField F] [IsUltrametricDist F]
    [ValuativeRel F] [IsNonarchimedeanLocalField F] [CharZero F]
    [Field E] [Algebra F E] [Module.Finite F E] [IsGalois F E]
    [IsCyclic Gal(E/F)] :
    letI : Fintype Gal(E/F) := Fintype.ofFinite Gal(E/F)
    letI : CommGroup Gal(E/F) := IsCyclic.commGroup
    HerbrandQuotientValue (localUnitRepresentation F E) 1 := by
  letI : Algebra.IsAlgebraic F E := Algebra.IsAlgebraic.of_finite F E
  letI : NontriviallyNormedField E :=
    FLExt.nontriviallyNormedField F E
  letI : NormedAlgebra F E := spectralNorm.normedAlgebra F E
  letI : IsUltrametricDist E := IsUltrametricDist.of_normedAlgebra F
  letI : CharZero E :=
    charZero_of_injective_algebraMap (algebraMap F E).injective
  letI : ValuativeRel E := FLExt.valuativeRel F E
  letI : Valuation.Compatible (NormedField.valuation (K := E)) :=
    Valuation.Compatible.ofValuation (NormedField.valuation (K := E))
  letI : IsNonarchimedeanLocalField E :=
    FLExt.nonarchimedeanLocalField F E
  letI : Fintype Gal(E/F) := Fintype.ofFinite Gal(E/F)
  letI : CommGroup Gal(E/F) := IsCyclic.commGroup
  let A : Subring F := @Valued.integer F _ NNReal _ NormedField.toValued
  obtain ⟨d, hd, hsource, hopen, hnear, hstable, e, hequiv, _⟩ :=
    galois_stable_acyclic F E
  let W := integralNormalSpan A F E d hd
  let U := localExpSubgroup E W.toAddSubgroup hsource
  have hopen' : extensionUnitOpen F E U := by
    change IsOpen (U : Set Eˣ)
    exact hopen
  have hnear' : extensionNearOne F E U := by
    change Units.val '' (U : Set Eˣ) ⊆ Metric.ball 1 1
    exact hnear
  let f := stableUnitInclusion F E U hstable hnear'
  have hsmall : HerbrandQuotientValue
      (stableUnitRepresentation F E U hstable) 1 :=
    stable_herbrand_value
      A F E d hd U hstable e hequiv
  exact (herbrandIsogenyBridge Gal(E/F)
    (stableUnitRepresentation F E U hstable)
    (localUnitRepresentation F E) f
    (stable_unit_inclusion F E U hstable hnear')
    (cokernel_stable_inclusion
      F E U hstable hnear' hopen') 1).mp hsmall

/-- The lifted integral line used in the arbitrary-universe valuation
sequence. -/
private abbrev liftedInt : Type u := ULift.{u} ℤ

/-- Normalized order, with its target lifted into the carrier universe. -/
noncomputable def localRepHom
    (F E : Type u)
    [NontriviallyNormedField F] [IsUltrametricDist F]
    [ValuativeRel F] [IsNonarchimedeanLocalField F]
    [Field E] [Algebra F E] [Module.Finite F E] [IsGalois F E] :
    Rep.ofAlgebraAutOnUnits F E ⟶
      Rep.trivial ℤ Gal(E/F) liftedInt := by
  letI : Algebra.IsAlgebraic F E := Algebra.IsAlgebraic.of_finite F E
  letI : NontriviallyNormedField E :=
    FLExt.nontriviallyNormedField F E
  letI : NormedAlgebra F E := spectralNorm.normedAlgebra F E
  letI : IsUltrametricDist E := IsUltrametricDist.of_normedAlgebra F
  letI : ValuativeRel E := FLExt.valuativeRel F E
  letI : Valuation.Compatible (NormedField.valuation (K := E)) :=
    Valuation.Compatible.ofValuation (NormedField.valuation (K := E))
  letI : IsNonarchimedeanLocalField E :=
    FLExt.nonarchimedeanLocalField F E
  apply Rep.ofHom
  refine {
    toLinearMap :=
      { toFun := fun x ↦ ULift.up (localUnitOrder E x)
        map_add' := fun x y ↦ by
          exact ULift.down_injective (map_add (localUnitOrder E) x y)
        map_smul' := fun n x ↦ by
          exact ULift.down_injective
            ((localUnitOrder E).toIntLinearMap.map_smul n x) }
    isIntertwining' := fun g ↦ by
      ext x
      change localUnitOrder E
          (Additive.ofMul (Units.map g.toMonoidHom x.toMul)) =
        localUnitOrder E x
      exact FLExt.unit_order_aut F E g x.toMul }

/-- Inclusion of local units into all nonzero elements, in arbitrary
universe. -/
noncomputable def inclusionRepHom
    (F E : Type u)
    [NontriviallyNormedField F] [IsUltrametricDist F]
    [ValuativeRel F] [IsNonarchimedeanLocalField F]
    [Field E] [Algebra F E] [Module.Finite F E] [IsGalois F E] :
    localUnitRepresentation F E ⟶ Rep.ofAlgebraAutOnUnits F E := by
  letI := localDistribAction F E
  apply Rep.ofHom
  let i : Additive (extensionUnitSubgroup F E) →+
      Additive Eˣ :=
    { toFun := fun x ↦ Additive.ofMul (x.toMul : Eˣ)
      map_zero' := rfl
      map_add' := fun _ _ ↦ rfl }
  refine ⟨i.toIntLinearMap, ?_⟩
  intro g
  apply LinearMap.ext
  intro x
  rfl

/-- The arbitrary-universe valuation sequence
`1 → U_E → E× → ULift ℤ → 0`. -/
noncomputable def localShortComplex
    (F E : Type u)
    [NontriviallyNormedField F] [IsUltrametricDist F]
    [ValuativeRel F] [IsNonarchimedeanLocalField F]
    [Field E] [Algebra F E] [Module.Finite F E] [IsGalois F E] :
    ShortComplex (Rep ℤ Gal(E/F)) :=
  ShortComplex.mk
    (inclusionRepHom F E)
    (localRepHom F E) (by
      letI : Algebra.IsAlgebraic F E := Algebra.IsAlgebraic.of_finite F E
      letI : NontriviallyNormedField E :=
        FLExt.nontriviallyNormedField F E
      letI : NormedAlgebra F E := spectralNorm.normedAlgebra F E
      letI : IsUltrametricDist E := IsUltrametricDist.of_normedAlgebra F
      letI : ValuativeRel E := FLExt.valuativeRel F E
      letI : Valuation.Compatible (NormedField.valuation (K := E)) :=
        Valuation.Compatible.ofValuation (NormedField.valuation (K := E))
      letI : IsNonarchimedeanLocalField E :=
        FLExt.nonarchimedeanLocalField F E
      apply Rep.hom_ext
      ext x
      change Additive (extensionUnitSubgroup F E) at x
      change localUnitOrder E
        (Additive.ofMul (x.toMul : Eˣ)) = 0
      exact (local_order_zero E _).mp
        x.toMul.2)

/-- The lifted valuation sequence is short exact. -/
theorem local_short_exact
    (F E : Type u)
    [NontriviallyNormedField F] [IsUltrametricDist F]
    [ValuativeRel F] [IsNonarchimedeanLocalField F]
    [Field E] [Algebra F E] [Module.Finite F E] [IsGalois F E] :
    (localShortComplex F E).ShortExact := by
  letI : Algebra.IsAlgebraic F E := Algebra.IsAlgebraic.of_finite F E
  letI : NontriviallyNormedField E :=
    FLExt.nontriviallyNormedField F E
  letI : NormedAlgebra F E := spectralNorm.normedAlgebra F E
  letI : IsUltrametricDist E := IsUltrametricDist.of_normedAlgebra F
  letI : ValuativeRel E := FLExt.valuativeRel F E
  letI : Valuation.Compatible (NormedField.valuation (K := E)) :=
    Valuation.Compatible.ofValuation (NormedField.valuation (K := E))
  letI : IsNonarchimedeanLocalField E :=
    FLExt.nonarchimedeanLocalField F E
  let X := localShortComplex F E
  letI intRepModule (A : Rep.{u, 0, u} ℤ Gal(E/F)) : Module ℤ A := A.hV2
  let Fgt : Rep.{u, 0, u} ℤ Gal(E/F) ⥤ ModuleCat.{u} ℤ :=
    forget₂ (Rep.{u, 0, u} ℤ Gal(E/F)) (ModuleCat.{u} ℤ)
  apply ShortComplex.ShortExact.mk'
  · exact Fgt.reflects_exact_of_faithful _ <|
      (ShortComplex.moduleCat_exact_iff (X.map Fgt)).2
        (fun (x : Additive Eˣ) hx ↦ by
          change ULift.up (localUnitOrder E x) = 0 at hx
          have hxdown : localUnitOrder E x = 0 := by
            simpa using congrArg ULift.down hx
          refine ⟨Additive.ofMul ⟨x.toMul,
            (local_order_zero E _).mpr
              hxdown⟩, rfl⟩)
  · rw [Rep.mono_iff_injective]
    intro x y hxy
    exact Additive.toMul.injective
      (Subtype.ext (congrArg Additive.toMul hxy))
  · rw [Rep.epi_iff_surjective]
    intro z
    obtain ⟨x, hx⟩ := local_order_surjective E z.down
    exact ⟨x, ULift.down_injective hx⟩

/-- The lifted trivial integral line is the singleton permutation lattice. -/
noncomputable def liftedTrivialIso
    (G : Type u) [Group G] :
    Rep.trivial ℤ G liftedInt ≅
      orbitFunctionRepresentation G (ULift.{u, 0} PUnit.{1}) :=
  Rep.mkIso (Representation.Equiv.mk
    { toFun := fun z _ ↦ z.down
      invFun := fun f ↦ ULift.up
        (f (ULift.up PUnit.unit : ULift.{u, 0} PUnit.{1}))
      left_inv := fun _ ↦ by apply ULift.down_injective; rfl
      right_inv := fun f ↦ by funext x; cases x; rfl
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
    (fun g ↦ by ext z x; cases x; rfl))

/-- The lifted trivial integral line has Herbrand quotient `|G|`. -/
theorem lifted_trivial_herbrand
    (G : Type u) [CommGroup G] [Fintype G] :
    HerbrandQuotientValue.{u, u}
      (Rep.trivial ℤ G liftedInt) (Fintype.card G : ℚ) := by
  apply (herbrand_value_iso
    (liftedTrivialIso G)
    (Fintype.card G : ℚ)).mpr
  simpa using
    (function_herbrand_value G
      (ULift.{u, 0} PUnit.{1})
      (ULift.up PUnit.unit : ULift.{u, 0} PUnit.{1}))

/-- Arbitrary-universe form of `h(E×)=[E:F]` for a cyclic local extension. -/
theorem units_herbrand_value
    (F E : Type u)
    [NontriviallyNormedField F] [IsUltrametricDist F]
    [ValuativeRel F] [IsNonarchimedeanLocalField F] [CharZero F]
    [Field E] [Algebra F E] [Module.Finite F E] [IsGalois F E]
    [IsCyclic Gal(E/F)] :
    letI : Fintype Gal(E/F) := Fintype.ofFinite Gal(E/F)
    letI : CommGroup Gal(E/F) := IsCyclic.commGroup
    HerbrandQuotientValue (Rep.ofAlgebraAutOnUnits F E)
      (Module.finrank F E : ℚ) := by
  letI : Fintype Gal(E/F) := Fintype.ofFinite Gal(E/F)
  letI : CommGroup Gal(E/F) := IsCyclic.commGroup
  let U := localUnitRepresentation F E
  let M := Rep.ofAlgebraAutOnUnits F E
  let Z := Rep.trivial ℤ Gal(E/F) liftedInt
  let X := localShortComplex F E
  have hX : X.ShortExact :=
    local_short_exact F E
  have hU : HerbrandQuotientValue U 1 :=
    local_herbrand_value F E
  have hZ : HerbrandQuotientValue Z (Fintype.card Gal(E/F) : ℚ) :=
    lifted_trivial_herbrand Gal(E/F)
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Gal(E/F))
  letI : Finite (tateZero U) := hU.1
  letI : Finite (tateNegOne U) := hU.2.1
  letI : Finite (tateZero Z) := hZ.1
  letI : Finite (tateNegOne Z) := hZ.2.1
  letI : Finite (tateZero X.X₁) := by
    simpa [X, U] using hU.1
  letI : Finite (tateNegOne X.X₁) := by
    simpa [X, U] using hU.2.1
  letI : Finite (tateZero X.X₃) := by
    simpa [X, Z] using hZ.1
  letI : Finite (tateNegOne X.X₃) := by
    simpa [X, Z] using hZ.2.1
  obtain ⟨hMzero, hMneg⟩ := tate_finite_middle hX g hg
  letI : Finite (tateZero M) := hMzero
  letI : Finite (tateNegOne M) := hMneg
  have hmul := tate_card_ratio hX g hg
  have hcard : Fintype.card Gal(E/F) = Module.finrank F E := by
    rw [← Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank]
  refine ⟨inferInstance, inferInstance, ?_⟩
  calc
    (Nat.card (tateZero M) : ℚ) /
        Nat.card (tateNegOne M) =
      ((Nat.card (tateZero U) : ℚ) /
          Nat.card (tateNegOne U)) *
        ((Nat.card (tateZero Z) : ℚ) /
          Nat.card (tateNegOne Z)) := hmul
    _ = 1 * (Fintype.card Gal(E/F) : ℚ) := by
      rw [hU.2.2, hZ.2.2]
    _ = (Module.finrank F E : ℚ) := by rw [one_mul, hcard]

end

end Submission.CField.ICohomo
