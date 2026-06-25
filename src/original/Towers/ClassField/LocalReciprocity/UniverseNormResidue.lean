import Mathlib.Algebra.Algebra.Shrink
import Towers.ClassField.LocalReciprocity.LocalUnitsRep
import Towers.ClassField.LocalReciprocity.UniversePolymorphicArtin

/-!
# The finite local norm-residue equivalence in an ambient universe

The categorical proof of Theorem III.3.1 is formulated in `Type 0` because
its coefficient category is `Rep ℤ`.  A finite extension of local fields used
by the number-field completion API is nevertheless `Small.{0}`.  This file
transports the Type-0 norm-residue equivalence through `Shrink` models,
including the norm subgroup and the Galois group.

The subsequent comparison with the ambient cup-defined Artin map is kept as
a separate theorem: it is the only part requiring compatibility of the local
cup invariant with simultaneous transport of the base and extension fields.
-/

namespace Towers.CField.LRecip

open Towers.CField.LFTheory
open scoped IsMulCommutative

noncomputable section

universe u v

/-- Conjugating both the base and extension fields transports a Galois
automorphism. -/
def transportGal
    {F₁ E₁ F₂ E₂ : Type*}
    [Field F₁] [Field E₁] [Field F₂] [Field E₂]
    [Algebra F₁ E₁] [Algebra F₂ E₂]
    (f : F₁ ≃+* F₂) (g : E₁ ≃+* E₂)
    (h : (algebraMap F₂ E₂).comp f.toRingHom =
      g.toRingHom.comp (algebraMap F₁ E₁))
    (sigma : Gal(E₁/F₁)) : Gal(E₂/F₂) := by
  let c : E₂ ≃+* E₂ := g.symm.trans (sigma.toRingEquiv.trans g)
  exact AlgEquiv.ofRingEquiv (f := c) fun x => by
    change g (sigma (g.symm (algebraMap F₂ E₂ x))) =
      algebraMap F₂ E₂ x
    have hsquare := DFunLike.congr_fun h (f.symm x)
    have hpreimage : g.symm (algebraMap F₂ E₂ x) =
        algebraMap F₁ E₁ (f.symm x) := by
      apply g.injective
      rw [g.apply_symm_apply]
      simpa using hsquare
    rw [hpreimage, sigma.commutes]
    simpa using hsquare.symm

/-- The Galois groups of two extensions identified by a commutative square
of field equivalences are multiplicatively equivalent. -/
def galMulEquiv
    {F₁ E₁ F₂ E₂ : Type*}
    [Field F₁] [Field E₁] [Field F₂] [Field E₂]
    [Algebra F₁ E₁] [Algebra F₂ E₂]
    (f : F₁ ≃+* F₂) (g : E₁ ≃+* E₂)
    (h : (algebraMap F₂ E₂).comp f.toRingHom =
      g.toRingHom.comp (algebraMap F₁ E₁)) :
    Gal(E₁/F₁) ≃* Gal(E₂/F₂) where
  toFun := transportGal f g h
  invFun := transportGal f.symm g.symm (by
    apply RingHom.ext
    intro x
    apply g.injective
    simpa using (DFunLike.congr_fun h (f.symm x)).symm)
  left_inv sigma := by
    ext x
    change g.symm (g (sigma (g.symm (g x)))) = sigma x
    simp
  right_inv sigma := by
    ext x
    change g (g.symm (sigma (g (g.symm x)))) = sigma x
    simp
  map_mul' sigma tau := by
    ext x
    change g ((sigma * tau) (g.symm x)) =
      g (sigma (g.symm (g (tau (g.symm x)))))
    simp

/-- Transport a quotient along a multiplicative equivalence when the source
subgroup is the comap of the target subgroup. -/
noncomputable def quotientMulComap
    {A : Type u} {B : Type v} [CommGroup A] [CommGroup B]
    (e : A ≃* B) (H : Subgroup B) (K : Subgroup A)
    (hcomap : H.comap e.toMonoidHom = K) :
    A ⧸ K ≃* B ⧸ H := by
  have hforward : K ≤ H.comap e.toMonoidHom := by
    rw [hcomap]
  have hbackward : H ≤ K.comap e.symm.toMonoidHom := by
    intro x hx
    change e.symm x ∈ K
    rw [← hcomap]
    change e (e.symm x) ∈ H
    simpa using hx
  exact
    { toFun := QuotientGroup.map K H e.toMonoidHom hforward
      invFun := QuotientGroup.map H K e.symm.toMonoidHom hbackward
      left_inv := by
        intro q
        obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective K q
        apply congrArg (QuotientGroup.mk' K)
        exact e.symm_apply_apply x
      right_inv := by
        intro q
        obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective H q
        apply congrArg (QuotientGroup.mk' H)
        exact e.apply_symm_apply x
      map_mul' := by
        intro x y
        exact map_mul _ x y }

@[simp]
theorem quotient_comap_mk
    {A : Type u} {B : Type v} [CommGroup A] [CommGroup B]
    (e : A ≃* B) (H : Subgroup B) (K : Subgroup A)
    (hcomap : H.comap e.toMonoidHom = K) (x : A) :
    quotientMulComap e H K hcomap
        (QuotientGroup.mk' K x) =
      QuotientGroup.mk' H (e x) := by
  rfl

set_option maxHeartbeats 5000000 in
-- The two Shrink field models, their norm subgroups, and their Galois groups
-- elaborate simultaneously.
set_option synthInstance.maxHeartbeats 1000000 in
/-- The finite abelian local norm-residue equivalence transported from its
Type-0 categorical construction to any `Small.{0}` ambient local fields. -/
noncomputable def abelianArtinSmall
    (F E : Type u)
    [Small.{0} F] [Small.{0} E]
    [NontriviallyNormedField F] [CharZero F] [IsUltrametricDist F]
    [ValuativeRel F]
    [Valuation.Compatible (NormedField.valuation (K := F))]
    [IsNonarchimedeanLocalField F]
    [Field E] [Algebra F E] [FiniteDimensional F E]
    [IsGalois F E] [IsMulCommutative Gal(E/F)] :
    (Fˣ ⧸ normSubgroup F E) ≃* Gal(E/F) := by
  let eF : (Shrink.{0} F) ≃+* F := Shrink.ringEquiv F
  let eE : (Shrink.{0} E) ≃+* E := Shrink.ringEquiv E
  letI : NormedField (Shrink.{0} F) :=
    NormedField.induced (Shrink.{0} F) F eF.toRingHom eF.injective
  letI : NontriviallyNormedField (Shrink.{0} F) :=
    { (inferInstance : NormedField (Shrink.{0} F)) with
      non_trivial := by
        obtain ⟨y, hy⟩ := NontriviallyNormedField.non_trivial (α := F)
        refine ⟨eF.symm y, ?_⟩
        change 1 < ‖eF (eF.symm y)‖
        simpa using hy }
  letI : CharZero (Shrink.{0} F) := eF.toRingHom.charZero
  letI : IsUltrametricDist (Shrink.{0} F) := by
    constructor
    intro a b c
    change dist (eF a) (eF c) ≤
      max (dist (eF a) (eF b)) (dist (eF b) (eF c))
    exact dist_triangle_max (eF a) (eF b) (eF c)
  letI : Algebra (Shrink.{0} F) F := eF.toRingHom.toAlgebra
  let eFAlg : (Shrink.{0} F) ≃ₐ[(Shrink.{0} F)] F :=
    AlgEquiv.ofRingEquiv (f := eF) (fun _ => rfl)
  letI : Module.Finite (Shrink.{0} F) F :=
    Module.Finite.equiv eFAlg.toLinearEquiv
  letI : Algebra (Shrink.{0} F) E :=
    ((algebraMap F E).comp eF.toRingHom).toAlgebra
  letI : IsScalarTower (Shrink.{0} F) F E :=
    IsScalarTower.of_algebraMap_eq' rfl
  letI : Module.Finite (Shrink.{0} F) E := Module.Finite.trans F E
  letI : Algebra (Shrink.{0} F) (Shrink.{0} E) := inferInstance
  let eEAlg : (Shrink.{0} E) ≃ₐ[(Shrink.{0} F)] E := Shrink.algEquiv (Shrink.{0} F) E
  letI : Module.Finite (Shrink.{0} F) (Shrink.{0} E) :=
    Module.Finite.equiv eEAlg.toLinearEquiv.symm
  letI : ValuativeRel (Shrink.{0} F) :=
    ValuativeRel.ofValuation (NormedField.valuation (K := (Shrink.{0} F)))
  letI : Valuation.Compatible (NormedField.valuation (K := (Shrink.{0} F))) :=
    Valuation.Compatible.ofValuation (NormedField.valuation (K := (Shrink.{0} F)))
  haveI htop : IsValuativeTopology (Shrink.{0} F) := by
    apply IsValuativeTopology.of_zero
    intro s
    rw [show s ∈ nhds (0 : (Shrink.{0} F)) ↔
        ∃ gamma : (MonoidWithZeroHom.ValueGroup₀
            (NormedField.valuation (K := (Shrink.{0} F))))ˣ,
          {y | (NormedField.valuation (K := (Shrink.{0} F))).restrict y < gamma.1} ⊆ s from
      (NormedField.toValued
        (K := (Shrink.{0} F))).is_topological_valuation s]
    simpa using
      (NormedField.valuation
        (K := Shrink.{0} F)).exists_setOf_restrict_le_iff 0 s
  haveI hcompact : LocallyCompactSpace (Shrink.{0} F) :=
    (Shrink.homeomorph F).symm.isOpenEmbedding.locallyCompactSpace
  haveI hvaluationNontrivial :
      (NormedField.valuation (K := (Shrink.{0} F))).IsNontrivial := by
    constructor
    obtain ⟨y, hy⟩ :=
      NontriviallyNormedField.non_trivial (α := (Shrink.{0} F))
    refine ⟨y, ?_, ?_⟩
    · have hy0 : y ≠ 0 := by
        intro h
        subst y
        have hnorm_zero : ‖(0 : (Shrink.{0} F))‖ = 0 := norm_zero
        rw [hnorm_zero] at hy
        exact (not_lt_of_ge zero_le_one) hy
      intro h
      apply hy0
      change ‖y‖₊ = 0 at h
      exact nnnorm_eq_zero.mp h
    · intro h
      change ‖y‖₊ = 1 at h
      have hnorm : ‖y‖ = 1 := by
        have hc := congrArg (fun r : NNReal => (r : ℝ)) h
        change (↑‖y‖₊ : ℝ) = (↑(1 : NNReal) : ℝ)
        exact hc
      exact (ne_of_gt hy) hnorm
  haveI hnontrivial : ValuativeRel.IsNontrivial (Shrink.{0} F) :=
    (ValuativeRel.isNontrivial_iff_isNontrivial
      (NormedField.valuation (K := (Shrink.{0} F)))).mpr inferInstance
  haveI hlocal : IsNonarchimedeanLocalField (Shrink.{0} F) :=
    { toIsValuativeTopology := htop
      toLocallyCompactSpace := hcompact
      toIsNontrivial := hnontrivial }
  have hsquare : (algebraMap (Shrink.{0} F) (Shrink.{0} E)).comp eF.symm.toRingHom =
      eE.symm.toRingHom.comp (algebraMap F E) := by
    apply RingHom.ext
    intro y
    change algebraMap (Shrink.{0} F) (Shrink.{0} E) (eF.symm y) =
      eE.symm (algebraMap F E y)
    calc
      _ = eE.symm (eE (algebraMap (Shrink.{0} F) (Shrink.{0} E) (eF.symm y))) :=
        (eE.symm_apply_apply _).symm
      _ = eE.symm (algebraMap F E y) := by
        congr 1
        calc
          eE (algebraMap (Shrink.{0} F) (Shrink.{0} E) (eF.symm y)) =
              algebraMap (Shrink.{0} F) E (eF.symm y) := eEAlg.commutes _
          _ = algebraMap F E y := by
            change algebraMap F E (eF (eF.symm y)) = _
            rw [eF.apply_symm_apply]
  letI : IsGalois (Shrink.{0} F) (Shrink.{0} E) := IsGalois.of_equiv_equiv
    (F := F) (E := E) (M := (Shrink.{0} F)) (N := (Shrink.{0} E))
    (f := eF.symm) (g := eE.symm) hsquare
  let galEquiv : Gal((Shrink.{0} E)/(Shrink.{0} F)) ≃* Gal(E/F) :=
    galMulEquiv eF eE (by
      apply RingHom.ext
      intro y
      change algebraMap F E (eF y) = eE (algebraMap (Shrink.{0} F) (Shrink.{0} E) y)
      exact (eEAlg.commutes y).symm)
  letI : IsMulCommutative Gal((Shrink.{0} E)/(Shrink.{0} F)) := by
    refine ⟨⟨fun sigma tau => galEquiv.injective ?_⟩⟩
    simpa only [map_mul] using mul_comm (galEquiv sigma) (galEquiv tau)
  have he : (algebraMap F E).comp eF.toRingHom =
      eE.toRingHom.comp (algebraMap (Shrink.{0} F) (Shrink.{0} E)) := by
    apply RingHom.ext
    intro y
    change algebraMap F E (eF y) = eE (algebraMap (Shrink.{0} F) (Shrink.{0} E) y)
    exact (eEAlg.commutes y).symm
  let eUnits : Fˣ ≃* (Shrink.{0} F)ˣ :=
    Units.mapEquiv eF.symm.toMulEquiv
  have hnorm :
      (normSubgroup (Shrink.{0} F) (Shrink.{0} E)).comap eUnits.toMonoidHom =
        normSubgroup F E := by
    ext y
    constructor
    · rintro ⟨z, hz⟩
      refine ⟨Units.map eE.toRingHom z, ?_⟩
      apply Units.ext
      change Algebra.norm F (eE (z : (Shrink.{0} E))) = (y : F)
      have hn := Algebra.norm_eq_of_equiv_equiv eF eE he (z : (Shrink.{0} E))
      change Algebra.norm (Shrink.{0} F) (z : (Shrink.{0} E)) =
        eF.symm (Algebra.norm F (eE (z : (Shrink.{0} E)))) at hn
      have hz' := congrArg Units.val hz
      change Algebra.norm (Shrink.{0} F) (z : (Shrink.{0} E)) = eF.symm (y : F) at hz'
      apply eF.symm.injective
      rw [← hn, ← hz']
    · rintro ⟨z, hz⟩
      refine ⟨Units.map eE.symm.toRingHom z, ?_⟩
      apply Units.ext
      change Algebra.norm (Shrink.{0} F) (eE.symm (z : E)) = eF.symm (y : F)
      have hn := Algebra.norm_eq_of_equiv_equiv eF eE he
        (eE.symm (z : E))
      rw [eE.apply_symm_apply] at hn
      have hz' := congrArg Units.val hz
      change Algebra.norm F (z : E) = (y : F) at hz'
      rw [hn, hz']
  let eQuot : (Fˣ ⧸ normSubgroup F E) ≃*
      ((Shrink.{0} F)ˣ ⧸ normSubgroup (Shrink.{0} F) (Shrink.{0} E)) :=
    quotientMulComap eUnits
      (normSubgroup (Shrink.{0} F) (Shrink.{0} E)) (normSubgroup F E) hnorm
  let artin := @abelianLocalArtin
    (Shrink.{0} F) (Shrink.{0} E)
    inferInstance inferInstance hlocal inferInstance inferInstance
    inferInstance inferInstance inferInstance
  exact eQuot.trans
    (artin.trans galEquiv)

/-- The homomorphism on base units induced by the transported ambient
norm-residue equivalence. -/
noncomputable def abelianLocalSmall
    (F E : Type u)
    [Small.{0} F] [Small.{0} E]
    [NontriviallyNormedField F] [CharZero F] [IsUltrametricDist F]
    [ValuativeRel F]
    [Valuation.Compatible (NormedField.valuation (K := F))]
    [IsNonarchimedeanLocalField F]
    [Field E] [Algebra F E] [FiniteDimensional F E]
    [IsGalois F E] [IsMulCommutative Gal(E/F)] :
    Fˣ →* Gal(E/F) :=
  (abelianArtinSmall F E).toMonoidHom.comp
    (QuotientGroup.mk' (normSubgroup F E))

/-- The transported ambient norm-residue homomorphism is surjective. -/
theorem abelian_small_surjective
    (F E : Type u)
    [Small.{0} F] [Small.{0} E]
    [NontriviallyNormedField F] [CharZero F] [IsUltrametricDist F]
    [ValuativeRel F]
    [Valuation.Compatible (NormedField.valuation (K := F))]
    [IsNonarchimedeanLocalField F]
    [Field E] [Algebra F E] [FiniteDimensional F E]
    [IsGalois F E] [IsMulCommutative Gal(E/F)] :
    Function.Surjective (abelianLocalSmall F E) := by
  intro sigma
  obtain ⟨q, rfl⟩ :=
    (abelianArtinSmall F E).surjective sigma
  obtain ⟨x, rfl⟩ :=
    QuotientGroup.mk'_surjective (normSubgroup F E) q
  exact ⟨x, rfl⟩

/-- The kernel of the transported ambient norm-residue homomorphism is the
local norm subgroup. -/
theorem abelian_small_ker
    (F E : Type u)
    [Small.{0} F] [Small.{0} E]
    [NontriviallyNormedField F] [CharZero F] [IsUltrametricDist F]
    [ValuativeRel F]
    [Valuation.Compatible (NormedField.valuation (K := F))]
    [IsNonarchimedeanLocalField F]
    [Field E] [Algebra F E] [FiniteDimensional F E]
    [IsGalois F E] [IsMulCommutative Gal(E/F)] :
    (abelianLocalSmall F E).ker = normSubgroup F E := by
  ext x
  simp only [MonoidHom.mem_ker]
  constructor
  · intro hx
    have hq : QuotientGroup.mk' (normSubgroup F E) x = 1 :=
      (abelianArtinSmall F E).injective (by
        simpa [abelianLocalSmall] using hx)
    exact (QuotientGroup.eq_one_iff x).mp hq
  · intro hx
    change (abelianArtinSmall F E)
      (QuotientGroup.mk' (normSubgroup F E) x) = 1
    have hq : QuotientGroup.mk' (normSubgroup F E) x = 1 :=
      (QuotientGroup.eq_one_iff _).mpr hx
    rw [hq, map_one]

/-- The one remaining compatibility statement for the `Shrink` transport:
the transported Type-0 norm-residue map has the same character formula as
the ambient cup-defined map. -/
def SmallCupFormula
    (F E : Type u)
    [Small.{0} F] [Small.{0} E]
    [NontriviallyNormedField F] [CharZero F] [IsUltrametricDist F]
    [ValuativeRel F]
    [Valuation.Compatible (NormedField.valuation (K := F))]
    [IsNonarchimedeanLocalField F]
    [Field E] [Algebra F E] [FiniteDimensional F E]
    [IsGalois F E] [IsMulCommutative Gal(E/F)] : Prop :=
  ∀ (a : Fˣ) (chi : CharacterModule (Additive Gal(E/F))),
    chi (Additive.ofMul (abelianLocalSmall F E a)) =
      characterCupUniverse F E a chi

/-- Character separation reduces equality of the transported norm-residue
map and the ambient cup-defined map to the mixed-base cup formula above. -/
theorem small_universe_formula
    (F E : Type u)
    [Small.{0} F] [Small.{0} E]
    [NontriviallyNormedField F] [CharZero F] [IsUltrametricDist F]
    [ValuativeRel F]
    [Valuation.Compatible (NormedField.valuation (K := F))]
    [IsNonarchimedeanLocalField F]
    [Field E] [Algebra F E] [FiniteDimensional F E]
    [IsGalois F E] [IsMulCommutative Gal(E/F)]
    (hcup : SmallCupFormula F E) :
    abelianLocalSmall F E =
      abelianArtinUniverse F E := by
  apply MonoidHom.ext
  intro a
  apply forall_rational_character
  intro chi
  rw [hcup a chi, abelian_universe_character F E a chi]

end


end Towers.CField.LRecip
