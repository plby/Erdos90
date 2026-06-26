import Towers.ClassField.LocalReciprocity.MixedCupTransport
import Towers.ClassField.LocalReciprocity.AmbientCompatibility
import Towers.ClassField.LocalReciprocity.UniverseNormResidue

/-!
# Cup normalization for the ambient `Small` local Artin map

The transported Type-0 norm-residue equivalence is compared with the ambient
cup-defined Artin map by applying mixed-universe character-cup naturality to
the canonical `Shrink` models.
-/

namespace Towers.CField.LRecip

open Towers.CField.LFTheory
open scoped IsMulCommutative

noncomputable section

universe u

set_option maxHeartbeats 5000000 in
-- The proof reinstalls both Shrink local-field models and unfolds the transported quotient map.
set_option synthInstance.maxHeartbeats 500000 in
-- The Shrink models carry transported local-field and Galois instances.
/-- The transported `Small` norm-residue map has the ambient Proposition
III.3.6 character formula. -/
theorem smallCupFormula
    (F E : Type u)
    [Small.{0} F] [Small.{0} E]
    [NontriviallyNormedField F] [CharZero F] [IsUltrametricDist F]
    [ValuativeRel F]
    [Valuation.Compatible (NormedField.valuation (K := F))]
    [IsNonarchimedeanLocalField F]
    [Field E] [Algebra F E] [FiniteDimensional F E]
    [IsGalois F E] [IsMulCommutative Gal(E/F)] :
    SmallCupFormula F E := by
  unfold SmallCupFormula
  intro a chi
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
    intro x y z
    change dist (eF x) (eF z) ≤
      max (dist (eF x) (eF y)) (dist (eF y) (eF z))
    exact dist_triangle_max (eF x) (eF y) (eF z)
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
  let eEAlg : (Shrink.{0} E) ≃ₐ[(Shrink.{0} F)] E :=
    Shrink.algEquiv (Shrink.{0} F) E
  letI : Module.Finite (Shrink.{0} F) (Shrink.{0} E) :=
    Module.Finite.equiv eEAlg.toLinearEquiv.symm
  letI : ValuativeRel (Shrink.{0} F) :=
    ValuativeRel.ofValuation
      (NormedField.valuation (K := (Shrink.{0} F)))
  letI : Valuation.Compatible
      (NormedField.valuation (K := (Shrink.{0} F))) :=
    Valuation.Compatible.ofValuation
      (NormedField.valuation (K := (Shrink.{0} F)))
  haveI htop : IsValuativeTopology (Shrink.{0} F) := by
    apply IsValuativeTopology.of_zero
    intro s
    rw [show s ∈ nhds (0 : (Shrink.{0} F)) ↔
        ∃ gamma : (MonoidWithZeroHom.ValueGroup₀
            (NormedField.valuation (K := (Shrink.{0} F))))ˣ,
          {y | (NormedField.valuation
            (K := (Shrink.{0} F))).restrict y < gamma.1} ⊆ s from
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
        exact congrArg (fun r : NNReal => (r : ℝ)) h
      exact (ne_of_gt hy) hnorm
  haveI hnontrivial : ValuativeRel.IsNontrivial (Shrink.{0} F) :=
    (ValuativeRel.isNontrivial_iff_isNontrivial
      (NormedField.valuation (K := (Shrink.{0} F)))).mpr inferInstance
  haveI hlocal : IsNonarchimedeanLocalField (Shrink.{0} F) :=
    { toIsValuativeTopology := htop
      toLocallyCompactSpace := hcompact
      toIsNontrivial := hnontrivial }
  have hsquare :
      (algebraMap (Shrink.{0} F) (Shrink.{0} E)).comp eF.symm.toRingHom =
        eE.symm.toRingHom.comp (algebraMap F E) := by
    apply RingHom.ext
    intro y
    change algebraMap (Shrink.{0} F) (Shrink.{0} E) (eF.symm y) =
      eE.symm (algebraMap F E y)
    calc
      _ = eE.symm
          (eE (algebraMap (Shrink.{0} F) (Shrink.{0} E) (eF.symm y))) :=
        (eE.symm_apply_apply _).symm
      _ = eE.symm (algebraMap F E y) := by
        congr 1
        calc
          eE (algebraMap (Shrink.{0} F) (Shrink.{0} E) (eF.symm y)) =
              algebraMap (Shrink.{0} F) E (eF.symm y) := eEAlg.commutes _
          _ = algebraMap F E y := by
            change algebraMap F E (eF (eF.symm y)) = _
            rw [eF.apply_symm_apply]
  letI : IsGalois (Shrink.{0} F) (Shrink.{0} E) :=
    IsGalois.of_equiv_equiv
      (F := F) (E := E) (M := (Shrink.{0} F)) (N := (Shrink.{0} E))
      (f := eF.symm) (g := eE.symm) hsquare
  have hbase (x : Shrink.{0} F) :
      eE (algebraMap (Shrink.{0} F) (Shrink.{0} E) x) =
        algebraMap F E (algebraMap (Shrink.{0} F) F x) := by
    change eEAlg (algebraMap (Shrink.{0} F) (Shrink.{0} E) x) = _
    rw [eEAlg.commutes]
    exact IsScalarTower.algebraMap_apply (Shrink.{0} F) F E x
  let g : Gal((Shrink.{0} E)/(Shrink.{0} F)) ≃* Gal(E/F) :=
    mixedUniverseGal eFAlg.symm eE hbase
  letI : IsMulCommutative Gal((Shrink.{0} E)/(Shrink.{0} F)) := by
    refine ⟨⟨fun sigma tau => g.injective ?_⟩⟩
    simpa only [map_mul] using mul_comm (g sigma) (g tau)
  have he : (algebraMap F E).comp eF.toRingHom =
      eE.toRingHom.comp (algebraMap (Shrink.{0} F) (Shrink.{0} E)) := by
    apply RingHom.ext
    intro y
    change algebraMap F E (eF y) =
      eE (algebraMap (Shrink.{0} F) (Shrink.{0} E) y)
    exact (eEAlg.commutes y).symm
  let galOld : Gal((Shrink.{0} E)/(Shrink.{0} F)) ≃* Gal(E/F) :=
    galMulEquiv eF eE he
  have hgal : galOld = g := by
    apply MulEquiv.ext
    intro sigma
    ext x
    rfl
  let a0 : (Shrink.{0} F)ˣ := Units.map eF.symm.toRingHom a
  let artin0 : (Shrink.{0} F)ˣ →*
      Gal((Shrink.{0} E)/(Shrink.{0} F)) :=
    @abelianArtinHom (Shrink.{0} F) (Shrink.{0} E)
      inferInstance inferInstance hlocal inferInstance inferInstance
      inferInstance inferInstance inferInstance
  let artinU : (Shrink.{0} F)ˣ →*
      Gal((Shrink.{0} E)/(Shrink.{0} F)) :=
    @abelianArtinUniverse (Shrink.{0} F) (Shrink.{0} E)
      inferInstance inferInstance inferInstance inferInstance hlocal
      inferInstance inferInstance inferInstance inferInstance inferInstance
  have hartin : artin0 = artinU :=
    @abelian_local_universe
      (Shrink.{0} F) (Shrink.{0} E) inferInstance inferInstance hlocal
      inferInstance inferInstance inferInstance inferInstance inferInstance
  unfold abelianLocalSmall
  unfold abelianArtinSmall
  simp only [MonoidHom.coe_comp, Function.comp_apply,
    MulEquiv.coe_toMonoidHom, MulEquiv.trans_apply,
    quotient_comap_mk]
  change chi (Additive.ofMul
    (galOld (artin0 a0))) = _
  rw [hgal]
  rw [hartin]
  let sourceInvariant :=
    @characterCupUniverse (Shrink.{0} F) (Shrink.{0} E)
      inferInstance inferInstance inferInstance inferInstance hlocal
      inferInstance inferInstance inferInstance inferInstance inferInstance
      a0 (chi.comp g.toAdditive)
  let sourceAmbient :=
    @ambientCupInvariant (Shrink.{0} F) (Shrink.{0} E)
      inferInstance inferInstance inferInstance inferInstance hlocal
      inferInstance inferInstance inferInstance inferInstance inferInstance
      a0 (chi.comp g.toAdditive)
  have hsource : sourceInvariant = sourceAmbient := rfl
  calc
    chi (Additive.ofMul
        (g (artinU a0))) =
        sourceInvariant := by
      exact (@abelian_universe_comp (Shrink.{0} F) (Shrink.{0} E)
        inferInstance inferInstance inferInstance inferInstance hlocal
        inferInstance inferInstance inferInstance inferInstance inferInstance
        (Gal(E/F)) inferInstance g.toMonoidHom a0 chi).symm
    _ = characterCupUniverse F E a chi := by
      have hnorm (x : Shrink.{0} F) : ‖eFAlg x‖ = ‖x‖ := rfl
      rw [hsource]
      change sourceAmbient = ambientCupInvariant F E a chi
      have hmapA :
          Units.map (algebraMap (Shrink.{0} F) F).toMonoidHom a0 = a := by
        apply Units.ext
        change eF (eF.symm (a : F)) = (a : F)
        exact eF.apply_symm_apply _
      have ht :=
        @ambient_cup_universe
          (Shrink.{0} F) (Shrink.{0} E) F E
          inferInstance inferInstance inferInstance hlocal inferInstance
          inferInstance inferInstance inferInstance inferInstance
          inferInstance inferInstance inferInstance inferInstance inferInstance
          inferInstance
          inferInstance inferInstance inferInstance inferInstance
          inferInstance inferInstance
          inferInstance inferInstance
          eFAlg.symm hnorm eE hbase a0 chi
      rw [hmapA] at ht
      simpa [sourceAmbient, g, a0] using ht

/-- Hence the transported norm-residue homomorphism is exactly the ambient
cup-defined local Artin homomorphism. -/
theorem abelian_small_universe
    (F E : Type u)
    [Small.{0} F] [Small.{0} E]
    [NontriviallyNormedField F] [CharZero F] [IsUltrametricDist F]
    [ValuativeRel F]
    [Valuation.Compatible (NormedField.valuation (K := F))]
    [IsNonarchimedeanLocalField F]
    [Field E] [Algebra F E] [FiniteDimensional F E]
    [IsGalois F E] [IsMulCommutative Gal(E/F)] :
    abelianLocalSmall F E =
      abelianArtinUniverse F E :=
  small_universe_formula F E
    (smallCupFormula F E)

end

end Towers.CField.LRecip
