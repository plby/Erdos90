import Towers.ClassField.GrunwaldWang.GrunwaldWangStatement
import Towers.ClassField.GrunwaldWang.IdeleCharacterGlobalization
import Towers.ClassField.Ideles.IdeleNorm
import Towers.NumberTheory.Galois.PlaceCompletionDegree
import Towers.NumberTheory.Locals.PlaceExtension
import Towers.ClassField.IdeleCohomology.CompletionProductAction

/-!
# Chapter VIII, Section 2, Corollary 2.5

Prescribed positive local degrees at finitely many places are realized by a
cyclic number-field extension whose global degree is their least common
multiple.  Local degrees are stated using the actual completions and the
canonical maps between them.
-/

namespace Towers.CField.GWang

open AbsoluteValue IsDedekindDomain NumberField
open Towers.NumberTheory.Milne
open Towers.CField.Ideles
open Towers.CField.Recip
open Towers.CField.ICohomo

noncomputable section
universe u

/-- A positive integer is a possible archimedean local degree when it is the
degree of an actual finite extension of the corresponding completion. -/
structure PossibleLocalDegree
    (K : Type u) [Field K] [NumberField K]
    (v : InfinitePlace K) (n : ℕ) where
  E : Type u
  fieldE : Field E
  algebraE : Algebra v.1.Completion E
  finiteDimensionalE : FiniteDimensional v.1.Completion E
  degree_eq : Module.finrank v.1.Completion E = n

/-- The actual finite cyclic number-field extension in Corollary VIII.2.5. -/
structure CEDataa
    (K : Type u) [Field K] [NumberField K] where
  L : Type u
  fieldL : Field L
  numberFieldL : NumberField L
  algebraKL : Algebra K L
  finiteDimensionalKL : FiniteDimensional K L
  isGaloisKL : IsGalois K L
  isCyclicKL : IsCyclic Gal(L/K)

/-- The degree of every completion above `v` is `n`.  Since the global
extension is Galois, these degrees are independent of the chosen place
above `v`; stating all of them avoids making an arbitrary choice. -/
def CEDataa.HasLocalDegree
    {K : Type u} [Field K] [NumberField K]
    (data : CEDataa K)
    (v : Place K) (n : ℕ) : Prop := by
  letI : Field data.L := data.fieldL
  letI : NumberField data.L := data.numberFieldL
  letI : Algebra K data.L := data.algebraKL
  letI : FiniteDimensional K data.L := data.finiteDimensionalKL
  letI : IsGalois K data.L := data.isGaloisKL
  cases v with
  | inl P =>
      exact ∀ w : CompletionPlacesAbove (L := data.L) (FinitePlace.mk P).val,
        letI : Algebra (FinitePlace.mk P).val.Completion w.1.Completion :=
          (completionLies (FinitePlace.mk P).val w.1 w.2).toAlgebra
        Module.finrank (FinitePlace.mk P).val.Completion w.1.Completion = n
  | inr v =>
      exact ∀ w : InfinitePlacesAbove (K := K) (L := data.L) v,
        letI : Algebra v.1.Completion w.1.1.Completion :=
          (completionLies v.1 w.1.1
            (infinite_lies_comap v w.1 w.2)).toAlgebra
        Module.finrank v.1.Completion w.1.1.Completion = n

/-- A finite place lying over the rational prime two. -/
def PlaceAboveTwo
    (K : Type u) [Field K] [NumberField K]
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K)) : Prop :=
  (2 : NumberField.RingOfIntegers K) ∈ P.asIdeal

/-- Local characters of the prescribed orders, including the refined
2-adic choice used to bypass the Wang exception. -/
structure CharacterChoiceData
    (K : Type u) [Field K] [NumberField K]
    (S : Finset (Place K)) (n_v : S → ℕ) where
  localCharacter : ∀ v : S, OrderLocalCharacter K v.1
  local_order : ∀ v : S, orderOf (localCharacter v).1 = n_v v
  wang_avoiding_extension :
    HasWangException K (Finset.univ.lcm n_v) →
      ∃ (P : HeightOneSpectrum (NumberField.RingOfIntegers K)),
        PlaceAboveTwo K P ∧
        ∃ chi : IdeleClassCharacter K,
          orderOf chi = Finset.univ.lcm n_v ∧
          ∀ v : S,
            CharacterRestrictsTo K chi v.1 (localCharacter v).1

/-- The narrow local-character input in the printed proof.  At finite places
away from two one uses an unramified character; at infinite places the
possible-degree assumption is necessary; in the exceptional case an
additional character at a place over two supplies the exact-order global
extension omitted by the coarse `GrunwaldWangTheorem` interface. -/
def CharacterChoiceBridge
    (K : Type u) [Field K] [NumberField K]
    (_hGW : GrunwaldWangTheorem K) : Prop :=
  ∀ (S : Finset (Place K)) (n_v : S → ℕ),
    (∀ v, 0 < n_v v) →
    (∀ v : S, match v.1 with
      | .inl _ => True
      | .inr w => Nonempty (PossibleLocalDegree K w (n_v v))) →
    Nonempty (CharacterChoiceData K S n_v)

/-- The remaining class-field compatibility: a finite-order global character
cuts out a cyclic class field, and restriction orders equal the degrees of
the corresponding completed extensions. -/
def CharacterClassBridge : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K]
    (S : Finset (Place K))
    (chi_v : ∀ v : S, OrderLocalCharacter K v.1)
    (chi : IdeleClassCharacter K),
    0 < orderOf chi →
    (∀ v : S, CharacterRestrictsTo K chi v.1 (chi_v v).1) →
      ∃ data : CEDataa K,
        letI : Field data.L := data.fieldL
        letI : Algebra K data.L := data.algebraKL
        Module.finrank K data.L = orderOf chi ∧
          ∀ v : S, data.HasLocalDegree v.1 (orderOf (chi_v v).1)

/-- Forget the reciprocity decorations on a finite-order character
globalization and retain its cyclic number-field extension. -/
noncomputable def OCGlobala.cyclic_ext_data
    {K : Type u} [Field K] [NumberField K]
    {chi : IdeleClassCharacter K}
    (data : OCGlobala chi) :
    CEDataa K where
  L := data.extension.1
  fieldL := inferInstance
  numberFieldL := NumberField.of_module_finite K data.extension.1
  algebraKL := inferInstance
  finiteDimensionalKL := inferInstance
  isGaloisKL := inferInstance
  isCyclicKL := data.cyclic

set_option synthInstance.maxHeartbeats 500000 in
-- Completion transport and decomposition-group cardinality are
-- typeclass-intensive for the intermediate field carried by `data`.
set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 3000000 in
/-- At a finite place, restriction order is the degree of every completed
factor of the cyclic class field cut out by the global character. -/
theorem OCGlobala.fin_local_degreerestrict
    {K : Type u} [Field K] [NumberField K]
    {chi : IdeleClassCharacter K}
    (data : OCGlobala chi)
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (chiP : OrderLocalCharacter K (.inl P))
    (hrestrict : CharacterRestrictsTo K chi (.inl P) chiP.1) :
    data.cyclic_ext_data.HasLocalDegree (.inl P)
      (orderOf chiP.1) := by
  letI : NumberField data.extension.1 :=
    NumberField.of_module_finite K data.extension.1
  let v := (FinitePlace.mk P).val
  change ∀ w : CompletionPlacesAbove (L := data.extension.1) v,
    letI : Algebra v.Completion w.1.Completion :=
      (completionLies v w.1 w.2).toAlgebra
    Module.finrank v.Completion w.1.Completion = orderOf chiP.1
  intro w
  letI : Algebra v.Completion w.1.Completion :=
    (completionLies v w.1 w.2).toAlgebra
  haveI : P.asIdeal.IsMaximal := P.isPrime.isMaximal P.ne_bot
  obtain ⟨Q, hQ⟩ :=
    finite_places_nonempty (L := data.extension.1) P.asIdeal
  have hQfactor : Q ∈
      IsDedekindDomain.primesOverFinset P.asIdeal
        (NumberField.RingOfIntegers data.extension.1) :=
    (IsDedekindDomain.mem_primesOverFinset_iff P.ne_bot
      (NumberField.RingOfIntegers data.extension.1)).2 hQ
  let Qfactor : UpperPrimeFactors
      (K := K) (L := data.extension.1) P := ⟨Q, hQfactor⟩
  obtain ⟨phiP, hphiP, hcompat⟩ :=
    data.exists_place_artin P Qfactor chiP.1 hrestrict
  obtain ⟨w₀, hw₀v, _hw₀q, hrange⟩ :=
    artin_range_decomposition
      data.extension P Qfactor phiP hphiP
  let w₀Above : CompletionPlacesAbove (L := data.extension.1) v :=
    ⟨w₀, hw₀v⟩
  letI : Algebra v.Completion w₀.Completion :=
    (completionLies v w₀ hw₀v).toAlgebra
  have horder : orderOf chiP.1 = Nat.card phiP.range :=
    circle_character_compatible
      chiP.1 chiP.2 phiP data.finiteCharacter
        data.finiteCharacter_injective hcompat
  have hdegree₀ :
      Module.finrank v.Completion w₀.Completion = orderOf chiP.1 := by
    calc
      Module.finrank v.Completion w₀.Completion =
          Nat.card (absoluteValueDecomposition v w₀) :=
        finrank_decomposition_card P w₀Above
      _ = Nat.card phiP.range :=
        congrArg
          (fun H : Subgroup Gal(data.extension.1/K) => Nat.card H)
          hrange.symm
      _ = orderOf chiP.1 := horder.symm
  letI : MulAction.IsPretransitive Gal(data.extension.1/K)
      (CompletionPlacesAbove (L := data.extension.1) v) :=
    completion_above_pretransitive P
  obtain ⟨sigma, hsigma⟩ :=
    MulAction.exists_smul_eq Gal(data.extension.1/K) w w₀Above
  have hw : sigma⁻¹ • w₀Above = w := by
    calc
      sigma⁻¹ • w₀Above = sigma⁻¹ • (sigma • w) :=
        congrArg (fun z => sigma⁻¹ • z) hsigma.symm
      _ = w := inv_smul_smul sigma w
  subst w
  exact
    (completionTransportAlg v sigma w₀Above).toLinearEquiv.finrank_eq.trans
      hdegree₀

/-- The remaining local statement after V.5.2, V.5.3, and V.5.5 have
constructed the cyclic class field: the order of a restricted character is
the degree of every completion above that place. -/
def RestrictionDegreeCompatibility : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K]
    (chi : IdeleClassCharacter K)
    (data : OCGlobala chi)
    (v : Place K) (chi_v : OrderLocalCharacter K v),
    CharacterRestrictsTo K chi v chi_v.1 →
      data.cyclic_ext_data.HasLocalDegree v
        (orderOf chi_v.1)

/-- The sole remaining archimedean input is numerical and independent of
characters: the degree of an infinite completion is the order of its
decomposition group.  This is the archimedean half of Proposition 8.10. -/
def InfiniteDegreeCompatibility : Prop :=
  ∀ (K L : Type u) [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (v : InfinitePlace K)
    (w : InfinitePlacesAbove (K := K) (L := L) v),
    letI : Algebra v.1.Completion w.1.1.Completion :=
      (completionLies v.1 w.1.1
        (infinite_lies_comap v w.1 w.2)).toAlgebra
    Module.finrank v.1.Completion w.1.1.Completion =
      Nat.card (absoluteValueDecomposition v.1 w.1.1)

set_option maxHeartbeats 3000000 in
-- Comparing the completed algebra map with the standard maps `ℝ → ℝ`,
-- `ℝ → ℂ`, and `ℂ → ℂ` unfolds the archimedean completion models.
/-- The archimedean degree/decomposition-group formula.  Both sides are one
except when a real place becomes complex, when both sides are two. -/
theorem infiniteDegreeCompatibility :
    InfiniteDegreeCompatibility.{u} := by
  intro K L _ _ _ _ _ _ _ v w
  let hwv : AbsoluteValue.LiesOver w.1.1 v.1 :=
    infinite_lies_comap v w.1 w.2
  letI : Fact (AbsoluteValue.LiesOver w.1.1 v.1) := ⟨hwv⟩
  letI : Algebra v.1.Completion w.1.1.Completion :=
    (completionLies v.1 w.1.1 hwv).toAlgebra
  letI : SMul v.1.Completion w.1.1.Completion :=
    ((completionLies v.1 w.1.1 hwv).toAlgebra).toSMul
  letI : Module v.1.Completion w.1.1.Completion := Algebra.toModule
  letI : ContinuousMul w.1.1.Completion := inferInstance
  letI : ContinuousSMul v.1.Completion w.1.1.Completion :=
    ⟨((completion_lies_isometry v.1 w.1.1 hwv).continuous.comp
      continuous_fst).mul continuous_snd⟩
  let hvUniform : IsUniformAddGroup (WithAbs v.1) :=
    SeminormedAddCommGroup.to_isUniformAddGroup
  let hwUniform : IsUniformAddGroup (WithAbs w.1.1) :=
    SeminormedAddCommGroup.to_isUniformAddGroup
  letI canonicalScalarTower :
      @IsScalarTower K v.1.Completion w.1.1.Completion
        (UniformSpace.Completion.instSMul K (WithAbs v.1))
        ((completionLies v.1 w.1.1 hwv).toAlgebra.toSMul)
        (UniformSpace.Completion.instSMul K (WithAbs w.1.1)) :=
    { smul_assoc := by
        intro x y z
        simp only [UniformSpace.Completion.smul_def]
        rw [@UniformSpace.Completion.map_smul_eq_mul_coe
              (WithAbs v.1) _ _ hvUniform _ K _
              (WithAbs.instAlgebra v.1) _ x,
          @UniformSpace.Completion.map_smul_eq_mul_coe
              (WithAbs w.1.1) _ _ hwUniform _ K _
              (WithAbs.instAlgebra w.1.1) _ x,
          Algebra.smul_def, Algebra.smul_def]
        dsimp only
        have hcoeff := RingHom.congr_fun
          (completion_lies_comp v.1 w.1.1 hwv) x
        change completionLies v.1 w.1.1 hwv
            (completionEmbedding v.1 x) =
          completionEmbedding w.1.1 (algebraMap K L x) at hcoeff
        have hvcoe :
            (algebraMap K (WithAbs v.1) x : v.1.Completion) =
              completionEmbedding v.1 x := by
          simp [completionEmbedding_apply, WithAbs.algebraMap_right_apply]
        have hwcoe :
            (algebraMap K (WithAbs w.1.1) x : w.1.1.Completion) =
              completionEmbedding w.1.1 (algebraMap K L x) := by
          simp [completionEmbedding_apply, WithAbs.algebraMap_right_apply]
        have hlocal :
            algebraMap v.1.Completion w.1.1.Completion =
              completionLies v.1 w.1.1 hwv := rfl
        have hcoeff' :
            completionLies v.1 w.1.1 hwv
                (algebraMap K (WithAbs v.1) x : v.1.Completion) =
              (algebraMap K (WithAbs w.1.1) x : w.1.1.Completion) := by
          calc
            _ = completionLies v.1 w.1.1 hwv
                  (completionEmbedding v.1 x) :=
              congrArg (completionLies v.1 w.1.1 hwv) hvcoe
            _ = completionEmbedding w.1.1 (algebraMap K L x) := hcoeff
            _ = _ := hwcoe.symm
        rw [hlocal, map_mul]
        exact (mul_assoc _ _ _).trans
          (congrArg (fun t : w.1.1.Completion =>
            t * (completionLies v.1 w.1.1 hwv y * z)) hcoeff') }
  have hstabilizer :
      absoluteValueDecomposition v.1 w.1.1 =
        MulAction.stabilizer Gal(L/K) w.1 := by
    rw [absolute_decomposition_stabilizer]
    ext sigma
    rw [MulAction.mem_stabilizer_iff, MulAction.mem_stabilizer_iff]
    constructor
    · intro h
      apply InfinitePlace.ext
      exact fun x => DFunLike.congr_fun h x
    · intro h
      exact congrArg (fun z : InfinitePlace L => z.1) h
  rcases w.1.isReal_or_isComplex with hw | hw
  · have hv : v.IsReal :=
      InfinitePlace.LiesOver.isReal_of_isReal_over (v := v) w.1 hw
    let ev := InfinitePlace.Completion.ringEquivRealOfIsReal hv
    let ew := InfinitePlace.Completion.ringEquivRealOfIsReal hw
    have hlie :=
      InfinitePlace.LiesOver.extensionEmbedding_liesOver_of_isReal w.1 hv
    have hc :
        (algebraMap ℝ ℝ).comp ev.toRingHom =
          ew.toRingHom.comp
            (algebraMap v.1.Completion w.1.1.Completion) := by
      ext y
      apply Complex.ofReal_injective
      simp [ev, ew,
        InfinitePlace.Completion.ringEquivRealOfIsReal,
        InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply]
    calc
      Module.finrank v.1.Completion w.1.1.Completion =
          Module.finrank ℝ ℝ :=
        Algebra.finrank_eq_of_equiv_equiv ev ew hc
      _ = 1 := Module.finrank_self ℝ
      _ = Nat.card (absoluteValueDecomposition v.1 w.1.1) := by
        rw [hstabilizer, InfinitePlace.card_stabilizer, if_pos]
        exact hw.isUnramified K
  · rcases v.isReal_or_isComplex with hv | hv
    · let ev := InfinitePlace.Completion.ringEquivRealOfIsReal hv
      let ew := InfinitePlace.Completion.ringEquivComplexOfIsComplex hw
      have hlie :=
        InfinitePlace.LiesOver.extensionEmbedding_liesOver_of_isReal w.1 hv
      have hc :
          (algebraMap ℝ ℂ).comp ev.toRingHom =
            ew.toRingHom.comp
              (algebraMap v.1.Completion w.1.1.Completion) := by
        ext y
        simp [ev, ew,
          InfinitePlace.Completion.ringEquivRealOfIsReal,
          InfinitePlace.Completion.ringEquivComplexOfIsComplex,
          InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply]
      have hramified : w.1.IsRamified K := by
        rw [InfinitePlace.isRamified_iff]
        exact ⟨hw, by simpa [InfinitePlace.LiesOver.comap_eq w.1 v] using hv⟩
      calc
        Module.finrank v.1.Completion w.1.1.Completion =
            Module.finrank ℝ ℂ :=
          Algebra.finrank_eq_of_equiv_equiv ev ew hc
        _ = 2 := Complex.finrank_real_complex
        _ = Nat.card (absoluteValueDecomposition v.1 w.1.1) := by
          rw [hstabilizer, InfinitePlace.card_stabilizer, if_neg]
          exact hramified
    · have hwComplex : w.1.IsComplex :=
        InfinitePlace.LiesOver.isComplex_of_isComplex_under w.1 hv
      let ev := InfinitePlace.Completion.ringEquivComplexOfIsComplex hv
      let ew := InfinitePlace.Completion.ringEquivComplexOfIsComplex hwComplex
      rcases
          InfinitePlace.LiesOver.embedding_comp_eq_or_conjugate_embedding_comp_eq
            w.1 v with h | h
      · letI : NumberField.ComplexEmbedding.LiesOver
            w.1.embedding v.embedding := ⟨h⟩
        have hlie :=
          InfinitePlace.Completion.liesOver_extensionEmbedding (v := v) w.1
        have hc :
            (algebraMap ℂ ℂ).comp ev.toRingHom =
              ew.toRingHom.comp
                (algebraMap v.1.Completion w.1.1.Completion) := by
          ext y
          simp [ev, ew,
            InfinitePlace.Completion.ringEquivComplexOfIsComplex]
        calc
          Module.finrank v.1.Completion w.1.1.Completion =
              Module.finrank ℂ ℂ :=
            Algebra.finrank_eq_of_equiv_equiv ev ew hc
          _ = 1 := Module.finrank_self ℂ
          _ = Nat.card (absoluteValueDecomposition v.1 w.1.1) := by
            rw [hstabilizer, InfinitePlace.card_stabilizer, if_pos]
            exact InfinitePlace.isUnramified_iff.mpr (Or.inr (by
              simpa [InfinitePlace.LiesOver.comap_eq w.1 v] using hv))
      · letI : NumberField.ComplexEmbedding.LiesOver
            (NumberField.ComplexEmbedding.conjugate w.1.embedding)
              v.embedding := ⟨h⟩
        have hlie :=
          InfinitePlace.Completion.liesOver_conjugate_extensionEmbedding
            (v := v) w.1
        let ew' : w.1.1.Completion ≃+* ℂ :=
          ew.trans Complex.conjAe.toRingEquiv
        have hc :
            (algebraMap ℂ ℂ).comp ev.toRingHom =
              ew'.toRingHom.comp
                (algebraMap v.1.Completion w.1.1.Completion) := by
          ext y
          simpa [ev, ew, ew',
            InfinitePlace.Completion.ringEquivComplexOfIsComplex] using
              (RingHom.congr_fun hlie.over y).symm
        calc
          Module.finrank v.1.Completion w.1.1.Completion =
              Module.finrank ℂ ℂ :=
            Algebra.finrank_eq_of_equiv_equiv ev ew' hc
          _ = 1 := Module.finrank_self ℂ
          _ = Nat.card (absoluteValueDecomposition v.1 w.1.1) := by
            rw [hstabilizer, InfinitePlace.card_stabilizer, if_pos]
            exact InfinitePlace.isUnramified_iff.mpr (Or.inr (by
              simpa [InfinitePlace.LiesOver.comap_eq w.1 v] using hv))

set_option synthInstance.maxHeartbeats 500000 in
-- The archimedean local Artin predicate unfolds completion norm quotients.
set_option maxHeartbeats 2000000 in
/-- Once the numerical archimedean Proposition 8.10 statement is supplied,
local reciprocity identifies restriction order with completion degree. -/
theorem OCGlobala.infinite_local_degreerestrict
    {K : Type u} [Field K] [NumberField K]
    {chi : IdeleClassCharacter K}
    (data : OCGlobala chi)
    (v : InfinitePlace K)
    (chi_v : OrderLocalCharacter K (.inr v))
    (hrestrict : CharacterRestrictsTo K chi (.inr v) chi_v.1)
    (hdegree : InfiniteDegreeCompatibility.{u}) :
    data.cyclic_ext_data.HasLocalDegree (.inr v)
      (orderOf chi_v.1) := by
  letI : NumberField data.extension.1 :=
    NumberField.of_module_finite K data.extension.1
  change ∀ w : InfinitePlacesAbove
      (K := K) (L := data.extension.1) v,
    letI : Algebra v.1.Completion w.1.1.Completion :=
      (completionLies v.1 w.1.1
        (infinite_lies_comap v w.1 w.2)).toAlgebra
    Module.finrank v.1.Completion w.1.1.Completion = orderOf chi_v.1
  intro w
  letI : Algebra v.1.Completion w.1.1.Completion :=
    (completionLies v.1 w.1.1
      (infinite_lies_comap v w.1 w.2)).toAlgebra
  obtain ⟨phi_v, hphi_v, hcompat⟩ :=
    data.exists_place_artia v w chi_v.1 hrestrict
  have hrange := infinite_artin_decomposition
    data.extension v w phi_v hphi_v
  have horder : orderOf chi_v.1 = Nat.card phi_v.range :=
    circle_character_compatible
      chi_v.1 chi_v.2 phi_v data.finiteCharacter
        data.finiteCharacter_injective hcompat
  calc
    Module.finrank v.1.Completion w.1.1.Completion =
        Nat.card (absoluteValueDecomposition v.1 w.1.1) :=
      hdegree K data.extension.1 v w
    _ = Nat.card phi_v.range :=
      congrArg
        (fun H : Subgroup Gal(data.extension.1/K) => Nat.card H)
        hrange.symm
    _ = orderOf chi_v.1 := horder.symm

/-- The general local compatibility follows from the proved finite-place
case and the residual archimedean comparison. -/
theorem restriction_compatibility_infinite
    (hinfinite : InfiniteDegreeCompatibility.{u}) :
    RestrictionDegreeCompatibility.{u} := by
  intro K _ _ chi data v chi_v hrestrict
  cases v with
  | inl P =>
      exact data.fin_local_degreerestrict P chi_v hrestrict
  | inr v =>
      exact data.infinite_local_degreerestrict
        v chi_v hrestrict hinfinite

/-- The broad character/class-field bridge reduces to the genuine global
class-field theorems and the single local restriction-degree comparison. -/
theorem character_bridge_cft
    (hV52 : ∀ (K : Type u) [Field K] [NumberField K],
      GlobalArtinProposition (K := K))
    (hV53 : ∀ (K : Type u) [Field K] [NumberField K],
      IdeleReciprocityLaw (K := K))
    (hV55 : ∀ (K : Type u) [Field K] [NumberField K],
      IdeleExistenceTheorem (K := K)) :
    CharacterClassBridge.{u} := by
  let hlocal : RestrictionDegreeCompatibility.{u} :=
    restriction_compatibility_infinite
      infiniteDegreeCompatibility
  intro K _ _ S chi_v chi hpositive hrestrict
  have hchi : IsOfFinOrder chi := orderOf_pos_iff.mp hpositive
  obtain ⟨globalization⟩ :=
    idele_character_globalization chi hchi
      (hV52 K) (hV53 K) (hV55 K)
  let data := globalization.cyclic_ext_data
  refine ⟨data, ?_, ?_⟩
  · exact globalization.degree_eq_order
  · intro v
    exact hlocal K chi globalization v.1 (chi_v v) (hrestrict v)

/-- Corollary 2.5 from Grunwald--Wang, the Wang-avoiding local choices, and
the character/class-field compatibility. -/
theorem possible_grunwald_wang
    (hGW : ∀ (K : Type u) [Field K] [NumberField K], GrunwaldWangTheorem K)
    (hchoice : ∀ (K : Type u) [Field K] [NumberField K],
      CharacterChoiceBridge K (hGW K))
    (hclassField : CharacterClassBridge.{u}) :
    (∀ (K : Type u) [Field K] [NumberField K]
          (S : Finset (Place K)) (n_v : S → ℕ),
          (∀ v, 0 < n_v v) →
          (∀ v : S, match v.1 with
            | .inl _ => True
            | .inr w => Nonempty (PossibleLocalDegree K w (n_v v))) →
            ∃ data : CEDataa K,
              letI : Field data.L := data.fieldL
              letI : Algebra K data.L := data.algebraKL
              Module.finrank K data.L = Finset.univ.lcm n_v ∧
                ∀ v : S, data.HasLocalDegree v.1 (n_v v)) := by
  intro K _ _ S n_v hpositive hpossible
  obtain ⟨choice⟩ := hchoice K S n_v hpositive hpossible
  let n := Finset.univ.lcm n_v
  have hlcm : Finset.univ.lcm
      (fun v : S => orderOf (choice.localCharacter v).1) = n := by
    dsimp only [n]
    apply Finset.lcm_congr rfl
    intro v _
    exact choice.local_order v
  obtain ⟨chi, hchiOrder, hrestrict⟩ :
      ∃ chi : IdeleClassCharacter K, orderOf chi = n ∧
        ∀ v : S,
          CharacterRestrictsTo K chi v.1 (choice.localCharacter v).1 := by
    by_cases hWang : HasWangException K n
    · obtain ⟨P, hP, chi, horder, hrestr⟩ :=
        choice.wang_avoiding_extension hWang
      exact ⟨chi, horder, hrestr⟩
    · have hno : ¬HasWangException K
          (Finset.univ.lcm
            (fun v : S => orderOf (choice.localCharacter v).1)) := by
        rwa [hlcm]
      obtain ⟨chi, horder, hrestr⟩ :=
        (hGW K).2 S choice.localCharacter hno
      exact ⟨chi, horder.trans hlcm, hrestr⟩
  have hnpos : 0 < n := by
    apply Nat.pos_of_ne_zero
    rw [ne_eq, Finset.lcm_eq_zero_iff]
    push Not
    intro v _
    exact (hpositive v).ne'
  obtain ⟨data, hdegree, hlocal⟩ :=
    hclassField K S choice.localCharacter chi
      (hchiOrder.symm ▸ hnpos) hrestrict
  refine ⟨data, ?_, ?_⟩
  · exact hdegree.trans hchiOrder
  · intro v
    rw [← choice.local_order v]
    exact hlocal v

end
end Towers.CField.GWang
