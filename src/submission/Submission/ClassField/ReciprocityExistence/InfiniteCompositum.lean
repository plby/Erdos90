import Submission.ClassField.NormIndex.IdeleTowerLocal
import Submission.ClassField.ReciprocityExistence.GaloisRestriction
import Submission.ClassField.ReciprocityExistence.InfiniteArtin
import Submission.NumberTheory.Locals.PlaceExtension

/-!
# The archimedean local compositum square in Lemma VII.8.4

The canonical infinite-place Artin maps are independent of the selected
upper place.  We therefore select a single place of the global compositum
and use its restrictions to both fields.  Both paths around the desired
square factor through the upper completed norm quotient.  That quotient has
order one or two.  In the nontrivial case, injectivity of restriction and
the elementary archimedean ramification classification identify both paths
with the unique equivalence onto the lower decomposition group.
-/

namespace Submission.CField.RExist

open AbsoluteValue Set
open NumberField
open Submission.NumberTheory.Milne
open Submission.CField.Ideles
open Submission.CField.Recip
open Submission.CField.NIndex

noncomputable section

universe u

/-- A fixed, choice-independent archimedean local Artin map with global
Galois target. -/
noncomputable def canonicalGlobalArtin
    (K L : Type u) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [IsMulCommutative Gal(L/K)]
    (v : InfinitePlace K) :
    v.1.Completionˣ →* Gal(L/K) := by
  let w : InfinitePlacesAbove (K := K) (L := L) v :=
    ⟨Classical.choose (infinite_place (L := L) v),
      Classical.choose_spec (infinite_place (L := L) v)⟩
  exact infiniteGlobalArtin v w

theorem global_artin_hom
    (K L : Type u) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [IsMulCommutative Gal(L/K)]
    (v : InfinitePlace K)
    (w : InfinitePlacesAbove (K := K) (L := L) v) :
    canonicalGlobalArtin K L v =
      infiniteGlobalArtin v w := by
  unfold canonicalGlobalArtin
  exact infinite_artin_independent v _ w

set_option maxHeartbeats 3000000 in
-- Surjectivity of the real completion norm elaborates the dependent completion tower.
set_option synthInstance.maxHeartbeats 500000 in
-- The real completion tower requires deeper module-instance search.
private theorem infinite_upper_real
    (K L : Type u) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L]
    (v : InfinitePlace K)
    (w : InfinitePlacesAbove (K := K) (L := L) v)
    (hw : w.1.IsReal) :
    Function.Surjective
      (infiniteCompletionNorm (K := K) (L := L) v w) := by
  let hwv := infinite_lies_comap v w.1 w.2
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
          (congrArg (fun q : w.1.1.Completion ↦
            q * (completionLies v.1 w.1.1 hwv y * z)) hcoeff') }
  letI : Module.Finite v.1.Completion w.1.1.Completion :=
    infinite_completion_module (K := K) (L := L) v w
  have hv : v.IsReal :=
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
  have hdegree : Module.finrank v.1.Completion w.1.1.Completion = 1 :=
    calc
      Module.finrank v.1.Completion w.1.1.Completion =
          Module.finrank ℝ ℝ :=
        Algebra.finrank_eq_of_equiv_equiv ev ew hc
      _ = 1 := Module.finrank_self ℝ
  intro x
  let y : w.1.1.Completionˣ :=
    Units.map (algebraMap v.1.Completion w.1.1.Completion).toMonoidHom x
  refine ⟨y, ?_⟩
  apply Units.ext
  change Algebra.norm v.1.Completion
      (algebraMap v.1.Completion w.1.1.Completion (x : v.1.Completion)) = x
  rw [Algebra.norm_algebraMap, hdegree, pow_one]

set_option maxHeartbeats 10000000 in
-- The common-compositum square normalizes two completion towers and their norm maps.
set_option synthInstance.maxHeartbeats 1000000 in
-- Both sides of the compositum square carry dependent completion structures.
set_option maxRecDepth 100000 in
/-- The canonical archimedean Artin square for compatible places obtained
from one place of the compositum. -/
private theorem compositum_commutes_common
    (K K' M : Type u)
    [Field K] [NumberField K] [Field K'] [NumberField K']
    [Field M] [NumberField M]
    [Algebra K K'] [FiniteDimensional K K']
    [Algebra K' M] [Algebra K M] [IsScalarTower K K' M]
    (E : IntermediateField K M)
    [NumberField E] [FiniteDimensional K E] [IsGalois K E]
    [FiniteDimensional K' M] [IsGalois K' M]
    [IsMulCommutative Gal(E/K)] [IsMulCommutative Gal(M/K')]
    (hcompositum : E ⊔ IntermediateField.adjoin K
      (Set.range (algebraMap K' M)) = ⊤)
    (v : InfinitePlace K)
    (w : InfinitePlacesAbove (K := K) (L := K') v)
    (t : InfinitePlacesAbove (K := K') (L := M) w.1)
    (u : InfinitePlacesAbove (K := K) (L := E) v)
    (htu : t.1.comap (algebraMap E M) = u.1) :
    (compositumGaloisRestriction (K := K) (K' := K') (M := M) E).comp
        (infiniteGlobalArtin w.1 t) =
      (infiniteGlobalArtin v u).comp
        (infiniteCompletionNorm (K := K) (L := K') v w) := by
  let globalTarget : Gal(M/K') →* Gal(E/K) :=
    compositumGaloisRestriction (K := K) (K' := K') (M := M) E
  have htargetInjective : Function.Injective globalTarget :=
    compositum_restriction_injective E hcompositum
  let Dupper := absoluteValueDecomposition w.1.1 t.1.1
  let Dlower := absoluteValueDecomposition v.1 u.1.1
  let normUpper := infiniteCompletionNorm (K := K') (L := M) w.1 t
  let normLower := infiniteCompletionNorm (K := K) (L := E) v u
  let normBase := infiniteCompletionNorm (K := K) (L := K') v w
  let tu : InfinitePlacesAbove (K := E) (L := M) u.1 := ⟨t.1, htu⟩
  let Nupper : Subgroup w.1.1.Completionˣ := normUpper.range
  let Nlower : Subgroup v.1.Completionˣ := normLower.range
  let eUpper : (w.1.1.Completionˣ ⧸ Nupper) ≃* Dupper :=
    infinitePlaceArtin w.1 t
  let eLower : (v.1.Completionˣ ⧸ Nlower) ≃* Dlower :=
    infinitePlaceArtin v u
  letI : Finite (w.1.1.Completionˣ ⧸ Nupper) :=
    Finite.of_equiv Dupper eUpper.symm.toEquiv
  let rD : Dupper →* Dlower :=
    { toFun := fun sigma ↦ ⟨globalTarget sigma.1, by
          intro x
          have hu : u.1.1 = (t.1.comap (algebraMap E M)).1 :=
            (congrArg (fun q : InfinitePlace E ↦ q.1) htu).symm
          rw [hu]
          change t.1.1
              (algebraMap E M
                ((sigma.1.restrictScalars K).restrictNormal E x)) =
            t.1.1 (algebraMap E M x)
          rw [AlgEquiv.restrictNormal_commutes]
          exact sigma.2 (algebraMap E M x)⟩
      map_one' := by
        apply Subtype.ext
        exact map_one globalTarget
      map_mul' := fun sigma tau ↦ by
        apply Subtype.ext
        exact map_mul globalTarget sigma.1 tau.1 }
  have hrDInjective : Function.Injective rD := by
    intro sigma tau h
    apply Subtype.ext
    apply htargetInjective
    exact congrArg Subtype.val h
  let fQ : (w.1.1.Completionˣ ⧸ Nupper) →* Dlower :=
    rD.comp eUpper.toMonoidHom
  have hfQInjective : Function.Injective fQ :=
    hrDInjective.comp eUpper.injective
  let g : w.1.1.Completionˣ →* Dlower :=
    eLower.toMonoidHom.comp
      ((QuotientGroup.mk' Nlower).comp normBase)
  have hNupperKer : Nupper ≤ g.ker := by
    rintro x ⟨y, rfl⟩
    rw [MonoidHom.mem_ker]
    have hwt := infinite_completion_trans v w t y
    have hut := infinite_completion_trans v u tu y
    have htotal :
        (infiniteAboveTower K K' M v).symm ⟨w, t⟩ =
          (infiniteAboveTower K E M v).symm ⟨u, tu⟩ := by
      apply Subtype.ext
      rfl
    have htotalNorm :
        infiniteCompletionNorm (K := K) (L := M) v
            ((infiniteAboveTower K K' M v).symm ⟨w, t⟩) =
          infiniteCompletionNorm (K := K) (L := M) v
            ((infiniteAboveTower K E M v).symm ⟨u, tu⟩) := by
      congr
    have hnorm : normBase (normUpper y) = normLower
        (infiniteCompletionNorm (K := E) (L := M) u.1 tu y) := by
      calc
        normBase (normUpper y) =
            infiniteCompletionNorm (K := K) (L := M) v
              ((infiniteAboveTower K K' M v).symm ⟨w, t⟩) y :=
          hwt.symm
        _ = infiniteCompletionNorm (K := K) (L := M) v
              ((infiniteAboveTower K E M v).symm ⟨u, tu⟩) y :=
          DFunLike.congr_fun htotalNorm y
        _ = normLower
            (infiniteCompletionNorm (K := E) (L := M) u.1 tu y) := hut
    change eLower
        (QuotientGroup.mk' Nlower (normBase (normUpper y))) = 1
    rw [hnorm]
    have hmem : normLower
        (infiniteCompletionNorm (K := E) (L := M) u.1 tu y) ∈ Nlower :=
      ⟨_, rfl⟩
    have hq : QuotientGroup.mk' Nlower
        (normLower
          (infiniteCompletionNorm (K := E) (L := M) u.1 tu y)) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr hmem
    rw [hq, map_one]
  let gQ : (w.1.1.Completionˣ ⧸ Nupper) →* Dlower :=
    QuotientGroup.lift Nupper g hNupperKer
  have hDupperCases : Nat.card Dupper = 1 ∨ Nat.card Dupper = 2 := by
    let D := Dupper
    have hstabilizer : D = MulAction.stabilizer Gal(M/K') t.1 := by
      change absoluteValueDecomposition w.1.1 t.1.1 = _
      rw [absolute_decomposition_stabilizer]
      ext sigma
      rw [MulAction.mem_stabilizer_iff, MulAction.mem_stabilizer_iff]
      constructor
      · intro h
        apply InfinitePlace.ext
        exact fun x ↦ DFunLike.congr_fun h x
      · intro h
        exact congrArg (fun z : InfinitePlace M ↦ z.1) h
    change Nat.card D = 1 ∨ Nat.card D = 2
    rw [hstabilizer]
    exact InfinitePlace.nat_card_stabilizer_eq_one_or_two K' t.1
  have hDlowerCases : Nat.card Dlower = 1 ∨ Nat.card Dlower = 2 := by
    let D := Dlower
    have hstabilizer : D = MulAction.stabilizer Gal(E/K) u.1 := by
      change absoluteValueDecomposition v.1 u.1.1 = _
      rw [absolute_decomposition_stabilizer]
      ext sigma
      rw [MulAction.mem_stabilizer_iff, MulAction.mem_stabilizer_iff]
      constructor
      · intro h
        apply InfinitePlace.ext
        exact fun x ↦ DFunLike.congr_fun h x
      · intro h
        exact congrArg (fun z : InfinitePlace E ↦ z.1) h
    change Nat.card D = 1 ∨ Nat.card D = 2
    rw [hstabilizer]
    exact InfinitePlace.nat_card_stabilizer_eq_one_or_two K u.1
  have hQcard : Nat.card (w.1.1.Completionˣ ⧸ Nupper) =
      Nat.card Dupper := Nat.card_congr eUpper.toEquiv
  have hfgQ : fQ = gQ := by
    rcases hDupperCases with hUpper | hUpper
    · have hQone : Nat.card (w.1.1.Completionˣ ⧸ Nupper) = 1 :=
        hQcard.trans hUpper
      letI : Subsingleton (w.1.1.Completionˣ ⧸ Nupper) :=
        (Nat.card_eq_one_iff_unique.mp hQone).1
      apply MonoidHom.ext
      intro q
      rw [show q = 1 from Subsingleton.elim _ _, map_one, map_one]
    · have hQtwo : Nat.card (w.1.1.Completionˣ ⧸ Nupper) = 2 :=
        hQcard.trans hUpper
      have hDlowerTwo : Nat.card Dlower = 2 := by
        rcases hDlowerCases with hLower | hLower
        · have hle := Nat.card_le_card_of_injective fQ hfQInjective
          rw [hQtwo, hLower] at hle
          omega
        · exact hLower
      have htRamified : t.1.IsRamified K' := by
        rw [InfinitePlace.isRamified_iff_card_stabilizer_eq_two]
        let D := Dupper
        have hstabilizer : D = MulAction.stabilizer Gal(M/K') t.1 := by
          change absoluteValueDecomposition w.1.1 t.1.1 = _
          rw [absolute_decomposition_stabilizer]
          ext sigma
          rw [MulAction.mem_stabilizer_iff, MulAction.mem_stabilizer_iff]
          constructor
          · intro h
            apply InfinitePlace.ext
            exact fun x ↦ DFunLike.congr_fun h x
          · intro h
            exact congrArg (fun z : InfinitePlace M ↦ z.1) h
        rw [← hstabilizer]
        exact hUpper
      have hwReal : w.1.IsReal := by
        have h := htRamified.isReal
        simpa only [t.2] using h
      have hnormBaseSurjective : Function.Surjective normBase :=
        infinite_upper_real K K' v w hwReal
      have hgSurjective : Function.Surjective g := by
        intro d
        obtain ⟨q, rfl⟩ := eLower.surjective d
        obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective Nlower q
        obtain ⟨z, hz⟩ := hnormBaseSurjective a
        refine ⟨z, ?_⟩
        change eLower (QuotientGroup.mk' Nlower (normBase z)) =
          eLower (QuotientGroup.mk' Nlower a)
        rw [hz]
      have hgQSurjective : Function.Surjective gQ :=
        QuotientGroup.lift_surjective_of_surjective
          Nupper g hgSurjective hNupperKer
      have hfQBijective : Function.Bijective fQ :=
        (Nat.bijective_iff_injective_and_card fQ).mpr
          ⟨hfQInjective, hQtwo.trans hDlowerTwo.symm⟩
      have hgQBijective : Function.Bijective gQ :=
        (Nat.bijective_iff_surjective_and_card gQ).mpr
          ⟨hgQSurjective, hQtwo.trans hDlowerTwo.symm⟩
      let ef : (w.1.1.Completionˣ ⧸ Nupper) ≃* Dlower :=
        MulEquiv.ofBijective fQ hfQBijective
      let eg : (w.1.1.Completionˣ ⧸ Nupper) ≃* Dlower :=
        MulEquiv.ofBijective gQ hgQBijective
      have heg : ef = eg :=
        card_or_two
          (Or.inr hDlowerTwo) ef eg
      exact congrArg MulEquiv.toMonoidHom heg
  apply MonoidHom.ext
  intro z
  change globalTarget
      ((Dupper.subtype.comp
        (eUpper.toMonoidHom.comp (QuotientGroup.mk' Nupper))) z) =
    Dlower.subtype
      (eLower (QuotientGroup.mk' Nlower (normBase z)))
  have hz := DFunLike.congr_fun hfgQ (QuotientGroup.mk' Nupper z)
  exact congrArg Subtype.val hz

set_option maxHeartbeats 10000000 in
-- The final compositum comparison unfolds both canonical Artin constructions.
set_option synthInstance.maxHeartbeats 1000000 in
-- Both canonical Artin maps require the full compositum instance tower.
set_option maxRecDepth 100000 in
/-- The canonical archimedean local maps commute with the completion norm
and restriction in the global compositum. -/
theorem compositum_artin_commutes
    (K K' M : Type u)
    [Field K] [NumberField K] [Field K'] [NumberField K']
    [Field M] [NumberField M]
    [Algebra K K'] [FiniteDimensional K K']
    [Algebra K' M] [Algebra K M] [IsScalarTower K K' M]
    (E : IntermediateField K M)
    [NumberField E] [FiniteDimensional K E] [IsGalois K E]
    [FiniteDimensional K' M] [IsGalois K' M]
    [IsMulCommutative Gal(E/K)] [IsMulCommutative Gal(M/K')]
    (hcompositum : E ⊔ IntermediateField.adjoin K
      (Set.range (algebraMap K' M)) = ⊤)
    (v : InfinitePlace K)
    (w : InfinitePlacesAbove (K := K) (L := K') v) :
    (compositumGaloisRestriction (K := K) (K' := K') (M := M) E).comp
        (canonicalGlobalArtin K' M w.1) =
      (canonicalGlobalArtin K E v).comp
        (infiniteCompletionNorm (K := K) (L := K') v w) := by
  let t0 : InfinitePlace M :=
    Classical.choose (infinite_place (L := M) w.1)
  have ht0 : t0.comap (algebraMap K' M) = w.1 :=
    Classical.choose_spec (infinite_place (L := M) w.1)
  let t : InfinitePlacesAbove (K := K') (L := M) w.1 := ⟨t0, ht0⟩
  let u0 : InfinitePlace E := t0.comap (algebraMap E M)
  have hu0 : u0.comap (algebraMap K E) = v := by
    rw [← InfinitePlace.comap_comp]
    change t0.comap ((algebraMap E M).comp (algebraMap K E)) = v
    rw [← IsScalarTower.algebraMap_eq K E M]
    rw [IsScalarTower.algebraMap_eq K K' M]
    rw [InfinitePlace.comap_comp, ht0, w.2]
  let u : InfinitePlacesAbove (K := K) (L := E) v := ⟨u0, hu0⟩
  rw [global_artin_hom K' M w.1 t]
  rw [global_artin_hom K E v u]
  exact compositum_commutes_common
    K K' M E hcompositum v w t u rfl

end

end Submission.CField.RExist
