import Submission.NumberTheory.Completions.PlaceFactorCorrespondence


open Polynomial NumberField Complex
open scoped ComplexConjugate

private theorem or_real_roots
    {p : ℝ[X]} (hp : Irreducible p) (hmonic : p.Monic)
    {z y : ℂ}
    (hz : eval₂ (algebraMap ℝ ℂ) z p = 0)
    (hy : eval₂ (algebraMap ℝ ℂ) y p = 0) :
    y = z ∨ y = conj z := by
  have hz' : aeval z p = 0 := by simpa [aeval_def] using hz
  have hy' : aeval y p = 0 := by simpa [aeval_def] using hy
  have hzint : IsIntegral ℝ z := ⟨p, hmonic, hz'⟩
  have hpmin : p = minpoly ℝ z :=
    minpoly.eq_of_irreducible_of_monic hp hz' hmonic
  have hyroot : y ∈ (minpoly ℝ z).rootSet ℂ := by
    rw [mem_rootSet_of_ne (minpoly.ne_zero hzint), ← hpmin]
    exact hy'
  have hyrange : y ∈ Set.range fun σ : ℂ →ₐ[ℝ] ℂ ↦ σ z := by
    rw [Algebra.IsAlgebraic.range_eval_eq_rootSet_minpoly ℂ z]
    exact hyroot
  rcases hyrange with ⟨σ, hσ⟩
  rcases Complex.real_algHom_eq_id_or_conj σ with hσid | hσconj
  · left
    have hzσ : σ z = z := by
      exact DFunLike.congr_fun hσid z
    exact hσ.symm.trans hzσ
  · right
    have hzσ : σ z = conj z := by
      simpa only [Complex.conjAe_coe] using DFunLike.congr_fun hσconj z
    exact hσ.symm.trans hzσ

namespace Submission.NumberTheory.Milne

noncomputable section

variable {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]
  [FiniteDimensional K L]

omit [NumberField K] in
private theorem or_irreducible_roots
    (v : InfinitePlace K) (hv : v.IsReal)
    {p : v.1.Completion[X]} (hp : Irreducible p) (hmonic : p.Monic)
    {z y : ℂ}
    (hz : eval₂ (InfinitePlace.Completion.extensionEmbedding v) z p = 0)
    (hy : eval₂ (InfinitePlace.Completion.extensionEmbedding v) y p = 0) :
    y = z ∨ y = conj z := by
  let r : v.1.Completion ≃+* ℝ :=
    InfinitePlace.Completion.ringEquivRealOfIsReal hv
  let pe : v.1.Completion[X] ≃+* ℝ[X] := Polynomial.mapEquiv r
  have hp' : Irreducible (pe p) := hp.map pe
  have hmonic' : (pe p).Monic := by
    simpa [pe, Polynomial.mapEquiv_apply] using hmonic.map r.toRingHom
  have he : (algebraMap ℝ ℂ).comp r.toRingHom =
      InfinitePlace.Completion.extensionEmbedding v := by
    ext x
    change ((InfinitePlace.Completion.extensionEmbeddingOfIsReal hv x : ℝ) : ℂ) =
      InfinitePlace.Completion.extensionEmbedding v x
    exact InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply hv x
  apply or_real_roots hp' hmonic'
  · change eval₂ (algebraMap ℝ ℂ) z (p.map r.toRingHom) = 0
    rw [eval₂_map, he]
    exact hz
  · change eval₂ (algebraMap ℝ ℂ) y (p.map r.toRingHom) = 0
    rw [eval₂_map, he]
    exact hy

omit [NumberField K] [NumberField L] [FiniteDimensional K L] in
private theorem embedding_lies_real
    (v : InfinitePlace K) (hv : v.IsReal) (w : InfinitePlace L)
    (hwv : AbsoluteValue.LiesOver w.1 v.1) :
    (InfinitePlace.Completion.extensionEmbedding w).comp
        (completionLies v.1 w.1 hwv) =
      InfinitePlace.Completion.extensionEmbedding v := by
  let ι : v.1.Completion →+* w.1.Completion :=
    completionLies v.1 w.1 hwv
  have hleft : Isometry
      ((InfinitePlace.Completion.extensionEmbedding w).comp ι) :=
    (InfinitePlace.Completion.isometry_extensionEmbedding w).comp
      (completion_lies_isometry v.1 w.1 hwv)
  apply DFunLike.ext _ _
  exact congrFun ((dense_range_embedding v.1).equalizer
    hleft.continuous
    (InfinitePlace.Completion.isometry_extensionEmbedding v).continuous (by
      apply _root_.funext
      intro x
      have hιx := RingHom.congr_fun
        (completion_lies_comp v.1 w.1 hwv) x
      change InfinitePlace.Completion.extensionEmbedding w
          (ι (completionEmbedding v.1 x)) =
        InfinitePlace.Completion.extensionEmbedding v
          (completionEmbedding v.1 x)
      rw [show ι (completionEmbedding v.1 x) =
          completionEmbedding w.1 (algebraMap K L x) by
        simpa [ι] using hιx]
      rw [completionEmbedding_apply, completionEmbedding_apply]
      rw [InfinitePlace.Completion.extensionEmbedding_coe,
        InfinitePlace.Completion.extensionEmbedding_coe]
      letI : AbsoluteValue.LiesOver w.1 v.1 := hwv
      exact RingHom.congr_fun
        (InfinitePlace.LiesOver.embedding_liesOver_of_isReal w hv).over x))

set_option maxHeartbeats 800000 in
-- Extra heartbeats are needed for the large search space in this proof.
omit [NumberField L] in
theorem minpoly_roundtrip_test
    (v : InfinitePlace K) (hv : v.IsReal) (alpha : L)
    (halpha : Algebra.adjoin K {alpha} = ⊤)
    (W : {w : InfinitePlace L // w.comap (algebraMap K L) = v}) :
    completedMinpolyPlace v alpha halpha
        (infiniteCompletedMinpoly v alpha W) = W := by
  apply Subtype.ext
  let w : InfinitePlace L := W.1
  have hwv : w.comap (algebraMap K L) = v := W.2
  let hwvAbs : AbsoluteValue.LiesOver w.1 v.1 :=
    infinite_lies_comap v w hwv
  let iota : v.1.Completion →+* w.1.Completion :=
    completionLies v.1 w.1 hwvAbs
  letI : Algebra v.1.Completion w.1.Completion := iota.toAlgebra
  let beta : w.1.Completion := completionEmbedding w.1 alpha
  let G : CompletedMinpolyFactor v.1 alpha :=
    infiniteCompletedMinpoly v alpha W
  have hG : G.1 = minpoly v.1.Completion beta := by rfl
  let e : v.1.Completion →+* ℂ :=
    InfinitePlace.Completion.extensionEmbedding v
  let rootExists := IsAlgClosed.exists_eval₂_eq_zero e G.1
    (degree_pos_of_irreducible G.2.1).ne'
  let z : ℂ := Classical.choose rootExists
  have hz : eval₂ e z G.1 = 0 := Classical.choose_spec rootExists
  let rootMap : AdjoinRoot G.1 →+* ℂ := AdjoinRoot.lift e z hz
  let phi : L →ₐ[K] AdjoinRoot G.1 :=
    primitiveAdjoinRoot alpha halpha G.1 G.2.2.2
  let psi : L →+* ℂ := rootMap.comp phi.toRingHom
  have hpsiAlpha : psi alpha = z := by
    change rootMap (phi alpha) = z
    have hphiAlpha : phi alpha = AdjoinRoot.root G.1 := by
      unfold phi primitiveAdjoinRoot
      simpa only [PowerBasis.ofAdjoinEqTop_gen] using
        (PowerBasis.lift_gen
          (PowerBasis.ofAdjoinEqTop (Algebra.IsIntegral.isIntegral alpha) halpha)
          (AdjoinRoot.root G.1) _)
    rw [hphiAlpha]
    exact AdjoinRoot.lift_root hz
  have hpsiBase : psi.comp (algebraMap K L) = v.embedding := by
    ext x
    change rootMap (phi (algebraMap K L x)) = v.embedding x
    rw [AlgHom.commutes]
    change rootMap (algebraMap v.1.Completion (AdjoinRoot G.1)
      (completionEmbedding v.1 x)) = v.embedding x
    change (AdjoinRoot.lift e z hz)
      (AdjoinRoot.of G.1 (completionEmbedding v.1 x)) = v.embedding x
    rw [AdjoinRoot.lift_of hz, completionEmbedding_apply]
    simp [e]
  have hwBase : w.embedding.comp (algebraMap K L) = v.embedding :=
    infinite_embedding_real v hv w hwv
  have hiota :
      (InfinitePlace.Completion.extensionEmbedding w).comp iota = e := by
    exact embedding_lies_real
      v hv w hwvAbs
  have hGeval : eval₂ iota beta G.1 = 0 := by
    rw [hG]
    change aeval beta (minpoly v.1.Completion beta) = 0
    exact minpoly.aeval v.1.Completion beta
  have hwRoot : eval₂ e (w.embedding alpha) G.1 = 0 := by
    have h := congrArg (InfinitePlace.Completion.extensionEmbedding w) hGeval
    rw [map_zero, Polynomial.hom_eval₂] at h
    change eval₂
      ((InfinitePlace.Completion.extensionEmbedding w).comp iota)
      (InfinitePlace.Completion.extensionEmbedding w beta) G.1 = 0 at h
    rw [hiota] at h
    change eval₂ e
      (InfinitePlace.Completion.extensionEmbedding w
        (completionEmbedding w.1 alpha)) G.1 = 0 at h
    rw [completionEmbedding_apply,
      InfinitePlace.Completion.extensionEmbedding_coe] at h
    exact h
  have hrootPair : w.embedding alpha = z ∨
      w.embedding alpha = conj z :=
    or_irreducible_roots
      v hv G.2.1 G.2.2.1 hz hwRoot
  have hplace : InfinitePlace.mk psi = w := by
    rw [← InfinitePlace.mk_embedding w, InfinitePlace.mk_eq_iff]
    letI : Algebra K ℂ := v.embedding.toAlgebra
    let psiAlg : L →ₐ[K] ℂ :=
      { toRingHom := psi
        commutes' := fun x => RingHom.congr_fun hpsiBase x }
    let wAlg : L →ₐ[K] ℂ :=
      { toRingHom := w.embedding
        commutes' := fun x => RingHom.congr_fun hwBase x }
    let pb : PowerBasis K L :=
      PowerBasis.ofAdjoinEqTop (Algebra.IsIntegral.isIntegral alpha) halpha
    rcases hrootPair with hroot | hroot
    · left
      have hAlg : psiAlg = wAlg := by
        apply pb.algHom_ext
        rw [show pb.gen = alpha by
          exact PowerBasis.ofAdjoinEqTop_gen
            (Algebra.IsIntegral.isIntegral alpha) halpha]
        change psi alpha = w.embedding alpha
        exact hpsiAlpha.trans hroot.symm
      exact congrArg AlgHom.toRingHom hAlg
    · right
      have hconjBase :
          (NumberField.ComplexEmbedding.conjugate psi).comp
              (algebraMap K L) = v.embedding := by
        calc
          (NumberField.ComplexEmbedding.conjugate psi).comp
                (algebraMap K L) =
              NumberField.ComplexEmbedding.conjugate
                (psi.comp (algebraMap K L)) := by
            rw [NumberField.ComplexEmbedding.conjugate_comp]
          _ = NumberField.ComplexEmbedding.conjugate v.embedding := by
            rw [hpsiBase]
          _ = v.embedding := InfinitePlace.conjugate_embedding_eq_of_isReal hv
      let conjPsiAlg : L →ₐ[K] ℂ :=
        { toRingHom := NumberField.ComplexEmbedding.conjugate psi
          commutes' := fun x => RingHom.congr_fun hconjBase x }
      have hAlg : conjPsiAlg = wAlg := by
        apply pb.algHom_ext
        rw [show pb.gen = alpha by
          exact PowerBasis.ofAdjoinEqTop_gen
            (Algebra.IsIntegral.isIntegral alpha) halpha]
        change starRingEnd ℂ (psi alpha) = w.embedding alpha
        rw [hpsiAlpha]
        exact hroot.symm
      exact congrArg AlgHom.toRingHom hAlg
  change (completedMinpolyPlace v alpha halpha G).1 = w
  have hconstructed :
      (completedMinpolyPlace v alpha halpha G).1 =
        InfinitePlace.mk psi := by rfl
  exact hconstructed.trans hplace

end

end Submission.NumberTheory.Milne
