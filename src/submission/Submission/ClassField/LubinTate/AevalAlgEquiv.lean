import Submission.ClassField.FormalGroups.FormalGroupEvaluation

/-!
# Class Field Theory, Chapter I, Lemma 3.5

The formal power-series core of Galois equivariance.  A continuous algebra
automorphism commutes with evaluation of every convergent multivariate power
series whose coefficients lie in the fixed base ring.

The local-field statement follows once the Galois automorphism and elements
of the maximal ideal are placed in a complete linearly topologized algebra;
that ring-of-integers topology bridge is not yet packaged in this project.
-/

namespace Submission.CField.LTate

noncomputable section

/-- Continuous base-algebra automorphisms commute with convergent evaluation
of multivariate power series. -/
theorem aeval_algEquiv
    {K S sigma : Type*}
    [CommRing K] [UniformSpace K] [IsTopologicalSemiring K]
    [IsUniformAddGroup K]
    [CommRing S] [UniformSpace S] [IsUniformAddGroup S]
    [CompleteSpace S] [T2Space S] [IsTopologicalRing S]
    [IsLinearTopology S S] [Algebra K S] [ContinuousSMul K S]
    (tau : S ≃ₐ[K] S) (htau : Continuous tau)
    (a : sigma → S) (ha : MvPowerSeries.HasEval a)
    (F : MvPowerSeries sigma K) :
    tau (MvPowerSeries.aeval ha F) =
      MvPowerSeries.aeval (ha.map (φ := tau.toAlgHom.toRingHom) htau) F := by
  exact DFunLike.congr_fun
    (MvPowerSeries.comp_aeval (R := K) ha
      (ε := tau.toAlgHom) htau) F

/-- Lemma 3.5 in direct evaluation notation: applying a continuous
base-algebra automorphism after evaluating a convergent power series is the
same as applying it to every input before evaluation. -/
theorem eval₂_algEquiv
    {K S sigma : Type*}
    [CommRing K] [UniformSpace K] [IsTopologicalSemiring K]
    [IsUniformAddGroup K]
    [CommRing S] [UniformSpace S] [IsUniformAddGroup S]
    [CompleteSpace S] [T2Space S] [IsTopologicalRing S]
    [IsLinearTopology S S] [Algebra K S] [ContinuousSMul K S]
    (tau : S ≃ₐ[K] S) (htau : Continuous tau)
    (a : sigma → S) (ha : MvPowerSeries.HasEval a)
    (F : MvPowerSeries sigma K) :
    tau (MvPowerSeries.eval₂ (algebraMap K S) a F) =
      MvPowerSeries.eval₂ (algebraMap K S) (fun i ↦ tau (a i)) F := by
  simpa only [MvPowerSeries.coe_aeval] using
    aeval_algEquiv tau htau a ha F

/-- Lemma 3.5 for a complete adic target: membership of the finitely many
inputs in the defining ideal supplies the convergence hypothesis. -/
theorem eval₂_algEquiv_of_forall_mem_adic
    {K S sigma : Type*} [Finite sigma]
    [CommRing K] [UniformSpace K] [IsTopologicalSemiring K]
    [IsUniformAddGroup K]
    [CommRing S] [UniformSpace S] [IsUniformAddGroup S]
    [CompleteSpace S] [T2Space S] [IsTopologicalRing S]
    [Algebra K S] [ContinuousSMul K S]
    {I : Ideal S} (hI : IsAdic I)
    (tau : S ≃ₐ[K] S) (htau : Continuous tau)
    (a : sigma → S) (ha : ∀ i, a i ∈ I)
    (F : MvPowerSeries sigma K) :
    tau (MvPowerSeries.eval₂ (algebraMap K S) a F) =
      MvPowerSeries.eval₂ (algebraMap K S) (fun i ↦ tau (a i)) F := by
  letI : IsLinearTopology S S :=
    IsLinearTopology.mk_of_hasBasis S hI.hasBasis_nhds_zero
  exact eval₂_algEquiv tau htau a
    (FGroups.mv_forall_adic hI a ha) F

/-- A continuous algebra homomorphism between two complete linearly
topologized algebras commutes with every convergent power-series evaluation. -/
theorem eval₂_algHom
    {K S T sigma : Type*}
    [CommRing K] [UniformSpace K] [IsTopologicalSemiring K]
    [IsUniformAddGroup K]
    [CommRing S] [UniformSpace S] [IsUniformAddGroup S]
    [CompleteSpace S] [T2Space S] [IsTopologicalRing S]
    [IsLinearTopology S S] [Algebra K S] [ContinuousSMul K S]
    [CommRing T] [UniformSpace T] [IsUniformAddGroup T]
    [CompleteSpace T] [T2Space T] [IsTopologicalRing T]
    [IsLinearTopology T T] [Algebra K T] [ContinuousSMul K T]
    (tau : S →ₐ[K] T) (htau : Continuous tau)
    (a : sigma → S) (ha : MvPowerSeries.HasEval a)
    (F : MvPowerSeries sigma K) :
    tau (MvPowerSeries.eval₂ (algebraMap K S) a F) =
      MvPowerSeries.eval₂ (algebraMap K T) (fun i ↦ tau (a i)) F := by
  simpa only [MvPowerSeries.coe_aeval, AlgHom.comp_apply] using DFunLike.congr_fun
    (MvPowerSeries.comp_aeval (R := K) ha (ε := tau) htau) F

/-- Adic convergence supplies the hypotheses for functorial evaluation along
a continuous algebra homomorphism into another complete adic ring. -/
theorem eval₂_algHom_of_forall_mem_adic
    {K S T sigma : Type*} [Finite sigma]
    [CommRing K] [UniformSpace K] [IsTopologicalSemiring K]
    [IsUniformAddGroup K]
    [CommRing S] [UniformSpace S] [IsUniformAddGroup S]
    [CompleteSpace S] [T2Space S] [IsTopologicalRing S]
    [Algebra K S] [ContinuousSMul K S]
    [CommRing T] [UniformSpace T] [IsUniformAddGroup T]
    [CompleteSpace T] [T2Space T] [IsTopologicalRing T]
    [Algebra K T] [ContinuousSMul K T]
    {I : Ideal S} (hI : IsAdic I) {J : Ideal T} (hJ : IsAdic J)
    (tau : S →ₐ[K] T) (htau : Continuous tau)
    (a : sigma → S) (ha : ∀ i, a i ∈ I)
    (F : MvPowerSeries sigma K) :
    tau (MvPowerSeries.eval₂ (algebraMap K S) a F) =
      MvPowerSeries.eval₂ (algebraMap K T) (fun i ↦ tau (a i)) F := by
  letI : IsLinearTopology S S :=
    IsLinearTopology.mk_of_hasBasis S hI.hasBasis_nhds_zero
  letI : IsLinearTopology T T :=
    IsLinearTopology.mk_of_hasBasis T hJ.hasBasis_nhds_zero
  exact eval₂_algHom tau htau a
    (FGroups.mv_forall_adic hI a ha) F

/-- Evaluating a series after extending its coefficients along the algebra
map agrees with evaluating the original series through that algebra map. -/
theorem eval₂_map_algebraMap_of_forall_mem_adic
    {K S sigma : Type*} [Finite sigma]
    [CommRing K] [UniformSpace K] [IsTopologicalSemiring K]
    [IsUniformAddGroup K]
    [CommRing S] [UniformSpace S] [IsUniformAddGroup S]
    [CompleteSpace S] [T2Space S] [IsTopologicalRing S]
    [Algebra K S] [ContinuousSMul K S]
    {I : Ideal S} (hI : IsAdic I)
    (a : sigma → S) (ha : ∀ i, a i ∈ I)
    (F : MvPowerSeries sigma K) :
    MvPowerSeries.eval₂ (RingHom.id S) a
        (MvPowerSeries.map (algebraMap K S) F) =
      MvPowerSeries.eval₂ (algebraMap K S) a F := by
  letI : IsLinearTopology S S :=
    IsLinearTopology.mk_of_hasBasis S hI.hasBasis_nhds_zero
  have hEval := FGroups.mv_forall_adic hI a ha
  rw [MvPowerSeries.eval₂_eq_tsum continuous_id hEval,
    MvPowerSeries.eval₂_eq_tsum (continuous_algebraMap K S) hEval]
  apply tsum_congr
  intro d
  rw [MvPowerSeries.coeff_map, RingHom.id_apply]

/-- Evaluation of an adically convergent coefficient-extended series is
natural under a continuous ring homomorphism that carries the source ideal
into the target ideal. -/
theorem eval₂_map_ringHom_of_forall_mem_adic
    {K S T sigma : Type*} [Finite sigma]
    [CommRing K]
    [CommRing S] [UniformSpace S] [IsUniformAddGroup S]
    [CompleteSpace S] [T2Space S] [IsTopologicalRing S]
    [CommRing T] [UniformSpace T] [IsUniformAddGroup T]
    [CompleteSpace T] [T2Space T] [IsTopologicalRing T]
    {I : Ideal S} (hI : IsAdic I)
    {J : Ideal T} (hJ : IsAdic J)
    (rho : K →+* S) (phi : S →+* T) (hphi : Continuous phi)
    (hIJ : ∀ x : S, x ∈ I → phi x ∈ J)
    (a : sigma → S) (ha : ∀ i, a i ∈ I)
    (F : MvPowerSeries sigma K) :
    phi (MvPowerSeries.eval₂ (RingHom.id S) a
        (MvPowerSeries.map rho F)) =
      MvPowerSeries.eval₂ (RingHom.id T) (fun i ↦ phi (a i))
        (MvPowerSeries.map (phi.comp rho) F) := by
  letI : IsLinearTopology S S :=
    IsLinearTopology.mk_of_hasBasis S hI.hasBasis_nhds_zero
  letI : IsLinearTopology T T :=
    IsLinearTopology.mk_of_hasBasis T hJ.hasBasis_nhds_zero
  have haS := FGroups.mv_forall_adic hI a ha
  have haT := FGroups.mv_forall_adic hJ
    (fun i ↦ phi (a i)) (fun i ↦ hIJ (a i) (ha i))
  have hsum := MvPowerSeries.hasSum_eval₂
    (φ := RingHom.id S) (a := a) continuous_id haS
    (MvPowerSeries.map rho F)
  rw [← (hsum.map phi hphi).tsum_eq,
    MvPowerSeries.eval₂_eq_tsum continuous_id haT]
  apply tsum_congr
  intro d
  simp only [Function.comp_apply, map_mul, map_finsuppProd, map_pow,
    MvPowerSeries.coeff_map, RingHom.id_apply, RingHom.comp_apply]

/-- A continuous base-algebra automorphism preserving the ideal of
definition commutes with evaluation of every coefficient-extended series on
that ideal. -/
theorem eval₂_map_algEquiv_of_forall_mem_adic
    {K S sigma : Type*} [Finite sigma]
    [CommRing K] [UniformSpace K] [IsTopologicalSemiring K]
    [IsUniformAddGroup K]
    [CommRing S] [UniformSpace S] [IsUniformAddGroup S]
    [CompleteSpace S] [T2Space S] [IsTopologicalRing S]
    [Algebra K S] [ContinuousSMul K S]
    {I : Ideal S} (hI : IsAdic I)
    (tau : S ≃ₐ[K] S) (htau : Continuous tau)
    (hI_tau : ∀ x : S, x ∈ I → tau x ∈ I)
    (a : sigma → S) (ha : ∀ i, a i ∈ I)
    (F : MvPowerSeries sigma K) :
    tau (MvPowerSeries.eval₂ (RingHom.id S) a
        (MvPowerSeries.map (algebraMap K S) F)) =
      MvPowerSeries.eval₂ (RingHom.id S) (fun i ↦ tau (a i))
        (MvPowerSeries.map (algebraMap K S) F) := by
  calc
    tau (MvPowerSeries.eval₂ (RingHom.id S) a
        (MvPowerSeries.map (algebraMap K S) F)) =
      tau (MvPowerSeries.eval₂ (algebraMap K S) a F) := by
        rw [eval₂_map_algebraMap_of_forall_mem_adic hI a ha F]
    _ = MvPowerSeries.eval₂ (algebraMap K S) (fun i ↦ tau (a i)) F :=
      eval₂_algEquiv_of_forall_mem_adic hI tau htau a ha F
    _ = MvPowerSeries.eval₂ (RingHom.id S) (fun i ↦ tau (a i))
        (MvPowerSeries.map (algebraMap K S) F) := by
      rw [eval₂_map_algebraMap_of_forall_mem_adic hI
        (fun i ↦ tau (a i)) (fun i ↦ hI_tau (a i) (ha i)) F]

/-- Cross-target form of Lemma 3.5: a continuous algebra homomorphism that
maps one ideal of definition into another commutes with evaluation after
coefficient extension on both sides. -/
theorem eval₂_map_algHom_of_forall_mem_adic
    {K S T sigma : Type*} [Finite sigma]
    [CommRing K] [UniformSpace K] [IsTopologicalSemiring K]
    [IsUniformAddGroup K]
    [CommRing S] [UniformSpace S] [IsUniformAddGroup S]
    [CompleteSpace S] [T2Space S] [IsTopologicalRing S]
    [Algebra K S] [ContinuousSMul K S]
    [CommRing T] [UniformSpace T] [IsUniformAddGroup T]
    [CompleteSpace T] [T2Space T] [IsTopologicalRing T]
    [Algebra K T] [ContinuousSMul K T]
    {I : Ideal S} (hI : IsAdic I) {J : Ideal T} (hJ : IsAdic J)
    (tau : S →ₐ[K] T) (htau : Continuous tau)
    (hIJ : ∀ x : S, x ∈ I → tau x ∈ J)
    (a : sigma → S) (ha : ∀ i, a i ∈ I)
    (F : MvPowerSeries sigma K) :
    tau (MvPowerSeries.eval₂ (RingHom.id S) a
        (MvPowerSeries.map (algebraMap K S) F)) =
      MvPowerSeries.eval₂ (RingHom.id T) (fun i ↦ tau (a i))
        (MvPowerSeries.map (algebraMap K T) F) := by
  calc
    tau (MvPowerSeries.eval₂ (RingHom.id S) a
        (MvPowerSeries.map (algebraMap K S) F)) =
      tau (MvPowerSeries.eval₂ (algebraMap K S) a F) := by
        rw [eval₂_map_algebraMap_of_forall_mem_adic hI a ha F]
    _ = MvPowerSeries.eval₂ (algebraMap K T) (fun i ↦ tau (a i)) F :=
      eval₂_algHom_of_forall_mem_adic hI hJ tau htau a ha F
    _ = MvPowerSeries.eval₂ (RingHom.id T) (fun i ↦ tau (a i))
        (MvPowerSeries.map (algebraMap K T) F) := by
      rw [eval₂_map_algebraMap_of_forall_mem_adic hJ
        (fun i ↦ tau (a i)) (fun i ↦ hIJ (a i) (ha i)) F]

end

end Submission.CField.LTate
