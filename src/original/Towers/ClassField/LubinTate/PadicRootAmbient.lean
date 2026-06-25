import Towers.ClassField.LubinTate.PadicBasic
import Towers.NumberTheory.Locals.AdicCompleteFree
import Mathlib.RingTheory.AdicCompletion.Topology

namespace Towers.CField.LTate
open Polynomial PowerSeries
open Towers.CField.FGroups
noncomputable section

variable (p : ℕ) [Fact p.Prime]
variable (k : Type*) [Field k] [CharP k p] [IsAlgClosed k]

theorem adic_span_singleton
    {R : Type*} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    {J : Ideal R} (hJ : IsAdic J) {x : R}
    (hx : PowerSeries.HasEval x) (hJx : J ≤ Ideal.span {x}) :
    IsAdic (Ideal.span {x}) := by
  let L : Ideal R := Ideal.span {x}
  obtain ⟨d, hd⟩ := hx.exists_pow_mem_of_mem_nhds
    (hJ.hasBasis_nhds_zero.mem_iff.mpr ⟨1, trivial, subset_rfl⟩)
  have hd' : x ^ d ∈ J := by simpa using hd
  have hdp : x ^ (d + 1) ∈ J := by
    rw [pow_succ]
    exact J.mul_mem_right x hd'
  have hpow : L ^ (d + 1) ≤ J := by
    change Ideal.span {x} ^ (d + 1) ≤ J
    rw [Ideal.span_singleton_pow, Ideal.span_singleton_le_iff_mem]
    exact hdp
  rw [isAdic_iff] at hJ ⊢
  constructor
  · intro n
    apply AddSubgroup.isOpen_mono
      (H₁ := (J ^ n).toAddSubgroup) (H₂ := (L ^ n).toAddSubgroup)
    · exact pow_le_pow_left' hJx n
    · exact hJ.1 n
  · intro s hs
    obtain ⟨n, hn⟩ := hJ.2 s hs
    refine ⟨(d + 1) * n, ?_⟩
    rw [pow_mul]
    intro z hz
    exact hn (pow_le_pow_left' hpow n hz)

theorem mapped_reduced_irreducible (n : ℕ) :
    Irreducible ((reducedLubinIterate
      (padicCyclotomicLubin p) n).map
        (padicIntWitt p k)) := by
  let W := WittVector p k
  let rho := padicIntWitt p k
  let fA := padicCyclotomicLubin p
  let fW := fA.map rho
  have hfW0 : fW.coeff 0 = 0 := by
    simp [fW, fA]
  have hfW1 : fW.coeff 1 = (p : W) := by
    change (fA.map rho).coeff 1 = (p : W)
    rw [Polynomial.coeff_map]
    change rho (fA.coeff 1) = (p : W)
    rw [padic_lubin_coeff]
    exact map_natCast rho p
  have hfWred : PowerSeries.map WittVector.constantCoeff
      (PowerSeries.map rho (fA : PowerSeries ℤ_[p])) = PowerSeries.X ^ p := by
    letI : CharP (PowerSeries k) p :=
      charP_of_injective_ringHom (PowerSeries.C_injective (R := k)) p
    simp only [fA, padicCyclotomicLubin, Polynomial.coe_sub,
      Polynomial.coe_pow, Polynomial.coe_add, Polynomial.coe_one,
      Polynomial.coe_X, map_sub, map_pow, map_add, map_one,
      PowerSeries.map_X]
    rw [add_pow_char]
    simp
  have hfWmod : fW.map (Ideal.Quotient.mk (Ideal.span {(p : W)})) =
      Polynomial.X ^ p := by
    let e := WittVector.quotientPEquiv (p := p) (k := k)
    apply Polynomial.map_injective e.toRingHom e.injective
    calc
      (fW.map (Ideal.Quotient.mk (Ideal.span {(p : W)}))).map e.toRingHom =
          fW.map WittVector.constantCoeff := by
        apply Polynomial.ext
        intro i
        simp only [Polynomial.coeff_map]
        exact WittVector.quotientPEquiv_mk (fW.coeff i)
      _ = Polynomial.X ^ p := by
        apply Polynomial.coe_injective
        have hred : PowerSeries.map WittVector.constantCoeff
            (fW : PowerSeries W) = PowerSeries.X ^ p := by
          rw [show (fW : PowerSeries W) =
              PowerSeries.map rho (fA : PowerSeries ℤ_[p]) by
            exact Polynomial.polynomial_map_coe (φ := rho) (f := fA)]
          exact hfWred
        simpa only [Polynomial.polynomial_map_coe, Polynomial.coe_X,
          Polynomial.coe_pow] using hred
      _ = (Polynomial.X ^ p).map e.toRingHom := by simp
  have heis := reduced_eisenstein_uniformizer
    (WittVector.irreducible p)
    ((padic_lubin_monic p).map rho)
    hfW0 hfW1 (by
      rw [(padic_lubin_monic p).natDegree_map]
      exact padic_lubin_degree p)
    (Fact.out : p.Prime).one_lt hfWmod n
  rw [lubin_tate_iterate]
  apply heis.irreducible
    (PrincipalIdealRing.isMaximal_of_irreducible (WittVector.irreducible p)).isPrime
  · exact (reduced_iterate_monic
      ((padic_lubin_monic p).map rho) hfW0 (by
        rw [(padic_lubin_monic p).natDegree_map,
          padic_lubin_degree]
        exact (Fact.out : p.Prime).ne_zero) n).isPrimitive
  · rw [reduced_iterate_degree,
      (padic_lubin_monic p).natDegree_map,
      padic_lubin_degree]
    exact Nat.mul_pos (Nat.sub_pos_of_lt (Fact.out : p.Prime).one_lt)
      (pow_pos (Fact.out : p.Prime).pos n)

set_option maxHeartbeats 2000000 in
-- The dependent quotient-root algebra needs a larger elaboration budget.
theorem mapped_cyclotomic_root (n : ℕ) :
    let W := WittVector p k
    let rho := padicIntWitt p k
    let f := (reducedLubinIterate
      (padicCyclotomicLubin p) n).map rho
    let B := AdjoinRoot f
    let I : Ideal W := Ideal.span {(p : W)}
    let J : Ideal B := I.map (algebraMap W B)
    letI : Fact (Irreducible f) := ⟨mapped_reduced_irreducible p k n⟩
    letI : IsDomain B := AdjoinRoot.isDomain_of_prime
      (mapped_reduced_irreducible p k n).prime
    letI : WithIdeal B := ⟨J⟩
    PowerSeries.HasEval (AdjoinRoot.root f) := by
  dsimp only
  let W := WittVector p k
  let rho := padicIntWitt p k
  let f := (reducedLubinIterate
    (padicCyclotomicLubin p) n).map rho
  let B := AdjoinRoot f
  let I : Ideal W := Ideal.span {(p : W)}
  let J : Ideal B := I.map (algebraMap W B)
  let hfmonic : f.Monic := by
    change ((reducedLubinIterate
      (padicCyclotomicLubin p) n).map rho).Monic
    rw [lubin_tate_iterate]
    apply reduced_iterate_monic
    · exact (padic_lubin_monic p).map rho
    · rw [Polynomial.coeff_map,
        padic_cyclotomic_lubin, map_zero]
    · rw [(padic_lubin_monic p).natDegree_map,
        padic_lubin_degree]
      exact (Fact.out : p.Prime).ne_zero
  letI : Fact (Irreducible f) := ⟨mapped_reduced_irreducible p k n⟩
  letI : IsDomain B := AdjoinRoot.isDomain_of_prime
    (mapped_reduced_irreducible p k n).prime
  letI : Module.Finite W B := hfmonic.finite_adjoinRoot
  letI : Module.Free W B := hfmonic.free_adjoinRoot
  letI : IsAdicComplete I B :=
    Towers.NumberTheory.Milne.adic_complete_free I
  letI : IsAdicComplete J B := by
    exact (IsAdicComplete.map_algebraMap_iff I B).mpr inferInstance
  letI : WithIdeal B := ⟨J⟩
  have hJ : IsAdic J := rfl
  letI : CompleteSpace B := (hJ.isAdicComplete_iff.mp inferInstance).1
  letI : T2Space B := (hJ.isAdicComplete_iff.mp inferInstance).2
  let d := (p - 1) * p ^ n
  let qB : B →+* B ⧸ J := Ideal.Quotient.mk J
  let qW : W →+* W ⧸ I := Ideal.Quotient.mk I
  let qWB : W →+* B ⧸ J := qB.comp (algebraMap W B)
  have hker : ∀ a ∈ I, qWB a = 0 := by
    intro a ha
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    exact Ideal.mem_map_of_mem (algebraMap W B) ha
  let e : W ⧸ I →+* B ⧸ J := Ideal.Quotient.lift I qWB hker
  have hmapW :
      (reducedLubinIterate
        ((padicCyclotomicLubin p).map rho) n).map qW =
          Polynomial.X ^ d := by
    apply reduced_iterate_uniformizer
    · exact (Fact.out : p.Prime).ne_zero
    · let fW := (padicCyclotomicLubin p).map rho
      have hfW0 : fW.coeff 0 = 0 := by simp [fW]
      have hfW1 : fW.coeff 1 = (p : W) := by
        simp [fW, rho]
      have hfWred : PowerSeries.map WittVector.constantCoeff
          (PowerSeries.map rho
            (padicCyclotomicLubin p : PowerSeries ℤ_[p])) =
            PowerSeries.X ^ p := by
        letI : CharP (PowerSeries k) p :=
          charP_of_injective_ringHom (PowerSeries.C_injective (R := k)) p
        simp only [padicCyclotomicLubin, Polynomial.coe_sub,
          Polynomial.coe_pow, Polynomial.coe_add, Polynomial.coe_one,
          Polynomial.coe_X, map_sub, map_pow, map_add, map_one,
          PowerSeries.map_X]
        rw [add_pow_char]
        simp
      apply Polynomial.map_injective
        (WittVector.quotientPEquiv (p := p) (k := k)).toRingHom
        (WittVector.quotientPEquiv (p := p) (k := k)).injective
      calc
        (fW.map qW).map
              (WittVector.quotientPEquiv (p := p) (k := k)).toRingHom =
            fW.map WittVector.constantCoeff := by
          apply Polynomial.ext
          intro i
          simp only [Polynomial.coeff_map]
          exact WittVector.quotientPEquiv_mk (fW.coeff i)
        _ = Polynomial.X ^ p := by
          apply Polynomial.coe_injective
          have hred : PowerSeries.map WittVector.constantCoeff
              (fW : PowerSeries W) = PowerSeries.X ^ p := by
            rw [show (fW : PowerSeries W) = PowerSeries.map rho
                (padicCyclotomicLubin p : PowerSeries ℤ_[p]) by
              exact Polynomial.polynomial_map_coe]
            exact hfWred
          simpa only [Polynomial.polynomial_map_coe, Polynomial.coe_X,
            Polynomial.coe_pow] using hred
        _ = (Polynomial.X ^ p).map
              (WittVector.quotientPEquiv (p := p) (k := k)).toRingHom := by simp
  have hmapB : f.map qWB = Polynomial.X ^ d := by
    change ((reducedLubinIterate
      (padicCyclotomicLubin p) n).map rho).map qWB = _
    rw [lubin_tate_iterate]
    have hcomp : qWB = e.comp qW := by
      ext a
      rfl
    rw [hcomp]
    rw [← Polynomial.map_map, hmapW]
    simp
  have hrootpow : (AdjoinRoot.root f) ^ d ∈ J := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    have hroot := AdjoinRoot.eval₂_root f
    have hqroot := congrArg qB hroot
    rw [Polynomial.hom_eval₂ f (AdjoinRoot.of f) qB
      (AdjoinRoot.root f)] at hqroot
    rw [map_zero] at hqroot
    change Polynomial.eval₂ qWB (qB (AdjoinRoot.root f)) f = 0 at hqroot
    rw [← Polynomial.eval_map] at hqroot
    rw [hmapB] at hqroot
    simpa using hqroot
  rw [PowerSeries.hasEval_def, IsTopologicallyNilpotent]
  apply hJ.hasBasis_nhds_zero.tendsto_right_iff.mpr
  intro m _
  rw [Filter.eventually_atTop]
  refine ⟨d * m, fun r hr ↦ ?_⟩
  have hdpos : 0 < d := Nat.mul_pos
    (Nat.sub_pos_of_lt (Fact.out : p.Prime).one_lt)
    (pow_pos (Fact.out : p.Prime).pos n)
  have hbase : (AdjoinRoot.root f) ^ (d * m) ∈ J ^ m := by
    rw [pow_mul]
    exact Ideal.pow_mem_pow hrootpow m
  exact (J ^ m).pow_mem_of_pow_mem hbase hr

set_option maxHeartbeats 2000000 in
-- Adic completeness of the dependent root algebra requires extra reduction.
theorem mapped_cyclotomic_adic (n : ℕ) :
    let W := WittVector p k
    let rho := padicIntWitt p k
    let f := (reducedLubinIterate
      (padicCyclotomicLubin p) n).map rho
    let B := AdjoinRoot f
    let I : Ideal W := Ideal.span {(p : W)}
    let J : Ideal B := I.map (algebraMap W B)
    letI : Fact (Irreducible f) := ⟨mapped_reduced_irreducible p k n⟩
    letI : IsDomain B := AdjoinRoot.isDomain_of_prime
      (mapped_reduced_irreducible p k n).prime
    letI : WithIdeal B := ⟨J⟩
    IsAdic (Ideal.span {AdjoinRoot.root f}) := by
  dsimp only
  let W := WittVector p k
  let rho := padicIntWitt p k
  let f := (reducedLubinIterate
    (padicCyclotomicLubin p) n).map rho
  let B := AdjoinRoot f
  let I : Ideal W := Ideal.span {(p : W)}
  let J : Ideal B := I.map (algebraMap W B)
  let hfmonic : f.Monic := by
    change ((reducedLubinIterate
      (padicCyclotomicLubin p) n).map rho).Monic
    rw [lubin_tate_iterate]
    apply reduced_iterate_monic
    · exact (padic_lubin_monic p).map rho
    · rw [Polynomial.coeff_map,
        padic_cyclotomic_lubin, map_zero]
    · rw [(padic_lubin_monic p).natDegree_map,
        padic_lubin_degree]
      exact (Fact.out : p.Prime).ne_zero
  letI : Fact (Irreducible f) := ⟨mapped_reduced_irreducible p k n⟩
  letI : IsDomain B := AdjoinRoot.isDomain_of_prime
    (mapped_reduced_irreducible p k n).prime
  letI : Module.Finite W B := hfmonic.finite_adjoinRoot
  letI : Module.Free W B := hfmonic.free_adjoinRoot
  letI : IsAdicComplete I B :=
    Towers.NumberTheory.Milne.adic_complete_free I
  letI : IsAdicComplete J B := by
    exact (IsAdicComplete.map_algebraMap_iff I B).mpr inferInstance
  letI : WithIdeal B := ⟨J⟩
  have hJ : IsAdic J := rfl
  letI : CompleteSpace B := (hJ.isAdicComplete_iff.mp inferInstance).1
  letI : T2Space B := (hJ.isAdicComplete_iff.mp inferInstance).2
  have hx : PowerSeries.HasEval (AdjoinRoot.root f) :=
    mapped_cyclotomic_root p k n
  have hf0 : f.coeff 0 = rho (p : ℤ_[p]) := by
    change ((reducedLubinIterate
      (padicCyclotomicLubin p) n).map rho).coeff 0 = rho (p : ℤ_[p])
    rw [Polynomial.coeff_map, reduced_iterate_coeff _
      (padic_cyclotomic_lubin p),
      padic_lubin_coeff]
  have hdiv : AdjoinRoot.root f ∣ algebraMap W B (rho (p : ℤ_[p])) := by
    have hroot : (f.map (algebraMap W B)).IsRoot (AdjoinRoot.root f) :=
      AdjoinRoot.isRoot_root f
    simpa [hf0] using hroot.dvd_coeff_zero
  have hJx : J ≤ Ideal.span {AdjoinRoot.root f} := by
    change (Ideal.span {(p : W)}).map (algebraMap W B) ≤
      Ideal.span {AdjoinRoot.root f}
    rw [Ideal.map_span, Set.image_singleton,
      Ideal.span_singleton_le_iff_mem, Ideal.mem_span_singleton]
    simpa only [map_natCast, map_natCast] using hdiv
  exact adic_span_singleton hJ hx hJx

/-! ## The bundled ambient ring -/

/-- The cyclotomic reduced-level polynomial after extension from `Z_p` to
the completed maximal-unramified Witt ring. -/
def padicWittReduced (n : ℕ) :
    (WittVector p k)[X] :=
  (reducedLubinIterate
    (padicCyclotomicLubin p) n).map (padicIntWitt p k)

/-- The finite integral Witt algebra obtained by adjoining the distinguished
cyclotomic torsion root. -/
abbrev PadicWittRing (n : ℕ) :=
  AdjoinRoot (padicWittReduced p k n)

instance reduced_irreducible_fact (n : ℕ) :
    Fact (Irreducible (padicWittReduced p k n)) :=
  ⟨mapped_reduced_irreducible p k n⟩

instance padic_witt_domain (n : ℕ) :
    IsDomain (PadicWittRing p k n) :=
  AdjoinRoot.isDomain_of_prime
    (mapped_reduced_irreducible p k n).prime

omit [IsAlgClosed k] in
theorem witt_reduced_monic (n : ℕ) :
    (padicWittReduced p k n).Monic := by
  rw [padicWittReduced,
    lubin_tate_iterate]
  apply reduced_iterate_monic
  · exact (padic_lubin_monic p).map
      (padicIntWitt p k)
  · rw [Polynomial.coeff_map,
      padic_cyclotomic_lubin, map_zero]
  · rw [(padic_lubin_monic p).natDegree_map,
      padic_lubin_degree]
    exact (Fact.out : p.Prime).ne_zero

instance padic_witt_module (n : ℕ) :
    Module.Finite (WittVector p k) (PadicWittRing p k n) :=
  (witt_reduced_monic p k n).finite_adjoinRoot

instance padic_module_free (n : ℕ) :
    Module.Free (WittVector p k) (PadicWittRing p k n) :=
  (witt_reduced_monic p k n).free_adjoinRoot

/-- The ideal defining the inherited `p`-adic topology on the finite root
algebra. -/
def padicWittIdeal (n : ℕ) :
    Ideal (PadicWittRing p k n) :=
  (Ideal.span {(p : WittVector p k)}).map
    (algebraMap (WittVector p k) (PadicWittRing p k n))

instance padic_witt_ideal (n : ℕ) :
    WithIdeal (PadicWittRing p k n) :=
  ⟨padicWittIdeal p k n⟩

instance padic_complete_module (n : ℕ) :
    IsAdicComplete (Ideal.span {(p : WittVector p k)})
      (PadicWittRing p k n) :=
  Towers.NumberTheory.Milne.adic_complete_free _

instance padic_witt_complete (n : ℕ) :
    IsAdicComplete (padicWittIdeal p k n)
      (PadicWittRing p k n) := by
  exact (IsAdicComplete.map_algebraMap_iff
    (Ideal.span {(p : WittVector p k)})
    (PadicWittRing p k n)).mpr inferInstance

omit [IsAlgClosed k] in
theorem padic_witt_adic (n : ℕ) :
    IsAdic (padicWittIdeal p k n) :=
  rfl

instance padic_complete_space (n : ℕ) :
    CompleteSpace (PadicWittRing p k n) :=
  ((padic_witt_adic p k n).isAdicComplete_iff.mp
    inferInstance).1

instance padic_t_space (n : ℕ) :
    T2Space (PadicWittRing p k n) :=
  ((padic_witt_adic p k n).isAdicComplete_iff.mp
    inferInstance).2

/-- The distinguished cyclotomic torsion root in the Witt algebra. -/
def cyclotomicWittRoot (n : ℕ) :
    PadicWittRing p k n :=
  AdjoinRoot.root (padicWittReduced p k n)

/-- The root is a valid point for convergent power-series evaluation. -/
theorem padic_cyclotomic_eval (n : ℕ) :
    PowerSeries.HasEval (cyclotomicWittRoot p k n) :=
  mapped_cyclotomic_root p k n

/-- The root ideal defines the same topology as the inherited `p`-adic
topology. -/
theorem padic_cyclotomic_adic (n : ℕ) :
    IsAdic (Ideal.span {cyclotomicWittRoot p k n}) :=
  mapped_cyclotomic_adic p k n

end
end Towers.CField.LTate
