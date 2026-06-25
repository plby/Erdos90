import Submission.ClassField.HasseNorm.RepresentationBaseChange
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.LinearAlgebra.QuadraticForm.AlgClosed
import Mathlib.LinearAlgebra.TensorProduct.Basis

/-! # Chapter VIII, Section 3, Proposition 3.9 and Corollaries 3.10--3.11 -/

namespace Submission.CField.HNorm

open scoped TensorProduct
open scoped Topology
open NumberField
open Submission.CField.Ideles

noncomputable section
universe u

/-- **Proposition VIII.3.9.** A nondegenerate four-dimensional form over a
nonarchimedean local field represents every nonzero scalar. -/
def FourDimensionalNonzero : Prop :=
  ∀ (K V : Type u) [NontriviallyNormedField K] [IsUltrametricDist K]
    [ValuativeRel K] [IsNonarchimedeanLocalField K] [NeZero (2 : K)]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (Q : QuadraticForm K V),
    Module.finrank K V = 4 → Q.Nondegenerate →
      ∀ c : K, c ≠ 0 → Represents Q c

/-- **Corollary VIII.3.10.** -/
def HighDimensionalIsotropic : Prop :=
  ∀ (K V : Type u) [NontriviallyNormedField K] [IsUltrametricDist K]
    [ValuativeRel K] [IsNonarchimedeanLocalField K] [NeZero (2 : K)]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (Q : QuadraticForm K V),
    5 ≤ Module.finrank K V → Q.Nondegenerate → Represents Q 0

theorem local_quadratic_consequences
    (h39 : FourDimensionalNonzero.{u}) :
    HighDimensionalIsotropic.{u} := by
  intro K V _ _ _ _ _ _ _ _ Q hdim hQ
  letI : Invertible (2 : K) := invertibleOfNonzero (NeZero.ne _)
  let n := Module.finrank K V
  have hfour : 4 ≤ n := by omega
  have hfour_lt : 4 < n := by omega
  let e : Fin 4 → Fin n := fun i ↦ ⟨i, lt_of_lt_of_le i.isLt hfour⟩
  have he : Function.Injective e := by
    intro i j hij
    apply Fin.ext
    exact congrArg (fun z : Fin n ↦ z.val) hij
  obtain ⟨B, hB⟩ :=
    LinearMap.BilinForm.exists_orthogonal_basis
      (B := Q.polarBilin) ⟨by
        intro x y
        simp only [RingHom.id_apply, QuadraticMap.polarBilin_apply_apply]
        exact QuadraticMap.polar_comm Q x y⟩
  let v : Fin 4 → V := fun i ↦ B (e i)
  have hv : LinearIndependent K v := B.linearIndependent.comp e he
  let U : Submodule K V := Submodule.span K (Set.range v)
  let BU : Module.Basis (Fin 4) K U := Module.Basis.span hv
  have hUdim : Module.finrank K U = 4 := by
    rw [Module.finrank_eq_card_basis BU]
    exact Fintype.card_fin 4
  have hpolar : Q.polarBilin.Nondegenerate :=
    QuadraticMap.nondegenerate_polar_iff.mpr hQ
  have hrestrictPolar (x y : U) :
      (Q.restrict U).polarBilin x y = Q.polarBilin (x : V) (y : V) := by
    simp only [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar,
      QuadraticMap.restrict_apply, Submodule.coe_add]
  have hBUcoe (i : Fin 4) : ((BU i : U) : V) = v i := by
    simp [BU, U, v]
  have hBUortho : (Q.restrict U).polarBilin.IsOrthoᵢ BU := by
    intro i j hij
    change (Q.restrict U).polarBilin (BU i) (BU j) = 0
    rw [hrestrictPolar, hBUcoe, hBUcoe]
    exact hB (fun heq ↦ hij (he heq))
  have hBUself : ∀ i, ¬ (Q.restrict U).polarBilin.IsOrtho (BU i) (BU i) := by
    intro i hi
    apply hB.not_isOrtho_basis_self_of_separatingLeft hpolar.1 (e i)
    rw [LinearMap.IsOrtho, hrestrictPolar, hBUcoe] at hi
    exact hi
  have hUQ : (Q.restrict U).Nondegenerate :=
    QuadraticMap.nondegenerate_polar_iff.mp
      (hBUortho.nondegenerate_of_not_isOrtho_basis_self BU hBUself)
  let i4 : Fin n := ⟨4, hfour_lt⟩
  let b : V := B i4
  have hbSelf : ¬ Q.polarBilin.IsOrtho b b :=
    hB.not_isOrtho_basis_self_of_separatingLeft hpolar.1 i4
  have hbQ : Q b ≠ 0 := by
    intro hb
    apply hbSelf
    rw [LinearMap.IsOrtho, QuadraticMap.polarBilin_apply_apply,
      QuadraticMap.polar_self, hb]
    simp
  have hneg : -Q b ≠ 0 := neg_ne_zero.mpr hbQ
  obtain ⟨x, hx, hQx⟩ := h39 K U (Q.restrict U) hUdim hUQ (-Q b) hneg
  have hxb : Q.polarBilin (x : V) b = 0 := by
    refine Submodule.span_induction
      (p := fun y _ ↦ Q.polarBilin y b = 0) ?_ ?_ ?_ ?_ x.property
    · rintro y ⟨i, rfl⟩
      exact hB (by
        intro hei
        have hval := congrArg Fin.val hei
        exact (Nat.ne_of_lt i.isLt) (by simpa [e, i4] using hval))
    · simp
    · intro y z _ _ hy hz
      simp [hy, hz]
    · intro c y _ hy
      simp [hy]
  refine ⟨(x : V) + b, ?_, ?_⟩
  · intro hzero
    have hxb' : Q.polarBilin (-b) b = 0 := by
      rw [← eq_neg_of_add_eq_zero_left hzero]
      exact hxb
    apply hbSelf
    simpa [LinearMap.IsOrtho] using hxb'
  · change Q (x : V) = -Q b at hQx
    have hxbPolar : QuadraticMap.polar Q (x : V) b = 0 := by
      simpa only [QuadraticMap.polarBilin_apply_apply] using hxb
    rw [QuadraticMap.map_add Q, hxbPolar, hQx]
    simp

/-- Nondegeneracy of a quadratic form is preserved by extension of scalars
between fields.  Mathlib does not currently package this consequence of
`QuadraticForm.polarBilin_baseChange`, so we prove it by base-changing an
orthogonal basis. -/
theorem quadratic_change_nondegenerate
    {K F V : Type u} [Field K] [Field F] [Algebra K F]
    [Invertible (2 : K)] [NeZero (2 : F)]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (Q : QuadraticForm K V) (hQ : Q.Nondegenerate) :
    (Q.baseChange F).Nondegenerate := by
  letI : Invertible (2 : F) := invertibleOfNonzero (NeZero.ne _)
  obtain ⟨B, hB⟩ := LinearMap.BilinForm.exists_orthogonal_basis
    (B := Q.polarBilin) ⟨fun x y ↦ QuadraticMap.polar_comm Q x y⟩
  have hpolar : Q.polarBilin.Nondegenerate :=
    QuadraticMap.nondegenerate_polar_iff.mpr hQ
  let BF : Module.Basis (Fin (Module.finrank K V)) F (F ⊗[K] V) :=
    B.baseChange F
  have hBFortho : (Q.baseChange F).polarBilin.IsOrthoᵢ BF := by
    intro i j hij
    change (Q.baseChange F).polarBilin (BF i) (BF j) = 0
    rw [show BF i = 1 ⊗ₜ[K] B i by simp [BF],
      show BF j = 1 ⊗ₜ[K] B j by simp [BF],
      QuadraticForm.polarBilin_baseChange,
      LinearMap.BilinForm.baseChange_tmul]
    rw [hB hij]
    simp
  have hBFself : ∀ i, ¬(Q.baseChange F).polarBilin.IsOrtho (BF i) (BF i) := by
    intro i hi
    have hsource : ¬Q.polarBilin.IsOrtho (B i) (B i) :=
      hB.not_isOrtho_basis_self_of_separatingLeft hpolar.1 i
    apply hsource
    rw [LinearMap.IsOrtho]
    rw [LinearMap.IsOrtho] at hi
    change (Q.baseChange F).polarBilin (BF i) (BF i) = 0 at hi
    rw [show BF i = 1 ⊗ₜ[K] B i by simp [BF],
      QuadraticForm.polarBilin_baseChange,
      LinearMap.BilinForm.baseChange_tmul] at hi
    exact (algebraMap K F).injective (by simpa using hi)
  apply QuadraticMap.nondegenerate_polar_iff.mp
  exact hBFortho.nondegenerate_of_not_isOrtho_basis_self BF hBFself

private theorem weighted_squares_represents
    {F : Type u} [Field F] {N : ℕ} (hN : 2 ≤ N)
    (w : Fin N → F) (hsqrt : ∀ x : F, ∃ z : F, x = z * z) :
    Represents (QuadraticMap.weightedSumSquares F w) 0 := by
  let i0 : Fin N := ⟨0, by omega⟩
  let i1 : Fin N := ⟨1, by omega⟩
  have hi : i0 ≠ i1 := by
    intro hi
    have := congrArg Fin.val hi
    simp [i0, i1] at this
  by_cases h0 : w i0 = 0
  · let y : Fin N → F := Pi.single i0 1
    refine ⟨y, ?_, ?_⟩
    · intro hy
      have := congrFun hy i0
      simp [y] at this
    · rw [QuadraticMap.weightedSumSquares_apply]
      simp [y, Pi.single_apply, h0]
  · by_cases h1 : w i1 = 0
    · let y : Fin N → F := Pi.single i1 1
      refine ⟨y, ?_, ?_⟩
      · intro hy
        have := congrFun hy i1
        simp [y] at this
      · rw [QuadraticMap.weightedSumSquares_apply]
        simp [y, Pi.single_apply, h1]
    · obtain ⟨z, hz⟩ := hsqrt (-w i0 / w i1)
      let y : Fin N → F := Pi.single i0 1 + Pi.single i1 z
      refine ⟨y, ?_, ?_⟩
      · intro hy
        have := congrFun hy i0
        simp [y, hi] at this
      · have hcalc : w i0 + w i1 * (z * z) = 0 := by
          rw [← hz]
          field_simp
          simp
        rw [QuadraticMap.weightedSumSquares_apply]
        change (∑ x, w x * (y x * y x)) = 0
        let f : Fin N → F := fun x ↦ w x * (y x * y x)
        have hsum : (∑ x, f x) = f i0 + f i1 := by
          calc
            (∑ x, f x) = ∑ x ∈ ({i0, i1} : Finset (Fin N)), f x := by
              symm
              apply Finset.sum_subset (by simp)
              intro x _ hx
              have hx0 : x ≠ i0 := by
                intro h
                apply hx
                simp [h]
              have hx1 : x ≠ i1 := by
                intro h
                apply hx
                simp [h]
              simp [f, y, Pi.single_apply, hx0, hx1]
            _ = f i0 + f i1 := by simp [hi]
        rw [show (∑ x, w x * (y x * y x)) = ∑ x, f x by rfl, hsum]
        simpa [f, y, Pi.single_apply, hi, hi.symm, pow_two] using hcalc

/-- The nonreal local assertions in Corollary 3.11 are consequences, not an
additional bridge: finite places use Corollary 3.10 after scalar extension;
complex places use algebraic closure and the classification by sums of
squares. -/
theorem nonrealPlaces
    (h310 : HighDimensionalIsotropic.{u}) :
    ∀ (K V : Type u) [Field K] [NumberField K]
      [AddCommGroup V] [Module K V] [FiniteDimensional K V]
      (Q : QuadraticForm K V),
      5 ≤ Module.finrank K V → Q.Nondegenerate →
        ∀ v : NumberFieldPlace K,
          (match v with | .inl _ => True | .inr w => InfinitePlace.IsComplex w) →
          Represents (quadraticFormPlace K V Q v) 0 := by
  intro K V _ _ _ _ _ Q hdim hQ v hv
  letI : Invertible (2 : K) := invertibleOfNonzero (by norm_num)
  have htwo : (2 : placeCompletion K v) ≠ 0 := by
    intro hzero
    have hK : (2 : K) ≠ 0 := by norm_num
    apply hK
    apply (algebraMap K (placeCompletion K v)).injective
    simpa only [map_ofNat, map_zero] using hzero
  cases v with
  | inl P =>
      letI : Algebra K (P.adicCompletion K) :=
        (FinitePlace.embedding P).toAlgebra
      have htwoP : (2 : P.adicCompletion K) ≠ 0 := by
        simpa only [placeCompletion] using htwo
      letI : NeZero (2 : P.adicCompletion K) := ⟨htwoP⟩
      let hnormed : NormedField (P.adicCompletion K) :=
        { (inferInstance : NormedField (P.adicCompletion K)) with
          toField := (inferInstance : Field (P.adicCompletion K)) }
      let hnontriviallyNormed : NontriviallyNormedField (P.adicCompletion K) :=
        Valued.toNontriviallyNormedField (P.adicCompletion K)
          (WithZero (Multiplicative ℤ))
      have hnormWitness : ∃ x : P.adicCompletion K, x ≠ 0 ∧ ‖x‖ ≠ 1 := by
        letI := hnontriviallyNormed
        obtain ⟨x, hxpos, hxlt⟩ :=
          NormedField.exists_norm_lt_one (P.adicCompletion K)
        exact ⟨x, norm_pos_iff.mp hxpos, ne_of_lt hxlt⟩
      letI : NontriviallyNormedField (P.adicCompletion K) :=
        @NontriviallyNormedField.ofNormNeOne (P.adicCompletion K)
          hnormed hnormWitness
      letI : IsUltrametricDist (P.adicCompletion K) := by infer_instance
      letI : ValuativeRel (P.adicCompletion K) :=
        ValuativeRel.ofValuation
          (NormedField.valuation (K := P.adicCompletion K))
      letI : Valuation.Compatible
          (NormedField.valuation (K := P.adicCompletion K)) :=
        Valuation.Compatible.ofValuation
          (NormedField.valuation (K := P.adicCompletion K))
      haveI htop : IsValuativeTopology (P.adicCompletion K) := by
        apply IsValuativeTopology.of_zero
        intro s
        rw [show s ∈ 𝓝 (0 : P.adicCompletion K) ↔
            ∃ γ : (MonoidWithZeroHom.ValueGroup₀
                (NormedField.valuation (K := P.adicCompletion K)))ˣ,
              {x | (NormedField.valuation
                (K := P.adicCompletion K)).restrict x < γ.1} ⊆ s from
          (NormedField.toValued
            (K := P.adicCompletion K)).is_topological_valuation s]
        simpa using
          (NormedField.valuation (K := P.adicCompletion K))
            |>.exists_setOf_restrict_le_iff 0 s
      letI hcompact : LocallyCompactSpace (P.adicCompletion K) :=
        adicLocallySpace P
      haveI hnontrivial : ValuativeRel.IsNontrivial (P.adicCompletion K) :=
        (ValuativeRel.isNontrivial_iff_isNontrivial
          (NormedField.valuation (K := P.adicCompletion K))).mpr inferInstance
      letI : IsNonarchimedeanLocalField (P.adicCompletion K) :=
        { toIsValuativeTopology := htop
          toLocallyCompactSpace := hcompact
          toIsNontrivial := hnontrivial }
      have hlocal : Represents (Q.baseChange (P.adicCompletion K)) 0 := by
        apply h310 (P.adicCompletion K) _ (Q.baseChange (P.adicCompletion K))
        · simpa only [Module.finrank_baseChange] using hdim
        · exact quadratic_change_nondegenerate Q hQ
      simpa only [quadraticFormPlace, placeCompletion] using hlocal
  | inr w =>
      let F := placeCompletion K (.inr w)
      let W := F ⊗[K] V
      let Qw : QuadraticForm F W := quadraticFormPlace K V Q (.inr w)
      have htwoF : (2 : F) ≠ 0 := by simpa [F] using htwo
      letI : Invertible (2 : F) := invertibleOfNonzero htwoF
      obtain ⟨weights, ⟨e⟩⟩ := Qw.equivalent_weightedSumSquares
      let N := Module.finrank F W
      have hdimW : 5 ≤ Module.finrank F W := by
        dsimp only [F, W]
        simpa only [Module.finrank_baseChange] using hdim
      have hN : 2 ≤ N := by
        dsimp only [N]
        omega
      have hsqrt : ∀ x : F, ∃ z : F, x = z * z := by
        intro x
        let E : F ≃+* ℂ := by
          simpa [F, placeCompletion] using
            InfinitePlace.Completion.ringEquivComplexOfIsComplex hv
        obtain ⟨z, hz⟩ := IsAlgClosed.exists_eq_mul_self (E x)
        refine ⟨E.symm z, ?_⟩
        apply E.injective
        simpa using hz
      obtain ⟨y, hy, hyQ⟩ :=
        weighted_squares_represents hN weights hsqrt
      refine ⟨e.symm y, ?_, ?_⟩
      · intro hzero
        apply hy
        have := congrArg e hzero
        simpa using this
      exact (e.symm.map_app y).trans hyQ

/-- Global isotropy remains isotropy after scalar extension to a completion. -/
def GlobalLocalBridge : Prop :=
  ∀ (K V : Type u) [Field K] [NumberField K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (Q : QuadraticForm K V),
    Represents Q 0 → ∀ v, Represents (quadraticFormPlace K V Q v) 0

/-- Global isotropy is preserved by scalar extension to every completion. -/
theorem globalToLocal :
    GlobalLocalBridge.{u} := by
  intro K V _ _ _ _ _ Q hQ v
  obtain ⟨x, hx, hQx⟩ := hQ
  refine ⟨(1 : placeCompletion K v) ⊗ₜ[K] x, ?_, ?_⟩
  · intro hzero
    exact hx ((Module.FaithfullyFlat.one_tmul_eq_zero_iff K V x).mp hzero)
  · simp [quadraticFormPlace, QuadraticForm.baseChange_tmul, hQx]

/-- **Corollary VIII.3.11 (source statement).** -/
def DimensionalIsotropyCriterion : Prop :=
  ∀ (K V : Type u) [Field K] [NumberField K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (Q : QuadraticForm K V),
    5 ≤ Module.finrank K V → Q.Nondegenerate →
      (Represents Q 0 ↔
        ∀ v : InfinitePlace K, InfinitePlace.IsReal v →
          Represents (quadraticFormPlace K V Q (.inr v)) 0)

theorem of_hasseMinkowski
    (h35 : HasseMinkowskiGlobal.{u})
    (h310 : HighDimensionalIsotropic.{u}) :
    DimensionalIsotropyCriterion.{u} := by
  intro K V _ _ _ _ _ Q hdim hQ
  constructor
  · intro hglobal v _hv
    exact globalToLocal K V Q hglobal (.inr v)
  · intro hreal
    apply h35 K V Q hQ
    intro v
    cases v with
    | inl P =>
        exact nonrealPlaces h310 K V Q hdim hQ (.inl P) trivial
    | inr v =>
        rcases InfinitePlace.isReal_or_isComplex v with hv | hv
        · exact hreal v hv
        · exact nonrealPlaces h310 K V Q hdim hQ (.inr v) hv

end
end Submission.CField.HNorm
