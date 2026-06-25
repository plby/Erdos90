import Submission.ClassField.CyclotomicBrauer.RationalPrimeTransport
import Submission.ClassField.ReciprocityExistence.CanonicalComparison
import Submission.ClassField.LubinTate.PadicCyclotomic
import Submission.NumberTheory.Locals.LocalFieldClassification
import Submission.ClassField.IdeleCohomology.FiniteIdeleAction

/-!
# The conductor-prime completion as a cyclotomic `Q_p`-extension

This file begins the transport from the finite Lubin--Tate calculation over
the standard field `Q_p` to the completion occurring in the canonical finite
place Artin map of Example VII.8.2.

The first step records the exact degree of the chosen completion.  The
ramification and inertia calculation is global, while
`ramification_idx_deg`
turns it into the required local degree.
-/

namespace Submission.CField.RExist

open AbsoluteValue IsDedekindDomain NumberField
open Submission.NumberTheory.Milne
open Submission.CField.Ideles
open Submission.CField.LTate
open Submission.CField.ICohomo
open Submission.CField.CBrauer

noncomputable section

/-- At the canonical rational height-one prime above `p`, the ideal-theoretic
valuation sends `p` to the standard generator `exp (-1)`. -/
theorem rational_valuation_self
    (p : ℕ) [Fact p.Prime] :
    let P := rationalHeightOne p
    P.valuation ℚ (p : ℚ) = WithZero.exp (-1 : ℤ) := by
  dsimp only
  let P := rationalHeightOne p
  let e : NumberField.RingOfIntegers ℚ ≃+* ℤ :=
    Rat.IsIntegralClosure.intEquiv (NumberField.RingOfIntegers ℚ)
  have hpgen : Rat.HeightOneSpectrum.natGenerator P = p :=
    congrArg Subtype.val
      (Rat.HeightOneSpectrum.primesEquiv.apply_symm_apply
        (⟨p, Fact.out⟩ : Nat.Primes))
  have hspan : P.asIdeal = Ideal.span
      {algebraMap ℤ (NumberField.RingOfIntegers ℚ) (p : ℤ)} := by
    ext x
    rw [← Ideal.apply_mem_of_equiv_iff (I := P.asIdeal) (f := e),
      ← Ideal.apply_mem_of_equiv_iff
        (I := Ideal.span
          {algebraMap ℤ (NumberField.RingOfIntegers ℚ) (p : ℤ)}) (f := e),
      ← Rat.HeightOneSpectrum.span_natGenerator P, hpgen]
    simp [Ideal.map_span, e]
  rw [show (p : ℚ) = algebraMap (NumberField.RingOfIntegers ℚ) ℚ
      (algebraMap ℤ (NumberField.RingOfIntegers ℚ) (p : ℤ)) by norm_num,
    HeightOneSpectrum.valuation_of_algebraMap]
  exact HeightOneSpectrum.intValuation_singleton _ (by
    exact (map_ne_zero_iff _ Int.cast_injective).2
      (by exact_mod_cast (Fact.out : p.Prime).ne_zero)) hspan

/-- The ideal-theoretic valuation at the canonical rational prime is
literally the standard `p`-adic valuation, not merely an equivalent one. -/
theorem rational_valuation_padic
    (p : ℕ) [Fact p.Prime] :
    let P := rationalHeightOne p
    P.valuation ℚ = Rat.padicValuation p := by
  dsimp only
  let P := rationalHeightOne p
  let v := P.valuation ℚ
  let w := Rat.padicValuation p
  have hvp : v (p : ℚ) = WithZero.exp (-1 : ℤ) :=
    rational_valuation_self p
  have hwp : w (p : ℚ) = WithZero.exp (-1 : ℤ) :=
    Rat.padicValuation_self p
  have hequiv : v.IsEquiv w := by
    have hpgen : Rat.HeightOneSpectrum.primesEquiv
        (rationalHeightOne p) = (⟨p, Fact.out⟩ : Nat.Primes) :=
      Rat.HeightOneSpectrum.primesEquiv.apply_symm_apply _
    simpa only [v, w, P, hpgen] using
      (Rat.HeightOneSpectrum.valuation_equiv_padicValuation
        (rationalHeightOne p))
  apply Valuation.ext
  intro q
  by_cases hq : q = 0
  · subst q
    simp
  have hvq0 : v q ≠ 0 := (Valuation.ne_zero_iff v).2 hq
  let z : ℤ := WithZero.log (v q)
  let t : ℚ := (p : ℚ) ^ (-z)
  have hvt : v t = v q := by
    dsimp only [t]
    rw [map_zpow₀, hvp, ← WithZero.exp_zsmul]
    simp [z, hvq0]
  have hwt : w t = w q := hequiv.eq_iff.mp hvt
  have hwteq : w t = v q := by
    calc
      w t = w ((p : ℚ) ^ (-z)) := rfl
      _ = (WithZero.exp (-1 : ℤ)) ^ (-z) := by rw [map_zpow₀, hwp]
      _ = WithZero.exp ((-z) • (-1 : ℤ)) := by rw [WithZero.exp_zsmul]
      _ = WithZero.exp z := by simp
      _ = v q := WithZero.exp_log hvq0
  exact hwteq.symm.trans hwt

/-- The standard rational adic-completion equivalence to `Q_p` preserves
the normalized metrics. -/
theorem rational_completion_isometry
    (p : ℕ) [Fact p.Prime] :
    Isometry (rationalCompletionEquiv p) := by
  let P := rationalHeightOne p
  let e := rationalCompletionEquiv p
  have hdense : DenseRange (algebraMap ℚ (P.adicCompletion ℚ)) :=
    P.denseRange_algebraMap ℚ
  have heq : (fun x : P.adicCompletion ℚ => ‖e x‖) = fun x => ‖x‖ := by
    apply hdense.equalizer
    · exact continuous_norm.comp e.continuous
    · exact continuous_norm
    · funext q
      simp only [Function.comp_apply]
      dsimp only [P]
      have he : e
          (algebraMap ℚ ((rationalHeightOne p).adicCompletion ℚ) q) =
          algebraMap ℚ ℚ_[p] q := e.commutes q
      rw [he]
      change ‖(q : ℚ_[p])‖ = ‖FinitePlace.embedding P q‖
      rw [FinitePlace.norm_embedding,
        NumberField.HeightOneSpectrum.adicAbv_def]
      have hpgen : Rat.HeightOneSpectrum.natGenerator P = p :=
        congrArg Subtype.val
          (Rat.HeightOneSpectrum.primesEquiv.apply_symm_apply
            (⟨p, Fact.out⟩ : Nat.Primes))
      have habs : Ideal.absNorm P.asIdeal = p :=
        (abs_rational_prime P).trans hpgen
      simp only [habs]
      have hval : P.valuation ℚ = Rat.padicValuation p := by
        simpa only [P] using rational_valuation_padic p
      rw [hval]
      by_cases hq : q = 0
      · subst q
        simp
      · have hv : Rat.padicValuation p q =
            WithZero.exp (-padicValRat p q) := by
          simp [Rat.padicValuation, hq]
        rw [hv, Padic.eq_padicNorm,
          padicNorm.eq_zpow_of_nonzero hq]
        let hne : WithZero.exp (-padicValRat p q) ≠ 0 := by simp
        rw [WithZeroMulInt.toNNReal_neg_apply _ hne]
        have hunit : WithZero.unzero hne =
            Multiplicative.ofAdd (-padicValRat p q) := by
          apply WithZero.coe_injective
          rfl
        rw [congrArg Multiplicative.toAdd hunit]
        push_cast
        congr 1
  rw [isometry_iff_dist_eq]
  intro x y
  rw [dist_eq_norm, dist_eq_norm, ← map_sub]
  exact congrFun heq (x - y)

/-- If two base-field structures on the same extension differ by a ring
equivalence, their Galois groups are canonically equivalent.  The underlying
ring automorphism is unchanged. -/
noncomputable def galoisBaseRing
    {K F E : Type} [Field K] [Field F] [Field E]
    [Algebra K E] [Algebra F E]
    (e : K ≃+* F)
    (h : (algebraMap F E).comp e.toRingHom = algebraMap K E) :
    Gal(E/F) ≃* Gal(E/K) where
  toFun σ := AlgEquiv.ofRingEquiv (f := σ.toRingEquiv) (fun x => by
    rw [← RingHom.congr_fun h x]
    change σ ((algebraMap F E) (e x)) = (algebraMap F E) (e x)
    exact σ.commutes (e x))
  invFun τ := AlgEquiv.ofRingEquiv (f := τ.toRingEquiv) (fun y => by
    have hy := RingHom.congr_fun h (e.symm y)
    change (algebraMap F E) (e (e.symm y)) =
      (algebraMap K E) (e.symm y) at hy
    rw [e.apply_symm_apply] at hy
    rw [hy]
    change τ ((algebraMap K E) (e.symm y)) =
      (algebraMap K E) (e.symm y)
    exact τ.commutes (e.symm y))
  left_inv σ := by
    ext x
    rfl
  right_inv τ := by
    ext x
    rfl
  map_mul' σ τ := by
    ext x
    rfl

/-- The absolute-value completion of `ℚ` at the canonical prime above `p`
is the standard field `Q_p`, as a `ℚ`-algebra. -/
noncomputable def rationalAbsoluteCompletion
    (p : ℕ) [Fact p.Prime] :
    let P := rationalHeightOne p
    let v := (FinitePlace.mk P).val
    letI : Fact v.IsNontrivial :=
      ⟨absolute_value_nontrivial P⟩
    letI : Algebra ℚ v.Completion :=
      (completionEmbedding v).toAlgebra
    v.Completion ≃ₐ[ℚ] ℚ_[p] := by
  dsimp only
  let P := rationalHeightOne p
  let v := (FinitePlace.mk P).val
  letI : Fact v.IsNontrivial :=
    ⟨absolute_value_nontrivial P⟩
  letI : Algebra ℚ v.Completion :=
    (completionEmbedding v).toAlgebra
  let eRing := placeCompletionAdic P
  let eAdic : v.Completion ≃ₐ[ℚ] P.adicCompletion ℚ :=
    AlgEquiv.ofRingEquiv (f := eRing) (fun x => by
      change eRing (completionEmbedding v x) =
        algebraMap ℚ (P.adicCompletion ℚ) x
      rw [finite_place_adic]
      rfl)
  exact eAdic.trans (rationalCompletionEquiv p)

/-- The rational-prime completion equivalence preserves the normalized
absolute values. -/
theorem rational_absolute_isometry
    (p : ℕ) [Fact p.Prime] :
    Isometry (rationalAbsoluteCompletion p) := by
  unfold rationalAbsoluteCompletion
  exact (rational_completion_isometry p).comp
    (place_adic_isometry _)

/-- The `Q_p`-algebra map into a chosen completion above the rational prime
`p`, obtained by transporting the canonical completion map along
`rationalAbsoluteCompletion`. -/
noncomputable def rationalQpAlgebra
    (p : ℕ) [Fact p.Prime]
    (L : Type) [Field L] [NumberField L]
    (w : CompletionPlacesAbove (L := L)
      (FinitePlace.mk (rationalHeightOne p)).val) :
    let P := rationalHeightOne p
    let v := (FinitePlace.mk P).val
    letI : Fact v.IsNontrivial :=
      ⟨absolute_value_nontrivial P⟩
    ℚ_[p] →+* w.1.Completion := by
  dsimp only
  let P := rationalHeightOne p
  let v := (FinitePlace.mk P).val
  letI : Fact v.IsNontrivial :=
    ⟨absolute_value_nontrivial P⟩
  letI : Algebra ℚ v.Completion :=
    (completionEmbedding v).toAlgebra
  exact (completionLies v w.1 w.2).comp
    (rationalAbsoluteCompletion p).symm.toRingHom

/-- The transported `Q_p`-algebra map followed by the base-completion
equivalence is the original completion map. -/
theorem rational_qp_absolute
    (p : ℕ) [Fact p.Prime]
    (L : Type) [Field L] [NumberField L]
    (w : CompletionPlacesAbove (L := L)
      (FinitePlace.mk (rationalHeightOne p)).val) :
    let P := rationalHeightOne p
    let v := (FinitePlace.mk P).val
    letI : Fact v.IsNontrivial :=
      ⟨absolute_value_nontrivial P⟩
    letI : Algebra ℚ v.Completion :=
      (completionEmbedding v).toAlgebra
    (rationalQpAlgebra p L w).comp
        (rationalAbsoluteCompletion p).toRingEquiv.toRingHom =
      completionLies v w.1 w.2 := by
  dsimp only
  let P := rationalHeightOne p
  let v := (FinitePlace.mk P).val
  letI : Fact v.IsNontrivial :=
    ⟨absolute_value_nontrivial P⟩
  letI : Algebra ℚ v.Completion :=
    (completionEmbedding v).toAlgebra
  let e := rationalAbsoluteCompletion p
  ext x
  change completionLies v w.1 w.2 (e.symm (e x)) =
    completionLies v w.1 w.2 x
  rw [e.symm_apply_apply]

/-- The global chosen primitive `p^(n+1)`-st root, embedded in the selected
completion above `p`. -/
noncomputable def cyclotomicCompletedZeta
    (p n : ℕ) [Fact p.Prime]
    (L : Type) [Field L] [NumberField L]
    [IsCyclotomicExtension {p ^ (n + 1)} ℚ L]
    (w : CompletionPlacesAbove (L := L)
      (FinitePlace.mk (rationalHeightOne p)).val) :
    w.1.Completion :=
  completionEmbedding w.1
    (IsCyclotomicExtension.zeta (p ^ (n + 1)) ℚ L)

/-- Completing the chosen global cyclotomic root preserves its exact
prime-power order. -/
theorem completed_zeta_primitive
    (p n : ℕ) [Fact p.Prime]
    (L : Type) [Field L] [NumberField L]
    [IsCyclotomicExtension {p ^ (n + 1)} ℚ L]
    (w : CompletionPlacesAbove (L := L)
      (FinitePlace.mk (rationalHeightOne p)).val) :
    IsPrimitiveRoot (cyclotomicCompletedZeta p n L w)
      (p ^ (n + 1)) :=
  (IsCyclotomicExtension.zeta_spec (p ^ (n + 1)) ℚ L).map_of_injective
    (completionEmbedding w.1).injective

/-- A completion of a rational `p^(n+1)`-cyclotomic field at the finite
place represented by `p` has degree `p^n * (p - 1)` over the rational
completion. -/
theorem finrank_nat_generator
    (p n : ℕ) [Fact p.Prime]
    (P : HeightOneSpectrum (NumberField.RingOfIntegers ℚ))
    (hP : Rat.HeightOneSpectrum.natGenerator P = p)
    (L : Type) [Field L] [NumberField L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    [IsCyclotomicExtension {p ^ (n + 1)} ℚ L]
    (w : CompletionPlacesAbove (L := L)
      (FinitePlace.mk P).val) :
    let v := (FinitePlace.mk P).val
    letI : Fact v.IsNontrivial :=
      ⟨absolute_value_nontrivial P⟩
    letI : IsUltrametricDist v.Completion :=
      placeUltrametricDist P
    letI : Algebra v.Completion w.1.Completion :=
      (completionLies v w.1 w.2).toAlgebra
    Module.finrank v.Completion w.1.Completion = p ^ n * (p - 1) := by
  subst p
  dsimp only
  let v := (FinitePlace.mk P).val
  letI : Fact v.IsNontrivial :=
    ⟨absolute_value_nontrivial P⟩
  letI : IsUltrametricDist v.Completion :=
    placeUltrametricDist P
  letI : Algebra v.Completion w.1.Completion :=
    (completionLies v w.1 w.2).toAlgebra
  let hcycl : IsCyclotomicExtension
      {(Rat.HeightOneSpectrum.natGenerator P) ^ (n + 1)} ℚ L :=
    inferInstance
  rw [ramification_idx_deg
      P w,
    ramification_idx_span P L,
    rational_deg_span P L,
    IsCyclotomicExtension.Rat.ramificationIdxIn_eq_of_prime_pow
      (hK := hcycl) (Rat.HeightOneSpectrum.natGenerator P) n L,
    IsCyclotomicExtension.Rat.inertiaDegIn_eq_of_prime_pow
      (hK := hcycl) (Rat.HeightOneSpectrum.natGenerator P) n L,
    mul_one]

/-- Specialization of
`finrank_nat_generator` to the canonical
height-one prime used by Example VII.8.2. -/
theorem cyclotomic_completion_finrank
    (p n : ℕ) [Fact p.Prime]
    (L : Type) [Field L] [NumberField L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    [IsCyclotomicExtension {p ^ (n + 1)} ℚ L]
    (w : CompletionPlacesAbove (L := L)
      (FinitePlace.mk (rationalHeightOne p)).val) :
    let v := (FinitePlace.mk (rationalHeightOne p)).val
    letI : Fact v.IsNontrivial :=
      ⟨absolute_value_nontrivial (rationalHeightOne p)⟩
    letI : IsUltrametricDist v.Completion :=
      placeUltrametricDist (rationalHeightOne p)
    letI : Algebra v.Completion w.1.Completion :=
      (completionLies v w.1 w.2).toAlgebra
    Module.finrank v.Completion w.1.Completion = p ^ n * (p - 1) := by
  have hgenerator : Rat.HeightOneSpectrum.natGenerator
      (rationalHeightOne p) = p := by
    exact congrArg Subtype.val
      (Rat.HeightOneSpectrum.primesEquiv.apply_symm_apply
        (⟨p, Fact.out⟩ : Nat.Primes))
  exact finrank_nat_generator
    p n (rationalHeightOne p) hgenerator L w

/-- After transporting the base completion to the standard field `Q_p`,
the chosen upper completion still has degree `p^n * (p - 1)`. -/
theorem cyclotomic_finrank_padic
    (p n : ℕ) [Fact p.Prime]
    (L : Type) [Field L] [NumberField L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    [IsCyclotomicExtension {p ^ (n + 1)} ℚ L]
    (w : CompletionPlacesAbove (L := L)
      (FinitePlace.mk (rationalHeightOne p)).val) :
    let P := rationalHeightOne p
    let v := (FinitePlace.mk P).val
    letI : Fact v.IsNontrivial :=
      ⟨absolute_value_nontrivial P⟩
    letI : IsUltrametricDist v.Completion :=
      placeUltrametricDist P
    letI : Algebra v.Completion w.1.Completion :=
      (completionLies v w.1 w.2).toAlgebra
    letI : Algebra ℚ_[p] w.1.Completion :=
      (rationalQpAlgebra p L w).toAlgebra
    Module.finrank ℚ_[p] w.1.Completion = p ^ n * (p - 1) := by
  dsimp only
  let P := rationalHeightOne p
  let v := (FinitePlace.mk P).val
  letI : Fact v.IsNontrivial :=
    ⟨absolute_value_nontrivial P⟩
  letI : IsUltrametricDist v.Completion :=
    placeUltrametricDist P
  letI : Algebra ℚ v.Completion :=
    (completionEmbedding v).toAlgebra
  letI : Algebra v.Completion w.1.Completion :=
    (completionLies v w.1 w.2).toAlgebra
  let e := rationalAbsoluteCompletion p
  letI : Algebra ℚ_[p] w.1.Completion :=
    (rationalQpAlgebra p L w).toAlgebra
  calc
    Module.finrank ℚ_[p] w.1.Completion =
        Module.finrank v.Completion w.1.Completion := by
      symm
      apply Algebra.finrank_eq_of_equiv_equiv e.toRingEquiv
        (RingEquiv.refl w.1.Completion)
      ext x
      change rationalQpAlgebra p L w (e x) =
        completionLies v w.1 w.2 x
      change completionLies v w.1 w.2 (e.symm (e x)) =
        completionLies v w.1 w.2 x
      rw [e.symm_apply_apply]
    _ = p ^ n * (p - 1) :=
      cyclotomic_completion_finrank p n L w

/-- With the transported `Q_p`-algebra structure, the chosen completion is
the full `p^(n+1)`-cyclotomic extension of `Q_p`.  The key point is that the
completed global primitive root has cyclotomic minimal polynomial of the
same degree as the whole completion. -/
theorem cyclotomic_completion_extension
    (p n : ℕ) [Fact p.Prime]
    (L : Type) [Field L] [NumberField L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    [IsCyclotomicExtension {p ^ (n + 1)} ℚ L]
    (w : CompletionPlacesAbove (L := L)
      (FinitePlace.mk (rationalHeightOne p)).val) :
    let P := rationalHeightOne p
    let v := (FinitePlace.mk P).val
    letI : Fact v.IsNontrivial :=
      ⟨absolute_value_nontrivial P⟩
    letI : IsUltrametricDist v.Completion :=
      placeUltrametricDist P
    letI : Algebra v.Completion w.1.Completion :=
      (completionLies v w.1 w.2).toAlgebra
    letI : Algebra ℚ_[p] w.1.Completion :=
      (rationalQpAlgebra p L w).toAlgebra
    IsCyclotomicExtension {p ^ (n + 1)} ℚ_[p] w.1.Completion := by
  dsimp only
  let P := rationalHeightOne p
  let v := (FinitePlace.mk P).val
  letI : Fact v.IsNontrivial :=
    ⟨absolute_value_nontrivial P⟩
  letI : IsUltrametricDist v.Completion :=
    placeUltrametricDist P
  letI : Algebra v.Completion w.1.Completion :=
    (completionLies v w.1 w.2).toAlgebra
  letI : Algebra ℚ_[p] w.1.Completion :=
    (rationalQpAlgebra p L w).toAlgebra
  let ζ := cyclotomicCompletedZeta p n L w
  have hfinrank : Module.finrank ℚ_[p] w.1.Completion =
      p ^ n * (p - 1) :=
    cyclotomic_finrank_padic p n L w
  have hfinrank_pos : 0 < Module.finrank ℚ_[p] w.1.Completion := by
    rw [hfinrank]
    exact Nat.mul_pos (pow_pos (Fact.out : p.Prime).pos n)
      (Nat.sub_pos_of_lt (Fact.out : p.Prime).one_lt)
  letI : FiniteDimensional ℚ_[p] w.1.Completion :=
    FiniteDimensional.of_finrank_pos hfinrank_pos
  have hζ : IsPrimitiveRoot ζ (p ^ (n + 1)) :=
    completed_zeta_primitive p n L w
  have hminpoly : minpoly ℚ_[p] ζ =
      Polynomial.cyclotomic (p ^ (n + 1)) ℚ_[p] :=
    (hζ.minpoly_eq_cyclotomic_of_irreducible
      (padicCyclotomic_irreducible p n)).symm
  have hdegree : (minpoly ℚ_[p] ζ).natDegree =
      Module.finrank ℚ_[p] w.1.Completion := by
    rw [hminpoly, Polynomial.natDegree_cyclotomic, hfinrank,
      Nat.totient_prime_pow (Fact.out : p.Prime) (Nat.zero_lt_succ n),
      Nat.add_one_sub_one]
  have hprimitive : IntermediateField.adjoin ℚ_[p] {ζ} = ⊤ :=
    (Field.primitive_element_iff_minpoly_natDegree_eq ℚ_[p] ζ).2 hdegree
  have hadjoin : Algebra.adjoin ℚ_[p] ({ζ} : Set w.1.Completion) = ⊤ := by
    calc
      Algebra.adjoin ℚ_[p] ({ζ} : Set w.1.Completion) =
          (IntermediateField.adjoin ℚ_[p] {ζ}).toSubalgebra :=
        (IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic
          (Algebra.IsAlgebraic.isAlgebraic ζ)).symm
      _ = ⊤ := by rw [hprimitive, IntermediateField.top_toSubalgebra]
  refine (IsCyclotomicExtension.iff_adjoin_eq_top
    ({p ^ (n + 1)} : Set ℕ) ℚ_[p] w.1.Completion).2 ⟨?_, ?_⟩
  · intro m hm _
    rw [Set.mem_singleton_iff] at hm
    subst m
    exact ⟨ζ, hζ⟩
  · apply top_unique
    rw [← hadjoin]
    apply Algebra.adjoin_mono
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst x
    exact ⟨p ^ (n + 1), Set.mem_singleton _,
      pow_ne_zero _ (Fact.out : p.Prime).ne_zero, hζ.pow_eq_one⟩

/-- The translated completed global root generates the entire chosen upper
completion over `Q_p`. -/
theorem zeta_adjoin_top
    (p n : ℕ) [Fact p.Prime]
    (L : Type) [Field L] [NumberField L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    [IsCyclotomicExtension {p ^ (n + 1)} ℚ L]
    (w : CompletionPlacesAbove (L := L)
      (FinitePlace.mk (rationalHeightOne p)).val) :
    let P := rationalHeightOne p
    let v := (FinitePlace.mk P).val
    letI : Fact v.IsNontrivial :=
      ⟨absolute_value_nontrivial P⟩
    letI : IsUltrametricDist v.Completion :=
      placeUltrametricDist P
    letI : Algebra v.Completion w.1.Completion :=
      (completionLies v w.1 w.2).toAlgebra
    letI : Algebra ℚ_[p] w.1.Completion :=
      (rationalQpAlgebra p L w).toAlgebra
    Algebra.adjoin ℚ_[p]
      ({cyclotomicCompletedZeta p n L w - 1} :
        Set w.1.Completion) = ⊤ := by
  dsimp only
  let P := rationalHeightOne p
  let v := (FinitePlace.mk P).val
  letI : Fact v.IsNontrivial :=
    ⟨absolute_value_nontrivial P⟩
  letI : IsUltrametricDist v.Completion :=
    placeUltrametricDist P
  letI : Algebra v.Completion w.1.Completion :=
    (completionLies v w.1 w.2).toAlgebra
  letI : Algebra ℚ_[p] w.1.Completion :=
    (rationalQpAlgebra p L w).toAlgebra
  letI : IsCyclotomicExtension {p ^ (n + 1)} ℚ_[p] w.1.Completion :=
    cyclotomic_completion_extension p n L w
  let ζ := cyclotomicCompletedZeta p n L w
  have hζ : IsPrimitiveRoot ζ (p ^ (n + 1)) :=
    completed_zeta_primitive p n L w
  simpa only [IsPrimitiveRoot.subOnePowerBasis_gen] using
    (hζ.subOnePowerBasis ℚ_[p]).adjoin_gen_eq_top

/-- The cyclotomic Lubin--Tate root field identified with the actual chosen
global completion, preserving the completed global primitive root. -/
noncomputable def cyclotomicAlgCompletion
    (p n : ℕ) [Fact p.Prime]
    (L : Type) [Field L] [NumberField L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    [IsCyclotomicExtension {p ^ (n + 1)} ℚ L]
    (w : CompletionPlacesAbove (L := L)
      (FinitePlace.mk (rationalHeightOne p)).val) :
    let P := rationalHeightOne p
    let v := (FinitePlace.mk P).val
    letI : Fact v.IsNontrivial :=
      ⟨absolute_value_nontrivial P⟩
    letI : IsUltrametricDist v.Completion :=
      placeUltrametricDist P
    letI : Algebra v.Completion w.1.Completion :=
      (completionLies v w.1 w.2).toAlgebra
    letI : Algebra ℚ_[p] w.1.Completion :=
      (rationalQpAlgebra p L w).toAlgebra
    (cyclotomicLubinDatum p).RootField ℚ_[p] n ≃ₐ[ℚ_[p]]
      w.1.Completion := by
  dsimp only
  let P := rationalHeightOne p
  let v := (FinitePlace.mk P).val
  letI : Fact v.IsNontrivial :=
    ⟨absolute_value_nontrivial P⟩
  letI : IsUltrametricDist v.Completion :=
    placeUltrametricDist P
  letI : Algebra v.Completion w.1.Completion :=
    (completionLies v w.1 w.2).toAlgebra
  letI : Algebra ℚ_[p] w.1.Completion :=
    (rationalQpAlgebra p L w).toAlgebra
  let ζ := cyclotomicCompletedZeta p n L w
  let hζ := completed_zeta_primitive p n L w
  let hadjoin :=
    zeta_adjoin_top p n L w
  exact padicAlgPrimitive
    p n w.1.Completion ζ hζ hadjoin

@[simp]
theorem cyclotomic_alg_completion
    (p n : ℕ) [Fact p.Prime]
    (L : Type) [Field L] [NumberField L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    [IsCyclotomicExtension {p ^ (n + 1)} ℚ L]
    (w : CompletionPlacesAbove (L := L)
      (FinitePlace.mk (rationalHeightOne p)).val) :
    let P := rationalHeightOne p
    let v := (FinitePlace.mk P).val
    letI : Fact v.IsNontrivial :=
      ⟨absolute_value_nontrivial P⟩
    letI : IsUltrametricDist v.Completion :=
      placeUltrametricDist P
    letI : Algebra v.Completion w.1.Completion :=
      (completionLies v w.1 w.2).toAlgebra
    letI : Algebra ℚ_[p] w.1.Completion :=
      (rationalQpAlgebra p L w).toAlgebra
    cyclotomicAlgCompletion p n L w
        ((cyclotomicLubinDatum p).root ℚ_[p] n) =
      cyclotomicCompletedZeta p n L w - 1 := by
  dsimp only
  let P := rationalHeightOne p
  let v := (FinitePlace.mk P).val
  letI : Fact v.IsNontrivial :=
    ⟨absolute_value_nontrivial P⟩
  letI : IsUltrametricDist v.Completion :=
    placeUltrametricDist P
  letI : Algebra v.Completion w.1.Completion :=
    (completionLies v w.1 w.2).toAlgebra
  letI : Algebra ℚ_[p] w.1.Completion :=
    (rationalQpAlgebra p L w).toAlgebra
  let ζ := cyclotomicCompletedZeta p n L w
  let hζ := completed_zeta_primitive p n L w
  let hadjoin :=
    zeta_adjoin_top p n L w
  change padicAlgPrimitive
      p n w.1.Completion ζ hζ hadjoin
        ((cyclotomicLubinDatum p).root ℚ_[p] n) = ζ - 1
  exact padic_alg_primitive
    p n w.1.Completion ζ hζ hadjoin

/-- Valuation-integer form of the preceding equivalence, matching the root
field used by the finite Lubin--Tate Artin calculation. -/
noncomputable def integerAlgCompletion
    (p n : ℕ) [Fact p.Prime]
    (L : Type) [Field L] [NumberField L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    [IsCyclotomicExtension {p ^ (n + 1)} ℚ L]
    (w : CompletionPlacesAbove (L := L)
      (FinitePlace.mk (rationalHeightOne p)).val) :
    let P := rationalHeightOne p
    let v := (FinitePlace.mk P).val
    letI : Fact v.IsNontrivial :=
      ⟨absolute_value_nontrivial P⟩
    letI : IsUltrametricDist v.Completion :=
      placeUltrametricDist P
    letI : Algebra v.Completion w.1.Completion :=
      (completionLies v w.1 w.2).toAlgebra
    letI : Algebra ℚ_[p] w.1.Completion :=
      (rationalQpAlgebra p L w).toAlgebra
    (padicLubinDatum p).RootField ℚ_[p] n ≃ₐ[ℚ_[p]]
      w.1.Completion := by
  dsimp only
  let P := rationalHeightOne p
  let v := (FinitePlace.mk P).val
  letI : Fact v.IsNontrivial :=
    ⟨absolute_value_nontrivial P⟩
  letI : IsUltrametricDist v.Completion :=
    placeUltrametricDist P
  letI : Algebra v.Completion w.1.Completion :=
    (completionLies v w.1 w.2).toAlgebra
  letI : Algebra ℚ_[p] w.1.Completion :=
    (rationalQpAlgebra p L w).toAlgebra
  exact (padicIntegerAlg p n).trans
    (cyclotomicAlgCompletion p n L w)

@[simp]
theorem integer_alg_completion
    (p n : ℕ) [Fact p.Prime]
    (L : Type) [Field L] [NumberField L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    [IsCyclotomicExtension {p ^ (n + 1)} ℚ L]
    (w : CompletionPlacesAbove (L := L)
      (FinitePlace.mk (rationalHeightOne p)).val) :
    let P := rationalHeightOne p
    let v := (FinitePlace.mk P).val
    letI : Fact v.IsNontrivial :=
      ⟨absolute_value_nontrivial P⟩
    letI : IsUltrametricDist v.Completion :=
      placeUltrametricDist P
    letI : Algebra v.Completion w.1.Completion :=
      (completionLies v w.1 w.2).toAlgebra
    letI : Algebra ℚ_[p] w.1.Completion :=
      (rationalQpAlgebra p L w).toAlgebra
    integerAlgCompletion p n L w
        ((padicLubinDatum p).root ℚ_[p] n) =
      cyclotomicCompletedZeta p n L w - 1 := by
  dsimp only
  let P := rationalHeightOne p
  let v := (FinitePlace.mk P).val
  letI : Fact v.IsNontrivial :=
    ⟨absolute_value_nontrivial P⟩
  letI : IsUltrametricDist v.Completion :=
    placeUltrametricDist P
  letI : Algebra v.Completion w.1.Completion :=
    (completionLies v w.1 w.2).toAlgebra
  letI : Algebra ℚ_[p] w.1.Completion :=
    (rationalQpAlgebra p L w).toAlgebra
  change ((padicIntegerAlg p n).trans
      (cyclotomicAlgCompletion p n L w))
        ((padicLubinDatum p).root ℚ_[p] n) =
      cyclotomicCompletedZeta p n L w - 1
  rw [AlgEquiv.trans_apply,
    padic_integer_alg,
    cyclotomic_alg_completion]

end

end Submission.CField.RExist
