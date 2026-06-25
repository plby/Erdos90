import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Algebra.BigOperators.Fin

/-!
# Milne, Algebraic Number Theory, Lemma 4.23

The Dirichlet integral over a simplex.  We use the iterated-integral presentation from Milne's
proof: after choosing the first coordinate, the remaining coordinates range over a simplex whose
radius is the unused part of `t`.
-/

namespace Submission.NumberTheory.Milne

open Complex intervalIntegral MeasureTheory Set
open scoped BigOperators Real

/-- The closed simplex `Z(t) = {x_i ≥ 0, sum x_i ≤ t}` from Milne's Lemma 4.23. -/
def milneSimplexSet (m : ℕ) (t : ℝ) : Set (Fin m → ℝ) :=
  {x | (∀ i, 0 ≤ x i) ∧ ∑ i, x i ≤ t}

/-- Milne's actual multidimensional integral over `Z(t)`. -/
noncomputable def milneSimplexIntegral {m : ℕ} (a : Fin m → ℝ) (t : ℝ) : ℝ :=
  ∫ x in milneSimplexSet m t, ∏ i, x i ^ a i

theorem milne_simplex_closed (m : ℕ) (t : ℝ) :
    IsClosed (milneSimplexSet m t) := by
  change IsClosed ({x : Fin m → ℝ | ∀ i, 0 ≤ x i} ∩
    {x : Fin m → ℝ | ∑ i, x i ≤ t})
  apply IsClosed.inter
  · have hclosed : IsClosed (⋂ i : Fin m, {x : Fin m → ℝ | 0 ≤ x i}) :=
      isClosed_iInter fun (i : Fin m) ↦
        isClosed_le
          (continuous_const : Continuous fun _ : Fin m → ℝ ↦ (0 : ℝ))
          (continuous_apply i : Continuous fun x : Fin m → ℝ ↦ x i)
    convert hclosed using 1
    ext x
    simp
  · exact isClosed_le
      (continuous_finsetSum _ fun (i : Fin m) _ ↦
        (continuous_apply i : Continuous fun x : Fin m → ℝ ↦ x i))
      continuous_const

theorem milne_simplex_compact (m : ℕ) (t : ℝ) :
    IsCompact (milneSimplexSet m t) := by
  let box : Set (Fin m → ℝ) := Set.univ.pi fun _ ↦ Set.Icc 0 t
  have hbox : IsCompact box := isCompact_univ_pi fun _ ↦ isCompact_Icc
  rw [Metric.isCompact_iff_isClosed_bounded]
  refine ⟨milne_simplex_closed m t, hbox.isBounded.subset ?_⟩
  exact fun x hx i _ ↦
    ⟨hx.1 i, le_trans
      (Finset.single_le_sum (s := Finset.univ) (f := fun j : Fin m ↦ x j)
        (fun j _ ↦ hx.1 j) (Finset.mem_univ i)) hx.2⟩

theorem milne_simplex_measurable (m : ℕ) (t : ℝ) :
    MeasurableSet (milneSimplexSet m t) :=
  (milne_simplex_closed m t).measurableSet

private theorem milne_simplex_monomial {m : ℕ} (a : Fin m → ℝ)
    (ha : ∀ i, 0 ≤ a i) :
    Continuous (fun x : Fin m → ℝ ↦ ∏ i, x i ^ a i) := by
  exact continuous_finsetProd _ fun i _ ↦
    (Real.continuous_rpow_const (ha i)).comp (continuous_apply i)

theorem milne_simplex_integrable {m : ℕ} (a : Fin m → ℝ)
    (t : ℝ) (ha : ∀ i, 0 ≤ a i) :
    IntegrableOn (fun x : Fin m → ℝ ↦ ∏ i, x i ^ a i)
      (milneSimplexSet m t) := by
  exact (milne_simplex_monomial a ha).continuousOn.integrableOn_compact
    (milne_simplex_compact m t)

private theorem milne_simplex_cons {m : ℕ} (a₀ : ℝ) (a : Fin m → ℝ)
    (t : ℝ) (ha₀ : 0 ≤ a₀) (ha : ∀ i, 0 ≤ a i) (ht : 0 ≤ t) :
    milneSimplexIntegral (Fin.cons a₀ a) t =
      ∫ x in 0..t, x ^ a₀ * milneSimplexIntegral a (t - x) := by
  let e : (Fin (m + 1) → ℝ) ≃ᵐ ℝ × (Fin m → ℝ) :=
    MeasurableEquiv.piFinSuccAbove (fun _ ↦ ℝ) 0
  let P : Set (ℝ × (Fin m → ℝ)) :=
    {p | p.1 ∈ Set.Icc 0 t ∧ p.2 ∈ milneSimplexSet m (t - p.1)}
  let G : ℝ × (Fin m → ℝ) → ℝ :=
    fun p ↦ p.1 ^ a₀ * ∏ i, p.2 i ^ a i
  let H : (Fin (m + 1) → ℝ) → ℝ :=
    (milneSimplexSet (m + 1) t).indicator
      (fun x ↦ ∏ i, x i ^ ((Fin.cons a₀ a : Fin (m + 1) → ℝ) i))
  let F : ℝ × (Fin m → ℝ) → ℝ := P.indicator G
  have hcomp : ∀ x, F (e x) = H x := by
    intro x
    have he : e x = (x 0, fun i ↦ x i.succ) := by
      rfl
    have hmem : e x ∈ P ↔ x ∈ milneSimplexSet (m + 1) t := by
      rw [he]
      simp only [P, milneSimplexSet, Set.mem_setOf_eq, Set.mem_Icc,
        Fin.forall_fin_succ]
      rw [Fin.sum_univ_succ]
      constructor
      · rintro ⟨⟨hx0, _⟩, htail, hsum⟩
        exact ⟨⟨hx0, htail⟩, by linarith⟩
      · rintro ⟨⟨hx0, htail⟩, hsum⟩
        have htailSum : 0 ≤ ∑ i : Fin m, x (Fin.succ i) :=
          Finset.sum_nonneg fun (i : Fin m) _ ↦ htail i
        exact ⟨⟨hx0, by linarith⟩, htail, by linarith⟩
    have hval : G (e x) = ∏ i, x i ^ ((Fin.cons a₀ a : Fin (m + 1) → ℝ) i) := by
      rw [he]
      simp only [G, Fin.prod_univ_succ, Fin.cons_zero,
        Fin.cons_succ]
    by_cases hx : x ∈ milneSimplexSet (m + 1) t
    · simpa [F, H, hmem.mpr hx, hx] using hval
    · simp [F, H, hmem.not.mpr hx, hx]
  have hH : Integrable H := by
    exact (milne_simplex_integrable (Fin.cons a₀ a) t (by
      intro i
      refine Fin.cases ha₀ (fun j ↦ ha j) i)).integrable_indicator
        (milne_simplex_measurable (m + 1) t)
  have hpres : MeasurePreserving e :=
    volume_preserving_piFinSuccAbove (fun _ : Fin (m + 1) ↦ ℝ) 0
  have hF : Integrable F := by
    rw [← hpres.integrable_comp_emb e.measurableEmbedding]
    exact hH.congr (Filter.Eventually.of_forall fun x ↦ (hcomp x).symm)
  have hchange : milneSimplexIntegral (Fin.cons a₀ a) t = ∫ p, F p := by
    rw [milneSimplexIntegral, ← MeasureTheory.integral_indicator
      (milne_simplex_measurable (m + 1) t)]
    calc
      ∫ x, H x = ∫ x, F (e x) := integral_congr_ae
        (Filter.Eventually.of_forall fun x ↦ (hcomp x).symm)
      _ = ∫ p, F p := hpres.integral_comp' F
  rw [hchange, Measure.volume_eq_prod, integral_prod F hF]
  have hfiber : ∀ x : ℝ, (∫ y, F (x, y)) =
      (Set.Icc 0 t).indicator
        (fun x ↦ x ^ a₀ * milneSimplexIntegral a (t - x)) x := by
    intro x
    by_cases hx : x ∈ Set.Icc 0 t
    · rw [Set.indicator_of_mem hx]
      have hx' : 0 ≤ x ∧ x ≤ t := by simpa [Set.mem_Icc] using hx
      have hfun : (fun y ↦ F (x, y)) =
          (milneSimplexSet m (t - x)).indicator
            (fun y ↦ x ^ a₀ * ∏ i, y i ^ a i) := by
        funext y
        by_cases hy : y ∈ milneSimplexSet m (t - x)
        · simp [F, P, G, hx', hy]
        · simp [F, P, G, hx', hy]
      rw [hfun, MeasureTheory.integral_indicator
          (milne_simplex_measurable m (t - x)),
        MeasureTheory.integral_const_mul]
      rfl
    · rw [Set.indicator_of_notMem hx]
      have hx' : ¬(0 ≤ x ∧ x ≤ t) := by simpa [Set.mem_Icc] using hx
      have hfun : (fun y ↦ F (x, y)) = 0 := by
        funext y
        simp [F, P, hx']
      simp [hfun]
  rw [integral_congr_ae (Filter.Eventually.of_forall hfiber),
    MeasureTheory.integral_indicator measurableSet_Icc,
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le ht]

/-- The iterated integral over
`{x_i ≥ 0 | x_1 + ... + x_m ≤ t}` with integrand `∏ x_i ^ a_i`.

The complex-valued formulation is convenient because Mathlib's beta integral is stated using
complex powers.  For positive real coordinates and real exponents this is the usual real power.
-/
noncomputable def milneSimplexList : List ℝ → ℝ → ℂ
  | [], _ => 1
  | a :: as, t =>
      ∫ x : ℝ in 0..t, (x : ℂ) ^ (a : ℂ) * milneSimplexList as (t - x)

/-- The Gamma product appearing in the Dirichlet integral. -/
noncomputable def milneGammaProduct (as : List ℝ) : ℂ :=
  (as.map fun a : ℝ => Gamma ((a + 1 : ℝ) : ℂ)).prod

private lemma gammaParameter_pos {as : List ℝ} (ha : ∀ a ∈ as, 0 < a) :
    0 < ((as.sum + as.length + 1 : ℝ) : ℂ).re := by
  norm_cast
  have hsum : 0 ≤ as.sum := by
    exact List.sum_nonneg fun a ha_mem => (ha a ha_mem).le
  positivity

/-- **Milne, Lemma 4.23**, in the iterated-integral form used in the printed proof. -/
theorem milne_simplex_list (as : List ℝ) (t : ℝ)
    (ha : ∀ a ∈ as, 0 < a) (ht : 0 < t) :
    milneSimplexList as t =
      (t : ℂ) ^ ((as.sum + as.length : ℝ) : ℂ) * milneGammaProduct as /
        Gamma ((as.sum + as.length + 1 : ℝ) : ℂ) := by
  induction as generalizing t with
  | nil =>
      simp [milneSimplexList, milneGammaProduct]
  | cons a as ih =>
      have ha0 : 0 < a := ha a (by simp)
      have has : ∀ b ∈ as, 0 < b := by
        intro b hb
        exact ha b (by simp [hb])
      have hB : 0 < ((as.sum + as.length + 1 : ℝ) : ℂ).re :=
        gammaParameter_pos has
      rw [milneSimplexList]
      have hrewrite :
          (∫ x : ℝ in 0..t,
              (x : ℂ) ^ (a : ℂ) * milneSimplexList as (t - x)) =
            ∫ x : ℝ in 0..t,
              (x : ℂ) ^ (a : ℂ) *
                (((t - x : ℝ) : ℂ) ^ ((as.sum + as.length : ℝ) : ℂ) *
                  (milneGammaProduct as /
                    Gamma ((as.sum + as.length + 1 : ℝ) : ℂ))) := by
        rw [intervalIntegral.integral_of_le ht.le, integral_Ioc_eq_integral_Ioo,
          intervalIntegral.integral_of_le ht.le, integral_Ioc_eq_integral_Ioo]
        refine setIntegral_congr_fun measurableSet_Ioo fun x hx => ?_
        rw [ih (t - x) has (sub_pos.mpr hx.2)]
        simp only [div_eq_mul_inv, mul_assoc]
      rw [hrewrite]
      let C : ℂ := milneGammaProduct as /
        Gamma ((as.sum + as.length + 1 : ℝ) : ℂ)
      have hfactor :
          (∫ x : ℝ in 0..t,
              (x : ℂ) ^ (a : ℂ) *
                (((t - x : ℝ) : ℂ) ^ ((as.sum + as.length : ℝ) : ℂ) * C)) =
            (∫ x : ℝ in 0..t,
              (x : ℂ) ^ (a : ℂ) *
                ((t - x : ℝ) : ℂ) ^ ((as.sum + as.length : ℝ) : ℂ)) * C := by
        simpa only [mul_assoc] using
          (intervalIntegral.integral_mul_const (a := 0) (b := t) C
            (fun x : ℝ ↦
              (x : ℂ) ^ (a : ℂ) *
                ((t - x : ℝ) : ℂ) ^ ((as.sum + as.length : ℝ) : ℂ)))
      change (∫ x : ℝ in 0..t,
          (x : ℂ) ^ (a : ℂ) *
            (((t - x : ℝ) : ℂ) ^ ((as.sum + as.length : ℝ) : ℂ) * C)) = _
      rw [hfactor]
      have hbeta := betaIntegral_scaled ((a + 1 : ℝ) : ℂ)
        ((as.sum + as.length + 1 : ℝ) : ℂ) ht
      have hbeta' :
          (∫ x : ℝ in 0..t,
              (x : ℂ) ^ (a : ℂ) *
                ((t - x : ℝ) : ℂ) ^ ((as.sum + as.length : ℝ) : ℂ)) =
            (t : ℂ) ^
                (((a + 1 : ℝ) : ℂ) +
                  ((as.sum + as.length + 1 : ℝ) : ℂ) - 1) *
              betaIntegral ((a + 1 : ℝ) : ℂ)
                ((as.sum + as.length + 1 : ℝ) : ℂ) := by
        simpa only [ofReal_add, ofReal_one, ofReal_sub, add_sub_cancel_right] using hbeta
      rw [hbeta', betaIntegral_eq_Gamma_mul_div]
      · have hGammaB :
            Gamma ((as.sum + as.length + 1 : ℝ) : ℂ) ≠ 0 :=
          Gamma_ne_zero_of_re_pos hB
        dsimp [C]
        have hexp :
            (((a + 1 : ℝ) : ℂ) + ((as.sum + as.length + 1 : ℝ) : ℂ) - 1) =
              (((a :: as).sum + (a :: as).length : ℝ) : ℂ) := by
          push_cast
          simp
          ring
        have hden :
            (((a + 1 : ℝ) : ℂ) + ((as.sum + as.length + 1 : ℝ) : ℂ)) =
              ((((a :: as).sum + (a :: as).length + 1 : ℝ)) : ℂ) := by
          push_cast
          simp
          ring
        rw [hexp, hden]
        simp only [milneGammaProduct, List.map_cons, List.prod_cons]
        have hsum :
            ((a :: as).sum + (a :: as).length : ℝ) =
              a + as.sum + (as.length + 1 : ℕ) := by
          simp
        rw [← hsum]
        have hGammaB' :
            Gamma (((1 + as.sum + as.length : ℝ)) : ℂ) ≠ 0 := by
          simpa [add_comm, add_left_comm, add_assoc] using hGammaB
        field_simp [hGammaB']
      · norm_cast
        linarith
      · exact hB

private lemma gamma_product_fn {m : ℕ} (a : Fin m → ℝ) :
    milneGammaProduct (List.ofFn a) = ∏ i, Gamma ((a i + 1 : ℝ) : ℂ) := by
  unfold milneGammaProduct
  rw [List.ofFn_eq_map, List.map_map]
  change ((List.finRange m).map (fun i => Gamma ((a i + 1 : ℝ) : ℂ))).prod = _
  rw [← List.ofFn_eq_map, List.prod_ofFn]

/-- Finite-family formulation of Milne's Lemma 4.23. -/
theorem milne_simplex {m : ℕ} (a : Fin m → ℝ) (t : ℝ)
    (ha : ∀ i, 0 < a i) (ht : 0 < t) :
    milneSimplexList (List.ofFn a) t =
      (t : ℂ) ^ (((∑ i, a i) + m : ℝ) : ℂ) *
          (∏ i, Gamma ((a i + 1 : ℝ) : ℂ)) /
        Gamma ((((∑ i, a i) + m + 1 : ℝ) : ℂ)) := by
  simpa [List.sum_ofFn, gamma_product_fn] using
    milne_simplex_list (List.ofFn a) t (by simpa using ha) ht

/-- The real-valued iterated simplex integral from Milne's statement. -/
noncomputable def milneSimplexReal : List ℝ → ℝ → ℝ
  | [], _ => 1
  | a :: as, t =>
      ∫ x : ℝ in 0..t, x ^ a * milneSimplexReal as (t - x)

/-- Fubini's theorem identifies Milne's multidimensional simplex integral with the
recursive iterated integral used in the printed induction proof. -/
theorem milne_simplex_iterated {m : ℕ} (a : Fin m → ℝ) (t : ℝ)
    (ha : ∀ i, 0 ≤ a i) (ht : 0 ≤ t) :
    milneSimplexIntegral a t =
      milneSimplexReal (List.ofFn a) t := by
  induction m generalizing t with
  | zero =>
      have hset : milneSimplexSet 0 t = Set.univ := by
        ext x
        simp [milneSimplexSet, ht]
      rw [milneSimplexIntegral, List.ofFn_zero,
        milneSimplexReal, hset, Measure.volume_pi_eq_dirac]
      simp
  | succ m ih =>
      let a₀ : ℝ := a 0
      let aTail : Fin m → ℝ := Fin.tail a
      have ha₀ : 0 ≤ a₀ := ha 0
      have haTail : ∀ i, 0 ≤ aTail i := fun i ↦ ha i.succ
      calc
        milneSimplexIntegral a t =
            milneSimplexIntegral (Fin.cons a₀ aTail) t := by
          rw [Fin.cons_self_tail]
        _ = ∫ x in 0..t, x ^ a₀ * milneSimplexIntegral aTail (t - x) :=
          milne_simplex_cons a₀ aTail t ha₀ haTail ht
        _ = ∫ x in 0..t,
            x ^ a₀ * milneSimplexReal (List.ofFn aTail) (t - x) := by
          apply intervalIntegral.integral_congr
          intro x hx
          change x ^ a₀ * milneSimplexIntegral aTail (t - x) =
            x ^ a₀ * milneSimplexReal (List.ofFn aTail) (t - x)
          rw [ih aTail (t - x) haTail
            (sub_nonneg.mpr (le_trans hx.2 (max_le ht le_rfl)))]
        _ = milneSimplexReal (a₀ :: List.ofFn aTail) t := by
          rw [milneSimplexReal]
        _ = milneSimplexReal (List.ofFn a) t := by
          unfold a₀ aTail
          rw [show Fin.tail a = (fun i ↦ a i.succ) by rfl, List.ofFn_succ]

/-- The real Gamma product in Milne's formula. -/
noncomputable def milneRealGamma (as : List ℝ) : ℝ :=
  (as.map fun a : ℝ => Real.Gamma (a + 1)).prod

private lemma real_milne_gamma (as : List ℝ) :
    (milneRealGamma as : ℂ) = milneGammaProduct as := by
  induction as with
  | nil => simp [milneRealGamma, milneGammaProduct]
  | cons a as ih =>
      change ((Real.Gamma (a + 1) * milneRealGamma as : ℝ) : ℂ) =
        Gamma (((a + 1 : ℝ) : ℂ)) * milneGammaProduct as
      rw [Complex.ofReal_mul]
      rw [ih, ← Complex.Gamma_ofReal]

private lemma real_milne_simplex (as : List ℝ) (t : ℝ)
    (ha : ∀ a ∈ as, 0 < a) (ht : 0 < t) :
    (milneSimplexReal as t : ℂ) = milneSimplexList as t := by
  induction as generalizing t with
  | nil => simp [milneSimplexReal, milneSimplexList]
  | cons a as ih =>
      have ha0 : 0 < a := ha a (by simp)
      have has : ∀ b ∈ as, 0 < b := by
        intro b hb
        exact ha b (by simp [hb])
      rw [milneSimplexReal, milneSimplexList,
        ← intervalIntegral.integral_ofReal]
      rw [intervalIntegral.integral_of_le ht.le, integral_Ioc_eq_integral_Ioo,
        intervalIntegral.integral_of_le ht.le, integral_Ioc_eq_integral_Ioo]
      refine setIntegral_congr_fun measurableSet_Ioo fun x hx => ?_
      rw [Complex.ofReal_mul, Complex.ofReal_cpow hx.1.le,
        ih (t - x) has (sub_pos.mpr hx.2)]

/-- **Milne, Lemma 4.23**, with real powers and the real Gamma function exactly as printed. -/
theorem milne_simplex_real (as : List ℝ) (t : ℝ)
    (ha : ∀ a ∈ as, 0 < a) (ht : 0 < t) :
    milneSimplexReal as t =
      t ^ (as.sum + as.length : ℝ) * milneRealGamma as /
        Real.Gamma (as.sum + as.length + 1) := by
  apply Complex.ofReal_injective
  rw [real_milne_simplex as t ha ht,
    milne_simplex_list as t ha ht]
  rw [Complex.ofReal_div, Complex.ofReal_mul,
    Complex.ofReal_cpow ht.le, real_milne_gamma,
    Complex.Gamma_ofReal]

private lemma milne_gamma_fn {m : ℕ} (a : Fin m → ℝ) :
    milneRealGamma (List.ofFn a) = ∏ i, Real.Gamma (a i + 1) := by
  unfold milneRealGamma
  rw [List.ofFn_eq_map, List.map_map]
  change ((List.finRange m).map (fun i => Real.Gamma (a i + 1))).prod = _
  rw [← List.ofFn_eq_map, List.prod_ofFn]

/-- Finite-family, real-valued formulation of Milne's Lemma 4.23. -/
theorem milne_simplex_integral {m : ℕ} (a : Fin m → ℝ) (t : ℝ)
    (ha : ∀ i, 0 < a i) (ht : 0 < t) :
    milneSimplexReal (List.ofFn a) t =
      t ^ ((∑ i, a i) + m : ℝ) * (∏ i, Real.Gamma (a i + 1)) /
        Real.Gamma ((∑ i, a i) + m + 1) := by
  simpa [List.sum_ofFn, milne_gamma_fn] using
    milne_simplex_real (List.ofFn a) t (by simpa using ha) ht

/-- **Milne, Lemma 4.23**, stated for the actual multidimensional Lebesgue
integral over `Z(t) ⊆ R^m`. -/
theorem milne_simplex_set {m : ℕ} (a : Fin m → ℝ) (t : ℝ)
    (ha : ∀ i, 0 < a i) (ht : 0 < t) :
    milneSimplexIntegral a t =
      t ^ ((∑ i, a i) + m : ℝ) * (∏ i, Real.Gamma (a i + 1)) /
        Real.Gamma ((∑ i, a i) + m + 1) := by
  rw [milne_simplex_iterated a t (fun i ↦ (ha i).le) ht.le,
    milne_simplex_integral a t ha ht]

end Submission.NumberTheory.Milne
