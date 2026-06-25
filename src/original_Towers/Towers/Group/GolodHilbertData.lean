import Towers.Group.GolodShafarevichPresentation
import Towers.Group.GolodShafarevichNilpotence


open scoped BigOperators AlgebraMonoidAlgebra

noncomputable section

universe u

namespace Towers
namespace GShafar

/--
The depth-counted Golod--Shafarevich relation expression
`1 - d t + ∑ᵢ t ^ depthᵢ`.
-/
def relationSeries (d r : ℕ) (depth : Fin r → ℕ) (t : ℝ) : ℝ :=
  1 - (d : ℝ) * t + ∑ i, t ^ depth i

/-- The polynomial form of `relationSeries`. -/
def relationPolynomial (d r : ℕ) (depth : Fin r → ℕ) : Polynomial ℝ :=
  Polynomial.C (1 : ℝ) -
    Polynomial.C (d : ℝ) * Polynomial.X +
    ∑ i, Polynomial.X ^ depth i

def quadraticSeries (d r : ℕ) (t : ℝ) : ℝ :=
  1 - (d : ℝ) * t + (r : ℝ) * t ^ (2 : ℕ)

/-- The polynomial form of the quadratic Golod--Shafarevich expression. -/
def quadraticPolynomial (d r : ℕ) : Polynomial ℝ :=
  Polynomial.C (1 : ℝ) -
    Polynomial.C (d : ℝ) * Polynomial.X +
    Polynomial.C (r : ℝ) * Polynomial.X ^ (2 : ℕ)

def PRSeries (d r : ℕ) (depth : Fin r → ℕ) : Prop :=
  ∀ t : ℝ, 0 < t → t < 1 → 0 < relationSeries d r depth t

/-- Positivity of the quadratic Golod--Shafarevich expression on `(0,1)`. -/
def PositiveQuadraticSeries (d r : ℕ) : Prop :=
  ∀ t : ℝ, 0 < t → t < 1 → 0 < quadraticSeries d r t

/--
For `0 < t < 1`, any power `t^n` with `n ≥ 2` is bounded above by `t^2`.
-/
lemma pow_sq_interval {t : ℝ}
    (ht0 : 0 < t) (ht1 : t < 1) {n : ℕ} (hn : 2 ≤ n) :
    t ^ n ≤ t ^ (2 : ℕ) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
  have hpow : t ^ m ≤ 1 := by
    have ht_nonneg : 0 ≤ t := le_of_lt ht0
    simpa using (pow_le_one₀ (a := t) ht_nonneg ht1.le : t ^ m ≤ 1)
  calc
    t ^ (2 + m) = t ^ (2 : ℕ) * t ^ m := by rw [pow_add]
    _ ≤ t ^ (2 : ℕ) * 1 := by gcongr
    _ = t ^ (2 : ℕ) := by ring

/--
If every relator has depth at least `2`, the full depth-counted relation
series is bounded above by the quadratic Golod--Shafarevich series on `(0,1)`.
-/
lemma relation_series_quadratic
    {d r : ℕ} (depth : Fin r → ℕ)
    (hdepth : ∀ i, 2 ≤ depth i)
    {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    relationSeries d r depth t ≤ quadraticSeries d r t := by
  unfold relationSeries quadraticSeries
  have hsum : ∑ i, t ^ depth i ≤ ∑ _i : Fin r, t ^ (2 : ℕ) := by
    refine Finset.sum_le_sum ?_
    intro i _hi
    exact pow_sq_interval ht0 ht1 (hdepth i)
  have hcard : (∑ _i : Fin r, t ^ (2 : ℕ)) = (r : ℝ) * t ^ (2 : ℕ) := by
    simp [nsmul_eq_mul]
  linarith

/--
Depth-counted positivity with all depths at least `2` implies positivity of
the quadratic Golod--Shafarevich series.
-/
theorem PRSeries.positiveQuadraticSeries
    {d r : ℕ} {depth : Fin r → ℕ}
    (hdepth : ∀ i, 2 ≤ depth i)
    (hpos : PRSeries d r depth) :
    PositiveQuadraticSeries d r := by
  intro t ht0 ht1
  have hseries : 0 < relationSeries d r depth t := hpos t ht0 ht1
  have hle : relationSeries d r depth t ≤ quadraticSeries d r t :=
    relation_series_quadratic depth hdepth ht0 ht1
  linarith

/-- The strict quadratic relation bound expected for a finite `p`-group. -/
def SGShafar (d r : ℕ) : Prop :=
  (d : ℝ) ^ (2 : ℕ) / 4 < (r : ℝ)

theorem SGShafar.pos_quadraticseries_twolt
    {d r : ℕ} (hd : 2 < d) (hpos : PositiveQuadraticSeries d r) :
    SGShafar d r := by
  have hd_nat : d ≠ 0 := by omega
  have hd_real : (d : ℝ) ≠ 0 := by exact_mod_cast hd_nat
  have ht0 : 0 < (2 : ℝ) / d := by positivity
  have ht1 : (2 : ℝ) / d < 1 := by
    have hdpos : (0 : ℝ) < d := by positivity
    exact (div_lt_one hdpos).2 (by exact_mod_cast hd)
  have h := hpos ((2 : ℝ) / d) ht0 ht1
  have hquad :
      quadraticSeries d r ((2 : ℝ) / d) =
        (4 * (r : ℝ) - (d : ℝ) ^ (2 : ℕ)) /
          (d : ℝ) ^ (2 : ℕ) := by
    unfold quadraticSeries
    field_simp [hd_nat]
    ring
  rw [hquad] at h
  have hd_sq_pos : 0 < (d : ℝ) ^ (2 : ℕ) := by positivity
  have hnum : 0 < 4 * (r : ℝ) - (d : ℝ) ^ (2 : ℕ) := by
    exact (div_pos_iff_of_pos_right hd_sq_pos).mp h
  unfold SGShafar
  nlinarith

/--
The small-generator analytic cases follow from the usual relation-count
bounds: `1 ≤ r`, and `2 ≤ r` when `d = 2`.
-/
theorem SGShafar.rel_bounds_smallgen
    {d r : ℕ} (hd : d ≤ 2) (hr : 1 ≤ r) (hr2 : d = 2 → 2 ≤ r) :
    SGShafar d r := by
  unfold SGShafar
  interval_cases d
  · have hr' : (1 : ℝ) ≤ r := by exact_mod_cast hr
    nlinarith
  · have hr' : (1 : ℝ) ≤ r := by exact_mod_cast hr
    nlinarith
  · have hr' : (2 : ℝ) ≤ r := by exact_mod_cast hr2 rfl
    nlinarith

/--
Full analytic endpoint once the small-generator cases have been discharged
separately.
-/
theorem SGShafar.pos_quadratic_series
    {d r : ℕ}
    (hsmall : d ≤ 2 → SGShafar d r)
    (hpos : PositiveQuadraticSeries d r) :
    SGShafar d r := by
  by_cases hd : d ≤ 2
  · exact hsmall hd
  · exact
      SGShafar.pos_quadraticseries_twolt
        (Nat.lt_of_not_ge hd) hpos

/--
Quadratic positivity plus the standard small-generator relation-count bounds
imply the strict quadratic Golod--Shafarevich bound.
-/
theorem SGShafar.pos_quadraticseries_relbounds
    {d r : ℕ} (hr : 1 ≤ r) (hr2 : d = 2 → 2 ≤ r)
    (hpos : PositiveQuadraticSeries d r) :
    SGShafar d r :=
  SGShafar.pos_quadratic_series
    (fun hd =>
      SGShafar.rel_bounds_smallgen
        hd hr hr2)
    hpos

def hilbertGeneratorTerm (a : ℕ → ℕ) (n : ℕ) : ℕ :=
  if 1 ≤ n then a (n - 1) else 0

/-- The relator contribution in the Hilbert-series coefficient recurrence. -/
def hilbertRelatorTerm {r : ℕ} (a : ℕ → ℕ) (depth : Fin r → ℕ) (n : ℕ) : ℕ :=
  ∑ i, if depth i ≤ n then a (n - depth i) else 0

/--
The generator source has the scalar dimension appearing in the Hilbert
coefficient recurrence, provided the target augmentation layer is finite
dimensional.
-/
theorem presented_hilbert_finrank {d r : ℕ}
    (p : ℕ) [Fact p.Prime] (rels : RelatorFamily d r) (n : ℕ)
    [FiniteDimensional (ZMod p) (pALayer p rels (n - 1))] :
    presentedHilbertFinrank p rels n =
      d * hilbertGeneratorTerm (presentedHilbertSequence p rels) n := by
  classical
  unfold presentedHilbertFinrank
  change
    Module.finrank (ZMod p)
      ((i : aGIndex d n) →
        pALayer p rels (n - 1)) =
      d * hilbertGeneratorTerm (presentedHilbertSequence p rels) n
  rw [Module.finrank_pi_fintype]
  by_cases hn : 1 ≤ n
  · simp [aGIndex, hn, hilbertGeneratorTerm,
      presentedHilbertSequence, presentedAugmentationFinrank,
      Finset.sum_const]
  · simp [aGIndex, hn, hilbertGeneratorTerm]

/--
The relator source has the scalar dimension appearing in the Hilbert
coefficient recurrence, provided the augmentation layers are finite
dimensional.
-/
theorem presented_hilbert_relator {d r : ℕ}
    (p : ℕ) [Fact p.Prime] (rels : RelatorFamily d r)
    (depth : Fin r → ℕ) (n : ℕ)
    (hfinite :
      ∀ m, FiniteDimensional (ZMod p)
        (pALayer p rels m)) :
    presentedHilbertRelator p rels depth n =
      hilbertRelatorTerm (presentedHilbertSequence p rels) depth n := by
  classical
  letI : ∀ i : aRIndex depth n,
      FiniteDimensional (ZMod p)
        (pALayer p rels (n - depth i.1)) :=
    fun i => hfinite (n - depth i.1)
  unfold presentedHilbertRelator
  change
    Module.finrank (ZMod p)
      ((i : aRIndex depth n) →
        pALayer p rels (n - depth i.1)) =
      hilbertRelatorTerm (presentedHilbertSequence p rels) depth n
  rw [Module.finrank_pi_fintype]
  unfold hilbertRelatorTerm
  rw [← Finset.sum_filter]
  simpa [aRIndex, presentedHilbertSequence,
    presentedAugmentationFinrank] using
      (Finset.sum_subtype_eq_sum_filter
        (s := (Finset.univ : Finset (Fin r)))
        (p := fun i : Fin r => depth i ≤ n)
        (f := fun i : Fin r =>
          Module.finrank (ZMod p) (pALayer p rels (n - depth i))))

/--
The coefficient inequality produced by the Hilbert-series proof at degree `n`.

Here `a n` is intended to be the dimension of the `n`th associated graded
augmentation layer.
-/
def HilbertCoefficientInequality {r : ℕ}
    (d : ℕ) (a : ℕ → ℕ) (depth : Fin r → ℕ) (n : ℕ) : Prop :=
  d * hilbertGeneratorTerm a n ≤ a n + hilbertRelatorTerm a depth n

/--
The dimension identities that simplify the associated-graded generator and
relator sources into the scalar terms of the Hilbert coefficient recurrence.
-/
def PHIdenti {d r : ℕ}
    (p : ℕ) [Fact p.Prime] (rels : RelatorFamily d r)
    (depth : Fin r → ℕ) : Prop :=
  ∀ n,
    presentedHilbertFinrank p rels n =
        d * hilbertGeneratorTerm (presentedHilbertSequence p rels) n ∧
      presentedHilbertRelator p rels depth n =
        hilbertRelatorTerm (presentedHilbertSequence p rels) depth n

/--
The full source-dimension identity follows from finite-dimensionality of the
augmentation layers: both source dimensions are finite-product computations.
-/
theorem PHIdenti.of_layerFinite
    {d r : ℕ} {p : ℕ} [Fact p.Prime] {rels : RelatorFamily d r}
    {depth : Fin r → ℕ}
    (hfinite :
      ∀ n, FiniteDimensional (ZMod p) (pALayer p rels n)) :
    PHIdenti p rels depth := by
  intro n
  letI : FiniteDimensional (ZMod p)
      (pALayer p rels (n - 1)) := hfinite (n - 1)
  exact
    ⟨presented_hilbert_finrank p rels n,
      presented_hilbert_relator p rels depth n hfinite⟩

/--
The associated-graded dimension inequality gives the scalar Hilbert
coefficient inequality once the source dimensions have been identified with
the corresponding Hilbert terms.
-/
theorem PHBounds.coefficientInequality
    {d r : ℕ} {p : ℕ} [Fact p.Prime] {rels : RelatorFamily d r}
    {depth : Fin r → ℕ}
    (hbounds : PHBounds p rels depth)
    (hsource : PHIdenti p rels depth)
    (n : ℕ) :
    HilbertCoefficientInequality d
      (presentedHilbertSequence p rels) depth n := by
  unfold HilbertCoefficientInequality
  have hdim := hbounds n
  unfold PresentationHilbertInequality at hdim
  rcases hsource n with ⟨hgen, hrel⟩
  rw [hgen, hrel] at hdim
  simpa [presentedHilbertSequence] using hdim

lemma hilbert_relator_depth
    {r : ℕ} (a : ℕ → ℕ) (depth : Fin r → ℕ) {n : ℕ}
    (hdepth : ∀ i, n < depth i) :
    hilbertRelatorTerm a depth n = 0 := by
  unfold hilbertRelatorTerm
  refine Finset.sum_eq_zero ?_
  intro i _hi
  have hnot : ¬ depth i ≤ n := Nat.not_le_of_gt (hdepth i)
  simp [hnot]

def HilbertSequenceEventually (a : ℕ → ℕ) : Prop :=
  ∃ N : ℕ, ∀ n, N ≤ n → a n = 0

/--
The degree-zero augmentation layer of a presented group algebra is
one-dimensional: `I^0 / I^1` is identified with `𝔽_p` by augmentation.
-/
theorem presented_hilbert_sequence
    {d r : ℕ} {p : ℕ} [Fact p.Prime] (rels : RelatorFamily d r) :
    presentedHilbertSequence p rels 0 = 1 := by
  classical
  let G := pGroup rels
  let A := MonoidAlgebra (ZMod p) G
  let I : Ideal A := augmentationIdeal (ZMod p) G
  let I0 : Submodule (ZMod p) A := (I ^ (0 : ℕ)).restrictScalars (ZMod p)
  let I1 : Submodule (ZMod p) A := (I ^ (1 : ℕ)).restrictScalars (ZMod p)
  let K : Submodule (ZMod p) I0 := I1.comap (Submodule.subtype I0)
  let augLinear : A →ₗ[ZMod p] ZMod p :=
    (augmentationHom (ZMod p) G).toLinearMap
  let aug0 : I0 →ₗ[ZMod p] ZMod p := augLinear.comp (Submodule.subtype I0)
  have hker : LinearMap.ker aug0 = K := by
    ext x
    constructor
    · intro hx
      have hxI : (x : A) ∈ I := by
        have hxaug : (augmentationHom (ZMod p) G).toRingHom (x : A) = 0 := by
          simpa [aug0, augLinear] using hx
        exact RingHom.mem_ker.mpr hxaug
      change (x : A) ∈ I1
      change (x : A) ∈ (I ^ (1 : ℕ)).restrictScalars (ZMod p)
      change (x : A) ∈ (I ^ (1 : ℕ) : Submodule A A)
      simpa [Submodule.pow_one] using hxI
    · intro hx
      have hxI : (x : A) ∈ I := by
        have hxI1 : (x : A) ∈ I1 := hx
        change (x : A) ∈ (I ^ (1 : ℕ)).restrictScalars (ZMod p) at hxI1
        change (x : A) ∈ (I ^ (1 : ℕ) : Submodule A A) at hxI1
        simpa [Submodule.pow_one] using hxI1
      have hxaug : (augmentationHom (ZMod p) G).toRingHom (x : A) = 0 :=
        RingHom.mem_ker.mp hxI
      change aug0 x = 0
      simpa [aug0, augLinear] using hxaug
  have hsurj : Function.Surjective aug0 := by
    intro c
    have hmem : (c • (1 : A)) ∈ I0 := by
      change (c • (1 : A)) ∈ (I ^ (0 : ℕ)).restrictScalars (ZMod p)
      change (c • (1 : A)) ∈ (I ^ (0 : ℕ) : Submodule A A)
      rw [Submodule.pow_zero]
      simp
    refine ⟨⟨c • (1 : A), hmem⟩, ?_⟩
    simp [aug0, augLinear]
  let e : ((↥I0) ⧸ K) ≃ₗ[ZMod p] ZMod p :=
    (Submodule.quotEquivOfEq K (LinearMap.ker aug0) hker.symm).trans
      (aug0.quotKerEquivOfSurjective hsurj)
  have hfinrank : Module.finrank (ZMod p) ((↥I0) ⧸ K) = 1 := by
    calc
      Module.finrank (ZMod p) ((↥I0) ⧸ K)
          = Module.finrank (ZMod p) (ZMod p) :=
            LinearEquiv.finrank_eq e
      _ = 1 := CommSemiring.finrank_self (ZMod p)
  change Module.finrank (ZMod p) ((↥I0) ⧸ K) = 1
  exact hfinrank

/--
If the `n`th augmentation power is zero, the `n`th associated-graded
augmentation coefficient is zero.
-/
theorem presented_hilbert_bot
    {d r : ℕ} {p : ℕ} [Fact p.Prime] {rels : RelatorFamily d r}
    {n : ℕ}
    (hpow : (presentedAugmentationIdeal p rels) ^ n = ⊥) :
    presentedHilbertSequence p rels n = 0 := by
  classical
  let A := MonoidAlgebra (ZMod p) (pGroup rels)
  let I : Ideal A := presentedAugmentationIdeal p rels
  let In1 : Submodule (ZMod p) A := (I ^ (n + 1)).restrictScalars (ZMod p)
  dsimp [presentedHilbertSequence,
    presentedAugmentationFinrank, pALayer,
    presentedAugmentationKernel, presentedAugmentationSubmodule]
  change Module.finrank (ZMod p)
      ((↥((I ^ n).restrictScalars (ZMod p))) ⧸
        Submodule.comap (Submodule.subtype ((I ^ n).restrictScalars (ZMod p))) In1) = 0
  rw [hpow]
  let K : Submodule (ZMod p) (↥(⊥ : Submodule (ZMod p) A)) :=
    Submodule.comap (Submodule.subtype (⊥ : Submodule (ZMod p) A)) In1
  change Module.finrank (ZMod p) ((↥(⊥ : Submodule (ZMod p) A)) ⧸ K) = 0
  haveI : Subsingleton ((↥(⊥ : Submodule (ZMod p) A)) ⧸ K) := inferInstance
  exact (Module.finrank_zero_iff
    (R := ZMod p) (M := ((↥(⊥ : Submodule (ZMod p) A)) ⧸ K))).2 inferInstance

/-- If an augmentation ideal has a zero power, all higher powers are zero. -/
lemma presented_bot_nilpotence
    {d r : ℕ} (p : ℕ) (rels : RelatorFamily d r)
    {N n : ℕ}
    (hN : (presentedAugmentationIdeal p rels) ^ N = ⊥)
    (hNn : N ≤ n) :
    (presentedAugmentationIdeal p rels) ^ n = ⊥ := by
  apply le_antisymm
  · calc
      (presentedAugmentationIdeal p rels) ^ n
          ≤ (presentedAugmentationIdeal p rels) ^ N :=
            Ideal.pow_le_pow_right hNn
      _ = ⊥ := hN
  · exact bot_le

/--
Nilpotence of the presented augmentation ideal gives eventual vanishing of
the concrete augmentation-layer Hilbert sequence.
-/
theorem hilbert_eventually_nilpotent
    {d r : ℕ} {p : ℕ} [Fact p.Prime] {rels : RelatorFamily d r}
    (hnil : ∃ N : ℕ, (presentedAugmentationIdeal p rels) ^ N = ⊥) :
    HilbertSequenceEventually (presentedHilbertSequence p rels) := by
  rcases hnil with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro n hNn
  exact presented_hilbert_bot
    (p := p) (rels := rels)
    (presented_bot_nilpotence
      p rels hN hNn)

/--
For a finite presented group, elementwise nilpotence of the augmentation ideal
implies a uniform nilpotence exponent for that ideal.
-/
theorem presented_nilpotent_nil
    {d r : ℕ} {p : ℕ} [Fact p.Prime] {rels : RelatorFamily d r}
    [Finite (pGroup rels)]
    (hI :
      ∀ x : MonoidAlgebra (ZMod p) (pGroup rels),
        x ∈ presentedAugmentationIdeal p rels → ∃ N : ℕ, x ^ N = 0) :
    ∃ N : ℕ, (presentedAugmentationIdeal p rels) ^ N = ⊥ := by
  classical
  haveI : Finite (MonoidAlgebra (ZMod p) (pGroup rels)) :=
    zmod_group_algebra p (Fact.out : Nat.Prime p)
      (pGroup rels)
  exact ring_nil_nilpotent
    (I := presentedAugmentationIdeal p rels) hI

/--
For a finite presented group, the augmentation-one unit criterion gives
elementwise nilpotence of the presented augmentation ideal.
-/
theorem presented_nil_units
    {d r : ℕ} {p : ℕ} [Fact p.Prime] {rels : RelatorFamily d r}
    [Finite (pGroup rels)]
    (hunit :
      ∀ a : MonoidAlgebra (ZMod p) (pGroup rels),
        (augmentationHom (ZMod p) (pGroup rels)).toRingHom a = 1 →
          IsUnit a) :
    ∀ x : MonoidAlgebra (ZMod p) (pGroup rels),
      x ∈ presentedAugmentationIdeal p rels → ∃ N : ℕ, x ^ N = 0 := by
  simpa [presentedAugmentationIdeal] using
    augmentation_nil_units
      (p := p) (G := pGroup rels) hunit

/--
The abstract finite Hilbert-recurrence package needed by the
Golod--Shafarevich proof.
-/
def FiniteHilbertRecurrence {r : ℕ}
    (d : ℕ) (depth : Fin r → ℕ) (a : ℕ → ℕ) : Prop :=
  a 0 = 1 ∧
    (∀ n, HilbertCoefficientInequality d a depth n) ∧
    HilbertSequenceEventually a

def HilbertRecurrenceForces {r : ℕ}
    (d : ℕ) (depth : Fin r → ℕ) : Prop :=
  ∀ a : ℕ → ℕ,
    FiniteHilbertRecurrence d depth a →
      PRSeries d r depth

/--
A presentation has the concrete Hilbert recurrence when the augmentation-layer
dimensions of its presented group algebra satisfy the coefficient recurrence.
-/
def PHRec {d r : ℕ}
    (p : ℕ) [Fact p.Prime] (rels : RelatorFamily d r) (depth : Fin r → ℕ) : Prop :=
  PresentationDepthsLeast p rels depth ∧
    FiniteHilbertRecurrence d depth
      (presentedHilbertSequence p rels)

/--
Concrete associated-graded dimension bounds give the concrete Hilbert
recurrence once the source dimensions have been identified with the scalar
Hilbert terms and the endpoint Hilbert-sequence facts are known.
-/
theorem PHRec.of_dimensionBounds
    {d r : ℕ} {p : ℕ} [Fact p.Prime] {rels : RelatorFamily d r}
    {depth : Fin r → ℕ}
    [Finite (pGroup rels)]
    (hdepth : PresentationDepthsLeast p rels depth)
    (hbounds : PHBounds p rels depth)
    (hunit :
      ∀ a : MonoidAlgebra (ZMod p) (pGroup rels),
        (augmentationHom (ZMod p) (pGroup rels)).toRingHom a = 1 →
          IsUnit a) :
    PHRec p rels depth :=
  ⟨hdepth, presented_hilbert_sequence rels,
    fun n =>
      PHBounds.coefficientInequality
        hbounds
          (PHIdenti.of_layerFinite
            (fun n =>
              presented_dimensional_group p rels n))
          n,
    hilbert_eventually_nilpotent
      (presented_nilpotent_nil
        (presented_nil_units hunit))⟩

theorem PHRec.finiteHilbertRecurrence {d r : ℕ}
    {p : ℕ} [Fact p.Prime] {rels : RelatorFamily d r} {depth : Fin r → ℕ}
    (h : PHRec p rels depth) :
    FiniteHilbertRecurrence d depth
      (presentedHilbertSequence p rels) :=
  h.2

theorem PHRec.pos_relseries_hilbertbridge
    {d r : ℕ} {p : ℕ} [Fact p.Prime] {rels : RelatorFamily d r}
    {depth : Fin r → ℕ}
    (h : PHRec p rels depth)
    (hbridge : HilbertRecurrenceForces d depth) :
    PRSeries d r depth :=
  hbridge
    (presentedHilbertSequence p rels)
    (PHRec.finiteHilbertRecurrence h)

/--
The full presentation-level data currently expected to feed the
Golod--Shafarevich argument.

The filtered Fox data supplies the relator-depth control needed for the
associated-graded maps.  The concrete Hilbert recurrence packages the
coefficient inequality for the actual augmentation-layer Hilbert sequence.
-/
def PGData {d r : ℕ}
    (p : ℕ) [Fact p.Prime] (rels : RelatorFamily d r) (depth : Fin r → ℕ) : Prop :=
  PFFox p rels depth ∧
    PHRec p rels depth

theorem PGData.gen_rankle_coeffone
    {d r : ℕ} {p : ℕ} [Fact p.Prime] {rels : RelatorFamily d r}
    {depth : Fin r → ℕ}
    (h : PGData p rels depth) :
    d ≤ (presentedHilbertSequence p rels) 1 := by
  let a := presentedHilbertSequence p rels
  have hrec :
      FiniteHilbertRecurrence d depth a :=
    PHRec.finiteHilbertRecurrence h.2
  have hineq : HilbertCoefficientInequality d a depth 1 := hrec.2.1 1
  unfold HilbertCoefficientInequality at hineq
  have hrel : hilbertRelatorTerm a depth 1 = 0 := by
    apply hilbert_relator_depth
    intro i
    have hi : 2 ≤ depth i := h.1.2.1 i
    omega
  have hgen : hilbertGeneratorTerm a 1 = a 0 := by
    simp [hilbertGeneratorTerm]
  rw [hgen, hrel, hrec.1] at hineq
  simpa [a] using hineq

def ExactGolodShafarevich {d r : ℕ}
    (p : ℕ) [Fact p.Prime] (rels : RelatorFamily d r) (depth : Fin r → ℕ) : Prop :=
  PresentationDepthsExact p rels depth ∧
    PGData p rels depth

def PositiveGolodShafarevich {d r : ℕ}
    (p : ℕ) [Fact p.Prime] (rels : RelatorFamily d r) (depth : Fin r → ℕ) : Prop :=
  PGData p rels depth ∧
    PRSeries d r depth

def PresentationGolodShafarevich {d r : ℕ}
    (p : ℕ) [Fact p.Prime] (rels : RelatorFamily d r) (depth : Fin r → ℕ) : Prop :=
  ExactGolodShafarevich p rels depth ∧
    PRSeries d r depth

def MinimalGolodData
    (p : ℕ) (G : Type*) [Group G] (hp : Nat.Prime p) : Prop := by
  letI : Fact p.Prime := ⟨hp⟩
  exact
    ∃ rels : RelatorFamily (generatorRank G) (relationRank G),
      IsMinimalPresentation (G := G) rels ∧
        ∃ depth : Fin (relationRank G) → ℕ,
          PGData p rels depth

/--
A group has the concrete minimal-presentation data with exact relator depths.

This is the shape closest to the classical finite pro-`p` statement: the
chosen minimal presentation comes with exact Zassenhaus depths, and the exact
profile feeds both the filtered Fox interface and the concrete Hilbert
recurrence.
-/
def GSData
    (p : ℕ) (G : Type*) [Group G] (hp : Nat.Prime p) : Prop := by
  letI : Fact p.Prime := ⟨hp⟩
  exact
    ∃ rels : RelatorFamily (generatorRank G) (relationRank G),
      IsMinimalPresentation (G := G) rels ∧
        ∃ depth : Fin (relationRank G) → ℕ,
          ExactGolodShafarevich p rels depth

def GSSeries
    (p : ℕ) (G : Type*) [Group G] (hp : Nat.Prime p) : Prop := by
  letI : Fact p.Prime := ⟨hp⟩
  exact
    ∃ rels : RelatorFamily (generatorRank G) (relationRank G),
      IsMinimalPresentation (G := G) rels ∧
        ∃ depth : Fin (relationRank G) → ℕ,
          PositiveGolodShafarevich p rels depth

/--
Minimal Golod--Shafarevich group data upgrades to positive-series minimal data
once the abstract Hilbert-series bridge is available for the chosen depth
profile.
-/
theorem GSSeries.min_data_hilbertbridge
    {p : ℕ} {G : Type*} [Group G] {hp : Nat.Prime p}
    (h : MinimalGolodData p G hp)
    (hbridge :
      ∀ depth : Fin (relationRank G) → ℕ,
        HilbertRecurrenceForces
          (generatorRank G) depth) :
    GSSeries p G hp := by
  letI : Fact p.Prime := ⟨hp⟩
  rcases h with ⟨rels, hmin, depth, hdata⟩
  exact
    ⟨rels, hmin, depth,
      ⟨hdata,
        PHRec.pos_relseries_hilbertbridge
          hdata.2 (hbridge depth)⟩⟩

/--
A group has a minimal presentation with exact relator depths and positive
depth-counted relation series.
-/
def MGShafar
    (p : ℕ) (G : Type*) [Group G] (hp : Nat.Prime p) : Prop := by
  letI : Fact p.Prime := ⟨hp⟩
  exact
    ∃ rels : RelatorFamily (generatorRank G) (relationRank G),
      IsMinimalPresentation (G := G) rels ∧
        ∃ depth : Fin (relationRank G) → ℕ,
          PresentationGolodShafarevich p rels depth

/-- Exact positive minimal data forgets to positive minimal data. -/
theorem MGShafar.positiveData
    {p : ℕ} {G : Type*} [Group G] {hp : Nat.Prime p}
    (h : MGShafar p G hp) :
    GSSeries p G hp := by
  letI : Fact p.Prime := ⟨hp⟩
  rcases h with ⟨rels, hmin, depth, hdata⟩
  exact
    ⟨rels, hmin, depth,
      ⟨hdata.1.2, hdata.2⟩⟩

theorem
    MGShafar.existsexact_depthspos_relseries
    {p : ℕ} {G : Type*} [Group G] {hp : Nat.Prime p}
    (h : MGShafar p G hp) :
    ∃ rels : RelatorFamily (generatorRank G) (relationRank G),
      IsMinimalPresentation (G := G) rels ∧
        ∃ depth : Fin (relationRank G) → ℕ,
          PresentationDepthsExact p rels depth ∧
            PRSeries (generatorRank G) (relationRank G) depth := by
  letI : Fact p.Prime := ⟨hp⟩
  rcases h with ⟨rels, hmin, depth, hdata⟩
  exact
    ⟨rels, hmin, depth, hdata.1.1, hdata.2⟩

/--
Exact minimal Golod--Shafarevich group data upgrades to exact positive-series
minimal data once the abstract Hilbert-series bridge is available for the
chosen exact depth profile.
-/
theorem MGShafar.exact_data_hilbertbridge
    {p : ℕ} {G : Type*} [Group G] {hp : Nat.Prime p}
    (h : GSData p G hp)
    (hbridge :
      ∀ depth : Fin (relationRank G) → ℕ,
        HilbertRecurrenceForces
          (generatorRank G) depth) :
    MGShafar p G hp := by
  letI : Fact p.Prime := ⟨hp⟩
  rcases h with ⟨rels, hmin, depth, hdata⟩
  exact
    ⟨rels, hmin, depth,
      ⟨hdata,
        PHRec.pos_relseries_hilbertbridge
          hdata.2.2 (hbridge depth)⟩⟩

/--
Exact minimal data plus the Hilbert-series bridge yields exact depths and a
positive relation series for a chosen minimal presentation.
-/
theorem
    GSData.existspos_relseries_hilbertbridge
    {p : ℕ} {G : Type*} [Group G] {hp : Nat.Prime p}
    (h : GSData p G hp)
    (hbridge :
      ∀ depth : Fin (relationRank G) → ℕ,
        HilbertRecurrenceForces
          (generatorRank G) depth) :
    ∃ rels : RelatorFamily (generatorRank G) (relationRank G),
      IsMinimalPresentation (G := G) rels ∧
        ∃ depth : Fin (relationRank G) → ℕ,
          PresentationDepthsExact p rels depth ∧
            PRSeries (generatorRank G) (relationRank G) depth :=
  MGShafar.existsexact_depthspos_relseries
    (MGShafar.exact_data_hilbertbridge
      h hbridge)

end GShafar
end Towers
