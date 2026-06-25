import Submission.ClassField.EulerProducts.PrimeAway
import Submission.ClassField.EulerProducts.RayGroupFiniteness
import Submission.ClassField.DirichletDensity.CharacterOrthogonality
import Submission.ClassField.DirichletDensity.DirichletDensity
import Submission.ClassField.DirichletDensity.PartialEulerProduct
import Submission.ClassField.IdeleCohomology.NormInvariants

/-!
# Chapter VI, Section 4, Theorem 4.8

The definitions here use an actual congruence subgroup
`I^S ⊇ H ⊇ i(K_{m,1})`, its quotient, the prime classes in that quotient,
and the ideal Euler/Dirichlet series value `L(1,chi)`.
-/

namespace Submission.CField.DDensit

open Filter Finset Ideal IsDedekindDomain NumberField Set
open scoped BigOperators nonZeroDivisors
open Submission.CField.RCGroups
open Submission.CField.ARecip
open Submission.CField.EProduc
open Submission.CField.ICohomo

noncomputable section

local instance (p : Prop) : Decidable p := Classical.propDecidable p

universe u

variable (K : Type u) [Field K] [NumberField K]

/-- The finite congruence quotient `I^{S(m)}/H`. -/
abbrev CongruenceClassQuotient (m : Modulus K)
    (H : Subgroup (IdealsPrimeTo (NumberField.RingOfIntegers K) K m.finiteSupport)) :=
  IdealsPrimeTo (NumberField.RingOfIntegers K) K m.finiteSupport ⧸ H

/-- The class of a prime away from the modulus in `I^{S(m)}/H`. -/
def congruencePrimeClass {m : Modulus K}
    (H : Subgroup (IdealsPrimeTo (NumberField.RingOfIntegers K) K m.finiteSupport))
    (p : PrimeAway K m) : CongruenceClassQuotient K m H :=
  QuotientGroup.mk' H (awayIntegralIdeal K p).idealsPrime

/-- Prime ideals represented by elements of `H`. -/
def idealsCongruenceSubgroup (m : Modulus K)
    (H : Subgroup (IdealsPrimeTo (NumberField.RingOfIntegers K) K m.finiteSupport)) :
    Set (HeightOneSpectrum (NumberField.RingOfIntegers K)) :=
  {p | ∃ hp : p ∉ m.finiteSupport,
    (awayIntegralIdeal K ⟨p, hp⟩).idealsPrime ∈ H}

/-- The contribution of the integral ideals of norm `n` to the quotient
character's Dirichlet series. -/
def congruenceLShell {m : Modulus K}
    {H : Subgroup (IdealsPrimeTo (NumberField.RingOfIntegers K) K m.finiteSupport)}
    (chi : CongruenceClassQuotient K m H →* ℂˣ)
    (s : ℂ) (n : ℕ) : ℂ :=
  ∑ I ∈ (Ideal.finite_setOf_absNorm_eq n).toFinset,
    if hI : I ≠ 0 ∧
        ∀ p ∈ m.finiteSupport,
          FractionalIdeal.count K p
            (I : FractionalIdeal (NumberField.RingOfIntegers K)⁰ K) = 0 then
      (chi (QuotientGroup.mk' H
        ({ ideal := I, ne_zero := hI.1, primeTo := hI.2 } :
          IIPrime K m).idealsPrime) : ℂ) *
        (n : ℂ) ^ (-s)
    else 0

/-- Ordered partial sums by increasing ideal norm. -/
def congruenceLPartial {m : Modulus K}
    {H : Subgroup (IdealsPrimeTo (NumberField.RingOfIntegers K) K m.finiteSupport)}
    (chi : CongruenceClassQuotient K m H →* ℂˣ)
    (s : ℂ) (N : ℕ) : ℂ :=
  ∑ n ∈ range N, congruenceLShell K chi s n

/-- The source's `L(1,chi)`: the limit of the ideal Dirichlet series in its
ordinary norm ordering.  This deliberately does not use `tsum`, which would
incorrectly demand unconditional (hence absolute) convergence at `1`. -/
def congruenceLValue {m : Modulus K}
    {H : Subgroup (IdealsPrimeTo (NumberField.RingOfIntegers K) K m.finiteSupport)}
    (chi : CongruenceClassQuotient K m H →* ℂˣ) : ℂ :=
  limUnder atTop (fun N ↦ congruenceLPartial K chi 1 N)

/-- The source's nonvanishing alternative for all nontrivial quotient
characters. -/
def LValuesNonzero (m : Modulus K)
    (H : Subgroup (IdealsPrimeTo (NumberField.RingOfIntegers K) K m.finiteSupport)) :
    Prop :=
  ∀ chi : CongruenceClassQuotient K m H →* ℂˣ, chi ≠ 1 →
    congruenceLValue K chi ≠ 0

/-- **Theorem VI.4.8 (source statement).** -/
def CongruenceDensityFormula : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K]
    (m : Modulus K)
    (H : Subgroup (IdealsPrimeTo (NumberField.RingOfIntegers K) K m.finiteSupport)),
    rayPrincipalSubgroup K m ≤ H →
    PrimeDirichletDensity K (idealsCongruenceSubgroup K m H)
      (if LValuesNonzero K m H
        then (1 : ℝ) / H.index else 0)

/-- The ordered ideal `L`-series at a variable argument. -/
def congruenceLSeries {m : Modulus K}
    {H : Subgroup (IdealsPrimeTo (NumberField.RingOfIntegers K) K m.finiteSupport)}
    (chi : CongruenceClassQuotient K m H →* ℂˣ) (s : ℂ) : ℂ :=
  limUnder atTop (fun N ↦ congruenceLPartial K chi s N)

@[simp]
lemma congruence_l_series {m : Modulus K}
    {H : Subgroup (IdealsPrimeTo (NumberField.RingOfIntegers K) K m.finiteSupport)}
    (chi : CongruenceClassQuotient K m H →* ℂˣ) :
    congruenceLSeries K chi 1 = congruenceLValue K chi :=
  rfl

/-- The character-weighted reciprocal-prime series occurring after taking
the logarithm of the Euler product.  Primes dividing the modulus contribute
zero. -/
def congruenceCharacterSum {m : Modulus K}
    {H : Subgroup (IdealsPrimeTo (NumberField.RingOfIntegers K) K m.finiteSupport)}
    (chi : CongruenceClassQuotient K m H →* ℂˣ) (s : ℝ) : ℂ :=
  ∑' p : HeightOneSpectrum (NumberField.RingOfIntegers K),
    if hp : p ∉ m.finiteSupport then
      (chi (congruencePrimeClass K H ⟨p, hp⟩) : ℂ) *
        (Real.rpow (p.asIdeal.absNorm : ℝ) (-s) : ℂ)
    else 0

/-- Finiteness of the congruence quotient.  It follows algebraically from
`rayPrincipalSubgroup K m ≤ H` and finiteness of the ray class group, but the
current ray-class API exposes that finiteness only as the bridge used in
Corollary 2.11. -/
def CongruenceFinitenessBridge : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K]
    (m : Modulus K)
    (H : Subgroup (IdealsPrimeTo (NumberField.RingOfIntegers K) K m.finiteSupport)),
    rayPrincipalSubgroup K m ≤ H → Finite (CongruenceClassQuotient K m H)

/-- The weighted version of Lemma 4.3 needed here.  Proposition 2.7 supplies
the Euler product; the proof of Lemma 4.3 supplies the locally summable
quadratic logarithmic remainder.  The remaining unavailable interface is the
ordered ideal-series/product identification for quotient characters. -/
def CongruenceEulerLog : Prop :=
  ∀ (_h27 : LocalHerbrandFormula.{u})
    (_h43 : (∀ u : ℕ → ℝ,
          (∀ j, 2 ≤ u j) →
          (∀ δ ε : ℝ, 0 < δ → 0 < ε →
            TendstoUniformlyOn (partialEulerProduct u)
              (eulerProduct u) atTop (dirichletRegion 1 δ ε)) →
          PartialEulerConclusion u))
    (K : Type u) [Field K] [NumberField K]
    (m : Modulus K)
    (H : Subgroup (IdealsPrimeTo (NumberField.RingOfIntegers K) K m.finiteSupport))
    (_hH : rayPrincipalSubgroup K m ≤ H)
    (chi : CongruenceClassQuotient K m H →* ℂˣ),
    BoundedDifferenceNear
      (fun s ↦ (Complex.log (congruenceLSeries K chi (s : ℂ))).re)
      (fun s ↦ (congruenceCharacterSum K chi s).re)

/-- The continuation/order interface at `s=1`.  Corollary 2.11 gives the
holomorphic continuation for nontrivial ray-class characters.  Factoring a
quotient character through the ray class group and comparing the two ordered
ideal series gives the orders below.  The trivial character has coefficient
`+1` (the Dedekind-zeta pole), while a nontrivial character has coefficient
the negative of its vanishing order. -/
def CongruenceLLog : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K]
    (_h211 : (∀ (m : Modulus K) (chi : RayClassGroup K m →* ℂˣ), chi ≠ 1 →
          RayFinitenessConclusion K m chi))
    (m : Modulus K)
    (H : Subgroup (IdealsPrimeTo (NumberField.RingOfIntegers K) K m.finiteSupport))
    (_hH : rayPrincipalSubgroup K m ≤ H)
    [Finite (CongruenceClassQuotient K m H)],
    ∃ order : (CongruenceClassQuotient K m H →* ℂˣ) → ℕ,
      (∀ chi, chi ≠ 1 →
        (order chi = 0 ↔ congruenceLValue K chi ≠ 0)) ∧
      ∀ chi,
        BoundedDifferenceNear
          (fun s ↦ (Complex.log
            (congruenceLSeries K chi (s : ℂ))).re)
          (fun s ↦ (if chi = 1 then (1 : ℝ) else -(order chi : ℝ)) *
            Real.log (1 / (s - 1)))

/-- The analytic rearrangement of the absolutely convergent prime sums.
The supplied pointwise character-orthogonality identity is the only
algebraic input; the conclusion just exchanges its finite character sum with
the prime sum and identifies the indicator of the identity class with the
literal set of primes represented by `H`. -/
def CongruenceSummationBridge : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K]
    (m : Modulus K)
    (H : Subgroup (IdealsPrimeTo (NumberField.RingOfIntegers K) K m.finiteSupport))
    [Finite (CongruenceClassQuotient K m H)]
    [Fintype (CongruenceClassQuotient K m H →* ℂˣ)],
    (∀ a : CongruenceClassQuotient K m H,
      ∑ chi : CongruenceClassQuotient K m H →* ℂˣ, (chi a : ℂ) =
        if a = 1 then (H.index : ℂ) else 0) →
    ∃ ε > 0, ∀ s ∈ Set.Ioo (1 : ℝ) (1 + ε),
      ∑ chi : CongruenceClassQuotient K m H →* ℂˣ,
          (congruenceCharacterSum K chi s).re =
        (H.index : ℝ) *
          primeReciprocalSum K
            (idealsCongruenceSubgroup K m H) s

/-- Symmetry of Milne's bounded-difference relation. -/
lemma difference_near_symm
    {f g : ℝ → ℝ} (h : BoundedDifferenceNear f g) :
    BoundedDifferenceNear g f := by
  obtain ⟨ε, hε, B, hB⟩ := h
  refine ⟨ε, hε, |B|, fun s hs ↦ ?_⟩
  have hle : |f s - g s| ≤ |B| := (hB s hs).trans (le_abs_self B)
  simpa [abs_sub_comm] using hle

/-- Transitivity of bounded difference. -/
lemma difference_near_trans
    {f g h : ℝ → ℝ}
    (hfg : BoundedDifferenceNear f g)
    (hgh : BoundedDifferenceNear g h) :
    BoundedDifferenceNear f h := by
  obtain ⟨ε₁, hε₁, B₁, hB₁⟩ := hfg
  obtain ⟨ε₂, hε₂, B₂, hB₂⟩ := hgh
  refine ⟨min ε₁ ε₂, lt_min hε₁ hε₂, |B₁| + |B₂|, fun s hs ↦ ?_⟩
  have hs₁ : s ∈ Set.Ioo (1 : ℝ) (1 + ε₁) :=
    ⟨hs.1, by linarith [hs.2, min_le_left ε₁ ε₂]⟩
  have hs₂ : s ∈ Set.Ioo (1 : ℝ) (1 + ε₂) :=
    ⟨hs.1, by linarith [hs.2, min_le_right ε₁ ε₂]⟩
  calc
    |f s - h s| = |(f s - g s) + (g s - h s)| := by ring_nf
    _ ≤ |f s - g s| + |g s - h s| := abs_add_le _ _
    _ ≤ |B₁| + |B₂| := add_le_add
      ((hB₁ s hs₁).trans (le_abs_self B₁))
      ((hB₂ s hs₂).trans (le_abs_self B₂))

/-- Bounded difference is preserved by scalar multiplication. -/
lemma difference_near_const
    (c : ℝ) {f g : ℝ → ℝ}
    (h : BoundedDifferenceNear f g) :
    BoundedDifferenceNear (fun s ↦ c * f s) (fun s ↦ c * g s) := by
  obtain ⟨ε, hε, B, hB⟩ := h
  refine ⟨ε, hε, |c| * |B|, fun s hs ↦ ?_⟩
  change |c * f s - c * g s| ≤ |c| * |B|
  rw [← mul_sub, abs_mul]
  exact mul_le_mul (le_rfl) ((hB s hs).trans (le_abs_self B))
    (abs_nonneg _) (abs_nonneg _)

/-- Finite sums preserve bounded difference. -/
lemma difference_near_finset
    {ι : Type*} (t : Finset ι) (f g : ι → ℝ → ℝ)
    (h : ∀ i ∈ t, BoundedDifferenceNear (f i) (g i)) :
    BoundedDifferenceNear
      (fun s ↦ ∑ i ∈ t, f i s) (fun s ↦ ∑ i ∈ t, g i s) := by
  classical
  induction t using Finset.induction_on with
  | empty =>
      exact ⟨1, by norm_num, 0, by simp⟩
  | @insert a t ha ih =>
      have ha' := h a (Finset.mem_insert_self a t)
      have ht' := ih fun i hi ↦ h i (Finset.mem_insert_of_mem hi)
      obtain ⟨ε₁, hε₁, B₁, hB₁⟩ := ha'
      obtain ⟨ε₂, hε₂, B₂, hB₂⟩ := ht'
      refine ⟨min ε₁ ε₂, lt_min hε₁ hε₂, |B₁| + |B₂|, fun s hs ↦ ?_⟩
      have hs₁ : s ∈ Set.Ioo (1 : ℝ) (1 + ε₁) :=
        ⟨hs.1, by linarith [hs.2, min_le_left ε₁ ε₂]⟩
      have hs₂ : s ∈ Set.Ioo (1 : ℝ) (1 + ε₂) :=
        ⟨hs.1, by linarith [hs.2, min_le_right ε₁ ε₂]⟩
      change |(∑ i ∈ insert a t, f i s) -
          ∑ i ∈ insert a t, g i s| ≤ |B₁| + |B₂|
      rw [sum_insert ha, sum_insert ha]
      calc
        |(f a s + ∑ i ∈ t, f i s) - (g a s + ∑ i ∈ t, g i s)| =
            |(f a s - g a s) +
              ((∑ i ∈ t, f i s) - ∑ i ∈ t, g i s)| := by ring_nf
        _ ≤ |f a s - g a s| +
            |(∑ i ∈ t, f i s) - ∑ i ∈ t, g i s| := abs_add_le _ _
        _ ≤ |B₁| + |B₂| := add_le_add
          ((hB₁ s hs₁).trans (le_abs_self B₁))
          ((hB₂ s hs₂).trans (le_abs_self B₂))

/-- Exact equality on a right neighborhood gives bounded difference zero. -/
lemma bounded_difference_near
    {f g : ℝ → ℝ} {ε : ℝ} (hε : 0 < ε)
    (h : ∀ s ∈ Set.Ioo (1 : ℝ) (1 + ε), f s = g s) :
    BoundedDifferenceNear f g := by
  exact ⟨ε, hε, 0, fun s hs ↦ by simp [h s hs]⟩

/-- Character orthogonality in the exact unit-valued form used by the
congruence quotient. -/
lemma sum_congruence_characters
    {G : Type*} [CommGroup G] [Finite G] [Fintype (G →* ℂˣ)] (a : G) :
    ∑ chi : G →* ℂˣ, (chi a : ℂ) =
      if a = 1 then (Nat.card G : ℂ) else 0 := by
  let e := (CommGroup.monoidHom_mulEquiv_of_hasEnoughRootsOfUnity G ℂ).some
  letI : Finite (G →* ℂˣ) := Finite.of_equiv G e.symm.toEquiv
  classical
  by_cases ha : a = 1
  · subst a
    rw [if_pos rfl]
    simp only [map_one, Units.val_one, sum_const, card_univ, nsmul_eq_mul,
      mul_one, Nat.cast_inj]
    rw [Fintype.card_eq_nat_card,
      CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity G ℂ]
  · rw [if_neg ha]
    obtain ⟨chi₁, hchi₁⟩ :=
      CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity G ℂ ha
    have hchi₁' : (chi₁ a : ℂ) ≠ 1 := by
      intro h
      exact hchi₁ (Units.ext h)
    apply eq_zero_of_mul_eq_self_left hchi₁'
    simp only [Finset.mul_sum, ← Units.val_mul]
    exact Fintype.sum_bijective _ (Group.mulLeft_bijective chi₁) _ _ fun _ ↦ rfl

/-- For a finite congruence quotient, the number of complex characters is
the subgroup index. -/
lemma congruence_characters_index
    {K : Type u} [Field K] [NumberField K]
    {m : Modulus K}
    (H : Subgroup (IdealsPrimeTo (NumberField.RingOfIntegers K) K m.finiteSupport))
    [Finite (CongruenceClassQuotient K m H)] :
    Nat.card (CongruenceClassQuotient K m H →* ℂˣ) = H.index := by
  rw [CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity,
    H.index_eq_card]

/-- The exact pointwise orthogonality formula used before exchanging the
finite character sum with the prime series. -/
lemma congruence_character_orthogonality
    {K : Type u} [Field K] [NumberField K]
    {m : Modulus K}
    (H : Subgroup (IdealsPrimeTo (NumberField.RingOfIntegers K) K m.finiteSupport))
    [Finite (CongruenceClassQuotient K m H)]
    [Fintype (CongruenceClassQuotient K m H →* ℂˣ)]
    (a : CongruenceClassQuotient K m H) :
    ∑ chi : CongruenceClassQuotient K m H →* ℂˣ, (chi a : ℂ) =
      if a = 1 then (H.index : ℂ) else 0 := by
  rw [sum_congruence_characters]
  congr 2

/-- The analytic bridges, character orthogonality, and nonnegativity of
Dirichlet density imply the full dichotomy in Theorem 4.8. -/
theorem congruence_analytic_bridges
    (hfinite : CongruenceFinitenessBridge.{u})
    (h27 : LocalHerbrandFormula.{u})
    (h43 : (∀ u : ℕ → ℝ,
          (∀ j, 2 ≤ u j) →
          (∀ δ ε : ℝ, 0 < δ → 0 < ε →
            TendstoUniformlyOn (partialEulerProduct u)
              (eulerProduct u) atTop (dirichletRegion 1 δ ε)) →
          PartialEulerConclusion u))
    (h211 : ∀ (K : Type u) [Field K] [NumberField K],
      (∀ (m : Modulus K) (chi : RayClassGroup K m →* ℂˣ), chi ≠ 1 →
            RayFinitenessConclusion K m chi))
    (hEulerLog : CongruenceEulerLog.{u})
    (hLogOrder : CongruenceLLog.{u})
    (hPrimeSum : CongruenceSummationBridge.{u})
    (hDensityNonnegative :
      ∀ (K : Type u) [Field K] [NumberField K]
        (T : Set (HeightOneSpectrum (NumberField.RingOfIntegers K))) (δ : ℝ),
        PrimeDirichletDensity K T δ → 0 ≤ δ) :
    CongruenceDensityFormula.{u} := by
  intro K _ _ m H hH
  let G := CongruenceClassQuotient K m H
  letI : Finite G := hfinite K m H hH
  let dualEquiv :=
    (CommGroup.monoidHom_mulEquiv_of_hasEnoughRootsOfUnity G ℂ).some
  letI : Finite (G →* ℂˣ) := Finite.of_equiv G dualEquiv.symm.toEquiv
  letI : Fintype (G →* ℂˣ) := Fintype.ofFinite _
  letI : DecidableEq (G →* ℂˣ) := Classical.decEq _
  obtain ⟨order, horderZero, horderAsymptotic⟩ :=
    hLogOrder K (h211 K) m H hH
  let nontrivialCharacters : Finset (G →* ℂˣ) := Finset.univ.erase 1
  let totalOrder : ℕ := ∑ chi ∈ nontrivialCharacters, order chi
  let logL : (G →* ℂˣ) → ℝ → ℝ := fun chi s ↦
    (Complex.log (congruenceLSeries K chi (s : ℂ))).re
  let primeSum : (G →* ℂˣ) → ℝ → ℝ := fun chi s ↦
    (congruenceCharacterSum K chi s).re
  let kernel : ℝ → ℝ := fun s ↦ Real.log (1 / (s - 1))
  have hLogPrimeSum : BoundedDifferenceNear
      (fun s ↦ ∑ chi : G →* ℂˣ, logL chi s)
      (fun s ↦ ∑ chi : G →* ℂˣ, primeSum chi s) := by
    simpa only [Finset.sum_filter, Finset.mem_univ, true_and] using
      difference_near_finset Finset.univ logL primeSum
        (fun chi _ ↦ hEulerLog h27 h43 K m H hH chi)
  obtain ⟨εPrime, hεPrime, hPrimeEq⟩ :=
    hPrimeSum K m H (congruence_character_orthogonality H)
  have hPrimeOrthogonality : BoundedDifferenceNear
      (fun s ↦ ∑ chi : G →* ℂˣ, primeSum chi s)
      (fun s ↦ (H.index : ℝ) *
        primeReciprocalSum K
          (idealsCongruenceSubgroup K m H) s) := by
    apply bounded_difference_near hεPrime
    intro s hs
    simpa only [primeSum] using hPrimeEq s hs
  have hLogPrime : BoundedDifferenceNear
      (fun s ↦ ∑ chi : G →* ℂˣ, logL chi s)
      (fun s ↦ (H.index : ℝ) *
        primeReciprocalSum K
          (idealsCongruenceSubgroup K m H) s) :=
    difference_near_trans hLogPrimeSum hPrimeOrthogonality
  have hLogOrderSum : BoundedDifferenceNear
      (fun s ↦ ∑ chi : G →* ℂˣ, logL chi s)
      (fun s ↦ ∑ chi : G →* ℂˣ,
        (if chi = 1 then (1 : ℝ) else -(order chi : ℝ)) * kernel s) := by
    simpa only [Finset.sum_filter, Finset.mem_univ, true_and, logL, kernel] using
      difference_near_finset Finset.univ
        (fun chi s ↦ logL chi s)
        (fun chi s ↦
          (if chi = 1 then (1 : ℝ) else -(order chi : ℝ)) * kernel s)
        (fun chi _ ↦ horderAsymptotic chi)
  have hcoefficient :
      (∑ chi : G →* ℂˣ,
        (if chi = 1 then (1 : ℝ) else -(order chi : ℝ))) =
          1 - (totalOrder : ℝ) := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (1 : G →* ℂˣ))]
    simp only [if_pos, nontrivialCharacters, totalOrder]
    rw [Finset.sum_congr rfl (fun chi hchi ↦ by
      rw [if_neg (Finset.ne_of_mem_erase hchi)])]
    simp only [Finset.sum_neg_distrib]
    push_cast
    ring
  have hLogOrderSum' : BoundedDifferenceNear
      (fun s ↦ ∑ chi : G →* ℂˣ, logL chi s)
      (fun s ↦ (1 - (totalOrder : ℝ)) * kernel s) := by
    convert hLogOrderSum using 1
    funext s
    rw [← Finset.sum_mul, hcoefficient]
  have hScaled : BoundedDifferenceNear
      (fun s ↦ (H.index : ℝ) *
        primeReciprocalSum K
          (idealsCongruenceSubgroup K m H) s)
      (fun s ↦ (1 - (totalOrder : ℝ)) * kernel s) :=
    difference_near_trans
      (difference_near_symm hLogPrime) hLogOrderSum'
  have hindexNe : H.index ≠ 0 := by
    rw [H.index_eq_card]
    exact Nat.card_pos.ne'
  have hindexPos : (0 : ℝ) < H.index := by
    exact_mod_cast Nat.pos_of_ne_zero hindexNe
  have hDensityFormula : PrimeDirichletDensity K
      (idealsCongruenceSubgroup K m H)
      ((1 - (totalOrder : ℝ)) / H.index) := by
    have hscaled' := difference_near_const
      ((H.index : ℝ)⁻¹) hScaled
    rw [PrimeDirichletDensity]
    convert hscaled' using 1 <;> funext s
    · field_simp
    · dsimp [kernel]
      field_simp
  have hnonnegative : 0 ≤ (1 - (totalOrder : ℝ)) / H.index :=
    hDensityNonnegative K _ _ hDensityFormula
  let P := LValuesNonzero K m H
  letI : Decidable P := Classical.propDecidable P
  by_cases hP : P
  · rw [if_pos hP]
    have htotalOrder : totalOrder = 0 := by
      dsimp only [totalOrder]
      apply Finset.sum_eq_zero
      intro chi hchi
      have hne : chi ≠ 1 := Finset.ne_of_mem_erase hchi
      exact (horderZero chi hne).2 (hP chi hne)
    simpa [htotalOrder] using hDensityFormula
  · rw [if_neg hP]
    have hexists : ∃ chi : G →* ℂˣ,
        chi ≠ 1 ∧ congruenceLValue K chi = 0 := by
      simpa [P, LValuesNonzero, not_forall,
        Classical.not_imp] using hP
    obtain ⟨chi, hchi, hvalue⟩ := hexists
    have horderPos : 0 < order chi := by
      exact Nat.pos_of_ne_zero fun hz ↦
        (horderZero chi hchi).1 hz (by simp [hvalue])
    have hchiMem : chi ∈ nontrivialCharacters := by
      exact Finset.mem_erase.mpr ⟨hchi, Finset.mem_univ chi⟩
    have htotalLower : 1 ≤ totalOrder := by
      exact horderPos.trans_le (Finset.single_le_sum
        (fun x _ ↦ Nat.zero_le (order x)) hchiMem)
    have htotalUpper : totalOrder ≤ 1 := by
      have hnumerator : 0 ≤ 1 - (totalOrder : ℝ) := by
        rcases div_nonneg_iff.mp hnonnegative with h | h
        · exact h.1
        · exact False.elim ((not_lt_of_ge h.2) hindexPos)
      exact_mod_cast (by linarith : (totalOrder : ℝ) ≤ 1)
    have htotalOrder : totalOrder = 1 := le_antisymm htotalUpper htotalLower
    simpa [htotalOrder] using hDensityFormula

end

end Submission.CField.DDensit
