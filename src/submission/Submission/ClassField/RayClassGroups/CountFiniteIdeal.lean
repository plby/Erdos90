import Submission.ClassField.RayClassGroups.ZeroCoprimeForbidden
import Submission.ClassField.ArtinReciprocity.Statements
import Submission.NumberTheory.Ideals.FractionalIdealBasics

/-!
# Chapter V, Section 1, Proposition 1.6 (source statement)

This file gives the literal ray-class formulation: integral representatives,
and the criterion for two integral representatives to define the same ray
class.
-/

namespace Submission.CField.RCGroups

open IsDedekindDomain NumberField
open scoped nonZeroDivisors

noncomputable section

variable (K : Type*) [Field K] [NumberField K]

namespace Modulus

private theorem count_finiteIdeal (m : Modulus K)
    (p : HeightOneSpectrum (𝓞 K)) :
    FractionalIdeal.count K p
        (m.finiteIdeal : FractionalIdeal (𝓞 K)⁰ K) = (m.finite p : ℤ) := by
  classical
  rw [finiteIdeal, Finsupp.prod]
  change FractionalIdeal.count K p
      (FractionalIdeal.coeIdealHom (𝓞 K)⁰ K
        (∏ q ∈ m.finite.support, q.asIdeal ^ m.finite q)) = _
  rw [map_prod]
  simp_rw [map_pow]
  rw [FractionalIdeal.count_prod]
  · simp [FractionalIdeal.count_pow, FractionalIdeal.count_maximal]
    all_goals omega
  · intro q hq
    exact pow_ne_zero _ (FractionalIdeal.coeIdeal_ne_zero.mpr q.ne_bot)

end Modulus

private theorem count_coe_coprime
    {A B : Ideal (𝓞 K)} (hA : A ≠ 0) (hB : B ≠ 0)
    (hcop : IsCoprime A B) {p : HeightOneSpectrum (𝓞 K)}
    (hcount : FractionalIdeal.count K p (A : FractionalIdeal (𝓞 K)⁰ K) =
      FractionalIdeal.count K p (B : FractionalIdeal (𝓞 K)⁰ K)) :
    FractionalIdeal.count K p (A : FractionalIdeal (𝓞 K)⁰ K) = 0 := by
  by_contra hne
  have hneA :
      (Associates.mk p.asIdeal).count (Associates.mk A).factors ≠ 0 := by
    simpa [FractionalIdeal.count_coe K p hA] using hne
  have hneB :
      (Associates.mk p.asIdeal).count (Associates.mk B).factors ≠ 0 := by
    have : FractionalIdeal.count K p (B : FractionalIdeal (𝓞 K)⁰ K) ≠ 0 := by
      rwa [← hcount]
    simpa [FractionalIdeal.count_coe K p hB] using this
  have hpA : p.asIdeal ∣ A :=
    (Associates.count_ne_zero_iff_dvd hA p.irreducible).mp hneA
  have hpB : p.asIdeal ∣ B :=
    (Associates.count_ne_zero_iff_dvd hB p.irreducible).mp hneB
  exact p.isPrime.ne_top
    (Ideal.isUnit_iff.mp (hcop.isUnit_of_dvd' hpA hpB))

/-- A nonzero fractional ideal prime to `S` is a quotient of two nonzero
integral ideals that are themselves prime to `S`. -/
private theorem integral_ideal_prime
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (I : IdealsPrimeTo (𝓞 K) K S) :
    ∃ A B : Ideal (𝓞 K), A ≠ 0 ∧ B ≠ 0 ∧
      (∀ p ∈ S,
        FractionalIdeal.count K p (A : FractionalIdeal (𝓞 K)⁰ K) = 0) ∧
      (∀ p ∈ S,
        FractionalIdeal.count K p (B : FractionalIdeal (𝓞 K)⁰ K) = 0) ∧
      (I.1 : FractionalIdeal (𝓞 K)⁰ K) =
        (B : FractionalIdeal (𝓞 K)⁰ K) /
          (A : FractionalIdeal (𝓞 K)⁰ K) := by
  obtain ⟨a, J, ha, hI⟩ :=
    FractionalIdeal.exists_eq_spanSingleton_mul
      (I.1 : FractionalIdeal (𝓞 K)⁰ K)
  let A₀ : Ideal (𝓞 K) := Ideal.span {a}
  let B₀ : Ideal (𝓞 K) := J
  have hA₀ : A₀ ≠ 0 := by
    simpa [A₀, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
  have hB₀ : B₀ ≠ 0 := by
    intro hJ
    have hJ' : J = 0 := by simpa [B₀] using hJ
    subst J
    apply I.1.ne_zero
    simp at hI
  have hIdiv :
      (I.1 : FractionalIdeal (𝓞 K)⁰ K) =
        (B₀ : FractionalIdeal (𝓞 K)⁰ K) /
          (A₀ : FractionalIdeal (𝓞 K)⁰ K) := by
    rw [show (A₀ : FractionalIdeal (𝓞 K)⁰ K) =
        FractionalIdeal.spanSingleton (𝓞 K)⁰ (algebraMap (𝓞 K) K a) by
          simp [A₀],
      FractionalIdeal.div_spanSingleton]
    simpa [B₀] using hI
  let C : Ideal (𝓞 K) := A₀ ⊔ B₀
  have hC : C ≠ 0 := by
    intro hC
    apply hA₀
    exact le_bot_iff.mp ((show A₀ ≤ C from le_sup_left).trans hC.le)
  obtain ⟨A, hAfac⟩ : C ∣ A₀ := Ideal.dvd_iff_le.mpr le_sup_left
  obtain ⟨B, hBfac⟩ : C ∣ B₀ := Ideal.dvd_iff_le.mpr le_sup_right
  have hA : A ≠ 0 := by
    intro h
    apply hA₀
    simpa [h] using hAfac
  have hB : B ≠ 0 := by
    intro h
    apply hB₀
    simpa [h] using hBfac
  have hcop : IsCoprime A B := by
    rw [Ideal.isCoprime_iff_sup_eq]
    apply mul_left_cancel₀ hC
    rw [Ideal.mul_sup, ← hAfac, ← hBfac]
    simp [C]
  have hcountA₀B₀ (p : HeightOneSpectrum (𝓞 K)) (hp : p ∈ S) :
      FractionalIdeal.count K p (A₀ : FractionalIdeal (𝓞 K)⁰ K) =
        FractionalIdeal.count K p (B₀ : FractionalIdeal (𝓞 K)⁰ K) := by
    have hcountI :
        FractionalIdeal.count K p
          (I.1 : FractionalIdeal (𝓞 K)⁰ K) = 0 := I.property p hp
    rw [hIdiv, div_eq_mul_inv,
      FractionalIdeal.count_mul K p
        (FractionalIdeal.coeIdeal_ne_zero.mpr hB₀)
        (inv_ne_zero (FractionalIdeal.coeIdeal_ne_zero.mpr hA₀)),
      FractionalIdeal.count_inv] at hcountI
    omega
  have hcountAB (p : HeightOneSpectrum (𝓞 K)) (hp : p ∈ S) :
      FractionalIdeal.count K p (A : FractionalIdeal (𝓞 K)⁰ K) =
        FractionalIdeal.count K p (B : FractionalIdeal (𝓞 K)⁰ K) := by
    have h := hcountA₀B₀ p hp
    rw [hAfac, hBfac, FractionalIdeal.coeIdeal_mul,
      FractionalIdeal.coeIdeal_mul,
      FractionalIdeal.count_mul K p
        (FractionalIdeal.coeIdeal_ne_zero.mpr hC)
        (FractionalIdeal.coeIdeal_ne_zero.mpr hA),
      FractionalIdeal.count_mul K p
        (FractionalIdeal.coeIdeal_ne_zero.mpr hC)
        (FractionalIdeal.coeIdeal_ne_zero.mpr hB)] at h
    omega
  have hAwayA (p : HeightOneSpectrum (𝓞 K)) (hp : p ∈ S) :
      FractionalIdeal.count K p (A : FractionalIdeal (𝓞 K)⁰ K) = 0 :=
    count_coe_coprime K hA hB hcop (hcountAB p hp)
  have hAwayB (p : HeightOneSpectrum (𝓞 K)) (hp : p ∈ S) :
      FractionalIdeal.count K p (B : FractionalIdeal (𝓞 K)⁰ K) = 0 := by
    rw [← hcountAB p hp]
    exact hAwayA p hp
  refine ⟨A, B, hA, hB, hAwayA, hAwayB, ?_⟩
  rw [hIdiv, hAfac, hBfac, FractionalIdeal.coeIdeal_mul,
    FractionalIdeal.coeIdeal_mul,
    mul_div_mul_left _ _ (FractionalIdeal.coeIdeal_ne_zero.mpr hC)]

omit [NumberField K] in
private theorem ideal_ne_zero (m : Modulus K) : m.finiteIdeal ≠ 0 := by
  classical
  rw [Modulus.finiteIdeal, Finsupp.prod]
  exact Finset.prod_ne_zero_iff.mpr fun p _ ↦ pow_ne_zero _ p.ne_bot

private theorem coprime_ideal_prime
    (m : Modulus K) {A : Ideal (𝓞 K)} (hA : A ≠ 0)
    (hAway : ∀ p ∈ m.finiteSupport,
      FractionalIdeal.count K p (A : FractionalIdeal (𝓞 K)⁰ K) = 0) :
    IsCoprime A m.finiteIdeal := by
  classical
  rw [Modulus.finiteIdeal, Finsupp.prod]
  apply IsCoprime.prod_right
  intro p hp
  apply IsCoprime.pow_right
  rw [Ideal.isCoprime_iff_sup_eq]
  by_contra htop
  have heq : p.asIdeal = A ⊔ p.asIdeal :=
    p.isMaximal.eq_of_le htop le_sup_right
  have hAle : A ≤ p.asIdeal := by
    rw [heq]
    exact le_sup_left
  have hpdiv : p.asIdeal ∣ A := Ideal.dvd_iff_le.mpr hAle
  have hcount :
      FractionalIdeal.count K p (A : FractionalIdeal (𝓞 K)⁰ K) ≠ 0 := by
    simpa [FractionalIdeal.count_coe K p hA] using
      (Associates.count_ne_zero_iff_dvd hA p.irreducible).mpr hpdiv
  exact hcount (hAway p (by simpa [Modulus.finiteSupport] using hp))

omit [NumberField K] in
/-- CRT plus a sum-of-squares adjustment gives an integral element in `A`
which is one modulo the finite part and positive at every real place in the
modulus. -/
private theorem positive_one_mod
    (m : Modulus K) {A : Ideal (𝓞 K)} (hA : A ≠ 0)
    (hcop : IsCoprime A m.finiteIdeal) :
    ∃ c : 𝓞 K, c ≠ 0 ∧ c ∈ A ∧ c - 1 ∈ m.finiteIdeal ∧
      Modulus.PositiveInfinity (K := K) m (algebraMap (𝓞 K) K c) := by
  obtain ⟨x, hxA, y, hym, hxy⟩ := hcop.exists
  have hprod : A * m.finiteIdeal ≠ 0 :=
    mul_ne_zero hA (ideal_ne_zero K m)
  obtain ⟨q, hqprod, hq⟩ : ∃ q ∈ A * m.finiteIdeal, q ≠ 0 := by
    obtain ⟨q, hqprod, hq0⟩ :=
      SetLike.exists_of_lt (bot_lt_iff_ne_bot.mpr hprod)
    exact ⟨q, hqprod, by simpa using hq0⟩
  have hqA : q ∈ A := Ideal.mul_le_right hqprod
  have hqm : q ∈ m.finiteIdeal := Ideal.mul_le_left hqprod
  have hxsub : x - 1 ∈ m.finiteIdeal := by
    have : x - 1 = -y := by rw [← hxy]; ring
    rw [this]
    exact m.finiteIdeal.neg_mem hym
  have hx2sub : x ^ 2 - 1 ∈ m.finiteIdeal := by
    have heq : x ^ 2 - 1 = (x - 1) * (x + 1) := by ring
    rw [heq]
    simpa [mul_comm] using m.finiteIdeal.mul_mem_left (x + 1) hxsub
  have hmemA (n : ℕ) : x ^ 2 + n * q ^ 2 ∈ A := by
    exact A.add_mem (by simpa [pow_two] using A.mul_mem_left x hxA)
      (A.mul_mem_left n (by simpa [pow_two] using A.mul_mem_left q hqA))
  have hsubm (n : ℕ) : x ^ 2 + n * q ^ 2 - 1 ∈ m.finiteIdeal := by
    have heq : x ^ 2 + n * q ^ 2 - 1 = (x ^ 2 - 1) + n * q ^ 2 := by ring
    rw [heq]
    exact m.finiteIdeal.add_mem hx2sub
      (m.finiteIdeal.mul_mem_left n
        (by simpa [pow_two] using m.finiteIdeal.mul_mem_left q hqm))
  have hpositive (n : ℕ) (hn : 0 < n) :
      Modulus.PositiveInfinity (K := K) m
        (algebraMap (𝓞 K) K (x ^ 2 + n * q ^ 2)) := by
    intro w hw
    let f : 𝓞 K →+* ℝ :=
      (NumberField.InfinitePlace.embedding_of_isReal w.property).comp
      (algebraMap (𝓞 K) K)
    have hf_inj : Function.Injective f :=
      (NumberField.InfinitePlace.embedding_of_isReal w.property).injective.comp
        NumberField.RingOfIntegers.coe_injective
    have hfq : f q ≠ 0 := (map_ne_zero_iff f hf_inj).mpr hq
    change 0 < f (x ^ 2 + n * q ^ 2)
    rw [map_add, map_pow, map_mul, map_natCast, map_pow]
    positivity
  let c₁ : 𝓞 K := x ^ 2 + 1 * q ^ 2
  by_cases hc₁ : c₁ ≠ 0
  · refine ⟨c₁, hc₁, ?_, ?_, ?_⟩
    · simpa [c₁] using hmemA 1
    · simpa [c₁] using hsubm 1
    · simpa [c₁] using hpositive 1 (by omega)
  · let c₂ : 𝓞 K := x ^ 2 + 2 * q ^ 2
    have hc₂ : c₂ ≠ 0 := by
      intro hc₂
      have hc₁' : c₁ = 0 := not_ne_iff.mp hc₁
      have hq2 : q ^ 2 = 0 := by
        dsimp [c₁, c₂] at hc₁' hc₂
        linear_combination hc₂ - hc₁'
      exact hq (sq_eq_zero_iff.mp hq2)
    refine ⟨c₂, hc₂, ?_, ?_, ?_⟩
    · simpa [c₂] using hmemA 2
    · simpa [c₂] using hsubm 2
    · simpa [c₂] using hpositive 2 (by omega)

private theorem congruent_one_sub
    (m : Modulus K) {c : 𝓞 K} (hc : c ≠ 0)
    (hsub : c - 1 ∈ m.finiteIdeal) :
    Submission.CField.ARecip.CongruentOneFinite K m
      (Units.mk0 (algebraMap (𝓞 K) K c)
        ((map_ne_zero_iff (algebraMap (𝓞 K) K)
          NumberField.RingOfIntegers.coe_injective).mpr hc)) := by
  let cu : Kˣ := Units.mk0 (algebraMap (𝓞 K) K c)
    ((map_ne_zero_iff (algebraMap (𝓞 K) K)
      NumberField.RingOfIntegers.coe_injective).mpr hc)
  by_cases hc1 : algebraMap (𝓞 K) K c = 1
  · left
    apply Units.ext
    exact hc1
  · right
    intro p hp
    have hcsub : c - 1 ≠ 0 := by
      intro h
      apply hc1
      have : c = 1 := sub_eq_zero.mp h
      simp [this]
    have hspan : Ideal.span {c - 1} ≤ m.finiteIdeal :=
      m.finiteIdeal.span_singleton_le_iff_mem.mpr hsub
    have hle :
        (Ideal.span {c - 1} : FractionalIdeal (𝓞 K)⁰ K) ≤
          (m.finiteIdeal : FractionalIdeal (𝓞 K)⁰ K) :=
      (FractionalIdeal.coeIdeal_le_coeIdeal K).mpr hspan
    have hne :
        (Ideal.span {c - 1} : FractionalIdeal (𝓞 K)⁰ K) ≠ 0 :=
      FractionalIdeal.coeIdeal_ne_zero.mpr (by
        simpa [Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot])
    have hcount := FractionalIdeal.count_mono K p hne hle
    rw [Modulus.count_finiteIdeal] at hcount
    simpa [cu, map_sub, FractionalIdeal.coeIdeal_span_singleton] using hcount

private theorem finite_ideal_count
    (m : Modulus K) {z : 𝓞 K} (hz : z ≠ 0)
    (hcount : ∀ p ∈ m.finiteSupport, (m.finite p : ℤ) ≤
      FractionalIdeal.count K p
        (FractionalIdeal.spanSingleton (𝓞 K)⁰ (algebraMap (𝓞 K) K z))) :
    z ∈ m.finiteIdeal := by
  classical
  have hspan : Ideal.span {z} ≠ (0 : Ideal (𝓞 K)) := by
    simpa [Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
  have hpair : ((m.finite.support : Finset (HeightOneSpectrum (𝓞 K))) :
      Set (HeightOneSpectrum (𝓞 K))).Pairwise
      (Function.onFun IsCoprime fun p ↦ p.asIdeal ^ m.finite p) := by
    intro p hp q hq hpq
    exact HeightOneSpectrum.isCoprime_pow_of_ne p q hpq _ _
  apply (m.finiteIdeal.span_singleton_le_iff_mem).mp
  rw [Modulus.finiteIdeal, Finsupp.prod,
    Ideal.prod_eq_iInf_of_pairwise_isCoprime hpair]
  refine le_iInf fun p ↦ le_iInf fun hp ↦ ?_
  apply Ideal.dvd_iff_le.mp
  rw [← Associates.mk_dvd_mk, Associates.mk_pow]
  simp only [Associates.dvd_eq_le]
  rw [Associates.prime_pow_dvd_iff_le (Associates.mk_ne_zero.mpr hspan)
    p.associates_irreducible]
  have hp' : p ∈ m.finiteSupport := by
    simpa [Modulus.finiteSupport] using hp
  have hc := hcount p hp'
  rw [← FractionalIdeal.coeIdeal_span_singleton,
    FractionalIdeal.count_coe K p hspan] at hc
  exact_mod_cast hc

private theorem nonzero_multiplier_mod
    (m : Modulus K) {b₀ : 𝓞 K}
    (hcop : IsCoprime (Ideal.span {b₀}) m.finiteIdeal) :
    ∃ d : 𝓞 K, d ≠ 0 ∧ d * b₀ - 1 ∈ m.finiteIdeal := by
  by_cases hm : m.finiteIdeal = ⊤
  · exact ⟨1, one_ne_zero, by simp [hm]⟩
  · obtain ⟨u, hu, v, hv, huv⟩ := hcop.exists
    obtain ⟨d, hd⟩ := Ideal.mem_span_singleton.mp hu
    have hu0 : u ≠ 0 := by
      intro hu0
      have hv1 : v = 1 := by simpa [hu0] using huv
      have : (1 : 𝓞 K) ∈ m.finiteIdeal := by simpa [hv1] using hv
      exact hm ((Ideal.eq_top_iff_one m.finiteIdeal).mpr this)
    have hd0 : d ≠ 0 := by
      intro hd0
      apply hu0
      rcases hd with rfl
      simp [hd0]
    refine ⟨d, hd0, ?_⟩
    have huv' : d * b₀ + v = 1 := by
      rcases hd with rfl
      simpa [mul_comm] using huv
    have : d * b₀ - 1 = -v := by rw [← huv']; ring
    rw [this]
    exact m.finiteIdeal.neg_mem hv

private theorem principal_count_sub
    (m : Modulus K) {c : 𝓞 K} (hc : c ≠ 0)
    (hsub : c - 1 ∈ m.finiteIdeal) {p : HeightOneSpectrum (𝓞 K)}
    (hp : p ∈ m.finiteSupport) :
    FractionalIdeal.count K p
      (FractionalIdeal.spanSingleton (𝓞 K)⁰ (algebraMap (𝓞 K) K c)) = 0 := by
  classical
  have hmpos : m.finite p ≠ 0 :=
    by simpa [Modulus.finiteSupport] using hp
  have hmle : m.finiteIdeal ≤ p.asIdeal := by
    rw [Modulus.finiteIdeal, Finsupp.prod]
    exact Ideal.prod_le_inf.trans
      ((Finset.inf_le (f := fun q ↦ q.asIdeal ^ m.finite q) hp).trans
        (Ideal.pow_le_self hmpos))
  have hspan : Ideal.span {c} ≠ 0 := by
    simpa [Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
  rw [← FractionalIdeal.coeIdeal_span_singleton,
    FractionalIdeal.count_coe K p hspan]
  norm_cast
  rw [← not_ne_iff]
  intro hcount
  have hpdiv : p.asIdeal ∣ Ideal.span {c} :=
    (Associates.count_ne_zero_iff_dvd hspan p.irreducible).mp hcount
  have hcP : c ∈ p.asIdeal :=
    (Ideal.dvd_iff_le.mp hpdiv) (Ideal.mem_span_singleton_self c)
  have hsubP : c - 1 ∈ p.asIdeal := hmle hsub
  have hone : (1 : 𝓞 K) ∈ p.asIdeal := by
    have := p.asIdeal.sub_mem hcP hsubP
    simpa using this
  exact p.isPrime.ne_top ((Ideal.eq_top_iff_one p.asIdeal).mpr hone)

private def elementIntegralMod
    (m : Modulus K) (c : 𝓞 K) (hc : c ≠ 0)
    (hsub : c - 1 ∈ m.finiteIdeal) :
    ElementsPrimeTo (𝓞 K) K m.finiteSupport :=
  ⟨Units.mk0 (algebraMap (𝓞 K) K c)
      ((map_ne_zero_iff (algebraMap (𝓞 K) K)
        NumberField.RingOfIntegers.coe_injective).mpr hc),
    by
      intro p hp
      simpa only [coe_toPrincipalIdeal] using
        principal_count_sub K m hc hsub hp⟩

private theorem element_mod_ray
    (m : Modulus K) (c : 𝓞 K) (hc : c ≠ 0)
    (hsub : c - 1 ∈ m.finiteIdeal)
    (hpos : Modulus.PositiveInfinity (K := K) m
      (algebraMap (𝓞 K) K c)) :
    Submission.CField.ARecip.IsRayElement K m
      (elementIntegralMod K m c hc hsub) := by
  exact ⟨congruent_one_sub K m hc hsub, hpos⟩

/-- An element of `K_{m,1}` is a quotient of nonzero integral elements,
each congruent to one modulo `m₀`, and having the same sign at every real
place in the modulus. -/
private theorem integral_ray_fraction
    (m : Modulus K) (x : ElementsPrimeTo (𝓞 K) K m.finiteSupport)
    (hx : Submission.CField.ARecip.IsRayElement K m x) :
    ∃ a b : 𝓞 K, a ≠ 0 ∧ b ≠ 0 ∧
      (x.1 : K) = algebraMap (𝓞 K) K a / algebraMap (𝓞 K) K b ∧
      a - 1 ∈ m.finiteIdeal ∧ b - 1 ∈ m.finiteIdeal ∧
      ∀ w ∈ m.infinite,
        0 < NumberField.InfinitePlace.embedding_of_isReal w.property
            (algebraMap (𝓞 K) K a) *
          NumberField.InfinitePlace.embedding_of_isReal w.property
            (algebraMap (𝓞 K) K b) := by
  obtain ⟨a₀, b₀, ha₀, hb₀, hfrac, hAwayA, hAwayB⟩ :=
    integral_fraction_prime (𝓞 K) K m.finiteSupport x
  have hspanB : Ideal.span {b₀} ≠ (0 : Ideal (𝓞 K)) := by
    simpa [Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
  have hcopB : IsCoprime (Ideal.span {b₀}) m.finiteIdeal :=
    coprime_ideal_prime K m hspanB (by
      intro p hp
      simpa [FractionalIdeal.coeIdeal_span_singleton] using hAwayB p hp)
  obtain ⟨d, hd, hbsub⟩ := nonzero_multiplier_mod K m hcopB
  have habsub : a₀ - b₀ ∈ m.finiteIdeal := by
    by_cases hab : a₀ = b₀
    · simp [hab]
    · apply finite_ideal_count K m (sub_ne_zero.mpr hab)
      intro p hp
      rcases hx.1 with hxone | hxcount
      · exfalso
        have hxfield : (x.1 : K) = 1 := congrArg (fun u : Kˣ ↦ (u : K)) hxone
        have habmap : algebraMap (𝓞 K) K a₀ = algebraMap (𝓞 K) K b₀ := by
          have hbmap : algebraMap (𝓞 K) K b₀ ≠ 0 :=
            (map_ne_zero_iff (algebraMap (𝓞 K) K)
              NumberField.RingOfIntegers.coe_injective).mpr hb₀
          calc
            algebraMap (𝓞 K) K a₀ =
                (algebraMap (𝓞 K) K a₀ /
                  algebraMap (𝓞 K) K b₀) * algebraMap (𝓞 K) K b₀ := by
                    exact (div_mul_cancel₀ _ hbmap).symm
            _ = (x.1 : K) * algebraMap (𝓞 K) K b₀ := by rw [hfrac]
            _ = algebraMap (𝓞 K) K b₀ := by rw [hxfield, one_mul]
        exact hab (NumberField.RingOfIntegers.coe_injective habmap)
      · have hfield :
            (x.1 : K) - 1 =
              algebraMap (𝓞 K) K (a₀ - b₀) /
                algebraMap (𝓞 K) K b₀ := by
            have hbmap : algebraMap (𝓞 K) K b₀ ≠ 0 :=
              (map_ne_zero_iff (algebraMap (𝓞 K) K)
                NumberField.RingOfIntegers.coe_injective).mpr hb₀
            rw [hfrac, map_sub]
            field_simp [hbmap]
        have hdiff :
            FractionalIdeal.spanSingleton (𝓞 K)⁰
                (algebraMap (𝓞 K) K (a₀ - b₀)) ≠ 0 :=
          FractionalIdeal.spanSingleton_ne_zero_iff.mpr
            ((map_ne_zero_iff (algebraMap (𝓞 K) K)
              NumberField.RingOfIntegers.coe_injective).mpr (sub_ne_zero.mpr hab))
        have hbspan :
            FractionalIdeal.spanSingleton (𝓞 K)⁰
                (algebraMap (𝓞 K) K b₀) ≠ 0 :=
          FractionalIdeal.spanSingleton_ne_zero_iff.mpr
            ((map_ne_zero_iff (algebraMap (𝓞 K) K)
              NumberField.RingOfIntegers.coe_injective).mpr hb₀)
        have hbound := hxcount p hp
        rw [hfield, ← FractionalIdeal.spanSingleton_div_spanSingleton,
          div_eq_mul_inv,
          FractionalIdeal.count_mul K p hdiff (inv_ne_zero hbspan),
          FractionalIdeal.count_inv, hAwayB p hp, neg_zero, add_zero] at hbound
        exact hbound
  let a : 𝓞 K := d * a₀
  let b : 𝓞 K := d * b₀
  have ha : a ≠ 0 := mul_ne_zero hd ha₀
  have hb : b ≠ 0 := mul_ne_zero hd hb₀
  have hasub : a - 1 ∈ m.finiteIdeal := by
    have hdab : d * (a₀ - b₀) ∈ m.finiteIdeal :=
      m.finiteIdeal.mul_mem_left d habsub
    have heq : a - 1 = d * (a₀ - b₀) + (b - 1) := by
      simp [a, b]
      ring
    rw [heq]
    exact m.finiteIdeal.add_mem hdab hbsub
  refine ⟨a, b, ha, hb, ?_, hasub, hbsub, ?_⟩
  · simp only [a, b]
    rw [map_mul, map_mul, mul_div_mul_left _ _
      ((map_ne_zero_iff (algebraMap (𝓞 K) K)
        NumberField.RingOfIntegers.coe_injective).mpr hd)]
    exact hfrac
  · intro w hw
    let f : 𝓞 K →+* ℝ :=
      (NumberField.InfinitePlace.embedding_of_isReal w.property).comp
        (algebraMap (𝓞 K) K)
    have hfinj : Function.Injective f :=
      (NumberField.InfinitePlace.embedding_of_isReal w.property).injective.comp
        NumberField.RingOfIntegers.coe_injective
    have hfd : f d ≠ 0 := (map_ne_zero_iff f hfinj).mpr hd
    have hfb : f b₀ ≠ 0 := (map_ne_zero_iff f hfinj).mpr hb₀
    have hxpos := hx.2 w hw
    change 0 < NumberField.InfinitePlace.embedding_of_isReal w.property (x.1 : K) at hxpos
    rw [hfrac] at hxpos
    have hxpos' : 0 < f a₀ / f b₀ := by
      simpa only [f, RingHom.comp_apply, map_div₀] using hxpos
    have habpos : 0 < f a₀ * f b₀ := by
      rcases (div_pos_iff.mp hxpos') with h | h
      · exact mul_pos h.1 h.2
      · exact mul_pos_of_neg_of_neg h.1 h.2
    change 0 < f a * f b
    simp only [a, b, map_mul]
    nlinarith [sq_pos_of_ne_zero hfd]

/-- A nonzero integral ideal prime to the finite support of `m`. -/
structure IIPrime (m : Modulus K) where
  ideal : Ideal (𝓞 K)
  ne_zero : ideal ≠ 0
  primeTo : ∀ p ∈ m.finiteSupport,
    FractionalIdeal.count K p
      (ideal : FractionalIdeal (𝓞 K)⁰ K) = 0

namespace IIPrime

def idealsPrime {m : Modulus K} (I : IIPrime K m) :
    IdealsPrimeTo (𝓞 K) K m.finiteSupport :=
  ⟨Units.mk0 (I.ideal : FractionalIdeal (𝓞 K)⁰ K)
      (FractionalIdeal.coeIdeal_ne_zero.mpr I.ne_zero), I.primeTo⟩

@[simp]
theorem ideals_prime_val {m : Modulus K} (I : IIPrime K m) :
    ((I.idealsPrime :
      (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) = I.ideal := rfl

end IIPrime

/-- The ray class group `C_m = I^S / i(K_{m,1})`. -/
abbrev RayClassGroup (m : Modulus K) :=
  IdealsPrimeTo (𝓞 K) K m.finiteSupport ⧸
    Submission.CField.ARecip.rayPrincipalSubgroup K m

/-- The ray class represented by a nonzero integral ideal prime to `m`. -/
def rayIntegralIdeal {m : Modulus K} (I : IIPrime K m) :
    RayClassGroup K m :=
  QuotientGroup.mk'
    (Submission.CField.ARecip.rayPrincipalSubgroup K m)
    I.idealsPrime

private def IntegralRayFraction (m : Modulus K)
    (g : IdealsPrimeTo (𝓞 K) K m.finiteSupport) : Prop :=
  ∃ a b : 𝓞 K, a ≠ 0 ∧ b ≠ 0 ∧
    a - 1 ∈ m.finiteIdeal ∧ b - 1 ∈ m.finiteIdeal ∧
    (∀ w ∈ m.infinite,
      0 < NumberField.InfinitePlace.embedding_of_isReal w.property
          (algebraMap (𝓞 K) K a) *
        NumberField.InfinitePlace.embedding_of_isReal w.property
          (algebraMap (𝓞 K) K b)) ∧
    (g.1 : FractionalIdeal (𝓞 K)⁰ K) =
      FractionalIdeal.spanSingleton (𝓞 K)⁰ (algebraMap (𝓞 K) K a) /
        FractionalIdeal.spanSingleton (𝓞 K)⁰ (algebraMap (𝓞 K) K b)

private theorem ray_principal_fraction
    (m : Modulus K)
    {g : IdealsPrimeTo (𝓞 K) K m.finiteSupport}
    (hg : g ∈ Submission.CField.ARecip.rayPrincipalSubgroup K m) :
    IntegralRayFraction K m g := by
  let s : Set (IdealsPrimeTo (𝓞 K) K m.finiteSupport) :=
    {I | ∃ x : ElementsPrimeTo (𝓞 K) K m.finiteSupport,
      Submission.CField.ARecip.IsRayElement K m x ∧
        principalIdealPrime (𝓞 K) K m.finiteSupport x = I}
  change g ∈ Subgroup.closure s at hg
  refine Subgroup.closure_induction (k := s)
    (p := fun g _ ↦ IntegralRayFraction K m g) ?_ ?_ ?_ ?_ hg
  · intro g hggen
    change ∃ x : ElementsPrimeTo (𝓞 K) K m.finiteSupport,
      Submission.CField.ARecip.IsRayElement K m x ∧
        principalIdealPrime (𝓞 K) K m.finiteSupport x = g at hggen
    obtain ⟨x, hx, rfl⟩ := hggen
    obtain ⟨a, b, ha, hb, hfrac, hasub, hbsub, hsign⟩ :=
      integral_ray_fraction K m x hx
    refine ⟨a, b, ha, hb, hasub, hbsub, hsign, ?_⟩
    change (toPrincipalIdeal (𝓞 K) K x.1 : FractionalIdeal (𝓞 K)⁰ K) = _
    rw [coe_toPrincipalIdeal, hfrac,
      ← FractionalIdeal.spanSingleton_div_spanSingleton]
  · refine ⟨1, 1, one_ne_zero, one_ne_zero, ?_, ?_, ?_, ?_⟩
    · simp
    · simp
    · intro w hw
      simp
    · simp
  · intro g h _ _ hg hh
    obtain ⟨a, b, ha, hb, hasub, hbsub, hsign, hfrac⟩ := hg
    obtain ⟨c, d, hc, hd, hcsub, hdsub, hsign', hfrac'⟩ := hh
    refine ⟨a * c, b * d, mul_ne_zero ha hc, mul_ne_zero hb hd, ?_, ?_, ?_, ?_⟩
    · have heq : a * c - 1 = a * (c - 1) + (a - 1) := by ring
      rw [heq]
      exact m.finiteIdeal.add_mem (m.finiteIdeal.mul_mem_left a hcsub) hasub
    · have heq : b * d - 1 = b * (d - 1) + (b - 1) := by ring
      rw [heq]
      exact m.finiteIdeal.add_mem (m.finiteIdeal.mul_mem_left b hdsub) hbsub
    · intro w hw
      have h₁ := hsign w hw
      have h₂ := hsign' w hw
      simp only [map_mul]
      nlinarith
    · change (g.1 : FractionalIdeal (𝓞 K)⁰ K) *
        (h.1 : FractionalIdeal (𝓞 K)⁰ K) = _
      rw [hfrac, hfrac', map_mul, map_mul,
        ← FractionalIdeal.spanSingleton_mul_spanSingleton,
        ← FractionalIdeal.spanSingleton_mul_spanSingleton]
      ring
  · intro g _ hg
    obtain ⟨a, b, ha, hb, hasub, hbsub, hsign, hfrac⟩ := hg
    refine ⟨b, a, hb, ha, hbsub, hasub, ?_, ?_⟩
    · intro w hw
      simpa [mul_comm] using hsign w hw
    · change (((g.1 : (FractionalIdeal (𝓞 K)⁰ K)ˣ)⁻¹ :
          (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
        FractionalIdeal (𝓞 K)⁰ K) = _
      rw [Units.val_inv_eq_inv_val, hfrac]
      simp [div_eq_mul_inv]

private theorem mod_ray_element
    (m : Modulus K) {a b : 𝓞 K} (ha : a ≠ 0) (hb : b ≠ 0)
    (hasub : a - 1 ∈ m.finiteIdeal) (hbsub : b - 1 ∈ m.finiteIdeal)
    (hsign : ∀ w ∈ m.infinite,
      0 < NumberField.InfinitePlace.embedding_of_isReal w.property
          (algebraMap (𝓞 K) K a) *
        NumberField.InfinitePlace.embedding_of_isReal w.property
          (algebraMap (𝓞 K) K b)) :
    Submission.CField.ARecip.IsRayElement K m
      (elementIntegralMod K m a ha hasub *
        (elementIntegralMod K m b hb hbsub)⁻¹) := by
  let xa := elementIntegralMod K m a ha hasub
  let xb := elementIntegralMod K m b hb hbsub
  let x : ElementsPrimeTo (𝓞 K) K m.finiteSupport := xa * xb⁻¹
  have hfield : (x.1 : K) =
      algebraMap (𝓞 K) K a / algebraMap (𝓞 K) K b := by
    simp [x, xa, xb, elementIntegralMod, div_eq_mul_inv]
  constructor
  · by_cases hx1 : x.1 = 1
    · exact Or.inl hx1
    · right
      intro p hp
      have hab : a ≠ b := by
        intro hab
        apply hx1
        apply Units.ext
        simp [x, xa, xb, hab]
      have habsub : a - b ∈ m.finiteIdeal := by
        have heq : a - b = (a - 1) - (b - 1) := by ring
        rw [heq]
        exact m.finiteIdeal.sub_mem hasub hbsub
      have hspanDiff : Ideal.span {a - b} ≠ (0 : Ideal (𝓞 K)) := by
        simpa [Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot, sub_ne_zero]
      have hle :
          (Ideal.span {a - b} : FractionalIdeal (𝓞 K)⁰ K) ≤
            (m.finiteIdeal : FractionalIdeal (𝓞 K)⁰ K) :=
        (FractionalIdeal.coeIdeal_le_coeIdeal K).mpr
          (m.finiteIdeal.span_singleton_le_iff_mem.mpr habsub)
      have hbound := FractionalIdeal.count_mono K p
        (FractionalIdeal.coeIdeal_ne_zero.mpr hspanDiff) hle
      rw [Modulus.count_finiteIdeal] at hbound
      have hbcount := principal_count_sub K m hb hbsub hp
      have hfieldSub : (x.1 : K) - 1 =
          algebraMap (𝓞 K) K (a - b) / algebraMap (𝓞 K) K b := by
        have hbmap : algebraMap (𝓞 K) K b ≠ 0 :=
          (map_ne_zero_iff (algebraMap (𝓞 K) K)
            NumberField.RingOfIntegers.coe_injective).mpr hb
        rw [hfield, map_sub]
        field_simp [hbmap]
      rw [hfieldSub, ← FractionalIdeal.spanSingleton_div_spanSingleton,
        div_eq_mul_inv,
        FractionalIdeal.count_mul K p
          (FractionalIdeal.spanSingleton_ne_zero_iff.mpr
            ((map_ne_zero_iff (algebraMap (𝓞 K) K)
              NumberField.RingOfIntegers.coe_injective).mpr (sub_ne_zero.mpr hab)))
          (inv_ne_zero (FractionalIdeal.spanSingleton_ne_zero_iff.mpr
            ((map_ne_zero_iff (algebraMap (𝓞 K) K)
              NumberField.RingOfIntegers.coe_injective).mpr hb))),
        FractionalIdeal.count_inv, hbcount, neg_zero, add_zero]
      simpa [FractionalIdeal.coeIdeal_span_singleton] using hbound
  · intro w hw
    let f : 𝓞 K →+* ℝ :=
      (NumberField.InfinitePlace.embedding_of_isReal w.property).comp
        (algebraMap (𝓞 K) K)
    have hfinj : Function.Injective f :=
      (NumberField.InfinitePlace.embedding_of_isReal w.property).injective.comp
        NumberField.RingOfIntegers.coe_injective
    have hfb : f b ≠ 0 := (map_ne_zero_iff f hfinj).mpr hb
    have hs := hsign w hw
    change 0 < NumberField.InfinitePlace.embedding_of_isReal w.property (x.1 : K)
    rw [hfield, map_div₀]
    change 0 < f a / f b
    rcases (mul_pos_iff.mp hs) with h | h
    · exact div_pos h.1 h.2
    · exact div_pos_of_neg_of_neg h.1 h.2

/-- Two integral prime-to fractions having the same finite residues and the
same signs differ by an element of the ray subgroup.  This is the precise
finite-data comparison needed to prove ray-class finiteness. -/
theorem ray_fraction_ratio
    (m : Modulus K)
    (z : ElementsPrimeTo (𝓞 K) K m.finiteSupport)
    {a b c d : 𝓞 K}
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0)
    (hz : (z.1 : K) =
      (algebraMap (𝓞 K) K a / algebraMap (𝓞 K) K b) /
        (algebraMap (𝓞 K) K c / algebraMap (𝓞 K) K d))
    (hAwayB : ∀ p ∈ m.finiteSupport,
      FractionalIdeal.count K p
        (FractionalIdeal.spanSingleton (𝓞 K)⁰ (algebraMap (𝓞 K) K b)) = 0)
    (hAwayC : ∀ p ∈ m.finiteSupport,
      FractionalIdeal.count K p
        (FractionalIdeal.spanSingleton (𝓞 K)⁰ (algebraMap (𝓞 K) K c)) = 0)
    (hac : a - c ∈ m.finiteIdeal) (hbd : b - d ∈ m.finiteIdeal)
    (hsignAC : ∀ w ∈ m.infinite,
      0 < NumberField.InfinitePlace.embedding_of_isReal w.property
          (algebraMap (𝓞 K) K a) *
        NumberField.InfinitePlace.embedding_of_isReal w.property
          (algebraMap (𝓞 K) K c))
    (hsignBD : ∀ w ∈ m.infinite,
      0 < NumberField.InfinitePlace.embedding_of_isReal w.property
          (algebraMap (𝓞 K) K b) *
        NumberField.InfinitePlace.embedding_of_isReal w.property
          (algebraMap (𝓞 K) K d)) :
    Submission.CField.ARecip.IsRayElement K m z := by
  have hbc : b * c ≠ 0 := mul_ne_zero hb hc
  have hspanBC : Ideal.span {b * c} ≠ (0 : Ideal (𝓞 K)) := by
    intro hspan
    apply hbc
    have hmem : b * c ∈ (0 : Ideal (𝓞 K)) := by
      rw [← hspan]
      exact Ideal.mem_span_singleton_self (b * c)
    simpa using hmem
  have hAwayBC : ∀ p ∈ m.finiteSupport,
      FractionalIdeal.count K p
        (Ideal.span {b * c} : FractionalIdeal (𝓞 K)⁰ K) = 0 := by
    intro p hp
    rw [FractionalIdeal.coeIdeal_span_singleton, map_mul,
      ← FractionalIdeal.spanSingleton_mul_spanSingleton,
      FractionalIdeal.count_mul K p
        (FractionalIdeal.spanSingleton_ne_zero_iff.mpr
          ((map_ne_zero_iff (algebraMap (𝓞 K) K)
            NumberField.RingOfIntegers.coe_injective).mpr hb))
        (FractionalIdeal.spanSingleton_ne_zero_iff.mpr
          ((map_ne_zero_iff (algebraMap (𝓞 K) K)
            NumberField.RingOfIntegers.coe_injective).mpr hc)),
      hAwayB p hp, hAwayC p hp, add_zero]
  have hcop : IsCoprime (Ideal.span {b * c}) m.finiteIdeal :=
    coprime_ideal_prime K m hspanBC hAwayBC
  obtain ⟨e, he, hbcsub⟩ :=
    nonzero_multiplier_mod K m hcop
  let A : 𝓞 K := e * (a * d)
  let B : 𝓞 K := e * (b * c)
  have hA : A ≠ 0 := mul_ne_zero he (mul_ne_zero ha hd)
  have hB : B ≠ 0 := mul_ne_zero he hbc
  have hadbc : a * d - b * c ∈ m.finiteIdeal := by
    have heq : a * d - b * c = d * (a - c) - c * (b - d) := by ring
    rw [heq]
    exact m.finiteIdeal.sub_mem
      (m.finiteIdeal.mul_mem_left d hac)
      (m.finiteIdeal.mul_mem_left c hbd)
  have hBsub : B - 1 ∈ m.finiteIdeal := by
    simpa [B, mul_assoc] using hbcsub
  have hAsub : A - 1 ∈ m.finiteIdeal := by
    have heq : A - 1 = e * (a * d - b * c) + (B - 1) := by
      simp only [A, B]
      ring
    rw [heq]
    exact m.finiteIdeal.add_mem
      (m.finiteIdeal.mul_mem_left e hadbc) hBsub
  have hsignAB : ∀ w ∈ m.infinite,
      0 < NumberField.InfinitePlace.embedding_of_isReal w.property
          (algebraMap (𝓞 K) K A) *
        NumberField.InfinitePlace.embedding_of_isReal w.property
          (algebraMap (𝓞 K) K B) := by
    intro w hw
    let f : 𝓞 K →+* ℝ :=
      (NumberField.InfinitePlace.embedding_of_isReal w.property).comp
        (algebraMap (𝓞 K) K)
    have hfinj : Function.Injective f :=
      (NumberField.InfinitePlace.embedding_of_isReal w.property).injective.comp
        NumberField.RingOfIntegers.coe_injective
    have hfe : f e ≠ 0 := (map_ne_zero_iff f hfinj).mpr he
    have hsq : 0 < f e * f e := mul_self_pos.mpr hfe
    have hacpos : 0 < f a * f c := hsignAC w hw
    have hbdpos : 0 < f b * f d := hsignBD w hw
    change 0 < f A * f B
    rw [map_mul, map_mul, map_mul, map_mul]
    nlinarith [mul_pos hacpos hbdpos]
  let z₀ : ElementsPrimeTo (𝓞 K) K m.finiteSupport :=
    elementIntegralMod K m A hA hAsub *
      (elementIntegralMod K m B hB hBsub)⁻¹
  have hz₀ : Submission.CField.ARecip.IsRayElement K m z₀ :=
    mod_ray_element K m hA hB hAsub hBsub hsignAB
  have hmapA : algebraMap (𝓞 K) K A =
      algebraMap (𝓞 K) K e *
        (algebraMap (𝓞 K) K a * algebraMap (𝓞 K) K d) := by
    simp [A]
  have hmapB : algebraMap (𝓞 K) K B =
      algebraMap (𝓞 K) K e *
        (algebraMap (𝓞 K) K b * algebraMap (𝓞 K) K c) := by
    simp [B]
  have heMap : algebraMap (𝓞 K) K e ≠ 0 :=
    (map_ne_zero_iff (algebraMap (𝓞 K) K)
      NumberField.RingOfIntegers.coe_injective).mpr he
  have haMap : algebraMap (𝓞 K) K a ≠ 0 :=
    (map_ne_zero_iff (algebraMap (𝓞 K) K)
      NumberField.RingOfIntegers.coe_injective).mpr ha
  have hbMap : algebraMap (𝓞 K) K b ≠ 0 :=
    (map_ne_zero_iff (algebraMap (𝓞 K) K)
      NumberField.RingOfIntegers.coe_injective).mpr hb
  have hcMap : algebraMap (𝓞 K) K c ≠ 0 :=
    (map_ne_zero_iff (algebraMap (𝓞 K) K)
      NumberField.RingOfIntegers.coe_injective).mpr hc
  have hdMap : algebraMap (𝓞 K) K d ≠ 0 :=
    (map_ne_zero_iff (algebraMap (𝓞 K) K)
      NumberField.RingOfIntegers.coe_injective).mpr hd
  have hfield : (z₀.1 : K) =
      (algebraMap (𝓞 K) K a / algebraMap (𝓞 K) K b) /
        (algebraMap (𝓞 K) K c / algebraMap (𝓞 K) K d) := by
    have halg : algebraMap (𝓞 K) K A / algebraMap (𝓞 K) K B =
        (algebraMap (𝓞 K) K a / algebraMap (𝓞 K) K b) /
          (algebraMap (𝓞 K) K c / algebraMap (𝓞 K) K d) := by
      rw [hmapA, hmapB]
      field_simp
    simpa [z₀, elementIntegralMod, div_eq_mul_inv] using halg
  have hzz₀ : z = z₀ := by
    apply Subtype.ext
    apply Units.ext
    exact hz.trans hfield.symm
  rwa [hzz₀]

/-- Proposition 1.6, first clause: every ray class has an integral ideal
representative. -/
theorem every_ray_representative
    (m : Modulus K) (C : RayClassGroup K m) :
    ∃ I : IIPrime K m, rayIntegralIdeal K I = C := by
  let H := Submission.CField.ARecip.rayPrincipalSubgroup K m
  obtain ⟨I, rfl⟩ := QuotientGroup.mk'_surjective H C
  obtain ⟨A, B, hA, hB, hAwayA, hAwayB, hI⟩ :=
    integral_ideal_prime K m.finiteSupport I
  have hcop := coprime_ideal_prime K m hA hAwayA
  obtain ⟨c, hc, hcA, hcsub, hcpos⟩ :=
    positive_one_mod K m hA hcop
  have hspan : Ideal.span {c} ≠ (0 : Ideal (𝓞 K)) := by
    simpa [Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
  obtain ⟨D, hDfac⟩ : A ∣ Ideal.span {c} :=
    Ideal.dvd_iff_le.mpr (A.span_singleton_le_iff_mem.mpr hcA)
  have hD : D ≠ 0 := by
    intro hD
    apply hspan
    simpa [hD] using hDfac
  have hAwayC (p : HeightOneSpectrum (𝓞 K)) (hp : p ∈ m.finiteSupport) :
      FractionalIdeal.count K p
        (Ideal.span {c} : FractionalIdeal (𝓞 K)⁰ K) = 0 := by
    simpa [FractionalIdeal.coeIdeal_span_singleton] using
      principal_count_sub K m hc hcsub hp
  have hAwayD (p : HeightOneSpectrum (𝓞 K)) (hp : p ∈ m.finiteSupport) :
      FractionalIdeal.count K p (D : FractionalIdeal (𝓞 K)⁰ K) = 0 := by
    have h := hAwayC p hp
    rw [hDfac, FractionalIdeal.coeIdeal_mul,
      FractionalIdeal.count_mul K p
        (FractionalIdeal.coeIdeal_ne_zero.mpr hA)
        (FractionalIdeal.coeIdeal_ne_zero.mpr hD),
      hAwayA p hp] at h
    simpa using h
  let J : Ideal (𝓞 K) := B * D
  have hJ : J ≠ 0 := mul_ne_zero hB hD
  have hAwayJ (p : HeightOneSpectrum (𝓞 K)) (hp : p ∈ m.finiteSupport) :
      FractionalIdeal.count K p (J : FractionalIdeal (𝓞 K)⁰ K) = 0 := by
    have h := FractionalIdeal.count_mul K p
      (FractionalIdeal.coeIdeal_ne_zero.mpr hB)
      (FractionalIdeal.coeIdeal_ne_zero.mpr hD)
    rw [hAwayB p hp, hAwayD p hp, add_zero] at h
    simpa [J, FractionalIdeal.coeIdeal_mul] using h
  let Jint : IIPrime K m := ⟨J, hJ, hAwayJ⟩
  refine ⟨Jint, ?_⟩
  symm
  change (QuotientGroup.mk' H I = QuotientGroup.mk' H Jint.idealsPrime)
  apply (QuotientGroup.eq).2
  have hmul :
      (FractionalIdeal.spanSingleton (𝓞 K)⁰ (algebraMap (𝓞 K) K c)) *
          (I.1 : FractionalIdeal (𝓞 K)⁰ K) =
        (J : FractionalIdeal (𝓞 K)⁰ K) := by
    simp only [J]
    rw [hI, ← FractionalIdeal.coeIdeal_span_singleton, hDfac,
      FractionalIdeal.coeIdeal_mul, FractionalIdeal.coeIdeal_mul, div_eq_mul_inv]
    calc
      ((A : FractionalIdeal (𝓞 K)⁰ K) *
          (D : FractionalIdeal (𝓞 K)⁰ K)) *
            ((B : FractionalIdeal (𝓞 K)⁰ K) *
              (A : FractionalIdeal (𝓞 K)⁰ K)⁻¹) =
          ((A : FractionalIdeal (𝓞 K)⁰ K) *
            (A : FractionalIdeal (𝓞 K)⁰ K)⁻¹) *
              ((B : FractionalIdeal (𝓞 K)⁰ K) *
                (D : FractionalIdeal (𝓞 K)⁰ K)) := by ac_rfl
      _ = (B : FractionalIdeal (𝓞 K)⁰ K) *
          (D : FractionalIdeal (𝓞 K)⁰ K) := by
        rw [mul_inv_cancel₀ (FractionalIdeal.coeIdeal_ne_zero.mpr hA), one_mul]
  let x := elementIntegralMod K m c hc hcsub
  have hxray : Submission.CField.ARecip.IsRayElement K m x :=
    element_mod_ray K m c hc hcsub hcpos
  have hprincipal :
      principalIdealPrime (𝓞 K) K m.finiteSupport x ∈ H := by
    apply Subgroup.subset_closure
    exact ⟨x, hxray, rfl⟩
  have hval :
      ((principalIdealPrime (𝓞 K) K m.finiteSupport x).1 :
          (FractionalIdeal (𝓞 K)⁰ K)ˣ) * I.1 = Jint.idealsPrime.1 := by
    apply Units.ext
    simpa [principalIdealPrime, x, elementIntegralMod,
      coe_toPrincipalIdeal, Jint] using hmul
  have hval' :
      principalIdealPrime (𝓞 K) K m.finiteSupport x * I =
        Jint.idealsPrime := by
    apply Subtype.ext
    exact hval
  rw [← hval']
  simpa [H] using hprincipal

/-- Proposition 1.6, second clause: two nonzero integral ideals prime to the
modulus represent the same ray class exactly when they become equal after
multiplication by nonzero integral elements which are both one modulo the
finite part and have the same signs at the real places in the modulus. -/
theorem ideals_same_ray
    (m : Modulus K) (I J : IIPrime K m) :
    rayIntegralIdeal K I = rayIntegralIdeal K J ↔
      ∃ a b : 𝓞 K, a ≠ 0 ∧ b ≠ 0 ∧
        Ideal.span {a} * I.ideal = Ideal.span {b} * J.ideal ∧
        a - 1 ∈ m.finiteIdeal ∧ b - 1 ∈ m.finiteIdeal ∧
        ∀ w ∈ m.infinite,
          0 < NumberField.InfinitePlace.embedding_of_isReal w.property
              (algebraMap (𝓞 K) K a) *
            NumberField.InfinitePlace.embedding_of_isReal w.property
              (algebraMap (𝓞 K) K b) := by
  let H := Submission.CField.ARecip.rayPrincipalSubgroup K m
  constructor
  · intro hclass
    have hmem : I.idealsPrime⁻¹ * J.idealsPrime ∈ H := by
      apply (QuotientGroup.eq).mp
      exact hclass
    obtain ⟨a, b, ha, hb, hasub, hbsub, hsign, hfrac⟩ :=
      ray_principal_fraction K m hmem
    refine ⟨a, b, ha, hb, ?_, hasub, hbsub, hsign⟩
    have hdiv :
        (J.ideal : FractionalIdeal (𝓞 K)⁰ K) /
            (I.ideal : FractionalIdeal (𝓞 K)⁰ K) =
          FractionalIdeal.spanSingleton (𝓞 K)⁰ (algebraMap (𝓞 K) K a) /
            FractionalIdeal.spanSingleton (𝓞 K)⁰ (algebraMap (𝓞 K) K b) := by
      simpa [div_eq_mul_inv, mul_comm] using hfrac
    have hcross := (div_eq_div_iff
      (FractionalIdeal.coeIdeal_ne_zero.mpr I.ne_zero)
      (FractionalIdeal.spanSingleton_ne_zero_iff.mpr
        ((map_ne_zero_iff (algebraMap (𝓞 K) K)
          NumberField.RingOfIntegers.coe_injective).mpr hb))).mp hdiv
    apply FractionalIdeal.coeIdeal_injective (K := K)
    simpa [FractionalIdeal.coeIdeal_mul,
      FractionalIdeal.coeIdeal_span_singleton, mul_comm] using hcross.symm
  · rintro ⟨a, b, ha, hb, hideal, hasub, hbsub, hsign⟩
    let xa := elementIntegralMod K m a ha hasub
    let xb := elementIntegralMod K m b hb hbsub
    let x : ElementsPrimeTo (𝓞 K) K m.finiteSupport := xa * xb⁻¹
    have hxray : Submission.CField.ARecip.IsRayElement K m x := by
      exact mod_ray_element K m ha hb hasub hbsub hsign
    have hprincipal : principalIdealPrime (𝓞 K) K m.finiteSupport x ∈ H := by
      apply Subgroup.subset_closure
      exact ⟨x, hxray, rfl⟩
    have hcross :
        (J.ideal : FractionalIdeal (𝓞 K)⁰ K) *
            FractionalIdeal.spanSingleton (𝓞 K)⁰ (algebraMap (𝓞 K) K b) =
          FractionalIdeal.spanSingleton (𝓞 K)⁰ (algebraMap (𝓞 K) K a) *
            (I.ideal : FractionalIdeal (𝓞 K)⁰ K) := by
      have := congrArg
        (fun L : Ideal (𝓞 K) ↦ (L : FractionalIdeal (𝓞 K)⁰ K)) hideal
      simpa [FractionalIdeal.coeIdeal_mul,
        FractionalIdeal.coeIdeal_span_singleton, mul_comm] using this.symm
    have hdiv :
        (J.ideal : FractionalIdeal (𝓞 K)⁰ K) /
            (I.ideal : FractionalIdeal (𝓞 K)⁰ K) =
          FractionalIdeal.spanSingleton (𝓞 K)⁰ (algebraMap (𝓞 K) K a) /
            FractionalIdeal.spanSingleton (𝓞 K)⁰ (algebraMap (𝓞 K) K b) :=
      (div_eq_div_iff
        (FractionalIdeal.coeIdeal_ne_zero.mpr I.ne_zero)
        (FractionalIdeal.spanSingleton_ne_zero_iff.mpr
          ((map_ne_zero_iff (algebraMap (𝓞 K) K)
            NumberField.RingOfIntegers.coe_injective).mpr hb))).mpr hcross
    have hg : I.idealsPrime⁻¹ * J.idealsPrime =
        principalIdealPrime (𝓞 K) K m.finiteSupport x := by
      have hv : (I.ideal : FractionalIdeal (𝓞 K)⁰ K)⁻¹ *
          (J.ideal : FractionalIdeal (𝓞 K)⁰ K) =
        FractionalIdeal.spanSingleton (𝓞 K)⁰
          ((algebraMap (𝓞 K) K a) / (algebraMap (𝓞 K) K b)) := by
        rw [← FractionalIdeal.spanSingleton_div_spanSingleton]
        simpa [div_eq_mul_inv, mul_comm] using hdiv
      apply Subtype.ext
      apply Units.ext
      simpa [IIPrime.idealsPrime, principalIdealPrime,
        x, xa, xb, elementIntegralMod, coe_toPrincipalIdeal,
        div_eq_mul_inv] using hv
    change QuotientGroup.mk' H I.idealsPrime =
      QuotientGroup.mk' H J.idealsPrime
    apply (QuotientGroup.eq).mpr
    rw [hg]
    exact hprincipal

end

end Submission.CField.RCGroups
