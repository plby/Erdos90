import Towers.NumberTheory.Density.SplittingPrimeDensity
import Towers.ClassField.ArtinReciprocity.ArtinMap

/-!
# Chapter VI, Section 3: density of splitting primes

Milne formulates this section using polar density.  The Towers ANT layer has
instead developed natural density of prime ideals, including finite-set
invariance, disjoint-union additivity, and the exact conditional Chebotarev
statement.  The results below record the corresponding (stronger when
available) natural-density statements.

The analytic proof of Chebotarev, comparison with polar density, passage to a
non-Galois extension through its Galois closure, and the polynomial and Bauer
corollaries are not yet available.  No axioms are introduced for them.
-/

namespace Towers.CField.PDensit

open Filter IsDedekindDomain NumberField
open Towers.NumberTheory.Milne
open Towers.CField.ARecip

noncomputable section

variable (K : Type*) [Field K] [NumberField K]

/-- **Proposition VI.3.1(a), natural-density form.** All finite primes have
density one. -/
theorem all_primes_density :
    PNDensit K Set.univ 1 := by
  unfold PNDensit
  have hpos : ∀ᶠ N in atTop, 0 < primeIdealCount K Set.univ N :=
    (tendsto_univ_top K).eventually (eventually_gt_atTop 0)
  apply (tendsto_congr' ?_).2 tendsto_const_nhds
  filter_upwards [hpos] with N hN
  simp [Nat.ne_of_gt hN]

/-- **Proposition VI.3.1(c), natural-density form.** Density is additive on
disjoint unions. -/
theorem natural_density_disjoint
    {S T : Set (HeightOneSpectrum (𝓞 K))} {δ ε : ℝ}
    (hS : PNDensit K S δ)
    (hT : PNDensit K T ε)
    (hST : Disjoint S T) :
    PNDensit K (S ∪ T) (δ + ε) :=
  hS.union_of_disjoint K hT hST

/-- **Proposition VI.3.1(e), natural-density form.** A finite set of finite
primes has density zero. -/
theorem primes_natural_density
    {S : Set (HeightOneSpectrum (𝓞 K))} (hS : S.Finite) :
    PNDensit K S 0 :=
  prime_natural_density K hS

/-- The natural-density analogue of Corollary VI.3.3 for sets differing by
only finitely many primes. -/
theorem density_congr_diff
    {S T : Set (HeightOneSpectrum (𝓞 K))} {δ : ℝ}
    (hS : PNDensit K S δ)
    (hST : (S \ T).Finite) (hTS : (T \ S).Finite) :
    PNDensit K T δ :=
  hS.congr_fin_diff K hST hTS

variable (L : Type*) [Field L] [NumberField L] [Algebra K L]

/-- **Theorem VI.3.4, Galois-case infinitude consequence.** Once the stated
density `1 / [L : K]` is supplied, infinitely many primes split completely. -/
theorem splittingPrimes_infinite
    (hdensity : PNDensit K (splittingPrimes K L)
      (1 / Module.finrank K L : ℝ)) :
    (splittingPrimes K L).Infinite :=
  splitting_primes_density K L hdensity

/-- The unconditional rational-base infinitude consequence available in the
Milne layer: completely split rational primes are unbounded in a finite
Galois number field. -/
theorem splitting_primes_unbounded
    (M : Type*) [Field M] [NumberField M] [Algebra ℚ M] [IsGalois ℚ M] :
    ∀ N : ℕ, ∃ p > N, Nat.Prime p ∧ Towers.splitsCompletely M p :=
  splitting_completely_unbounded M

omit [NumberField L] in
/-- **Example VI.3.7, cyclic cubic numerical specialization.** A splitting
set of density `1 / [L : K]` has density `1/3` when the Galois closure has
degree three. -/
theorem cyclic_cubic
    (hdegree : Module.finrank K L = 3)
    (hdensity : PNDensit K (splittingPrimes K L)
      (1 / Module.finrank K L : ℝ)) :
    PNDensit K (splittingPrimes K L) (1 / 3) := by
  simpa [hdegree] using hdensity

omit [NumberField L] in
/-- **Example VI.3.7, symmetric cubic numerical specialization.** The same
formula gives density `1/6` when the Galois closure has degree six. -/
theorem symmetric_cubic
    (hdegree : Module.finrank K L = 6)
    (hdensity : PNDensit K (splittingPrimes K L)
      (1 / Module.finrank K L : ℝ)) :
    PNDensit K (splittingPrimes K L) (1 / 6) := by
  simpa [hdegree] using hdensity

/-- In the abelian Chebotarev statement, every Frobenius element occurs at
some finite prime (indeed at infinitely many). -/
theorem abelian_frobenius_occurs
    {G : Type*} [CommGroup G] [Finite G]
    {frobeniusClass : HeightOneSpectrum (𝓞 K) → Option (ConjClasses G)}
    (hcheb : ChebotarevDensityProperty K frobeniusClass) (sigma : G) :
    ∃ p, frobeniusClass p = some (ConjClasses.mk sigma) := by
  have hdensity := abelian_density_chebotarev K hcheb sigma
  have hinfinite :
      (primesFrobeniusClass K frobeniusClass
        (ConjClasses.mk sigma)).Infinite := by
    apply Set.Infinite.prime_ideal_densi K hdensity
    exact one_div_pos.mpr (Nat.cast_pos.mpr Nat.card_pos)
  rcases hinfinite.nonempty with ⟨p, hp⟩
  exact ⟨p, hp⟩

/-- **Corollary VI.3.8, generator form.** If every Galois element occurs as
the Frobenius of a pointed unramified prime, the Artin map on the free group
of those primes is surjective. -/
theorem artin_surjective_frobenius
    {R S G : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [CommGroup G] [Finite G] [MulSemiringAction G S] [IsGaloisGroup G R S]
    (hFrob : Function.Surjective
      (fun P : PUPrime R S ↦ P.frobenius (G := G))) :
    Function.Surjective (artinMap (R := R) (S := S) (G := G)) := by
  intro g
  rcases hFrob g.toMul with ⟨P, hP⟩
  refine ⟨FreeAbelianGroup.of P, ?_⟩
  simp [hP]

end

end Towers.CField.PDensit
