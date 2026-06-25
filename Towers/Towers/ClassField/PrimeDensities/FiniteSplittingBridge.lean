import Towers.ClassField.PrimeDensities.IsGaloisClosure

/-!
# Milne, Class Field Theory, Corollary VI.3.6 (Bauer)

For finite Galois extensions `L` and `M` of a number field `K`, embedded in a
fixed algebraic closure `Ω`, Bauer's theorem says that field inclusion is
equivalent to reverse inclusion of the sets of completely split primes.  It
follows that equality of fields is equivalent to equality of splitting sets,
and that the splitting-set assignment is injective.

The ambient algebraic closure is deliberately not assumed finite-dimensional
over `K`.  Finiteness is carried by `FiniteGaloisIntermediateField` itself.
The one missing interface isolated below is the compositum splitting identity
in precisely this unrestricted ambient setting.
-/

namespace Towers.CField.PDensit

open IsDedekindDomain NumberField Set
open Towers.NumberTheory.Milne
open scoped NumberField

noncomputable section

universe u

/-- A finite Galois intermediate field of an algebraic closure of a number
field is itself a number field. -/
noncomputable local instance finiteGaloisIntermediateFieldNumberField
    {K Ω : Type u} [Field K] [NumberField K]
    [Field Ω] [Algebra K Ω]
    (L : FiniteGaloisIntermediateField K Ω) : NumberField L :=
  NumberField.of_module_finite K L

/-- The exact missing compositum interface needed by Bauer's argument.  The
existing Towers theorem has the same conclusion but assumes that the entire
ambient field `Ω` is a number field; that hypothesis is inappropriate when
`Ω` is the fixed algebraic closure in the source. -/
def CompositumSplittingBridge : Prop :=
  ∀ (K Ω : Type u)
    [Field K] [NumberField K]
    [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
    (L M : FiniteGaloisIntermediateField K Ω),
    splittingPrimes K (L ⊔ M : FiniteGaloisIntermediateField K Ω) =
      splittingPrimes K L ∩ splittingPrimes K M

/-- The inclusion assertion in Bauer's corollary. -/
def InclusionConclusion
    (K Ω : Type u)
    [Field K] [NumberField K]
    [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] : Prop :=
  ∀ L M : FiniteGaloisIntermediateField K Ω,
    L ≤ M ↔ splittingPrimes K M ⊆ splittingPrimes K L

/-- The equality assertion following Bauer's inclusion criterion. -/
def EqualityConclusion
    (K Ω : Type u)
    [Field K] [NumberField K]
    [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] : Prop :=
  ∀ L M : FiniteGaloisIntermediateField K Ω,
    L = M ↔ splittingPrimes K L = splittingPrimes K M

/-- The splitting-set assignment appearing in the final sentence of the
corollary. -/
def galoisSplittingPrimes
    (K Ω : Type u)
    [Field K] [NumberField K]
    [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] :
    FiniteGaloisIntermediateField K Ω →
      Set (HeightOneSpectrum (NumberField.RingOfIntegers K)) :=
  fun L ↦ splittingPrimes K L

/-- The injectivity assertion in the final sentence of Bauer's corollary. -/
def InjectivityConclusion
    (K Ω : Type u)
    [Field K] [NumberField K]
    [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] : Prop :=
  Function.Injective (galoisSplittingPrimes K Ω)

/-- **Corollary VI.3.6 (Bauer 1916), source statement.** -/
def GaloisSplittingRigidity : Prop :=
  ∀ (K Ω : Type u)
    [Field K] [NumberField K]
    [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω],
    InclusionConclusion K Ω ∧
      EqualityConclusion K Ω ∧
      InjectivityConclusion K Ω

/-- A finite Galois extension is its own Galois closure. -/
lemma galois_closure_self
    {K Ω : Type u} [Field K] [NumberField K]
    [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
    (L : FiniteGaloisIntermediateField K Ω) :
    IsGaloisClosure K L L := by
  rw [IsGaloisClosure]
  have hrange : Set.range (algebraMap L L) = Set.univ := by
    ext x
    simp
  rw [hrange, IntermediateField.adjoin_univ]
  exact top_unique (IntermediateField.le_normalClosure
    (K := (⊤ : IntermediateField K L)))

/-- Theorem 3.4 specializes to density `1 / [L : K]` for a finite Galois
subextension `L` of the fixed algebraic closure. -/
lemma splitting_polar_density
    (h34 : (∀ (K L M : Type u)
          [Field K] [NumberField K]
          [Field L] [NumberField L]
          [Field M] [NumberField M]
          [Algebra K L] [Algebra K M] [Algebra L M] [IsScalarTower K L M]
          [FiniteDimensional K L] [FiniteDimensional K M] [IsGalois K M],
          GaloisClosureConclusion K L M))
    {K Ω : Type u} [Field K] [NumberField K]
    [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
    (L : FiniteGaloisIntermediateField K Ω) :
    PrimePolarDensity K (splittingPrimes K L)
      (1 / (Module.finrank K L : ℝ)) :=
  h34 K L L (galois_closure_self L)

/-- Polar density has at most one value, using Proposition 3.1(d) in both
directions. -/
lemma polarDensity_unique
    {K : Type u} [Field K] [NumberField K]
    (h31d : PolarDensityMonotone K)
    (T : Set (HeightOneSpectrum (NumberField.RingOfIntegers K)))
    {δ δ' : ℝ}
    (hδ : PrimePolarDensity K T δ)
    (hδ' : PrimePolarDensity K T δ') :
    δ = δ' := by
  exact le_antisymm
    (h31d T T δ δ' Set.Subset.rfl hδ hδ')
    (h31d T T δ' δ Set.Subset.rfl hδ' hδ)

/-- The finite-dimensional degree step, stated without imposing finite
dimensionality on the ambient algebraic closure. -/
lemma finrank_sup_right
    {K Ω : Type u} [Field K] [Field Ω] [Algebra K Ω]
    (L M : FiniteGaloisIntermediateField K Ω)
    (hdegree : Module.finrank K
      (L ⊔ M : FiniteGaloisIntermediateField K Ω) = Module.finrank K M) :
    L ≤ M := by
  have hMsup : M.toIntermediateField ≤
      (L ⊔ M : FiniteGaloisIntermediateField K Ω).toIntermediateField :=
    (FiniteGaloisIntermediateField.le_iff M (L ⊔ M)).1 le_sup_right
  have hM : M.toIntermediateField =
      (L ⊔ M : FiniteGaloisIntermediateField K Ω).toIntermediateField :=
    IntermediateField.eq_of_le_of_finrank_le hMsup hdegree.le
  have hLsup : L.toIntermediateField ≤
      (L ⊔ M : FiniteGaloisIntermediateField K Ω).toIntermediateField :=
    (FiniteGaloisIntermediateField.le_iff L (L ⊔ M)).1 le_sup_left
  exact (FiniteGaloisIntermediateField.le_iff L M).2 (hM ▸ hLsup)

/-- The reverse implication in Bauer's criterion: inclusion of splitting
sets forces inclusion of fields. -/
lemma splitting_reverse_subset
    (h34 : (∀ (K L M : Type u)
          [Field K] [NumberField K]
          [Field L] [NumberField L]
          [Field M] [NumberField M]
          [Algebra K L] [Algebra K M] [Algebra L M] [IsScalarTower K L M]
          [FiniteDimensional K L] [FiniteDimensional K M] [IsGalois K M],
          GaloisClosureConclusion K L M))
    (h31d : ∀ (K : Type u) [Field K] [NumberField K], PolarDensityMonotone K)
    (hcompositum : CompositumSplittingBridge.{u})
    {K Ω : Type u} [Field K] [NumberField K]
    [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
    (L M : FiniteGaloisIntermediateField K Ω)
    (hsubset : splittingPrimes K M ⊆ splittingPrimes K L) :
    L ≤ M := by
  have hset : splittingPrimes K
      (L ⊔ M : FiniteGaloisIntermediateField K Ω) = splittingPrimes K M :=
    (hcompositum K Ω L M).trans (Set.inter_eq_right.mpr hsubset)
  have hcompositumDensity :
      PrimePolarDensity K
        (splittingPrimes K (L ⊔ M : FiniteGaloisIntermediateField K Ω))
        (1 / (Module.finrank K
          (L ⊔ M : FiniteGaloisIntermediateField K Ω) : ℝ)) :=
    splitting_polar_density h34 (L ⊔ M)
  have hMDensity :
      PrimePolarDensity K (splittingPrimes K M)
        (1 / (Module.finrank K M : ℝ)) :=
    splitting_polar_density h34 M
  have hrecip :
      (1 / (Module.finrank K
        (L ⊔ M : FiniteGaloisIntermediateField K Ω) : ℝ)) =
        1 / (Module.finrank K M : ℝ) := by
    apply polarDensity_unique (h31d K)
      (splittingPrimes K M)
    · simpa only [hset] using hcompositumDensity
    · exact hMDensity
  have hdegree : Module.finrank K
      (L ⊔ M : FiniteGaloisIntermediateField K Ω) =
      Module.finrank K M := by
    have hleftNat : 0 < Module.finrank K
        (L ⊔ M : FiniteGaloisIntermediateField K Ω) := Module.finrank_pos
    have hrightNat : 0 < Module.finrank K M := Module.finrank_pos
    have hleft : (Module.finrank K
        (L ⊔ M : FiniteGaloisIntermediateField K Ω) : ℝ) ≠ 0 := by
      exact_mod_cast hleftNat.ne'
    have hright : (Module.finrank K M : ℝ) ≠ 0 := by
      exact_mod_cast hrightNat.ne'
    field_simp [hleft, hright] at hrecip
    exact_mod_cast hrecip.symm
  exact finrank_sup_right L M hdegree

/-- Theorem 3.4, Proposition 3.1(d), and the compositum splitting identity
prove all three assertions of Bauer's corollary. -/
theorem splitting_chebotarev_density
    (h34 : (∀ (K L M : Type u)
          [Field K] [NumberField K]
          [Field L] [NumberField L]
          [Field M] [NumberField M]
          [Algebra K L] [Algebra K M] [Algebra L M] [IsScalarTower K L M]
          [FiniteDimensional K L] [FiniteDimensional K M] [IsGalois K M],
          GaloisClosureConclusion K L M))
    (h31d : ∀ (K : Type u) [Field K] [NumberField K], PolarDensityMonotone K)
    (hcompositum : CompositumSplittingBridge.{u}) :
    GaloisSplittingRigidity.{u} := by
  intro K Ω _ _ _ _ _
  have hinclusion : InclusionConclusion K Ω := by
    intro L M
    constructor
    · intro hLM
      have hsup : L ⊔ M = M := sup_eq_right.mpr hLM
      have hsplit := hcompositum K Ω L M
      rw [hsup] at hsplit
      exact Set.inter_eq_right.mp hsplit.symm
    · exact splitting_reverse_subset
        h34 h31d hcompositum L M
  have hequality : EqualityConclusion K Ω := by
    intro L M
    constructor
    · rintro rfl
      rfl
    · intro hsplit
      apply le_antisymm
      · exact (hinclusion L M).2 (hsplit ▸ Set.Subset.rfl)
      · exact (hinclusion M L).2 (hsplit ▸ Set.Subset.rfl)
  refine ⟨hinclusion, hequality, ?_⟩
  intro L M hsplit
  exact (hequality L M).2 hsplit

end

end Towers.CField.PDensit
