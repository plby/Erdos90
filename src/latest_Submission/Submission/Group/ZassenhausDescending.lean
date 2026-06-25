import Submission.Algebra.DenseGenerators.DimensionSubgroup

open scoped commutatorElement

namespace Submission

/-- Dimension-subgroup depths add under group commutators. -/
lemma commutator_element_dimension
    {p : ℕ} {G : Type*} [Group G] [Fact p.Prime]
    {r s : ℕ} {x y : G}
    (hx : x ∈ dSubgro p G r)
    (hy : y ∈ dSubgro p G s) :
    ⁅x, y⁆ ∈ dSubgro p G (r + s) := by
  change groupAlgebraSub p G x ∈ augmentationIdealPower p G r at hx
  change groupAlgebraSub p G y ∈ augmentationIdealPower p G s at hy
  change groupAlgebraSub p G ⁅x, y⁆ ∈ augmentationIdealPower p G (r + s)
  have hxcong :
      dDCongru p G r x := by
    have hxI :
        groupAlgebraSub p G x ∈
          denseGeneratorsIdeal p G ^ r :=
      (Submodule.restrictScalars_mem (ZMod p)
        (denseGeneratorsIdeal p G ^ r)
        (groupAlgebraSub p G x)).mp
        (by simpa [augmentationIdealPower] using hx)
    simpa [groupAlgebraSub,
      dDCongru] using hxI
  have hycong :
      dDCongru p G s y := by
    have hyI :
        groupAlgebraSub p G y ∈
          denseGeneratorsIdeal p G ^ s :=
      (Submodule.restrictScalars_mem (ZMod p)
        (denseGeneratorsIdeal p G ^ s)
        (groupAlgebraSub p G y)).mp
        (by simpa [augmentationIdealPower] using hy)
    simpa [groupAlgebraSub,
      dDCongru] using hyI
  have hcomm :
      dDCongru p G (r + s) ⁅x, y⁆ := by
    simpa [commutatorElement_def] using
      (dense_generators_add
        (p := p) (Λ := G) hxcong hycong)
  exact
    (Submodule.restrictScalars_mem (ZMod p)
      (denseGeneratorsIdeal p G ^ (r + s))
      (groupAlgebraSub p G ⁅x, y⁆)).mpr
      (by simpa [augmentationIdealPower, groupAlgebraSub,
        dDCongru] using hcomm)

/-- Taking a `p`th power multiplies dimension-subgroup depth by `p`. -/
lemma pow_dimension_prime
    {p : ℕ} {G : Type*} [Group G] [Fact p.Prime]
    {r : ℕ} {x : G}
    (hx : x ∈ dSubgro p G r) :
    x ^ p ∈ dSubgro p G (r * p) := by
  change groupAlgebraSub p G x ∈ augmentationIdealPower p G r at hx
  change groupAlgebraSub p G (x ^ p) ∈ augmentationIdealPower p G (r * p)
  simpa using
    (algebra_sub_ideal
      (p := p) (G := G) (r := r) (j := 1) hx)

/-- A known reverse inclusion at the sum of two depths transfers the additive commutator law
from dimension subgroups to the explicit Zassenhaus filtration. -/
lemma element_filtration_reverse
    {p : ℕ} {G : Type*} [Group G] [Fact p.Prime]
    {r s : ℕ}
    (hreverse :
      dSubgro p G (r + s) ≤ zassenhausFiltration p G (r + s))
    {x y : G}
    (hx : x ∈ zassenhausFiltration p G r)
    (hy : y ∈ zassenhausFiltration p G s) :
    ⁅x, y⁆ ∈ zassenhausFiltration p G (r + s) := by
  apply hreverse
  exact
    commutator_element_dimension
      (filtration_dimension_subgroup (p := p) (G := G) r hx)
      (filtration_dimension_subgroup (p := p) (G := G) s hy)

/-- A known reverse inclusion at the multiplied depth transfers the `p`-power law from
dimension subgroups to the explicit Zassenhaus filtration. -/
lemma pow_filtration_reverse
    {p : ℕ} {G : Type*} [Group G] [Fact p.Prime]
    {r : ℕ}
    (hreverse :
      dSubgro p G (r * p) ≤ zassenhausFiltration p G (r * p))
    {x : G}
    (hx : x ∈ zassenhausFiltration p G r) :
    x ^ p ∈ zassenhausFiltration p G (r * p) := by
  apply hreverse
  exact
    pow_dimension_prime
      (filtration_dimension_subgroup (p := p) (G := G) r hx)

end Submission
