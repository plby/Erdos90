import Mathlib.Init

/-!
# Efrat--Chapman formalization coverage

Source: `docs/1601.08006/EfratChapman_revised.tex`.

This file is the statement-fidelity audit. A checked item has the paper's
scope. A partial item records the exact restriction still present in Lean.

## Section 2: graded Lie algebras

- [x] Lemma 2.1 (`inverse in Magnus ring`, in `MSeries` and `MagnusInverse`)
- [x] Lemma 2.2 (`subgroup`, in `OnePlusIdeal`)
- [~] Lemma 2.3 (`GCokern` proves it for finite `X`; the paper fixes
  an arbitrary set `X`)
- [~] Corollary 2.4 (`ICokern` and `FCokern` require finite
  `X`; the field theorem explicitly uses scalar extension of the source)

## Section 3: multiplicatively descending maps

- [x] Definition 3.1 (`MDescen`)
- [x] Example 3.2 (trivial map)
- [x] Example 3.3 (the map attached to a sequence `A`)
- [x] Example 3.4 (constant sequence, including binomiality)
- [x] Example 3.5 (logarithmic prime-power map)
- [x] Definition 3.6 (`IsBinomial`)
- [x] Lemma 3.7 (`binomial_valuation_condition`)
- [x] Example 3.8 (the map attached to `A` is binomial)
- [x] Example 3.9 (the logarithmic map is binomial)

## Section 4: powers of the lower central series

- [x] Lemma 4.1 (`description of grd(e,n)`, in
  `WeightedSeries` and `MagnusWeightedCoefficients`)
- [x] Corollary 4.2 (`cor to th 4.2`, in
  `WeightedSeries` and `MagnusWeightedCoefficients`)
- [~] Theorem 4.3 (both constructive inclusions are arbitrary-rank in
  `MagnusWeighted` and `GAWt`; the integral reverse
  inclusion and equalities in `WeightedConverse` require finite `X`)

## Section 5: intersections of kernels

- [x] Lemma 5.1 (`intlem`, in `UnitriangularMagnus`)
- [x] Proposition 5.2 (`inclusion of intersections`, in
  `UniversalUnitriangularKernels`)
- [x] Theorem 5.3 (`intersection thm`, in
  `WeightedKernelIntersections`)
- [x] Proposition 5.4 (`kernel intersection to bar U`, in `UnitriangularMagnus`)
- [x] Corollary 5.5 (`restriction of mu hom`, in `UnitriangularMagnus`)

## Section 6: inductive definitions

- [x] Theorem 6.1 (`rec sequence inclusion`, in
  `RecursiveWeightedIdeals` and `RecursiveMagnus`)

## Section 7: the A-filtration

- [x] Lemma 7.1 (`(1) (2) for A-filtration`, in `RecursiveConditions`)
- [x] Lemma 7.2 (`comm`, in `CommutatorPowers`)
- [x] Lemma 7.3 (`ABseq`, in `AFiltration`)
- [x] Theorem 7.4 (`closed formula for A filtration`, arbitrary groups in
  `ArbitraryRankDescent`)
- [x] Corollary 7.5 (constant `a` closed formula, arbitrary groups in
  `ArbitraryRankDescent`)

## Section 8: the q-Zassenhaus filtration

- [x] Lemma 8.1 (`Zassenhaus is decreasing`, in `ZassenhausRecursive`)
- [x] Lemma 8.2 (`1, 2 for q-Zassenhaus`, in `RecursiveConditions`)
- [x] Theorem 8.3 (`q Zassenhaus as product`, arbitrary groups in
  `ArbitraryRankDescent`)

## Section 9: Massey products

- [x] Lemma 9.1 (`MMassey` constructs the canonical defining system,
  proves its value is a cocycle, and identifies its class with
  transgression)
- [x] Theorem 9.2 (`masseyPairing_nondegenerate`, in `MMassey`,
  including the final finite-field specialization)
- [~] Corollary 9.3 (`IntegralMasseyRank`, `HallWittFormula`, and
  `HallWittRank` prove the finite-alphabet freeness and Witt formula; the
  paper also includes infinite `X`, with rank `l_∞(n) = ∞`)

## Missing arbitrary-alphabet infrastructure

The four partial entries above share the same blocker: the current
`HallTree.BasicIndex`/PBW basis is constructed by enumerating a finite
alphabet. Completing them at the paper's scope requires an
arbitrary-alphabet Hall basis (or an equivalent finite-support/direct-limit
development) and functorial compatibility with the graded Magnus maps.
-/
