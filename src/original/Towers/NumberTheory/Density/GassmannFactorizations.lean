import Towers.NumberTheory.Density.PolynomialFactorization
import Mathlib.GroupTheory.Coset.Card
import Mathlib.GroupTheory.GroupAction.Quotient

/-!
# Gassmann-equivalent actions and arithmetic equivalence

Remark 8.40(c) of ANT points out that nonisomorphic number fields can have
the same prime-decomposition data.  The finite-group mechanism is Gassmann
equivalence: two permutation actions have the same cycle partition for every
group element.  This file records that mechanism and connects it to the
factor-degree form of Dedekind's theorem.

The source does not construct the required nonconjugate subgroups or their
realization over `ℚ`.  Accordingly, the arithmetic theorems below take the
Gassmann-equivalent root actions as their explicit input and prove the full
local factorization consequence.
-/

namespace Towers.NumberTheory.Milne

open Equiv IsDedekindDomain NumberField Polynomial

noncomputable section

section FiniteActions

variable {G alpha beta gamma : Type*} [Group G]
  [Fintype alpha] [Fintype beta] [Fintype gamma]
  [DecidableEq alpha] [DecidableEq beta] [DecidableEq gamma]

/-- Two finite permutation actions are Gassmann equivalent when every group
element has the same full cycle partition in both actions.  Fixed points are
included as parts of size one. -/
def GEAction
    (rho : G →* Equiv.Perm alpha) (tau : G →* Equiv.Perm beta) : Prop :=
  ∀ g, ((rho g).partition).parts = ((tau g).partition).parts

theorem GEAction.refl (rho : G →* Equiv.Perm alpha) :
    GEAction rho rho :=
  fun _ => rfl

theorem GEAction.symm
    {rho : G →* Equiv.Perm alpha} {tau : G →* Equiv.Perm beta}
    (h : GEAction rho tau) :
    GEAction tau rho :=
  fun g => (h g).symm

theorem GEAction.trans
    {rho : G →* Equiv.Perm alpha} {tau : G →* Equiv.Perm beta}
    {upsilon : G →* Equiv.Perm gamma}
    (h₁ : GEAction rho tau)
    (h₂ : GEAction tau upsilon) :
    GEAction rho upsilon :=
  fun g => (h₁ g).trans (h₂ g)

/-- Gassmann-equivalent actions have the same degree. -/
theorem GEAction.card_eq
    {rho : G →* Equiv.Perm alpha} {tau : G →* Equiv.Perm beta}
    (h : GEAction rho tau) :
    Fintype.card alpha = Fintype.card beta := by
  calc
    Fintype.card alpha = ((rho 1).partition).parts.sum :=
      (rho 1).partition.parts_sum.symm
    _ = ((tau 1).partition).parts.sum := congrArg Multiset.sum (h 1)
    _ = Fintype.card beta := (tau 1).partition.parts_sum

/-- The cycle-partition definition implies equality of the usual permutation
characters, i.e. equality of the number of fixed points of every element. -/
theorem GEAction.card_fixed_pointseq
    {rho : G →* Equiv.Perm alpha} {tau : G →* Equiv.Perm beta}
    (h : GEAction rho tau) (g : G) :
    Fintype.card (Function.fixedPoints (rho g)) =
      Fintype.card (Function.fixedPoints (tau g)) := by
  have hcycles : (rho g).cycleType = (tau g).cycleType := by
    rw [← Equiv.Perm.filter_parts_partition_eq_cycleType,
      ← Equiv.Perm.filter_parts_partition_eq_cycleType, h g]
  rw [Equiv.Perm.card_fixedPoints, Equiv.Perm.card_fixedPoints,
    h.card_eq, hcycles]

/-- Gassmann equivalence descends from elements to conjugacy classes. -/
theorem GEAction.conjug_actio_parts
    {rho : G →* Equiv.Perm alpha} {tau : G →* Equiv.Perm beta}
    (h : GEAction rho tau) (C : ConjClasses G) :
    (conjugacyActionPartition rho C).parts =
      (conjugacyActionPartition tau C).parts := by
  refine Quotient.inductionOn C ?_
  intro g
  exact h g

end FiniteActions

section Subgroups

variable {G : Type*} [Group G] [Fintype G]

/-- The natural left action of a finite group on the left cosets of a
subgroup. -/
noncomputable def subgroupCosetAction (H : Subgroup G) :
    G →* Equiv.Perm (G ⧸ H) :=
  MulAction.toPermHom G (G ⧸ H)

/-- Two subgroups are Gassmann equivalent when their left-coset actions are
Gassmann equivalent. -/
noncomputable def GESubgro (H J : Subgroup G) : Prop := by
  classical
  exact GEAction
    (subgroupCosetAction H) (subgroupCosetAction J)

/-- Gassmann-equivalent subgroups have the same index. -/
theorem GESubgro.index_eq
    {H J : Subgroup G} (h : GESubgro H J) :
    H.index = J.index := by
  classical
  rw [Subgroup.index_eq_card, Subgroup.index_eq_card]
  simpa only [Nat.card_eq_fintype_card] using h.card_eq

/-- In the usual permutation-character language, every group element fixes
the same number of cosets of two Gassmann-equivalent subgroups. -/
theorem GESubgro.card_fixed_cosetseq
    {H J : Subgroup G} (h : GESubgro H J) (g : G) :
    Nat.card (Function.fixedPoints (subgroupCosetAction H g)) =
      Nat.card (Function.fixedPoints (subgroupCosetAction J g)) := by
  classical
  simpa only [Nat.card_eq_fintype_card] using h.card_fixed_pointseq g

end Subgroups

section IntegralPolynomials

variable (K L : Type*) [Field K] [Field L]
  [NumberField K] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

noncomputable local instance gassmannIntegralClosureDecidableEq :
    DecidableEq (𝓞 L) := Classical.decEq _

/-- At a prime where both reductions are separable, Gassmann-equivalent root
actions give identical multisets of irreducible-factor degrees. -/
theorem degrees_gassmann_actions
    (f g : (𝓞 K)[X]) (hf : f.Monic) (hg : g.Monic)
    (hfsplits : (f.map (algebraMap (𝓞 K) (𝓞 L))).Splits)
    (hgsplits : (g.map (algebraMap (𝓞 K) (𝓞 L))).Splits)
    (hGassmann : GEAction
      (integralRootAction K L f)
      (integralRootAction K L g))
    (v : HeightOneSpectrum (𝓞 K))
    (hfsep : (f.map (Ideal.Quotient.mk v.asIdeal)).Separable)
    (hgsep : (g.map (Ideal.Quotient.mk v.asIdeal)).Separable) :
    reductionDegrees K f v = reductionDegrees K g v := by
  rw [degrees_frobenius_partition K L f hf hfsplits v hfsep,
    degrees_frobenius_partition K L g hg hgsplits v hgsep]
  exact hGassmann.conjug_actio_parts _

/-- The primes where at least one of the two polynomial reductions is
inseparable. -/
def commonInseparablePrimes (f g : (𝓞 K)[X]) :
    Set (HeightOneSpectrum (𝓞 K)) :=
  inseparableReductionPrimes K f ∪ inseparableReductionPrimes K g

/-- The common exceptional set is finite when both polynomial discriminants
are nonzero. -/
theorem common_inseparable_primes
    (f g : (𝓞 K)[X]) (hf : f.Monic) (hg : g.Monic)
    (hfdegree : 0 < f.natDegree) (hgdegree : 0 < g.natDegree)
    (hfdisc : f.discr ≠ 0) (hgdisc : g.discr ≠ 0) :
    (commonInseparablePrimes K f g).Finite :=
  (inseparable_reduction_primes K f hf hfdegree hfdisc).union
    (inseparable_reduction_primes K g hg hgdegree hgdisc)

/-- The primes dividing at least one of the two polynomial discriminants. -/
def commonDiscriminantPrimes (f g : (𝓞 K)[X]) :
    Set (HeightOneSpectrum (𝓞 K)) :=
  polynomialDiscriminantPrimes K f ∪ polynomialDiscriminantPrimes K g

/-- The common discriminant-prime set is finite when both discriminants are
nonzero. -/
theorem common_discriminant_primes
    (f g : (𝓞 K)[X]) (hfdisc : f.discr ≠ 0) (hgdisc : g.discr ≠ 0) :
    (commonDiscriminantPrimes K f g).Finite :=
  (polynomial_discriminant_primes K f hfdisc).union
    (polynomial_discriminant_primes K g hgdisc)

/-- Outside the common exceptional set, Gassmann-equivalent root actions give
the same decomposition type at every prime. -/
theorem degrees_outside_inseparable
    (f g : (𝓞 K)[X]) (hf : f.Monic) (hg : g.Monic)
    (hfsplits : (f.map (algebraMap (𝓞 K) (𝓞 L))).Splits)
    (hgsplits : (g.map (algebraMap (𝓞 K) (𝓞 L))).Splits)
    (hGassmann : GEAction
      (integralRootAction K L f)
      (integralRootAction K L g))
    (v : HeightOneSpectrum (𝓞 K))
    (hv : v ∉ commonInseparablePrimes K f g) :
    reductionDegrees K f v = reductionDegrees K g v := by
  apply degrees_gassmann_actions
    K L f g hf hg hfsplits hgsplits hGassmann v
  · by_contra h
    exact hv (Or.inl h)
  · by_contra h
    exact hv (Or.inr h)

/-- In ANT's discriminant formulation, the same conclusion holds at every
prime dividing neither polynomial discriminant. -/
theorem degrees_outside_discriminant
    (f g : (𝓞 K)[X]) (hf : f.Monic) (hg : g.Monic)
    (hfdegree : 0 < f.natDegree) (hgdegree : 0 < g.natDegree)
    (hfsplits : (f.map (algebraMap (𝓞 K) (𝓞 L))).Splits)
    (hgsplits : (g.map (algebraMap (𝓞 K) (𝓞 L))).Splits)
    (hGassmann : GEAction
      (integralRootAction K L f)
      (integralRootAction K L g))
    (v : HeightOneSpectrum (𝓞 K))
    (hv : v ∉ commonDiscriminantPrimes K f g) :
    reductionDegrees K f v = reductionDegrees K g v := by
  apply degrees_outside_inseparable
    K L f g hf hg hfsplits hgsplits hGassmann v
  intro hbad
  apply hv
  rcases hbad with hfBad | hgBad
  · exact Or.inl
      (inseparable_subset_discriminant
        K f hf hfdegree hfBad)
  · exact Or.inr
      (inseparable_subset_discriminant
        K g hg hgdegree hgBad)

/-- Consequently, for every factor-degree pattern, the corresponding prime
sets agree after removing the common finite exceptional set. -/
theorem degrees_diff_inseparable
    (f g : (𝓞 K)[X]) (hf : f.Monic) (hg : g.Monic)
    (hfsplits : (f.map (algebraMap (𝓞 K) (𝓞 L))).Splits)
    (hgsplits : (g.map (algebraMap (𝓞 K) (𝓞 L))).Splits)
    (hGassmann : GEAction
      (integralRootAction K L f)
      (integralRootAction K L g))
    (parts : Multiset ℕ) :
    primesReductionDegrees K f parts \
        commonInseparablePrimes K f g =
      primesReductionDegrees K g parts \
        commonInseparablePrimes K f g := by
  ext v
  constructor
  · rintro ⟨hvparts, hvgood⟩
    refine ⟨?_, hvgood⟩
    change reductionDegrees K g v = parts
    rw [← degrees_outside_inseparable
      K L f g hf hg hfsplits hgsplits hGassmann v hvgood]
    exact hvparts
  · rintro ⟨hvparts, hvgood⟩
    refine ⟨?_, hvgood⟩
    change reductionDegrees K f v = parts
    rw [degrees_outside_inseparable
      K L f g hf hg hfsplits hgsplits hGassmann v hvgood]
    exact hvparts

/-- For every factor-degree pattern, the two prime sets agree away from the
primes dividing either discriminant.  If the discriminants are equal, this is
the precise "away from the common discriminant" conclusion in Remark
8.40(c). -/
theorem degrees_diff_discriminant
    (f g : (𝓞 K)[X]) (hf : f.Monic) (hg : g.Monic)
    (hfdegree : 0 < f.natDegree) (hgdegree : 0 < g.natDegree)
    (hfsplits : (f.map (algebraMap (𝓞 K) (𝓞 L))).Splits)
    (hgsplits : (g.map (algebraMap (𝓞 K) (𝓞 L))).Splits)
    (hGassmann : GEAction
      (integralRootAction K L f)
      (integralRootAction K L g))
    (parts : Multiset ℕ) :
    primesReductionDegrees K f parts \
        commonDiscriminantPrimes K f g =
      primesReductionDegrees K g parts \
        commonDiscriminantPrimes K f g := by
  ext v
  constructor
  · rintro ⟨hvparts, hvgood⟩
    refine ⟨?_, hvgood⟩
    change reductionDegrees K g v = parts
    rw [← degrees_outside_discriminant
      K L f g hf hg hfdegree hgdegree hfsplits hgsplits hGassmann v hvgood]
    exact hvparts
  · rintro ⟨hvparts, hvgood⟩
    refine ⟨?_, hvgood⟩
    change reductionDegrees K f v = parts
    rw [degrees_outside_discriminant
      K L f g hf hg hfdegree hgdegree hfsplits hgsplits hGassmann v hvgood]
    exact hvparts

end IntegralPolynomials

end

end Towers.NumberTheory.Milne
