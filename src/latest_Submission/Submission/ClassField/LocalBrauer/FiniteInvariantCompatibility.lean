import Submission.ClassField.LocalBrauer.CanonicalUnramifiedTower
import Submission.ClassField.LocalBrauer.InvariantAssembly
import Submission.ClassField.LocalBrauer.UnramifiedFiniteInvariant

/-!
# Chapter IV, Section 4: compatibility of finite unramified invariants

The finite unramified invariant is compatible with inflation once this is
checked on Milne's carry class.  This file isolates the remaining concrete
input: under inclusion of factorial unramified levels, the carry class at the
smaller level must become the appropriate power of the carry class at the
larger level.  The Galois equivalences currently exported by
`CanonicalUnramifiedTower` use `zmodCyclicMulEquiv`, which chooses generators
independently at each level; a concrete carry formula therefore additionally
requires Frobenius-compatible choices of those generators.
-/

namespace Submission.CField.LBrauer

noncomputable section

universe u

open BGroups CProduca

local instance localInvariantLevelDegree_neZero (r : ℕ) :
    NeZero (invariantLevelDegree r) :=
  ⟨(invariant_level_pos r).ne'⟩

/-- Under inclusion of factorial torsion levels, `1 / n` becomes the
corresponding power of `1 / m`. -/
theorem torsion_inclusion_div
    {r s : ℕ} (h : r ≤ s) :
    invariantTorsionInclusion r s h
        (Multiplicative.ofAdd
          (localDivTorsion (invariantLevelDegree r))) =
      Multiplicative.ofAdd
          (localDivTorsion (invariantLevelDegree s)) ^
        (invariantLevelDegree s / invariantLevelDegree r) := by
  let nr := invariantLevelDegree r
  let ns := invariantLevelDegree s
  let c := ns / nr
  have hnr : 0 < nr := invariant_level_pos r
  have hns : 0 < ns := invariant_level_pos s
  letI : NeZero nr := ⟨hnr.ne'⟩
  letI : NeZero ns := ⟨hns.ne'⟩
  have hdvd : nr ∣ ns := invariant_level_dvd h
  have hmul : nr * c = ns := by
    exact Nat.mul_div_cancel' hdvd
  apply Multiplicative.toAdd.injective
  apply Subtype.ext
  change ((localDivTorsion nr : localInvariantTorsion nr) :
      LocalInvariant) =
    c • ((localDivTorsion ns : localInvariantTorsion ns) :
      LocalInvariant)
  rw [invariant_div_coe, invariant_div_coe]
  apply congrArg (fun q : ℚ ↦ (q : LocalInvariant))
  change (1 : ℚ) / nr = (c : ℚ) * ((1 : ℚ) / ns)
  field_simp
  exact_mod_cast hmul.symm

variable {K : Type u} [Field K]
variable {F E : FiniteGaloisIntermediateField K (SeparableClosure K)}

/-- The defining square of `Corollary316.inflationHom` transports a power
formula in `H²` directly to the corresponding relative Brauer classes.  Taking
`xF` and `xE` to be the two carry classes reduces the missing concrete
compatibility theorem to an equality of inflated carry cocycles. -/
theorem relative_inclusion_inflation
    (hFE : F ≤ E)
    (xF : MHTwo Gal(F/K) Fˣ)
    (xE : MHTwo Gal(E/K) Eˣ)
    (c : ℕ) (hinflation : inflationHom K hFE xF = xE ^ c) :
    relativeBrauerInclusion K hFE
        (CProduc.hRelativeBrauer K F xF) =
      (CProduc.hRelativeBrauer K E xE) ^ c := by
  calc
    relativeBrauerInclusion K hFE
        (CProduc.hRelativeBrauer K F xF) =
      CProduc.hRelativeBrauer K E
        (inflationHom K hFE xF) :=
      (relative_brauer_inflation K hFE xF).symm
    _ = CProduc.hRelativeBrauer K E (xE ^ c) := by
      rw [hinflation]
    _ = (CProduc.hRelativeBrauer K E xE) ^ c := by
      rw [map_pow]

section CanonicalFactorialTower

variable (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K]
  [ValuativeRel K] [IsNonarchimedeanLocalField K]
  [Valuation.Compatible (NormedField.valuation (K := K))]

/-- `Corollary316.inflationHom` turns the carry-class formula at the canonical
factorial `H²` levels into the relative-Brauer carry formula needed by the
finite invariant assembly. -/
theorem factorial_relative_inflation
    (x : ∀ r, MHTwo
      Gal(unramifiedFactorialLevel K r/K)
      (unramifiedFactorialLevel K r)ˣ)
    (hinflation : ∀ r s (h : r ≤ s),
      inflationHom K (factorial_level_monotone K h) (x r) =
        (x s) ^ (invariantLevelDegree s /
          invariantLevelDegree r)) :
    ∀ r s (h : r ≤ s),
      brauerCofinalInclusion K (unramifiedFactorialLevel K)
          (factorial_level_monotone K) r s h
          (CProduc.hRelativeBrauer K
            (unramifiedFactorialLevel K r) (x r)) =
        (CProduc.hRelativeBrauer K
          (unramifiedFactorialLevel K s) (x s)) ^
            (invariantLevelDegree s /
              invariantLevelDegree r) := by
  intro r s h
  exact relative_inclusion_inflation
    (factorial_level_monotone K h)
    (x r) (x s)
    (invariantLevelDegree s / invariantLevelDegree r)
    (hinflation r s h)

/-- Canonical-factorial specialization of
`brauer_compatibility_carry`.  Once the chosen carry `H²`
classes satisfy the displayed inflation formula, their finite invariants
assemble with exactly the compatibility hypothesis required by
`localBrauerInvariant`. -/
theorem factorial_compatibility_carry
    (e : ∀ r,
      brauerCofinalLevel K (unramifiedFactorialLevel K) r ≃*
        invariantTorsionLevel r)
    (x : ∀ r, MHTwo
      Gal(unramifiedFactorialLevel K r/K)
      (unramifiedFactorialLevel K r)ˣ)
    (hgenerator : ∀ r
      (y : brauerCofinalLevel K (unramifiedFactorialLevel K) r),
      ∃ i : ℕ, y =
        (CProduc.hRelativeBrauer K
          (unramifiedFactorialLevel K r) (x r)) ^ i)
    (hcarry : ∀ r,
      e r (CProduc.hRelativeBrauer K
          (unramifiedFactorialLevel K r) (x r)) =
        Multiplicative.ofAdd
          (localDivTorsion (invariantLevelDegree r)))
    (hinflation : ∀ r s (h : r ≤ s),
      inflationHom K (factorial_level_monotone K h) (x r) =
        (x s) ^ (invariantLevelDegree s /
          invariantLevelDegree r)) :
    ∀ r s h y,
      e s (brauerCofinalInclusion K
          (unramifiedFactorialLevel K)
          (factorial_level_monotone K) r s h y) =
        invariantTorsionInclusion r s h (e r y) := by
  intro r s h y
  obtain ⟨i, rfl⟩ := hgenerator r y
  let g := fun t ↦ CProduc.hRelativeBrauer K
    (unramifiedFactorialLevel K t) (x t)
  have hg := factorial_relative_inflation
    K x hinflation r s h
  change e s (brauerCofinalInclusion K
      (unramifiedFactorialLevel K)
      (factorial_level_monotone K) r s h
      ((g r) ^ i)) =
    invariantTorsionInclusion r s h (e r ((g r) ^ i))
  calc
    e s (brauerCofinalInclusion K
        (unramifiedFactorialLevel K)
        (factorial_level_monotone K) r s h
        ((g r) ^ i)) =
      (e s (brauerCofinalInclusion K
        (unramifiedFactorialLevel K)
        (factorial_level_monotone K) r s h (g r))) ^ i := by
        rw [map_pow, map_pow]
    _ = (e s ((g s) ^ (invariantLevelDegree s /
          invariantLevelDegree r))) ^ i := by rw [hg]
    _ = ((e s (g s)) ^ (invariantLevelDegree s /
          invariantLevelDegree r)) ^ i := by rw [map_pow]
    _ = (Multiplicative.ofAdd
          (localDivTorsion (invariantLevelDegree s)) ^
        (invariantLevelDegree s / invariantLevelDegree r)) ^ i := by
      rw [hcarry s]
    _ = (invariantTorsionInclusion r s h
          (Multiplicative.ofAdd (localDivTorsion
            (invariantLevelDegree r)))) ^ i := by
      rw [torsion_inclusion_div h]
    _ = invariantTorsionInclusion r s h
        ((Multiplicative.ofAdd (localDivTorsion
          (invariantLevelDegree r))) ^ i) := by rw [map_pow]
    _ = invariantTorsionInclusion r s h (e r ((g r) ^ i)) := by
      apply congrArg (invariantTorsionInclusion r s h)
      rw [map_pow, hcarry r]

end CanonicalFactorialTower

variable (K : Type u) [Field K]
variable (L : ℕ → FiniteGaloisIntermediateField K (SeparableClosure K))
variable (hL : Monotone L)

/-- Compatibility on a family of carry generators implies the exact
finite-level compatibility hypothesis used by `localBrauerInvariant`.

For the canonical unramified tower, `g r` is
`unramifiedCarryRelative` at factorial level `r`.  The hypotheses
`hgenerator` and `hinclusion` are respectively the cyclic finite-level
calculation and the concrete inflation formula for carry crossed products. -/
theorem brauer_compatibility_carry
    (e : ∀ r, brauerCofinalLevel K L r ≃*
      invariantTorsionLevel r)
    (g : ∀ r, brauerCofinalLevel K L r)
    (hgenerator : ∀ r (x : brauerCofinalLevel K L r),
      ∃ i : ℕ, x = (g r) ^ i)
    (hcarry : ∀ r,
      e r (g r) = Multiplicative.ofAdd
        (localDivTorsion (invariantLevelDegree r)))
    (hinclusion : ∀ r s (h : r ≤ s),
      brauerCofinalInclusion K L hL r s h (g r) =
        (g s) ^ (invariantLevelDegree s /
          invariantLevelDegree r)) :
    ∀ r s h x,
      e s (brauerCofinalInclusion K L hL r s h x) =
        invariantTorsionInclusion r s h (e r x) := by
  intro r s h x
  obtain ⟨i, rfl⟩ := hgenerator r x
  calc
    e s (brauerCofinalInclusion K L hL r s h ((g r) ^ i)) =
        (e s (brauerCofinalInclusion K L hL r s h (g r))) ^ i := by
      rw [map_pow, map_pow]
    _ = (e s ((g s) ^ (invariantLevelDegree s /
          invariantLevelDegree r))) ^ i := by
      rw [hinclusion r s h]
    _ = ((e s (g s)) ^ (invariantLevelDegree s /
          invariantLevelDegree r)) ^ i := by
      rw [map_pow]
    _ = (Multiplicative.ofAdd
          (localDivTorsion (invariantLevelDegree s)) ^
        (invariantLevelDegree s / invariantLevelDegree r)) ^ i := by
      rw [hcarry s]
    _ = (invariantTorsionInclusion r s h
          (Multiplicative.ofAdd
            (localDivTorsion
              (invariantLevelDegree r)))) ^ i := by
      rw [torsion_inclusion_div h]
    _ = invariantTorsionInclusion r s h
          ((Multiplicative.ofAdd
            (localDivTorsion
              (invariantLevelDegree r))) ^ i) := by
      rw [map_pow]
    _ = invariantTorsionInclusion r s h (e r ((g r) ^ i)) := by
      apply congrArg (invariantTorsionInclusion r s h)
      rw [map_pow, hcarry r]

end

end Submission.CField.LBrauer
