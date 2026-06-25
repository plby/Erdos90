import Submission.ClassField.NormCorrespondence.CanonicalNormalization
import Submission.ClassField.LocalBrauer.CanonicalAutomorphismExt

/-!
# Uniqueness of arithmetic Frobenius on canonical unramified extensions

The intrinsic residue-power condition in Theorem I.1.1 determines an
automorphism of a canonical unramified extension uniquely.  In particular,
the unique arithmetic Frobenius is the canonical one constructed in
Chapter IV.
-/

namespace Submission.CField.LFTheory

noncomputable section

universe u

open LBrauer

variable (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K]
  [ValuativeRel K] [IsNonarchimedeanLocalField K]
  [Valuation.Compatible (NormedField.valuation (K := K))]

/-- On the canonical unramified extension of degree `n`, the intrinsic
residue-power characterization determines arithmetic Frobenius uniquely. -/
theorem subextension_arithmetic_unique
    (n : ℕ) [NeZero n]
    (σ : Gal((canonicalUnramifiedSubextension K n).1/K))
    (hσ : (canonicalUnramifiedSubextension K n).IsArithmeticFrobenius K σ) :
    σ = canonicalArithmeticFrobenius K n := by
  dsimp only [canonicalUnramifiedSubextension] at σ hσ ⊢
  apply canonical_unramified_ext K n
  intro y hy
  have hσ' := hσ y hy
  have hcanonical :=
    subextension_arithmetic_frobenius K n y hy
  have htriangle := IsUltrametricDist.norm_add_le_max
    (σ y - y ^ localResidueCardinality K)
    (y ^ localResidueCardinality K - canonicalArithmeticFrobenius K n y)
  have hadd :
      (σ y - y ^ localResidueCardinality K) +
          (y ^ localResidueCardinality K - canonicalArithmeticFrobenius K n y) =
        σ y - canonicalArithmeticFrobenius K n y := by
    ring
  rw [hadd] at htriangle
  have hcanonical' :
      ‖y ^ localResidueCardinality K - canonicalArithmeticFrobenius K n y‖ < 1 := by
    rwa [norm_sub_rev]
  exact htriangle.trans_lt (max_lt hσ' hcanonical')

end

end Submission.CField.LFTheory
