import Submission.ClassField.ArtinLSeries.SquareSumIdentity

/-!
# Chapter VIII, Section 10: Gauss's theorem on the Fermat cubic

The source ends with Gauss's point-count formula for the projective cubic
`X³ + Y³ + Z³ = 0`.  Its split-case formula is printed as `Nₚ = A`; as noted
in `GaussBound.lean`, the intended formula is `Nₚ = p + 1 + A`.

This file gives the corrected source statement an exact finite model.  A
projective point is represented in its unique first-nonzero-coordinate chart:
either `(1 : y : z)`, or `(0 : 1 : z)`.  The two hard arithmetic ingredients
in Gauss's theorem—the uniqueness of the normalized coefficient and the
point-count calculation—are isolated as narrow bridges.
-/

namespace Submission.CField.ALSeries

/-- The `X ≠ 0` chart of `X³ + Y³ + Z³ = 0`, normalized to `X = 1`. -/
abbrev FermatCubicChart (p : ℕ) :=
  {q : ZMod p × ZMod p // 1 + q.1 ^ 3 + q.2 ^ 3 = 0}

/-- The `X = 0`, `Y ≠ 0` chart of `X³ + Y³ + Z³ = 0`, normalized to `Y = 1`.
There is no third chart: `(0 : 0 : 1)` does not lie on the cubic. -/
abbrev GaussFermatChart (p : ℕ) :=
  {z : ZMod p // 1 + z ^ 3 = 0}

/-- A canonical finite model of the projective Fermat cubic over `ZMod p`. -/
abbrev GaussFermatPoints (p : ℕ) :=
  FermatCubicChart p ⊕ GaussFermatChart p

/-- The number `Nₚ` of projective points on `X³ + Y³ + Z³ = 0` over `ZMod p`. -/
noncomputable def gaussFermatCount (p : ℕ) [NeZero p] : ℕ := by
  classical
  exact Fintype.card (GaussFermatPoints p)

/-- The normalization imposed on `A` in the split case: `A ≡ 1 (mod 3)` and
`4p = A² + 27B²` for some integer `B`. -/
def GaussNormalizedCoefficient (p : ℕ) (A : ℤ) : Prop :=
  (A : ZMod 3) = 1 ∧
    ∃ B : ℤ, 4 * (p : ℤ) = A ^ 2 + 27 * B ^ 2

/-- Existence of the coefficient used in Gauss's split formula follows from
the integral normalization already formalized for Example 10.1. -/
theorem gauss_normalized_coefficient
    (p : ℕ) [Fact p.Prime] (hpmod : p % 3 = 1) :
    ∃ A : ℤ, GaussNormalizedCoefficient p A := by
  obtain ⟨A, B, hrep⟩ :=
    sq_twenty_seven p hpmod
  have hpcast : (p : ZMod 3) = 1 := by
    simp [← ZMod.natCast_mod p 3, hpmod]
  have hA_sq : (A : ZMod 3) ^ 2 = 1 := by
    have hcast := congrArg (fun z : ℤ ↦ (z : ZMod 3)) hrep
    simp only [Int.cast_mul, Int.cast_natCast, Int.cast_pow, Int.cast_add,
      Int.cast_ofNat] at hcast
    have hfour : (4 : ZMod 3) = 1 := by decide
    have htwentySeven : (27 : ZMod 3) = 0 := by decide
    calc
      (A : ZMod 3) ^ 2 =
          (A : ZMod 3) ^ 2 + 27 * (B : ZMod 3) ^ 2 := by
            rw [htwentySeven, zero_mul, add_zero]
      _ = 4 * (p : ZMod 3) := hcast.symm
      _ = 1 := by rw [hpcast, hfour, one_mul]
  have hsign : (A : ZMod 3) = 1 ∨ (-A : ℤ) = (1 : ZMod 3) := by
    have hfinite : ∀ a : ZMod 3, a ^ 2 = 1 → a = 1 ∨ -a = 1 := by decide
    simpa using hfinite (A : ZMod 3) hA_sq
  rcases hsign with hA | hA
  · exact ⟨A, hA, B, hrep⟩
  · refine ⟨-A, hA, B, ?_⟩
    nlinarith

/-- The elementary uniqueness input for the integer `A` selected by the
Eisenstein-integer factorization of a split prime. -/
def GaussUniquenessBridge : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], p % 3 = 1 →
    ∀ A A' : ℤ,
      GaussNormalizedCoefficient p A →
      GaussNormalizedCoefficient p A' → A = A'

/-- The actual finite-field calculation in Gauss's theorem, separated from
the already formalized integral normalization. -/
def GaussFermatBridge : Prop :=
  ∀ (p : ℕ) [Fact p.Prime],
    (p % 3 ≠ 1 →
      (gaussFermatCount p : ℤ) = (p : ℤ) + 1) ∧
    (p % 3 = 1 → ∀ A : ℤ,
      GaussNormalizedCoefficient p A →
        (gaussFermatCount p : ℤ) = (p : ℤ) + 1 + A)

/-- The corrected source statement follows from the two narrow arithmetic
inputs.  Existence of `A` is discharged by Example 10.1 rather than assumed. -/
theorem fermat_point_bridges
    (hunique : GaussUniquenessBridge)
    (hcount : GaussFermatBridge) :
    (∀ (p : ℕ) [Fact p.Prime],
          (p % 3 ≠ 1 →
            (gaussFermatCount p : ℤ) = (p : ℤ) + 1) ∧
          (p % 3 = 1 →
            (∃! A : ℤ, GaussNormalizedCoefficient p A) ∧
            ∀ A : ℤ, GaussNormalizedCoefficient p A →
              (gaussFermatCount p : ℤ) = (p : ℤ) + 1 + A)) := by
  intro p _
  constructor
  · exact (hcount p).1
  · intro hpmod
    constructor
    · obtain ⟨A, hA⟩ := gauss_normalized_coefficient p hpmod
      refine ⟨A, hA, ?_⟩
      intro A' hA'
      exact hunique p hpmod A' A hA' hA
    · exact (hcount p).2 hpmod

end Submission.CField.ALSeries
