import Towers.ClassField.ArtinLSeries.GaussCoefficientUniqueness
import Mathlib.GroupTheory.OrderOfElement

/-!
# Gauss's Fermat cubic at nonsplit primes

When `p ≠ 1 (mod 3)`, cubing is a bijection on `ZMod p`.  The two affine
charts of the projective Fermat cubic then have respectively `p` and `1`
points, giving Gauss's elementary count `Nₚ = p + 1`.
-/

namespace Towers.CField.ALSeries

noncomputable section

/-- Cubing is bijective on `ZMod p` when the prime `p` is not one modulo
three.  This includes `p = 3`, where cubing is the Frobenius identity. -/
theorem zmod_cube_bijective
    (p : ℕ) [Fact p.Prime] (hpmod : p % 3 ≠ 1) :
    Function.Bijective (fun x : ZMod p ↦ x ^ 3) := by
  by_cases hp3 : p = 3
  · subst p
    have hfun : (fun x : ZMod 3 ↦ x ^ 3) = id := by
      funext x
      exact ZMod.pow_card x
    rw [hfun]
    exact Function.bijective_id
  · have hpmod2 : p % 3 = 2 := by
      have hpmodlt : p % 3 < 3 := Nat.mod_lt _ (by norm_num)
      have hpmod0 : p % 3 ≠ 0 := by
        intro hpzero
        have hpdiv : 3 ∣ p := Nat.dvd_iff_mod_eq_zero.mpr hpzero
        exact hp3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three
          (Fact.out : p.Prime)).mp hpdiv).symm
      omega
    have hcoprime : (p - 1).Coprime 3 := by
      apply Nat.coprime_of_mul_modEq_one 1
      change (p - 1) * 1 % 3 = 1 % 3
      omega
    have hunitCoprime : (Nat.card (ZMod p)ˣ).Coprime 3 := by
      have hcard : Nat.card (ZMod p) = p := Nat.card_zmod p
      rw [Nat.card_units, hcard]
      exact hcoprime
    have hunitCube : Function.Bijective (fun x : (ZMod p)ˣ ↦ x ^ 3) :=
      hunitCoprime.pow_left_bijective
    constructor
    · intro x y hxy
      by_cases hx : x = 0
      · subst x
        have hy : y = 0 := by
          by_contra hy0
          exact (pow_ne_zero 3 hy0) (by simpa using hxy.symm)
        exact hy.symm
      · have hy : y ≠ 0 := by
          intro hy
          subst y
          apply hx
          by_contra hx0
          exact (pow_ne_zero 3 hx0) (by simpa using hxy)
        let xu : (ZMod p)ˣ := Units.mk0 x hx
        let yu : (ZMod p)ˣ := Units.mk0 y hy
        have hxyu : xu ^ 3 = yu ^ 3 := by
          apply Units.ext
          exact hxy
        exact congrArg Units.val (hunitCube.1 hxyu)
    · intro y
      by_cases hy : y = 0
      · exact ⟨0, by simp [hy]⟩
      · let yu : (ZMod p)ˣ := Units.mk0 y hy
        obtain ⟨xu, hxu⟩ := hunitCube.2 yu
        refine ⟨(xu : ZMod p), ?_⟩
        exact congrArg Units.val hxu

/-- If cubing is bijective, the first affine chart of the Fermat cubic has
exactly one point above each `Y`-coordinate. -/
noncomputable def fermatCubicChart
    (p : ℕ) [Fact p.Prime]
    (hcube : Function.Bijective (fun x : ZMod p ↦ x ^ 3)) :
    FermatCubicChart p ≃ ZMod p := by
  let cubeEquiv : ZMod p ≃ ZMod p :=
    Equiv.ofBijective (fun x : ZMod p ↦ x ^ 3) hcube
  let root (y : ZMod p) : ZMod p := cubeEquiv.symm (-1 - y ^ 3)
  have hroot (y : ZMod p) : root y ^ 3 = -1 - y ^ 3 := by
    change cubeEquiv (cubeEquiv.symm (-1 - y ^ 3)) = -1 - y ^ 3
    exact cubeEquiv.apply_symm_apply _
  refine
    { toFun := fun q ↦ q.1.1
      invFun := fun y ↦ ⟨(y, root y), by rw [hroot]; ring⟩
      left_inv := ?_
      right_inv := fun _ ↦ rfl }
  intro q
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · apply hcube.1
    change root q.1.1 ^ 3 = q.1.2 ^ 3
    have hq := q.2
    rw [hroot]
    linear_combination -hq

/-- If cubing is bijective, the second affine chart has its unique point
`(0 : 1 : cubeRoot(-1))`. -/
theorem gauss_fermat_chart
    (p : ℕ) [Fact p.Prime]
    (hcube : Function.Bijective (fun x : ZMod p ↦ x ^ 3)) :
    Fintype.card (GaussFermatChart p) = 1 := by
  let cubeEquiv : ZMod p ≃ ZMod p :=
    Equiv.ofBijective (fun x : ZMod p ↦ x ^ 3) hcube
  let z : ZMod p := cubeEquiv.symm (-1)
  have hz : z ^ 3 = -1 := cubeEquiv.apply_symm_apply (-1)
  let q : GaussFermatChart p := ⟨z, by rw [hz]; ring⟩
  letI : Unique (GaussFermatChart p) :=
    { default := q
      uniq := fun x ↦ by
        apply Subtype.ext
        apply hcube.1
        have hx := x.2
        change x.1 ^ 3 = z ^ 3
        rw [hz]
        linear_combination hx }
  exact Fintype.card_unique

/-- Gauss's nonsplit point count: the projective Fermat cubic has `p + 1`
points at every prime not congruent to one modulo three. -/
theorem gauss_fermat_cubic
    (p : ℕ) [Fact p.Prime] (hpmod : p % 3 ≠ 1) :
    gaussFermatCount p = p + 1 := by
  let hcube := zmod_cube_bijective p hpmod
  have hfirst : Fintype.card (FermatCubicChart p) = p := by
    calc
      Fintype.card (FermatCubicChart p) = Fintype.card (ZMod p) :=
        Fintype.card_congr (fermatCubicChart p hcube)
      _ = p := ZMod.card p
  have hsecond : Fintype.card (GaussFermatChart p) = 1 :=
    gauss_fermat_chart p hcube
  change Fintype.card
      (FermatCubicChart p ⊕ GaussFermatChart p) = p + 1
  rw [Fintype.card_sum, hfirst, hsecond]

/-- The nonsplit half of the point-count bridge used by the corrected
source statement is now unconditional. -/
theorem gauss_fermat_ne
    (p : ℕ) [Fact p.Prime] (hpmod : p % 3 ≠ 1) :
    (gaussFermatCount p : ℤ) = (p : ℤ) + 1 := by
  exact_mod_cast gauss_fermat_cubic p hpmod

/-- The genuinely arithmetic part still needed for Gauss's theorem: the
point count at primes split in the Eisenstein field. -/
def GaussFermatPoint : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], p % 3 = 1 → ∀ A : ℤ,
    GaussNormalizedCoefficient p A →
      (gaussFermatCount p : ℤ) = (p : ℤ) + 1 + A

/-- The full point-count bridge used previously follows from its split half;
the nonsplit half is the unconditional cube-bijection calculation above. -/
theorem gauss_fermat_split
    (hsplit : GaussFermatPoint) :
    GaussFermatBridge := by
  intro p _
  constructor
  · exact gauss_fermat_ne p
  · exact hsplit p

/-- The corrected Gauss source statement now requires only uniqueness of
the normalized coefficient and the split-prime cubic point count. -/
theorem fermat_point_bridge
    (hunique : GaussUniquenessBridge)
    (hsplit : GaussFermatPoint) :
    (∀ (p : ℕ) [Fact p.Prime],
          (p % 3 ≠ 1 →
            (gaussFermatCount p : ℤ) = (p : ℤ) + 1) ∧
          (p % 3 = 1 →
            (∃! A : ℤ, GaussNormalizedCoefficient p A) ∧
            ∀ A : ℤ, GaussNormalizedCoefficient p A →
              (gaussFermatCount p : ℤ) = (p : ℤ) + 1 + A)) :=
  fermat_point_bridges hunique
    (gauss_fermat_split hsplit)

/-- After discharging coefficient uniqueness by Eisenstein factorization,
only the split-prime point-count calculation remains as an input to Gauss's
corrected theorem. -/
theorem fermat_point_split
    (hsplit : GaussFermatPoint) :
    (∀ (p : ℕ) [Fact p.Prime],
          (p % 3 ≠ 1 →
            (gaussFermatCount p : ℤ) = (p : ℤ) + 1) ∧
          (p % 3 = 1 →
            (∃! A : ℤ, GaussNormalizedCoefficient p A) ∧
            ∀ A : ℤ, GaussNormalizedCoefficient p A →
              (gaussFermatCount p : ℤ) = (p : ℤ) + 1 + A)) :=
  fermat_point_bridge
    gaussNormalizedUniqueness hsplit

end

end Towers.CField.ALSeries
