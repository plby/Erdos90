import Submission.ClassField.LocalBrauer.UnramifiedH2
import Submission.ClassField.LocalBrauer.LocalInvariantTorsion

/-!
# Chapter IV, Section 4: the finite unramified invariant

For an unramified cyclic extension of degree `n`, the relative Brauer group is
already identified with `ZMod n`.  Composing that calculation with the
canonical embedding of `ZMod n` as the `n`-torsion in `\mathbb{Q}/\mathbb{Z}`
gives the finite-level local invariant.  Milne's carry crossed product maps to
`1 / n`.
-/

namespace Submission.CField.LBrauer

noncomputable section

universe u

open ValuativeRel
open BGroups
open CProduca

attribute [local instance] Units.mulDistribMulActionRight

/-- The canonical generator `1 / n` of the `n`-torsion subgroup of the local
invariant group. -/
def localDivTorsion (n : ℕ) [NeZero n] :
    localInvariantTorsion n :=
  torsionZMod n (1 : ZMod n)

@[simp]
theorem invariant_div_coe (n : ℕ) [NeZero n] :
    ((localDivTorsion n : localInvariantTorsion n) :
        LocalInvariant) =
      ((1 : ℚ) / (n : ℚ) : LocalInvariant) := by
  rw [localDivTorsion,
    torsion_z_coe]
  simpa using zmod_invariant_cast n 1

variable (K L : Type u) [NontriviallyNormedField K] [IsUltrametricDist K]
  [ValuativeRel K] [IsNonarchimedeanLocalField K]
  [Valuation.Compatible (NormedField.valuation (K := K))]
  [NontriviallyNormedField L] [IsUltrametricDist L] [ValuativeRel L]
  [IsNonarchimedeanLocalField L]
  [Valuation.Compatible (NormedField.valuation (K := L))]
  [Algebra K L] [Module.Finite K L] [IsGalois K L]
  [Algebra 𝓀[K] 𝓀[L]]

variable {n : ℕ} [NeZero n]

/-- The finite-level local invariant for an unramified cyclic extension. -/
def unramifiedInvariantEquiv
    (eGal : Multiplicative (ZMod n) ≃* Gal(L/K)) (hn : 1 < n)
    (N : 𝒪[L]ˣ →* 𝒪[K]ˣ) (hN : UnramifiedLocalData K L N)
    (horderNorm : ∀ x : Lˣ,
      localUnitOrder K
          (Additive.ofMul (localNormUnits K L x)) =
        (n : ℤ) * localUnitOrder L (Additive.ofMul x)) :
    relativeBrauerGroup K L ≃*
      Multiplicative (localInvariantTorsion n) :=
  (unramifiedZMod
      K L eGal hn N hN horderNorm).trans
    (torsionZMod n).toMultiplicative

/-- After forgetting the torsion subtype, the finite invariant is the
existing `ZMod n` invariant followed by `m ↦ m / n` in `\mathbb{Q}/\mathbb{Z}`. -/
theorem unramified_mul_coe
    (eGal : Multiplicative (ZMod n) ≃* Gal(L/K)) (hn : 1 < n)
    (N : 𝒪[L]ˣ →* 𝒪[K]ˣ) (hN : UnramifiedLocalData K L N)
    (horderNorm : ∀ x : Lˣ,
      localUnitOrder K
          (Additive.ofMul (localNormUnits K L x)) =
        (n : ℤ) * localUnitOrder L (Additive.ofMul x))
    (x : relativeBrauerGroup K L) :
    ((unramifiedInvariantEquiv K L eGal hn N hN horderNorm x).toAdd :
        LocalInvariant) =
      zmodLocalInvariant n
        ((unramifiedZMod
          K L eGal hn N hN horderNorm x).toAdd) :=
  rfl

/-- The finite invariant of the carry class attached to an arbitrary
base-field unit is its normalized order in `ZMod n`. -/
theorem unramified_mul_carry
    (eGal : Multiplicative (ZMod n) ≃* Gal(L/K)) (hn : 1 < n)
    (N : 𝒪[L]ˣ →* 𝒪[K]ˣ) (hN : UnramifiedLocalData K L N)
    (horderNorm : ∀ x : Lˣ,
      localUnitOrder K
          (Additive.ofMul (localNormUnits K L x)) =
        (n : ℤ) * localUnitOrder L (Additive.ofMul x))
    (a : Kˣ) :
    unramifiedInvariantEquiv K L eGal hn N hN horderNorm
        (unramifiedCarryRelative K L eGal a) =
      Multiplicative.ofAdd
        (torsionZMod n
          (localUnitOrder K (Additive.ofMul a) : ZMod n)) := by
  change Multiplicative.ofAdd
      (torsionZMod n
        (unramifiedZMod
          K L eGal hn N hN horderNorm
          (unramifiedCarryRelative K L eGal a)).toAdd) = _
  rw [unramified_z_carry
    K L eGal hn N hN horderNorm a]
  rfl

/-- In `ℚ/ℤ`, the finite invariant of the carry class attached to `a` is
`ord(a) / n`. -/
theorem unramified_carry_coe
    (eGal : Multiplicative (ZMod n) ≃* Gal(L/K)) (hn : 1 < n)
    (N : 𝒪[L]ˣ →* 𝒪[K]ˣ) (hN : UnramifiedLocalData K L N)
    (horderNorm : ∀ x : Lˣ,
      localUnitOrder K
          (Additive.ofMul (localNormUnits K L x)) =
        (n : ℤ) * localUnitOrder L (Additive.ofMul x))
    (a : Kˣ) :
    ((unramifiedInvariantEquiv K L eGal hn N hN horderNorm
        (unramifiedCarryRelative K L eGal a)).toAdd :
          LocalInvariant) =
      (((localUnitOrder K (Additive.ofMul a) : ℤ) : ℚ) /
        (n : ℚ) : LocalInvariant) := by
  rw [unramified_mul_carry
    K L eGal hn N hN horderNorm a]
  change
    ((torsionZMod n
        (localUnitOrder K (Additive.ofMul a) : ZMod n) :
      localInvariantTorsion n) : LocalInvariant) = _
  rw [torsion_z_coe,
    zmod_int_cast]

/-- Milne's carry relative Brauer class maps to the torsion element `1 / n`. -/
theorem unramified_equiv_carry
    (eGal : Multiplicative (ZMod n) ≃* Gal(L/K)) (hn : 1 < n)
    (N : 𝒪[L]ˣ →* 𝒪[K]ˣ) (hN : UnramifiedLocalData K L N)
    (horderNorm : ∀ x : Lˣ,
      localUnitOrder K
          (Additive.ofMul (localNormUnits K L x)) =
        (n : ℤ) * localUnitOrder L (Additive.ofMul x))
    (varpiK : Kˣ)
    (hvarpiK : localUnitOrder K (Additive.ofMul varpiK) = 1) :
    unramifiedInvariantEquiv K L eGal hn N hN horderNorm
        (unramifiedCarryRelative K L eGal varpiK) =
      Multiplicative.ofAdd (localDivTorsion n) := by
  rw [unramified_mul_carry
    K L eGal hn N hN horderNorm varpiK, hvarpiK]
  apply Multiplicative.toAdd.injective
  simp [localDivTorsion]

/-- In `\mathbb{Q}/\mathbb{Z}`, the invariant of Milne's carry relative
Brauer class is exactly `1 / n`. -/
theorem unramified_invariant_coe
    (eGal : Multiplicative (ZMod n) ≃* Gal(L/K)) (hn : 1 < n)
    (N : 𝒪[L]ˣ →* 𝒪[K]ˣ) (hN : UnramifiedLocalData K L N)
    (horderNorm : ∀ x : Lˣ,
      localUnitOrder K
          (Additive.ofMul (localNormUnits K L x)) =
        (n : ℤ) * localUnitOrder L (Additive.ofMul x))
    (varpiK : Kˣ)
    (hvarpiK : localUnitOrder K (Additive.ofMul varpiK) = 1) :
    ((unramifiedInvariantEquiv K L eGal hn N hN horderNorm
        (unramifiedCarryRelative K L eGal varpiK)).toAdd :
        LocalInvariant) =
      ((1 : ℚ) / (n : ℚ) : LocalInvariant) := by
  rw [unramified_equiv_carry
    K L eGal hn N hN horderNorm varpiK hvarpiK]
  exact invariant_div_coe n

end

end Submission.CField.LBrauer
