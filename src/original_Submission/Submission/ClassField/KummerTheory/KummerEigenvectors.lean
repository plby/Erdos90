import Submission.ClassField.KummerTheory.KummerRadicalPairing
import Mathlib.FieldTheory.Galois.NormalBasis

/-!
# Kummer eigenvectors from a normal basis

The decisive surjectivity input in Kummer theory is that every character of
a finite Galois group occurs on a nonzero vector of the extension.  We prove
this directly from the normal basis theorem: for a normal basis generator
`u` and a character `χ`, the resolvent

`xχ = ∑_g χ(g)⁻¹ g(u)`

is nonzero and satisfies `σ(xχ) = χ(σ) xχ`.  If the Galois group has
exponent dividing `n`, then `xχⁿ` lies in the base field.  Thus every
character is represented by a genuine Kummer radical.
-/

namespace Submission.CField.KTheory

noncomputable section

universe u

open scoped BigOperators

variable (K L : Type u) [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

/-- The normal-basis resolvent attached to a multiplicative character of
the Galois group. -/
def galoisCharacterEigenvector (χ : Gal(L/K) →* Kˣ) : L := by
  classical
  exact ∑ g : Gal(L/K), (((χ g)⁻¹ : Kˣ) : K) • IsGalois.normalBasis K L g

/-- Galois automorphisms translate the normal basis by left multiplication. -/
theorem gal_normal_basis (σ g : Gal(L/K)) :
    σ (IsGalois.normalBasis K L g) = IsGalois.normalBasis K L (σ * g) := by
  calc
    σ (IsGalois.normalBasis K L g) =
        σ (g (IsGalois.normalBasis K L 1)) :=
      congrArg σ (IsGalois.normalBasis_apply (K := K) (L := L) g)
    _ = (σ * g) (IsGalois.normalBasis K L 1) := rfl
    _ = IsGalois.normalBasis K L (σ * g) :=
      (IsGalois.normalBasis_apply (K := K) (L := L) (σ * g)).symm

/-- The resolvent is a `χ`-eigenvector. -/
theorem gal_character_eigenvector
    (χ : Gal(L/K) →* Kˣ) (σ : Gal(L/K)) :
    σ (galoisCharacterEigenvector K L χ) =
      algebraMap K L ((χ σ : Kˣ) : K) * galoisCharacterEigenvector K L χ := by
  let b := IsGalois.normalBasis K L
  let coeff : Gal(L/K) → K := fun g ↦ (((χ g)⁻¹ : Kˣ) : K)
  have htranslate (g : Gal(L/K)) : σ (b g) = b (σ * g) :=
    gal_normal_basis K L σ g
  have hcoeff (g : Gal(L/K)) :
      coeff g = ((χ σ : Kˣ) : K) * coeff (σ * g) := by
    change (((χ g)⁻¹ : Kˣ) : K) =
      ((χ σ : Kˣ) : K) * (((χ (σ * g))⁻¹ : Kˣ) : K)
    simpa only [Units.val_mul] using
      congrArg (fun z : Kˣ ↦ (z : K)) (show
        (χ g)⁻¹ = χ σ * (χ (σ * g))⁻¹ by
          calc
            (χ g)⁻¹ = (χ g)⁻¹ * 1 := by rw [mul_one]
            _ = (χ g)⁻¹ * (χ σ * (χ σ)⁻¹) := by rw [mul_inv_cancel]
            _ = χ σ * ((χ g)⁻¹ * (χ σ)⁻¹) := by ac_rfl
            _ = χ σ * (χ (σ * g))⁻¹ := by rw [map_mul, mul_inv_rev])
  calc
    σ (galoisCharacterEigenvector K L χ) =
        ∑ g : Gal(L/K), coeff g • σ (b g) := by
      simp only [galoisCharacterEigenvector, map_sum, map_smul, coeff, b]
    _ = ∑ g : Gal(L/K), coeff g • b (σ * g) := by
      apply Finset.sum_congr rfl
      intro g hg
      rw [htranslate]
    _ = ∑ g : Gal(L/K),
        ((χ σ : Kˣ) : K) • (coeff (σ * g) • b (σ * g)) := by
      apply Finset.sum_congr rfl
      intro g hg
      rw [hcoeff, mul_smul]
    _ = ((χ σ : Kˣ) : K) •
        ∑ g : Gal(L/K), coeff (σ * g) • b (σ * g) := by
      rw [Finset.smul_sum]
    _ = ((χ σ : Kˣ) : K) •
        ∑ g : Gal(L/K), coeff g • b g := by
      congr 1
      exact Fintype.sum_equiv (Equiv.mulLeft σ) _ _ (fun _ ↦ rfl)
    _ = algebraMap K L ((χ σ : Kˣ) : K) *
        galoisCharacterEigenvector K L χ := by
      simp [Algebra.smul_def, galoisCharacterEigenvector, coeff, b]

/-- The normal-basis resolvent never vanishes.  Its coordinate at the
identity basis vector is `χ(1)⁻¹ = 1`. -/
theorem galois_character_eigenvector (χ : Gal(L/K) →* Kˣ) :
    galoisCharacterEigenvector K L χ ≠ 0 := by
  let b := IsGalois.normalBasis K L
  intro hx
  have hcoord := congrArg (fun z : L ↦ (b.repr z) (1 : Gal(L/K))) hx
  have hleft : (b.repr (galoisCharacterEigenvector K L χ)) (1 : Gal(L/K)) = 1 := by
    rw [galoisCharacterEigenvector, b.repr_sum_self]
    simp
  change (b.repr (galoisCharacterEigenvector K L χ)) (1 : Gal(L/K)) =
    (b.repr (0 : L)) (1 : Gal(L/K)) at hcoord
  rw [hleft] at hcoord
  simp at hcoord

/-- The resolvent bundled as a nonzero unit. -/
def galoisCharacterEigenunit (χ : Gal(L/K) →* Kˣ) : Lˣ :=
  Units.mk0 (galoisCharacterEigenvector K L χ)
    (galois_character_eigenvector K L χ)

@[simp]
theorem gal_character_eigenunit
    (χ : Gal(L/K) →* Kˣ) (σ : Gal(L/K)) :
    Units.map σ (galoisCharacterEigenunit K L χ) =
      Units.map (algebraMap K L).toMonoidHom (χ σ) *
        galoisCharacterEigenunit K L χ := by
  apply Units.ext
  exact gal_character_eigenvector K L χ σ

/-- If the Galois group is killed by `n`, the `n`th power of every
character eigenvector lies in the base field. -/
theorem galois_eigenunit_base
    (n : ℕ) (hexponent : ∀ σ : Gal(L/K), σ ^ n = 1)
    (χ : Gal(L/K) →* Kˣ) :
    (galoisCharacterEigenunit K L χ : L) ^ n ∈
      (⊥ : IntermediateField K L) := by
  apply (IsGalois.mem_bot_iff_fixed _).2
  intro σ
  have hχpow : χ σ ^ n = 1 := by
    rw [← map_pow, hexponent, map_one]
  change σ ((galoisCharacterEigenunit K L χ : L) ^ n) = _
  rw [map_pow]
  change (σ (galoisCharacterEigenvector K L χ)) ^ n = _
  rw [gal_character_eigenvector, mul_pow]
  simp only [galoisCharacterEigenunit, Units.val_mk0]
  rw [← map_pow, ← Units.val_pow_eq_pow_val, hχpow, Units.val_one,
    map_one, one_mul]

/-- Explicit base element whose image is the `n`th power of the character
eigenvector. -/
theorem base_character_eigenunit
    (n : ℕ) (hexponent : ∀ σ : Gal(L/K), σ ^ n = 1)
    (χ : Gal(L/K) →* Kˣ) :
    ∃ a : K, algebraMap K L a = (galoisCharacterEigenunit K L χ : L) ^ n := by
  exact IntermediateField.mem_bot.mp
    (galois_eigenunit_base K L n hexponent χ)

end

end Submission.CField.KTheory
