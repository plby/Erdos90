import Towers.ClassField.HilbertSymbols.FiniteCharacter
import Towers.ClassField.HilbertSymbols.KummerNormCriterion

/-!
# Milne, Remark III.4.5: the Artin action on a Kummer root

For an irreducible Kummer extension, the Galois action on a chosen `n`th
root is explicitly measured by `ZMod n`.  This file constructs both the
Artin-defined root-of-unity multiplier and the multiplier obtained from the
cup invariant of Proposition III.3.6.
-/

namespace Towers.CField.HSymbol

open Polynomial
open Towers.CField.LRecip
open Towers.CField.LBrauer

noncomputable section

variable {K L : Type}
  [NontriviallyNormedField K] [IsUltrametricDist K]
  [Field L] [Algebra K L]
variable {n : ℕ} [NeZero n] {a ζ : K}
variable [IsSplittingField K L (X ^ n - C a)]

local instance kummerArtinValuativeRel : ValuativeRel K :=
  ValuativeRel.ofValuation (NormedField.valuation (K := K))

local instance kummerArtinValuationCompatible :
    Valuation.Compatible (NormedField.valuation (K := K)) :=
  Valuation.Compatible.ofValuation (NormedField.valuation (K := K))

variable [IsNonarchimedeanLocalField K]
  [FiniteDimensional K L] [IsGalois K L] [IsMulCommutative Gal(L/K)]

/-- The Kummer character `Gal(L/K) → Z/nZ` determined by the chosen
primitive root. -/
noncomputable def kummerFiniteCharacter
    (H : Irreducible (X ^ n - C a)) (hζ : IsPrimitiveRoot ζ n) :
    FiniteCharacter Gal(L/K) n where
  toFun σ := (autEquivZmod H L hζ σ.toMul).toAdd
  map_zero' := by
    change (autEquivZmod H L hζ 1).toAdd = 0
    rw [map_one]
    rfl
  map_add' σ τ := by
    have h := (autEquivZmod H L hζ).map_mul σ.toMul τ.toMul
    exact congrArg Multiplicative.toAdd h

/-- The exponent of the root-of-unity by which the finite Artin symbol of
`b` acts on the Kummer root. -/
noncomputable def artinKummerExponent
    (H : Irreducible (X ^ n - C a)) (hζ : IsPrimitiveRoot ζ n)
    (b : Kˣ) : ZMod n :=
  kummerFiniteCharacter (K := K) (L := L) H hζ
    (Additive.ofMul (abelianArtinHom K L b))

/-- The corresponding root of unity in the base field. -/
noncomputable def artinKummerSymbol
    (H : Irreducible (X ^ n - C a)) (hζ : IsPrimitiveRoot ζ n)
    (b : Kˣ) : K :=
  ζ ^ (artinKummerExponent (K := K) (L := L) H hζ b).val

/-- The purely algebraic Kummer-action formula for the finite local Artin
symbol. -/
theorem artin_kummer_root
    (H : Irreducible (X ^ n - C a)) (hζ : IsPrimitiveRoot ζ n)
    {alpha : L} (halpha : alpha ^ n = algebraMap K L a) (b : Kˣ) :
    abelianArtinHom K L b alpha =
      artinKummerSymbol (K := K) (L := L) H hζ b • alpha := by
  let e := autEquivZmod H L hζ
  let z := artinKummerExponent (K := K) (L := L) H hζ b
  have hsigma : abelianArtinHom K L b =
      e.symm (Multiplicative.ofAdd z) := by
    exact (e.symm_apply_apply (abelianArtinHom K L b)).symm
  rw [hsigma]
  change e.symm (Multiplicative.ofAdd z) alpha =
    ζ ^ z.val • alpha
  calc
    e.symm (Multiplicative.ofAdd z) alpha =
        e.symm (Multiplicative.ofAdd (z.val : ZMod n)) alpha := by
      rw [ZMod.natCast_zmod_val]
    _ = ζ ^ z.val • alpha :=
      autEquivZmod_symm_apply_natCast H L halpha hζ z.val

/-- The cup invariant attached to the Kummer character, restricted to the
canonical `n`-torsion subgroup of `Q/Z`. -/
noncomputable def cupKummerTorsion
    (H : Irreducible (X ^ n - C a)) (hζ : IsPrimitiveRoot ζ n)
    (b : Kˣ) : localInvariantTorsion n := by
  let chi := kummerFiniteCharacter (K := K) (L := L) H hζ
  let chiQ := finiteCharacterRational Gal(L/K) n chi
  refine ⟨characterCupInvariant K L b chiQ, ?_⟩
  have h := (characterInvariant K L b).map_nsmul n chiQ
  rw [nsmul_character_rational, map_zero] at h
  exact h.symm

/-- The `Z/nZ` coordinate of the cup-defined Kummer invariant. -/
noncomputable def cupKummerExponent
    (H : Irreducible (X ^ n - C a)) (hζ : IsPrimitiveRoot ζ n)
    (b : Kˣ) : ZMod n :=
  (torsionZMod n).symm
    (cupKummerTorsion (K := K) (L := L) H hζ b)

/-- The root-of-unity-valued symbol obtained from the cup invariant. -/
noncomputable def cupKummerSymbol
    (H : Irreducible (X ^ n - C a)) (hζ : IsPrimitiveRoot ζ n)
    (b : Kˣ) : K :=
  ζ ^ (cupKummerExponent (K := K) (L := L) H hζ b).val

/-- **Remark III.4.5, literal finite Kummer formula.**  This proposition
has no proof-assumption parameters: it says that the finite Artin symbol
acts on the chosen root through the cup-defined Hilbert multiplier. -/
def Formula
    (H : Irreducible (X ^ n - C a)) (hζ : IsPrimitiveRoot ζ n)
    (alpha : L) (b : Kˣ) : Prop :=
  abelianArtinHom K L b alpha =
    cupKummerSymbol (K := K) (L := L) H hζ b • alpha

/-- Proposition III.3.6 identifies the Artin and cup exponents for the
Kummer character. -/
theorem artin_kummer_formula
    (H : Irreducible (X ^ n - C a)) (hζ : IsPrimitiveRoot ζ n)
    (b : Kˣ)
    (hformula : CharacterFormula K L b
      (finiteCharacterRational Gal(L/K) n
        (kummerFiniteCharacter (K := K) (L := L) H hζ))) :
    artinKummerExponent (K := K) (L := L) H hζ b =
      cupKummerExponent (K := K) (L := L) H hζ b := by
  let e := torsionZMod n
  apply e.injective
  rw [show e (cupKummerExponent (K := K) (L := L) H hζ b) =
      cupKummerTorsion (K := K) (L := L) H hζ b by
    exact e.apply_symm_apply _]
  apply Subtype.ext
  simpa [e, artinKummerExponent, cupKummerTorsion,
    finiteCharacterRational] using hformula

/-- Exact reduction of Remark III.4.5 to Proposition III.3.6. -/
theorem formula_character
    (H : Irreducible (X ^ n - C a)) (hζ : IsPrimitiveRoot ζ n)
    {alpha : L} (halpha : alpha ^ n = algebraMap K L a) (b : Kˣ)
    (hformula : CharacterFormula K L b
      (finiteCharacterRational Gal(L/K) n
        (kummerFiniteCharacter (K := K) (L := L) H hζ))) :
    Formula (K := K) (L := L) H hζ alpha b := by
  unfold Formula cupKummerSymbol
  rw [← artin_kummer_formula
    (K := K) (L := L) H hζ b hformula]
  exact artin_kummer_root (K := K) (L := L) H hζ halpha b

end

end Towers.CField.HSymbol
