import Towers.ClassField.LocalReciprocity.TransportedProduct
import Towers.ClassField.HilbertSymbols.ContinuousAddRange

/-!
# Proposition III.4.3 at a finite abelian level

Milne proves triviality of the left kernel by evaluating a character on the
dense image of the absolute local Artin map.  At one finite abelian level,
density is simply surjectivity.  This file proves that finite statement
unconditionally and records the exact reduction of the cup-product statement
to Proposition III.3.6.
-/

namespace Towers.CField.HSymbol

open Towers.CField.LFTheory
open Towers.CField.LClass
open Towers.CField.LRecip
open Towers.CField.LBrauer

noncomputable section

/-- A finite `Z/nZ`-valued character, without an unnecessary commutative
typeclass on its source group. -/
abbrev FiniteCharacter (G : Type) [Group G] (n : ℕ) :=
  Additive G →+ ZMod n

/-- Embed a `Z/nZ`-valued character into a `Q/Z`-valued character using
the canonical degree-`n` torsion subgroup of the local invariant. -/
noncomputable def finiteCharacterRational
  (G : Type) [Group G] (n : ℕ) [NeZero n]
    (χ : FiniteCharacter G n) : RationalCharacter G :=
  (localInvariantTorsion n).subtype.comp
    ((torsionZMod n).toAddMonoidHom.comp χ)

theorem character_rational_injective
    (G : Type) [Group G] (n : ℕ) [NeZero n] :
    Function.Injective (finiteCharacterRational G n) := by
  intro χ ψ h
  apply AddMonoidHom.ext
  intro g
  apply (torsionZMod n).injective
  apply Subtype.ext
  exact DFunLike.congr_fun h g

@[simp]
theorem nsmul_character_rational
    (G : Type) [Group G] (n : ℕ) [NeZero n]
    (χ : FiniteCharacter G n) :
    n • finiteCharacterRational G n χ = 0 := by
  apply AddMonoidHom.ext
  intro g
  change n •
      (((torsionZMod n) (χ g) :
        localInvariantTorsion n) : LocalInvariant) = 0
  exact (torsionZMod n (χ g)).property

variable (K L : Type)
  [NontriviallyNormedField K] [IsUltrametricDist K]

local instance finiteCharacterValuativeRel : ValuativeRel K :=
  ValuativeRel.ofValuation (NormedField.valuation (K := K))

local instance finiteCharacterValuationCompatible :
    Valuation.Compatible (NormedField.valuation (K := K)) :=
  Valuation.Compatible.ofValuation (NormedField.valuation (K := K))

variable [IsNonarchimedeanLocalField K]
  [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
  [IsMulCommutative Gal(L/K)]

/-- The finite abelian local Artin homomorphism is onto.  This is the
finite-level form of the density input in Milne's proof. -/
theorem abelian_artin_surjective :
    Function.Surjective (abelianArtinHom K L) := by
  intro σ
  let q := (abelianLocalArtin K L).symm σ
  obtain ⟨a, ha⟩ := QuotientGroup.mk'_surjective
    (normSubgroup K L) q
  refine ⟨a, ?_⟩
  change abelianLocalArtin K L
    (QuotientGroup.mk' (normSubgroup K L) a) = σ
  rw [ha]
  exact (abelianLocalArtin K L).apply_symm_apply σ

/-- **Proposition III.4.3, unconditional finite-character core.**  A
`Z/nZ`-valued character which vanishes on every value of the finite local
Artin map is zero. -/
theorem character_artin_evaluation
    (n : ℕ) (χ : FiniteCharacter Gal(L/K) n)
    (hχ : ∀ a : Kˣ,
      χ (Additive.ofMul (abelianArtinHom K L a)) = 0) :
    χ = 0 := by
  apply AddMonoidHom.ext
  intro σ
  obtain ⟨a, ha⟩ := abelian_artin_surjective K L σ.toMul
  have ha' : Additive.ofMul (abelianArtinHom K L a) = σ :=
    congrArg Additive.ofMul ha
  rw [← ha']
  exact hχ a

/-- Equivalently, a nonzero finite character has a nonzero value on some
finite local Artin symbol. -/
theorem artin_evaluation_character
    (n : ℕ) (χ : FiniteCharacter Gal(L/K) n) (hχ : χ ≠ 0) :
    ∃ a : Kˣ,
      χ (Additive.ofMul (abelianArtinHom K L a)) ≠ 0 := by
  by_contra h
  apply hχ
  apply character_artin_evaluation K L n χ
  intro a
  by_contra ha
  exact h ⟨a, ha⟩

/-- The finite-level cup-pairing statement whose left kernel is asserted
to be zero in Proposition III.4.3.  The character is embedded in `Q/Z`
before applying the pairing constructed for Proposition III.3.6. -/
def CupPairingZero (n : ℕ) [NeZero n] : Prop :=
  ∀ χ : FiniteCharacter Gal(L/K) n,
    (∀ a : Kˣ,
      characterCupInvariant K L a
        (finiteCharacterRational Gal(L/K) n χ) = 0) →
      χ = 0

/-- For a fixed base-field unit, the cup invariant is additive in the
character variable. -/
noncomputable def characterInvariant (a : Kˣ) :
    RationalCharacter Gal(L/K) →+ LocalInvariant where
  toFun χ := characterCupInvariant K L a χ
  map_zero' := by
    have h := character_cup_add K L a
      (0 : RationalCharacter Gal(L/K)) 0
    apply add_left_cancel
      (a := characterCupInvariant K L a
        (0 : RationalCharacter Gal(L/K)))
    rw [add_zero, ← h, zero_add]
  map_add' χ ψ := character_cup_add K L a χ ψ

omit [IsMulCommutative Gal(L/K)] in
/-- The finite-character cup invariant depends only on the class of the
base unit modulo `n`th powers, as in Milne's source pairing on
`Kˣ / Kˣⁿ`. -/
theorem character_cup_invariant
    (n : ℕ) [NeZero n] (a : Kˣ)
    (χ : FiniteCharacter Gal(L/K) n) :
    characterCupInvariant K L (a ^ n)
      (finiteCharacterRational Gal(L/K) n χ) = 0 := by
  let χ' := finiteCharacterRational Gal(L/K) n χ
  have hchar := (characterInvariant K L a).map_nsmul n χ'
  rw [nsmul_character_rational,
    map_zero] at hchar
  change 0 = n • characterCupInvariant K L a χ' at hchar
  have hunit := (characterCup K L χ').map_nsmul
    n (Additive.ofMul a)
  change characterCupInvariant K L (a ^ n) χ' =
    n • characterCupInvariant K L a χ' at hunit
  rw [← hchar] at hunit
  simpa [χ'] using hunit

/-- Exact reduction of finite-level Proposition III.4.3 to the character
formula of Proposition III.3.6.  This theorem adds no field-theoretic or
cohomological hypothesis: its premise is precisely the full character
formula. -/
theorem cup_pairing_formula
    (n : ℕ) [NeZero n]
    (hformula : ∀ (a : Kˣ) (χ : FiniteCharacter Gal(L/K) n),
      CharacterFormula K L a
        (finiteCharacterRational Gal(L/K) n χ)) :
    CupPairingZero K L n := by
  intro χ hpair
  apply character_artin_evaluation K L n χ
  intro a
  apply (torsionZMod n).injective
  apply Subtype.ext
  have hf := hformula a χ
  change
    finiteCharacterRational Gal(L/K) n χ
        (Additive.ofMul (abelianArtinHom K L a)) =
      characterCupInvariant K L a
        (finiteCharacterRational Gal(L/K) n χ) at hf
  rw [hpair a] at hf
  simpa [finiteCharacterRational] using hf

/-- **Proposition III.4.3.**  The finite local cup pairing has trivial left
kernel.  This is the finite-character form of Milne's proposition; the
character formula is Proposition III.3.6. -/
theorem finiteCharacter (n : ℕ) [NeZero n] :
    CupPairingZero K L n := by
  apply cup_pairing_formula K L n
  intro a χ
  exact transportedCupBoundary K L a
    (finiteCharacterRational Gal(L/K) n χ)

end

end Towers.CField.HSymbol
