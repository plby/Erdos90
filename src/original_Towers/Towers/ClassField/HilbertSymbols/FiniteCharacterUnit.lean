import Mathlib.GroupTheory.FiniteAbelian.Duality
import Towers.ClassField.HilbertSymbols.FiniteCupTorsion

/-!
# Milne, Class Field Theory, Remark III.4.6

The existence theorem will identify `Kˣ/Kˣⁿ` with the Galois group of the
largest finite abelian extension of exponent `n`.  Independently of that
future theorem, the finite group theory in Milne's cardinality argument is
already unconditional: a finite abelian group killed by `n` has as many
`Z/nZ`-valued characters as elements, those characters separate points, and
a left-nondegenerate pairing between two equal-size such groups is perfect.

The final section packages the precise finite-Artin identification that the
existence theorem would supply, as an implication rather than an assumption.
-/

namespace Towers.CField.HSymbol

open Towers.CField.LFTheory
open Towers.CField.LTate
open Towers.CField.LRecip
open Towers.CField.KTheory

noncomputable section

section FiniteDuality

variable (G : Type) [CommGroup G] [Finite G]
variable (K : Type) [Field K]
variable (n : ℕ) [NeZero n] {ζ : K} (hζ : IsPrimitiveRoot ζ n)
variable (hpow : ∀ g : G, g ^ n = 1)

/-- Convert a `Z/nZ`-valued additive character into a unit-valued character
using the chosen primitive root. -/
noncomputable def characterUnit
    (χ : FiniteCharacter G n) : G →* Kˣ :=
  (rootsOfUnity n K).subtype.comp
    ((zmodAddUnity hζ).toMultiplicative.toMonoidHom.comp
      χ.toMultiplicative)

/-- Every unit-valued character of an exponent-`n` group lands in `μ_n`,
and hence has a unique `Z/nZ` coordinate. -/
noncomputable def unitCharacterFinite
    (φ : G →* Kˣ) : FiniteCharacter G n :=
  (zmodAddUnity hζ).symm.toAddMonoidHom.comp
    ((φ.codRestrict (rootsOfUnity n K) fun g => by
      rw [mem_rootsOfUnity, ← map_pow, hpow g, map_one]).toAdditive)

/-- The preceding constructions are inverse. -/
noncomputable def finiteCharacterUnit :
    FiniteCharacter G n ≃ (G →* Kˣ) where
  toFun := characterUnit G K n hζ
  invFun := unitCharacterFinite G K n hζ hpow
  left_inv χ := by
    apply AddMonoidHom.ext
    intro g
    apply (zmodAddUnity hζ).injective
    change zmodAddUnity hζ
        ((zmodAddUnity hζ).symm
          (zmodAddUnity hζ (χ g))) =
      zmodAddUnity hζ (χ g)
    rw [AddEquiv.apply_symm_apply]
  right_inv φ := by
    apply MonoidHom.ext
    intro g
    let φr : G →* rootsOfUnity n K :=
      φ.codRestrict (rootsOfUnity n K) fun x => by
        rw [mem_rootsOfUnity, ← map_pow, hpow x, map_one]
    apply Units.ext
    change (((Additive.toMul
      (zmodAddUnity hζ
        ((zmodAddUnity hζ).symm
          (Additive.ofMul (φr g)))) : rootsOfUnity n K) : Kˣ) : K) =
      (φ g : K)
    rw [AddEquiv.apply_symm_apply]
    rfl

/-- A primitive `n`th root in the target field supplies all roots needed for
duality of a finite group whose exponent divides `n`. -/
@[reducible] private noncomputable def enoughRootsExponent :
    HasEnoughRootsOfUnity K (Monoid.exponent G) := by
  letI : HasEnoughRootsOfUnity K n :=
    HasEnoughRootsOfUnity.of_card_le (by
      rw [hζ.card_rootsOfUnity])
  exact HasEnoughRootsOfUnity.of_dvd K
    ((Monoid.exponent_dvd_iff_forall_pow_eq_one).2 hpow)

include K hζ hpow in
/-- **Remark III.4.6, finite dual cardinality.**  A finite abelian group
killed by `n` and its `Z/nZ` character group have the same order. -/
theorem nat_card_character :
    Nat.card (FiniteCharacter G n) = Nat.card G := by
  letI : HasEnoughRootsOfUnity K (Monoid.exponent G) :=
    enoughRootsExponent G K n hζ hpow
  calc
    Nat.card (FiniteCharacter G n) = Nat.card (G →* Kˣ) :=
      Nat.card_congr (finiteCharacterUnit G K n hζ hpow)
    _ = Nat.card G :=
      CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity G K

include K hζ hpow in
/-- The same finite characters separate points. -/
theorem finiteCharacter_separates {g : G}
    (hg : ∀ χ : FiniteCharacter G n, χ (Additive.ofMul g) = 0) :
    g = 1 := by
  letI : HasEnoughRootsOfUnity K (Monoid.exponent G) :=
    enoughRootsExponent G K n hζ hpow
  rw [← CommGroup.forall_apply_eq_apply_iff (G := G) (M := K)]
  intro φ
  rw [map_one]
  let φr : G →* rootsOfUnity n K :=
    φ.codRestrict (rootsOfUnity n K) fun x => by
      rw [mem_rootsOfUnity, ← map_pow, hpow x, map_one]
  let χ := unitCharacterFinite G K n hζ hpow φ
  have hχ := hg χ
  have hh := congrArg (zmodAddUnity hζ) hχ
  change zmodAddUnity hζ
      ((zmodAddUnity hζ).symm
        (Additive.ofMul (φr g))) =
    zmodAddUnity hζ 0 at hh
  rw [AddEquiv.apply_symm_apply, map_zero] at hh
  have hr := congrArg Additive.toMul hh
  change φr g = 1 at hr
  exact congrArg Subtype.val hr

end FiniteDuality

section PerfectPairing

variable {A B : Type} [AddCommGroup A] [AddCommGroup B] [Finite B]
variable (K : Type) [Field K]
variable (n : ℕ) [NeZero n] {ζ : K} (hζ : IsPrimitiveRoot ζ n)
variable (hBpow : ∀ b : B, n • b = 0)

include K hζ hBpow in
/-- Equal cardinalities and a trivial left kernel upgrade a finite bilinear
pairing to a perfect pairing.  This is the cardinality argument in Remark
III.4.6. -/
theorem bot_nondegenerate_card
    (pairing : A →+ (B →+ ZMod n))
    (hleft : Function.Injective pairing)
    (hcard : Nat.card A = Nat.card B) :
    ∀ b : B, (∀ a : A, pairing a b = 0) → b = 0 := by
  have hpowMul : ∀ b : Multiplicative B,
      b ^ n = 1 := by
    intro b
    exact congrArg Multiplicative.ofAdd (hBpow b.toAdd)
  have hdualCard : Nat.card (B →+ ZMod n) = Nat.card B := by
    simpa using nat_card_character
      (Multiplicative B) K n hζ hpowMul
  letI : Finite (B →+ ZMod n) :=
    Finite.of_injective (fun f : B →+ ZMod n => (f : B → ZMod n))
      DFunLike.coe_injective
  have hpairCard : Nat.card A = Nat.card (B →+ ZMod n) :=
    hcard.trans hdualCard.symm
  have hsurj : Function.Surjective pairing :=
    (Nat.bijective_iff_injective_and_card pairing).2
      ⟨hleft, hpairCard⟩ |>.2
  intro b hb
  apply Additive.toMul.injective
  apply finiteCharacter_separates (Multiplicative B) K n hζ hpowMul
  intro χ
  obtain ⟨a, rfl⟩ := hsurj χ
  exact hb a

end PerfectPairing

section FiniteArtin

variable (K L : Type)
  [NontriviallyNormedField K] [IsUltrametricDist K]

local instance finiteCharacterToUnitCharacterValuativeRel : ValuativeRel K :=
  ValuativeRel.ofValuation (NormedField.valuation (K := K))

local instance finiteCharacterToUnitCharacterValuationCompatible :
    Valuation.Compatible (NormedField.valuation (K := K)) :=
  Valuation.Compatible.ofValuation (NormedField.valuation (K := K))

variable [IsNonarchimedeanLocalField K]
  [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
  [IsMulCommutative Gal(L/K)]

/-- The exact finite-level identification whose existence for a largest
exponent-`n` extension is promised by the later existence theorem. -/
def ExistenceIdentification (n : ℕ) : Prop :=
  normSubgroup K L = (powMonoidHom n : Kˣ →* Kˣ).range

/-- If the future existence theorem supplies the preceding norm-group
identity, finite Artin reciprocity immediately identifies power classes with
the Galois group. -/
theorem power_gal_reduction (n : ℕ) :
    ExistenceIdentification K L n →
      Nonempty (PowerClassGroup K n ≃* Gal(L/K)) := by
  intro hnorm
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hnorm.symm).trans
    (abelianLocalArtin K L)⟩

/-- Under the same future norm-group identification, the power-class group
and the `Z/nZ` character group of the exponent-`n` Galois group have the
same order, exactly as asserted in Remark III.4.6. -/
theorem card_character_reduction
    (n : ℕ) [NeZero n] {ζ : K} (hζ : IsPrimitiveRoot ζ n)
    (hpow : ∀ σ : Gal(L/K), σ ^ n = 1) :
    ExistenceIdentification K L n →
      Nat.card (PowerClassGroup K n) =
        Nat.card (FiniteCharacter Gal(L/K) n) := by
  intro hnorm
  letI : CommGroup Gal(L/K) :=
    { (inferInstance : Group Gal(L/K)) with
      mul_comm := mul_comm' }
  let e : PowerClassGroup K n ≃* Gal(L/K) :=
    (QuotientGroup.quotientMulEquivOfEq hnorm.symm).trans
      (abelianLocalArtin K L)
  calc
    Nat.card (PowerClassGroup K n) = Nat.card Gal(L/K) :=
      Nat.card_congr e.toEquiv
    _ = Nat.card (FiniteCharacter Gal(L/K) n) :=
      (nat_card_character Gal(L/K) K n hζ hpow).symm

end FiniteArtin

end

end Towers.CField.HSymbol
