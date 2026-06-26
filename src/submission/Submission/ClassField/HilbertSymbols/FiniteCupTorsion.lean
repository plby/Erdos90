import Submission.ClassField.LubinTate.CyclotomicRootsModule
import Submission.ClassField.HilbertSymbols.FiniteCyclicExtension
import Submission.ClassField.HilbertSymbols.FiniteCharacter
import Submission.ClassField.HilbertSymbols.NondegeneracyCore
import Submission.ClassField.HilbertSymbols.Nondegeneracy
import Submission.ClassField.KummerTheory.PowerClasses

/-!
# Milne, Class Field Theory, Theorem III.4.4

The lower finite-level cup pairing in Milne's Step 4 pairs a `Z/nZ`-valued
Galois character with a base-field unit and applies the finite local
invariant.  After choosing a primitive root, its values are honest `n`th
roots of unity.  This file constructs that pairing and proves its
multiplicative laws and invariance under `n`th powers.

`Theorem44Nondegeneracy` supplies the substantive Kummer argument: for each
power class it constructs the associated finite Kummer extension, factors
local reciprocity through `Kˣ/Kˣⁿ`, and uses the perfect Kummer pairing to
prove the left kernel trivial.  In characteristic zero it constructs the
full Kummer--Artin Hilbert pairing and proves bilinearity, skew symmetry,
triviality of both kernels, and the norm criterion for arbitrary
irreducible Kummer splitting-field models.
-/

namespace Submission.CField.HSymbol

open Submission.CField.LFTheory
open Submission.CField.LTate
open Submission.CField.LRecip
open Submission.CField.LBrauer
open Submission.CField.KTheory

noncomputable section

variable (K L : Type)
  [NontriviallyNormedField K] [IsUltrametricDist K]

local instance finiteHilbertCupTorsionValuativeRel : ValuativeRel K :=
  ValuativeRel.ofValuation (NormedField.valuation (K := K))

local instance finiteHilbertCupTorsionValuationCompatible :
    Valuation.Compatible (NormedField.valuation (K := K)) :=
  Valuation.Compatible.ofValuation (NormedField.valuation (K := K))

variable [IsNonarchimedeanLocalField K]
  [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
  [IsMulCommutative Gal(L/K)]

/-- The finite character cup invariant naturally lands in the `n`-torsion
of the local invariant group. -/
noncomputable def hilbertCupTorsion
    (n : ℕ) [NeZero n]
    (χ : FiniteCharacter Gal(L/K) n) (b : Kˣ) :
    localInvariantTorsion n := by
  let χ' := finiteCharacterRational Gal(L/K) n χ
  refine ⟨characterCupInvariant K L b χ', ?_⟩
  have h := (characterInvariant K L b).map_nsmul n χ'
  rw [nsmul_character_rational, map_zero] at h
  exact h.symm

/-- The same finite cup pairing in the canonical `Z/nZ` coordinate. -/
noncomputable def hilbertZMod
    (n : ℕ) [NeZero n]
    (χ : FiniteCharacter Gal(L/K) n) (b : Kˣ) : ZMod n :=
  (torsionZMod n).symm
    (hilbertCupTorsion K L n χ b)

/-- After choosing a primitive `n`th root in `K`, the finite cup pairing is
an actual `μ_n(K)`-valued pairing, as in Milne's Step 4. -/
noncomputable def hilbertCupRoot
    (n : ℕ) [NeZero n] {ζ : K} (hζ : IsPrimitiveRoot ζ n)
    (χ : FiniteCharacter Gal(L/K) n) (b : Kˣ) : rootsOfUnity n K :=
  Additive.toMul
    (zmodAddUnity hζ (hilbertZMod K L n χ b))

omit [IsMulCommutative Gal(L/K)] in
@[simp]
theorem hilbert_torsion_mul
    (n : ℕ) [NeZero n]
    (χ : FiniteCharacter Gal(L/K) n) (a b : Kˣ) :
    hilbertCupTorsion K L n χ (a * b) =
      hilbertCupTorsion K L n χ a +
        hilbertCupTorsion K L n χ b := by
  apply Subtype.ext
  simp only [hilbertCupTorsion]
  exact character_cup_mul K L a b
    (finiteCharacterRational Gal(L/K) n χ)

omit [IsMulCommutative Gal(L/K)] in
@[simp]
theorem hilbert_cup_torsion
    (n : ℕ) [NeZero n]
    (χ ψ : FiniteCharacter Gal(L/K) n) (b : Kˣ) :
    hilbertCupTorsion K L n (χ + ψ) b =
      hilbertCupTorsion K L n χ b +
        hilbertCupTorsion K L n ψ b := by
  apply Subtype.ext
  simp only [hilbertCupTorsion]
  change characterCupInvariant K L b
      (finiteCharacterRational Gal(L/K) n (χ + ψ)) =
    characterCupInvariant K L b
        (finiteCharacterRational Gal(L/K) n χ) +
      characterCupInvariant K L b
        (finiteCharacterRational Gal(L/K) n ψ)
  have hχ :
      finiteCharacterRational Gal(L/K) n (χ + ψ) =
        finiteCharacterRational Gal(L/K) n χ +
          finiteCharacterRational Gal(L/K) n ψ := by
    apply AddMonoidHom.ext
    intro g
    simp [finiteCharacterRational]
  rw [hχ, character_cup_add]

omit [IsMulCommutative Gal(L/K)] in
@[simp]
theorem hilbert_z_mod
    (n : ℕ) [NeZero n]
    (χ : FiniteCharacter Gal(L/K) n) (a b : Kˣ) :
    hilbertZMod K L n χ (a * b) =
      hilbertZMod K L n χ a +
        hilbertZMod K L n χ b := by
  unfold hilbertZMod
  rw [hilbert_torsion_mul, map_add]

omit [IsMulCommutative Gal(L/K)] in
@[simp]
theorem hilbert_cup_z
    (n : ℕ) [NeZero n]
    (χ ψ : FiniteCharacter Gal(L/K) n) (b : Kˣ) :
    hilbertZMod K L n (χ + ψ) b =
      hilbertZMod K L n χ b +
        hilbertZMod K L n ψ b := by
  unfold hilbertZMod
  rw [hilbert_cup_torsion, map_add]

omit [IsMulCommutative Gal(L/K)] in
@[simp]
theorem hilbert_cup_root
    (n : ℕ) [NeZero n] {ζ : K} (hζ : IsPrimitiveRoot ζ n)
    (χ : FiniteCharacter Gal(L/K) n) (a b : Kˣ) :
    hilbertCupRoot K L n hζ χ (a * b) =
      hilbertCupRoot K L n hζ χ a *
        hilbertCupRoot K L n hζ χ b := by
  change Additive.toMul
      (zmodAddUnity hζ
        (hilbertZMod K L n χ (a * b))) =
    Additive.toMul
      (zmodAddUnity hζ
        (hilbertZMod K L n χ a) +
       zmodAddUnity hζ
        (hilbertZMod K L n χ b))
  apply Additive.toMul.injective
  rw [hilbert_z_mod, map_add]

omit [IsMulCommutative Gal(L/K)] in
@[simp]
theorem hilbert_cup_add
    (n : ℕ) [NeZero n] {ζ : K} (hζ : IsPrimitiveRoot ζ n)
    (χ ψ : FiniteCharacter Gal(L/K) n) (b : Kˣ) :
    hilbertCupRoot K L n hζ (χ + ψ) b =
      hilbertCupRoot K L n hζ χ b *
        hilbertCupRoot K L n hζ ψ b := by
  change Additive.toMul
      (zmodAddUnity hζ
        (hilbertZMod K L n (χ + ψ) b)) =
    Additive.toMul
      (zmodAddUnity hζ
        (hilbertZMod K L n χ b) +
       zmodAddUnity hζ
        (hilbertZMod K L n ψ b))
  apply Additive.toMul.injective
  rw [hilbert_cup_z, map_add]

omit [IsMulCommutative Gal(L/K)] in
@[simp]
theorem hilbert_cup_right
    (n : ℕ) [NeZero n] {ζ : K} (hζ : IsPrimitiveRoot ζ n)
    (χ : FiniteCharacter Gal(L/K) n) (b : Kˣ) :
    hilbertCupRoot K L n hζ χ (b ^ n) = 1 := by
  have ht : hilbertCupTorsion K L n χ (b ^ n) = 0 := by
    apply Subtype.ext
    simp only [hilbertCupTorsion]
    exact character_cup_invariant K L n b χ
  have hz : hilbertZMod K L n χ (b ^ n) = 0 := by
    unfold hilbertZMod
    rw [ht, map_zero]
  unfold hilbertCupRoot
  rw [hz, map_zero]
  rfl

omit [IsMulCommutative Gal(L/K)] in
/-- Vanishing of the concrete root-valued pairing is exactly vanishing of
the finite local cup invariant from Proposition III.3.6. -/
theorem hilbert_cup_character
    (n : ℕ) [NeZero n] {ζ : K} (hζ : IsPrimitiveRoot ζ n)
    (χ : FiniteCharacter Gal(L/K) n) (b : Kˣ) :
    hilbertCupRoot K L n hζ χ b = 1 ↔
      characterCupInvariant K L b
        (finiteCharacterRational Gal(L/K) n χ) = 0 := by
  constructor
  · intro h
    have hr := congrArg Additive.ofMul h
    change zmodAddUnity hζ
        (hilbertZMod K L n χ b) = 0 at hr
    have hz : hilbertZMod K L n χ b = 0 := by
      apply (zmodAddUnity hζ).injective
      simpa using hr
    have ht : hilbertCupTorsion K L n χ b = 0 := by
      apply (torsionZMod n).symm.injective
      simpa [hilbertZMod] using hz
    simpa only [hilbertCupTorsion] using congrArg Subtype.val ht
  · intro h
    have ht : hilbertCupTorsion K L n χ b = 0 := by
      apply Subtype.ext
      simp only [hilbertCupTorsion]
      exact h
    unfold hilbertCupRoot hilbertZMod
    rw [ht, map_zero, map_zero]
    rfl

/-- Once the character formula of Proposition III.3.6 is supplied, the
concrete finite cup pairing has trivial left kernel.  The Kummer boundary
argument converting this character statement into nondegeneracy on power
classes is proved in `Theorem44Nondegeneracy`. -/
theorem hilbert_cup_formula
    (n : ℕ) [NeZero n] {ζ : K} (hζ : IsPrimitiveRoot ζ n)
    (hformula : ∀ (b : Kˣ) (χ : FiniteCharacter Gal(L/K) n),
      CharacterFormula K L b
        (finiteCharacterRational Gal(L/K) n χ))
    (χ : FiniteCharacter Gal(L/K) n)
    (hχ : ∀ b : Kˣ, hilbertCupRoot K L n hζ χ b = 1) :
    χ = 0 := by
  apply cup_pairing_formula K L n hformula χ
  intro b
  exact
    (hilbert_cup_character
      K L n hζ χ b).mp (hχ b)

/-- The exact source properties (a)--(c) for a candidate Hilbert symbol on
the power-class group.  No auxiliary proof assumptions occur in this
statement. -/
def HilbertSymbolABC
    (n : ℕ) (symbol : PowerClassGroup K n →
      PowerClassGroup K n → rootsOfUnity n K) : Prop :=
  (∀ a a' b, symbol (a * a') b = symbol a b * symbol a' b) ∧
  (∀ a b b', symbol a (b * b') = symbol a b * symbol a b') ∧
  (∀ a b, symbol b a = (symbol a b)⁻¹) ∧
  (∀ a, (∀ b, symbol a b = 1) → a = 1) ∧
  (∀ b, (∀ a, symbol a b = 1) → b = 1)

omit [IsUltrametricDist K] [IsNonarchimedeanLocalField K] in
/-- Theorem III.4.4(c), right-kernel half, is a formal consequence of its
left-kernel half and skew symmetry. -/
theorem hilbert_symbol_skew
    (n : ℕ) (symbol : PowerClassGroup K n →
      PowerClassGroup K n → rootsOfUnity n K)
    (hleft : ∀ a, (∀ b, symbol a b = 1) → a = 1)
    (hskew : ∀ a b, symbol b a = (symbol a b)⁻¹) :
    ∀ b, (∀ a, symbol a b = 1) → b = 1 :=
  nondegenerate_skew_symmetric
    symbol hleft hskew

/-- In characteristic zero, the concrete full Kummer--Artin symbol satisfies
all of Theorem III.4.4(a)--(c), without auxiliary assumptions. -/
theorem hilbert_symbol_abc
    [CharZero K]
    (n : ℕ) (hn : 0 < n) {ζ : K} (hζ : IsPrimitiveRoot ζ n) :
    HilbertSymbolABC K n (localKummerSymbol K n hn hζ) :=
  ⟨hilbert_symbol_left K n hn hζ,
    hilbert_symbol_right K n hn hζ,
    kummer_hilbert_skew K n hn hζ,
    hilbert_symbol_kernel K n hn hζ,
    local_hilbert_symbol K n hn hζ⟩

/-- The norm criterion in Theorem III.4.4(d), uniformly in the chosen
primitive root and in the splitting-field model. -/
def HilbertSymbolCriterion
  (n : ℕ) [NeZero n]
    (symbol : ∀ {ζ : K}, IsPrimitiveRoot ζ n →
      Kˣ → Kˣ → rootsOfUnity n K) : Prop :=
  ∀ (E : Type) (_ : Field E) (_ : Algebra K E)
    (a b : Kˣ) (ζ : K),
    Polynomial.IsSplittingField K E
      (Polynomial.X ^ n - Polynomial.C (a : K)) →
    Irreducible (Polynomial.X ^ n - Polynomial.C (a : K)) →
    (hζ : IsPrimitiveRoot ζ n) →
    symbol hζ a b = 1 ↔ b ∈ normSubgroup K E

/-- The concrete full Kummer--Artin symbol satisfies Theorem III.4.4(d). -/
theorem hilbert_symbol_criterion
    [CharZero K]
    (n : ℕ) [NeZero n] :
    HilbertSymbolCriterion K n
      (fun hζ a b ↦ localKummerSymbol K n (NeZero.pos n) hζ
        (powerClass n a) (powerClass n b)) := by
  intro E _ _ a b ζ hsplit hirr hζ
  exact hilbert_symbol_subgroup
    K n (NeZero.pos n) hζ E a b hsplit hirr

/-- **Milne III.4.4, complete formal statement.**  The same concrete symbol
has properties (a)--(c), and its representative-level form satisfies the
Kummer norm criterion (d). -/
theorem complete
    [CharZero K]
    (n : ℕ) [NeZero n] {ζ : K} (hζ : IsPrimitiveRoot ζ n) :
    HilbertSymbolABC K n
        (localKummerSymbol K n (NeZero.pos n) hζ) ∧
      HilbertSymbolCriterion K n
        (fun hξ a b ↦ localKummerSymbol K n (NeZero.pos n) hξ
          (powerClass n a) (powerClass n b)) :=
  ⟨hilbert_symbol_abc K n (NeZero.pos n) hζ,
    hilbert_symbol_criterion K n⟩

end

end Submission.CField.HSymbol
