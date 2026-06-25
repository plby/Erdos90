import Submission.ClassField.LocalReciprocity.ResidueMulEquiv
import Submission.ClassField.HilbertSymbols.PairingTheoreticCore
import Submission.ClassField.HilbertSymbols.KummerPowerInflation
import Submission.ClassField.HilbertSymbols.NondegeneracyCore
import Submission.ClassField.HilbertSymbols.Nondegeneracy

/-!
# Milne, Class Field Theory, Proposition III.4.1: source statement

This file gives the literal extension-theoretic formulation of the norm
hypothesis in Proposition III.4.1 and assembles the result from the Kummer
norm criterion and the nondegeneracy of the local Kummer--Hilbert symbol.
-/

namespace Submission.CField.HSymbol

open Polynomial
open Submission.CField.LFTheory
open Submission.CField.LRecip
open Submission.CField.LBrauer
open Submission.CField.KTheory

noncomputable section

universe u

/-- A finite cyclic extension, bundled so that Proposition III.4.1 can
quantify literally over all such extensions without auxiliary typeclass
hypotheses in its norm condition. -/
structure FCExt (K : Type u) [Field K] where
  carrier : Type u
  [field : Field carrier]
  [algebra : Algebra K carrier]
  [finiteDimensional : FiniteDimensional K carrier]
  [isGalois : IsGalois K carrier]
  [isCyclic : IsCyclic Gal(carrier/K)]

attribute [instance]
  FCExt.field
  FCExt.algebra
  FCExt.finiteDimensional
  FCExt.isGalois
  FCExt.isCyclic

namespace FCExt

variable {K : Type u} [Field K]

/-- The degree of a bundled finite cyclic extension. -/
def degree (L : FCExt K) : ℕ :=
  Module.finrank K L.carrier

/-- Its norm subgroup in the base field. -/
def normGroup (L : FCExt K) : Subgroup Kˣ :=
  normSubgroup K L.carrier

end FCExt

/-- The literal norm hypothesis of Proposition III.4.1: `b` is a norm from
every finite cyclic extension whose degree divides `n`. -/
def EveryCyclicDvd
    (K : Type u) [Field K] (n : ℕ) (b : Kˣ) : Prop :=
  ∀ L : FCExt K,
    L.degree ∣ n → b ∈ L.normGroup

/-- The literal conclusion asserted by Proposition III.4.1.  The primitive
root hypothesis is kept as an actual element of the base field. -/
def AlgebraicStatement
    (K : Type u) [Field K] (n : ℕ) (ζ : K) (b : Kˣ) : Prop :=
  IsPrimitiveRoot ζ n →
    EveryCyclicDvd K n b →
      IsNthPower n b

section ElementaryNormDirection

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

/-- The easy converse direction: an `n`th power is a norm from every finite
extension whose degree divides `n`. -/
theorem nth_finrank_dvd
    (n : ℕ) (b : Kˣ) (hb : IsNthPower n b)
    (hdegree : Module.finrank K L ∣ n) :
    b ∈ normSubgroup K L := by
  obtain ⟨x, rfl⟩ := hb
  obtain ⟨m, hm⟩ := hdegree
  refine ⟨Units.map (algebraMap K L) (x ^ m), ?_⟩
  apply Units.ext
  change Algebra.norm K (algebraMap K L (((x ^ m : Kˣ) : K))) =
    ((x ^ n : Kˣ) : K)
  rw [Algebra.norm_algebraMap]
  simp only [Units.val_pow_eq_pow_val]
  rw [← pow_mul, hm, mul_comm]

/-- Consequently, every `n`th power satisfies Milne's universal cyclic norm
hypothesis. -/
theorem every_dvd_nth
    {K : Type u} [Field K] (n : ℕ) (b : Kˣ)
    (hb : IsNthPower n b) :
    EveryCyclicDvd K n b := by
  intro L hdegree
  exact nth_finrank_dvd
    n b hb hdegree

end ElementaryNormDirection

section KummerReduction

variable {K L : Type u} [Field K] [Field L] [Algebra K L]
variable {n : ℕ} [NeZero n] {a ζ : K} {b : Kˣ}
variable [IsSplittingField K L (X ^ n - C a)]

/-- Milne's universal norm hypothesis applies, in particular, to every
irreducible degree-`n` Kummer splitting field supplied by Step 2. -/
theorem kummer_splitting_field
    (hζ : IsPrimitiveRoot ζ n)
    (hirr : Irreducible (X ^ n - C a))
    (hNorm : EveryCyclicDvd
      K n b) :
    b ∈ normSubgroup K L := by
  letI : FiniteDimensional K L :=
    IsSplittingField.finiteDimensional L (X ^ n - C a)
  have hs := kummer_splitting_structure (L := L) hirr hζ
  letI : IsGalois K L := hs.1
  letI : IsCyclic Gal(L/K) := hs.2.1
  let E : FCExt K :=
    @FCExt.mk K _ L _ _ _ hs.1 hs.2.1
  apply hNorm E
  change Module.finrank K L ∣ n
  rw [hs.2.2]

end KummerReduction

section LocalArtinReduction

variable (K : Type)
  [NontriviallyNormedField K] [IsUltrametricDist K]

local instance finiteCyclicExtensionValuativeRel : ValuativeRel K :=
  ValuativeRel.ofValuation (NormedField.valuation (K := K))

local instance finiteCyclicExtensionValuationCompatible :
    Valuation.Compatible (NormedField.valuation (K := K)) :=
  Valuation.Compatible.ofValuation (NormedField.valuation (K := K))

variable [IsNonarchimedeanLocalField K]

/-- **Proposition III.4.1 (literal source statement).**  For a local field
containing a primitive `n`th root of unity, an element which is a norm from
every cyclic extension of degree dividing `n` is an `n`th power. -/
def ExtensionsImpliesNth (n : ℕ) (ζ : K) (b : Kˣ) : Prop :=
  IsPrimitiveRoot ζ n →
    EveryCyclicDvd K n b →
      IsNthPower n b

/-- The unconditional finite local Artin equivalence has exactly the norm
subgroup as its kernel. -/
theorem local_artin_subgroup
    (L : FCExt K) (b : Kˣ) :
    localArtinHom K L.carrier b = 1 ↔
      b ∈ normSubgroup K L.carrier := by
  rw [local_artin_hom]
  constructor
  · intro h
    have he := congrArg (localNormResidue K L.carrier) h
    have hmk : QuotientGroup.mk' (normSubgroup K L.carrier) b = 1 := by
      simpa using he
    exact (QuotientGroup.eq_one_iff b).mp hmk
  · intro hb
    have hmk : QuotientGroup.mk' (normSubgroup K L.carrier) b = 1 :=
      (QuotientGroup.eq_one_iff b).mpr hb
    rw [hmk, map_one]

/-- Under the universal norm hypothesis, the unconditional finite local
Artin map of Theorem III.3.1 kills `b` at every cyclic level of degree
dividing `n`. -/
theorem artin_every_extension
    (n : ℕ) (b : Kˣ)
    (hNorm : EveryCyclicDvd
      K n b)
    (L : FCExt K)
    (hdegree : L.degree ∣ n) :
    localArtinHom K L.carrier b = 1 := by
  have hb : b ∈ normSubgroup K L.carrier := hNorm L hdegree
  exact (local_artin_subgroup K L b).mpr hb

/-- Thus Milne's universal norm hypothesis is exactly simultaneous
vanishing under all cyclic finite-level Artin maps of degree dividing `n`.
The missing implication to `IsNthPower n b` is the concrete right
nondegeneracy of the Hilbert symbol. -/
theorem every_cyclic_artin
    (n : ℕ) (b : Kˣ) :
    EveryCyclicDvd K n b ↔
      ∀ (L : FCExt K), L.degree ∣ n →
        localArtinHom K L.carrier b = 1 := by
  constructor
  · intro hNorm L hdegree
    exact artin_every_extension
      K n b hNorm L hdegree
  · intro hArtin L hdegree
    exact (local_artin_subgroup K L b).mp
      (hArtin L hdegree)

/-- Exact unconditional reduction of the source statement to its missing
Hilbert-nondegeneracy content: simultaneous vanishing at all cyclic Artin
levels of degree dividing `n` must force an `n`th power. -/
theorem cyclic_extension_artin
    (n : ℕ) (ζ : K) (b : Kˣ) :
    ExtensionsImpliesNth K n ζ b ↔
      (IsPrimitiveRoot ζ n →
        (∀ (L : FCExt K), L.degree ∣ n →
          localArtinHom K L.carrier b = 1) →
        IsNthPower n b) := by
  unfold ExtensionsImpliesNth
  rw [every_cyclic_artin K n b]

section NormPowerCriterionAssembly

variable [CharZero K]

omit [IsUltrametricDist K] [IsNonarchimedeanLocalField K] [CharZero K] in
/-- The degree of the canonical Kummer extension generated by one power
class divides the Kummer exponent. -/
theorem cyclic_kummer_dvd
    (n : ℕ) (hn : 0 < n) {ζ : K} (hζ : IsPrimitiveRoot ζ n)
    (a : PowerClassGroup K n) :
    Module.finrank K (cyclicKummerExtension K n hn hζ a).carrier ∣ n := by
  let B := cyclicClassSubgroup K n hn a
  calc
    Module.finrank K (cyclicKummerExtension K n hn hζ a).carrier = B.card :=
      finrank_kummer_field n hn
        ⟨ζ, (mem_primitiveRoots hn).2 hζ⟩ B
    _ = Nat.card B.carrier :=
      PCSubgro.card_eq_card K B
    _ = orderOf a := Nat.card_zpowers a
    _ ∣ n := orderOf_dvd_of_pow_eq_one (power_class_pow n a)

omit [IsUltrametricDist K] [IsNonarchimedeanLocalField K] [CharZero K] in
/-- The canonical Kummer extension generated by a single power class is
cyclic.  Its radical generator and the preceding degree divisibility supply
the required primitive root at the actual extension degree. -/
theorem cyclic_kummer_extension
    (n : ℕ) (hn : 0 < n) {ζ : K} (hζ : IsPrimitiveRoot ζ n)
    (a : PowerClassGroup K n) :
    IsCyclic Gal((cyclicKummerExtension K n hn hζ a).carrier/K) := by
  let F := (cyclicKummerExtension K n hn hζ a).carrier
  let d := Module.finrank K F
  have hdpos : 0 < d := Module.finrank_pos
  have hdvd : d ∣ n := cyclic_kummer_dvd K n hn hζ a
  have hroots : (primitiveRoots d K).Nonempty := by
    refine ⟨ζ ^ (n / d), (mem_primitiveRoots hdpos).2 ?_⟩
    exact IsPrimitiveRoot.pow hn hζ (Nat.div_mul_cancel hdvd).symm
  obtain ⟨c, hc⟩ := IntermediateField.mem_bot.mp
    (cyclic_kummer_bot K n hn hζ a)
  exact (radical_generator_cyclic K F hroots hc.symm
    (kummer_adjoin_top K n hn hζ a)).2

/-- **Proposition III.4.1 (literal universal-norm assembly).**  For positive
`n` in characteristic zero, the universal cyclic norm condition makes every
Kummer--Hilbert multiplier vanish.  Right nondegeneracy then says that the
class of `b` modulo `n`th powers is trivial. -/
theorem cyclic_extension_pos
    (n : ℕ) (hn : 0 < n) (ζ : K) (b : Kˣ) :
    ExtensionsImpliesNth K n ζ b := by
  intro hζ hNorm
  apply (power_class_nth n b).mp
  apply local_hilbert_symbol K n hn hζ
  intro a
  rw [hilbert_symbol_artin K n hn hζ]
  apply (kummer_artin_symbol
    K n hn hζ a b).2
  let E := cyclicKummerExtension K n hn hζ a
  have hcyclic : IsCyclic Gal(E.carrier/K) :=
    cyclic_kummer_extension K n hn hζ a
  let L : FCExt K :=
    @FCExt.mk K _ E.carrier inferInstance inferInstance
      inferInstance inferInstance hcyclic
  have hdegree : L.degree ∣ n := by
    change Module.finrank K E.carrier ∣ n
    exact cyclic_kummer_dvd K n hn hζ a
  exact hNorm L hdegree

end NormPowerCriterionAssembly

end LocalArtinReduction

end


end Submission.CField.HSymbol
