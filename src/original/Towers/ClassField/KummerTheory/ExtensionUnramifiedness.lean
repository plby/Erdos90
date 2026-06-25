import Towers.ClassField.KummerTheory.PolynomialRamification
import Towers.ClassField.KummerTheory.KummerUnramified
import Towers.NumberTheory.Ramification.RamificationDiscriminant

/-!
# Chapter VII, Appendix A, Proposition A.5

A number field obtained by adjoining finitely many `n`th roots is unramified
at a finite prime whenever `n` times every radicand is a local unit there.
The radical presentation and the upper primes are represented literally.
-/

namespace Towers.CField.KTheory

open IsDedekindDomain NumberField

noncomputable section

universe u

private abbrev OK (K : Type u) [Field K] [NumberField K] :=
  NumberField.RingOfIntegers K

/-- A finite radical presentation `L = K[a_i^(1/n)]`. -/
structure RFData
    (K : Type u) [Field K] [NumberField K]
    (n m : ℕ) where
  L : Type u
  fieldL : Field L
  numberFieldL : NumberField L
  algebraKL : Algebra K L
  finiteDimensionalKL : FiniteDimensional K L
  radicand : Fin m → Kˣ
  root : Fin m → L
  root_pow : ∀ i, root i ^ n = algebraMap K L ((radicand i : Kˣ) : K)
  adjoin_roots_top : IntermediateField.adjoin K (Set.range root) = ⊤

/-- The extension is unramified above the finite prime `P`. -/
def RFData.IsUnramifiedAt
    {K : Type u} [Field K] [NumberField K]
    {n m : ℕ} (data : RFData K n m)
    (P : HeightOneSpectrum (OK K)) : Prop :=
  letI : Field data.L := data.fieldL
  letI : NumberField data.L := data.numberFieldL
  letI : Algebra K data.L := data.algebraKL
  ∀ Q : HeightOneSpectrum (OK data.L),
    Q.under (OK K) = P → Algebra.IsUnramifiedAt (OK K) Q.asIdeal

/-- The source's hypothesis that `n a_i` is a unit in `K_P`, expressed by
the normalized multiplicative valuation. -/
def RFData.RadicandsAreUnits
    {K : Type u} [Field K] [NumberField K]
    {n m : ℕ} (data : RFData K n m)
    (P : HeightOneSpectrum (OK K)) : Prop :=
  ∀ i, P.valuation K ((n : K) * ((data.radicand i : Kˣ) : K)) = 1

/-- A single radical `K[a^(1/n)]` is unramified at `P`.  This predicate is
quantified over literal one-generator presentations, so it does not hide a
choice of splitting field. -/
def SingleRadicalUnramified
    (K : Type u) [Field K] [NumberField K]
    (n : ℕ) (a : Kˣ) (P : HeightOneSpectrum (OK K)) : Prop :=
  ∀ data : RFData K n 1,
    data.radicand 0 = a → data.IsUnramifiedAt P

/-- The discriminant step in the printed proof: the derivative calculation
for `X^n-a`, together with the order-discriminant comparison, proves the
single-radical criterion. -/
def DiscriminantBridge : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K]
    (n : ℕ) (a : Kˣ) (P : HeightOneSpectrum (OK K)),
    P.valuation K ((n : K) * ((a : Kˣ) : K)) = 1 →
      SingleRadicalUnramified K n a P

/-- Unramifiedness at a fixed base prime is preserved when finitely many
single radical extensions are composed. -/
def FiniteCompositumBridge : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K]
    (n m : ℕ) (P : HeightOneSpectrum (OK K))
    (data : RFData K n m),
    (∀ i, SingleRadicalUnramified K n (data.radicand i) P) →
      data.IsUnramifiedAt P

/-- Proposition A.5 from the one-radical discriminant calculation and
stability under finite composita. -/
theorem radical_unramifiedness_bridges
    (hdisc : DiscriminantBridge.{u})
    (hcompositum : FiniteCompositumBridge.{u}) :
    ∀ (K : Type u) [Field K] [NumberField K]
    (n m : ℕ) (P : HeightOneSpectrum (OK K))
    (data : RFData K n m),
    data.RadicandsAreUnits P → data.IsUnramifiedAt P
  := by
  intro K _ _ n m P data hunits
  apply hcompositum K n m P data
  intro i
  exact hdisc K n (data.radicand i) P (hunits i)

/-- The valid Kummer-unramifiedness conclusion obtained from the printed
hypothesis once the exponent is also a local unit.  The primitive-root
assumption is the standing hypothesis of Appendix A, and it supplies the
Galois property of the multiradical extension rather than being stored as an
extra field of `RFData`.

The additional equation for `n` is genuinely necessary for the statement as
currently printed: the condition that `n * a_i` alone have valuation one
allows the valuation of `a_i` to cancel a positive valuation of `n`. -/
theorem unramified_exponent_unit
    (K : Type u) [Field K] [NumberField K]
    (n m : ℕ) (hn : 0 < n) (hroots : (primitiveRoots n K).Nonempty)
    (P : HeightOneSpectrum (OK K))
    (data : RFData K n m)
    (hnUnit : P.valuation K (n : K) = 1)
    (hproducts : data.RadicandsAreUnits P) :
    data.IsUnramifiedAt P := by
  letI : Field data.L := data.fieldL
  letI : NumberField data.L := data.numberFieldL
  letI : Algebra K data.L := data.algebraKL
  letI : FiniteDimensional K data.L := data.finiteDimensionalKL
  have hradicandUnit : ∀ i, P.valuation K (data.radicand i : K) = 1 := by
    intro i
    have hi := hproducts i
    rw [map_mul, hnUnit, one_mul] at hi
    exact hi
  let zeta : K := hroots.choose
  have hzeta : IsPrimitiveRoot zeta n :=
    (mem_primitiveRoots hn).mp hroots.choose_spec
  have hpowers : ∀ x ∈ Set.range data.root,
      x ^ n ∈ Set.range (algebraMap K data.L) := by
    rintro x ⟨i, rfl⟩
    exact ⟨((data.radicand i : Kˣ) : K), (data.root_pow i).symm⟩
  letI : IsGalois K data.L :=
    adjoin_nth_roots hn hzeta (Set.range data.root)
      data.adjoin_roots_top hpowers
  intro Q hQ
  exact nth_roots_units n hn.ne' K data.L
    (fun i ↦ data.radicand i) data.root data.root_pow
    data.adjoin_roots_top P Q hQ hnUnit hradicandUnit

/-- A faithful repair of Proposition A.5: retain the printed condition on
`n * a_i`, add the appendix's standing primitive-root assumption explicitly,
and require that the finite prime not divide `n`. -/
def CorrectedRadicalUnramifiedness : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K]
    (n m : ℕ), 0 < n → (primitiveRoots n K).Nonempty →
    ∀ (P : HeightOneSpectrum (OK K))
      (data : RFData K n m),
      P.valuation K (n : K) = 1 →
      data.RadicandsAreUnits P → data.IsUnramifiedAt P

/-- The corrected source statement follows from the multiradical inertia
calculation, with no discriminant or compositum bridge left as an assumption. -/
theorem correctedRadicalUnramifiedness :
    CorrectedRadicalUnramifiedness.{u} := by
  intro K _ _ n m hn hroots P data hnUnit hproducts
  exact unramified_exponent_unit
    K n m hn hroots P data hnUnit hproducts

end

end Towers.CField.KTheory
