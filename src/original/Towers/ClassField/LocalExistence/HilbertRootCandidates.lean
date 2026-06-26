import Towers.ClassField.HilbertSymbols.PairingTheoreticCore
import Towers.ClassField.LocalExistence.FiniteReciprocity

/-!
# Hilbert-pairing input for the divisible norm core

This file isolates the arithmetic content of Milne's Steps III.5.2--3.
If an element of the base norm core has a norm preimage upstairs which is a
norm for every Kummer parameter, Proposition III.4.1 makes that preimage an
`n`th power.  Taking its norm then produces an element of `E(L)`.
-/

namespace Towers.CField.LExist

open Towers.CField.LFTheory
open Towers.CField.HSymbol

noncomputable section

universe u v

variable (K : Type u) [NontriviallyNormedField K]
  [IsUltrametricDist K] [ValuativeRel K] [IsNonarchimedeanLocalField K]
  [Valuation.Compatible (NormedField.valuation (K := K))]

/-- A precise norm-root input for one extension: `a` is the norm of an
upstairs element which is an `n`th power. -/
def NthNormPreimage (n : ℕ) (a : Kˣ)
    (L : FASubext K) : Prop :=
  ∃ y : L.1ˣ,
    normOnUnits K L.1 y = a ∧ IsNthPower n y

omit [IsUltrametricDist K] [ValuativeRel K]
  [IsNonarchimedeanLocalField K]
  [Valuation.Compatible (NormedField.valuation (K := K))] in
/-- An `n`th-power norm preimage gives a member of Milne's candidate set
`E(L)`.  The proof is the norm-of-a-power calculation in Step III.5.3. -/
theorem candidates_nth_preimage
    (n : ℕ) (a : Kˣ) (L : FASubext K)
    (h : NthNormPreimage K n a L) :
    (localRootCandidates K n a L).Nonempty := by
  obtain ⟨y, hyNorm, c, hc⟩ := h
  refine ⟨normOnUnits K L.1 c, ?_, ?_⟩
  · calc
      normOnUnits K L.1 c ^ n = normOnUnits K L.1 (c ^ n) := by
        rw [map_pow]
      _ = normOnUnits K L.1 y := congrArg (normOnUnits K L.1) hc
      _ = a := hyNorm
  · change normOnUnits K L.1 c ∈ normSubgroup K L.1
    exact ⟨c, rfl⟩

omit [IsUltrametricDist K] [ValuativeRel K]
  [IsNonarchimedeanLocalField K]
  [Valuation.Compatible (NormedField.valuation (K := K))] in
/-- Proposition III.4.1 turns a universal norm preimage into the precise
norm-root input needed above.  This theorem is independent of any particular
construction of the Hilbert pairing. -/
theorem nth_preimage_hilbert
    {C : Type v} [One C]
    (n : ℕ) (a : Kˣ) (L : FASubext K)
    (pairing : L.1ˣ → L.1ˣ → C)
    (IsNormFrom : L.1ˣ → L.1ˣ → Prop)
    (norm_iff : ∀ x y, IsNormFrom x y ↔ pairing x y = 1)
    (right_nondegenerate : ∀ y,
      (∀ x, pairing x y = 1) → IsNthPower n y)
    (hlift : ∃ y : L.1ˣ,
      normOnUnits K L.1 y = a ∧ ∀ x, IsNormFrom x y) :
    NthNormPreimage K n a L := by
  obtain ⟨y, hyNorm, hyUniversal⟩ := hlift
  refine ⟨y, hyNorm, ?_⟩
  exact nth_forall_nondegenerate
    n pairing IsNormFrom norm_iff right_nondegenerate hyUniversal

omit [IsUltrametricDist K] [ValuativeRel K]
  [IsNonarchimedeanLocalField K]
  [Valuation.Compatible (NormedField.valuation (K := K))] in
/-- The Hilbert norm criterion and right nondegeneracy make `E(L)` nonempty
once Step III.5.2 supplies a universal-norm preimage upstairs. -/
theorem candidates_hilbert_lift
    {C : Type v} [One C]
    (n : ℕ) (a : Kˣ) (L : FASubext K)
    (pairing : L.1ˣ → L.1ˣ → C)
    (IsNormFrom : L.1ˣ → L.1ˣ → Prop)
    (norm_iff : ∀ x y, IsNormFrom x y ↔ pairing x y = 1)
    (right_nondegenerate : ∀ y,
      (∀ x, pairing x y = 1) → IsNthPower n y)
    (hlift : ∃ y : L.1ˣ,
      normOnUnits K L.1 y = a ∧ ∀ x, IsNormFrom x y) :
    (localRootCandidates K n a L).Nonempty := by
  apply candidates_nth_preimage K n a L
  exact nth_preimage_hilbert K n a L
    pairing IsNormFrom norm_iff right_nondegenerate hlift

/-- A uniform family of Hilbert pairings and the Step III.5.2 lifting
property imply divisibility of the common finite-abelian norm subgroup.

The hypotheses separate the two missing arithmetic inputs precisely:
`norm_iff` and `right_nondegenerate` are Proposition III.4.1, while `hlift`
is the norm-core surjectivity asserted in Step III.5.2. -/
theorem core_divisible_lifts
    {C : Type v} [One C]
    (hNorm : LocalNormCorrespondence K)
    (pairing : (n : ℕ) → (L : FASubext K) →
      L.1ˣ → L.1ˣ → C)
    (IsNormFrom : (n : ℕ) → (L : FASubext K) →
      L.1ˣ → L.1ˣ → Prop)
    (norm_iff : ∀ (n : ℕ) (L : FASubext K) x y,
      IsNormFrom n L x y ↔ pairing n L x y = 1)
    (right_nondegenerate :
      ∀ (n : ℕ) (L : FASubext K) y,
        (∀ x, pairing n L x y = 1) → IsNthPower n y)
    (hlift : ∀ (n : ℕ), n ≠ 0 → ∀ a ∈ localNormCore K,
      ∀ L : FASubext K,
        ∃ y : L.1ˣ, normOnUnits K L.1 y = a ∧
          ∀ x, IsNormFrom n L x y) :
    IDSubgro (localNormCore K) := by
  apply divisible_candidates_nonempty K hNorm
  intro n hn a ha L
  exact candidates_hilbert_lift K n a L
    (pairing n L) (IsNormFrom n L) (norm_iff n L)
    (right_nondegenerate n L) (hlift n hn a ha L)

/-- Local existence from finite reciprocity together with the two concrete
Hilbert/compactness inputs in Milne's proof of norm-core divisibility. -/
theorem existence_reciprocity_lifts
    {C : Type v} [One C]
    (phi : Kˣ →* AbsoluteAbelianGalois K)
    (hphi : ∀ L : FASubext K,
      InducesLocalReciprocity K phi L)
    (pairing : (n : ℕ) → (L : FASubext K) →
      L.1ˣ → L.1ˣ → C)
    (IsNormFrom : (n : ℕ) → (L : FASubext K) →
      L.1ˣ → L.1ˣ → Prop)
    (norm_iff : ∀ (n : ℕ) (L : FASubext K) x y,
      IsNormFrom n L x y ↔ pairing n L x y = 1)
    (right_nondegenerate :
      ∀ (n : ℕ) (L : FASubext K) y,
        (∀ x, pairing n L x y = 1) → IsNthPower n y)
    (hlift : ∀ (n : ℕ), n ≠ 0 → ∀ a ∈ localNormCore K,
      ∀ L : FASubext K,
        ∃ y : L.1ˣ, normOnUnits K L.1 y = a ∧
          ∀ x, IsNormFrom n L x y) :
    LocalExistenceTheorem K := by
  apply reciprocity_divisible_core K phi hphi
  exact core_divisible_lifts K
    (local_correspondence_reciprocity phi hphi)
    pairing IsNormFrom norm_iff right_nondegenerate hlift

end

end Towers.CField.LExist
