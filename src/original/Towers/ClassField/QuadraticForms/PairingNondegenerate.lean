import Towers.ClassField.QuadraticForms.HilbertInvariants
import Towers.ClassField.QuadraticForms.DiagonalInvariance
import Towers.ClassField.HilbertSymbols.QuadraticSquareClasses

/-!
# Chapter VIII, Section 6, Proposition 6.11

This file proves the classification of the possible triples of local
quadratic invariants in the diagonal square-class model.  The only local
field input is the standard nondegeneracy of the quadratic Hilbert pairing:
for a nontrivial square class `b`, the character `(·, b)` is onto.  All rank
constructions and both exceptional constraints are proved from that input.
-/

namespace Towers.CField.QForms

variable {G μ : Type*} [CommGroup G] [CommGroup μ]

namespace AHSym

variable (h : AHSym G μ)

/-- Nondegeneracy of the local quadratic Hilbert pairing, in the exact form
used in the rank-two construction of Proposition 6.11. -/
def PairingNondegenerate : Prop :=
  ∀ b : G, b ≠ 1 → Function.Surjective (fun a : G ↦ h.symbol a b)

/-- A triple `(n,d,s)` is realized by a nondegenerate diagonal form.  Elements
of `G` are square classes, so every coefficient is automa nonzero. -/
def InvariantTripleRealizable (n : ℕ) (d : G) (s : μ) : Prop :=
  ∃ coeffs : List G,
    coeffs.length = n ∧ discriminant coeffs = d ∧ h.hasse coeffs = s

/-- The two and only two exceptional constraints in Proposition 6.11. -/
def Constraints (n : ℕ) (d : G) (s : μ) : Prop :=
  (n = 1 → s = h.symbol h.negOne d) ∧
  (n = 2 → d = h.negOne → s = h.symbol h.negOne h.negOne)

private theorem hasse_self_formula
    (a d : G) :
    h.hasse [a, a * d] =
      h.symbol a (h.negOne * d) * h.symbol d d := by
  simp only [hasse, List.map, List.prod_cons, List.prod_nil, mul_one]
  rw [h.map_mul_right a a d, h.self_neg_one a,
    h.self_neg_one (a * d), h.map_mul_right h.negOne a d,
    h.map_mul_right a h.negOne d, h.self_neg_one d,
    h.symmetric a h.negOne]
  calc
    h.symbol h.negOne a *
          (h.symbol h.negOne a * h.symbol a d) *
          (h.symbol h.negOne a * h.symbol h.negOne d) =
        (h.symbol h.negOne a * h.symbol h.negOne a) *
          (h.symbol h.negOne a * h.symbol a d * h.symbol h.negOne d) := by
            ac_rfl
    _ = h.symbol h.negOne a * h.symbol a d * h.symbol h.negOne d := by
      rw [← pow_two, h.value_sq, one_mul]

private theorem neg_mul_ne
    {d : G} (hd : d ≠ h.negOne) : h.negOne * d ≠ 1 := by
  intro hprod
  apply hd
  calc
    d = 1 * d := (one_mul d).symm
    _ = h.negOne ^ 2 * d := by rw [h.negOne_sq]
    _ = h.negOne * (h.negOne * d) := by simp [pow_two, mul_assoc]
    _ = h.negOne := by rw [hprod, mul_one]

private theorem binary_realizable
    [Nontrivial μ]
    (hsq : ∀ a : G, a ^ 2 = 1)
    (hnondeg : h.PairingNondegenerate)
    (d : G) (s : μ)
    (hexceptional : d = h.negOne → s = h.symbol h.negOne h.negOne) :
    h.InvariantTripleRealizable 2 d s := by
  by_cases hd : d = h.negOne
  · subst d
    refine ⟨[1, h.negOne], by simp, by simp [discriminant], ?_⟩
    rw [hexceptional rfl]
    exact h.hasse_pair_discriminant
      (a := (1 : G)) (b := h.negOne) (by simp)
  · have hb : h.negOne * d ≠ 1 := h.neg_mul_ne hd
    obtain ⟨a, ha⟩ := hnondeg (h.negOne * d) hb
      (s * (h.symbol d d)⁻¹)
    refine ⟨[a, a * d], by simp, discriminant_pair_self a d (hsq a), ?_⟩
    rw [hasse_self_formula, show h.symbol a (h.negOne * d) =
      s * (h.symbol d d)⁻¹ from ha]
    simp

private theorem eq_neg_iff
    (hsq : ∀ a : G, a ^ 2 = 1) (a d : G) :
    d * a = h.negOne ↔ a = h.negOne * d := by
  constructor
  · intro hda
    calc
      a = 1 * a := (one_mul a).symm
      _ = d ^ 2 * a := by rw [hsq d]
      _ = d * (d * a) := by simp [pow_two, mul_assoc]
      _ = d * h.negOne := by rw [hda]
      _ = h.negOne * d := mul_comm _ _
  · intro ha
    rw [ha]
    calc
      d * (h.negOne * d) = h.negOne * (d * d) := by ac_rfl
      _ = h.negOne * d ^ 2 := by rw [pow_two]
      _ = h.negOne := by rw [hsq d, mul_one]

private theorem ternary_realizable
    [Nontrivial G] [Nontrivial μ]
    (hsq : ∀ a : G, a ^ 2 = 1)
    (hnondeg : h.PairingNondegenerate)
    (d : G) (s : μ) :
    h.InvariantTripleRealizable 3 d s := by
  obtain ⟨a, ha⟩ : ∃ a : G, a ≠ h.negOne * d := exists_ne (h.negOne * d)
  let d₁ : G := d * a
  let correction : μ := h.symbol a a * h.symbol a d₁
  let s₁ : μ := s * correction⁻¹
  have hd₁ : d₁ ≠ h.negOne := by
    intro hd
    exact ha ((h.eq_neg_iff hsq a d).mp (by simpa [d₁, mul_comm] using hd))
  obtain ⟨coeffs, hlen, hdisc, hhasse⟩ :=
    h.binary_realizable hsq hnondeg d₁ s₁ (fun hd ↦ (hd₁ hd).elim)
  refine ⟨coeffs ++ [a], by simp [hlen], ?_, ?_⟩
  · rw [discriminant_append_singleton, hdisc]
    dsimp [d₁]
    calc
      d * a * a = d * (a ^ 2) := by simp [pow_two, mul_assoc]
      _ = d := by rw [hsq a, mul_one]
  · rw [h.hasse_append_singleton, hhasse, hdisc]
    dsimp [s₁, correction]
    group

private theorem realizable_succ
    {n : ℕ} {d : G} {s : μ}
    (hr : h.InvariantTripleRealizable n d s) :
    h.InvariantTripleRealizable (n + 1) d s := by
  obtain ⟨coeffs, hlen, hdisc, hhasse⟩ := hr
  refine ⟨1 :: coeffs, by simp [hlen], ?_, ?_⟩
  · simpa [discriminant] using hdisc
  · simpa [hasse] using hhasse

/-- Proposition 6.11 follows from exponent two for square classes and
nondegeneracy of the local Hilbert pairing. -/
theorem of_pairingNondegenerate
    [Nontrivial G] [Nontrivial μ]
    (hsq : ∀ a : G, a ^ 2 = 1)
    (hnondeg : h.PairingNondegenerate) :
    (∀ (n : ℕ) (d : G) (s : μ), 1 ≤ n →
          (h.InvariantTripleRealizable n d s ↔ h.Constraints n d s)) := by
  intro n d s hn
  constructor
  · rintro ⟨coeffs, hlen, hdisc, hhasse⟩
    constructor
    · intro hn1
      have hlen1 : coeffs.length = 1 := hlen.trans hn1
      obtain ⟨a, rfl⟩ : ∃ a, coeffs = [a] := by
        simpa [List.length_eq_one_iff] using hlen1
      simp only [discriminant, List.prod_cons, List.prod_nil, mul_one] at hdisc
      rw [← hhasse, h.hasse_singleton, hdisc]
    · intro hn2 hd
      have hlen2 : coeffs.length = 2 := hlen.trans hn2
      obtain ⟨a, b, rfl⟩ : ∃ a b, coeffs = [a, b] := by
        cases coeffs with
        | nil => simp at hlen2
        | cons a tail =>
            cases tail with
            | nil => simp at hlen2
            | cons b tail =>
                cases tail with
                | nil => exact ⟨a, b, rfl⟩
                | cons c tail => simp at hlen2
      have hab : a * b = h.negOne := by
        simpa [discriminant] using hdisc.trans hd
      rw [← hhasse]
      exact h.hasse_pair_discriminant hab
  · intro hconstraints
    rcases hconstraints with ⟨hrank1, hrank2⟩
    rcases Nat.eq_or_lt_of_le hn with rfl | hn_gt
    · refine ⟨[d], by simp, by simp [discriminant], ?_⟩
      simpa [h.hasse_singleton] using (hrank1 rfl).symm
    · by_cases hn2 : n = 2
      · subst n
        exact h.binary_realizable hsq hnondeg d s (hrank2 rfl)
      · have h3 : 3 ≤ n := by omega
        have hbase : h.InvariantTripleRealizable 3 d s :=
          h.ternary_realizable hsq hnondeg d s
        exact Nat.le_induction hbase
          (fun m _ hm ↦ h.realizable_succ hm) n h3

end AHSym

open Towers.CField.HSymbol

noncomputable section

universe u

/-- The square class of `-1` in an actual field. -/
def quadraticNegSquare (K : Type u) [Field K] :
    QuadraticSquareClass K :=
  QuotientGroup.mk (Units.mk0 (-1 : K) (neg_ne_zero.mpr one_ne_zero))

/-- The discriminant of an actual nondegenerate diagonal form. -/
def actualDiagonalDiscriminant
    {K : Type u} [Field K] (coeffs : List Kˣ) : QuadraticSquareClass K :=
  AHSym.discriminant
    (coeffs.map fun a ↦ (QuotientGroup.mk a : QuadraticSquareClass K))

/-- The Hasse invariant of an actual diagonal form, computed using the
concrete conic Hilbert sign. -/
def actualDiagonalHasse {K : Type u} [Field K] : List Kˣ → ℤˣ
  | [] => 1
  | a :: as =>
      quadraticHilbertSign (a : K) (a : K) *
        (as.map fun b ↦ quadraticHilbertSign (a : K) (b : K)).prod *
          actualDiagonalHasse as

/-- An actual diagonal quadratic form realizes the invariant triple
`(n,d,s)`.  Coefficients are units, so nondegeneracy is built into the
presentation rather than added as a hypothesis. -/
def ActualTripleRealizable
    (K : Type u) [Field K] (n : ℕ) (d : QuadraticSquareClass K) (s : ℤˣ) : Prop :=
  ∃ coeffs : List Kˣ,
    coeffs.length = n ∧ actualDiagonalDiscriminant coeffs = d ∧
      actualDiagonalHasse coeffs = s

/-- The two exceptional constraints, now expressed with the actual square
class of `-1` and the actual quadratic Hilbert sign. -/
def ActualConstraints
    (K : Type u) [Field K] (n : ℕ) (d : QuadraticSquareClass K) (s : ℤˣ) : Prop :=
  (n = 1 →
    s = hilbertSignSquare (quadraticNegSquare K) d) ∧
  (n = 2 → d = quadraticNegSquare K →
    s = hilbertSignSquare
      (quadraticNegSquare K) (quadraticNegSquare K))

/-- **Proposition VIII.6.11, actual local-field source statement.**  For a
positive rank, the displayed constraints are the only restrictions on the
rank, square-class discriminant, and Hasse sign of an actual nondegenerate
diagonal form over a nonarchimedean local field. -/
def QuadraticPairingNondegenerate : Prop :=
  ∀ (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K]
    [ValuativeRel K] [IsNonarchimedeanLocalField K] [NeZero (2 : K)]
    (n : ℕ) (d : QuadraticSquareClass K) (s : ℤˣ), 1 ≤ n →
      (ActualTripleRealizable K n d s ↔
        ActualConstraints K n d s)

/-- The narrow missing local input: construction of the bimultiplicative
Hilbert pairing on square classes, its concrete identification with the conic
sign, and its nondegeneracy. -/
structure ConcreteHilbertData
    (K : Type u) [Field K] where
  hilbert : AHSym (QuadraticSquareClass K) ℤˣ
  negOne_eq : hilbert.negOne = quadraticNegSquare K
  symbol_eq : ∀ a b,
    hilbert.symbol a b = hilbertSignSquare a b
  pairingNondegenerate : hilbert.PairingNondegenerate
  squareClass_nontrivial : Nontrivial (QuadraticSquareClass K)

/-- Construction of the concrete nondegenerate Hilbert pairing at every
nonarchimedean local field. -/
def ConcreteHilbertBridge : Prop :=
  ∀ (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K]
    [ValuativeRel K] [IsNonarchimedeanLocalField K] [NeZero (2 : K)],
    Nonempty (ConcreteHilbertData K)

private theorem quadratic_square_sq
    {K : Type u} [Field K] (a : QuadraticSquareClass K) : a ^ 2 = 1 := by
  induction a using QuotientGroup.induction_on with
  | _ a =>
      rw [← QuotientGroup.mk_pow]
      apply (QuotientGroup.eq_one_iff _).2
      exact Subgroup.mem_square.mpr ⟨a, pow_two a⟩

private theorem abstract_symbol_actual
    {K : Type u} [Field K] (H : ConcreteHilbertData K)
    (a : Kˣ) (coeffs : List Kˣ) :
    ((coeffs.map fun b ↦ (QuotientGroup.mk b : QuadraticSquareClass K)).map
        fun b ↦ H.hilbert.symbol (QuotientGroup.mk a) b).prod =
      (coeffs.map fun b ↦ quadraticHilbertSign (a : K) (b : K)).prod := by
  induction coeffs with
  | nil => rfl
  | cons b bs ih =>
      simp only [List.map_cons, List.prod_cons]
      rw [H.symbol_eq, hilbert_sign_mk, ih]
      rfl

private theorem abstract_hasse_actual
    {K : Type u} [Field K] (H : ConcreteHilbertData K)
    (coeffs : List Kˣ) :
    H.hilbert.hasse
        (coeffs.map fun a ↦ (QuotientGroup.mk a : QuadraticSquareClass K)) =
      actualDiagonalHasse coeffs := by
  induction coeffs with
  | nil => rfl
  | cons a as ih =>
      simp only [actualDiagonalHasse, List.map_cons,
        AHSym.hasse_cons]
      rw [ih, H.symbol_eq, hilbert_sign_mk,
        abstract_symbol_actual H]
      rfl

private theorem exists_actual_coefficients
    {K : Type u} [Field K] (xs : List (QuadraticSquareClass K)) :
    ∃ coeffs : List Kˣ,
      coeffs.map (fun a ↦ (QuotientGroup.mk a : QuadraticSquareClass K)) = xs := by
  induction xs with
  | nil => exact ⟨[], rfl⟩
  | cons x xs ih =>
      obtain ⟨a, ha⟩ := QuotientGroup.mk'_surjective (Subgroup.square Kˣ) x
      obtain ⟨coeffs, hcoeffs⟩ := ih
      refine ⟨a :: coeffs, ?_⟩
      change (QuotientGroup.mk' (Subgroup.square Kˣ)) a ::
          coeffs.map (fun a ↦ (QuotientGroup.mk a : QuadraticSquareClass K)) =
        x :: xs
      rw [ha, hcoeffs]

private theorem actual_realizable_abstract
    {K : Type u} [Field K] (H : ConcreteHilbertData K)
    (n : ℕ) (d : QuadraticSquareClass K) (s : ℤˣ) :
    ActualTripleRealizable K n d s ↔
      H.hilbert.InvariantTripleRealizable n d s := by
  constructor
  · rintro ⟨coeffs, hlen, hdisc, hhasse⟩
    refine ⟨coeffs.map fun a ↦ (QuotientGroup.mk a : QuadraticSquareClass K),
      by simpa using hlen, hdisc, ?_⟩
    rw [abstract_hasse_actual H, hhasse]
  · rintro ⟨xs, hlen, hdisc, hhasse⟩
    obtain ⟨coeffs, hcoeffs⟩ := exists_actual_coefficients xs
    refine ⟨coeffs, ?_, ?_, ?_⟩
    · simpa [← hcoeffs] using hlen
    · simpa [actualDiagonalDiscriminant, hcoeffs] using hdisc
    · rw [← abstract_hasse_actual H, hcoeffs, hhasse]

private theorem actual_constraints_abstract
    {K : Type u} [Field K] (H : ConcreteHilbertData K)
    (n : ℕ) (d : QuadraticSquareClass K) (s : ℤˣ) :
    ActualConstraints K n d s ↔
      H.hilbert.Constraints n d s := by
  simp only [ActualConstraints,
    AHSym.Constraints]
  rw [H.negOne_eq, H.symbol_eq, H.symbol_eq]

/-- The abstract construction specializes to actual local diagonal forms;
surjectivity of the square-class quotient supplies coefficient
representatives, so no representability hypothesis is added. -/
theorem local_concrete_hilbert
    (hconcrete : ConcreteHilbertBridge.{u}) :
    QuadraticPairingNondegenerate.{u} := by
  intro K _ _ _ _ _ n d s hn
  obtain ⟨H⟩ := hconcrete K
  letI : Nontrivial (QuadraticSquareClass K) := H.squareClass_nontrivial
  have honeNegOne : (1 : ℤˣ) ≠ -1 := by
    intro h
    have hval := congrArg (fun x : ℤˣ ↦ (x : ℤ)) h
    norm_num at hval
  letI : Nontrivial ℤˣ := ⟨⟨1, -1, honeNegOne⟩⟩
  have habstract : (∀ (n : ℕ) (d : QuadraticSquareClass K) (s : ℤˣ), 1 ≤ n →
        (H.hilbert.InvariantTripleRealizable n d s ↔
          H.hilbert.Constraints n d s)) :=
    H.hilbert.of_pairingNondegenerate
      quadratic_square_sq H.pairingNondegenerate
  rw [actual_realizable_abstract H,
    actual_constraints_abstract H]
  exact habstract n d s hn

end

end Towers.CField.QForms
