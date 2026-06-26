import Towers.ClassField.HilbertSymbols.QuadraticSquareClasses
import Towers.ClassField.HasseNorm.LocalQuadraticConsequences
import Towers.ClassField.QuadraticForms.HilbertInvariants
import Towers.ClassField.QuadraticForms.AbstractSymbol

/-! # Chapter VIII, Section 6, Proposition 6.9

This file states the representation criterion with the actual square-class
group `Kˣ/Kˣ²` and an actual diagonal quadratic form.  The algebraic rank-one
case and the Hilbert-symbol calculation in rank two are proved here.  The
remaining bridges are precisely the local representation inputs used in the
source proof.
-/

namespace Towers.CField.QForms

open Towers.CField.HSymbol
open Towers.CField.HNorm

noncomputable section

universe u

variable {K : Type*} [Field K]

/-- The square class of a nonzero field element. -/
abbrev squareClass (a : Kˣ) : QuadraticSquareClass K :=
  QuotientGroup.mk a

/-- The diagonal quadratic form with the displayed nonzero coefficients. -/
def diagonalForm (coeffs : List Kˣ) :
    QuadraticForm K (Fin coeffs.length → K) :=
  QuadraticMap.weightedSumSquares K (fun i ↦ (coeffs.get i : K))

@[simp]
theorem diagonalForm_apply (coeffs : List Kˣ) (x : Fin coeffs.length → K) :
    diagonalForm coeffs x =
      ∑ i : Fin coeffs.length, (coeffs.get i : K) * (x i * x i) := by
  simp [diagonalForm, QuadraticMap.weightedSumSquares_apply]

/-- Representation by the diagonal form, with the source convention that
the representing vector is nonzero. -/
def DiagonalRepresents (coeffs : List Kˣ) (a : Kˣ) : Prop :=
  Represents (diagonalForm coeffs) (a : K)

/-- The square-class coefficient list attached to a diagonal form. -/
def squareClassCoefficients (coeffs : List Kˣ) : List (QuadraticSquareClass K) :=
  coeffs.map squareClass

/-- The exact four-case conclusion of Proposition VIII.6.9 for a diagonal
presentation. -/
def Criterion
    (h : AHSym (QuadraticSquareClass K) ℤˣ)
    (coeffs : List Kˣ) (a : Kˣ) : Prop :=
  match coeffs with
  | [] => False
  | [d] => squareClass a = squareClass d
  | [b, c] =>
      h.symbol (squareClass a)
          (h.negOne * AHSym.discriminant
            (squareClassCoefficients [b, c])) *
        h.symbol h.negOne
          (AHSym.discriminant
            (squareClassCoefficients [b, c])) =
        h.hasse (squareClassCoefficients [b, c])
  | [a₁, a₂, a₃] =>
      squareClass a ≠
          h.negOne * AHSym.discriminant
            (squareClassCoefficients [a₁, a₂, a₃]) ∨
        (squareClass a =
            h.negOne * AHSym.discriminant
              (squareClassCoefficients [a₁, a₂, a₃]) ∧
          h.symbol h.negOne h.negOne =
            h.hasse (squareClassCoefficients [a₁, a₂, a₃]))
  | _ :: _ :: _ :: _ :: _ => True

/-- The nonzero field element `-1`. -/
def negOneUnit (K : Type*) [Field K] : Kˣ :=
  Units.mk0 (-1 : K) (neg_ne_zero.mpr one_ne_zero)

/-- The concrete Hasse sign of a displayed diagonal coefficient list. -/
def concreteHasse : List Kˣ → ℤˣ
  | [] => 1
  | b :: bs =>
      quadraticHilbertSign (b : K) (b : K) *
        (bs.map fun c : Kˣ ↦ quadraticHilbertSign (b : K) (c : K)).prod *
        concreteHasse bs

/-- The exact four-case criterion written solely with actual coefficients
and the concrete quadratic Hilbert sign. -/
def ConcreteCriterion (coeffs : List Kˣ) (a : Kˣ) : Prop :=
  match coeffs with
  | [] => False
  | [d] => squareClass a = squareClass d
  | [b, c] =>
      quadraticHilbertSign (a : K) (-(b * c : Kˣ) : K) *
          quadraticHilbertSign (-1 : K) ((b * c : Kˣ) : K) =
        concreteHasse [b, c]
  | [a₁, a₂, a₃] =>
      squareClass a ≠ squareClass (negOneUnit K * (a₁ * a₂ * a₃)) ∨
        (squareClass a = squareClass (negOneUnit K * (a₁ * a₂ * a₃)) ∧
          quadraticHilbertSign (-1 : K) (-1 : K) =
            concreteHasse [a₁, a₂, a₃])
  | _ :: _ :: _ :: _ :: _ => True

/-- The concrete local Hilbert-symbol input.  Its distinguished `negOne` is
the square class of `-1`, and on representatives its pairing is the conic
indicator constructed in Chapter III, Section 4. -/
structure QHData (K : Type*) [Field K] where
  hilbert : NHSym (QuadraticSquareClass K) ℤˣ
  negOne_eq :
    hilbert.negOne = squareClass (Units.mk0 (-1 : K) (neg_ne_zero.mpr one_ne_zero))
  negativeValue_eq : hilbert.negativeValue = -1
  symbol_mk : ∀ a b : Kˣ,
    hilbert.symbol (squareClass a) (squareClass b) =
      quadraticHilbertSign (a : K) (b : K)

theorem square_coefficients_discriminant (coeffs : List Kˣ) :
    AHSym.discriminant (squareClassCoefficients coeffs) =
      squareClass coeffs.prod := by
  induction coeffs with
  | nil => simp [squareClassCoefficients, AHSym.discriminant,
      squareClass]
  | cons b bs ih =>
      rw [squareClassCoefficients, List.map_cons,
        AHSym.discriminant_cons]
      change squareClass b *
          AHSym.discriminant (squareClassCoefficients bs) = _
      rw [ih]
      exact (map_mul (QuotientGroup.mk' (Subgroup.square Kˣ)) b bs.prod).symm

theorem QHData.hasse_eq_concrete
    (H : QHData K) (coeffs : List Kˣ) :
    H.hilbert.hasse (squareClassCoefficients coeffs) = concreteHasse coeffs := by
  induction coeffs with
  | nil => simp [squareClassCoefficients, concreteHasse]
  | cons b bs ih =>
      change H.hilbert.hasse (squareClass b :: squareClassCoefficients bs) = _
      rw [AHSym.hasse_cons, concreteHasse, ih, H.symbol_mk]
      have hmap :
          (squareClassCoefficients bs).map
              (fun c ↦ H.hilbert.symbol (squareClass b) c) =
            bs.map (fun c : Kˣ ↦ quadraticHilbertSign (b : K) (c : K)) := by
        simp only [squareClassCoefficients, List.map_map]
        apply List.map_congr_left
        intro c hc
        exact H.symbol_mk b c
      rw [hmap]

/-- The abstract square-class formulation used in the proof agrees with the
literal coefficient/Hilbert-sign formulation exposed by the source
statement. -/
theorem criterion_iff_concrete
    (H : QHData K) (coeffs : List Kˣ) (a : Kˣ) :
    Criterion H.hilbert.toAHSym coeffs a ↔
      ConcreteCriterion coeffs a := by
  rcases coeffs with _ | ⟨d, tail⟩
  · rfl
  · rcases tail with _ | ⟨b, tail⟩
    · rfl
    · rcases tail with _ | ⟨c, tail⟩
      · simp only [Criterion, ConcreteCriterion,
          square_coefficients_discriminant, H.hasse_eq_concrete]
        rw [H.negOne_eq]
        simp only [List.prod_cons, List.prod_nil, mul_one]
        rw [← QuotientGroup.mk_mul, H.symbol_mk, H.symbol_mk]
        simp
      · rcases tail with _ | ⟨e, tail⟩
        · simp only [Criterion, ConcreteCriterion,
            square_coefficients_discriminant, H.hasse_eq_concrete]
          rw [H.negOne_eq]
          simp only [List.prod_cons, List.prod_nil, mul_one]
          rw [← QuotientGroup.mk_mul, H.symbol_mk]
          simp [negOneUnit, mul_assoc]
        · rfl

/-- Rank one is purely algebraic: `dX²` represents `a` precisely when
`a` and `d` have the same nonzero square class. -/
theorem diagonal_singleton_square (d a : Kˣ) :
    DiagonalRepresents [d] a ↔ squareClass a = squareClass d := by
  constructor
  · rintro ⟨x, hx, hvalue⟩
    have hx0 : x 0 ≠ 0 := by
      intro hzero
      apply hx
      funext i
      exact Fin.eq_zero i ▸ hzero
    let u : Kˣ := Units.mk0 (x 0) hx0
    have hunit : a = d * u ^ 2 := by
      rw [diagonalForm_apply] at hvalue
      ext
      simpa [Fin.sum_univ_one, u, pow_two] using hvalue.symm
    rw [hunit]
    change QuotientGroup.mk (d * u ^ 2) = QuotientGroup.mk d
    have huSquare : (QuotientGroup.mk (u ^ 2) : QuadraticSquareClass K) = 1 := by
      apply (QuotientGroup.eq_one_iff _).2
      exact Subgroup.mem_square.mpr ⟨u, pow_two u⟩
    rw [QuotientGroup.mk_mul, huSquare, mul_one]
  · intro hclass
    have hsquare : a / d ∈ Subgroup.square Kˣ :=
      QuotientGroup.eq_iff_div_mem.mp hclass
    obtain ⟨u, hu⟩ := Subgroup.mem_square.mp hsquare
    refine ⟨fun _ ↦ (u : K), ?_, ?_⟩
    · intro hzero
      have := congrFun hzero 0
      exact u.ne_zero this
    · have hunit : a = d * u ^ 2 := by
        calc
          a = (a / d) * d := by simp
          _ = (u * u) * d := by rw [hu]
          _ = d * u ^ 2 := by simp [pow_two, mul_comm]
      rw [diagonalForm_apply]
      simpa [Fin.sum_univ_one, pow_two] using
        congrArg (↑· : Kˣ → K) hunit.symm

@[simp]
theorem diagonal_form_pair (b c : Kˣ) (x : Fin 2 → K) :
    diagonalForm [b, c] x =
      (b : K) * (x 0 * x 0) + (c : K) * (x 1 * x 1) := by
  rw [diagonalForm_apply]
  change (∑ i : Fin 2, ([b, c].get i : K) * (x i * x i)) = _
  rw [Fin.sum_univ_two]
  rfl

/-- The elementary binary step in the source: after scaling by `a`,
representation of `a` is equivalent to the defining conic of the Hilbert
symbol having a nontrivial point. -/
theorem diagonal_hilbert_sign
    [NeZero (2 : K)] (a b c : Kˣ)
    (hnondegenerate : (diagonalForm [b, c]).Nondegenerate) :
    DiagonalRepresents [b, c] a ↔
      quadraticHilbertSign ((a * b : Kˣ) : K) ((a * c : Kˣ) : K) = 1 := by
  rw [hilbert_sign_one]
  constructor
  · rintro ⟨v, _hv, hvalue⟩
    rw [diagonal_form_pair] at hvalue
    refine ⟨v 0, v 1, (a : K), Or.inr (Or.inr a.ne_zero), ?_⟩
    change (a : K) ^ 2 =
      (a : K) * (b : K) * (v 0) ^ 2 + (a : K) * (c : K) * (v 1) ^ 2
    calc
      (a : K) ^ 2 = (a : K) * (a : K) := by ring
      _ = (a : K) *
          ((b : K) * (v 0 * v 0) + (c : K) * (v 1 * v 1)) :=
        congrArg (fun t : K ↦ (a : K) * t) hvalue.symm
      _ = (a : K) * (b : K) * (v 0) ^ 2 +
          (a : K) * (c : K) * (v 1) ^ 2 := by ring
  · rintro ⟨x, y, z, hxyz, heq⟩
    change z ^ 2 =
      (a : K) * (b : K) * x ^ 2 + (a : K) * (c : K) * y ^ 2 at heq
    by_cases hz : z = 0
    · have hxy : (![x, y] : Fin 2 → K) ≠ 0 := by
        intro hzero
        have hx : x = 0 := by simpa using congrFun hzero 0
        have hy : y = 0 := by simpa using congrFun hzero 1
        rcases hxyz with hx' | hy' | hz'
        · exact hx' hx
        · exact hy' hy
        · exact hz' hz
      have hsum : (b : K) * (x * x) + (c : K) * (y * y) = 0 := by
        apply (mul_eq_zero.mp ?_).resolve_left a.ne_zero
        calc
          (a : K) * ((b : K) * (x * x) + (c : K) * (y * y)) =
              (a : K) * (b : K) * x ^ 2 +
                (a : K) * (c : K) * y ^ 2 := by ring
          _ = z ^ 2 := heq.symm
          _ = 0 := by simp [hz]
      have hformZero : diagonalForm [b, c] (![x, y] : Fin 2 → K) = 0 := by
        rw [diagonal_form_pair]
        simpa using hsum
      exact represents_all_nondegenerate
        hnondegenerate ⟨![x, y], hxy, hformZero⟩ (a : K)
    · let v : Fin 2 → K := ![(a : K) * x / z, (a : K) * y / z]
      have hvalue : diagonalForm [b, c] v = (a : K) := by
        simp only [v, diagonal_form_pair, Matrix.cons_val_zero,
          Matrix.cons_val_one]
        field_simp [hz]
        rw [heq]
        ring
      refine ⟨v, ?_, hvalue⟩
      intro hv
      rw [hv] at hvalue
      have hformZero : diagonalForm [b, c] (0 : Fin 2 → K) = 0 := by
        rw [diagonal_form_pair]
        simp
      exact a.ne_zero (hvalue.symm.trans hformZero)

namespace AHSym

variable (h : AHSym (QuadraticSquareClass K) ℤˣ)

/-- The Hilbert-symbol calculation in the binary part of Proposition 6.9.
This is the algebraic content of the displayed computation in the source. -/
theorem binary_scaled_criterion (a b c : QuadraticSquareClass K) :
    h.symbol (a * b) (a * c) = 1 ↔
      h.symbol a (h.negOne * (b * c)) * h.symbol h.negOne (b * c) =
        h.hasse [b, c] := by
  rw [h.binary_scaled_symbol]
  rw [h.hasse_epsilon_discriminant]
  simp only [epsilon, discriminant, List.map, List.prod_cons, List.prod_nil, mul_one]
  constructor <;> intro H
  · have : h.symbol a (h.negOne * (b * c)) = h.symbol b c := by
      calc
        h.symbol a (h.negOne * (b * c)) =
            h.symbol a (h.negOne * (b * c)) * 1 := (mul_one _).symm
        _ = h.symbol a (h.negOne * (b * c)) *
            (h.symbol b c * h.symbol b c) := by rw [← pow_two, h.value_sq, mul_one]
        _ = h.symbol b c := by rw [← mul_assoc, H, one_mul]
    rw [this]
  · have Heq : h.symbol a (h.negOne * (b * c)) = h.symbol b c := by
      exact mul_right_cancel H
    rw [Heq, ← pow_two, h.value_sq]

end AHSym

/-- The only binary representation input: after scaling by `a`, the binary
form represents `a` exactly when the corresponding conic is split. -/
def BinaryRepresentationBridge : Prop :=
  ∀ (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K]
    [ValuativeRel K] [IsNonarchimedeanLocalField K] [NeZero (2 : K)]
    (H : QHData K) (a b c : Kˣ),
    (diagonalForm [b, c]).Nondegenerate →
      (DiagonalRepresents [b, c] a ↔
        H.hilbert.symbol (squareClass a * squareClass b)
          (squareClass a * squareClass c) = 1)

/-- The binary representation bridge is elementary and requires no local
classification theorem beyond the concrete definition of the Hilbert sign. -/
theorem binaryRepresentation :
    BinaryRepresentationBridge.{u} := by
  intro K _ _ _ _ _ H a b c hnondegenerate
  rw [diagonal_hilbert_sign a b c hnondegenerate]
  rw [← H.symbol_mk (a * b) (a * c)]
  change H.hilbert.symbol
      (QuotientGroup.mk (a * b)) (QuotientGroup.mk (a * c)) = 1 ↔
    H.hilbert.symbol
      (QuotientGroup.mk a * QuotientGroup.mk b)
      (QuotientGroup.mk a * QuotientGroup.mk c) = 1
  rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul]

/-- The simultaneous-pairing argument in rank three, isolated in exactly
the form needed after the algebraic Hilbert identities have been established. -/
def TernaryRepresentationBridge : Prop :=
  ∀ (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K]
    [ValuativeRel K] [IsNonarchimedeanLocalField K] [NeZero (2 : K)]
    (H : QHData K) (a a₁ a₂ a₃ : Kˣ),
    DiagonalRepresents [a₁, a₂, a₃] a ↔
      Criterion H.hilbert.toAHSym [a₁, a₂, a₃] a

/-- The dimension-at-least-four input, obtained in the source by applying
Corollary 3.10 to `q-aZ²`. -/
def LargeRepresentationBridge : Prop :=
  ∀ (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K]
    [ValuativeRel K] [IsNonarchimedeanLocalField K] [NeZero (2 : K)]
    (coeffs : List Kˣ) (a : Kˣ),
    4 ≤ coeffs.length → (diagonalForm coeffs).Nondegenerate →
      DiagonalRepresents coeffs a

/-- Proposition 6.9 follows from the concrete Hilbert pairing and the two
genuinely local representation inputs.  Rank one and the rank-two invariant
calculation are discharged in this file. -/
theorem of_localRepresentation
    (hHilbert : ∀ (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K]
      [ValuativeRel K] [IsNonarchimedeanLocalField K] [NeZero (2 : K)],
      QHData K)
    (hternary : TernaryRepresentationBridge.{u})
    (hlarge : LargeRepresentationBridge.{u}) :
    (∀ (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K]
          [ValuativeRel K] [IsNonarchimedeanLocalField K] [NeZero (2 : K)]
          (coeffs : List Kˣ) (a : Kˣ),
          (diagonalForm coeffs).Nondegenerate →
            (DiagonalRepresents coeffs a ↔
              ConcreteCriterion coeffs a)) := by
  intro K _ _ _ _ _ coeffs a hnondegenerate
  let H := hHilbert K
  cases coeffs with
  | nil =>
      change DiagonalRepresents [] a ↔ False
      simp only [iff_false]
      rintro ⟨x, hx, _hvalue⟩
      apply hx
      funext i
      exact Fin.elim0 i
  | cons d tail =>
      cases tail with
      | nil => exact diagonal_singleton_square d a
      | cons b tail =>
          cases tail with
          | nil =>
              rw [binaryRepresentation K H a d b hnondegenerate]
              rw [H.hilbert.toAHSym.binary_scaled_criterion]
              simpa [Criterion, squareClassCoefficients] using
                (criterion_iff_concrete H [d, b] a)
          | cons e tail =>
              cases tail with
              | nil =>
                  rw [hternary K H a d b e]
                  exact criterion_iff_concrete H [d, b, e] a
              | cons f tail =>
                  change DiagonalRepresents (d :: b :: e :: f :: tail) a ↔ True
                  simp only [iff_true]
                  exact hlarge K (d :: b :: e :: f :: tail) a (by simp)
                    hnondegenerate

end

end Towers.CField.QForms
