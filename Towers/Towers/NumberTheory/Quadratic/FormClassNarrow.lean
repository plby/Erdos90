import Towers.NumberTheory.Quadratic.FormNarrowEquivalence
import Towers.NumberTheory.Quadratic.FieldFormSetup


/-!
# Form classes to narrow ideal classes

For a squarefree radicand `d != 1`, every corrected primitive form class of fundamental
discriminant has a representative with positive leading coefficient.  Such a representative
defines an explicit form ideal, and the principal-scaling calculation for properly equivalent
positive-leading forms shows that its genuine narrow ideal class is independent of all choices.
-/

namespace Towers.NumberTheory.Milne

open Towers.NumberTheory
open scoped MatrixGroups NumberField nonZeroDivisors

noncomputable section

namespace FNarrow

open BQForm

variable {d : ℤ}
variable (hd : Squarefree d) (hd1 : d ≠ 1)
variable [Fact (∀ r : ℚ, r ^ 2 ≠ (d : ℚ) + 0 * r)]
variable [Module.Finite ℚ (QFModel d)]
variable [NumberField (QFModel d)]

/-- A determinant-one transformation making the leading coefficient positive.  It is chosen
to be the identity when the given representative already has positive leading coefficient. -/
def positiveTransform
    (Q : ProperPrimitive (quadraticFundamentalDiscriminant d)) : SL(2, ℤ) :=
  if _h : 0 < Q.1.a then 1 else
    Classical.choose
      (transform_proper_square
        (quadraticFundamentalDiscriminant d) Q.1 Q.2
        (fundamental_discriminant_square hd hd1))

omit [Fact (∀ (r : ℚ), r ^ 2 ≠ ↑d + 0 * r)] [Module.Finite ℚ (QFModel d)]
  [NumberField (QFModel d)] in
theorem positive_transform_pos
    (Q : ProperPrimitive (quadraticFundamentalDiscriminant d)) :
    0 < (Q.1.transform (positiveTransform hd hd1 Q)).a := by
  simp only [positiveTransform]
  split_ifs with h
  · rw [BQForm.transform_one]
    exact h
  · exact Classical.choose_spec
      (transform_proper_square
        (quadraticFundamentalDiscriminant d) Q.1 Q.2
        (fundamental_discriminant_square hd hd1))

omit [Fact (∀ (r : ℚ), r ^ 2 ≠ ↑d + 0 * r)] [Module.Finite ℚ (QFModel d)]
  [NumberField (QFModel d)] in
theorem positive_transform_one
    (Q : ProperPrimitive (quadraticFundamentalDiscriminant d))
    (hQ : 0 < Q.1.a) :
    positiveTransform hd hd1 Q = 1 := by
  simp [positiveTransform, hQ]

/-- The chosen positive-leading representative of a corrected proper form class. -/
def positiveRepresentative
    (Q : ProperPrimitive (quadraticFundamentalDiscriminant d)) :
    ProperPrimitive (quadraticFundamentalDiscriminant d) :=
  ⟨Q.1.transform (positiveTransform hd hd1 Q),
    (proper_discr_equiv
      ⟨positiveTransform hd hd1 Q, rfl⟩).mp Q.2⟩

omit [Fact (∀ (r : ℚ), r ^ 2 ≠ ↑d + 0 * r)] [Module.Finite ℚ (QFModel d)]
  [NumberField (QFModel d)] in
@[simp]
theorem representative_pos
    (Q : ProperPrimitive (quadraticFundamentalDiscriminant d)) :
    0 < (positiveRepresentative hd hd1 Q).1.a :=
  positive_transform_pos hd hd1 Q

omit [Fact (∀ (r : ℚ), r ^ 2 ≠ ↑d + 0 * r)] [Module.Finite ℚ (QFModel d)]
  [NumberField (QFModel d)] in
theorem positiver_equivale
    (Q : ProperPrimitive (quadraticFundamentalDiscriminant d)) :
    Q.1.Equivalent (positiveRepresentative hd hd1 Q).1 :=
  ⟨positiveTransform hd hd1 Q, rfl⟩

omit [Fact (∀ (r : ℚ), r ^ 2 ≠ ↑d + 0 * r)] [Module.Finite ℚ (QFModel d)]
  [NumberField (QFModel d)] in
@[simp]
theorem positi_repre_pos
    (Q : ProperPrimitive (quadraticFundamentalDiscriminant d))
    (hQ : 0 < Q.1.a) :
    positiveRepresentative hd hd1 Q = Q := by
  apply Subtype.ext
  simp [positiveRepresentative, positive_transform_one hd hd1 Q hQ,
    BQForm.transform_one]

/-- The integer `r` with `b = B + 2r` used in the explicit form ideal. -/
def middleRoot
    (Q : ProperPrimitive (quadraticFundamentalDiscriminant d)) : ℤ :=
  Classical.choose (middle_parameter_relation Q.1 Q.2.1)

omit [Fact (∀ (r : ℚ), r ^ 2 ≠ ↑d + 0 * r)] [Module.Finite ℚ (QFModel d)]
  [NumberField (QFModel d)] in
theorem middleRoot_spec
    (Q : ProperPrimitive (quadraticFundamentalDiscriminant d)) :
    Q.1.b = quadraticParameterB d + 2 * middleRoot Q ∧
      middleRoot Q ^ 2 + quadraticParameterB d * middleRoot Q -
          quadraticOrderParameter d = Q.1.a * Q.1.c :=
  Classical.choose_spec (middle_parameter_relation Q.1 Q.2.1)

/-- The genuine narrow ideal class of an explicit positive-leading form representative. -/
def ofPositiveRepresentative
    (Q : ProperPrimitive (quadraticFundamentalDiscriminant d))
    (hQ : 0 < Q.1.a) : NCGroup (QFModel d) :=
  NCGroup.mk (QFModel d)
    (mappedFormUnit
      (integersQuadraticOrder hd hd1).symm Q.1 (middleRoot Q)
      (middleRoot_spec Q).1
      (Q.2.1.trans (fundam_discr_param d)) hQ.ne')

/-- Properly equivalent positive-leading corrected forms give the same narrow ideal class. -/
theorem positi_repre_equiv
    (Q Q' : ProperPrimitive (quadraticFundamentalDiscriminant d))
    (hQ : 0 < Q.1.a) (hQ' : 0 < Q'.1.a) (h : Q.1.Equivalent Q'.1) :
    ofPositiveRepresentative hd hd1 Q hQ =
      ofPositiveRepresentative hd hd1 Q' hQ' := by
  obtain ⟨g, hg⟩ := h
  have hb' :
      (Q.1.transform g).b = quadraticParameterB d + 2 * middleRoot Q' := by
    rw [← hg]
    exact (middleRoot_spec Q').1
  have hQ'g : 0 < (Q.1.transform g).a := by simpa [hg] using hQ'
  have hnarrow := narrow_mapped_transform hd hd1
    Q.1 (middleRoot Q) (middleRoot Q') g (middleRoot_spec Q).1 hb'
    (Q.2.1.trans (fundam_discr_param d)) hQ hQ'g
  simpa [ofPositiveRepresentative, hg] using hnarrow

/-- Attach a narrow ideal class to an arbitrary corrected form representative by first choosing
the positive-leading representative in its proper equivalence class. -/
def ofRepresentative
    (Q : ProperPrimitive (quadraticFundamentalDiscriminant d)) :
    NCGroup (QFModel d) :=
  ofPositiveRepresentative hd hd1 (positiveRepresentative hd hd1 Q)
    (representative_pos hd hd1 Q)

/-- The preceding construction is independent of the corrected form representative. -/
theorem representative_equivalent
    (Q Q' : ProperPrimitive (quadraticFundamentalDiscriminant d))
    (h : Q.1.Equivalent Q'.1) :
    ofRepresentative hd hd1 Q = ofRepresentative hd hd1 Q' := by
  apply positi_repre_equiv hd hd1
  exact equivalent_trans (equivalent_symm (positiver_equivale hd hd1 Q))
    (equivalent_trans h (positiver_equivale hd hd1 Q'))

/-- **Theorem 4.29, form-to-ideal direction.**  Corrected proper primitive form classes of the
fundamental discriminant map canonically to genuine narrow ideal classes. -/
def narrowGroup :
    ProperPrimitDiscri (quadraticFundamentalDiscriminant d) →
      NCGroup (QFModel d) :=
  Quotient.lift (ofRepresentative hd hd1)
    (representative_equivalent hd hd1)

@[simp]
theorem narrow_group_mk
    (Q : ProperPrimitive (quadraticFundamentalDiscriminant d)) :
    narrowGroup hd hd1 (Quotient.mk _ Q) = ofRepresentative hd hd1 Q :=
  rfl

/-- On a representative whose leading coefficient is already positive, the quotient map is
the narrow class of its explicit form ideal, with no normalization visible in the result. -/
theorem narrow_mk_pos
    (Q : ProperPrimitive (quadraticFundamentalDiscriminant d))
    (hQ : 0 < Q.1.a) :
    narrowGroup hd hd1 (Quotient.mk _ Q) =
      ofPositiveRepresentative hd hd1 Q hQ := by
  rw [narrow_group_mk, ofRepresentative]
  exact positi_repre_equiv hd hd1
    (positiveRepresentative hd hd1 Q) Q
    (representative_pos hd hd1 Q) hQ
    (equivalent_symm (positiver_equivale hd hd1 Q))

end FNarrow

end

end Towers.NumberTheory.Milne
