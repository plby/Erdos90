import Towers.ClassField.HasseNorm.QuadraticForms

/-! # Chapter VIII, Section 3, Proposition 3.7(d) and Lemma 3.8 -/

namespace Towers.CField.HNorm

universe u

variable {k : Type*} [Field k]

/-- The norm of `x + y√a` from the quadratic algebra `k[√a]`. -/
def quadratic_norm_criterion (a x y : k) : k :=
  x ^ 2 - a * y ^ 2

/-- If `a` is a nonzero square, its split quadratic norm form represents
every scalar. -/
private theorem quadratic_value_square
    [NeZero (2 : k)] {a : k} (ha : a ≠ 0) (haSquare : IsSquare a) (c : k) :
    ∃ x y : k, quadratic_norm_criterion a x y = c := by
  obtain ⟨s, rfl⟩ := haSquare
  have hs : s ≠ 0 := by
    intro hs
    apply ha
    simp [hs]
  refine ⟨(c + 1) / 2, (c - 1) / (2 * s), ?_⟩
  simp only [quadratic_norm_criterion]
  field_simp [NeZero.ne (2 : k), hs]
  ring

/-- Inverting an element of a quadratic algebra in coordinates inverts its
quadratic norm. -/
private theorem quadratic_inverse_coordinates
    {a x y : k} :
    quadratic_norm_criterion a
      (x / quadratic_norm_criterion a x y)
      (-y / quadratic_norm_criterion a x y) =
        (quadratic_norm_criterion a x y)⁻¹ := by
  simp only [quadratic_norm_criterion]
  field_simp

/-- Being a product of a norm from `k[√a]` and a norm from `k[√b]`. -/
def ProductQuadraticNorms (a b c : k) : Prop :=
  ∃ x y z t : k,
    quadratic_norm_criterion a x y * quadratic_norm_criterion b z t = c

/-- Coordinate form of being a norm from
`k[√a,√b] / k[√(ab)]`.

For `u = x + y√a + z√b + t√(ab)`, multiplication by the conjugate
which negates both `√a` and `√b` gives the displayed constant and
`√(ab)` coefficients. -/
def BiquadraticRelativeNorm (a b c : k) : Prop :=
  ∃ x y z t : k,
    x ^ 2 - a * y ^ 2 - b * z ^ 2 + a * b * t ^ 2 = c ∧
    2 * (x * t - y * z) = 0

/-- The easy direction of Lemma 3.8: a product of two quadratic norms is a
relative norm from the biquadratic algebra. -/
theorem biquadratic_quadratic_norms
    {a b c : k} (h : ProductQuadraticNorms a b c) :
    BiquadraticRelativeNorm a b c := by
  obtain ⟨x, y, z, t, hnorm⟩ := h
  refine ⟨x * z, y * z, x * t, y * t, ?_, ?_⟩
  · calc
      (x * z) ^ 2 - a * (y * z) ^ 2 - b * (x * t) ^ 2 +
          a * b * (y * t) ^ 2 =
          quadratic_norm_criterion a x y * quadratic_norm_criterion b z t := by
            simp [quadratic_norm_criterion]
            ring
      _ = c := hnorm
  · ring

/-- The converse direction of Lemma 3.8.  The vanishing mixed coefficient
means that the matrix of four coordinates has rank at most one.  Factoring
that matrix writes the relative norm as a product of two quadratic norms. -/
theorem quadratic_norms_biquadratic
    [NeZero (2 : k)] {a b c : k}
    (h : BiquadraticRelativeNorm a b c) :
    ProductQuadraticNorms a b c := by
  obtain ⟨x, y, z, t, hvalue, hmixed⟩ := h
  have hdet : x * t = y * z := by
    apply sub_eq_zero.mp
    exact (mul_eq_zero.mp hmixed).resolve_left (NeZero.ne (2 : k))
  by_cases hx : x = 0
  · subst x
    have hyz : y * z = 0 := by simpa using hdet.symm
    rcases mul_eq_zero.mp hyz with hy | hz
    · subst y
      refine ⟨z, t, 0, 1, ?_⟩
      calc
        quadratic_norm_criterion a z t * quadratic_norm_criterion b 0 1 =
            0 ^ 2 - a * 0 ^ 2 - b * z ^ 2 + a * b * t ^ 2 := by
          simp [quadratic_norm_criterion]
          ring
        _ = c := hvalue
    · subst z
      refine ⟨0, 1, y, t, ?_⟩
      calc
        quadratic_norm_criterion a 0 1 * quadratic_norm_criterion b y t =
            0 ^ 2 - a * y ^ 2 - b * 0 ^ 2 + a * b * t ^ 2 := by
          simp [quadratic_norm_criterion]
          ring
        _ = c := hvalue
  · have ht : t = y * z / x := by
      apply (eq_div_iff hx).2
      simpa [mul_comm] using hdet
    refine ⟨x, y, 1, z / x, ?_⟩
    calc
      quadratic_norm_criterion a x y * quadratic_norm_criterion b 1 (z / x) =
          x ^ 2 - a * y ^ 2 - b * z ^ 2 +
            a * b * (y * z / x) ^ 2 := by
        simp only [quadratic_norm_criterion, one_pow]
        field_simp [hx]
        ring
      _ = c := by simpa [ht] using hvalue

/-- The Hilbert-90 descent formulation used in the source proof of Lemma
3.8.  The coordinate factorization above proves it without requiring a
separate cohomological interface. -/
def Hilbert90Bridge : Prop :=
  ∀ (k : Type u) [Field k] [NeZero (2 : k)] (a b : k) (c : kˣ),
    BiquadraticRelativeNorm a b (c : k) →
      ProductQuadraticNorms a b (c : k)

/-- The Hilbert-90 bridge follows from the direct coordinate
factorization. -/
theorem hilbert90Bridge : Hilbert90Bridge.{u} := by
  intro k _ _ a b c
  exact quadratic_norms_biquadratic

theorem of_hilbert90
    (h90 : Hilbert90Bridge.{u}) :
    (∀ (k : Type u) [Field k] [NeZero (2 : k)] (a b : k) (c : kˣ),
          ProductQuadraticNorms a b (c : k) ↔
            BiquadraticRelativeNorm a b (c : k)) := by
  intro k _ _ a b c
  constructor
  · exact biquadratic_quadratic_norms
  · exact h90 k a b c

/-- **Lemma VIII.3.8.** An element is a product of norms from the two
quadratic algebras exactly when it is the relative norm from their
biquadratic compositum. -/
theorem quadraticValueStatement : (∀ (k : Type u) [Field k] [NeZero (2 : k)] (a b : k) (c : kˣ),
      ProductQuadraticNorms a b (c : k) ↔
        BiquadraticRelativeNorm a b (c : k)) :=
  of_hilbert90 hilbert90Bridge

/-- The four-variable form in Proposition 3.7(d), written as
`Nm_b(X+Y√b) - c Nm_a(Z+T√a)`. -/
def quaternaryNormForm (a b c : k) :
    QuadraticForm k ((k × k) × (k × k)) :=
  (binaryNormForm b).prod ((-c) • binaryNormForm a)

@[simp]
theorem quaternary_norm_form (a b c : k) (v : (k × k) × (k × k)) :
    quaternaryNormForm a b c v =
      v.1.1 ^ 2 - b * v.1.2 ^ 2 - c * v.2.1 ^ 2 + a * c * v.2.2 ^ 2 := by
  simp [quaternaryNormForm, binary_norm_form]
  ring

/-- The elementary ratio-of-norms step in Proposition 3.7(d), including the
degenerate square cases. -/
def NormProductBridge : Prop :=
  ∀ (k : Type u) [Field k] [NeZero (2 : k)] (a b c : kˣ),
    ¬ (quaternaryNormForm (a : k) (b : k) (c : k)).Anisotropic ↔
      ProductQuadraticNorms (a : k) (b : k) (c : k)

/-- The elementary ratio-of-norms argument proves the norm-product bridge.
The zero-denominator cases are exactly the split quadratic-algebra cases,
where the corresponding norm form represents every scalar. -/
theorem normProductBridge :
    NormProductBridge.{u} := by
  intro k _ _ a b c
  rw [QuadraticMap.not_anisotropic_iff_exists]
  constructor
  · rintro ⟨⟨⟨x, y⟩, ⟨z, t⟩⟩, hvector, hzero⟩
    have hnorm :
        quadratic_norm_criterion (b : k) x y =
          (c : k) * quadratic_norm_criterion (a : k) z t := by
      calc
        quadratic_norm_criterion (b : k) x y =
            (c : k) * quadratic_norm_criterion (a : k) z t +
              quaternaryNormForm (a : k) (b : k) (c : k)
                ((x, y), (z, t)) := by
          simp [quadratic_norm_criterion, quaternary_norm_form]
          ring
        _ = (c : k) * quadratic_norm_criterion (a : k) z t := by
          rw [hzero, add_zero]
    by_cases hdenom : quadratic_norm_criterion (a : k) z t = 0
    · have hnum : quadratic_norm_criterion (b : k) x y = 0 := by
        rw [hnorm, hdenom, mul_zero]
      by_cases hzt : (z, t) = (0, 0)
      · have hxy : (x, y) ≠ (0, 0) := by
          intro hxy
          apply hvector
          simp [hxy, hzt]
        have hbSquare : IsSquare (b : k) :=
          (binary_isotropic_square (b : k)).mp <| by
            rw [QuadraticMap.not_anisotropic_iff_exists]
            exact ⟨(x, y), hxy, by simpa [binary_norm_form,
              quadratic_norm_criterion] using hnum⟩
        obtain ⟨r, s, hrs⟩ :=
          quadratic_value_square
            (Units.ne_zero b) hbSquare (c : k)
        exact ⟨1, 0, r, s, by simpa [quadratic_norm_criterion] using hrs⟩
      · have haSquare : IsSquare (a : k) :=
          (binary_isotropic_square (a : k)).mp <| by
            rw [QuadraticMap.not_anisotropic_iff_exists]
            exact ⟨(z, t), hzt, by simpa [binary_norm_form,
              quadratic_norm_criterion] using hdenom⟩
        obtain ⟨r, s, hrs⟩ :=
          quadratic_value_square
            (Units.ne_zero a) haSquare (c : k)
        exact ⟨r, s, 1, 0, by simpa [quadratic_norm_criterion] using hrs⟩
    · refine ⟨z / quadratic_norm_criterion (a : k) z t,
        -t / quadratic_norm_criterion (a : k) z t, x, y, ?_⟩
      rw [quadratic_inverse_coordinates, hnorm]
      field_simp [hdenom]
  · rintro ⟨x, y, z, t, hproduct⟩
    let n := quadratic_norm_criterion (a : k) x y
    have hn : n ≠ 0 := by
      intro hn
      have hc0 : (c : k) = 0 := by
        calc
          (c : k) = n * quadratic_norm_criterion (b : k) z t := by
            simpa [n] using hproduct.symm
          _ = 0 := by rw [hn, zero_mul]
      exact (Units.ne_zero c) hc0
    refine ⟨⟨⟨z, t⟩, ⟨x / n, -y / n⟩⟩, ?_, ?_⟩
    · intro hvector
      have hx : x / n = 0 := by
        exact congrArg (fun v : (k × k) × (k × k) => v.2.1) hvector
      have hy : -y / n = 0 := by
        exact congrArg (fun v : (k × k) × (k × k) => v.2.2) hvector
      have hx0 : x = 0 := (div_eq_zero_iff).mp hx |>.resolve_right hn
      have hy0 : y = 0 := by
        have : -y = 0 := (div_eq_zero_iff).mp hy |>.resolve_right hn
        simpa using this
      apply hn
      simp [n, quadratic_norm_criterion, hx0, hy0]
    · calc
        quaternaryNormForm (a : k) (b : k) (c : k)
            ((z, t), (x / n, -y / n)) =
            quadratic_norm_criterion (b : k) z t -
              (c : k) * quadratic_norm_criterion (a : k) (x / n) (-y / n) := by
          simp [quaternary_norm_form, quadratic_norm_criterion]
          ring
        _ = 0 := by
          rw [quadratic_inverse_coordinates, ← hproduct]
          change quadratic_norm_criterion (b : k) z t -
            n * quadratic_norm_criterion (b : k) z t * n⁻¹ = 0
          field_simp [hn]
          ring

/-- **Proposition VIII.3.7(d) (source statement).** -/
def QuaternaryIsotropicBiquadratic : Prop :=
  ∀ (k : Type u) [Field k] [NeZero (2 : k)] (a b c : kˣ),
    ¬ (quaternaryNormForm (a : k) (b : k) (c : k)).Anisotropic ↔
      BiquadraticRelativeNorm (a : k) (b : k) (c : k)

/-- Proposition 3.7(d) from its elementary norm-product reduction and Lemma
3.8. -/
theorem quaternary_norm_criterion
    (hproduct : NormProductBridge.{u})
    (h38 : (∀ (k : Type u) [Field k] [NeZero (2 : k)] (a b : k) (c : kˣ),
          ProductQuadraticNorms a b (c : k) ↔
            BiquadraticRelativeNorm a b (c : k))) :
    QuaternaryIsotropicBiquadratic.{u} := by
  intro k _ _ a b c
  rw [hproduct k a b c]
  exact h38 k a b c

/-- **Proposition VIII.3.7(d).** The four-variable norm form is isotropic
exactly when `c` is the indicated relative norm from the biquadratic
algebra. -/
theorem quaternary_isotropic_biquadratic : QuaternaryIsotropicBiquadratic.{u} :=
  quaternary_norm_criterion normProductBridge
    quadraticValueStatement

end Towers.CField.HNorm
