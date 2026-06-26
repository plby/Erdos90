import Towers.NumberTheory.LocalInertia


open Filter
open scoped Pointwise EuclideanGeometry Topology

noncomputable section

open NumberField

namespace Towers

lemma ideal_generator_sq
    {R : Type*} [CommRing R]
    (P : Ideal R) [P.IsMaximal]
    {π c : R}
    (hπ_mem : π ∈ P)
    (hπ_not_sq : π ∉ P ^ 2)
    (hcπ : c * π ∈ P ^ 2) :
    c ∈ P := by
  classical
  by_contra hc_not_mem
  letI : Field (R ⧸ P) := Ideal.Quotient.field P
  have hc_ne_zero : Ideal.Quotient.mk P c ≠ 0 := by
    intro hc_zero
    exact hc_not_mem ((Ideal.Quotient.eq_zero_iff_mem (I := P)).1 hc_zero)
  obtain ⟨r, hr⟩ :=
    Ideal.Quotient.mk_surjective ((Ideal.Quotient.mk P c)⁻¹)
  have hrc_unit : Ideal.Quotient.mk P (r * c) = 1 := by
    calc
      Ideal.Quotient.mk P (r * c) =
          Ideal.Quotient.mk P r * Ideal.Quotient.mk P c := by
        simp
      _ = (Ideal.Quotient.mk P c)⁻¹ * Ideal.Quotient.mk P c := by
        rw [hr]
      _ = 1 := by
        exact inv_mul_cancel₀ hc_ne_zero
  have hrc_sub_one : r * c - 1 ∈ P := by
    exact (Ideal.Quotient.eq (I := P)).1 hrc_unit
  have hone_sub_rc : 1 - r * c ∈ P := by
    have hneg : - (r * c - 1) ∈ P := P.neg_mem hrc_sub_one
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hneg
  have hfirst : (1 - r * c) * π ∈ P ^ 2 := by
    rw [pow_two]
    exact Ideal.mul_mem_mul hone_sub_rc hπ_mem
  have hsecond : r * (c * π) ∈ P ^ 2 := by
    exact Ideal.mul_mem_left (P ^ 2) r hcπ
  have hsum : (1 - r * c) * π + r * (c * π) ∈ P ^ 2 := by
    exact Ideal.add_mem (P ^ 2) hfirst hsecond
  have hπ_sq : π ∈ P ^ 2 := by
    convert hsum using 1
    ring
  exact hπ_not_sq hπ_sq

lemma cotangent_unique_ideal
    {R : Type*} [CommRing R]
    (P : Ideal R) [P.IsMaximal]
    {π x a b : R}
    (hπ_mem : π ∈ P)
    (hπ_not_sq : π ∉ P ^ 2)
    (ha : x - a * π ∈ P ^ 2)
    (hb : x - b * π ∈ P ^ 2) :
    a - b ∈ P := by
  classical
  have hdiff : (x - b * π) - (x - a * π) ∈ P ^ 2 := by
    exact Ideal.sub_mem (P ^ 2) hb ha
  have hmul : (a - b) * π ∈ P ^ 2 := by
    convert hdiff using 1
    ring
  exact ideal_generator_sq P hπ_mem hπ_not_sq hmul

lemma dedekind_nonzero_sq
    {A : Type*} [CommRing A] [IsDedekindDomain A]
    (P : Ideal A) [P.IsPrime] (hP0 : P ≠ ⊥) :
    ∃ π : A, π ∈ P ∧ π ∉ P ^ 2 := by
  classical
  have hP_ne_top : P ≠ ⊤ :=
    Ideal.IsPrime.ne_top (show P.IsPrime from inferInstance)
  have hstrict : P ^ 2 < P := by
    have hanti := Ideal.pow_right_strictAnti P hP0 hP_ne_top
    have hlt : P ^ 2 < P ^ 1 := hanti (by norm_num : (1 : ℕ) < 2)
    simpa using hlt
  obtain ⟨π, hπ_mem, hπ_not_sq⟩ := SetLike.exists_of_lt hstrict
  exact ⟨π, hπ_mem, hπ_not_sq⟩

lemma number_not_sq
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    {q : ℕ} (hq : Nat.Prime q)
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)] :
    ∃ π : NumberField.RingOfIntegers L, π ∈ P ∧ π ∉ P ^ 2 := by
  classical
  have hp_ne_bot : Ideal.rationalPrimeIdeal q ≠ ⊥ :=
    rational_ne_bot hq
  have hP_ne_bot : P ≠ ⊥ :=
    Ideal.ne_bot_of_liesOver_of_ne_bot hp_ne_bot P
  exact dedekind_nonzero_sq P hP_ne_bot

lemma dedekind_complement_sq
    {A : Type*} [CommRing A] [IsDedekindDomain A]
    (P : Ideal A) [P.IsPrime] [P.IsMaximal]
    {π : A}
    (hπ_mem : π ∈ P)
    (hπ_not_sq : π ∉ P ^ 2) :
    ∃ J : Ideal A, Ideal.span ({π} : Set A) = P * J ∧ J ⊔ P = ⊤ := by
  classical
  have hspan_le : Ideal.span ({π} : Set A) ≤ P := by
    exact (Ideal.span_singleton_le_iff_mem P).2 hπ_mem
  have hdiv : P ∣ Ideal.span ({π} : Set A) := by
    exact (Ideal.dvd_iff_le).2 hspan_le
  obtain ⟨J, hJ⟩ := hdiv
  refine ⟨J, hJ, ?_⟩
  have hJ_not_le : ¬ J ≤ P := by
    intro hJP
    have hspan_le_sq : Ideal.span ({π} : Set A) ≤ P ^ 2 := by
      rw [hJ, pow_two]
      exact mul_le_mul_right hJP P
    have hπ_span : π ∈ Ideal.span ({π} : Set A) := by
      exact (Ideal.mem_span_singleton).2 (dvd_refl π)
    exact hπ_not_sq (hspan_le_sq hπ_span)
  by_contra hsup_ne
  have hle_sup : J ⊔ P ≤ P := by
    have hEq : P = J ⊔ P :=
      Ideal.IsMaximal.eq_of_le (show P.IsMaximal from inferInstance) hsup_ne le_sup_right
    rw [← hEq]
  exact hJ_not_le (le_sup_left.trans hle_sup)

lemma dedekind_spans_complement
    {A : Type*} [CommRing A]
    (P J : Ideal A) {π x : A}
    (hπ : Ideal.span ({π} : Set A) = P * J)
    (hsup : J ⊔ P = ⊤)
    (hx : x ∈ P) :
    ∃ a : A, x - a * π ∈ P ^ 2 := by
  classical
  have hone : (1 : A) ∈ J ⊔ P := by
    rw [hsup]
    trivial
  rw [Submodule.mem_sup] at hone
  rcases hone with ⟨j, hj, p, hp, hjp⟩
  have hjx_span : j * x ∈ Ideal.span ({π} : Set A) := by
    rw [hπ]
    convert Ideal.mul_mem_mul hx hj using 1
    ring
  obtain ⟨a, ha⟩ := (Ideal.mem_span_singleton).1 hjx_span
  refine ⟨a, ?_⟩
  have hpx : p * x ∈ P ^ 2 := by
    rw [pow_two]
    exact Ideal.mul_mem_mul hp hx
  convert hpx using 1
  calc
    x - a * π = (j + p) * x - a * π := by
      rw [hjp]
      ring
    _ = p * x := by
      rw [add_mul, ha]
      ring

lemma cotangent_spans_sq
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    {q : ℕ} (hq : Nat.Prime q)
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)]
    (π : NumberField.RingOfIntegers L)
    (hπ_mem : π ∈ P)
    (hπ_not_sq : π ∉ P ^ 2) :
    ∀ x : NumberField.RingOfIntegers L,
      x ∈ P → ∃ a : NumberField.RingOfIntegers L, x - a * π ∈ P ^ 2 := by
  classical
  letI : P.IsMaximal :=
    number_above_maximal (L := L) hq P
  obtain ⟨J, hπ_span, hJP_top⟩ :=
    dedekind_complement_sq P hπ_mem hπ_not_sq
  intro x hx
  exact dedekind_spans_complement P J hπ_span hJP_top hx

lemma prime_cotangent_generator
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    {q : ℕ} (hq : Nat.Prime q)
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)] :
    ∃ π : NumberField.RingOfIntegers L,
      π ∈ P ∧ π ∉ P ^ 2 ∧
        ∀ x : NumberField.RingOfIntegers L,
          x ∈ P → ∃ a : NumberField.RingOfIntegers L, x - a * π ∈ P ^ 2 := by
  classical
  obtain ⟨π, hπ_mem, hπ_not_sq⟩ :=
    number_not_sq (L := L) hq P
  exact
    ⟨π, hπ_mem, hπ_not_sq,
      cotangent_spans_sq
        (L := L) hq P π hπ_mem hπ_not_sq⟩

lemma number_generator_scalar
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    {q : ℕ} (_hq : Nat.Prime q)
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)]
    (π : NumberField.RingOfIntegers L)
    (hπ_mem : π ∈ P)
    (_hπ_not_sq : π ∉ P ^ 2)
    (hπ_spans : ∀ x : NumberField.RingOfIntegers L,
      x ∈ P → ∃ a : NumberField.RingOfIntegers L, x - a * π ∈ P ^ 2)
    (σ : P.inertia (Gal(L/ℚ))) :
    ∃ a : NumberField.RingOfIntegers L,
      ((σ : Gal(L/ℚ)) • π) - a * π ∈ P ^ 2 := by
  classical
  have hσπ_mem :
      ((σ : Gal(L/ℚ)) • π) ∈ P := by
    exact number_smul_prime (L := L) P σ hπ_mem
  have hscalar :
      ∃ a : NumberField.RingOfIntegers L,
        ((σ : Gal(L/ℚ)) • π) - a * π ∈ P ^ 2 := by
    exact hπ_spans ((σ : Gal(L/ℚ)) • π) hσπ_mem
  exact hscalar

lemma cotangent_scalar_unique
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    {q : ℕ} (hq : Nat.Prime q)
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)]
    (π : NumberField.RingOfIntegers L)
    (hπ_mem : π ∈ P)
    (hπ_not_sq : π ∉ P ^ 2)
    (σ : P.inertia (Gal(L/ℚ)))
    {a b : NumberField.RingOfIntegers L}
    (ha : ((σ : Gal(L/ℚ)) • π) - a * π ∈ P ^ 2)
    (hb : ((σ : Gal(L/ℚ)) • π) - b * π ∈ P ^ 2) :
    a - b ∈ P := by
  classical
  letI : P.IsMaximal :=
    number_above_maximal (L := L) hq P
  have hunique :
      a - b ∈ P := by
    exact
      cotangent_unique_ideal
        P hπ_mem hπ_not_sq ha hb
  exact hunique

lemma cotangent_scalar_not
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    {q : ℕ} (_hq : Nat.Prime q)
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)]
    (π : NumberField.RingOfIntegers L)
    (hπ_mem : π ∈ P)
    (hπ_not_sq : π ∉ P ^ 2)
    (σ : P.inertia (Gal(L/ℚ)))
    (a : NumberField.RingOfIntegers L)
    (ha : ((σ : Gal(L/ℚ)) • π) - a * π ∈ P ^ 2) :
    a ∉ P := by
  classical
  intro ha_mem
  have haπ : a * π ∈ P ^ 2 := by
    rw [pow_two]
    exact Ideal.mul_mem_mul ha_mem hπ_mem
  have hσπ_sq : ((σ : Gal(L/ℚ)) • π) ∈ P ^ 2 := by
    have hsum : (((σ : Gal(L/ℚ)) • π) - a * π) + a * π ∈ P ^ 2 := by
      exact Ideal.add_mem (P ^ 2) ha haπ
    convert hsum using 1
    ring
  let τ : P.inertia (Gal(L/ℚ)) := σ⁻¹
  have hback_sq : ((τ : Gal(L/ℚ)) • ((σ : Gal(L/ℚ)) • π)) ∈ P ^ 2 := by
    exact number_inertia_sq (L := L) P τ hσπ_sq
  have hπ_sq : π ∈ P ^ 2 := by
    simpa [τ, mul_smul] using hback_sq
  exact hπ_not_sq hπ_sq

lemma number_cotangent_scalar
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    {q : ℕ} (hq : Nat.Prime q)
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)]
    (π : NumberField.RingOfIntegers L)
    (hπ_mem : π ∈ P)
    (hπ_not_sq : π ∉ P ^ 2)
    (σ : P.inertia (Gal(L/ℚ)))
    (a : NumberField.RingOfIntegers L)
    (ha : ((σ : Gal(L/ℚ)) • π) - a * π ∈ P ^ 2) :
    algebraMap (NumberField.RingOfIntegers L) P.ResidueField a ≠ 0 := by
  classical
  have ha_not_mem :
      a ∉ P := by
    exact
      cotangent_scalar_not
        (L := L) hq P π hπ_mem hπ_not_sq σ a ha
  intro ha_zero
  have ha_mem : a ∈ P := by
    exact (Ideal.algebraMap_residueField_eq_zero (I := P)).1 ha_zero
  exact ha_not_mem ha_mem

lemma cotangent_scalar_unit
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    {q : ℕ} (hq : Nat.Prime q)
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)]
    (π : NumberField.RingOfIntegers L)
    (hπ_mem : π ∈ P)
    (hπ_not_sq : π ∉ P ^ 2)
    (σ : P.inertia (Gal(L/ℚ)))
    (a : NumberField.RingOfIntegers L)
    (ha : ((σ : Gal(L/ℚ)) • π) - a * π ∈ P ^ 2) :
    ∃ u : P.ResidueFieldˣ,
      (u : P.ResidueField) =
        algebraMap (NumberField.RingOfIntegers L) P.ResidueField a := by
  classical
  let c : P.ResidueField :=
    algebraMap (NumberField.RingOfIntegers L) P.ResidueField a
  have hc_ne_zero : c ≠ 0 := by
    exact
      number_cotangent_scalar
        (L := L) hq P π hπ_mem hπ_not_sq σ a ha
  refine ⟨Units.mk0 c hc_ne_zero, ?_⟩
  rfl

noncomputable def field_cotangent_scalar
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    {q : ℕ} (hq : Nat.Prime q)
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)]
    (π : NumberField.RingOfIntegers L)
    (hπ_mem : π ∈ P)
    (hπ_not_sq : π ∉ P ^ 2)
    (hπ_spans : ∀ x : NumberField.RingOfIntegers L,
      x ∈ P → ∃ a : NumberField.RingOfIntegers L, x - a * π ∈ P ^ 2)
    (σ : P.inertia (Gal(L/ℚ))) :
    NumberField.RingOfIntegers L :=
  Classical.choose
    (number_generator_scalar
      (L := L) hq P π hπ_mem hπ_not_sq hπ_spans σ)

lemma cotangent_scalar_spec
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    {q : ℕ} (hq : Nat.Prime q)
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)]
    (π : NumberField.RingOfIntegers L)
    (hπ_mem : π ∈ P)
    (hπ_not_sq : π ∉ P ^ 2)
    (hπ_spans : ∀ x : NumberField.RingOfIntegers L,
      x ∈ P → ∃ a : NumberField.RingOfIntegers L, x - a * π ∈ P ^ 2)
    (σ : P.inertia (Gal(L/ℚ))) :
    ((σ : Gal(L/ℚ)) • π) -
        field_cotangent_scalar
          (L := L) hq P π hπ_mem hπ_not_sq hπ_spans σ * π ∈ P ^ 2 := by
  classical
  have hspec :=
    Classical.choose_spec
      (number_generator_scalar
        (L := L) hq P π hπ_mem hπ_not_sq hπ_spans σ)
  exact hspec

noncomputable def number_generator_unit
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    {q : ℕ} (hq : Nat.Prime q)
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)]
    (π : NumberField.RingOfIntegers L)
    (hπ_mem : π ∈ P)
    (hπ_not_sq : π ∉ P ^ 2)
    (hπ_spans : ∀ x : NumberField.RingOfIntegers L,
      x ∈ P → ∃ a : NumberField.RingOfIntegers L, x - a * π ∈ P ^ 2)
    (σ : P.inertia (Gal(L/ℚ))) :
    P.ResidueFieldˣ :=
  Units.mk0
    (algebraMap (NumberField.RingOfIntegers L) P.ResidueField
      (field_cotangent_scalar
        (L := L) hq P π hπ_mem hπ_not_sq hπ_spans σ))
    (number_cotangent_scalar
      (L := L) hq P π hπ_mem hπ_not_sq σ
      (field_cotangent_scalar
        (L := L) hq P π hπ_mem hπ_not_sq hπ_spans σ)
      (cotangent_scalar_spec
        (L := L) hq P π hπ_mem hπ_not_sq hπ_spans σ))

lemma cotangent_generator_unit
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    {q : ℕ} (hq : Nat.Prime q)
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)]
    (π : NumberField.RingOfIntegers L)
    (hπ_mem : π ∈ P)
    (hπ_not_sq : π ∉ P ^ 2)
    (hπ_spans : ∀ x : NumberField.RingOfIntegers L,
      x ∈ P → ∃ a : NumberField.RingOfIntegers L, x - a * π ∈ P ^ 2) :
    number_generator_unit
        (L := L) hq P π hπ_mem hπ_not_sq hπ_spans
        (1 : P.inertia (Gal(L/ℚ))) = 1 := by
  classical
  apply Units.ext
  change
    algebraMap (NumberField.RingOfIntegers L) P.ResidueField
        (field_cotangent_scalar
          (L := L) hq P π hπ_mem hπ_not_sq hπ_spans
          (1 : P.inertia (Gal(L/ℚ)))) = 1
  let a : NumberField.RingOfIntegers L :=
    field_cotangent_scalar
      (L := L) hq P π hπ_mem hπ_not_sq hπ_spans
      (1 : P.inertia (Gal(L/ℚ)))
  have ha :
      (((1 : P.inertia (Gal(L/ℚ))) : Gal(L/ℚ)) • π) - a * π ∈ P ^ 2 := by
    simpa [a] using
      cotangent_scalar_spec
        (L := L) hq P π hπ_mem hπ_not_sq hπ_spans
        (1 : P.inertia (Gal(L/ℚ)))
  have hone :
      (((1 : P.inertia (Gal(L/ℚ))) : Gal(L/ℚ)) • π) - 1 * π ∈ P ^ 2 := by
    simp
  have ha_sub_one : a - 1 ∈ P := by
    exact
      cotangent_scalar_unique
        (L := L) hq P π hπ_mem hπ_not_sq
        (1 : P.inertia (Gal(L/ℚ))) ha hone
  have hres :
      algebraMap (NumberField.RingOfIntegers L) P.ResidueField a =
        algebraMap (NumberField.RingOfIntegers L) P.ResidueField 1 := by
    exact residue_field_sub (I := P) ha_sub_one
  change algebraMap (NumberField.RingOfIntegers L) P.ResidueField a = 1
  simpa only [map_one] using hres

lemma cotangent_generator_scalar
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    {q : ℕ} (hq : Nat.Prime q)
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)]
    (π : NumberField.RingOfIntegers L)
    (hπ_mem : π ∈ P)
    (hπ_not_sq : π ∉ P ^ 2)
    (hπ_spans : ∀ x : NumberField.RingOfIntegers L,
      x ∈ P → ∃ a : NumberField.RingOfIntegers L, x - a * π ∈ P ^ 2)
    (σ τ : P.inertia (Gal(L/ℚ))) :
    field_cotangent_scalar
        (L := L) hq P π hπ_mem hπ_not_sq hπ_spans (σ * τ) -
      field_cotangent_scalar
        (L := L) hq P π hπ_mem hπ_not_sq hπ_spans σ *
      field_cotangent_scalar
        (L := L) hq P π hπ_mem hπ_not_sq hπ_spans τ ∈ P := by
  classical
  let aστ : NumberField.RingOfIntegers L :=
    field_cotangent_scalar
      (L := L) hq P π hπ_mem hπ_not_sq hπ_spans (σ * τ)
  let aσ : NumberField.RingOfIntegers L :=
    field_cotangent_scalar
      (L := L) hq P π hπ_mem hπ_not_sq hπ_spans σ
  let aτ : NumberField.RingOfIntegers L :=
    field_cotangent_scalar
      (L := L) hq P π hπ_mem hπ_not_sq hπ_spans τ
  have hστ :
      (((σ * τ : P.inertia (Gal(L/ℚ))) : Gal(L/ℚ)) • π) -
          aστ * π ∈ P ^ 2 := by
    simpa [aστ] using
      cotangent_scalar_spec
        (L := L) hq P π hπ_mem hπ_not_sq hπ_spans (σ * τ)
  have hσ :
      ((σ : Gal(L/ℚ)) • π) - aσ * π ∈ P ^ 2 := by
    simpa [aσ] using
      cotangent_scalar_spec
        (L := L) hq P π hπ_mem hπ_not_sq hπ_spans σ
  have hτ :
      ((τ : Gal(L/ℚ)) • π) - aτ * π ∈ P ^ 2 := by
    simpa [aτ] using
      cotangent_scalar_spec
        (L := L) hq P π hπ_mem hπ_not_sq hπ_spans τ
  have hτ_smul :
      ((σ : Gal(L/ℚ)) • ((τ : Gal(L/ℚ)) • π)) -
          ((σ : Gal(L/ℚ)) • aτ) * ((σ : Gal(L/ℚ)) • π) ∈ P ^ 2 := by
    have hstable :
        (σ : Gal(L/ℚ)) • (((τ : Gal(L/ℚ)) • π) - aτ * π) ∈ P ^ 2 := by
      exact number_inertia_sq (L := L) P σ hτ
    simpa [smul_sub, smul_mul_assoc] using hstable
  have hσ_scaled :
      ((σ : Gal(L/ℚ)) • aτ) * ((σ : Gal(L/ℚ)) • π) -
          ((σ : Gal(L/ℚ)) • aτ) * (aσ * π) ∈ P ^ 2 := by
    have hmul :
        ((σ : Gal(L/ℚ)) • aτ) *
            (((σ : Gal(L/ℚ)) • π) - aσ * π) ∈ P ^ 2 := by
      exact Ideal.mul_mem_left (P ^ 2) ((σ : Gal(L/ℚ)) • aτ) hσ
    convert hmul using 1
    ring
  have hσaτ_sub_aτ :
      ((σ : Gal(L/ℚ)) • aτ) - aτ ∈ P := by
    exact number_smul_sub (L := L) P σ aτ
  have haσπ_mem : aσ * π ∈ P := by
    exact Ideal.mul_mem_left P aσ hπ_mem
  have hresidue_scaled :
      ((σ : Gal(L/ℚ)) • aτ) * (aσ * π) - aτ * (aσ * π) ∈ P ^ 2 := by
    have hmul :
        (((σ : Gal(L/ℚ)) • aτ) - aτ) * (aσ * π) ∈ P ^ 2 := by
      rw [pow_two]
      exact Ideal.mul_mem_mul hσaτ_sub_aτ haσπ_mem
    convert hmul using 1
    ring
  have hcandidate_raw :
      ((σ : Gal(L/ℚ)) • ((τ : Gal(L/ℚ)) • π)) -
          (aσ * aτ) * π ∈ P ^ 2 := by
    have hsum :
        (((σ : Gal(L/ℚ)) • ((τ : Gal(L/ℚ)) • π)) -
            ((σ : Gal(L/ℚ)) • aτ) * ((σ : Gal(L/ℚ)) • π)) +
          (((σ : Gal(L/ℚ)) • aτ) * ((σ : Gal(L/ℚ)) • π) -
            ((σ : Gal(L/ℚ)) • aτ) * (aσ * π)) +
          (((σ : Gal(L/ℚ)) • aτ) * (aσ * π) -
            aτ * (aσ * π)) ∈ P ^ 2 := by
      exact Ideal.add_mem (P ^ 2)
        (Ideal.add_mem (P ^ 2) hτ_smul hσ_scaled)
        hresidue_scaled
    convert hsum using 1
    ring
  have hcandidate :
      (((σ * τ : P.inertia (Gal(L/ℚ))) : Gal(L/ℚ)) • π) -
          (aσ * aτ) * π ∈ P ^ 2 := by
    simpa [mul_smul] using hcandidate_raw
  have hunique :
      aστ - aσ * aτ ∈ P := by
    exact
      cotangent_scalar_unique
        (L := L) hq P π hπ_mem hπ_not_sq (σ * τ) hστ hcandidate
  simpa [aστ, aσ, aτ] using hunique

lemma number_cotangent_unit
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    {q : ℕ} (hq : Nat.Prime q)
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)]
    (π : NumberField.RingOfIntegers L)
    (hπ_mem : π ∈ P)
    (hπ_not_sq : π ∉ P ^ 2)
    (hπ_spans : ∀ x : NumberField.RingOfIntegers L,
      x ∈ P → ∃ a : NumberField.RingOfIntegers L, x - a * π ∈ P ^ 2)
    (σ τ : P.inertia (Gal(L/ℚ))) :
    number_generator_unit
        (L := L) hq P π hπ_mem hπ_not_sq hπ_spans (σ * τ) =
      number_generator_unit
        (L := L) hq P π hπ_mem hπ_not_sq hπ_spans σ *
      number_generator_unit
        (L := L) hq P π hπ_mem hπ_not_sq hπ_spans τ := by
  classical
  apply Units.ext
  change
    algebraMap (NumberField.RingOfIntegers L) P.ResidueField
        (field_cotangent_scalar
          (L := L) hq P π hπ_mem hπ_not_sq hπ_spans (σ * τ)) =
      algebraMap (NumberField.RingOfIntegers L) P.ResidueField
          (field_cotangent_scalar
            (L := L) hq P π hπ_mem hπ_not_sq hπ_spans σ) *
        algebraMap (NumberField.RingOfIntegers L) P.ResidueField
          (field_cotangent_scalar
            (L := L) hq P π hπ_mem hπ_not_sq hπ_spans τ)
  have hmod :
      field_cotangent_scalar
          (L := L) hq P π hπ_mem hπ_not_sq hπ_spans (σ * τ) -
        field_cotangent_scalar
          (L := L) hq P π hπ_mem hπ_not_sq hπ_spans σ *
        field_cotangent_scalar
          (L := L) hq P π hπ_mem hπ_not_sq hπ_spans τ ∈ P := by
    exact
      cotangent_generator_scalar
        (L := L) hq P π hπ_mem hπ_not_sq hπ_spans σ τ
  have hres :
      algebraMap (NumberField.RingOfIntegers L) P.ResidueField
          (field_cotangent_scalar
            (L := L) hq P π hπ_mem hπ_not_sq hπ_spans (σ * τ)) =
        algebraMap (NumberField.RingOfIntegers L) P.ResidueField
          (field_cotangent_scalar
            (L := L) hq P π hπ_mem hπ_not_sq hπ_spans σ *
            field_cotangent_scalar
              (L := L) hq P π hπ_mem hπ_not_sq hπ_spans τ) := by
    exact residue_field_sub (I := P) hmod
  simpa [map_mul] using hres

noncomputable def number_cotangent_character
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    {q : ℕ} (hq : Nat.Prime q)
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)]
    (π : NumberField.RingOfIntegers L)
    (hπ_mem : π ∈ P)
    (hπ_not_sq : π ∉ P ^ 2)
    (hπ_spans : ∀ x : NumberField.RingOfIntegers L,
      x ∈ P → ∃ a : NumberField.RingOfIntegers L, x - a * π ∈ P ^ 2) :
    P.inertia (Gal(L/ℚ)) →* P.ResidueFieldˣ where
  toFun :=
    number_generator_unit
      (L := L) hq P π hπ_mem hπ_not_sq hπ_spans
  map_one' :=
    cotangent_generator_unit
      (L := L) hq P π hπ_mem hπ_not_sq hπ_spans
  map_mul' := by
    intro σ τ
    exact
      number_cotangent_unit
        (L := L) hq P π hπ_mem hπ_not_sq hπ_spans σ τ

lemma cotangent_scalar_sub
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    {q : ℕ} (hq : Nat.Prime q)
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)]
    (π : NumberField.RingOfIntegers L)
    (hπ_mem : π ∈ P)
    (hπ_not_sq : π ∉ P ^ 2)
    (hπ_spans : ∀ x : NumberField.RingOfIntegers L,
      x ∈ P → ∃ a : NumberField.RingOfIntegers L, x - a * π ∈ P ^ 2)
    (σ : P.inertia (Gal(L/ℚ))) :
    number_generator_unit
        (L := L) hq P π hπ_mem hπ_not_sq hπ_spans σ = 1 ↔
      field_cotangent_scalar
        (L := L) hq P π hπ_mem hπ_not_sq hπ_spans σ - 1 ∈ P := by
  classical
  constructor
  · intro hunit
    have hval :
        (number_generator_unit
            (L := L) hq P π hπ_mem hπ_not_sq hπ_spans σ :
          P.ResidueField) = 1 := by
      simpa using congrArg (fun u : P.ResidueFieldˣ => (u : P.ResidueField)) hunit
    change
      algebraMap (NumberField.RingOfIntegers L) P.ResidueField
        (field_cotangent_scalar
          (L := L) hq P π hπ_mem hπ_not_sq hπ_spans σ) = 1 at hval
    have hzero :
        algebraMap (NumberField.RingOfIntegers L) P.ResidueField
          (field_cotangent_scalar
            (L := L) hq P π hπ_mem hπ_not_sq hπ_spans σ - 1) = 0 := by
      rw [map_sub, map_one, hval, sub_self]
    exact (Ideal.algebraMap_residueField_eq_zero (I := P)).1 hzero
  · intro hscalar
    apply Units.ext
    change
      algebraMap (NumberField.RingOfIntegers L) P.ResidueField
          (field_cotangent_scalar
            (L := L) hq P π hπ_mem hπ_not_sq hπ_spans σ) = 1
    have hres :
        algebraMap (NumberField.RingOfIntegers L) P.ResidueField
            (field_cotangent_scalar
              (L := L) hq P π hπ_mem hπ_not_sq hπ_spans σ) =
          algebraMap (NumberField.RingOfIntegers L) P.ResidueField 1 := by
      exact residue_field_sub (I := P) hscalar
    simpa only [map_one] using hres

lemma number_cotangent_ker
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    {q : ℕ} (hq : Nat.Prime q)
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)]
    (π : NumberField.RingOfIntegers L)
    (hπ_mem : π ∈ P)
    (hπ_not_sq : π ∉ P ^ 2)
    (hπ_spans : ∀ x : NumberField.RingOfIntegers L,
      x ∈ P → ∃ a : NumberField.RingOfIntegers L, x - a * π ∈ P ^ 2)
    (σ : P.inertia (Gal(L/ℚ))) :
    σ ∈ (number_cotangent_character
        (L := L) hq P π hπ_mem hπ_not_sq hπ_spans).ker ↔
      field_cotangent_scalar
        (L := L) hq P π hπ_mem hπ_not_sq hπ_spans σ - 1 ∈ P := by
  classical
  rw [MonoidHom.mem_ker]
  exact
    cotangent_scalar_sub
      (L := L) hq P π hπ_mem hπ_not_sq hπ_spans σ

lemma cotangent_scalar_sq
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    {q : ℕ} (hq : Nat.Prime q)
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)]
    (π : NumberField.RingOfIntegers L)
    (hπ_mem : π ∈ P)
    (hπ_not_sq : π ∉ P ^ 2)
    (hπ_spans : ∀ x : NumberField.RingOfIntegers L,
      x ∈ P → ∃ a : NumberField.RingOfIntegers L, x - a * π ∈ P ^ 2)
    (σ : P.inertia (Gal(L/ℚ))) :
    field_cotangent_scalar
        (L := L) hq P π hπ_mem hπ_not_sq hπ_spans σ - 1 ∈ P ↔
      ((σ : Gal(L/ℚ)) • π) - π ∈ P ^ 2 := by
  classical
  let a : NumberField.RingOfIntegers L :=
    field_cotangent_scalar
      (L := L) hq P π hπ_mem hπ_not_sq hπ_spans σ
  have ha :
      ((σ : Gal(L/ℚ)) • π) - a * π ∈ P ^ 2 := by
    simpa [a] using
      cotangent_scalar_spec
        (L := L) hq P π hπ_mem hπ_not_sq hπ_spans σ
  constructor
  · intro hscalar
    have hscalar' : a - 1 ∈ P := by
      simpa [a] using hscalar
    have hmul : (a - 1) * π ∈ P ^ 2 := by
      rw [pow_two]
      exact Ideal.mul_mem_mul hscalar' hπ_mem
    have hsum :
        (((σ : Gal(L/ℚ)) • π) - a * π) + (a - 1) * π ∈ P ^ 2 := by
      exact Ideal.add_mem (P ^ 2) ha hmul
    convert hsum using 1
    ring
  · intro hfixed
    have hone :
        ((σ : Gal(L/ℚ)) • π) - 1 * π ∈ P ^ 2 := by
      simpa using hfixed
    have hscalar' : a - 1 ∈ P := by
      exact
        cotangent_scalar_unique
          (L := L) hq P π hπ_mem hπ_not_sq σ ha hone
    simpa [a] using hscalar'

lemma sq_square_ker
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (P : Ideal (NumberField.RingOfIntegers L))
    (π : NumberField.RingOfIntegers L)
    (σ : P.inertia (Gal(L/ℚ)))
    (hσ : σ ∈ (number_square_representation (L := L) P).ker) :
    ((σ : Gal(L/ℚ)) • π) - π ∈ P ^ 2 := by
  classical
  rw [MonoidHom.mem_ker] at hσ
  have happly :=
    congrArg
      (fun e : (NumberField.RingOfIntegers L ⧸ P ^ 2) ≃+*
          (NumberField.RingOfIntegers L ⧸ P ^ 2) =>
        e (Ideal.Quotient.mk (P ^ 2) π)) hσ
  have hfixed :
      number_square_representation (L := L) P σ
          (Ideal.Quotient.mk (P ^ 2) π) =
        Ideal.Quotient.mk (P ^ 2) π := by
    simpa using happly
  have hquot :
      Ideal.Quotient.mk (P ^ 2) ((σ : Gal(L/ℚ)) • π) =
        Ideal.Quotient.mk (P ^ 2) π := by
    calc
      Ideal.Quotient.mk (P ^ 2) ((σ : Gal(L/ℚ)) • π) =
          number_square_representation (L := L) P σ
            (Ideal.Quotient.mk (P ^ 2) π) := by
        exact
          (square_representation_mk
            (L := L) P σ π).symm
      _ = Ideal.Quotient.mk (P ^ 2) π := hfixed
  exact (ideal_quotient_sub (P ^ 2)).1 hquot

lemma number_sq_fixed
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    {q : ℕ} (_hq : Nat.Prime q)
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)]
    (π : NumberField.RingOfIntegers L)
    (hπ_mem : π ∈ P)
    (_hπ_not_sq : π ∉ P ^ 2)
    (hπ_spans : ∀ x : NumberField.RingOfIntegers L,
      x ∈ P → ∃ a : NumberField.RingOfIntegers L, x - a * π ∈ P ^ 2)
    (σ : P.inertia (Gal(L/ℚ)))
    (hπ_fixed : ((σ : Gal(L/ℚ)) • π) - π ∈ P ^ 2)
    {x : NumberField.RingOfIntegers L}
    (hx : x ∈ P) :
    ((σ : Gal(L/ℚ)) • x) - x ∈ P ^ 2 := by
  classical
  obtain ⟨b, hb⟩ := hπ_spans x hx
  have hstable :
      (σ : Gal(L/ℚ)) • (x - b * π) ∈ P ^ 2 := by
    exact number_inertia_sq (L := L) P σ hb
  have herror_fixed :
      ((σ : Gal(L/ℚ)) • (x - b * π)) - (x - b * π) ∈ P ^ 2 := by
    have hneg : - (x - b * π) ∈ P ^ 2 := by
      exact (P ^ 2).neg_mem hb
    simpa [sub_eq_add_neg] using Ideal.add_mem (P ^ 2) hstable hneg
  have hcoef_sub :
      ((σ : Gal(L/ℚ)) • b) - b ∈ P := by
    exact number_smul_sub (L := L) P σ b
  have hterm_generator :
      ((σ : Gal(L/ℚ)) • b) * (((σ : Gal(L/ℚ)) • π) - π) ∈ P ^ 2 := by
    exact Ideal.mul_mem_left (P ^ 2) ((σ : Gal(L/ℚ)) • b) hπ_fixed
  have hterm_coeff :
      (((σ : Gal(L/ℚ)) • b) - b) * π ∈ P ^ 2 := by
    rw [pow_two]
    exact Ideal.mul_mem_mul hcoef_sub hπ_mem
  have hproduct_fixed :
      ((σ : Gal(L/ℚ)) • (b * π)) - b * π ∈ P ^ 2 := by
    have hsum :
        ((σ : Gal(L/ℚ)) • b) * (((σ : Gal(L/ℚ)) • π) - π) +
          (((σ : Gal(L/ℚ)) • b) - b) * π ∈ P ^ 2 := by
      exact Ideal.add_mem (P ^ 2) hterm_generator hterm_coeff
    convert hsum using 1
    rw [smul_mul']
    ring
  have htotal :
      (((σ : Gal(L/ℚ)) • (x - b * π)) - (x - b * π)) +
        (((σ : Gal(L/ℚ)) • (b * π)) - b * π) ∈ P ^ 2 := by
    exact Ideal.add_mem (P ^ 2) herror_fixed hproduct_fixed
  convert htotal using 1
  rw [smul_sub]
  ring

lemma field_displacement_scalar
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    {q : ℕ} (_hq : Nat.Prime q)
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)]
    (π : NumberField.RingOfIntegers L)
    (_hπ_mem : π ∈ P)
    (_hπ_not_sq : π ∉ P ^ 2)
    (hπ_spans : ∀ x : NumberField.RingOfIntegers L,
      x ∈ P → ∃ a : NumberField.RingOfIntegers L, x - a * π ∈ P ^ 2)
    (σ : P.inertia (Gal(L/ℚ)))
    (x : NumberField.RingOfIntegers L) :
    ∃ a : NumberField.RingOfIntegers L,
      (((σ : Gal(L/ℚ)) • x) - x) - a * π ∈ P ^ 2 := by
  classical
  have hdiff_mem :
      ((σ : Gal(L/ℚ)) • x) - x ∈ P := by
    exact number_smul_sub (L := L) P σ x
  exact hπ_spans (((σ : Gal(L/ℚ)) • x) - x) hdiff_mem

lemma displacement_scalar_unique
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    {q : ℕ} (hq : Nat.Prime q)
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)]
    (π : NumberField.RingOfIntegers L)
    (hπ_mem : π ∈ P)
    (hπ_not_sq : π ∉ P ^ 2)
    (σ : P.inertia (Gal(L/ℚ)))
    (x : NumberField.RingOfIntegers L)
    {a b : NumberField.RingOfIntegers L}
    (ha : (((σ : Gal(L/ℚ)) • x) - x) - a * π ∈ P ^ 2)
    (hb : (((σ : Gal(L/ℚ)) • x) - x) - b * π ∈ P ^ 2) :
    a - b ∈ P := by
  classical
  letI : P.IsMaximal :=
    number_above_maximal (L := L) hq P
  exact
    cotangent_unique_ideal
      P hπ_mem hπ_not_sq ha hb

noncomputable def number_order_displacement
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    {q : ℕ} (hq : Nat.Prime q)
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)]
    (π : NumberField.RingOfIntegers L)
    (hπ_mem : π ∈ P)
    (hπ_not_sq : π ∉ P ^ 2)
    (hπ_spans : ∀ x : NumberField.RingOfIntegers L,
      x ∈ P → ∃ a : NumberField.RingOfIntegers L, x - a * π ∈ P ^ 2)
    (σ : P.inertia (Gal(L/ℚ)))
    (x : NumberField.RingOfIntegers L) :
    NumberField.RingOfIntegers L :=
  Classical.choose
    (field_displacement_scalar
      (L := L) hq P π hπ_mem hπ_not_sq hπ_spans σ x)

lemma number_displacement_spec
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    {q : ℕ} (hq : Nat.Prime q)
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)]
    (π : NumberField.RingOfIntegers L)
    (hπ_mem : π ∈ P)
    (hπ_not_sq : π ∉ P ^ 2)
    (hπ_spans : ∀ x : NumberField.RingOfIntegers L,
      x ∈ P → ∃ a : NumberField.RingOfIntegers L, x - a * π ∈ P ^ 2)
    (σ : P.inertia (Gal(L/ℚ)))
    (x : NumberField.RingOfIntegers L) :
    (((σ : Gal(L/ℚ)) • x) - x) -
        number_order_displacement
          (L := L) hq P π hπ_mem hπ_not_sq hπ_spans σ x * π ∈ P ^ 2 := by
  classical
  exact
    Classical.choose_spec
      (field_displacement_scalar
        (L := L) hq P π hπ_mem hπ_not_sq hπ_spans σ x)

lemma displacement_scalar_mod
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    {q : ℕ} (hq : Nat.Prime q)
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)]
    (π : NumberField.RingOfIntegers L)
    (hπ_mem : π ∈ P)
    (hπ_not_sq : π ∉ P ^ 2)
    (hπ_spans : ∀ x : NumberField.RingOfIntegers L,
      x ∈ P → ∃ a : NumberField.RingOfIntegers L, x - a * π ∈ P ^ 2)
    (σ : P.inertia (Gal(L/ℚ)))
    (x y : NumberField.RingOfIntegers L) :
    number_order_displacement
        (L := L) hq P π hπ_mem hπ_not_sq hπ_spans σ (x + y) -
      (number_order_displacement
          (L := L) hq P π hπ_mem hπ_not_sq hπ_spans σ x +
        number_order_displacement
          (L := L) hq P π hπ_mem hπ_not_sq hπ_spans σ y) ∈ P := by
  classical
  let ax : NumberField.RingOfIntegers L :=
    number_order_displacement
      (L := L) hq P π hπ_mem hπ_not_sq hπ_spans σ x
  let ay : NumberField.RingOfIntegers L :=
    number_order_displacement
      (L := L) hq P π hπ_mem hπ_not_sq hπ_spans σ y
  let axy : NumberField.RingOfIntegers L :=
    number_order_displacement
      (L := L) hq P π hπ_mem hπ_not_sq hπ_spans σ (x + y)
  have hx :
      (((σ : Gal(L/ℚ)) • x) - x) - ax * π ∈ P ^ 2 := by
    simpa [ax] using
      number_displacement_spec
        (L := L) hq P π hπ_mem hπ_not_sq hπ_spans σ x
  have hy :
      (((σ : Gal(L/ℚ)) • y) - y) - ay * π ∈ P ^ 2 := by
    simpa [ay] using
      number_displacement_spec
        (L := L) hq P π hπ_mem hπ_not_sq hπ_spans σ y
  have hxy :
      (((σ : Gal(L/ℚ)) • (x + y)) - (x + y)) - axy * π ∈ P ^ 2 := by
    simpa [axy] using
      number_displacement_spec
        (L := L) hq P π hπ_mem hπ_not_sq hπ_spans σ (x + y)
  have hcandidate :
      (((σ : Gal(L/ℚ)) • (x + y)) - (x + y)) - (ax + ay) * π ∈ P ^ 2 := by
    have hsum :
        ((((σ : Gal(L/ℚ)) • x) - x) - ax * π) +
          ((((σ : Gal(L/ℚ)) • y) - y) - ay * π) ∈ P ^ 2 := by
      exact Ideal.add_mem (P ^ 2) hx hy
    convert hsum using 1
    rw [smul_add]
    ring
  have huniq :
      axy - (ax + ay) ∈ P := by
    exact
      displacement_scalar_unique
        (L := L) hq P π hπ_mem hπ_not_sq σ (x + y) hxy hcandidate
  simpa [axy, ax, ay] using huniq

lemma order_displacement_scalar
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    {q : ℕ} (hq : Nat.Prime q)
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)]
    (π : NumberField.RingOfIntegers L)
    (hπ_mem : π ∈ P)
    (hπ_not_sq : π ∉ P ^ 2)
    (hπ_spans : ∀ x : NumberField.RingOfIntegers L,
      x ∈ P → ∃ a : NumberField.RingOfIntegers L, x - a * π ∈ P ^ 2)
    (σ : P.inertia (Gal(L/ℚ)))
    (x y : NumberField.RingOfIntegers L) :
    number_order_displacement
        (L := L) hq P π hπ_mem hπ_not_sq hπ_spans σ (x * y) -
      (x * number_order_displacement
          (L := L) hq P π hπ_mem hπ_not_sq hπ_spans σ y +
        y * number_order_displacement
          (L := L) hq P π hπ_mem hπ_not_sq hπ_spans σ x) ∈ P := by
  classical
  let ax : NumberField.RingOfIntegers L :=
    number_order_displacement
      (L := L) hq P π hπ_mem hπ_not_sq hπ_spans σ x
  let ay : NumberField.RingOfIntegers L :=
    number_order_displacement
      (L := L) hq P π hπ_mem hπ_not_sq hπ_spans σ y
  let axy : NumberField.RingOfIntegers L :=
    number_order_displacement
      (L := L) hq P π hπ_mem hπ_not_sq hπ_spans σ (x * y)
  have hx :
      (((σ : Gal(L/ℚ)) • x) - x) - ax * π ∈ P ^ 2 := by
    simpa [ax] using
      number_displacement_spec
        (L := L) hq P π hπ_mem hπ_not_sq hπ_spans σ x
  have hy :
      (((σ : Gal(L/ℚ)) • y) - y) - ay * π ∈ P ^ 2 := by
    simpa [ay] using
      number_displacement_spec
        (L := L) hq P π hπ_mem hπ_not_sq hπ_spans σ y
  have hxy :
      (((σ : Gal(L/ℚ)) • (x * y)) - (x * y)) - axy * π ∈ P ^ 2 := by
    simpa [axy] using
      number_displacement_spec
        (L := L) hq P π hπ_mem hπ_not_sq hπ_spans σ (x * y)
  have hdelta_x_mem :
      ((σ : Gal(L/ℚ)) • x) - x ∈ P := by
    exact number_smul_sub (L := L) P σ x
  have hayπ_mem : ay * π ∈ P := by
    exact Ideal.mul_mem_left P ay hπ_mem
  have hterm_y :
      ((σ : Gal(L/ℚ)) • x) * (((σ : Gal(L/ℚ)) • y - y) - ay * π) ∈ P ^ 2 := by
    exact Ideal.mul_mem_left (P ^ 2) ((σ : Gal(L/ℚ)) • x) hy
  have hterm_residue :
      (((σ : Gal(L/ℚ)) • x) - x) * (ay * π) ∈ P ^ 2 := by
    rw [pow_two]
    exact Ideal.mul_mem_mul hdelta_x_mem hayπ_mem
  have hterm_x :
      y * ((((σ : Gal(L/ℚ)) • x) - x) - ax * π) ∈ P ^ 2 := by
    exact Ideal.mul_mem_left (P ^ 2) y hx
  have hcandidate :
      (((σ : Gal(L/ℚ)) • (x * y)) - (x * y)) - (x * ay + y * ax) * π ∈ P ^ 2 := by
    have hsum :
        ((σ : Gal(L/ℚ)) • x) * (((σ : Gal(L/ℚ)) • y - y) - ay * π) +
          (((σ : Gal(L/ℚ)) • x - x) * (ay * π)) +
          y * ((((σ : Gal(L/ℚ)) • x) - x) - ax * π) ∈ P ^ 2 := by
      exact Ideal.add_mem (P ^ 2)
        (Ideal.add_mem (P ^ 2) hterm_y hterm_residue)
        hterm_x
    convert hsum using 1
    rw [smul_mul']
    ring
  have huniq :
      axy - (x * ay + y * ax) ∈ P := by
    exact
      displacement_scalar_unique
        (L := L) hq P π hπ_mem hπ_not_sq σ (x * y) hxy hcandidate
  simpa [axy, ax, ay] using huniq

lemma number_displacement_scalar
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    {q : ℕ} (hq : Nat.Prime q)
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)]
    (π : NumberField.RingOfIntegers L)
    (hπ_mem : π ∈ P)
    (hπ_not_sq : π ∉ P ^ 2)
    (hπ_spans : ∀ x : NumberField.RingOfIntegers L,
      x ∈ P → ∃ a : NumberField.RingOfIntegers L, x - a * π ∈ P ^ 2)
    (σ : P.inertia (Gal(L/ℚ)))
    (hπ_fixed : ((σ : Gal(L/ℚ)) • π) - π ∈ P ^ 2)
    {x y : NumberField.RingOfIntegers L}
    (hxy : x - y ∈ P) :
    number_order_displacement
        (L := L) hq P π hπ_mem hπ_not_sq hπ_spans σ x -
      number_order_displacement
        (L := L) hq P π hπ_mem hπ_not_sq hπ_spans σ y ∈ P := by
  classical
  let ax : NumberField.RingOfIntegers L :=
    number_order_displacement
      (L := L) hq P π hπ_mem hπ_not_sq hπ_spans σ x
  let ay : NumberField.RingOfIntegers L :=
    number_order_displacement
      (L := L) hq P π hπ_mem hπ_not_sq hπ_spans σ y
  have hx :
      (((σ : Gal(L/ℚ)) • x) - x) - ax * π ∈ P ^ 2 := by
    simpa [ax] using
      number_displacement_spec
        (L := L) hq P π hπ_mem hπ_not_sq hπ_spans σ x
  have hy :
      (((σ : Gal(L/ℚ)) • y) - y) - ay * π ∈ P ^ 2 := by
    simpa [ay] using
      number_displacement_spec
        (L := L) hq P π hπ_mem hπ_not_sq hπ_spans σ y
  have hfixed_diff :
      ((σ : Gal(L/ℚ)) • (x - y)) - (x - y) ∈ P ^ 2 := by
    exact
      number_sq_fixed
        (L := L) hq P π hπ_mem hπ_not_sq hπ_spans σ hπ_fixed hxy
  have hcandidate :
      ((σ : Gal(L/ℚ)) • (x - y)) - (x - y) - (ax - ay) * π ∈ P ^ 2 := by
    have hsub :
        ((((σ : Gal(L/ℚ)) • x) - x) - ax * π) -
          ((((σ : Gal(L/ℚ)) • y) - y) - ay * π) ∈ P ^ 2 := by
      exact Ideal.sub_mem (P ^ 2) hx hy
    convert hsub using 1
    rw [smul_sub]
    ring
  have hzero :
      ((σ : Gal(L/ℚ)) • (x - y)) - (x - y) - 0 * π ∈ P ^ 2 := by
    simpa using hfixed_diff
  have huniq :
      (ax - ay) - 0 ∈ P := by
    exact
      displacement_scalar_unique
        (L := L) hq P π hπ_mem hπ_not_sq σ (x - y) hcandidate hzero
  simpa [ax, ay] using huniq

lemma displacement_scalar_sub
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    {q : ℕ} (hq : Nat.Prime q)
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)]
    (π : NumberField.RingOfIntegers L)
    (hπ_mem : π ∈ P)
    (hπ_not_sq : π ∉ P ^ 2)
    (hπ_spans : ∀ x : NumberField.RingOfIntegers L,
      x ∈ P → ∃ a : NumberField.RingOfIntegers L, x - a * π ∈ P ^ 2)
    (σ : P.inertia (Gal(L/ℚ)))
    (hπ_fixed : ((σ : Gal(L/ℚ)) • π) - π ∈ P ^ 2)
    {x y : NumberField.RingOfIntegers L}
    (hxy : x - y ∈ P) :
    algebraMap (NumberField.RingOfIntegers L) P.ResidueField
        (number_order_displacement
          (L := L) hq P π hπ_mem hπ_not_sq hπ_spans σ x) =
      algebraMap (NumberField.RingOfIntegers L) P.ResidueField
        (number_order_displacement
          (L := L) hq P π hπ_mem hπ_not_sq hπ_spans σ y) := by
  classical
  have hcoeff :
      number_order_displacement
          (L := L) hq P π hπ_mem hπ_not_sq hπ_spans σ x -
        number_order_displacement
          (L := L) hq P π hπ_mem hπ_not_sq hπ_spans σ y ∈ P := by
    exact
      number_displacement_scalar
        (L := L) hq P π hπ_mem hπ_not_sq hπ_spans σ hπ_fixed hxy
  exact residue_field_sub (I := P) hcoeff

lemma displacement_scalar_add
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    {q : ℕ} (hq : Nat.Prime q)
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)]
    (π : NumberField.RingOfIntegers L)
    (hπ_mem : π ∈ P)
    (hπ_not_sq : π ∉ P ^ 2)
    (hπ_spans : ∀ x : NumberField.RingOfIntegers L,
      x ∈ P → ∃ a : NumberField.RingOfIntegers L, x - a * π ∈ P ^ 2)
    (σ : P.inertia (Gal(L/ℚ)))
    (x y : NumberField.RingOfIntegers L) :
    algebraMap (NumberField.RingOfIntegers L) P.ResidueField
        (number_order_displacement
          (L := L) hq P π hπ_mem hπ_not_sq hπ_spans σ (x + y)) =
      algebraMap (NumberField.RingOfIntegers L) P.ResidueField
          (number_order_displacement
            (L := L) hq P π hπ_mem hπ_not_sq hπ_spans σ x) +
        algebraMap (NumberField.RingOfIntegers L) P.ResidueField
          (number_order_displacement
            (L := L) hq P π hπ_mem hπ_not_sq hπ_spans σ y) := by
  classical
  have hcoeff :
      number_order_displacement
          (L := L) hq P π hπ_mem hπ_not_sq hπ_spans σ (x + y) -
        (number_order_displacement
            (L := L) hq P π hπ_mem hπ_not_sq hπ_spans σ x +
          number_order_displacement
            (L := L) hq P π hπ_mem hπ_not_sq hπ_spans σ y) ∈ P := by
    exact
      displacement_scalar_mod
        (L := L) hq P π hπ_mem hπ_not_sq hπ_spans σ x y
  have hres :=
    residue_field_sub (I := P) hcoeff
  simpa [map_add] using hres

lemma displacement_scalar_mul
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    {q : ℕ} (hq : Nat.Prime q)
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)]
    (π : NumberField.RingOfIntegers L)
    (hπ_mem : π ∈ P)
    (hπ_not_sq : π ∉ P ^ 2)
    (hπ_spans : ∀ x : NumberField.RingOfIntegers L,
      x ∈ P → ∃ a : NumberField.RingOfIntegers L, x - a * π ∈ P ^ 2)
    (σ : P.inertia (Gal(L/ℚ)))
    (x y : NumberField.RingOfIntegers L) :
    algebraMap (NumberField.RingOfIntegers L) P.ResidueField
        (number_order_displacement
          (L := L) hq P π hπ_mem hπ_not_sq hπ_spans σ (x * y)) =
      algebraMap (NumberField.RingOfIntegers L) P.ResidueField x *
          algebraMap (NumberField.RingOfIntegers L) P.ResidueField
            (number_order_displacement
              (L := L) hq P π hπ_mem hπ_not_sq hπ_spans σ y) +
        algebraMap (NumberField.RingOfIntegers L) P.ResidueField y *
          algebraMap (NumberField.RingOfIntegers L) P.ResidueField
            (number_order_displacement
              (L := L) hq P π hπ_mem hπ_not_sq hπ_spans σ x) := by
  classical
  have hcoeff :
      number_order_displacement
          (L := L) hq P π hπ_mem hπ_not_sq hπ_spans σ (x * y) -
        (x * number_order_displacement
            (L := L) hq P π hπ_mem hπ_not_sq hπ_spans σ y +
          y * number_order_displacement
            (L := L) hq P π hπ_mem hπ_not_sq hπ_spans σ x) ∈ P := by
    exact
      order_displacement_scalar
        (L := L) hq P π hπ_mem hπ_not_sq hπ_spans σ x y
  have hres :=
    residue_field_sub (I := P) hcoeff
  simpa [map_add, map_mul] using hres

lemma displacement_scalar_residue
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    {q : ℕ} (hq : Nat.Prime q)
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)]
    (π : NumberField.RingOfIntegers L)
    (hπ_mem : π ∈ P)
    (hπ_not_sq : π ∉ P ^ 2)
    (hπ_spans : ∀ x : NumberField.RingOfIntegers L,
      x ∈ P → ∃ a : NumberField.RingOfIntegers L, x - a * π ∈ P ^ 2)
    (σ : P.inertia (Gal(L/ℚ)))
    (hπ_fixed : ((σ : Gal(L/ℚ)) • π) - π ∈ P ^ 2)
    {x : NumberField.RingOfIntegers L}
    (hx : x ∈ P) :
    algebraMap (NumberField.RingOfIntegers L) P.ResidueField
        (number_order_displacement
          (L := L) hq P π hπ_mem hπ_not_sq hπ_spans σ x) = 0 := by
  classical
  have hspec :
      (((σ : Gal(L/ℚ)) • x) - x) -
          number_order_displacement
            (L := L) hq P π hπ_mem hπ_not_sq hπ_spans σ x * π ∈ P ^ 2 := by
    exact
      number_displacement_spec
        (L := L) hq P π hπ_mem hπ_not_sq hπ_spans σ x
  have hzero :
      (((σ : Gal(L/ℚ)) • x) - x) - 0 * π ∈ P ^ 2 := by
    simpa using
      number_sq_fixed
        (L := L) hq P π hπ_mem hπ_not_sq hπ_spans σ hπ_fixed hx
  have hcoeff_mem :
      number_order_displacement
        (L := L) hq P π hπ_mem hπ_not_sq hπ_spans σ x ∈ P := by
    have hdiff :
        number_order_displacement
          (L := L) hq P π hπ_mem hπ_not_sq hπ_spans σ x - 0 ∈ P := by
      exact
        displacement_scalar_unique
          (L := L) hq P π hπ_mem hπ_not_sq σ x hspec hzero
    simpa using hdiff
  exact (Ideal.algebraMap_residueField_eq_zero (I := P)).2 hcoeff_mem

lemma first_displacement_scalar
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    {q : ℕ} (hq : Nat.Prime q)
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)]
    (π : NumberField.RingOfIntegers L)
    (hπ_mem : π ∈ P)
    (hπ_not_sq : π ∉ P ^ 2)
    (hπ_spans : ∀ x : NumberField.RingOfIntegers L,
      x ∈ P → ∃ a : NumberField.RingOfIntegers L, x - a * π ∈ P ^ 2)
    (σ : P.inertia (Gal(L/ℚ))) :
    number_order_displacement
      (L := L) hq P π hπ_mem hπ_not_sq hπ_spans σ 1 ∈ P := by
  classical
  have hone :
      (((σ : Gal(L/ℚ)) • (1 : NumberField.RingOfIntegers L)) - 1) -
          number_order_displacement
            (L := L) hq P π hπ_mem hπ_not_sq hπ_spans σ 1 * π ∈ P ^ 2 := by
    exact
      number_displacement_spec
        (L := L) hq P π hπ_mem hπ_not_sq hπ_spans σ 1
  have hzero :
      (((σ : Gal(L/ℚ)) • (1 : NumberField.RingOfIntegers L)) - 1) -
          0 * π ∈ P ^ 2 := by
    simp
  have hdiff :
      number_order_displacement
        (L := L) hq P π hπ_mem hπ_not_sq hπ_spans σ 1 - 0 ∈ P := by
    exact
      displacement_scalar_unique
        (L := L) hq P π hπ_mem hπ_not_sq σ 1 hone hzero
  simpa using hdiff

lemma number_displacement_residue
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    {q : ℕ} (hq : Nat.Prime q)
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)]
    (π : NumberField.RingOfIntegers L)
    (hπ_mem : π ∈ P)
    (hπ_not_sq : π ∉ P ^ 2)
    (hπ_spans : ∀ x : NumberField.RingOfIntegers L,
      x ∈ P → ∃ a : NumberField.RingOfIntegers L, x - a * π ∈ P ^ 2)
    (σ : P.inertia (Gal(L/ℚ))) :
    algebraMap (NumberField.RingOfIntegers L) P.ResidueField
        (number_order_displacement
          (L := L) hq P π hπ_mem hπ_not_sq hπ_spans σ 1) = 0 := by
  classical
  have hone_mem :
      number_order_displacement
        (L := L) hq P π hπ_mem hπ_not_sq hπ_spans σ 1 ∈ P := by
    exact
      first_displacement_scalar
        (L := L) hq P π hπ_mem hπ_not_sq hπ_spans σ
  exact (Ideal.algebraMap_residueField_eq_zero (I := P)).2 hone_mem

lemma sq_displacement_scalar
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    {q : ℕ} (hq : Nat.Prime q)
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)]
    (π : NumberField.RingOfIntegers L)
    (hπ_mem : π ∈ P)
    (hπ_not_sq : π ∉ P ^ 2)
    (hπ_spans : ∀ x : NumberField.RingOfIntegers L,
      x ∈ P → ∃ a : NumberField.RingOfIntegers L, x - a * π ∈ P ^ 2)
    (σ : P.inertia (Gal(L/ℚ)))
    (x : NumberField.RingOfIntegers L)
    (hcoeff : number_order_displacement
      (L := L) hq P π hπ_mem hπ_not_sq hπ_spans σ x ∈ P) :
    ((σ : Gal(L/ℚ)) • x) - x ∈ P ^ 2 := by
  classical
  have hspec :
      (((σ : Gal(L/ℚ)) • x) - x) -
          number_order_displacement
            (L := L) hq P π hπ_mem hπ_not_sq hπ_spans σ x * π ∈ P ^ 2 := by
    exact
      number_displacement_spec
        (L := L) hq P π hπ_mem hπ_not_sq hπ_spans σ x
  have hprod :
      number_order_displacement
          (L := L) hq P π hπ_mem hπ_not_sq hπ_spans σ x * π ∈ P ^ 2 := by
    rw [pow_two]
    exact Ideal.mul_mem_mul hcoeff hπ_mem
  have hsum :
      ((((σ : Gal(L/ℚ)) • x) - x) -
          number_order_displacement
            (L := L) hq P π hπ_mem hπ_not_sq hπ_spans σ x * π) +
        number_order_displacement
          (L := L) hq P π hπ_mem hπ_not_sq hπ_spans σ x * π ∈ P ^ 2 := by
    exact Ideal.add_mem (P ^ 2) hspec hprod
  convert hsum using 1
  ring

lemma derivation_like_succ
    {K : Type*} [Field K]
    (D : K → K)
    (hMul : ∀ x y : K, D (x * y) = x * D y + y * D x)
    (x : K) :
    ∀ n : ℕ, D (x ^ (n + 1)) = (n + 1 : K) * x ^ n * D x := by
  intro n
  induction n with
  | zero =>
      simp
  | succ n ih =>
      calc
        D (x ^ (n + 1 + 1)) = D (x ^ (n + 1) * x) := by
          rw [pow_succ]
        _ = x ^ (n + 1) * D x + x * D (x ^ (n + 1)) := by
          rw [hMul]
        _ = x ^ (n + 1) * D x + x * ((n + 1 : K) * x ^ n * D x) := by
          rw [ih]
        _ = (((n + 1 : ℕ) : K) + 1) * x ^ (n + 1) * D x := by
          have hcast : ((n + 1 : ℕ) : K) = (n : K) + 1 := by
            rw [Nat.cast_add, Nat.cast_one]
          rw [hcast]
          ring

lemma derivation_like_zero
    {K : Type*} [Field K] [Finite K]
    (D : K → K)
    (hMul : ∀ x y : K, D (x * y) = x * D y + y * D x) :
    ∀ x : K, D x = 0 := by
  classical
  letI : Fintype K := Fintype.ofFinite K
  intro x
  obtain ⟨n, hn⟩ :=
    Nat.exists_eq_succ_of_ne_zero
      (show Fintype.card K ≠ 0 by exact Fintype.card_ne_zero)
  have hpow_formula :
      D (x ^ Fintype.card K) =
        (Fintype.card K : K) * x ^ (Fintype.card K - 1) * D x := by
    have h := derivation_like_succ D hMul x n
    simpa [hn] using h
  have hcard_cast : (Fintype.card K : K) = 0 := by
    have hsmul : Fintype.card K • (1 : K) = 0 := by
      exact card_nsmul_eq_zero
    simpa only [nsmul_eq_mul, mul_one] using hsmul
  have hleft : D (x ^ Fintype.card K) = D x := by
    rw [FiniteField.pow_card]
  calc
    D x = D (x ^ Fintype.card K) := hleft.symm
    _ = (Fintype.card K : K) * x ^ (Fintype.card K - 1) * D x := hpow_formula
    _ = 0 := by
      simp [hcard_cast]

lemma displacement_derivation_like
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    {q : ℕ} (hq : Nat.Prime q)
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)]
    (π : NumberField.RingOfIntegers L)
    (hπ_mem : π ∈ P)
    (hπ_not_sq : π ∉ P ^ 2)
    (hπ_spans : ∀ x : NumberField.RingOfIntegers L,
      x ∈ P → ∃ a : NumberField.RingOfIntegers L, x - a * π ∈ P ^ 2)
    (σ : P.inertia (Gal(L/ℚ)))
    (D : P.ResidueField → P.ResidueField)
    (hD_rep : ∀ x : NumberField.RingOfIntegers L,
      D (algebraMap (NumberField.RingOfIntegers L) P.ResidueField x) =
        algebraMap (NumberField.RingOfIntegers L) P.ResidueField
          (number_order_displacement
            (L := L) hq P π hπ_mem hπ_not_sq hπ_spans σ x))
    (hD_mul : ∀ u v : P.ResidueField,
      D (u * v) = u * D v + v * D u)
    (x : NumberField.RingOfIntegers L) :
    algebraMap (NumberField.RingOfIntegers L) P.ResidueField
        (number_order_displacement
          (L := L) hq P π hπ_mem hπ_not_sq hπ_spans σ x) = 0 := by
  classical
  letI : P.IsMaximal :=
    number_above_maximal (L := L) hq P
  have hFiniteResidue :
      Finite P.ResidueField :=
    number_local_residue (L := L) hq P
  letI : Fintype P.ResidueField := Fintype.ofFinite P.ResidueField
  have hD_zero :
      ∀ z : P.ResidueField, D z = 0 := by
    exact derivation_like_zero D hD_mul
  calc
    algebraMap (NumberField.RingOfIntegers L) P.ResidueField
        (number_order_displacement
          (L := L) hq P π hπ_mem hπ_not_sq hπ_spans σ x) =
        D (algebraMap (NumberField.RingOfIntegers L) P.ResidueField x) := by
          exact (hD_rep x).symm
    _ = 0 := by
          exact hD_zero (algebraMap (NumberField.RingOfIntegers L) P.ResidueField x)

lemma displacement_scalar_derivation
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    {q : ℕ} (hq : Nat.Prime q)
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)]
    (π : NumberField.RingOfIntegers L)
    (hπ_mem : π ∈ P)
    (hπ_not_sq : π ∉ P ^ 2)
    (hπ_spans : ∀ x : NumberField.RingOfIntegers L,
      x ∈ P → ∃ a : NumberField.RingOfIntegers L, x - a * π ∈ P ^ 2)
    (σ : P.inertia (Gal(L/ℚ)))
    (hπ_fixed : ((σ : Gal(L/ℚ)) • π) - π ∈ P ^ 2)
    (x : NumberField.RingOfIntegers L) :
    algebraMap (NumberField.RingOfIntegers L) P.ResidueField
        (number_order_displacement
          (L := L) hq P π hπ_mem hπ_not_sq hπ_spans σ x) = 0 := by
  classical
  letI : P.IsMaximal :=
    number_above_maximal (L := L) hq P
  let D : P.ResidueField → P.ResidueField := fun z =>
    algebraMap (NumberField.RingOfIntegers L) P.ResidueField
      (number_order_displacement
        (L := L) hq P π hπ_mem hπ_not_sq hπ_spans σ
        (Classical.choose (Ideal.algebraMap_residueField_surjective P z)))
  have hD_rep :
      ∀ y : NumberField.RingOfIntegers L,
        D (algebraMap (NumberField.RingOfIntegers L) P.ResidueField y) =
          algebraMap (NumberField.RingOfIntegers L) P.ResidueField
            (number_order_displacement
              (L := L) hq P π hπ_mem hπ_not_sq hπ_spans σ y) := by
    intro y
    have hchoose :
        algebraMap (NumberField.RingOfIntegers L) P.ResidueField
            (Classical.choose
              (Ideal.algebraMap_residueField_surjective P
                (algebraMap (NumberField.RingOfIntegers L) P.ResidueField y))) =
          algebraMap (NumberField.RingOfIntegers L) P.ResidueField y := by
      exact
        Classical.choose_spec
          (Ideal.algebraMap_residueField_surjective P
            (algebraMap (NumberField.RingOfIntegers L) P.ResidueField y))
    have hsub :
        Classical.choose
            (Ideal.algebraMap_residueField_surjective P
              (algebraMap (NumberField.RingOfIntegers L) P.ResidueField y)) -
          y ∈ P := by
      exact (ideal_residue_sub (I := P)).1 hchoose
    change
      algebraMap (NumberField.RingOfIntegers L) P.ResidueField
          (number_order_displacement
            (L := L) hq P π hπ_mem hπ_not_sq hπ_spans σ
            (Classical.choose
              (Ideal.algebraMap_residueField_surjective P
                (algebraMap (NumberField.RingOfIntegers L) P.ResidueField y)))) =
        algebraMap (NumberField.RingOfIntegers L) P.ResidueField
          (number_order_displacement
            (L := L) hq P π hπ_mem hπ_not_sq hπ_spans σ y)
    exact
      displacement_scalar_sub
        (L := L) hq P π hπ_mem hπ_not_sq hπ_spans σ hπ_fixed hsub
  have hD_mul :
      ∀ u v : P.ResidueField, D (u * v) = u * D v + v * D u := by
    intro u v
    obtain ⟨x, rfl⟩ := Ideal.algebraMap_residueField_surjective P u
    obtain ⟨y, rfl⟩ := Ideal.algebraMap_residueField_surjective P v
    calc
      D (algebraMap (NumberField.RingOfIntegers L) P.ResidueField x *
          algebraMap (NumberField.RingOfIntegers L) P.ResidueField y) =
          D (algebraMap (NumberField.RingOfIntegers L) P.ResidueField (x * y)) := by
            rw [map_mul]
      _ = algebraMap (NumberField.RingOfIntegers L) P.ResidueField
          (number_order_displacement
            (L := L) hq P π hπ_mem hπ_not_sq hπ_spans σ (x * y)) := by
            exact hD_rep (x * y)
      _ =
          algebraMap (NumberField.RingOfIntegers L) P.ResidueField x *
              algebraMap (NumberField.RingOfIntegers L) P.ResidueField
                (number_order_displacement
                  (L := L) hq P π hπ_mem hπ_not_sq hπ_spans σ y) +
            algebraMap (NumberField.RingOfIntegers L) P.ResidueField y *
              algebraMap (NumberField.RingOfIntegers L) P.ResidueField
                (number_order_displacement
                  (L := L) hq P π hπ_mem hπ_not_sq hπ_spans σ x) := by
            exact
              displacement_scalar_mul
                (L := L) hq P π hπ_mem hπ_not_sq hπ_spans σ x y
      _ =
          algebraMap (NumberField.RingOfIntegers L) P.ResidueField x *
              D (algebraMap (NumberField.RingOfIntegers L) P.ResidueField y) +
            algebraMap (NumberField.RingOfIntegers L) P.ResidueField y *
              D (algebraMap (NumberField.RingOfIntegers L) P.ResidueField x) := by
            rw [hD_rep y, hD_rep x]
  exact
    displacement_derivation_like
      (L := L) hq P π hπ_mem hπ_not_sq hπ_spans σ D hD_rep hD_mul x

lemma displacement_scalar_prime
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    {q : ℕ} (hq : Nat.Prime q)
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)]
    (π : NumberField.RingOfIntegers L)
    (hπ_mem : π ∈ P)
    (hπ_not_sq : π ∉ P ^ 2)
    (hπ_spans : ∀ x : NumberField.RingOfIntegers L,
      x ∈ P → ∃ a : NumberField.RingOfIntegers L, x - a * π ∈ P ^ 2)
    (σ : P.inertia (Gal(L/ℚ)))
    (hπ_fixed : ((σ : Gal(L/ℚ)) • π) - π ∈ P ^ 2)
    {x a : NumberField.RingOfIntegers L}
    (hx : x ∈ P)
    (ha : (((σ : Gal(L/ℚ)) • x) - x) - a * π ∈ P ^ 2) :
    a ∈ P := by
  classical
  have hzero :
      (((σ : Gal(L/ℚ)) • x) - x) - 0 * π ∈ P ^ 2 := by
    simpa using
      number_sq_fixed
        (L := L) hq P π hπ_mem hπ_not_sq hπ_spans σ hπ_fixed hx
  have hdiff :
      a - 0 ∈ P := by
    exact
      displacement_scalar_unique
        (L := L) hq P π hπ_mem hπ_not_sq σ x ha hzero
  simpa using hdiff

lemma inertia_sq_fixed
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    {q : ℕ} (hq : Nat.Prime q)
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)]
    (π : NumberField.RingOfIntegers L)
    (hπ_mem : π ∈ P)
    (hπ_not_sq : π ∉ P ^ 2)
    (hπ_spans : ∀ x : NumberField.RingOfIntegers L,
      x ∈ P → ∃ a : NumberField.RingOfIntegers L, x - a * π ∈ P ^ 2)
    (σ : P.inertia (Gal(L/ℚ)))
    (hπ_fixed : ((σ : Gal(L/ℚ)) • π) - π ∈ P ^ 2)
    (x : NumberField.RingOfIntegers L) :
    ((σ : Gal(L/ℚ)) • x) - x ∈ P ^ 2 := by
  classical
  have hcoeff_zero :
      algebraMap (NumberField.RingOfIntegers L) P.ResidueField
        (number_order_displacement
          (L := L) hq P π hπ_mem hπ_not_sq hπ_spans σ x) = 0 := by
    exact
      displacement_scalar_derivation
        (L := L) hq P π hπ_mem hπ_not_sq hπ_spans σ hπ_fixed x
  have hcoeff_mem :
      number_order_displacement
        (L := L) hq P π hπ_mem hπ_not_sq hπ_spans σ x ∈ P := by
    exact (Ideal.algebraMap_residueField_eq_zero (I := P)).1 hcoeff_zero
  exact
    sq_displacement_scalar
      (L := L) hq P π hπ_mem hπ_not_sq hπ_spans σ x hcoeff_mem

lemma number_square_sq
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    {q : ℕ} (hq : Nat.Prime q)
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)]
    (π : NumberField.RingOfIntegers L)
    (hπ_mem : π ∈ P)
    (hπ_not_sq : π ∉ P ^ 2)
    (hπ_spans : ∀ x : NumberField.RingOfIntegers L,
      x ∈ P → ∃ a : NumberField.RingOfIntegers L, x - a * π ∈ P ^ 2)
    (σ : P.inertia (Gal(L/ℚ)))
    (hπ_fixed : ((σ : Gal(L/ℚ)) • π) - π ∈ P ^ 2) :
    σ ∈ (number_square_representation (L := L) P).ker := by
  classical
  rw [square_representation_ker (L := L) P]
  rw [wild_inertia_subgroup (L := L) P σ]
  intro x
  exact
    inertia_sq_fixed
      (L := L) hq P π hπ_mem hπ_not_sq hπ_spans σ hπ_fixed x

lemma cotangent_scalar_square
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    {q : ℕ} (hq : Nat.Prime q)
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)]
    (π : NumberField.RingOfIntegers L)
    (hπ_mem : π ∈ P)
    (hπ_not_sq : π ∉ P ^ 2)
    (hπ_spans : ∀ x : NumberField.RingOfIntegers L,
      x ∈ P → ∃ a : NumberField.RingOfIntegers L, x - a * π ∈ P ^ 2)
    (σ : P.inertia (Gal(L/ℚ))) :
    field_cotangent_scalar
        (L := L) hq P π hπ_mem hπ_not_sq hπ_spans σ - 1 ∈ P ↔
      σ ∈ (number_square_representation (L := L) P).ker := by
  classical
  constructor
  · intro hscalar
    have hπ_fixed :
        ((σ : Gal(L/ℚ)) • π) - π ∈ P ^ 2 := by
      exact
        (cotangent_scalar_sq
          (L := L) hq P π hπ_mem hπ_not_sq hπ_spans σ).1 hscalar
    exact
      number_square_sq
        (L := L) hq P π hπ_mem hπ_not_sq hπ_spans σ hπ_fixed
  · intro hker
    have hπ_fixed :
        ((σ : Gal(L/ℚ)) • π) - π ∈ P ^ 2 := by
      exact
        sq_square_ker
          (L := L) P π σ hker
    exact
      (cotangent_scalar_sq
        (L := L) hq P π hπ_mem hπ_not_sq hπ_spans σ).2 hπ_fixed

lemma cotangent_character_ker
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    {q : ℕ} (hq : Nat.Prime q)
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)]
    (π : NumberField.RingOfIntegers L)
    (hπ_mem : π ∈ P)
    (hπ_not_sq : π ∉ P ^ 2)
    (hπ_spans : ∀ x : NumberField.RingOfIntegers L,
      x ∈ P → ∃ a : NumberField.RingOfIntegers L, x - a * π ∈ P ^ 2) :
    (number_cotangent_character
        (L := L) hq P π hπ_mem hπ_not_sq hπ_spans).ker =
      (number_square_representation (L := L) P).ker := by
  classical
  ext σ
  calc
    σ ∈ (number_cotangent_character
        (L := L) hq P π hπ_mem hπ_not_sq hπ_spans).ker ↔
      field_cotangent_scalar
        (L := L) hq P π hπ_mem hπ_not_sq hπ_spans σ - 1 ∈ P := by
        exact
          number_cotangent_ker
            (L := L) hq P π hπ_mem hπ_not_sq hπ_spans σ
    _ ↔ σ ∈ (number_square_representation (L := L) P).ker := by
        exact
          cotangent_scalar_square
            (L := L) hq P π hπ_mem hπ_not_sq hπ_spans σ

lemma number_cotangent_generator
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    {q : ℕ} (hq : Nat.Prime q)
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)]
    (π : NumberField.RingOfIntegers L)
    (hπ_mem : π ∈ P)
    (hπ_not_sq : π ∉ P ^ 2)
    (hπ_spans : ∀ x : NumberField.RingOfIntegers L,
      x ∈ P → ∃ a : NumberField.RingOfIntegers L, x - a * π ∈ P ^ 2) :
    ∃ χ : P.inertia (Gal(L/ℚ)) →* P.ResidueFieldˣ,
      χ.ker = (number_square_representation (L := L) P).ker := by
  classical
  refine
    ⟨number_cotangent_character
        (L := L) hq P π hπ_mem hπ_not_sq hπ_spans, ?_⟩
  exact
    cotangent_character_ker
      (L := L) hq P π hπ_mem hπ_not_sq hπ_spans

end Towers
