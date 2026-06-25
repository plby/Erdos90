import Submission.NumberTheory.CotangentGenerator


open Filter
open scoped Pointwise EuclideanGeometry Topology

noncomputable section

open NumberField

namespace Submission

lemma number_field_wild
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    {q : ℕ} (_hq : Nat.Prime q)
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)] :
    Finite (number_wild_subgroup (L := L) P) := by
  classical
  letI : Finite (Gal(L/ℚ)) :=
    IsGaloisGroup.finite (Gal(L/ℚ)) ℚ L
  letI : Finite (P.inertia (Gal(L/ℚ))) :=
    inferInstance
  infer_instance

noncomputable def field_higher_ramification
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (P : Ideal (NumberField.RingOfIntegers L)) (n : ℕ) :
    Subgroup (P.inertia (Gal(L/ℚ))) where
  carrier :=
    {σ | ∀ x : NumberField.RingOfIntegers L,
      ((σ : Gal(L/ℚ)) • x) - x ∈ P ^ (n + 1)}
  one_mem' := by
    intro x
    simp
  mul_mem' := by
    intro σ τ hσ hτ x
    have hτx :
        ((τ : Gal(L/ℚ)) • x) - x ∈ P ^ (n + 1) := by
      exact hτ x
    have hστx :
        (σ : Gal(L/ℚ)) • (((τ : Gal(L/ℚ)) • x) - x) ∈ P ^ (n + 1) := by
      exact number_smul_pow (L := L) P σ (n + 1) hτx
    have hσx :
        ((σ : Gal(L/ℚ)) • x) - x ∈ P ^ (n + 1) := by
      exact hσ x
    have hdecomp :
        (((σ * τ : P.inertia (Gal(L/ℚ))) : Gal(L/ℚ)) • x) - x =
          (σ : Gal(L/ℚ)) • (((τ : Gal(L/ℚ)) • x) - x) +
            (((σ : Gal(L/ℚ)) • x) - x) := by
      calc
        (((σ * τ : P.inertia (Gal(L/ℚ))) : Gal(L/ℚ)) • x) - x =
            ((σ : Gal(L/ℚ)) • ((τ : Gal(L/ℚ)) • x)) - x := by
          simp [mul_smul]
        _ =
            (σ : Gal(L/ℚ)) • (((τ : Gal(L/ℚ)) • x) - x) +
              (((σ : Gal(L/ℚ)) • x) - x) := by
          rw [smul_sub]
          abel
    rw [hdecomp]
    exact Ideal.add_mem (P ^ (n + 1)) hστx hσx
  inv_mem' := by
    intro σ hσ x
    let τ : P.inertia (Gal(L/ℚ)) := σ⁻¹
    have hσ_on_inv :
        ((σ : Gal(L/ℚ)) • ((τ : Gal(L/ℚ)) • x)) -
            ((τ : Gal(L/ℚ)) • x) ∈ P ^ (n + 1) := by
      exact hσ ((τ : Gal(L/ℚ)) • x)
    have hx_sub :
        x - ((τ : Gal(L/ℚ)) • x) ∈ P ^ (n + 1) := by
      simpa [τ, mul_smul] using hσ_on_inv
    have hneg :
        - (x - ((τ : Gal(L/ℚ)) • x)) ∈ P ^ (n + 1) := by
      exact (P ^ (n + 1)).neg_mem hx_sub
    change ((τ : Gal(L/ℚ)) • x) - x ∈ P ^ (n + 1)
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hneg

lemma number_ramification_subgroup
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (P : Ideal (NumberField.RingOfIntegers L)) (n : ℕ)
    (σ : P.inertia (Gal(L/ℚ))) :
    σ ∈ field_higher_ramification (L := L) P n ↔
      ∀ x : NumberField.RingOfIntegers L,
        ((σ : Gal(L/ℚ)) • x) - x ∈ P ^ (n + 1) := by
  rfl

lemma higher_ramification_one
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (P : Ideal (NumberField.RingOfIntegers L)) :
    field_higher_ramification (L := L) P 1 =
      number_wild_subgroup (L := L) P := by
  ext σ
  rfl

lemma higher_ramification_antitone
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (P : Ideal (NumberField.RingOfIntegers L)) :
    Antitone (field_higher_ramification (L := L) P) := by
  classical
  intro m n hmn σ hσ x
  have hpow_le : P ^ (n + 1) ≤ P ^ (m + 1) := by
    exact Ideal.pow_le_pow_right (Nat.succ_le_succ hmn)
  exact hpow_le (hσ x)

lemma higher_ramification_top
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (P : Ideal (NumberField.RingOfIntegers L)) :
    field_higher_ramification (L := L) P 0 = ⊤ := by
  classical
  ext σ
  constructor
  · intro _hσ
    trivial
  · intro _hσ x
    simpa using number_smul_sub (L := L) P σ x

lemma number_field_higher
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (P : Ideal (NumberField.RingOfIntegers L)) (n : ℕ) :
    Finite (field_higher_ramification (L := L) P n) := by
  classical
  letI : Finite (Gal(L/ℚ)) :=
    IsGaloisGroup.finite (Gal(L/ℚ)) ℚ L
  letI : Finite (P.inertia (Gal(L/ℚ))) :=
    inferInstance
  infer_instance

lemma number_ramification_succ
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (P : Ideal (NumberField.RingOfIntegers L)) (n : ℕ) :
    field_higher_ramification (L := L) P (n + 1) ≤
      field_higher_ramification (L := L) P n := by
  classical
  exact higher_ramification_antitone (L := L) P (Nat.le_succ n)

lemma higher_wild_inertia
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (P : Ideal (NumberField.RingOfIntegers L)) {n : ℕ}
    (hn : 1 ≤ n) :
    field_higher_ramification (L := L) P n ≤
      number_wild_subgroup (L := L) P := by
  classical
  have hle :
      field_higher_ramification (L := L) P n ≤
        field_higher_ramification (L := L) P 1 := by
    exact higher_ramification_antitone (L := L) P hn
  simpa [higher_ramification_one (L := L) P] using hle

lemma number_higher_normal
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (P : Ideal (NumberField.RingOfIntegers L)) (n : ℕ) :
    (field_higher_ramification (L := L) P n).Normal := by
  classical
  refine Subgroup.Normal.mk ?_
  intro τ hτ σ
  rw [number_ramification_subgroup (L := L) P n]
  intro x
  let y : NumberField.RingOfIntegers L :=
    ((σ⁻¹ : P.inertia (Gal(L/ℚ))) : Gal(L/ℚ)) • x
  have hτy :
      ((τ : Gal(L/ℚ)) • y) - y ∈ P ^ (n + 1) := by
    exact
      (number_ramification_subgroup
        (L := L) P n τ).1 hτ y
  have hστy :
      (σ : Gal(L/ℚ)) • (((τ : Gal(L/ℚ)) • y) - y) ∈ P ^ (n + 1) := by
    exact number_smul_pow (L := L) P σ (n + 1) hτy
  have hconj :
      (((σ * τ * σ⁻¹ : P.inertia (Gal(L/ℚ))) : Gal(L/ℚ)) • x) - x =
        (σ : Gal(L/ℚ)) • (((τ : Gal(L/ℚ)) • y) - y) := by
    calc
      (((σ * τ * σ⁻¹ : P.inertia (Gal(L/ℚ))) : Gal(L/ℚ)) • x) - x =
          ((σ : Gal(L/ℚ)) • ((τ : Gal(L/ℚ)) •
            (((σ⁻¹ : P.inertia (Gal(L/ℚ))) : Gal(L/ℚ)) • x))) - x := by
            simp [mul_smul]
      _ =
          ((σ : Gal(L/ℚ)) • ((τ : Gal(L/ℚ)) • y)) -
            ((σ : Gal(L/ℚ)) • y) := by
            simp [y]
      _ = (σ : Gal(L/ℚ)) • (((τ : Gal(L/ℚ)) • y) - y) := by
            rw [smul_sub]
  rw [hconj]
  exact hστy

noncomputable def number_higher_subgroup
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (P : Ideal (NumberField.RingOfIntegers L)) (n : ℕ) :
    Subgroup (field_higher_ramification (L := L) P n) where
  carrier := fun σ =>
    ((σ : field_higher_ramification (L := L) P n) :
        P.inertia (Gal(L/ℚ))) ∈
      field_higher_ramification (L := L) P (n + 1)
  one_mem' := by
    change ((1 : field_higher_ramification (L := L) P n) :
        P.inertia (Gal(L/ℚ))) ∈
      field_higher_ramification (L := L) P (n + 1)
    exact Subgroup.one_mem (field_higher_ramification (L := L) P (n + 1))
  mul_mem' := by
    intro σ τ hσ hτ
    change (((σ * τ : field_higher_ramification (L := L) P n) :
        P.inertia (Gal(L/ℚ))) ∈
      field_higher_ramification (L := L) P (n + 1))
    exact
      Subgroup.mul_mem
        (field_higher_ramification (L := L) P (n + 1))
        hσ hτ
  inv_mem' := by
    intro σ hσ
    change (((σ⁻¹ : field_higher_ramification (L := L) P n) :
        P.inertia (Gal(L/ℚ))) ∈
      field_higher_ramification (L := L) P (n + 1))
    exact
      Subgroup.inv_mem
        (field_higher_ramification (L := L) P (n + 1))
        hσ

lemma higher_ramification_subgroup
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (P : Ideal (NumberField.RingOfIntegers L)) (n : ℕ)
    (σ : field_higher_ramification (L := L) P n) :
    σ ∈ number_higher_subgroup (L := L) P n ↔
      ((σ : field_higher_ramification (L := L) P n) :
        P.inertia (Gal(L/ℚ))) ∈
        field_higher_ramification (L := L) P (n + 1) := by
  rfl

lemma higher_ramification_normal
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (P : Ideal (NumberField.RingOfIntegers L)) (n : ℕ) :
    (number_higher_subgroup (L := L) P n).Normal := by
  classical
  refine Subgroup.Normal.mk ?_
  intro τ hτ σ
  rw [higher_ramification_subgroup (L := L) P n]
  have hnormal :
      (field_higher_ramification (L := L) P (n + 1)).Normal :=
    number_higher_normal (L := L) P (n + 1)
  have hconj :
      ((σ : P.inertia (Gal(L/ℚ))) *
          (τ : P.inertia (Gal(L/ℚ))) *
          (σ : P.inertia (Gal(L/ℚ)))⁻¹) ∈
        field_higher_ramification (L := L) P (n + 1) := by
    exact hnormal.conj_mem (τ : P.inertia (Gal(L/ℚ))) hτ
      (σ : P.inertia (Gal(L/ℚ)))
  change
    ((σ : P.inertia (Gal(L/ℚ))) *
        (τ : P.inertia (Gal(L/ℚ))) *
        (σ : P.inertia (Gal(L/ℚ)))⁻¹) ∈
      field_higher_ramification (L := L) P (n + 1)
  exact hconj

instance instHigherRamification
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (P : Ideal (NumberField.RingOfIntegers L)) (n : ℕ) :
    (number_higher_subgroup (L := L) P n).Normal :=
  higher_ramification_normal (L := L) P n

abbrev number_ramification_step
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (P : Ideal (NumberField.RingOfIntegers L)) (n : ℕ) :=
  field_higher_ramification (L := L) P n ⧸
    number_higher_subgroup (L := L) P n

lemma higher_ramification_step
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (P : Ideal (NumberField.RingOfIntegers L)) (n : ℕ) :
    Finite (number_ramification_step (L := L) P n) := by
  classical
  have hFinite :
      Finite (field_higher_ramification (L := L) P n) :=
    number_field_higher (L := L) P n
  letI : Finite (field_higher_ramification (L := L) P n) :=
    hFinite
  infer_instance

noncomputable def number_higher_succ
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (P : Ideal (NumberField.RingOfIntegers L)) (n : ℕ) :
    number_higher_subgroup (L := L) P n ≃
      field_higher_ramification (L := L) P (n + 1) where
  toFun σ :=
    ⟨((σ : field_higher_ramification (L := L) P n) :
        P.inertia (Gal(L/ℚ))), by
      exact σ.property⟩
  invFun τ :=
    let τn : field_higher_ramification (L := L) P n :=
      ⟨(τ : P.inertia (Gal(L/ℚ))),
        number_ramification_succ (L := L) P n τ.property⟩
    ⟨τn, by
      change (τ : P.inertia (Gal(L/ℚ))) ∈
        field_higher_ramification (L := L) P (n + 1)
      exact τ.property⟩
  left_inv σ := by
    ext
    rfl
  right_inv τ := by
    ext
    rfl

lemma higher_ramification_succ
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (P : Ideal (NumberField.RingOfIntegers L)) (n : ℕ) :
    Nat.card (number_higher_subgroup (L := L) P n) =
      Nat.card (field_higher_ramification (L := L) P (n + 1)) := by
  classical
  exact
    Nat.card_congr
      (number_higher_succ (L := L) P n)

lemma additive_p_group
    {K : Type*} [Field K] [Finite K]
    {q : ℕ} [CharP K q] :
    IsPGroup q (Multiplicative K) := by
  classical
  letI : Fintype K := Fintype.ofFinite K
  obtain ⟨n, _hq, hcard⟩ := FiniteField.card K q
  refine IsPGroup.of_card (p := q) (n := (n : ℕ)) ?_
  have hnat : Nat.card (Multiplicative K) = Nat.card K :=
    Nat.card_congr Multiplicative.ofAdd.symm
  rw [hnat, Nat.card_eq_fintype_card, hcard]

lemma number_residue_additive
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    {q : ℕ} (hq : Nat.Prime q)
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)]
    {Γ : Type*} [Group Γ]
    (φ : Γ →* Multiplicative P.ResidueField)
    (hφ : Function.Injective φ) :
    IsPGroup q Γ := by
  classical
  letI : CharP P.ResidueField q :=
    number_char_p (L := L) hq P
  have hResidueFinite : Finite P.ResidueField :=
    number_local_residue (L := L) hq P
  letI : Finite P.ResidueField := hResidueFinite
  have hAdditive : IsPGroup q (Multiplicative P.ResidueField) :=
    additive_p_group (K := P.ResidueField) (q := q)
  exact hAdditive.of_injective φ hφ

lemma number_divisor_additive
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    {q : ℕ} (hq : Nat.Prime q)
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)]
    {Γ : Type*} [Group Γ] [Finite Γ]
    (φ : Γ →* Multiplicative P.ResidueField)
    (hφ : Function.Injective φ) :
    ∀ l : ℕ, Nat.Prime l → l ∣ Nat.card Γ → l = q := by
  classical
  letI : Fact q.Prime := ⟨hq⟩
  have hΓ : IsPGroup q Γ :=
    number_residue_additive
      (L := L) hq P φ hφ
  exact divisor_p_group hΓ

lemma number_divisor_injective
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    {q : ℕ} (hq : Nat.Prime q)
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)]
    (n : ℕ)
    (φ : number_ramification_step (L := L) P n →*
      Multiplicative P.ResidueField)
    (hφ : Function.Injective φ) :
    ∀ l : ℕ, Nat.Prime l →
      l ∣ Nat.card (number_ramification_step (L := L) P n) →
        l = q := by
  classical
  have hFinite :
      Finite (number_ramification_step (L := L) P n) :=
    higher_ramification_step (L := L) P n
  letI : Finite (number_ramification_step (L := L) P n) :=
    hFinite
  exact
    number_divisor_additive
      (L := L) hq P φ hφ

lemma ideal_sup_top
    {A : Type*} [CommRing A]
    {J P : Ideal A} [P.IsPrime] [P.IsMaximal]
    (m : ℕ)
    (hsup : J ⊔ P = ⊤) :
    J ^ m ⊔ P = ⊤ := by
  classical
  cases m with
  | zero =>
      simp
  | succ m =>
      have hJ_not_le : ¬ J ≤ P := by
        intro hJP
        have htop_le : (⊤ : Ideal A) ≤ P := by
          rw [← hsup]
          exact sup_le hJP le_rfl
        have hP_top : P = ⊤ := by
          exact top_le_iff.mp htop_le
        exact Ideal.IsPrime.ne_top (show P.IsPrime from inferInstance) hP_top
      obtain ⟨j, hjJ, hjP⟩ : ∃ j : A, j ∈ J ∧ j ∉ P := by
        by_contra hnone
        exact hJ_not_le (by
          intro j hj
          by_contra hjP
          exact hnone ⟨j, hj, hjP⟩)
      have hjpowJ : j ^ (m + 1) ∈ J ^ (m + 1) :=
        Ideal.pow_mem_pow hjJ (m + 1)
      have hjpowP : j ^ (m + 1) ∉ P := by
        intro hmem
        have hjP' : j ∈ P := by
          exact
            Ideal.IsPrime.mem_of_pow_mem
              (show P.IsPrime from inferInstance) (m + 1) hmem
        exact hjP hjP'
      have hpow_not_le : ¬ J ^ (m + 1) ≤ P := by
        intro hle
        exact hjpowP (hle hjpowJ)
      by_contra hne
      have hle_sup : J ^ (m + 1) ⊔ P ≤ P := by
        have hEq : P = J ^ (m + 1) ⊔ P :=
          Ideal.IsMaximal.eq_of_le (show P.IsMaximal from inferInstance) hne le_sup_right
        rw [← hEq]
      exact hpow_not_le (le_sup_left.trans hle_sup)

lemma cotangent_spans_complement
    {A : Type*} [CommRing A]
    (P J : Ideal A) {π x : A} {m : ℕ}
    (hπ : Ideal.span ({π} : Set A) = P * J)
    (hsup : J ^ m ⊔ P = ⊤)
    (hx : x ∈ P ^ m) :
    ∃ a : A, x - a * π ^ m ∈ P ^ (m + 1) := by
  classical
  have hspan_pow : Ideal.span ({π ^ m} : Set A) = P ^ m * J ^ m := by
    calc
      Ideal.span ({π ^ m} : Set A) =
          Ideal.span ({π} : Set A) ^ m := by
            rw [Ideal.span_singleton_pow]
      _ = (P * J) ^ m := by
            rw [hπ]
      _ = P ^ m * J ^ m := by
            rw [mul_pow]
  have hone : (1 : A) ∈ J ^ m ⊔ P := by
    rw [hsup]
    trivial
  rw [Submodule.mem_sup] at hone
  rcases hone with ⟨j, hj, p, hp, hjp⟩
  have hjx_span : j * x ∈ Ideal.span ({π ^ m} : Set A) := by
    rw [hspan_pow]
    convert Ideal.mul_mem_mul hx hj using 1
    ring
  obtain ⟨a, ha⟩ := (Ideal.mem_span_singleton).1 hjx_span
  refine ⟨a, ?_⟩
  have hpx : p * x ∈ P ^ (m + 1) := by
    simpa [pow_succ'] using Ideal.mul_mem_mul hp hx
  convert hpx using 1
  calc
    x - a * π ^ m = (j + p) * x - a * π ^ m := by
      rw [hjp]
      ring
    _ = p * x := by
      rw [add_mul, ha]
      ring

lemma not_succ_sq
    {A : Type*} [CommRing A] [IsDedekindDomain A]
    (P : Ideal A) [P.IsPrime] [P.IsMaximal]
    {π : A} {m : ℕ}
    (hm : 0 < m)
    (hπ_mem : π ∈ P)
    (hπ_not_sq : π ∉ P ^ 2) :
    π ^ m ∉ P ^ (m + 1) := by
  classical
  have hP_ne_bot : P ≠ ⊥ := by
    intro hbot
    have hπ_bot : π ∈ (⊥ : Ideal A) := by
      simpa [hbot] using hπ_mem
    have hπ_zero : π = 0 := by
      simpa using hπ_bot
    exact hπ_not_sq (by simp [hπ_zero])
  have hP_ne_top : P ≠ ⊤ :=
    Ideal.IsPrime.ne_top (show P.IsPrime from inferInstance)
  obtain ⟨J, hπ_span, hJP_top⟩ :=
    dedekind_complement_sq P hπ_mem hπ_not_sq
  have hJpow_top : J ^ m ⊔ P = ⊤ :=
    ideal_sup_top (J := J) (P := P) m hJP_top
  intro hπm_succ
  have hspan_pow : Ideal.span ({π ^ m} : Set A) = P ^ m * J ^ m := by
    calc
      Ideal.span ({π ^ m} : Set A) =
          Ideal.span ({π} : Set A) ^ m := by
            rw [Ideal.span_singleton_pow]
      _ = (P * J) ^ m := by
            rw [hπ_span]
      _ = P ^ m * J ^ m := by
            rw [mul_pow]
  have hspan_le_succ : Ideal.span ({π ^ m} : Set A) ≤ P ^ (m + 1) := by
    exact (Ideal.span_singleton_le_iff_mem (P ^ (m + 1))).2 hπm_succ
  have hprod_le_succ : P ^ m * J ^ m ≤ P ^ (m + 1) := by
    simpa [hspan_pow] using hspan_le_succ
  have hpow_le_succ : P ^ m ≤ P ^ (m + 1) := by
    intro y hy
    have hone : (1 : A) ∈ J ^ m ⊔ P := by
      rw [hJpow_top]
      trivial
    rw [Submodule.mem_sup] at hone
    rcases hone with ⟨j, hj, p, hp, hjp⟩
    have hjy : j * y ∈ P ^ (m + 1) := by
      apply hprod_le_succ
      convert Ideal.mul_mem_mul hy hj using 1
      ring
    have hpy : p * y ∈ P ^ (m + 1) := by
      simpa [pow_succ'] using Ideal.mul_mem_mul hp hy
    have hsum : j * y + p * y ∈ P ^ (m + 1) :=
      Ideal.add_mem (P ^ (m + 1)) hjy hpy
    convert hsum using 1
    calc
      y = (j + p) * y := by
        rw [hjp]
        ring
      _ = j * y + p * y := by
        ring
  have hstrict : P ^ (m + 1) < P ^ m := by
    have _hm_nonzero : m ≠ 0 := Nat.ne_of_gt hm
    have hanti := Ideal.pow_right_strictAnti P hP_ne_bot hP_ne_top
    exact hanti (Nat.lt_succ_self m)
  exact (not_le_of_gt hstrict) hpow_le_succ

lemma ideal_generator_succ
    {A : Type*} [CommRing A] [IsDedekindDomain A]
    (P : Ideal A) [P.IsPrime] [P.IsMaximal]
    {π c : A} {m : ℕ}
    (hm : 0 < m)
    (hπ_mem : π ∈ P)
    (hπ_not_sq : π ∉ P ^ 2)
    (hcπ : c * π ^ m ∈ P ^ (m + 1)) :
    c ∈ P := by
  classical
  by_contra hc_not_mem
  letI : Field (A ⧸ P) := Ideal.Quotient.field P
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
  have hπ_pow_mem : π ^ m ∈ P ^ m :=
    Ideal.pow_mem_pow hπ_mem m
  have hfirst : (1 - r * c) * π ^ m ∈ P ^ (m + 1) := by
    simpa [pow_succ'] using Ideal.mul_mem_mul hone_sub_rc hπ_pow_mem
  have hsecond : r * (c * π ^ m) ∈ P ^ (m + 1) := by
    exact Ideal.mul_mem_left (P ^ (m + 1)) r hcπ
  have hsum :
      (1 - r * c) * π ^ m + r * (c * π ^ m) ∈ P ^ (m + 1) := by
    exact Ideal.add_mem (P ^ (m + 1)) hfirst hsecond
  have hπm_succ : π ^ m ∈ P ^ (m + 1) := by
    convert hsum using 1
    ring
  exact
    (not_succ_sq
      P hm hπ_mem hπ_not_sq) hπm_succ

lemma ideal_sub_succ
    {A : Type*} [CommRing A]
    (P : Ideal A) {u v : A} {n k : ℕ}
    (hu : u ∈ P)
    (hv : v ∈ P)
    (hsub : u - v ∈ P ^ (n + 1)) :
    u ^ k - v ^ k ∈ P ^ (n + k) := by
  classical
  induction k with
  | zero =>
      simp
  | succ k ih =>
      have hu_pow : u ^ k ∈ P ^ k :=
        Ideal.pow_mem_pow hu k
      have hfirst : u ^ k * (u - v) ∈ P ^ (n + (k + 1)) := by
        have hmul := Ideal.mul_mem_mul hu_pow hsub
        have hEq : P ^ k * P ^ (n + 1) = P ^ (n + (k + 1)) := by
          rw [← pow_add]
          congr 1
          omega
        simpa [hEq] using hmul
      have hsecond : (u ^ k - v ^ k) * v ∈ P ^ (n + (k + 1)) := by
        have hmul := Ideal.mul_mem_mul ih hv
        have hEq : P ^ (n + k) * P = P ^ (n + (k + 1)) := by
          calc
            P ^ (n + k) * P = P ^ (n + k) * P ^ 1 := by
              rw [pow_one]
            _ = P ^ ((n + k) + 1) := by
              rw [← pow_add]
            _ = P ^ (n + (k + 1)) := by
              congr 1
        simpa [hEq] using hmul
      have hsum :
          u ^ k * (u - v) + (u ^ k - v ^ k) * v ∈ P ^ (n + (k + 1)) :=
        Ideal.add_mem (P ^ (n + (k + 1))) hfirst hsecond
      convert hsum using 1
      ring

lemma ideal_succ_sub
    {A : Type*} [CommRing A]
    (P : Ideal A) {u v : A} {n : ℕ}
    (hn : 1 ≤ n)
    (hu : u ∈ P)
    (hv : v ∈ P)
    (hsub : u - v ∈ P ^ (n + 1)) :
    u ^ (n + 1) - v ^ (n + 1) ∈ P ^ (n + 2) := by
  classical
  have hdeep : u ^ (n + 1) - v ^ (n + 1) ∈ P ^ (n + (n + 1)) :=
    ideal_sub_succ P hu hv hsub
  exact Ideal.pow_le_pow_right (by omega : n + 2 ≤ n + (n + 1)) hdeep

lemma scalar_unique_mod
    {A : Type*} [CommRing A] [IsDedekindDomain A]
    (P : Ideal A) [P.IsPrime] [P.IsMaximal]
    {π x a b : A} {m : ℕ}
    (hm : 0 < m)
    (hπ_mem : π ∈ P)
    (hπ_not_sq : π ∉ P ^ 2)
    (ha : x - a * π ^ m ∈ P ^ (m + 1))
    (hb : x - b * π ^ m ∈ P ^ (m + 1)) :
    a - b ∈ P := by
  classical
  have hdiff : (x - b * π ^ m) - (x - a * π ^ m) ∈ P ^ (m + 1) := by
    exact Ideal.sub_mem (P ^ (m + 1)) hb ha
  have hmul : (a - b) * π ^ m ∈ P ^ (m + 1) := by
    convert hdiff using 1
    ring
  exact
    ideal_generator_succ
      P hm hπ_mem hπ_not_sq hmul

noncomputable def number_coefficient_scalar
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (P : Ideal (NumberField.RingOfIntegers L)) (n : ℕ)
    (π : NumberField.RingOfIntegers L)
    (hgraded_spans : ∀ x : NumberField.RingOfIntegers L,
      x ∈ P ^ (n + 1) →
        ∃ a : NumberField.RingOfIntegers L,
          x - a * π ^ (n + 1) ∈ P ^ (n + 2))
    (σ : field_higher_ramification (L := L) P n) :
    NumberField.RingOfIntegers L :=
  Classical.choose
    (hgraded_spans
      ((((σ : field_higher_ramification (L := L) P n) :
          P.inertia (Gal(L/ℚ))) : Gal(L/ℚ)) • π - π)
      (by exact σ.property π))

lemma number_scalar_spec
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (P : Ideal (NumberField.RingOfIntegers L)) (n : ℕ)
    (π : NumberField.RingOfIntegers L)
    (hgraded_spans : ∀ x : NumberField.RingOfIntegers L,
      x ∈ P ^ (n + 1) →
        ∃ a : NumberField.RingOfIntegers L,
          x - a * π ^ (n + 1) ∈ P ^ (n + 2))
    (σ : field_higher_ramification (L := L) P n) :
    ((((σ : field_higher_ramification (L := L) P n) :
        P.inertia (Gal(L/ℚ))) : Gal(L/ℚ)) • π - π) -
      number_coefficient_scalar
        (L := L) P n π hgraded_spans σ * π ^ (n + 1) ∈ P ^ (n + 2) := by
  classical
  exact
    Classical.choose_spec
      (hgraded_spans
        ((((σ : field_higher_ramification (L := L) P n) :
            P.inertia (Gal(L/ℚ))) : Gal(L/ℚ)) • π - π)
        (by exact σ.property π))

lemma number_scalar_unique
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    {q : ℕ} (hq : Nat.Prime q)
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)]
    {π x a b : NumberField.RingOfIntegers L} {n : ℕ}
    (hπ_mem : π ∈ P)
    (hπ_not_sq : π ∉ P ^ 2)
    (ha : x - a * π ^ (n + 1) ∈ P ^ (n + 2))
    (hb : x - b * π ^ (n + 1) ∈ P ^ (n + 2)) :
    a - b ∈ P := by
  classical
  letI : P.IsMaximal :=
    number_above_maximal (L := L) hq P
  exact
    scalar_unique_mod
      (P := P) (π := π) (x := x) (a := a) (b := b)
      (m := n + 1) (Nat.succ_pos n) hπ_mem hπ_not_sq ha hb

lemma ramification_coefficient_scalar
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    {q : ℕ} (hq : Nat.Prime q)
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)]
    {n : ℕ}
    (π : NumberField.RingOfIntegers L)
    (hπ_mem : π ∈ P)
    (hπ_not_sq : π ∉ P ^ 2)
    (hgraded_spans : ∀ x : NumberField.RingOfIntegers L,
      x ∈ P ^ (n + 1) →
        ∃ a : NumberField.RingOfIntegers L,
          x - a * π ^ (n + 1) ∈ P ^ (n + 2)) :
    number_coefficient_scalar
      (L := L) P n π hgraded_spans
      (1 : field_higher_ramification (L := L) P n) ∈ P := by
  classical
  have hspec :
      (((((1 : field_higher_ramification (L := L) P n) :
          P.inertia (Gal(L/ℚ))) : Gal(L/ℚ)) • π - π) -
        (number_coefficient_scalar
            (L := L) P n π hgraded_spans
            (1 : field_higher_ramification (L := L) P n) *
          π ^ (n + 1))) ∈ P ^ (n + 2) := by
    exact
      number_scalar_spec
        (L := L) P n π hgraded_spans
        (1 : field_higher_ramification (L := L) P n)
  have hzero :
      (((((1 : field_higher_ramification (L := L) P n) :
          P.inertia (Gal(L/ℚ))) : Gal(L/ℚ)) • π - π) -
        (0 * π ^ (n + 1))) ∈ P ^ (n + 2) := by
    simp
  have hdiff :
      number_coefficient_scalar
          (L := L) P n π hgraded_spans
          (1 : field_higher_ramification (L := L) P n) - 0 ∈ P := by
    exact
      number_scalar_unique
        (L := L) hq P hπ_mem hπ_not_sq hspec hzero
  simpa using hdiff

lemma higher_ramification_smul
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (P : Ideal (NumberField.RingOfIntegers L))
    {n : ℕ} (hn : 1 ≤ n)
    (π c : NumberField.RingOfIntegers L)
    (hπ_mem : π ∈ P)
    (σ : field_higher_ramification (L := L) P n) :
    (((σ : field_higher_ramification (L := L) P n) :
        P.inertia (Gal(L/ℚ))) : Gal(L/ℚ)) • (c * π ^ (n + 1)) -
      c * π ^ (n + 1) ∈ P ^ (n + 2) := by
  classical
  let σI : P.inertia (Gal(L/ℚ)) :=
    (σ : field_higher_ramification (L := L) P n)
  have hc_sub :
      ((σI : Gal(L/ℚ)) • c) - c ∈ P ^ (n + 1) := by
    exact σ.property c
  have hσπ_sub :
      ((σI : Gal(L/ℚ)) • π) - π ∈ P ^ (n + 1) := by
    exact σ.property π
  have hσπ_mem : ((σI : Gal(L/ℚ)) • π) ∈ P := by
    exact number_smul_prime (L := L) P σI hπ_mem
  have hσπ_pow_mem : ((σI : Gal(L/ℚ)) • π) ^ (n + 1) ∈ P ^ (n + 1) :=
    Ideal.pow_mem_pow hσπ_mem (n + 1)
  have hterm_coeff :
      (((σI : Gal(L/ℚ)) • c) - c) *
        (((σI : Gal(L/ℚ)) • π) ^ (n + 1)) ∈ P ^ (n + 2) := by
    have hmul := Ideal.mul_mem_mul hc_sub hσπ_pow_mem
    have hle : P ^ ((n + 1) + (n + 1)) ≤ P ^ (n + 2) := by
      exact Ideal.pow_le_pow_right (by omega : n + 2 ≤ (n + 1) + (n + 1))
    exact hle (by
      simpa [pow_add] using hmul)
  have hpow_diff :
      ((σI : Gal(L/ℚ)) • π) ^ (n + 1) - π ^ (n + 1) ∈ P ^ (n + 2) := by
    exact
      ideal_succ_sub
        P hn hσπ_mem hπ_mem hσπ_sub
  have hterm_pow :
      c * (((σI : Gal(L/ℚ)) • π) ^ (n + 1) - π ^ (n + 1)) ∈
        P ^ (n + 2) := by
    exact Ideal.mul_mem_left (P ^ (n + 2)) c hpow_diff
  have hsum :
      (((σI : Gal(L/ℚ)) • c) - c) *
          (((σI : Gal(L/ℚ)) • π) ^ (n + 1)) +
        c * (((σI : Gal(L/ℚ)) • π) ^ (n + 1) - π ^ (n + 1)) ∈
          P ^ (n + 2) :=
    Ideal.add_mem (P ^ (n + 2)) hterm_coeff hterm_pow
  change
    ((σI : Gal(L/ℚ)) • (c * π ^ (n + 1))) -
      c * π ^ (n + 1) ∈ P ^ (n + 2)
  convert hsum using 1
  simp [smul_mul']
  ring

lemma number_higher_ramification
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    {q : ℕ} (hq : Nat.Prime q)
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)]
    {n : ℕ} (hn : 1 ≤ n)
    (π : NumberField.RingOfIntegers L)
    (hπ_mem : π ∈ P)
    (hπ_not_sq : π ∉ P ^ 2)
    (hgraded_spans : ∀ x : NumberField.RingOfIntegers L,
      x ∈ P ^ (n + 1) →
        ∃ a : NumberField.RingOfIntegers L,
          x - a * π ^ (n + 1) ∈ P ^ (n + 2))
    (σ τ : field_higher_ramification (L := L) P n) :
    number_coefficient_scalar
        (L := L) P n π hgraded_spans (σ * τ) -
      (number_coefficient_scalar
          (L := L) P n π hgraded_spans σ +
        number_coefficient_scalar
          (L := L) P n π hgraded_spans τ) ∈ P := by
  classical
  let σI : P.inertia (Gal(L/ℚ)) :=
    (σ : field_higher_ramification (L := L) P n)
  let τI : P.inertia (Gal(L/ℚ)) :=
    (τ : field_higher_ramification (L := L) P n)
  let aστ : NumberField.RingOfIntegers L :=
    number_coefficient_scalar
      (L := L) P n π hgraded_spans (σ * τ)
  let aσ : NumberField.RingOfIntegers L :=
    number_coefficient_scalar
      (L := L) P n π hgraded_spans σ
  let aτ : NumberField.RingOfIntegers L :=
    number_coefficient_scalar
      (L := L) P n π hgraded_spans τ
  have hστ :
      ((((σ * τ : field_higher_ramification (L := L) P n) :
          P.inertia (Gal(L/ℚ))) : Gal(L/ℚ)) • π - π) -
        aστ * π ^ (n + 1) ∈ P ^ (n + 2) := by
    simpa [aστ] using
      number_scalar_spec
        (L := L) P n π hgraded_spans (σ * τ)
  have hσ :
      ((σI : Gal(L/ℚ)) • π - π) - aσ * π ^ (n + 1) ∈ P ^ (n + 2) := by
    simpa [σI, aσ] using
      number_scalar_spec
        (L := L) P n π hgraded_spans σ
  have hτ :
      ((τI : Gal(L/ℚ)) • π - π) - aτ * π ^ (n + 1) ∈ P ^ (n + 2) := by
    simpa [τI, aτ] using
      number_scalar_spec
        (L := L) P n π hgraded_spans τ
  have hτ_smul :
      (σI : Gal(L/ℚ)) • (((τI : Gal(L/ℚ)) • π - π) -
          aτ * π ^ (n + 1)) ∈ P ^ (n + 2) := by
    exact number_smul_pow (L := L) P σI (n + 2) hτ
  have hterm :
      (σI : Gal(L/ℚ)) • (aτ * π ^ (n + 1)) -
          aτ * π ^ (n + 1) ∈ P ^ (n + 2) := by
    exact
      higher_ramification_smul
        (L := L) P hn π aτ hπ_mem σ
  have hcandidate :
      ((((σ * τ : field_higher_ramification (L := L) P n) :
          P.inertia (Gal(L/ℚ))) : Gal(L/ℚ)) • π - π) -
        (aσ + aτ) * π ^ (n + 1) ∈ P ^ (n + 2) := by
    have hsum :
        (σI : Gal(L/ℚ)) • (((τI : Gal(L/ℚ)) • π - π) -
            aτ * π ^ (n + 1)) +
          ((σI : Gal(L/ℚ)) • (aτ * π ^ (n + 1)) -
            aτ * π ^ (n + 1)) +
          (((σI : Gal(L/ℚ)) • π - π) - aσ * π ^ (n + 1)) ∈
            P ^ (n + 2) := by
      exact Ideal.add_mem (P ^ (n + 2))
        (Ideal.add_mem (P ^ (n + 2)) hτ_smul hterm)
        hσ
    convert hsum using 1
    simp [σI, τI, mul_smul, smul_sub]
    ring
  have huniq :
      aστ - (aσ + aτ) ∈ P := by
    exact
      number_scalar_unique
        (L := L) hq P hπ_mem hπ_not_sq hστ hcandidate
  simpa [aστ, aσ, aτ] using huniq

noncomputable def number_higher_displacement
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (P : Ideal (NumberField.RingOfIntegers L)) (n : ℕ)
    (π : NumberField.RingOfIntegers L)
    (hgraded_spans : ∀ x : NumberField.RingOfIntegers L,
      x ∈ P ^ (n + 1) →
        ∃ a : NumberField.RingOfIntegers L,
          x - a * π ^ (n + 1) ∈ P ^ (n + 2))
    (σ : field_higher_ramification (L := L) P n)
    (x : NumberField.RingOfIntegers L) :
    NumberField.RingOfIntegers L :=
  Classical.choose
    (hgraded_spans
      ((((σ : field_higher_ramification (L := L) P n) :
          P.inertia (Gal(L/ℚ))) : Gal(L/ℚ)) • x - x)
      (by exact σ.property x))

lemma displacement_scalar_spec
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (P : Ideal (NumberField.RingOfIntegers L)) (n : ℕ)
    (π : NumberField.RingOfIntegers L)
    (hgraded_spans : ∀ x : NumberField.RingOfIntegers L,
      x ∈ P ^ (n + 1) →
        ∃ a : NumberField.RingOfIntegers L,
          x - a * π ^ (n + 1) ∈ P ^ (n + 2))
    (σ : field_higher_ramification (L := L) P n)
    (x : NumberField.RingOfIntegers L) :
    ((((σ : field_higher_ramification (L := L) P n) :
        P.inertia (Gal(L/ℚ))) : Gal(L/ℚ)) • x - x) -
      number_higher_displacement
        (L := L) P n π hgraded_spans σ x * π ^ (n + 1) ∈ P ^ (n + 2) := by
  classical
  exact
    Classical.choose_spec
      (hgraded_spans
        ((((σ : field_higher_ramification (L := L) P n) :
            P.inertia (Gal(L/ℚ))) : Gal(L/ℚ)) • x - x)
        (by exact σ.property x))

lemma higher_displacement_scalar
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    {q : ℕ} (hq : Nat.Prime q)
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)]
    {n : ℕ}
    (π : NumberField.RingOfIntegers L)
    (hπ_mem : π ∈ P)
    (hπ_not_sq : π ∉ P ^ 2)
    (hgraded_spans : ∀ x : NumberField.RingOfIntegers L,
      x ∈ P ^ (n + 1) →
        ∃ a : NumberField.RingOfIntegers L,
          x - a * π ^ (n + 1) ∈ P ^ (n + 2))
    (σ : field_higher_ramification (L := L) P n)
    (x y : NumberField.RingOfIntegers L) :
    number_higher_displacement
        (L := L) P n π hgraded_spans σ (x + y) -
      (number_higher_displacement
          (L := L) P n π hgraded_spans σ x +
        number_higher_displacement
          (L := L) P n π hgraded_spans σ y) ∈ P := by
  classical
  let ax : NumberField.RingOfIntegers L :=
    number_higher_displacement
      (L := L) P n π hgraded_spans σ x
  let ay : NumberField.RingOfIntegers L :=
    number_higher_displacement
      (L := L) P n π hgraded_spans σ y
  let axy : NumberField.RingOfIntegers L :=
    number_higher_displacement
      (L := L) P n π hgraded_spans σ (x + y)
  have hx :
      ((((σ : field_higher_ramification (L := L) P n) :
          P.inertia (Gal(L/ℚ))) : Gal(L/ℚ)) • x - x) -
        ax * π ^ (n + 1) ∈ P ^ (n + 2) := by
    simpa [ax] using
      displacement_scalar_spec
        (L := L) P n π hgraded_spans σ x
  have hy :
      ((((σ : field_higher_ramification (L := L) P n) :
          P.inertia (Gal(L/ℚ))) : Gal(L/ℚ)) • y - y) -
        ay * π ^ (n + 1) ∈ P ^ (n + 2) := by
    simpa [ay] using
      displacement_scalar_spec
        (L := L) P n π hgraded_spans σ y
  have hxy :
      ((((σ : field_higher_ramification (L := L) P n) :
          P.inertia (Gal(L/ℚ))) : Gal(L/ℚ)) • (x + y) - (x + y)) -
        axy * π ^ (n + 1) ∈ P ^ (n + 2) := by
    simpa [axy] using
      displacement_scalar_spec
        (L := L) P n π hgraded_spans σ (x + y)
  have hcandidate :
      ((((σ : field_higher_ramification (L := L) P n) :
          P.inertia (Gal(L/ℚ))) : Gal(L/ℚ)) • (x + y) - (x + y)) -
        (ax + ay) * π ^ (n + 1) ∈ P ^ (n + 2) := by
    have hsum :
        (((((σ : field_higher_ramification (L := L) P n) :
            P.inertia (Gal(L/ℚ))) : Gal(L/ℚ)) • x - x) -
          ax * π ^ (n + 1)) +
        (((((σ : field_higher_ramification (L := L) P n) :
            P.inertia (Gal(L/ℚ))) : Gal(L/ℚ)) • y - y) -
          ay * π ^ (n + 1)) ∈ P ^ (n + 2) :=
      Ideal.add_mem (P ^ (n + 2)) hx hy
    convert hsum using 1
    rw [smul_add]
    ring
  have huniq :
      axy - (ax + ay) ∈ P := by
    exact
      number_scalar_unique
        (L := L) hq P hπ_mem hπ_not_sq hxy hcandidate
  simpa [axy, ax, ay] using huniq

lemma higher_ramification_displacement
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    {q : ℕ} (hq : Nat.Prime q)
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)]
    {n : ℕ} (hn : 1 ≤ n)
    (π : NumberField.RingOfIntegers L)
    (hπ_mem : π ∈ P)
    (hπ_not_sq : π ∉ P ^ 2)
    (hgraded_spans : ∀ x : NumberField.RingOfIntegers L,
      x ∈ P ^ (n + 1) →
        ∃ a : NumberField.RingOfIntegers L,
          x - a * π ^ (n + 1) ∈ P ^ (n + 2))
    (σ : field_higher_ramification (L := L) P n)
    (x y : NumberField.RingOfIntegers L) :
    number_higher_displacement
        (L := L) P n π hgraded_spans σ (x * y) -
      (x * number_higher_displacement
          (L := L) P n π hgraded_spans σ y +
        y * number_higher_displacement
          (L := L) P n π hgraded_spans σ x) ∈ P := by
  classical
  let σI : P.inertia (Gal(L/ℚ)) :=
    (σ : field_higher_ramification (L := L) P n)
  let ax : NumberField.RingOfIntegers L :=
    number_higher_displacement
      (L := L) P n π hgraded_spans σ x
  let ay : NumberField.RingOfIntegers L :=
    number_higher_displacement
      (L := L) P n π hgraded_spans σ y
  let axy : NumberField.RingOfIntegers L :=
    number_higher_displacement
      (L := L) P n π hgraded_spans σ (x * y)
  have hx :
      ((σI : Gal(L/ℚ)) • x - x) - ax * π ^ (n + 1) ∈ P ^ (n + 2) := by
    simpa [σI, ax] using
      displacement_scalar_spec
        (L := L) P n π hgraded_spans σ x
  have hy :
      ((σI : Gal(L/ℚ)) • y - y) - ay * π ^ (n + 1) ∈ P ^ (n + 2) := by
    simpa [σI, ay] using
      displacement_scalar_spec
        (L := L) P n π hgraded_spans σ y
  have hxy :
      ((σI : Gal(L/ℚ)) • (x * y) - x * y) - axy * π ^ (n + 1) ∈
        P ^ (n + 2) := by
    simpa [σI, axy] using
      displacement_scalar_spec
        (L := L) P n π hgraded_spans σ (x * y)
  have hdx : (σI : Gal(L/ℚ)) • x - x ∈ P ^ (n + 1) := by
    exact σ.property x
  have hdy : (σI : Gal(L/ℚ)) • y - y ∈ P ^ (n + 1) := by
    exact σ.property y
  have hdxdy :
      ((σI : Gal(L/ℚ)) • x - x) * ((σI : Gal(L/ℚ)) • y - y) ∈ P ^ (n + 2) := by
    have hmul := Ideal.mul_mem_mul hdx hdy
    have hle : P ^ ((n + 1) + (n + 1)) ≤ P ^ (n + 2) := by
      exact Ideal.pow_le_pow_right (by omega : n + 2 ≤ (n + 1) + (n + 1))
    exact hle (by simpa [pow_add] using hmul)
  have hcandidate :
      ((σI : Gal(L/ℚ)) • (x * y) - x * y) -
        (x * ay + y * ax) * π ^ (n + 1) ∈ P ^ (n + 2) := by
    have hsum :
        x * (((σI : Gal(L/ℚ)) • y - y) - ay * π ^ (n + 1)) +
          y * (((σI : Gal(L/ℚ)) • x - x) - ax * π ^ (n + 1)) +
          ((σI : Gal(L/ℚ)) • x - x) * ((σI : Gal(L/ℚ)) • y - y) ∈
            P ^ (n + 2) :=
      Ideal.add_mem (P ^ (n + 2))
        (Ideal.add_mem (P ^ (n + 2))
          (Ideal.mul_mem_left (P ^ (n + 2)) x hy)
          (Ideal.mul_mem_left (P ^ (n + 2)) y hx))
        hdxdy
    convert hsum using 1
    rw [smul_mul']
    ring
  have huniq :
      axy - (x * ay + y * ax) ∈ P := by
    exact
      number_scalar_unique
        (L := L) hq P hπ_mem hπ_not_sq hxy hcandidate
  simpa [axy, ax, ay] using huniq

lemma ideal_span_set
    {A : Type*} [CommSemiring A] (I J : Ideal A) :
    I * J = Ideal.span ((I : Set A) * (J : Set A)) := by
  classical
  ext x
  constructor
  · intro hx
    exact
      (Ideal.mul_le.mpr (fun a ha b hb =>
        Ideal.subset_span (Set.mul_mem_mul ha hb))) hx
  · intro hx
    exact
      (Ideal.mem_span x).1 hx (I * J) (by
        intro z hz
        rcases (Set.mem_mul).1 hz with ⟨a, ha, b, hb, rfl⟩
        exact Ideal.mul_mem_mul ha hb)

lemma square_induction_span
    {A : Type*} [CommRing A] (P : Ideal A) {F : A → Prop}
    (hzero : F 0)
    (hadd : ∀ x y : A, F x → F y → F (x + y))
    (hsmul : ∀ r x : A, x ∈ P ^ 2 → F x → F (r * x))
    (hprod : ∀ a b : A, a ∈ P → b ∈ P → F (a * b))
    {x : A} (hx : x ∈ P ^ 2) :
    F x := by
  classical
  have hxmul : x ∈ P * P := by
    simpa [pow_two] using hx
  have hxspan : x ∈ Ideal.span ((P : Set A) * (P : Set A)) := by
    simpa [ideal_span_set (I := P) (J := P)] using hxmul
  change x ∈ Submodule.span A ((P : Set A) * (P : Set A)) at hxspan
  refine
    Submodule.span_induction
      (p := fun y _hy => F y) ?mem ?zero ?add ?smul hxspan
  · intro y hy
    rcases (Set.mem_mul).1 hy with ⟨a, ha, b, hb, rfl⟩
    exact hprod a b ha hb
  · exact hzero
  · intro y z _hy _hz hFy hFz
    exact hadd y z hFy hFz
  · intro r y hy hFy
    have hyIdeal : y ∈ Ideal.span ((P : Set A) * (P : Set A)) := by
      change y ∈ Submodule.span A ((P : Set A) * (P : Set A))
      exact hy
    have hymul : y ∈ P * P := by
      simpa [ideal_span_set (I := P) (J := P)] using hyIdeal
    have hy_sq : y ∈ P ^ 2 := by
      simpa [pow_two] using hymul
    exact hsmul r y hy_sq hFy

lemma displacement_scalar_sq
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    {q : ℕ} (hq : Nat.Prime q)
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)]
    {n : ℕ} (hn : 1 ≤ n)
    (π : NumberField.RingOfIntegers L)
    (hπ_mem : π ∈ P)
    (hπ_not_sq : π ∉ P ^ 2)
    (hgraded_spans : ∀ x : NumberField.RingOfIntegers L,
      x ∈ P ^ (n + 1) →
        ∃ a : NumberField.RingOfIntegers L,
          x - a * π ^ (n + 1) ∈ P ^ (n + 2))
    (σ : field_higher_ramification (L := L) P n)
    {x : NumberField.RingOfIntegers L}
    (hx : x ∈ P ^ 2) :
    number_higher_displacement
      (L := L) P n π hgraded_spans σ x ∈ P := by
  classical
  let c : NumberField.RingOfIntegers L → NumberField.RingOfIntegers L :=
    fun y =>
      number_higher_displacement
        (L := L) P n π hgraded_spans σ y
  refine square_induction_span
    (P := P) (F := fun y => c y ∈ P) ?zero ?add ?smul ?prod hx
  · have hspec :
        (((((σ : field_higher_ramification (L := L) P n) :
            P.inertia (Gal(L/ℚ))) : Gal(L/ℚ)) • 0 - 0) -
          c 0 * π ^ (n + 1)) ∈ P ^ (n + 2) := by
      simpa [c] using
        displacement_scalar_spec
          (L := L) P n π hgraded_spans σ 0
    have hzero :
        (((((σ : field_higher_ramification (L := L) P n) :
            P.inertia (Gal(L/ℚ))) : Gal(L/ℚ)) • 0 - 0) -
          0 * π ^ (n + 1)) ∈ P ^ (n + 2) := by
      simp
    have hdiff : c 0 - 0 ∈ P := by
      exact
        number_scalar_unique
          (L := L) hq P hπ_mem hπ_not_sq hspec hzero
    simpa [c] using hdiff
  · intro y z hy hz
    have hadd :
        c (y + z) - (c y + c z) ∈ P := by
      simpa [c] using
        higher_displacement_scalar
          (L := L) hq P π hπ_mem hπ_not_sq hgraded_spans σ y z
    have hterms : c y + c z ∈ P :=
      Ideal.add_mem P hy hz
    have hsum : (c (y + z) - (c y + c z)) + (c y + c z) ∈ P :=
      Ideal.add_mem P hadd hterms
    convert hsum using 1
    ring_nf
  · intro r y hy_sq hy
    have hmul :
        c (r * y) - (r * c y + y * c r) ∈ P := by
      simpa [c] using
        higher_ramification_displacement
          (L := L) hq P hn π hπ_mem hπ_not_sq hgraded_spans σ r y
    have hyP : y ∈ P := by
      have hyP_one : y ∈ P ^ 1 :=
        (Ideal.pow_le_pow_right (by norm_num : 1 ≤ 2)) hy_sq
      simpa using hyP_one
    have hleft : r * c y ∈ P :=
      Ideal.mul_mem_left P r hy
    have hright : y * c r ∈ P :=
      Ideal.mul_mem_right (c r) P hyP
    have hterms : r * c y + y * c r ∈ P :=
      Ideal.add_mem P hleft hright
    have hsum : (c (r * y) - (r * c y + y * c r)) +
        (r * c y + y * c r) ∈ P :=
      Ideal.add_mem P hmul hterms
    convert hsum using 1
    ring_nf
  · intro a b ha hb
    have hmul :
        c (a * b) - (a * c b + b * c a) ∈ P := by
      simpa [c] using
        higher_ramification_displacement
          (L := L) hq P hn π hπ_mem hπ_not_sq hgraded_spans σ a b
    have hleft : a * c b ∈ P :=
      Ideal.mul_mem_right (c b) P ha
    have hright : b * c a ∈ P :=
      Ideal.mul_mem_right (c a) P hb
    have hterms : a * c b + b * c a ∈ P :=
      Ideal.add_mem P hleft hright
    have hsum : (c (a * b) - (a * c b + b * c a)) +
        (a * c b + b * c a) ∈ P :=
      Ideal.add_mem P hmul hterms
    convert hsum using 1
    ring_nf

lemma displacement_uniformizer_fixed
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    {q : ℕ} (hq : Nat.Prime q)
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)]
    {n : ℕ} (hn : 1 ≤ n)
    (π : NumberField.RingOfIntegers L)
    (hπ_mem : π ∈ P)
    (hπ_not_sq : π ∉ P ^ 2)
    (hgraded_spans : ∀ x : NumberField.RingOfIntegers L,
      x ∈ P ^ (n + 1) →
        ∃ a : NumberField.RingOfIntegers L,
          x - a * π ^ (n + 1) ∈ P ^ (n + 2))
    (σ : field_higher_ramification (L := L) P n)
    (hπ_fixed :
      ((((σ : field_higher_ramification (L := L) P n) :
          P.inertia (Gal(L/ℚ))) : Gal(L/ℚ)) • π - π) ∈ P ^ (n + 2))
    {x : NumberField.RingOfIntegers L}
    (hx : x ∈ P) :
    number_higher_displacement
      (L := L) P n π hgraded_spans σ x ∈ P := by
  classical
  let c : NumberField.RingOfIntegers L → NumberField.RingOfIntegers L :=
    fun y =>
      number_higher_displacement
        (L := L) P n π hgraded_spans σ y
  obtain ⟨b, hb⟩ :=
    cotangent_spans_sq
      (L := L) hq P π hπ_mem hπ_not_sq x hx
  have hcπ : c π ∈ P := by
    have hspec :
        (((((σ : field_higher_ramification (L := L) P n) :
            P.inertia (Gal(L/ℚ))) : Gal(L/ℚ)) • π - π) -
          c π * π ^ (n + 1)) ∈ P ^ (n + 2) := by
      simpa [c] using
        displacement_scalar_spec
          (L := L) P n π hgraded_spans σ π
    have hzero :
        (((((σ : field_higher_ramification (L := L) P n) :
            P.inertia (Gal(L/ℚ))) : Gal(L/ℚ)) • π - π) -
          0 * π ^ (n + 1)) ∈ P ^ (n + 2) := by
      simpa using hπ_fixed
    have hdiff : c π - 0 ∈ P := by
      exact
        number_scalar_unique
          (L := L) hq P hπ_mem hπ_not_sq hspec hzero
    simpa [c] using hdiff
  have herror : c (x - b * π) ∈ P := by
    exact
      displacement_scalar_sq
        (L := L) hq P hn π hπ_mem hπ_not_sq hgraded_spans σ hb
  have hproduct : c (b * π) ∈ P := by
    have hmul :
        c (b * π) - (b * c π + π * c b) ∈ P := by
      simpa [c] using
        higher_ramification_displacement
          (L := L) hq P hn π hπ_mem hπ_not_sq hgraded_spans σ b π
    have hleft : b * c π ∈ P :=
      Ideal.mul_mem_left P b hcπ
    have hright : π * c b ∈ P :=
      Ideal.mul_mem_right (c b) P hπ_mem
    have hterms : b * c π + π * c b ∈ P :=
      Ideal.add_mem P hleft hright
    have hsum : (c (b * π) - (b * c π + π * c b)) +
        (b * c π + π * c b) ∈ P :=
      Ideal.add_mem P hmul hterms
    convert hsum using 1
    ring_nf
  have hadd :
      c ((x - b * π) + b * π) - (c (x - b * π) + c (b * π)) ∈ P := by
    simpa [c] using
      higher_displacement_scalar
        (L := L) hq P π hπ_mem hπ_not_sq hgraded_spans σ
        (x - b * π) (b * π)
  have hterms : c (x - b * π) + c (b * π) ∈ P :=
    Ideal.add_mem P herror hproduct
  have hsum : (c ((x - b * π) + b * π) -
      (c (x - b * π) + c (b * π))) +
      (c (x - b * π) + c (b * π)) ∈ P :=
    Ideal.add_mem P hadd hterms
  change c x ∈ P
  convert hsum using 1
  ring_nf

lemma ramification_displacement_scalar
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    {q : ℕ} (hq : Nat.Prime q)
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)]
    {n : ℕ} (hn : 1 ≤ n)
    (π : NumberField.RingOfIntegers L)
    (hπ_mem : π ∈ P)
    (hπ_not_sq : π ∉ P ^ 2)
    (hgraded_spans : ∀ x : NumberField.RingOfIntegers L,
      x ∈ P ^ (n + 1) →
        ∃ a : NumberField.RingOfIntegers L,
          x - a * π ^ (n + 1) ∈ P ^ (n + 2))
    (σ : field_higher_ramification (L := L) P n)
    (hπ_fixed :
      ((((σ : field_higher_ramification (L := L) P n) :
          P.inertia (Gal(L/ℚ))) : Gal(L/ℚ)) • π - π) ∈ P ^ (n + 2))
    {x y : NumberField.RingOfIntegers L}
    (hxy : x - y ∈ P) :
    algebraMap (NumberField.RingOfIntegers L) P.ResidueField
        (number_higher_displacement
          (L := L) P n π hgraded_spans σ x) =
    algebraMap (NumberField.RingOfIntegers L) P.ResidueField
        (number_higher_displacement
          (L := L) P n π hgraded_spans σ y) := by
  classical
  let c : NumberField.RingOfIntegers L → NumberField.RingOfIntegers L :=
    fun z =>
      number_higher_displacement
        (L := L) P n π hgraded_spans σ z
  have hcz : c (x - y) ∈ P := by
    exact
      displacement_uniformizer_fixed
        (L := L) hq P hn π hπ_mem hπ_not_sq hgraded_spans σ hπ_fixed hxy
  have hadd :
      c (y + (x - y)) - (c y + c (x - y)) ∈ P := by
    simpa [c] using
      higher_displacement_scalar
        (L := L) hq P π hπ_mem hπ_not_sq hgraded_spans σ y (x - y)
  have hdiff : c x - c y ∈ P := by
    have hsum :
        (c (y + (x - y)) - (c y + c (x - y))) + c (x - y) ∈ P := by
      exact Ideal.add_mem P hadd hcz
    convert hsum using 1
    ring_nf
  have hres := residue_field_sub (I := P) hdiff
  change
    algebraMap (NumberField.RingOfIntegers L) P.ResidueField (c x) =
      algebraMap (NumberField.RingOfIntegers L) P.ResidueField (c y)
  exact hres

lemma number_ramification_displacement
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    {q : ℕ} (hq : Nat.Prime q)
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)]
    {n : ℕ} (hn : 1 ≤ n)
    (π : NumberField.RingOfIntegers L)
    (hπ_mem : π ∈ P)
    (hπ_not_sq : π ∉ P ^ 2)
    (hgraded_spans : ∀ x : NumberField.RingOfIntegers L,
      x ∈ P ^ (n + 1) →
        ∃ a : NumberField.RingOfIntegers L,
          x - a * π ^ (n + 1) ∈ P ^ (n + 2))
    (σ : field_higher_ramification (L := L) P n)
    (x y : NumberField.RingOfIntegers L) :
    algebraMap (NumberField.RingOfIntegers L) P.ResidueField
        (number_higher_displacement
          (L := L) P n π hgraded_spans σ (x * y)) =
      algebraMap (NumberField.RingOfIntegers L) P.ResidueField x *
          algebraMap (NumberField.RingOfIntegers L) P.ResidueField
            (number_higher_displacement
              (L := L) P n π hgraded_spans σ y) +
        algebraMap (NumberField.RingOfIntegers L) P.ResidueField y *
          algebraMap (NumberField.RingOfIntegers L) P.ResidueField
            (number_higher_displacement
              (L := L) P n π hgraded_spans σ x) := by
  classical
  have hcoeff :
      number_higher_displacement
          (L := L) P n π hgraded_spans σ (x * y) -
        (x * number_higher_displacement
            (L := L) P n π hgraded_spans σ y +
          y * number_higher_displacement
            (L := L) P n π hgraded_spans σ x) ∈ P := by
    exact
      higher_ramification_displacement
        (L := L) hq P hn π hπ_mem hπ_not_sq hgraded_spans σ x y
  have hres :=
    residue_field_sub (I := P) hcoeff
  simpa [map_add, map_mul] using hres

lemma displacement_scalar_uniformizer
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    {q : ℕ} (hq : Nat.Prime q)
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)]
    {n : ℕ} (hn : 1 ≤ n)
    (π : NumberField.RingOfIntegers L)
    (hπ_mem : π ∈ P)
    (hπ_not_sq : π ∉ P ^ 2)
    (hgraded_spans : ∀ x : NumberField.RingOfIntegers L,
      x ∈ P ^ (n + 1) →
        ∃ a : NumberField.RingOfIntegers L,
          x - a * π ^ (n + 1) ∈ P ^ (n + 2))
    (σ : field_higher_ramification (L := L) P n)
    (hπ_fixed :
      ((((σ : field_higher_ramification (L := L) P n) :
          P.inertia (Gal(L/ℚ))) : Gal(L/ℚ)) • π - π) ∈ P ^ (n + 2))
    (x : NumberField.RingOfIntegers L) :
    algebraMap (NumberField.RingOfIntegers L) P.ResidueField
        (number_higher_displacement
          (L := L) P n π hgraded_spans σ x) = 0 := by
  classical
  letI : P.IsMaximal :=
    number_above_maximal (L := L) hq P
  let D : P.ResidueField → P.ResidueField := fun z =>
    algebraMap (NumberField.RingOfIntegers L) P.ResidueField
      (number_higher_displacement
        (L := L) P n π hgraded_spans σ
        (Classical.choose (Ideal.algebraMap_residueField_surjective P z)))
  have hD_rep :
      ∀ y : NumberField.RingOfIntegers L,
        D (algebraMap (NumberField.RingOfIntegers L) P.ResidueField y) =
          algebraMap (NumberField.RingOfIntegers L) P.ResidueField
            (number_higher_displacement
              (L := L) P n π hgraded_spans σ y) := by
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
          (number_higher_displacement
            (L := L) P n π hgraded_spans σ
            (Classical.choose
              (Ideal.algebraMap_residueField_surjective P
                (algebraMap (NumberField.RingOfIntegers L) P.ResidueField y)))) =
        algebraMap (NumberField.RingOfIntegers L) P.ResidueField
          (number_higher_displacement
            (L := L) P n π hgraded_spans σ y)
    exact
      ramification_displacement_scalar
        (L := L) hq P hn π hπ_mem hπ_not_sq hgraded_spans σ hπ_fixed hsub
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
          (number_higher_displacement
            (L := L) P n π hgraded_spans σ (x * y)) := by
            exact hD_rep (x * y)
      _ =
          algebraMap (NumberField.RingOfIntegers L) P.ResidueField x *
              algebraMap (NumberField.RingOfIntegers L) P.ResidueField
                (number_higher_displacement
                  (L := L) P n π hgraded_spans σ y) +
            algebraMap (NumberField.RingOfIntegers L) P.ResidueField y *
              algebraMap (NumberField.RingOfIntegers L) P.ResidueField
                (number_higher_displacement
                  (L := L) P n π hgraded_spans σ x) := by
            exact
              number_ramification_displacement
                (L := L) hq P hn π hπ_mem hπ_not_sq hgraded_spans σ x y
      _ =
          algebraMap (NumberField.RingOfIntegers L) P.ResidueField x *
              D (algebraMap (NumberField.RingOfIntegers L) P.ResidueField y) +
            algebraMap (NumberField.RingOfIntegers L) P.ResidueField y *
              D (algebraMap (NumberField.RingOfIntegers L) P.ResidueField x) := by
            rw [hD_rep y, hD_rep x]
  have hFiniteResidue :
      Finite P.ResidueField :=
    number_local_residue (L := L) hq P
  letI : Fintype P.ResidueField := Fintype.ofFinite P.ResidueField
  have hD_zero : ∀ z : P.ResidueField, D z = 0 :=
    derivation_like_zero D hD_mul
  calc
    algebraMap (NumberField.RingOfIntegers L) P.ResidueField
        (number_higher_displacement
          (L := L) P n π hgraded_spans σ x) =
        D (algebraMap (NumberField.RingOfIntegers L) P.ResidueField x) := by
          exact (hD_rep x).symm
    _ = 0 := by
          exact hD_zero (algebraMap (NumberField.RingOfIntegers L) P.ResidueField x)

lemma ramification_uniformizer_fixed
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    {q : ℕ} (hq : Nat.Prime q)
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)]
    {n : ℕ} (hn : 1 ≤ n)
    (π : NumberField.RingOfIntegers L)
    (hπ_mem : π ∈ P)
    (hπ_not_sq : π ∉ P ^ 2)
    (σ : field_higher_ramification (L := L) P n)
    (hπ_fixed :
      ((((σ : field_higher_ramification (L := L) P n) :
          P.inertia (Gal(L/ℚ))) : Gal(L/ℚ)) • π - π) ∈ P ^ (n + 2)) :
    σ ∈ number_higher_subgroup (L := L) P n := by
  classical
  letI : P.IsMaximal :=
    number_above_maximal (L := L) hq P
  obtain ⟨J, hπ_span, hJP_top⟩ :=
    dedekind_complement_sq P hπ_mem hπ_not_sq
  have hgraded_spans :
      ∀ x : NumberField.RingOfIntegers L,
        x ∈ P ^ (n + 1) →
          ∃ a : NumberField.RingOfIntegers L,
            x - a * π ^ (n + 1) ∈ P ^ (n + 2) := by
    intro x hx
    have hJpow_top : J ^ (n + 1) ⊔ P = ⊤ :=
      ideal_sup_top (J := J) (P := P) (n + 1) hJP_top
    simpa [Nat.add_assoc] using
      (cotangent_spans_complement
        (P := P) (J := J) (π := π) (x := x) (m := n + 1)
        hπ_span hJpow_top hx)
  rw [higher_ramification_subgroup (L := L) P n]
  intro x
  have hcoeff_zero :
      algebraMap (NumberField.RingOfIntegers L) P.ResidueField
          (number_higher_displacement
            (L := L) P n π hgraded_spans σ x) = 0 := by
    exact
      displacement_scalar_uniformizer
        (L := L) hq P hn π hπ_mem hπ_not_sq hgraded_spans σ hπ_fixed x
  have hcoeff_mem :
      number_higher_displacement
          (L := L) P n π hgraded_spans σ x ∈ P := by
    exact (Ideal.algebraMap_residueField_eq_zero (I := P)).1 hcoeff_zero
  have hspec :
      ((((σ : field_higher_ramification (L := L) P n) :
          P.inertia (Gal(L/ℚ))) : Gal(L/ℚ)) • x - x) -
        number_higher_displacement
          (L := L) P n π hgraded_spans σ x * π ^ (n + 1) ∈ P ^ (n + 2) := by
    exact
      displacement_scalar_spec
        (L := L) P n π hgraded_spans σ x
  have hπ_pow : π ^ (n + 1) ∈ P ^ (n + 1) :=
    Ideal.pow_mem_pow hπ_mem (n + 1)
  have hprod :
      number_higher_displacement
          (L := L) P n π hgraded_spans σ x * π ^ (n + 1) ∈ P ^ (n + 2) := by
    have hmul := Ideal.mul_mem_mul hcoeff_mem hπ_pow
    have hEq : P * P ^ (n + 1) = P ^ (n + 2) := by
      calc
        P * P ^ (n + 1) = P ^ 1 * P ^ (n + 1) := by
          rw [pow_one]
        _ = P ^ (1 + (n + 1)) := by
          rw [← pow_add]
        _ = P ^ (n + 2) := by
          congr 1
          omega
    simpa [hEq] using hmul
  have hsum :
      (((((σ : field_higher_ramification (L := L) P n) :
          P.inertia (Gal(L/ℚ))) : Gal(L/ℚ)) • x - x) -
        number_higher_displacement
          (L := L) P n π hgraded_spans σ x * π ^ (n + 1)) +
      number_higher_displacement
          (L := L) P n π hgraded_spans σ x * π ^ (n + 1) ∈ P ^ (n + 2) :=
    Ideal.add_mem (P ^ (n + 2)) hspec hprod
  convert hsum using 1
  ring

lemma number_ramification_scalar
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    {q : ℕ} (hq : Nat.Prime q)
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)]
    {n : ℕ} (hn : 1 ≤ n)
    (π : NumberField.RingOfIntegers L)
    (hπ_mem : π ∈ P)
    (hπ_not_sq : π ∉ P ^ 2)
    (hgraded_spans : ∀ x : NumberField.RingOfIntegers L,
      x ∈ P ^ (n + 1) →
        ∃ a : NumberField.RingOfIntegers L,
          x - a * π ^ (n + 1) ∈ P ^ (n + 2))
    (σ : field_higher_ramification (L := L) P n) :
    number_coefficient_scalar
        (L := L) P n π hgraded_spans σ ∈ P →
      σ ∈ number_higher_subgroup (L := L) P n := by
  classical
  intro hcoeff
  have hspec :
      ((((σ : field_higher_ramification (L := L) P n) :
          P.inertia (Gal(L/ℚ))) : Gal(L/ℚ)) • π - π) -
        number_coefficient_scalar
          (L := L) P n π hgraded_spans σ * π ^ (n + 1) ∈ P ^ (n + 2) := by
    exact
      number_scalar_spec
        (L := L) P n π hgraded_spans σ
  have hπ_pow : π ^ (n + 1) ∈ P ^ (n + 1) :=
    Ideal.pow_mem_pow hπ_mem (n + 1)
  have hprod :
      number_coefficient_scalar
          (L := L) P n π hgraded_spans σ * π ^ (n + 1) ∈ P ^ (n + 2) := by
    have hmul := Ideal.mul_mem_mul hcoeff hπ_pow
    have hEq : P * P ^ (n + 1) = P ^ (n + 2) := by
      calc
        P * P ^ (n + 1) = P ^ 1 * P ^ (n + 1) := by
          rw [pow_one]
        _ = P ^ (1 + (n + 1)) := by
          rw [← pow_add]
        _ = P ^ (n + 2) := by
          congr 1
          omega
    simpa [hEq] using hmul
  have hπ_fixed :
      ((((σ : field_higher_ramification (L := L) P n) :
          P.inertia (Gal(L/ℚ))) : Gal(L/ℚ)) • π - π) ∈ P ^ (n + 2) := by
    have hsum :
        (((((σ : field_higher_ramification (L := L) P n) :
            P.inertia (Gal(L/ℚ))) : Gal(L/ℚ)) • π - π) -
          number_coefficient_scalar
            (L := L) P n π hgraded_spans σ * π ^ (n + 1)) +
        number_coefficient_scalar
            (L := L) P n π hgraded_spans σ * π ^ (n + 1) ∈ P ^ (n + 2) :=
      Ideal.add_mem (P ^ (n + 2)) hspec hprod
    convert hsum using 1
    ring
  exact
    ramification_uniformizer_fixed
      (L := L) hq P hn π hπ_mem hπ_not_sq σ hπ_fixed

lemma number_higher_scalar
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    {q : ℕ} (hq : Nat.Prime q)
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)]
    {n : ℕ} (_hn : 1 ≤ n)
    (π : NumberField.RingOfIntegers L)
    (hπ_mem : π ∈ P)
    (hπ_not_sq : π ∉ P ^ 2)
    (hgraded_spans : ∀ x : NumberField.RingOfIntegers L,
      x ∈ P ^ (n + 1) →
        ∃ a : NumberField.RingOfIntegers L,
          x - a * π ^ (n + 1) ∈ P ^ (n + 2))
    (σ : field_higher_ramification (L := L) P n)
    (hσ : σ ∈ number_higher_subgroup (L := L) P n) :
    number_coefficient_scalar
        (L := L) P n π hgraded_spans σ ∈ P := by
  classical
  have hspec :
      ((((σ : field_higher_ramification (L := L) P n) :
          P.inertia (Gal(L/ℚ))) : Gal(L/ℚ)) • π - π) -
        number_coefficient_scalar
          (L := L) P n π hgraded_spans σ * π ^ (n + 1) ∈ P ^ (n + 2) := by
    exact
      number_scalar_spec
        (L := L) P n π hgraded_spans σ
  have hσ_succ :
      ((σ : field_higher_ramification (L := L) P n) :
        P.inertia (Gal(L/ℚ))) ∈
        field_higher_ramification (L := L) P (n + 1) := by
    exact
      (higher_ramification_subgroup
        (L := L) P n σ).1 hσ
  have hzero :
      ((((σ : field_higher_ramification (L := L) P n) :
          P.inertia (Gal(L/ℚ))) : Gal(L/ℚ)) • π - π) -
        0 * π ^ (n + 1) ∈ P ^ (n + 2) := by
    simpa [Nat.add_assoc] using hσ_succ π
  have hdiff :
      number_coefficient_scalar
          (L := L) P n π hgraded_spans σ - 0 ∈ P := by
    exact
      number_scalar_unique
        (L := L) hq P hπ_mem hπ_not_sq hspec hzero
  simpa using hdiff

lemma higher_ramification_scalar
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    {q : ℕ} (hq : Nat.Prime q)
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)]
    {n : ℕ} (hn : 1 ≤ n)
    (π : NumberField.RingOfIntegers L)
    (hπ_mem : π ∈ P)
    (hπ_not_sq : π ∉ P ^ 2)
    (hgraded_spans : ∀ x : NumberField.RingOfIntegers L,
      x ∈ P ^ (n + 1) →
        ∃ a : NumberField.RingOfIntegers L,
          x - a * π ^ (n + 1) ∈ P ^ (n + 2))
    (σ : field_higher_ramification (L := L) P n) :
    number_coefficient_scalar
        (L := L) P n π hgraded_spans σ ∈ P ↔
      σ ∈ number_higher_subgroup (L := L) P n := by
  classical
  constructor
  · exact
      number_ramification_scalar
        (L := L) hq P hn π hπ_mem hπ_not_sq hgraded_spans σ
  · exact
      number_higher_scalar
        (L := L) hq P hn π hπ_mem hπ_not_sq hgraded_spans σ

lemma higher_ramification_hom
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    {q : ℕ} (hq : Nat.Prime q)
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)]
    (n : ℕ) (hn : 1 ≤ n) :
    ∃ ψ : field_higher_ramification (L := L) P n →*
        Multiplicative P.ResidueField,
      ψ.ker = number_higher_subgroup (L := L) P n := by
  classical
  letI : P.IsMaximal :=
    number_above_maximal (L := L) hq P
  obtain ⟨π, hπ_mem, hπ_not_sq, _hπ_spans⟩ :=
    prime_cotangent_generator (L := L) hq P
  obtain ⟨J, hπ_span, hJP_top⟩ :=
    dedekind_complement_sq P hπ_mem hπ_not_sq
  have hgraded_spans :
      ∀ x : NumberField.RingOfIntegers L,
        x ∈ P ^ (n + 1) →
          ∃ a : NumberField.RingOfIntegers L,
            x - a * π ^ (n + 1) ∈ P ^ (n + 2) := by
    intro x hx
    have hJpow_top : J ^ (n + 1) ⊔ P = ⊤ :=
      ideal_sup_top (J := J) (P := P) (n + 1) hJP_top
    simpa [Nat.add_assoc] using
      (cotangent_spans_complement
        (P := P) (J := J) (π := π) (x := x) (m := n + 1)
        hπ_span hJpow_top hx)
  let ψ : field_higher_ramification (L := L) P n →*
      Multiplicative P.ResidueField := {
    toFun σ :=
      Multiplicative.ofAdd
        (algebraMap (NumberField.RingOfIntegers L) P.ResidueField
          (number_coefficient_scalar
            (L := L) P n π hgraded_spans σ))
    map_one' := by
      change
        algebraMap (NumberField.RingOfIntegers L) P.ResidueField
          (number_coefficient_scalar
            (L := L) P n π hgraded_spans
            (1 : field_higher_ramification (L := L) P n)) = 0
      exact
        (Ideal.algebraMap_residueField_eq_zero (I := P)).2
          (ramification_coefficient_scalar
            (L := L) hq P π hπ_mem hπ_not_sq hgraded_spans)
    map_mul' := by
      intro σ τ
      change
        algebraMap (NumberField.RingOfIntegers L) P.ResidueField
            (number_coefficient_scalar
              (L := L) P n π hgraded_spans (σ * τ)) =
          algebraMap (NumberField.RingOfIntegers L) P.ResidueField
              (number_coefficient_scalar
                (L := L) P n π hgraded_spans σ) +
            algebraMap (NumberField.RingOfIntegers L) P.ResidueField
              (number_coefficient_scalar
                (L := L) P n π hgraded_spans τ)
      have hcoeff :
          number_coefficient_scalar
              (L := L) P n π hgraded_spans (σ * τ) -
            (number_coefficient_scalar
                (L := L) P n π hgraded_spans σ +
              number_coefficient_scalar
                (L := L) P n π hgraded_spans τ) ∈ P := by
        exact
          number_higher_ramification
            (L := L) hq P hn π hπ_mem hπ_not_sq hgraded_spans σ τ
      have hres :=
        residue_field_sub (I := P) hcoeff
      simpa [map_add] using hres
  }
  refine ⟨ψ, ?_⟩
  ext σ
  rw [MonoidHom.mem_ker]
  constructor
  · intro hσ
    change
      algebraMap (NumberField.RingOfIntegers L) P.ResidueField
        (number_coefficient_scalar
          (L := L) P n π hgraded_spans σ) = 0 at hσ
    have hcoeff_mem :
        number_coefficient_scalar
          (L := L) P n π hgraded_spans σ ∈ P := by
      exact (Ideal.algebraMap_residueField_eq_zero (I := P)).1 hσ
    exact
      (higher_ramification_scalar
        (L := L) hq P hn π hπ_mem hπ_not_sq hgraded_spans σ).1 hcoeff_mem
  · intro hσ
    have hcoeff_mem :
        number_coefficient_scalar
          (L := L) P n π hgraded_spans σ ∈ P := by
      exact
        (higher_ramification_scalar
          (L := L) hq P hn π hπ_mem hπ_not_sq hgraded_spans σ).2 hσ
    change
      algebraMap (NumberField.RingOfIntegers L) P.ResidueField
        (number_coefficient_scalar
          (L := L) P n π hgraded_spans σ) = 0
    exact (Ideal.algebraMap_residueField_eq_zero (I := P)).2 hcoeff_mem

lemma higher_ramification_additive
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    {q : ℕ} (hq : Nat.Prime q)
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)]
    (n : ℕ) (hn : 1 ≤ n) :
    ∃ φ : number_ramification_step (L := L) P n →*
        Multiplicative P.ResidueField,
      Function.Injective φ := by
  classical
  let Gₙ := field_higher_ramification (L := L) P n
  let Nₙ := number_higher_subgroup (L := L) P n
  have hNormal : Nₙ.Normal :=
    higher_ramification_normal (L := L) P n
  letI : Nₙ.Normal := hNormal
  obtain ⟨ψ, hψker⟩ :=
    higher_ramification_hom (L := L) hq P n hn
  have hN_le : Nₙ ≤ ψ.ker := by
    intro σ hσ
    simpa [hψker] using hσ
  refine ⟨QuotientGroup.lift Nₙ ψ hN_le, ?_⟩
  exact lift_injective_ker Nₙ ψ hN_le hψker

lemma number_divisor_char
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    {q : ℕ} (hq : Nat.Prime q)
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)]
    (n : ℕ) (hn : 1 ≤ n) :
    ∀ l : ℕ, Nat.Prime l →
      l ∣ Nat.card (number_ramification_step (L := L) P n) →
        l = q := by
  classical
  obtain ⟨φ, hφ⟩ :=
    higher_ramification_additive
      (L := L) hq P n hn
  exact
    number_divisor_injective
      (L := L) hq P n φ hφ

lemma higher_ramification_divisor
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    {q : ℕ}
    (P : Ideal (NumberField.RingOfIntegers L)) (n : ℕ)
    (hSucc : ∀ l : ℕ, Nat.Prime l →
      l ∣ Nat.card (field_higher_ramification (L := L) P (n + 1)) →
        l = q)
    (hStep : ∀ l : ℕ, Nat.Prime l →
      l ∣ Nat.card (number_ramification_step (L := L) P n) →
        l = q) :
    ∀ l : ℕ, Nat.Prime l →
      l ∣ Nat.card (field_higher_ramification (L := L) P n) →
        l = q := by
  classical
  let Gₙ := field_higher_ramification (L := L) P n
  let Nₙ := number_higher_subgroup (L := L) P n
  have hFiniteGn : Finite Gₙ :=
    number_field_higher (L := L) P n
  letI : Finite Gₙ := hFiniteGn
  have hNormal : Nₙ.Normal :=
    higher_ramification_normal (L := L) P n
  letI : Nₙ.Normal := hNormal
  have hSub : ∀ l : ℕ, Nat.Prime l → l ∣ Nat.card Nₙ → l = q := by
    intro l hl hldiv
    have hcard :
        Nat.card Nₙ =
          Nat.card (field_higher_ramification (L := L) P (n + 1)) :=
      higher_ramification_succ (L := L) P n
    have hldiv_succ :
        l ∣ Nat.card (field_higher_ramification (L := L) P (n + 1)) := by
      rw [← hcard]
      exact hldiv
    exact hSucc l hl hldiv_succ
  exact
    prime_divisor_normal
      (p := q) (Γ := Gₙ) Nₙ hSub hStep

lemma ideal_span_singleton
    {A : Type*} [CommRing A]
    (P : Ideal A) {x : A} {n : ℕ}
    (hx : x ∈ P ^ (n + 1)) :
    Ideal.span ({x} : Set A) ≤ P ^ (n + 1) := by
  classical
  exact (Ideal.span_singleton_le_iff_mem (P ^ (n + 1))).2 hx

lemma dedekind_all_powers
    {A : Type*} [CommRing A] [IsDedekindDomain A]
    (P J : Ideal A) [P.IsPrime]
    (hP_ne_bot : P ≠ ⊥)
    (hJ_ne_bot : J ≠ ⊥) :
    ∃ n : ℕ, ¬ J ≤ P ^ (n + 1) := by
  classical
  have hP_prime : Prime P :=
    Ideal.prime_of_isPrime hP_ne_bot (show P.IsPrime from inferInstance)
  have hJ_ne_zero : J ≠ 0 := by
    simpa using hJ_ne_bot
  have hfinite : FiniteMultiplicity P J :=
    FiniteMultiplicity.of_prime_left hP_prime hJ_ne_zero
  obtain ⟨n, hn_not_dvd⟩ := (FiniteMultiplicity.def).1 hfinite
  refine ⟨n, ?_⟩
  intro hle
  exact hn_not_dvd ((Ideal.dvd_iff_le).2 hle)

lemma dedekind_nonzero_powers
    {A : Type*} [CommRing A] [IsDedekindDomain A]
    (P : Ideal A) [P.IsPrime]
    (hP_ne_bot : P ≠ ⊥)
    {x : A}
    (hx_ne_zero : x ≠ 0) :
    ∃ n : ℕ, x ∉ P ^ (n + 1) := by
  classical
  have hspan_ne_bot : Ideal.span ({x} : Set A) ≠ ⊥ := by
    intro hspan
    have hx_zero : x = 0 := by
      exact (Ideal.span_singleton_eq_bot).1 hspan
    exact hx_ne_zero hx_zero
  obtain ⟨n, hn_not_le⟩ :=
    dedekind_all_powers
      P (Ideal.span ({x} : Set A)) hP_ne_bot hspan_ne_bot
  refine ⟨n, ?_⟩
  intro hx_mem
  exact hn_not_le (ideal_span_singleton P hx_mem)

lemma dedekind_prime_separated
    {A : Type*} [CommRing A] [IsDedekindDomain A]
    (P : Ideal A) [P.IsPrime]
    (hP_ne_bot : P ≠ ⊥)
    {x : A}
    (hx : ∀ n : ℕ, x ∈ P ^ (n + 1)) :
    x = 0 := by
  classical
  by_contra hx_ne_zero
  obtain ⟨n, hn_not_mem⟩ :=
    dedekind_nonzero_powers P hP_ne_bot hx_ne_zero
  exact hn_not_mem (hx n)

lemma dedekind_powers_zero
    {A : Type*} [CommRing A] [IsDedekindDomain A]
    (P : Ideal A) [P.IsPrime]
    (hP_ne_bot : P ≠ ⊥)
    {x : A} :
    (∀ n : ℕ, x ∈ P ^ (n + 1)) ↔ x = 0 := by
  classical
  constructor
  · intro hx
    exact dedekind_prime_separated P hP_ne_bot hx
  · intro hx n
    rw [hx]
    exact Submodule.zero_mem (P ^ (n + 1))

lemma number_integers_separated
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L]
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime] (hP_ne_bot : P ≠ ⊥)
    {x : NumberField.RingOfIntegers L}
    (hx : ∀ n : ℕ, x ∈ P ^ (n + 1)) :
    x = 0 := by
  classical
  exact dedekind_prime_separated P hP_ne_bot hx

lemma number_integers_algebra
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    (σ : Gal(L/ℚ)) (x : NumberField.RingOfIntegers L) :
    algebraMap (NumberField.RingOfIntegers L) L (σ • x) =
      σ (algebraMap (NumberField.RingOfIntegers L) L x) := by
  classical
  change ((σ • x : NumberField.RingOfIntegers L) : L) = σ (x : L)
  change σ • (x : L) = σ (x : L)
  rw [AlgEquiv.smul_def]

lemma number_smul_integers
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (σ : Gal(L/ℚ))
    (hσ : ∀ x : NumberField.RingOfIntegers L, σ • x = x) :
    σ = 1 := by
  classical
  apply AlgEquiv.ext
  intro z
  obtain ⟨x, y, _hy, hz⟩ :=
    IsFractionRing.div_surjective (NumberField.RingOfIntegers L) z
  have hfix_integral :
      ∀ x : NumberField.RingOfIntegers L,
        σ (algebraMap (NumberField.RingOfIntegers L) L x) =
          algebraMap (NumberField.RingOfIntegers L) L x := by
    intro x
    calc
      σ (algebraMap (NumberField.RingOfIntegers L) L x) =
          algebraMap (NumberField.RingOfIntegers L) L (σ • x) := by
            exact
              (number_integers_algebra
                (L := L) σ x).symm
      _ = algebraMap (NumberField.RingOfIntegers L) L x := by
            rw [hσ x]
  rw [← hz]
  simp [hfix_integral x, hfix_integral y]

lemma number_nontrivial_separating
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime] (hP_ne_bot : P ≠ ⊥)
    (σ : P.inertia (Gal(L/ℚ))) (hσ_ne_one : σ ≠ 1) :
    ∃ data : ℕ × NumberField.RingOfIntegers L,
      ((σ : Gal(L/ℚ)) • data.2) - data.2 ∉ P ^ (data.1 + 1) := by
  classical
  by_contra hnone
  have hzero :
      ∀ x : NumberField.RingOfIntegers L,
        ((σ : Gal(L/ℚ)) • x) - x = 0 := by
    intro x
    refine
      number_integers_separated
        (L := L) P hP_ne_bot ?_
    intro n
    by_contra hnot
    exact hnone ⟨⟨n, x⟩, hnot⟩
  have hfix :
      ∀ x : NumberField.RingOfIntegers L, (σ : Gal(L/ℚ)) • x = x := by
    intro x
    exact sub_eq_zero.mp (hzero x)
  have hσ_gal : (σ : Gal(L/ℚ)) = 1 :=
    number_smul_integers (L := L) (σ : Gal(L/ℚ)) hfix
  have hσ_subgroup : σ = 1 := by
    exact Subtype.ext hσ_gal
  exact hσ_ne_one hσ_subgroup

lemma eventually_pointwise_separated
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (P : Ideal (NumberField.RingOfIntegers L))
    [Finite (P.inertia (Gal(L/ℚ)))]
    (hsep : ∀ σ : P.inertia (Gal(L/ℚ)), σ ≠ 1 →
      ∃ data : ℕ × NumberField.RingOfIntegers L,
        ((σ : Gal(L/ℚ)) • data.2) - data.2 ∉ P ^ (data.1 + 1)) :
    ∃ N : ℕ, 1 ≤ N ∧
      field_higher_ramification (L := L) P N = ⊥ := by
  classical
  let I := P.inertia (Gal(L/ℚ))
  letI : Fintype I := Fintype.ofFinite I
  let separatingData : I → ℕ × NumberField.RingOfIntegers L := fun σ =>
    if hσ : σ = 1 then (1, 0) else Classical.choose (hsep σ hσ)
  let separatingLevel : I → ℕ := fun σ => (separatingData σ).1
  let N : ℕ := (Finset.univ : Finset I).sup separatingLevel
  have hN_ge : ∀ σ : I, separatingLevel σ ≤ N := by
    intro σ
    exact Finset.le_sup (s := (Finset.univ : Finset I)) (f := separatingLevel)
      (b := σ) (Finset.mem_univ σ)
  have hN_pos : 1 ≤ N := by
    have hle_one : separatingLevel (1 : I) ≤ N := hN_ge 1
    have hone : separatingLevel (1 : I) = 1 := by
      simp [separatingLevel, separatingData]
    simpa [hone] using hle_one
  have hsep_N :
      ∀ σ : I, σ ≠ 1 →
        ∃ x : NumberField.RingOfIntegers L,
          ((σ : Gal(L/ℚ)) • x) - x ∉ P ^ (N + 1) := by
    intro σ hσ_ne_one
    refine ⟨(separatingData σ).2, ?_⟩
    have hchoose :
        ((σ : Gal(L/ℚ)) • (separatingData σ).2) - (separatingData σ).2 ∉
          P ^ (separatingLevel σ + 1) := by
      dsimp [separatingLevel, separatingData]
      rw [dif_neg hσ_ne_one]
      exact Classical.choose_spec (hsep σ hσ_ne_one)
    intro hmem_N
    have hpow_le : P ^ (N + 1) ≤ P ^ (separatingLevel σ + 1) := by
      exact Ideal.pow_le_pow_right (Nat.succ_le_succ (hN_ge σ))
    exact hchoose (hpow_le hmem_N)
  refine ⟨N, hN_pos, ?_⟩
  apply Subgroup.ext
  intro σ
  constructor
  · intro hσ_mem
    have hσ_eq_one : σ = 1 := by
      by_contra hσ_ne_one
      obtain ⟨x, hx_not_mem⟩ := hsep_N σ hσ_ne_one
      exact hx_not_mem (hσ_mem x)
    rw [hσ_eq_one]
    exact Subgroup.one_mem ⊥
  · intro hσ_bot
    have hσ_eq_one : σ = 1 := by
      simpa using hσ_bot
    rw [hσ_eq_one]
    exact Subgroup.one_mem (field_higher_ramification (L := L) P N)

lemma number_eventually_bot
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    {q : ℕ} (hq : Nat.Prime q)
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)] :
    ∃ N : ℕ, 1 ≤ N ∧
      field_higher_ramification (L := L) P N = ⊥ := by
  classical
  let I := P.inertia (Gal(L/ℚ))
  have hFiniteI : Finite I := by
    letI : Finite (Gal(L/ℚ)) := IsGaloisGroup.finite (Gal(L/ℚ)) ℚ L
    infer_instance
  have hP_ne_bot : P ≠ ⊥ :=
    Ideal.ne_bot_of_liesOver_of_ne_bot (rational_ne_bot hq) P
  letI : Finite (P.inertia (Gal(L/ℚ))) := hFiniteI
  refine
    eventually_pointwise_separated
      (L := L) P ?_
  intro σ hσ_ne_one
  exact
    number_nontrivial_separating
      (L := L) P hP_ne_bot σ hσ_ne_one

lemma divisor_eventually_steps
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    {q : ℕ}
    (P : Ideal (NumberField.RingOfIntegers L))
    (hbot : ∃ N : ℕ, 1 ≤ N ∧
      field_higher_ramification (L := L) P N = ⊥)
    (hsteps : ∀ n : ℕ, 1 ≤ n →
      ∀ l : ℕ, Nat.Prime l →
        l ∣ Nat.card (number_ramification_step (L := L) P n) →
          l = q) :
    ∀ l : ℕ, Nat.Prime l →
      l ∣ Nat.card (field_higher_ramification (L := L) P 1) →
        l = q := by
  classical
  obtain ⟨N, hNpos, hNbot⟩ := hbot
  have hbase : ∀ l : ℕ, Nat.Prime l →
      l ∣ Nat.card (field_higher_ramification (L := L) P N) →
        l = q := by
    intro l hl hldiv
    have hcard :
        Nat.card (field_higher_ramification (L := L) P N) = 1 := by
      rw [hNbot]
      exact Nat.card_unique
    have hldiv_one : l ∣ 1 := by
      rw [← hcard]
      exact hldiv
    exact False.elim (hl.not_dvd_one hldiv_one)
  let Pred : ℕ → Prop := fun n =>
    ∀ l : ℕ, Nat.Prime l →
      l ∣ Nat.card (field_higher_ramification (L := L) P n) →
        l = q
  change Pred 1
  refine Nat.decreasingInduction' (m := 1) (n := N) (P := Pred) ?_ hNpos ?_
  · intro k _hkN hkpos hsucc
    exact
      higher_ramification_divisor
        (L := L) (q := q) P k hsucc (hsteps k hkpos)
  · exact hbase

lemma higher_divisor_char
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    {q : ℕ} (hq : Nat.Prime q)
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)] :
    ∀ l : ℕ, Nat.Prime l →
      l ∣ Nat.card (field_higher_ramification (L := L) P 1) →
        l = q := by
  classical
  exact
    divisor_eventually_steps
      (L := L) (q := q) P
      (number_eventually_bot (L := L) hq P)
      (fun n hn =>
        number_divisor_char
          (L := L) hq P n hn)

lemma wild_divisor_char
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    {q : ℕ} (hq : Nat.Prime q)
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)] :
    ∀ l : ℕ, Nat.Prime l →
      l ∣ Nat.card (number_wild_subgroup (L := L) P) →
        l = q := by
  classical
  intro l hl hldiv
  have hdiv :
      l ∣ Nat.card (field_higher_ramification (L := L) P 1) := by
    simpa [higher_ramification_one (L := L) P] using hldiv
  exact
    higher_divisor_char
      (L := L) hq P l hl hdiv

end Submission
