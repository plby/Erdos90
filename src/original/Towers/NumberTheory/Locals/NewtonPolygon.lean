import Mathlib.Algebra.Polynomial.Splits
import Mathlib.Algebra.Polynomial.Eval.Subring
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.RingTheory.Polynomial.GaussNorm
import Towers.NumberTheory.Locals.CompleteDiscreteExtension

/-!
# Newton polygons

This file develops the Gauss-norm form of Milne's Proposition 7.44.  For a
positive radius `c`, the Gauss norm of a polynomial is the maximum of
`v (f.coeff i) * c ^ i`.  Its factorization below says that this coefficient
profile is exactly the product of the profiles of the roots.  Passing to
negative logarithms gives the usual lower Newton polygon and identifies its
slopes, with multiplicity, with the valuations of the roots.
-/

namespace Towers.NumberTheory.Milne

noncomputable section

open Polynomial

variable {K : Type*} [Field K]

/-- A coefficientwise field embedding that preserves absolute values also
preserves every weighted Gauss norm. -/
theorem gauss_absolute_extension
    {L : Type*} [Field L] (i : K →+* L) (hi : Function.Injective i)
    (vK : AbsoluteValue K ℝ) (vL : AbsoluteValue L ℝ)
    (hext : ∀ x : K, vL (i x) = vK x)
    (f : K[X]) (c : ℝ) :
    (f.map i).gaussNorm vL c = f.gaussNorm vK c := by
  simp only [Polynomial.gaussNorm, Polynomial.support_map_of_injective f hi,
    Polynomial.coeff_map, hext]

/-- The Gauss norm of a linear factor is the larger of the radius and the
absolute value of its root. -/
theorem gauss_x_c
    (v : AbsoluteValue K ℝ) (hv : IsNonarchimedean v)
    (a : K) {c : ℝ} (hc : 0 < c) :
    (X - C a).gaussNorm v c = max c (v a) := by
  have hX : X.gaussNorm v c = c := by
    rw [← monomial_one_one_eq_X]
    simp
  apply le_antisymm
  · calc
      (X - C a).gaussNorm v c = (X + C (-a)).gaussNorm v c := by
        rw [sub_eq_add_neg, map_neg]
      _ ≤ max (X.gaussNorm v c) ((C (-a)).gaussNorm v c) :=
        Polynomial.isNonarchimedean_gaussNorm v hv hc.le X (C (-a))
      _ = max c (v a) := by
        rw [hX, Polynomial.gaussNorm_C]
        simp
  · apply max_le
    · convert (X - C a).le_gaussNorm v hc.le 1 using 1
      simp
    · convert (X - C a).le_gaussNorm v hc.le 0 using 1
      simp

section Faces

variable (v : AbsoluteValue K ℝ)

/-- The coefficient indices at which the weighted Gauss norm is attained.

For a polynomial written in Milne's descending convention
`a₀ Xⁿ + a₁ Xⁿ⁻¹ + ⋯ + aₙ`, Lean's coefficient index `k` corresponds to
Milne's horizontal coordinate `n - k`.  At radius `exp (-s)`, this finset is
therefore exactly the exposed lower face of slope `s`. -/
def gaussFaceIndices (f : K[X]) (c : ℝ) : Finset ℕ :=
  f.support.filter fun k ↦
    f.gaussNorm v c = v (f.coeff k) * c ^ k

theorem gaussNorm_pos {f : K[X]} (hf : f ≠ 0) {c : ℝ} (hc : 0 < c) :
    0 < f.gaussNorm v c := by
  have hnonneg := f.gaussNorm_nonneg v hc.le
  have hne : f.gaussNorm v c ≠ 0 := by
    intro hzero
    apply hf
    exact (Polynomial.gaussNorm_eq_zero_iff v f
      (fun _ hx ↦ (AbsoluteValue.eq_zero v).mp hx) hc).mp hzero
  exact lt_of_le_of_ne hnonneg (Ne.symm hne)

theorem gauss_face_nonempty {f : K[X]} (hf : f ≠ 0)
    {c : ℝ} (hc : 0 < c) : (gaussFaceIndices v f c).Nonempty := by
  obtain ⟨i, hi⟩ := f.exists_eq_gaussNorm v c
  have hcoeff : f.coeff i ≠ 0 := by
    intro hzero
    rw [hzero, map_zero, zero_mul] at hi
    exact (gaussNorm_pos v hf hc).ne' hi
  exact ⟨i, Finset.mem_filter.mpr ⟨mem_support_iff.mpr hcoeff, hi⟩⟩

/-- The first coefficient index on an exposed Gauss face. -/
def gaussFaceMin (f : K[X]) (hf : f ≠ 0) (c : ℝ) (hc : 0 < c) : ℕ :=
  (gaussFaceIndices v f c).min' (gauss_face_nonempty v hf hc)

/-- The last coefficient index on an exposed Gauss face. -/
def gaussFaceMax (f : K[X]) (hf : f ≠ 0) (c : ℝ) (hc : 0 < c) : ℕ :=
  (gaussFaceIndices v f c).max' (gauss_face_nonempty v hf hc)

/-- The horizontal length of an exposed Gauss face.  Reversing coefficient
indices to Milne's coordinates does not change this difference. -/
def gaussFaceLength (f : K[X]) (hf : f ≠ 0) (c : ℝ) (hc : 0 < c) : ℕ :=
  gaussFaceMax v f hf c hc - gaussFaceMin v f hf c hc

/-- An injective coefficient embedding preserving absolute values preserves
the exposed Gauss face coefficient by coefficient. -/
theorem face_indices
    {L : Type*} [Field L] (i : K →+* L) (hi : Function.Injective i)
    (vL : AbsoluteValue L ℝ) (hext : ∀ x : K, vL (i x) = v x)
    (f : K[X]) (c : ℝ) :
    gaussFaceIndices vL (f.map i) c = gaussFaceIndices v f c := by
  ext k
  simp only [gaussFaceIndices, Polynomial.support_map_of_injective f hi,
    Finset.mem_filter, Polynomial.coeff_map]
  rw [gauss_absolute_extension i hi v vL hext f c, hext]

/-- The horizontal length of an exposed face is unchanged by an injective
coefficient embedding preserving absolute values. -/
theorem gauss_face_length
    {L : Type*} [Field L] (i : K →+* L) (hi : Function.Injective i)
    (vL : AbsoluteValue L ℝ) (hext : ∀ x : K, vL (i x) = v x)
    {f : K[X]} (hf : f ≠ 0) {c : ℝ} (hc : 0 < c) :
    gaussFaceLength vL (f.map i) ((Polynomial.map_ne_zero_iff hi).mpr hf) c hc =
      gaussFaceLength v f hf c hc := by
  simp only [gaussFaceLength, gaussFaceMin, gaussFaceMax,
    face_indices v i hi vL hext f c]

theorem gauss_face_min {f : K[X]} (hf : f ≠ 0) {c : ℝ} (hc : 0 < c) :
    gaussFaceMin v f hf c hc ∈ gaussFaceIndices v f c :=
  Finset.min'_mem _ _

theorem gauss_face_max {f : K[X]} (hf : f ≠ 0) {c : ℝ} (hc : 0 < c) :
    gaussFaceMax v f hf c hc ∈ gaussFaceIndices v f c :=
  Finset.max'_mem _ _

theorem gauss_min_index {f : K[X]} (hf : f ≠ 0)
    {c : ℝ} (hc : 0 < c) :
    f.gaussNorm v c =
      v (f.coeff (gaussFaceMin v f hf c hc)) *
        c ^ gaussFaceMin v f hf c hc := by
  have h := (Finset.mem_filter.mp (gauss_face_min v hf hc)).2
  simpa using h

theorem gauss_max_index {f : K[X]} (hf : f ≠ 0)
    {c : ℝ} (hc : 0 < c) :
    f.gaussNorm v c =
      v (f.coeff (gaussFaceMax v f hf c hc)) *
        c ^ gaussFaceMax v f hf c hc := by
  have h := (Finset.mem_filter.mp (gauss_face_max v hf hc)).2
  simpa using h

theorem coeff_gauss_min {f : K[X]} (hf : f ≠ 0)
    {c : ℝ} (hc : 0 < c) {i : ℕ}
    (hi : i < gaussFaceMin v f hf c hc) :
    v (f.coeff i) * c ^ i < f.gaussNorm v c := by
  refine lt_of_le_of_ne (f.le_gaussNorm v hc.le i) ?_
  intro heq
  have hcoeff : f.coeff i ≠ 0 := by
    intro hzero
    rw [hzero, map_zero, zero_mul] at heq
    exact (gaussNorm_pos v hf hc).ne' heq.symm
  have himem : i ∈ gaussFaceIndices v f c :=
    Finset.mem_filter.mpr ⟨mem_support_iff.mpr hcoeff, heq.symm⟩
  exact (Nat.not_le_of_gt hi) (Finset.min'_le _ _ himem)

theorem coeff_gauss_max {f : K[X]} (hf : f ≠ 0)
    {c : ℝ} (hc : 0 < c) {i : ℕ}
    (hi : gaussFaceMax v f hf c hc < i) :
    v (f.coeff i) * c ^ i < f.gaussNorm v c := by
  refine lt_of_le_of_ne (f.le_gaussNorm v hc.le i) ?_
  intro heq
  have hcoeff : f.coeff i ≠ 0 := by
    intro hzero
    rw [hzero, map_zero, zero_mul] at heq
    exact (gaussNorm_pos v hf hc).ne' heq.symm
  have himem : i ∈ gaussFaceIndices v f c :=
    Finset.mem_filter.mpr ⟨mem_support_iff.mpr hcoeff, heq.symm⟩
  exact (Nat.not_le_of_gt hi) (Finset.le_max' _ _ himem)

private theorem coeff_min_index
    (hv : IsNonarchimedean v) {p q : K[X]} (hp : p ≠ 0) (hq : q ≠ 0)
    {c : ℝ} (hc : 0 < c) {k : ℕ}
    (hk : k < gaussFaceMin v p hp c hc + gaussFaceMin v q hq c hc) :
    v ((p * q).coeff k) * c ^ k < p.gaussNorm v c * q.gaussNorm v c := by
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  obtain ⟨i, hi, hsum⟩ := hv.finset_image_add_of_nonempty
    (t := Finset.range (k + 1))
    (fun i ↦ p.coeff i * q.coeff (k - i))
      ⟨0, Finset.mem_range.mpr (by omega)⟩
  have hik : i ≤ k := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
  calc
    v (∑ i ∈ Finset.range (k + 1), p.coeff i * q.coeff (k - i)) * c ^ k
        ≤ v (p.coeff i * q.coeff (k - i)) * c ^ k := by
          gcongr
    _ = (v (p.coeff i) * c ^ i) * (v (q.coeff (k - i)) * c ^ (k - i)) := by
          rw [map_mul]
          have hpow : c ^ i * c ^ (k - i) = c ^ k := by
            rw [← pow_add, Nat.add_sub_of_le hik]
          rw [← hpow]
          ring
    _ < p.gaussNorm v c * q.gaussNorm v c := by
          by_cases hip : i < gaussFaceMin v p hp c hc
          · calc
              (v (p.coeff i) * c ^ i) * (v (q.coeff (k - i)) * c ^ (k - i))
                  ≤ (v (p.coeff i) * c ^ i) * q.gaussNorm v c := by
                    gcongr
                    exact q.le_gaussNorm v hc.le (k - i)
              _ < p.gaussNorm v c * q.gaussNorm v c := by
                    exact mul_lt_mul_of_pos_right
                      (coeff_gauss_min v hp hc hip)
                      (gaussNorm_pos v hq hc)
          · have hqi : k - i < gaussFaceMin v q hq c hc := by omega
            calc
              (v (p.coeff i) * c ^ i) * (v (q.coeff (k - i)) * c ^ (k - i))
                  ≤ p.gaussNorm v c * (v (q.coeff (k - i)) * c ^ (k - i)) := by
                    gcongr
                    exact p.le_gaussNorm v hc.le i
              _ < p.gaussNorm v c * q.gaussNorm v c := by
                    exact mul_lt_mul_of_pos_left
                      (coeff_gauss_min v hq hc hqi)
                      (gaussNorm_pos v hp hc)

private theorem min_face_indices
    (hv : IsNonarchimedean v) {p q : K[X]} (hp : p ≠ 0) (hq : q ≠ 0)
    {c : ℝ} (hc : 0 < c) :
    gaussFaceMin v p hp c hc + gaussFaceMin v q hq c hc ∈
      gaussFaceIndices v (p * q) c := by
  let i := gaussFaceMin v p hp c hc
  let j := gaussFaceMin v q hq c hc
  have hi : p.gaussNorm v c = v (p.coeff i) * c ^ i := by
    simpa [i] using gauss_min_index v hp hc
  have hj : q.gaussNorm v c = v (q.coeff j) * c ^ j := by
    simpa [j] using gauss_min_index v hq hc
  have hcoeff :
      p.gaussNorm v c * q.gaussNorm v c =
        v ((p * q).coeff (i + j)) * c ^ (i + j) := by
    rw [hi, hj, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
      hv.apply_sum_eq_of_lt (k := i) (by simp)]
    · grind
    · intro x hx hxi
      apply lt_of_mul_lt_mul_right _ (pow_nonneg hc.le (i + j))
      have hxle : x ≤ i + j := Nat.le_of_lt_succ (Finset.mem_range.mp hx)
      have hsum : x + (i + j - x) = i + j := Nat.add_sub_of_le hxle
      convert_to
        (v (p.coeff x) * c ^ x) * (v (q.coeff (i + j - x)) * c ^ (i + j - x)) <
          (v (p.coeff i) * c ^ i) * (v (q.coeff j) * c ^ j)
      · grind
      · grind
      rcases lt_or_gt_of_ne hxi with hxi' | hxi'
      · calc
          (v (p.coeff x) * c ^ x) * (v (q.coeff (i + j - x)) * c ^ (i + j - x))
              ≤ (v (p.coeff x) * c ^ x) * q.gaussNorm v c := by
                gcongr
                exact q.le_gaussNorm v hc.le (i + j - x)
          _ = (v (p.coeff x) * c ^ x) * (v (q.coeff j) * c ^ j) := by rw [hj]
          _ < (v (p.coeff i) * c ^ i) * (v (q.coeff j) * c ^ j) := by
                have hpstrict :=
                  coeff_gauss_min v hp hc hxi'
                rw [hi] at hpstrict
                exact mul_lt_mul_of_pos_right
                  hpstrict
                  (by rw [← hj]; exact gaussNorm_pos v hq hc)
      · have hq' : i + j - x < j := by omega
        calc
          (v (p.coeff x) * c ^ x) * (v (q.coeff (i + j - x)) * c ^ (i + j - x))
              ≤ p.gaussNorm v c * (v (q.coeff (i + j - x)) * c ^ (i + j - x)) := by
                gcongr
                exact p.le_gaussNorm v hc.le x
          _ = (v (p.coeff i) * c ^ i) *
              (v (q.coeff (i + j - x)) * c ^ (i + j - x)) := by rw [hi]
          _ < (v (p.coeff i) * c ^ i) * (v (q.coeff j) * c ^ j) := by
                have hqstrict :=
                  coeff_gauss_min v hq hc hq'
                rw [hj] at hqstrict
                exact mul_lt_mul_of_pos_left
                  hqstrict
                  (by rw [← hi]; exact gaussNorm_pos v hp hc)
  have hmulNorm := Polynomial.gaussNorm_mul hv hc p q
  have hattain :
      (p * q).gaussNorm v c =
        v ((p * q).coeff (i + j)) * c ^ (i + j) := by
    rw [hmulNorm, hcoeff]
  have hcoeffne : (p * q).coeff (i + j) ≠ 0 := by
    intro hzero
    rw [hzero, map_zero, zero_mul] at hattain
    exact (gaussNorm_pos v (mul_ne_zero hp hq) hc).ne' hattain
  exact Finset.mem_filter.mpr ⟨mem_support_iff.mpr hcoeffne, hattain⟩

/-- The first coefficient index on an exposed face is additive under
multiplication. -/
theorem gauss_face_index (hv : IsNonarchimedean v)
    {p q : K[X]} (hp : p ≠ 0) (hq : q ≠ 0) {c : ℝ} (hc : 0 < c) :
    gaussFaceMin v (p * q) (mul_ne_zero hp hq) c hc =
      gaussFaceMin v p hp c hc + gaussFaceMin v q hq c hc := by
  let m := gaussFaceMin v (p * q) (mul_ne_zero hp hq) c hc
  let i := gaussFaceMin v p hp c hc
  let j := gaussFaceMin v q hq c hc
  apply le_antisymm
  · exact Finset.min'_le _ _
      (min_face_indices v hv hp hq hc)
  · by_contra hnot
    have hm : m < i + j := Nat.lt_of_not_ge hnot
    have hstrict := coeff_min_index v hv hp hq hc hm
    have hattain := (Finset.mem_filter.mp
      (gauss_face_min v (mul_ne_zero hp hq) hc)).2
    rw [Polynomial.gaussNorm_mul hv hc] at hattain
    exact (ne_of_lt hstrict) hattain.symm

private theorem coeff_max_index
    (hv : IsNonarchimedean v) {p q : K[X]} (hp : p ≠ 0) (hq : q ≠ 0)
    {c : ℝ} (hc : 0 < c) {k : ℕ}
    (hk : gaussFaceMax v p hp c hc + gaussFaceMax v q hq c hc < k) :
    v ((p * q).coeff k) * c ^ k < p.gaussNorm v c * q.gaussNorm v c := by
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  obtain ⟨i, hi, hsum⟩ := hv.finset_image_add_of_nonempty
    (t := Finset.range (k + 1))
    (fun i ↦ p.coeff i * q.coeff (k - i))
      ⟨0, Finset.mem_range.mpr (by omega)⟩
  have hik : i ≤ k := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
  calc
    v (∑ i ∈ Finset.range (k + 1), p.coeff i * q.coeff (k - i)) * c ^ k
        ≤ v (p.coeff i * q.coeff (k - i)) * c ^ k := by
          gcongr
    _ = (v (p.coeff i) * c ^ i) * (v (q.coeff (k - i)) * c ^ (k - i)) := by
          rw [map_mul]
          have hpow : c ^ i * c ^ (k - i) = c ^ k := by
            rw [← pow_add, Nat.add_sub_of_le hik]
          rw [← hpow]
          ring
    _ < p.gaussNorm v c * q.gaussNorm v c := by
          by_cases hip : gaussFaceMax v p hp c hc < i
          · calc
              (v (p.coeff i) * c ^ i) * (v (q.coeff (k - i)) * c ^ (k - i))
                  ≤ (v (p.coeff i) * c ^ i) * q.gaussNorm v c := by
                    gcongr
                    exact q.le_gaussNorm v hc.le (k - i)
              _ < p.gaussNorm v c * q.gaussNorm v c := by
                    exact mul_lt_mul_of_pos_right
                      (coeff_gauss_max v hp hc hip)
                      (gaussNorm_pos v hq hc)
          · have hqi : gaussFaceMax v q hq c hc < k - i := by omega
            calc
              (v (p.coeff i) * c ^ i) * (v (q.coeff (k - i)) * c ^ (k - i))
                  ≤ p.gaussNorm v c * (v (q.coeff (k - i)) * c ^ (k - i)) := by
                    gcongr
                    exact p.le_gaussNorm v hc.le i
              _ < p.gaussNorm v c * q.gaussNorm v c := by
                    exact mul_lt_mul_of_pos_left
                      (coeff_gauss_max v hq hc hqi)
                      (gaussNorm_pos v hp hc)

private theorem max_face_indices
    (hv : IsNonarchimedean v) {p q : K[X]} (hp : p ≠ 0) (hq : q ≠ 0)
    {c : ℝ} (hc : 0 < c) :
    gaussFaceMax v p hp c hc + gaussFaceMax v q hq c hc ∈
      gaussFaceIndices v (p * q) c := by
  let i := gaussFaceMax v p hp c hc
  let j := gaussFaceMax v q hq c hc
  have hi : p.gaussNorm v c = v (p.coeff i) * c ^ i := by
    simpa [i] using gauss_max_index v hp hc
  have hj : q.gaussNorm v c = v (q.coeff j) * c ^ j := by
    simpa [j] using gauss_max_index v hq hc
  have hcoeff :
      p.gaussNorm v c * q.gaussNorm v c =
        v ((p * q).coeff (i + j)) * c ^ (i + j) := by
    rw [hi, hj, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
      hv.apply_sum_eq_of_lt (k := i) (by simp)]
    · grind
    · intro x hx hxi
      apply lt_of_mul_lt_mul_right _ (pow_nonneg hc.le (i + j))
      have hxle : x ≤ i + j := Nat.le_of_lt_succ (Finset.mem_range.mp hx)
      have hsum : x + (i + j - x) = i + j := Nat.add_sub_of_le hxle
      convert_to
        (v (p.coeff x) * c ^ x) * (v (q.coeff (i + j - x)) * c ^ (i + j - x)) <
          (v (p.coeff i) * c ^ i) * (v (q.coeff j) * c ^ j)
      · grind
      · grind
      rcases lt_or_gt_of_ne hxi with hxi' | hxi'
      · have hq' : j < i + j - x := by omega
        calc
          (v (p.coeff x) * c ^ x) * (v (q.coeff (i + j - x)) * c ^ (i + j - x))
              ≤ p.gaussNorm v c * (v (q.coeff (i + j - x)) * c ^ (i + j - x)) := by
                gcongr
                exact p.le_gaussNorm v hc.le x
          _ = (v (p.coeff i) * c ^ i) *
              (v (q.coeff (i + j - x)) * c ^ (i + j - x)) := by rw [hi]
          _ < (v (p.coeff i) * c ^ i) * (v (q.coeff j) * c ^ j) := by
                have hqstrict :=
                  coeff_gauss_max v hq hc hq'
                rw [hj] at hqstrict
                exact mul_lt_mul_of_pos_left hqstrict
                  (by rw [← hi]; exact gaussNorm_pos v hp hc)
      · calc
          (v (p.coeff x) * c ^ x) * (v (q.coeff (i + j - x)) * c ^ (i + j - x))
              ≤ (v (p.coeff x) * c ^ x) * q.gaussNorm v c := by
                gcongr
                exact q.le_gaussNorm v hc.le (i + j - x)
          _ = (v (p.coeff x) * c ^ x) * (v (q.coeff j) * c ^ j) := by rw [hj]
          _ < (v (p.coeff i) * c ^ i) * (v (q.coeff j) * c ^ j) := by
                have hpstrict :=
                  coeff_gauss_max v hp hc hxi'
                rw [hi] at hpstrict
                exact mul_lt_mul_of_pos_right hpstrict
                  (by rw [← hj]; exact gaussNorm_pos v hq hc)
  have hmulNorm := Polynomial.gaussNorm_mul hv hc p q
  have hattain :
      (p * q).gaussNorm v c =
        v ((p * q).coeff (i + j)) * c ^ (i + j) := by
    rw [hmulNorm, hcoeff]
  have hcoeffne : (p * q).coeff (i + j) ≠ 0 := by
    intro hzero
    rw [hzero, map_zero, zero_mul] at hattain
    exact (gaussNorm_pos v (mul_ne_zero hp hq) hc).ne' hattain
  exact Finset.mem_filter.mpr ⟨mem_support_iff.mpr hcoeffne, hattain⟩

/-- The last coefficient index on an exposed face is additive under
multiplication. -/
theorem gauss_face_mul (hv : IsNonarchimedean v)
    {p q : K[X]} (hp : p ≠ 0) (hq : q ≠ 0) {c : ℝ} (hc : 0 < c) :
    gaussFaceMax v (p * q) (mul_ne_zero hp hq) c hc =
      gaussFaceMax v p hp c hc + gaussFaceMax v q hq c hc := by
  let m := gaussFaceMax v (p * q) (mul_ne_zero hp hq) c hc
  let i := gaussFaceMax v p hp c hc
  let j := gaussFaceMax v q hq c hc
  apply le_antisymm
  · by_contra hnot
    have hm : i + j < m := Nat.lt_of_not_ge hnot
    have hstrict := coeff_max_index v hv hp hq hc hm
    have hattain := (Finset.mem_filter.mp
      (gauss_face_max v (mul_ne_zero hp hq) hc)).2
    rw [Polynomial.gaussNorm_mul hv hc] at hattain
    exact (ne_of_lt hstrict) hattain.symm
  · exact Finset.le_max' _ _
      (max_face_indices v hv hp hq hc)

/-- Horizontal face lengths add under multiplication. -/
theorem face_length_mul (hv : IsNonarchimedean v)
    {p q : K[X]} (hp : p ≠ 0) (hq : q ≠ 0) {c : ℝ} (hc : 0 < c) :
    gaussFaceLength v (p * q) (mul_ne_zero hp hq) c hc =
      gaussFaceLength v p hp c hc + gaussFaceLength v q hq c hc := by
  rw [gaussFaceLength, gaussFaceLength, gaussFaceLength,
    gauss_face_index v hv hp hq hc, gauss_face_mul v hv hp hq hc]
  have hp_le : gaussFaceMin v p hp c hc ≤
      gaussFaceMax v p hp c hc := by
    exact Finset.min'_le_max' (gaussFaceIndices v p c)
      (gauss_face_nonempty v hp hc)
  have hq_le : gaussFaceMin v q hq c hc ≤
      gaussFaceMax v q hq c hc := by
    exact Finset.min'_le_max' (gaussFaceIndices v q c)
      (gauss_face_nonempty v hq hc)
  omega

private theorem face_x_c
    (a : K) {c : ℝ}
    {i : ℕ} (hi : i ∈ gaussFaceIndices v (X - C a) c) : i ≤ 1 := by
  exact (le_natDegree_of_mem_supp i (Finset.mem_filter.mp hi).1).trans_eq
    (natDegree_X_sub_C a)

private theorem gauss_face_indices
    (hv : IsNonarchimedean v) (a : K) {c : ℝ} (hc : 0 < c)
    (ha : v a ≤ c) : 1 ∈ gaussFaceIndices v (X - C a) c := by
  simp [gaussFaceIndices, gauss_x_c v hv a hc, max_eq_left ha]

private theorem face_indices_c
    (hv : IsNonarchimedean v) (a : K) {c : ℝ} (hc : 0 < c)
    (ha : c ≤ v a) : 0 ∈ gaussFaceIndices v (X - C a) c := by
  have ha0 : a ≠ 0 := by
    intro hzero
    subst a
    simp at ha
    linarith
  simp [gaussFaceIndices, gauss_x_c v hv a hc, max_eq_right ha, ha0]

/-- A linear factor contributes horizontal length one precisely when the
radius equals the absolute value of its root. -/
theorem face_length_c (hv : IsNonarchimedean v)
    (a : K) {c : ℝ} (hc : 0 < c) :
    gaussFaceLength v (X - C a) (X_sub_C_ne_zero a) c hc =
      if v a = c then 1 else 0 := by
  by_cases heq : v a = c
  · have hzero := face_indices_c v hv a hc heq.ge
    have hone := gauss_face_indices v hv a hc heq.le
    have hmin : gaussFaceMin v (X - C a) (X_sub_C_ne_zero a) c hc = 0 := by
      apply (Finset.min'_eq_iff _ _ 0).mpr
      exact ⟨hzero, fun _ _ ↦ Nat.zero_le _⟩
    have hmax : gaussFaceMax v (X - C a) (X_sub_C_ne_zero a) c hc = 1 := by
      apply (Finset.max'_eq_iff _ _ 1).mpr
      exact ⟨hone, fun i hi ↦ face_x_c v a hi⟩
    simp [gaussFaceLength, hmin, hmax, heq]
  · by_cases hlt : v a < c
    · have hone := gauss_face_indices v hv a hc hlt.le
      have hall : ∀ i ∈ gaussFaceIndices v (X - C a) c, i = 1 := by
        intro i hi
        have hle := face_x_c v a hi
        have hi0 : i ≠ 0 := by
          intro hi0
          subst i
          have hattain := (Finset.mem_filter.mp hi).2
          simp [gauss_x_c v hv a hc, max_eq_left hlt.le] at hattain
          exact (ne_of_lt hlt) hattain.symm
        omega
      have hmin : gaussFaceMin v (X - C a) (X_sub_C_ne_zero a) c hc = 1 := by
        apply (Finset.min'_eq_iff _ _ 1).mpr
        exact ⟨hone, fun i hi ↦ by rw [hall i hi]⟩
      have hmax : gaussFaceMax v (X - C a) (X_sub_C_ne_zero a) c hc = 1 := by
        apply (Finset.max'_eq_iff _ _ 1).mpr
        exact ⟨hone, fun i hi ↦ by rw [hall i hi]⟩
      simp [gaussFaceLength, hmin, hmax, heq]
    · have hgt : c < v a := lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm heq)
      have hzero := face_indices_c v hv a hc hgt.le
      have hall : ∀ i ∈ gaussFaceIndices v (X - C a) c, i = 0 := by
        intro i hi
        have hle := face_x_c v a hi
        have hi1 : i ≠ 1 := by
          intro hi1
          subst i
          have hattain := (Finset.mem_filter.mp hi).2
          simp [gauss_x_c v hv a hc, max_eq_right hgt.le] at hattain
          exact (ne_of_lt hgt) hattain.symm
        omega
      have hmin : gaussFaceMin v (X - C a) (X_sub_C_ne_zero a) c hc = 0 := by
        apply (Finset.min'_eq_iff _ _ 0).mpr
        exact ⟨hzero, fun i hi ↦ by rw [hall i hi]⟩
      have hmax : gaussFaceMax v (X - C a) (X_sub_C_ne_zero a) c hc = 0 := by
        apply (Finset.max'_eq_iff _ _ 0).mpr
        exact ⟨hzero, fun i hi ↦ by rw [hall i hi]⟩
      simp [gaussFaceLength, hmin, hmax, heq]

theorem gauss_face_one {c : ℝ} (hc : 0 < c) :
    gaussFaceLength v (1 : K[X]) one_ne_zero c hc = 0 := by
  have hnorm : (1 : K[X]).gaussNorm v c = 1 := by
    rw [← C_1, Polynomial.gaussNorm_C, map_one]
  have hzero : 0 ∈ gaussFaceIndices v (1 : K[X]) c := by
    simp [gaussFaceIndices, hnorm]
  have hall : ∀ i ∈ gaussFaceIndices v (1 : K[X]) c, i = 0 := by
    intro i hi
    have hsupp := (Finset.mem_filter.mp hi).1
    simpa [mem_support_iff, coeff_one] using hsupp
  have hmin : gaussFaceMin v (1 : K[X]) one_ne_zero c hc = 0 := by
    apply (Finset.min'_eq_iff _ _ 0).mpr
    exact ⟨hzero, fun i hi ↦ by rw [hall i hi]⟩
  have hmax : gaussFaceMax v (1 : K[X]) one_ne_zero c hc = 0 := by
    apply (Finset.max'_eq_iff _ _ 0).mpr
    exact ⟨hzero, fun i hi ↦ by rw [hall i hi]⟩
  simp [gaussFaceLength, hmin, hmax]

/-- The horizontal length of the exposed face of a product of linear factors
counts, with multiplicity, the roots whose absolute value is the radius. -/
theorem gauss_face_c (hv : IsNonarchimedean v)
    (roots : Multiset K) {c : ℝ} (hc : 0 < c) :
    gaussFaceLength v (roots.map fun a ↦ X - C a).prod
        (monic_multisetProd_X_sub_C roots).ne_zero c hc =
      roots.countP fun a ↦ v a = c := by
  induction roots using Multiset.induction_on with
  | empty => simpa using gauss_face_one v hc
  | cons a roots ih =>
      simp only [Multiset.map_cons, Multiset.prod_cons]
      rw [face_length_mul v hv (X_sub_C_ne_zero a)
          (monic_multisetProd_X_sub_C roots).ne_zero hc,
        face_length_c v hv a hc, ih, Multiset.countP_cons]
      split <;> omega

/-- Milne, Proposition 7.44, first assertion in Gauss-face form: for a monic
split polynomial, the horizontal length of the face exposed at radius `c` is
the number of roots of absolute value `c`, counted with multiplicity. -/
theorem gauss_face_roots (hv : IsNonarchimedean v)
    {f : K[X]} (hsplit : f.Splits) (hmonic : f.Monic)
    {c : ℝ} (hc : 0 < c) :
    gaussFaceLength v f hmonic.ne_zero c hc =
      f.roots.countP fun a ↦ v a = c := by
  have hfactor := hsplit.eq_prod_roots_of_monic hmonic
  have hprod := gauss_face_c v hv f.roots hc
  simpa only [← hfactor] using hprod

/-- The exposed lower face of additive slope `s`. -/
def newtonFaceIndices (f : K[X]) (s : ℝ) : Finset ℕ :=
  gaussFaceIndices v f (Real.exp (-s))

/-- The horizontal length of the lower Newton-polygon face of additive slope
`s`. -/
def newtonSlopeLength (f : K[X]) (hf : f ≠ 0) (s : ℝ) : ℕ :=
  gaussFaceLength v f hf (Real.exp (-s)) (Real.exp_pos _)

/-- Lower Newton-polygon face lengths are preserved by an injective
coefficient embedding preserving absolute values. -/
theorem newton_slope_length
    {L : Type*} [Field L] (i : K →+* L) (hi : Function.Injective i)
    (vL : AbsoluteValue L ℝ) (hext : ∀ x : K, vL (i x) = v x)
    {f : K[X]} (hf : f ≠ 0) (s : ℝ) :
    newtonSlopeLength vL (f.map i) ((Polynomial.map_ne_zero_iff hi).mpr hf) s =
      newtonSlopeLength v f hf s := by
  exact gauss_face_length v i hi vL hext hf (Real.exp_pos _)

/-- Milne, Proposition 7.44, first assertion.  The lower Newton-polygon face
of additive slope `s` has horizontal length equal to the multiplicity of the
roots of finite additive value `s`, encoded without assigning a logarithmic
value to zero by the equality `|α| = exp (-s)`. -/
theorem newton_slope_roots (hv : IsNonarchimedean v)
    {f : K[X]} (hsplit : f.Splits) (hmonic : f.Monic) (s : ℝ) :
    newtonSlopeLength v f hmonic.ne_zero s =
      f.roots.countP fun a ↦ v a = Real.exp (-s) := by
  exact gauss_face_roots v hv hsplit hmonic (Real.exp_pos _)

/-- Extension-field form of Milne's Proposition 7.44: when a monic
polynomial splits after extending scalars, the base Newton-polygon face length
counts its roots in the extension having the corresponding absolute value. -/
theorem slope_length_aroots
    {L : Type*} [Field L] [Algebra K L]
    (vL : AbsoluteValue L ℝ) (hvL : IsNonarchimedean vL)
    (hext : ∀ x : K, vL (algebraMap K L x) = v x)
    {f : K[X]} (hsplit : (f.map (algebraMap K L)).Splits)
    (hmonic : f.Monic) (s : ℝ) :
    newtonSlopeLength v f hmonic.ne_zero s =
      (f.aroots L).countP fun a ↦ vL a = Real.exp (-s) := by
  have hmapMonic : (f.map (algebraMap K L)).Monic := hmonic.map _
  calc
    newtonSlopeLength v f hmonic.ne_zero s =
        newtonSlopeLength vL (f.map (algebraMap K L)) hmapMonic.ne_zero s :=
      (newton_slope_length v (algebraMap K L) (algebraMap K L).injective
        vL hext hmonic.ne_zero s).symm
    _ = (f.aroots L).countP fun a ↦ vL a = Real.exp (-s) :=
      newton_slope_roots vL hvL hsplit hmapMonic s

end Faces

/-- Gauss-norm factorization over the roots of a split polynomial.  This is
the multiplicative (and logarithmically dual) form of the first assertion of
Milne's Proposition 7.44. -/
theorem gauss_leading_max
    (v : AbsoluteValue K ℝ) (hv : IsNonarchimedean v)
    {f : K[X]} (hf : f.Splits) {c : ℝ} (hc : 0 < c) :
    f.gaussNorm v c =
      v f.leadingCoeff * (f.roots.map fun a ↦ max c (v a)).prod := by
  have hprod (s : Multiset K) :
      ((s.map fun a ↦ X - C a).prod).gaussNorm v c =
        (s.map fun a ↦ max c (v a)).prod := by
    induction s using Multiset.induction_on with
    | empty =>
        rw [Multiset.map_zero, Multiset.prod_zero]
        have hC : (1 : K[X]) = C 1 := by
          ext n
          simp
        rw [hC, Polynomial.gaussNorm_C, map_one]
        simp
    | cons a s ih =>
        simp only [Multiset.map_cons, Multiset.prod_cons]
        rw [Polynomial.gaussNorm_mul hv hc, gauss_x_c v hv a hc, ih]
  calc
    f.gaussNorm v c =
        (C f.leadingCoeff * (f.roots.map fun a ↦ X - C a).prod).gaussNorm v c :=
      congrArg (Polynomial.gaussNorm v c) hf.eq_prod_roots
    _ = v f.leadingCoeff *
        ((f.roots.map fun a ↦ X - C a).prod).gaussNorm v c := by
      rw [Polynomial.gaussNorm_mul hv hc, Polynomial.gaussNorm_C]
    _ = v f.leadingCoeff * (f.roots.map fun a ↦ max c (v a)).prod := by
      rw [hprod]

/-- For a monic split polynomial, the weighted coefficient maximum is the
product of `max c (v a)` over all roots, counted with multiplicity. -/
theorem gauss_max_monic
    (v : AbsoluteValue K ℝ) (hv : IsNonarchimedean v)
    {f : K[X]} (hf : f.Splits) (hmonic : f.Monic)
    {c : ℝ} (hc : 0 < c) :
    f.gaussNorm v c = (f.roots.map fun a ↦ max c (v a)).prod := by
  rw [gauss_leading_max v hv hf hc, hmonic.leadingCoeff]
  simp

section RootFactor

variable {L Γ : Type*} [Field L] [Algebra K L]

/-- The factor made from the roots of `p` in `L` having value `s`.
Roots are counted with their multiplicities. -/
def newtonRootFactor [DecidableEq Γ] (w : L → Γ) (s : Γ) (p : K[X]) : L[X] :=
  Polynomial.ofMultiset
    ((p.map (algebraMap K L)).roots.filter fun x ↦ w x = s)

@[simp]
theorem roots_newton_factor [DecidableEq Γ] (w : L → Γ) (s : Γ) (p : K[X]) :
    (newtonRootFactor w s p).roots =
      (p.map (algebraMap K L)).roots.filter fun x ↦ w x = s := by
  exact Polynomial.roots_ofMultiset _

@[simp]
theorem nat_newton_factor [DecidableEq Γ]
    (w : L → Γ) (s : Γ) (p : K[X]) :
    (newtonRootFactor w s p).natDegree =
      Multiset.card ((p.map (algebraMap K L)).roots.filter fun x ↦ w x = s) := by
  simp [newtonRootFactor]

private theorem mapped_polynomial
    (p : K[X]) (sigma : L ≃ₐ[K] L) :
    (p.map (algebraMap K L)).map sigma.toRingHom = p.map (algebraMap K L) := by
  ext n
  simp

private theorem roots_alg_equiv
    (p : K[X]) (hsplit : (p.map (algebraMap K L)).Splits)
    (sigma : L ≃ₐ[K] L) :
    (p.map (algebraMap K L)).roots.map sigma =
      (p.map (algebraMap K L)).roots := by
  change (p.map (algebraMap K L)).roots.map sigma.toRingHom =
    (p.map (algebraMap K L)).roots
  rw [← hsplit.roots_map sigma.toRingHom, mapped_polynomial p sigma]

/-- If a function on a splitting field is invariant under all automorphisms
over `K`, each of its strata in the root multiset is invariant as well. -/
theorem filter_roots [DecidableEq Γ]
    (w : L → Γ) (s : Γ) (p : K[X])
    (hsplit : (p.map (algebraMap K L)).Splits)
    (hw : ∀ (sigma : L ≃ₐ[K] L) x, w (sigma x) = w x)
    (sigma : L ≃ₐ[K] L) :
    (((p.map (algebraMap K L)).roots.filter fun x ↦ w x = s).map sigma) =
      ((p.map (algebraMap K L)).roots.filter fun x ↦ w x = s) := by
  let roots := (p.map (algebraMap K L)).roots
  have hfilter :
      roots.filter (fun x ↦ w x = s) = roots.filter (fun x ↦ w (sigma x) = s) := by
    apply Multiset.filter_congr
    intro x hx
    rw [hw sigma x]
  calc
    (roots.filter fun x ↦ w x = s).map sigma =
        (roots.filter fun x ↦ w (sigma x) = s).map sigma := congrArg (Multiset.map sigma) hfilter
    _ = (roots.map sigma).filter (fun x ↦ w x = s) := by
      simpa only [Function.comp_apply] using
        (Multiset.filter_map (p := fun x ↦ w x = s) sigma roots).symm
    _ = roots.filter (fun x ↦ w x = s) := by
      rw [roots_alg_equiv p hsplit sigma]

/-- The factor consisting of all roots with one value is fixed coefficientwise
by every automorphism of the splitting field. -/
theorem newton_factor [DecidableEq Γ]
    (w : L → Γ) (s : Γ) (p : K[X])
    (hsplit : (p.map (algebraMap K L)).Splits)
    (hw : ∀ (sigma : L ≃ₐ[K] L) x, w (sigma x) = w x)
    (sigma : L ≃ₐ[K] L) :
    (newtonRootFactor w s p).map sigma.toRingHom = newtonRootFactor w s p := by
  let roots := (p.map (algebraMap K L)).roots
  let m := roots.filter fun x ↦ w x = s
  have hm : m.map sigma = m := by
    exact filter_roots w s p hsplit hw sigma
  have hm' : m.map sigma.toRingHom = m := by
    simpa using hm
  change (Polynomial.ofMultiset m).map sigma.toRingHom = Polynomial.ofMultiset m
  simp only [Polynomial.ofMultiset_apply, Polynomial.map_multiset_prod,
    Multiset.map_map, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C,
    Function.comp_apply]
  have hmap := congrArg (Multiset.map fun a : L ↦ X - C a) hm'
  simpa only [Multiset.map_map, Function.comp_apply] using
    congrArg Multiset.prod hmap

/-- Milne, Proposition 7.44, second assertion: in a possibly infinite Galois
splitting field, the product of the linear factors belonging to one valuation
stratum has coefficients in the base field. -/
theorem newton_root_factor [DecidableEq Γ]
    [IsGalois K L]
    (w : L → Γ) (s : Γ) (p : K[X])
    (hsplit : (p.map (algebraMap K L)).Splits)
    (hw : ∀ (sigma : L ≃ₐ[K] L) x, w (sigma x) = w x) :
    ∃ q : K[X], q.map (algebraMap K L) = newtonRootFactor w s p := by
  have hmem : newtonRootFactor w s p ∈
      (Polynomial.mapRingHom (algebraMap K L)).range := by
    rw [Polynomial.mem_map_range]
    intro n
    rw [RingHom.mem_range]
    apply (InfiniteGalois.mem_range_algebraMap_iff_fixed _).2
    intro sigma
    have hfixed := congrArg (fun q : L[X] ↦ q.coeff n)
      (newton_factor w s p hsplit hw sigma)
    simpa only [Polynomial.coeff_map] using hfixed
  rcases hmem with ⟨q, hq⟩
  exact ⟨q, hq⟩

end RootFactor

/-- Gauss-norm factorization for a polynomial whose roots are taken in an
extension field.  Both sides are expressed in the original coefficient
absolute value and the chosen extending absolute value, respectively. -/
theorem gauss_max_aroot
    {L : Type*} [Field L] [Algebra K L]
    (vK : AbsoluteValue K ℝ) (vL : AbsoluteValue L ℝ)
    (hvL : IsNonarchimedean vL)
    (hext : ∀ x : K, vL (algebraMap K L x) = vK x)
    {f : K[X]} (hf : (f.map (algebraMap K L)).Splits)
    {c : ℝ} (hc : 0 < c) :
    f.gaussNorm vK c =
      vK f.leadingCoeff * (f.aroots L |>.map fun a ↦ max c (vL a)).prod := by
  rw [← gauss_absolute_extension
    (algebraMap K L) (algebraMap K L).injective vK vL hext f c]
  rw [gauss_leading_max vL hvL hf hc]
  rw [Polynomial.leadingCoeff_map_of_injective (algebraMap K L).injective, hext]

/-- Monic form of `gauss_max_aroot`. -/
theorem gauss_aroots_monic
    {L : Type*} [Field L] [Algebra K L]
    (vK : AbsoluteValue K ℝ) (vL : AbsoluteValue L ℝ)
    (hvL : IsNonarchimedean vL)
    (hext : ∀ x : K, vL (algebraMap K L x) = vK x)
    {f : K[X]} (hf : (f.map (algebraMap K L)).Splits) (hmonic : f.Monic)
    {c : ℝ} (hc : 0 < c) :
    f.gaussNorm vK c = (f.aroots L |>.map fun a ↦ max c (vL a)).prod := by
  rw [gauss_max_aroot vK vL hvL hext hf hc,
    hmonic.leadingCoeff]
  simp

section RootStrata

variable {F L : Type*} [NontriviallyNormedField F] [Field L] [Algebra F L]
  [Algebra.IsAlgebraic F L] [IsUltrametricDist F] [CompleteSpace F]

/-- Milne, Proposition 7.44, first assertion in its characteristic-zero
algebraic-closure setting: the base Newton-polygon face of slope `s` counts
the roots of that finite additive value in the algebraic closure. -/
theorem newton_slope_aroots
    [CharZero F] [IsAlgClosed L] {f : F[X]} (hmonic : f.Monic) (s : ℝ) :
    newtonSlopeLength (NormedField.toAbsoluteValue F) f hmonic.ne_zero s =
      (f.aroots L).countP fun a ↦
        completeAbsoluteValue F L a = Real.exp (-s) := by
  apply slope_length_aroots
    (NormedField.toAbsoluteValue F)
    (completeAbsoluteValue F L)
    (complete_absolute_nonarchimedean F L)
  · intro x
    exact complete_absolute_algebra F L x
  · exact IsAlgClosed.splits _
  · exact hmonic

/-- The canonical extension of the absolute value is invariant under every
automorphism over the complete base field. -/
theorem complete_absolute_alg
    (sigma : L ≃ₐ[F] L) (x : L) :
    completeAbsoluteValue F L (sigma x) =
      completeAbsoluteValue F L x := by
  exact (spectralNorm_eq_of_equiv sigma x).symm

/-- Roots of one monic irreducible factor have the same value under the unique
extension of the absolute value.  Thus every value stratum of the roots of a
polynomial over `F` is a union of complete irreducible factors, which is the
descent input in the second assertion of Milne's Proposition 7.44. -/
theorem complete_roots_irreducible
    {f : F[X]} (hirr : Irreducible f) (hmonic : f.Monic)
    {x y : L} (hx : Polynomial.aeval x f = 0)
    (hy : Polynomial.aeval y f = 0) :
    completeAbsoluteValue F L x =
      completeAbsoluteValue F L y := by
  have hxint : IsIntegral F x := ⟨f, hmonic, hx⟩
  have hyint : IsIntegral F y := ⟨f, hmonic, hy⟩
  have hxmin : f = minpoly F x :=
    minpoly.eq_of_irreducible_of_monic hirr hx hmonic
  have hymin : f = minpoly F y :=
    minpoly.eq_of_irreducible_of_monic hirr hy hmonic
  rw [complete_absolute_rpow,
    complete_absolute_rpow, ← hxmin, ← hymin]

/-- Milne, Proposition 7.44, second assertion for the canonical absolute-value
extension: the factor formed by all roots of one absolute value descends to the
base field. -/
theorem complete_extension_factor
    [IsGalois F L]
    (s : ℝ) (p : F[X]) (hsplit : (p.map (algebraMap F L)).Splits) :
    ∃ q : F[X], q.map (algebraMap F L) =
      newtonRootFactor (completeAbsoluteValue F L) s p := by
  apply newton_root_factor
    (completeAbsoluteValue F L) s p hsplit
  intro sigma x
  exact complete_absolute_alg sigma x

/-- Milne, Proposition 7.44, second assertion in the source's characteristic
zero algebraic-closure setting.  No finite splitting-field or separately
supplied Galois hypothesis is needed: an algebraically closed algebraic
extension of a characteristic-zero field is Galois. -/
theorem complete_algebraic_closure
    [CharZero F] [IsAlgClosed L]
    (s : ℝ) (p : F[X]) :
    ∃ q : F[X], q.map (algebraMap F L) =
      newtonRootFactor (completeAbsoluteValue F L) s p := by
  letI : Normal F L := normal_iff.mpr fun x =>
    ⟨Algebra.IsAlgebraic.isIntegral.isIntegral x, IsAlgClosed.splits _⟩
  letI : IsGalois F L := IsGalois.mk
  exact complete_extension_factor s p
    (IsAlgClosed.splits _)

end RootStrata

end

end Towers.NumberTheory.Milne
