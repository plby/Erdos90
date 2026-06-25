import Towers.Algebra.DenseGenerators.JenningsSeparationCore


open Filter
open scoped Pointwise EuclideanGeometry Topology

noncomputable section

universe u v

open NumberField

namespace Towers
namespace TJennin

/-- In a quotient where the successor Zassenhaus term has been killed, membership in that
successor term is the same thing as being the identity element. -/
lemma killed_succ_one
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q]
    {n : ℕ}
    (hbot : zassenhausFiltration p Q (n + 1) = ⊥)
    {q : Q} :
    q ∈ zassenhausFiltration p Q (n + 1) ↔ q = 1 := by
  constructor
  · intro hq
    have hqbot : q ∈ (⊥ : Subgroup Q) := by
      simpa [hbot] using hq
    exact Subgroup.mem_bot.mp hqbot
  · intro hq
    rw [hq]
    exact (zassenhausFiltration p Q (n + 1)).one_mem

/-- A nonidentity element cannot lie in the killed successor Zassenhaus term. -/
lemma not_killed_ne
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q]
    {n : ℕ}
    (hbot : zassenhausFiltration p Q (n + 1) = ⊥)
    {q : Q}
    (hq : q ≠ 1) :
    q ∉ zassenhausFiltration p Q (n + 1) := by
  intro hmem
  have hq_one : q = 1 :=
    (killed_succ_one
      (p := p) (Q := Q) (n := n) hbot).1 hmem
  exact hq hq_one

namespace OZReps

/-- In the killed quotient, the ordered normal-form word is the identity exactly when all
coordinates vanish. This is the formal uniqueness statement from Step 4, read through the
`mem_iff_below` field of `OZReps`. -/
lemma word_zero_killed
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q]
    {m : ℕ}
    (R : OZReps p Q m)
    (hbot : zassenhausFiltration p Q m = ⊥)
    {e : Fin R.r → Fin p} :
    R.wordEquiv e = 1 ↔ ∀ i, e i = 0 := by
  constructor
  · intro he i
    have hmem :
        R.wordEquiv e ∈ zassenhausFiltration p Q m := by
      rw [he]
      exact (zassenhausFiltration p Q m).one_mem
    exact
      ((R.mem_iff_below (t := m) le_rfl e).1 hmem)
        i (R.weight_lt i)
  · intro hzero
    have hmem :
        R.wordEquiv e ∈ zassenhausFiltration p Q m := by
      exact
        (R.mem_iff_below (t := m) le_rfl e).2
          (fun i _hi => hzero i)
    have hbotmem : R.wordEquiv e ∈ (⊥ : Subgroup Q) := by
      simpa [hbot] using hmem
    exact Subgroup.mem_bot.mp hbotmem

/-- A nonidentity normal-form word has a nonzero coordinate. -/
lemma nonzero_coord_ne
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q]
    {m : ℕ}
    (R : OZReps p Q m)
    (hbot : zassenhausFiltration p Q m = ⊥)
    {e : Fin R.r → Fin p}
    (he : R.wordEquiv e ≠ 1) :
    ∃ i : Fin R.r, e i ≠ 0 := by
  classical
  by_contra hnone
  have hzero : ∀ i : Fin R.r, e i = 0 := by
    intro i
    by_contra hi
    exact hnone ⟨i, hi⟩
  exact he ((word_zero_killed R hbot).2 hzero)

/-- Every nonidentity group element has a normal-form exponent vector with a nonzero coordinate
of weight below the killed level. -/
lemma nonzero_form_coord
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q]
    {m : ℕ}
    (R : OZReps p Q m)
    (hbot : zassenhausFiltration p Q m = ⊥)
    {q : Q}
    (hq : q ≠ 1) :
    ∃ e : Fin R.r → Fin p,
      ∃ i : Fin R.r,
        R.wordEquiv e = q ∧ e i ≠ 0 ∧ R.weight i < m := by
  classical
  let e : Fin R.r → Fin p := R.wordEquiv.symm q
  have heq : R.wordEquiv e = q := by
    simp [e]
  have hword_ne : R.wordEquiv e ≠ 1 := by
    intro hword
    exact hq (by simpa [heq] using hword)
  obtain ⟨i, hi⟩ :=
    nonzero_coord_ne R hbot hword_ne
  exact ⟨e, i, heq, hi, R.weight_lt i⟩

/-- Membership in a layer is equivalent to vanishing of all lower-weight normal-form
coordinates. This restates the `OZReps` field in a lemma form convenient for the
later Jennings-basis construction. -/
lemma word_zero_below
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q]
    {m t : ℕ}
    (R : OZReps p Q m)
    (ht : t ≤ m)
    (e : Fin R.r → Fin p) :
    R.wordEquiv e ∈ zassenhausFiltration p Q t ↔
      ∀ i, R.weight i < t → e i = 0 := by
  exact R.mem_iff_below ht e

end OZReps

/-- The TeX normal-form package for the truncated Jennings argument.

This records the concrete output of Steps 3--12 of `S.tex`: ordered representatives, a Jennings
monomial basis, equality between augmentation powers and high-weight spans, and a low-weight
coordinate detecting every nontrivial group element after `D_m` has been killed. -/
structure NFData
    (p : ℕ) [Fact p.Prime]
    (Q : Type u) [Group Q] [Finite Q]
    (m : ℕ) : Type (max (u + 1) (v + 1)) where
  reps : OZReps p Q m
  ι : Type v
  decEq : DecidableEq ι
  basis : Module.Basis ι (ZMod p) (denseGroupAlgebra p Q)
  weight : ι → ℕ
  aug_high :
    augmentationIdealPower p Q m =
      basisHighSpan (p := p) (Q := Q) basis weight m
  separates_nontrivial :
    ∀ {q : Q}, q ≠ 1 →
      ∃ e : ι,
        weight e < m ∧
          basis.repr (groupAlgebraSub p Q q) e ≠ 0

/-- Step 6--8 data: the ordered Jennings monomials attached to a chosen normal-form system form
a basis, and the basis is indexed with the expected Jennings weight. -/
structure MBData
    (p : ℕ) [Fact p.Prime]
    {Q : Type u} [Group Q] [Finite Q]
    {m : ℕ}
    (R : OZReps p Q m) : Type (max (u + 1) (v + 1)) where
  ι : Type v
  decEq : DecidableEq ι
  basis : Module.Basis ι (ZMod p) (denseGroupAlgebra p Q)
  weight : ι → ℕ
  monomialIndex : ι ≃ (Fin R.r → Fin p)
  basis_apply :
    ∀ e : ι,
      basis e =
        jenningsMonomialFin p Q R.gen (monomialIndex e)
  weight_apply :
    ∀ e : ι,
      weight e = expWeight R.weight (monomialIndex e)

namespace MBData

/-- The canonical ordered Jennings monomial basis attached directly to
`OZReps`, packaged in the truncated-Jennings `MBData` interface. -/
noncomputable def canonical
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q] [Finite Q]
    {m : ℕ}
    (R : OZReps p Q m) :
    MBData.{u, 0} (p := p) (Q := Q) R where
  ι := Fin R.r → Fin p
  decEq := inferInstance
  basis := R.jenningsMonomialBasis
  weight := fun e => expWeight R.weight e
  monomialIndex := Equiv.refl (Fin R.r → Fin p)
  basis_apply := by
    intro e
    exact R.monomial_basis e
  weight_apply := by
    intro e
    rfl

@[simp]
lemma canonical_monomialIndex
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q] [Finite Q]
    {m : ℕ}
    (R : OZReps p Q m)
    (e : Fin R.r → Fin p) :
    (canonical (p := p) (Q := Q) R).monomialIndex e = e :=
  rfl

@[simp]
lemma canonical_monomial_symm
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q] [Finite Q]
    {m : ℕ}
    (R : OZReps p Q m)
    (e : Fin R.r → Fin p) :
    (canonical (p := p) (Q := Q) R).monomialIndex.symm e = e :=
  rfl

end MBData

/-- If every exponent is zero, the Jennings weight of the exponent vector is zero. -/
lemma exp_weight_forall
    {p r : ℕ}
    [NeZero p]
    (wt : Fin r → ℕ)
    {e : Fin r → Fin p}
    (hzero : ∀ i, e i = 0) :
    expWeight wt e = 0 := by
  simp [expWeight, hzero]

/-- A nonzero coordinate has positive natural value. -/
lemma fin_val_pos
    {p : ℕ} [NeZero p]
    {a : Fin p}
    (ha : a ≠ 0) :
    0 < a.val := by
  apply Nat.pos_of_ne_zero
  intro hval
  apply ha
  ext
  simp [hval]

/-- A single term of the Jennings weight sum is bounded by the whole sum. -/
lemma exp_weight_term
    {p r : ℕ}
    (wt : Fin r → ℕ)
    (e : Fin r → Fin p)
    (i : Fin r) :
    (e i).val * wt i ≤ expWeight wt e := by
  unfold expWeight
  exact
    Finset.single_le_sum
      (fun j _hj => Nat.zero_le ((e j).val * wt j))
      (Finset.mem_univ i)

/-- If a nonzero exponent occurs only at weights at least `s`, then the total Jennings weight is
at least `s`. This is the arithmetic core of Step 9 in `S.tex`. -/
lemma exp_ne_below
    {p r s : ℕ}
    [NeZero p]
    {wt : Fin r → ℕ}
    {e : Fin r → Fin p}
    (hzeroBelow : ∀ i, wt i < s → e i = 0)
    (hne : ∃ i, e i ≠ 0) :
    s ≤ expWeight wt e := by
  rcases hne with ⟨i, hi⟩
  have hwt_not_lt : ¬ wt i < s := by
    intro hlt
    exact hi (hzeroBelow i hlt)
  have hwt_ge : s ≤ wt i := le_of_not_gt hwt_not_lt
  have hval_pos : 0 < (e i).val := fin_val_pos hi
  have hwt_le_term : wt i ≤ (e i).val * wt i := by
    simpa [Nat.mul_comm] using Nat.le_mul_of_pos_right (wt i) hval_pos
  exact le_trans hwt_ge (le_trans hwt_le_term (exp_weight_term wt e i))

/-- If every generator has positive weight, then every nonconstant exponent vector has positive
Jennings weight. -/
lemma exp_pos_ne
    {p r : ℕ}
    [NeZero p]
    {wt : Fin r → ℕ}
    {e : Fin r → Fin p}
    (hwt_pos : ∀ i, 0 < wt i)
    (hne : ∃ i, e i ≠ 0) :
    0 < expWeight wt e := by
  rcases hne with ⟨i, hi⟩
  have hval_pos : 0 < (e i).val := fin_val_pos hi
  have hterm_pos : 0 < (e i).val * wt i :=
    Nat.mul_pos hval_pos (hwt_pos i)
  exact lt_of_lt_of_le hterm_pos (exp_weight_term wt e i)

/-- With positive generator weights, zero Jennings weight is equivalent to all exponents being
zero. -/
lemma exp_forall_pos
    {p r : ℕ}
    [NeZero p]
    {wt : Fin r → ℕ}
    {e : Fin r → Fin p}
    (hwt_pos : ∀ i, 0 < wt i) :
    expWeight wt e = 0 ↔ ∀ i, e i = 0 := by
  constructor
  · intro hweight i
    by_contra hi
    have hpos : 0 < expWeight wt e :=
      exp_pos_ne hwt_pos ⟨i, hi⟩
    omega
  · intro hzero
    exact exp_weight_forall wt hzero

/-- If all lower-weight coordinates vanish and the total weight is still below the cutoff, then
the exponent vector was zero after all. -/
lemma forall_exp_below
    {p r s : ℕ}
    [NeZero p]
    {wt : Fin r → ℕ}
    {e : Fin r → Fin p}
    (hzeroBelow : ∀ i, wt i < s → e i = 0)
    (hlt : expWeight wt e < s) :
    ∀ i, e i = 0 := by
  by_contra hnot
  have hne : ∃ i, e i ≠ 0 := by
    by_contra hnone
    apply hnot
    intro i
    by_contra hi
    exact hnone ⟨i, hi⟩
  have hs_le : s ≤ expWeight wt e :=
    exp_ne_below hzeroBelow hne
  omega

/-- The exponent vector for the single Jennings variable `i`. -/
def singleJenningsExponent
    {p r : ℕ}
    [NeZero p]
    (i : Fin r) :
    Fin r → Fin p :=
  fun j => if j = i then 1 else 0

/-- The single-variable exponent is `1` at its chosen coordinate. -/
lemma single_jennings_self
    {p r : ℕ}
    [NeZero p]
    (i : Fin r) :
    singleJenningsExponent (p := p) i i = 1 := by
  simp [singleJenningsExponent]

/-- The single-variable exponent is `0` away from its chosen coordinate. -/
lemma single_ne
    {p r : ℕ}
    [NeZero p]
    {i j : Fin r}
    (hji : j ≠ i) :
    singleJenningsExponent (p := p) i j = 0 := by
  simp [singleJenningsExponent, hji]

/-- The exponent vector supported at one coordinate with an arbitrary bounded exponent.

This is the bookkeeping object needed for the one-factor binomial expansions in Step 7:
the group word `x_i^k` has normal-form exponent vector `coordinateJenningsExponent i k`. -/
def coordinateJenningsExponent
    {p r : ℕ}
    [NeZero p]
    (i : Fin r)
    (k : Fin p) :
    Fin r → Fin p :=
  fun j => if j = i then k else 0

/-- A one-coordinate exponent has the requested value at its chosen coordinate. -/
lemma coordinate_jennings_self
    {p r : ℕ}
    [NeZero p]
    (i : Fin r)
    (k : Fin p) :
    coordinateJenningsExponent (p := p) i k i = k := by
  simp [coordinateJenningsExponent]

/-- A one-coordinate exponent vanishes away from its chosen coordinate. -/
lemma coordinate_jennings_ne
    {p r : ℕ}
    [NeZero p]
    {i j : Fin r}
    (hji : j ≠ i)
    (k : Fin p) :
    coordinateJenningsExponent (p := p) i k j = 0 := by
  simp [coordinateJenningsExponent, hji]

/-- The one-coordinate exponent with zero value is the zero exponent vector. -/
lemma coordinate_jennings_zero
    {p r : ℕ}
    [NeZero p]
    (i : Fin r) :
    coordinateJenningsExponent (p := p) i 0 =
      (fun _ : Fin r => (0 : Fin p)) := by
  funext j
  by_cases hji : j = i
  · subst j
    simp [coordinate_jennings_self]
  · simp [coordinate_jennings_ne (p := p) hji]

/-- The one-coordinate exponent with value `1` is the single Jennings exponent. -/
lemma coordinate_jennings_one
    {p r : ℕ}
    [NeZero p]
    (i : Fin r) :
    coordinateJenningsExponent (p := p) i 1 =
      singleJenningsExponent (p := p) i := by
  funext j
  by_cases hji : j = i
  · subst j
    simp [coordinate_jennings_self, single_jennings_self]
  · simp [coordinate_jennings_ne (p := p) hji,
      single_ne (p := p) hji]

/-- Coordinatewise comparison of bounded Jennings exponent vectors.

This is the partial order used in the unitriangular Step 7 argument: a monomial with exponent
`a` can occur in the binomial expansion of a normal-form word with exponent `b` only when every
coordinate of `a` is bounded by the corresponding coordinate of `b`. -/
def exponentCoordinatewiseLE
    {p r : ℕ}
    (a b : Fin r → Fin p) : Prop :=
  ∀ j : Fin r, (a j).val ≤ (b j).val

/-- Coordinatewise comparison is reflexive. -/
lemma exponent_coordinatewise_refl
    {p r : ℕ}
    (a : Fin r → Fin p) :
    exponentCoordinatewiseLE a a := by
  intro j
  rfl

/-- Coordinatewise comparison is transitive. -/
lemma exponent_trans
    {p r : ℕ}
    {a b c : Fin r → Fin p}
    (hab : exponentCoordinatewiseLE a b)
    (hbc : exponentCoordinatewiseLE b c) :
    exponentCoordinatewiseLE a c := by
  intro j
  exact le_trans (hab j) (hbc j)

/-- Two bounded exponent vectors which are coordinatewise bounded in both directions are equal. -/
lemma exponent_coordinatewise_antisymm
    {p r : ℕ}
    {a b : Fin r → Fin p}
    (hab : exponentCoordinatewiseLE a b)
    (hba : exponentCoordinatewiseLE b a) :
    a = b := by
  funext j
  exact Fin.ext (le_antisymm (hab j) (hba j))

/-- The zero exponent vector is coordinatewise below every exponent vector. -/
lemma exponent_coordinatewise_left
    {p r : ℕ}
    [NeZero p]
    (a : Fin r → Fin p) :
    exponentCoordinatewiseLE (fun _ : Fin r => (0 : Fin p)) a := by
  intro j
  exact Nat.zero_le (a j).val

/-- Equality of exponent vectors gives coordinatewise comparison. -/
lemma exponent_coordinatewise
    {p r : ℕ}
    {a b : Fin r → Fin p}
    (h : a = b) :
    exponentCoordinatewiseLE a b := by
  rw [h]
  exact exponent_coordinatewise_refl b

/-- To be below a one-coordinate exponent, all other coordinates must vanish and the chosen
coordinate must be bounded by that one value. -/
lemma exponent_coordinatewise_jennings
    {p r : ℕ}
    [NeZero p]
    {a : Fin r → Fin p}
    (i : Fin r)
    (k : Fin p) :
    exponentCoordinatewiseLE a (coordinateJenningsExponent (p := p) i k) ↔
      (a i).val ≤ k.val ∧ ∀ j : Fin r, j ≠ i → a j = 0 := by
  constructor
  · intro ha
    constructor
    · simpa [coordinate_jennings_self] using ha i
    · intro j hji
      have hle : (a j).val ≤ 0 := by
        simpa [coordinateJenningsExponent, hji] using ha j
      exact Fin.ext (Nat.eq_zero_of_le_zero hle)
  · rintro ⟨hi, hzero⟩ j
    by_cases hji : j = i
    · subst j
      simpa [coordinate_jennings_self] using hi
    · have hz : a j = 0 := hzero j hji
      simp [hz, coordinateJenningsExponent, hji]

/-- Comparing two one-coordinate exponent vectors at the same coordinate is just comparing their
chosen finite values. -/
lemma exponent_coordinatewise_val
    {p r : ℕ}
    [NeZero p]
    (i : Fin r)
    (k l : Fin p) :
    exponentCoordinatewiseLE
        (coordinateJenningsExponent (p := p) i k)
        (coordinateJenningsExponent (p := p) i l) ↔
      k.val ≤ l.val := by
  constructor
  · intro h
    simpa [coordinate_jennings_self] using h i
  · intro hkl j
    by_cases hji : j = i
    · subst j
      simpa [coordinate_jennings_self] using hkl
    · simp [coordinateJenningsExponent, hji]

/-- Monotonicity of the one-coordinate exponent constructor. -/
lemma coordinatewise_jennings_val
    {p r : ℕ}
    [NeZero p]
    {i : Fin r}
    {k l : Fin p}
    (hkl : k.val ≤ l.val) :
    exponentCoordinatewiseLE
      (coordinateJenningsExponent (p := p) i k)
      (coordinateJenningsExponent (p := p) i l) := by
  exact
    (exponent_coordinatewise_val
      (p := p) i k l).2 hkl

/-- Any exponent vector below a one-coordinate exponent is itself a one-coordinate exponent,
with value equal to its chosen coordinate. -/
lemma coordinate_jennings_exponent
    {p r : ℕ}
    [NeZero p]
    {a : Fin r → Fin p}
    {i : Fin r}
    {k : Fin p}
    (ha : exponentCoordinatewiseLE a (coordinateJenningsExponent (p := p) i k)) :
    a = coordinateJenningsExponent (p := p) i (a i) := by
  have hdesc :=
    (exponent_coordinatewise_jennings (p := p) i k).1 ha
  funext j
  by_cases hji : j = i
  · subst j
    simp [coordinate_jennings_self]
  · rw [hdesc.2 j hji]
    exact (coordinate_jennings_ne (p := p) hji (a i)).symm

/-- If an exponent below a one-coordinate exponent has a prescribed value at the chosen
coordinate, then it is the corresponding one-coordinate exponent. -/
lemma coordinate_jennings_coord
    {p r : ℕ}
    [NeZero p]
    {a : Fin r → Fin p}
    {i : Fin r}
    {k l : Fin p}
    (ha : exponentCoordinatewiseLE a (coordinateJenningsExponent (p := p) i k))
    (hi : a i = l) :
    a = coordinateJenningsExponent (p := p) i l := by
  rw [coordinate_jennings_exponent
    (p := p) ha, hi]

/-- The unweighted total degree of a bounded exponent vector. This is not the Jennings weight;
it is only a finite induction measure for the triangular linear algebra in Step 7. -/
def exponentTotalDegree
    {p r : ℕ}
    (a : Fin r → Fin p) : ℕ :=
  ∑ j : Fin r, (a j).val

/-- Coordinatewise comparison can only increase total degree. -/
lemma exponent_coordinatewise_degree
    {p r : ℕ}
    {a b : Fin r → Fin p}
    (hab : exponentCoordinatewiseLE a b) :
    exponentTotalDegree a ≤ exponentTotalDegree b := by
  unfold exponentTotalDegree
  exact Finset.sum_le_sum (fun j _hj => hab j)

/-- If `a ≤ b` coordinatewise and one coordinate is strictly smaller, then the total degree is
strictly smaller. -/
lemma coordinatewise_total_degree
    {p r : ℕ}
    {a b : Fin r → Fin p}
    (hab : exponentCoordinatewiseLE a b)
    (hstrict : ∃ j : Fin r, (a j).val < (b j).val) :
    exponentTotalDegree a < exponentTotalDegree b := by
  unfold exponentTotalDegree
  rcases hstrict with ⟨j, hj⟩
  exact
    Finset.sum_lt_sum
      (fun i _hi => hab i)
      ⟨j, Finset.mem_univ j, hj⟩

/-- A proper coordinatewise inequality strictly lowers total degree. -/
lemma coordinatewise_total_ne
    {p r : ℕ}
    {a b : Fin r → Fin p}
    (hab : exponentCoordinatewiseLE a b)
    (hne : a ≠ b) :
    exponentTotalDegree a < exponentTotalDegree b := by
  have hcoord : ∃ j : Fin r, a j ≠ b j := by
    by_contra hnone
    apply hne
    funext j
    by_contra hj
    exact hnone ⟨j, hj⟩
  rcases hcoord with ⟨j, hj⟩
  have hval_ne : (a j).val ≠ (b j).val := by
    intro hval
    exact hj (Fin.ext hval)
  have hlt : (a j).val < (b j).val := lt_of_le_of_ne (hab j) hval_ne
  exact coordinatewise_total_degree hab ⟨j, hlt⟩

/-- If `a ≤ b` coordinatewise and `b` has no larger total degree than `a`, then `a = b`.

This is the induction-stopping lemma for the Step 7 triangular inversion: among terms lying
below a fixed exponent, the top total degree can only occur at the top exponent itself. -/
lemma exponent_coordinatewise_total
    {p r : ℕ}
    {a b : Fin r → Fin p}
    (hab : exponentCoordinatewiseLE a b)
    (hdeg : exponentTotalDegree b ≤ exponentTotalDegree a) :
    a = b := by
  by_contra hne
  have hlt : exponentTotalDegree a < exponentTotalDegree b :=
    coordinatewise_total_ne hab hne
  exact (not_lt_of_ge hdeg) hlt

/-- For coordinatewise-comparable exponent vectors, equality of total degrees is the same as
equality of exponent vectors. -/
lemma exponent_total_degree
    {p r : ℕ}
    {a b : Fin r → Fin p}
    (hab : exponentCoordinatewiseLE a b) :
    exponentTotalDegree a = exponentTotalDegree b ↔ a = b := by
  constructor
  · intro hdeg
    exact exponent_coordinatewise_total hab (by omega)
  · intro h
    subst h
    rfl

/-- Strict coordinatewise comparison, used to describe the off-diagonal terms in Step 7. -/
def exponentCoordinatewiseLT
    {p r : ℕ}
    (a b : Fin r → Fin p) : Prop :=
  exponentCoordinatewiseLE a b ∧ a ≠ b

/-- Strict coordinatewise comparison implies strict decrease of total degree. -/
lemma coordinatewise_total
    {p r : ℕ}
    {a b : Fin r → Fin p}
    (hab : exponentCoordinatewiseLT a b) :
    exponentTotalDegree a < exponentTotalDegree b :=
  coordinatewise_total_ne hab.1 hab.2

/-- No exponent vector is strictly coordinatewise below itself. -/
lemma not_coordinatewise_self
    {p r : ℕ}
    (a : Fin r → Fin p) :
    ¬ exponentCoordinatewiseLT a a := by
  intro haa
  exact haa.2 rfl

/-- Strict-below followed by weak-below is strict-below. -/
lemma coordinatewise_trans
    {p r : ℕ}
    {a b c : Fin r → Fin p}
    (hab : exponentCoordinatewiseLT a b)
    (hbc : exponentCoordinatewiseLE b c) :
    exponentCoordinatewiseLT a c := by
  refine ⟨exponent_trans hab.1 hbc, ?_⟩
  intro hac
  apply hab.2
  exact exponent_coordinatewise_antisymm hab.1 (by simpa [hac] using hbc)

/-- Weak-below followed by strict-below is strict-below. -/
lemma exponent_coordinatewise_trans
    {p r : ℕ}
    {a b c : Fin r → Fin p}
    (hab : exponentCoordinatewiseLE a b)
    (hbc : exponentCoordinatewiseLT b c) :
    exponentCoordinatewiseLT a c := by
  refine ⟨exponent_trans hab hbc.1, ?_⟩
  intro hac
  apply hbc.2
  exact exponent_coordinatewise_antisymm hbc.1 (by simpa [hac] using hab)

/-- The finite set of exponent vectors coordinatewise below a fixed vector. -/
def exponentCoordinatewiseFinset
    {p r : ℕ}
    (e : Fin r → Fin p) :
    Finset (Fin r → Fin p) :=
  by
    classical
    exact Finset.univ.filter fun a => exponentCoordinatewiseLE a e

/-- Membership in the finite lower set is exactly coordinatewise comparison. -/
lemma exponent_lower_finset
    {p r : ℕ}
    {e a : Fin r → Fin p} :
    a ∈ exponentCoordinatewiseFinset e ↔ exponentCoordinatewiseLE a e := by
  classical
  simp [exponentCoordinatewiseFinset]

/-- The top exponent belongs to its own coordinatewise lower set. -/
lemma self_coordinatewise_finset
    {p r : ℕ}
    (e : Fin r → Fin p) :
    e ∈ exponentCoordinatewiseFinset e := by
  exact
    (exponent_lower_finset (e := e) (a := e)).2
      (exponent_coordinatewise_refl e)

/-- The zero exponent belongs to every coordinatewise lower set. -/
lemma coordinatewise_lower_finset
    {p r : ℕ}
    [NeZero p]
    (e : Fin r → Fin p) :
    (fun _ : Fin r => (0 : Fin p)) ∈ exponentCoordinatewiseFinset e := by
  exact
    (exponent_lower_finset
      (e := e) (a := fun _ : Fin r => (0 : Fin p))).2
      (exponent_coordinatewise_left e)

/-- Membership below a one-coordinate exponent is exactly the corresponding one-coordinate
description. -/
lemma finset_jennings_exponent
    {p r : ℕ}
    [NeZero p]
    {a : Fin r → Fin p}
    (i : Fin r)
    (k : Fin p) :
    a ∈ exponentCoordinatewiseFinset (coordinateJenningsExponent (p := p) i k) ↔
      (a i).val ≤ k.val ∧ ∀ j : Fin r, j ≠ i → a j = 0 := by
  constructor
  · intro ha
    exact
      (exponent_coordinatewise_jennings
        (p := p) i k).1
        ((exponent_lower_finset
          (e := coordinateJenningsExponent (p := p) i k) (a := a)).1 ha)
  · intro hdesc
    exact
      (exponent_lower_finset
        (e := coordinateJenningsExponent (p := p) i k) (a := a)).2
        ((exponent_coordinatewise_jennings
          (p := p) i k).2 hdesc)

/-- A smaller value at the same coordinate gives an element of the lower set under a
one-coordinate exponent. -/
lemma jennings_finset_val
    {p r : ℕ}
    [NeZero p]
    {i : Fin r}
    {k l : Fin p}
    (hlk : l.val ≤ k.val) :
    coordinateJenningsExponent (p := p) i l ∈
      exponentCoordinatewiseFinset (coordinateJenningsExponent (p := p) i k) := by
  exact
    (exponent_lower_finset
      (e := coordinateJenningsExponent (p := p) i k)
      (a := coordinateJenningsExponent (p := p) i l)).2
      (coordinatewise_jennings_val
        (p := p) hlk)

/-- The finite set of bounded exponents `l` with `l ≤ k` in the chosen coordinate. -/
def coordinateJenningsFinset
    {p : ℕ}
    (k : Fin p) : Finset (Fin p) :=
  Finset.univ.filter (fun l : Fin p => l.val ≤ k.val)

/-- Membership in the one-coordinate value lower set is exactly the natural-value inequality. -/
lemma jennings_lower_finset
    {p : ℕ}
    {k l : Fin p} :
    l ∈ coordinateJenningsFinset k ↔ l.val ≤ k.val := by
  classical
  simp [coordinateJenningsFinset]

/-- The top value belongs to its own one-coordinate value lower set. -/
lemma self_jennings_finset
    {p : ℕ}
    (k : Fin p) :
    k ∈ coordinateJenningsFinset k := by
  exact (jennings_lower_finset (k := k) (l := k)).2 le_rfl

/-- Zero belongs to every one-coordinate value lower set. -/
lemma jennings_value_finset
    {p : ℕ}
    [NeZero p]
    (k : Fin p) :
    (0 : Fin p) ∈ coordinateJenningsFinset k := by
  exact
    (jennings_lower_finset (k := k) (l := 0)).2
      (Nat.zero_le k.val)

/-- Values in the one-coordinate lower set give one-coordinate exponent vectors below the
corresponding top exponent. -/
lemma exponent_coordinatewise_finset
    {p r : ℕ}
    [NeZero p]
    {i : Fin r}
    {k l : Fin p}
    (hl : l ∈ coordinateJenningsFinset k) :
    exponentCoordinatewiseLE
      (coordinateJenningsExponent (p := p) i l)
      (coordinateJenningsExponent (p := p) i k) := by
  exact
    coordinatewise_jennings_val
      (p := p)
      ((jennings_lower_finset (k := k) (l := l)).1 hl)

/-- Every lower-set element under a one-coordinate exponent is the one-coordinate exponent
with its own chosen-coordinate value. -/
lemma coordinate_jennings_finset
    {p r : ℕ}
    [NeZero p]
    {a : Fin r → Fin p}
    {i : Fin r}
    {k : Fin p}
    (ha : a ∈ exponentCoordinatewiseFinset
      (coordinateJenningsExponent (p := p) i k)) :
    a = coordinateJenningsExponent (p := p) i (a i) := by
  exact
    coordinate_jennings_exponent
      (p := p)
      ((exponent_lower_finset
        (e := coordinateJenningsExponent (p := p) i k) (a := a)).1 ha)

/-- Elements of the coordinatewise lower set have no larger total degree than the top exponent. -/
lemma exponent_total_finset
    {p r : ℕ}
    {e a : Fin r → Fin p}
    (ha : a ∈ exponentCoordinatewiseFinset e) :
    exponentTotalDegree a ≤ exponentTotalDegree e :=
  exponent_coordinatewise_degree
    ((exponent_lower_finset (e := e) (a := a)).1 ha)

/-- The only element of the lower set with total degree at least the top exponent is the top
exponent. -/
lemma finset_total_degree
    {p r : ℕ}
    {e a : Fin r → Fin p}
    (ha : a ∈ exponentCoordinatewiseFinset e)
    (hdeg : exponentTotalDegree e ≤ exponentTotalDegree a) :
    a = e :=
  exponent_coordinatewise_total
    ((exponent_lower_finset (e := e) (a := a)).1 ha) hdeg

/-- Every non-top element in the lower set has strictly smaller total degree. -/
lemma total_finset_ne
    {p r : ℕ}
    {e a : Fin r → Fin p}
    (ha : a ∈ exponentCoordinatewiseFinset e)
    (hne : a ≠ e) :
    exponentTotalDegree a < exponentTotalDegree e :=
  coordinatewise_total_ne
    ((exponent_lower_finset (e := e) (a := a)).1 ha) hne

/-- In characteristic `p` with `p` prime, the element `1 : Fin p` is not zero. -/
lemma fin_ne_prime
    {p : ℕ} [Fact p.Prime] :
    (1 : Fin p) ≠ 0 := by
  have hp2 : 2 ≤ p := (Fact.out : Nat.Prime p).two_le
  intro h
  have hval := congrArg Fin.val h
  have hone_val : ((1 : Fin p).val) = 1 := by
    simp [Nat.mod_eq_of_lt (by omega : 1 < p)]
  have hzero_val : ((0 : Fin p).val) = 0 := by
    rfl
  omega

/-- A nonzero finite exponent gives a nonzero scalar in `ZMod p`.

This is the scalar arithmetic used in Step 12: the normal-form exponents live as `Fin p`
coordinates, while the coefficient of a Jennings linear term lives in the ground field
`ZMod p`. -/
lemma zmod_cast_val
    {p : ℕ} [Fact p.Prime]
    {a : Fin p}
    (ha : a ≠ 0) :
    ((a.val : ℕ) : ZMod p) ≠ 0 := by
  intro hcast
  have hdiv : p ∣ a.val :=
    (CharP.cast_eq_zero_iff (ZMod p) p a.val).1 hcast
  have hpos : 0 < a.val :=
    fin_val_pos ha
  have hp_le_val : p ≤ a.val :=
    Nat.le_of_dvd hpos hdiv
  exact (not_lt_of_ge hp_le_val) a.isLt

/-- A finite exponent has zero image in `ZMod p` exactly when it is the zero finite exponent. -/
lemma zmod_fin_val
    {p : ℕ} [Fact p.Prime]
    {a : Fin p} :
    ((a.val : ℕ) : ZMod p) = 0 ↔ a = 0 := by
  constructor
  · intro h
    by_contra ha
    exact zmod_cast_val ha h
  · intro h
    subst a
    simp

/-- The nonzero version of `zmod_fin_val`. -/
lemma zmod_val_ne
    {p : ℕ} [Fact p.Prime]
    {a : Fin p} :
    ((a.val : ℕ) : ZMod p) ≠ 0 ↔ a ≠ 0 := by
  constructor
  · intro h hzero
    exact h ((zmod_fin_val (p := p) (a := a)).2 hzero)
  · intro h
    exact zmod_cast_val h

/-- The single-variable exponent is a nonzero exponent vector. -/
lemma single_jennings_zero
    {p r : ℕ}
    [Fact p.Prime]
    (i : Fin r) :
    singleJenningsExponent (p := p) i ≠ 0 := by
  letI : NeZero p := ⟨(Fact.out : Nat.Prime p).ne_zero⟩
  intro h
  have hself :
      singleJenningsExponent (p := p) i i = (0 : Fin p) := by
    simpa using congrFun h i
  exact fin_ne_prime (by simpa [single_jennings_self] using hself)

/-- The Jennings weight of a single-variable exponent is exactly the weight of that variable. -/
lemma exp_single_exponent
    {p r : ℕ}
    [Fact p.Prime]
    (wt : Fin r → ℕ)
    (i : Fin r) :
    expWeight wt (singleJenningsExponent (p := p) i) = wt i := by
  letI : NeZero p := ⟨(Fact.out : Nat.Prime p).ne_zero⟩
  have hp1 : 1 < p := (Fact.out : Nat.Prime p).one_lt
  have hone_mod : 1 % p = 1 := Nat.mod_eq_of_lt hp1
  unfold expWeight
  rw [Finset.sum_eq_single i]
  · simp [singleJenningsExponent, hone_mod]
  · intro j _hj hji
    have hne : j ≠ i := by
      intro h
      exact hji h
    simp [singleJenningsExponent, hne]
  · intro hi
    exact False.elim (hi (Finset.mem_univ i))

/-- The total degree of the zero exponent vector is zero. -/
lemma exponent_total_zero
    {p r : ℕ}
    [NeZero p] :
    exponentTotalDegree (fun _ : Fin r => (0 : Fin p)) = 0 := by
  simp [exponentTotalDegree]

/-- The Jennings weight of a one-coordinate exponent is the chosen exponent value times the
weight of that coordinate. -/
lemma exp_jennings_exponent
    {p r : ℕ}
    [NeZero p]
    (wt : Fin r → ℕ)
    (i : Fin r)
    (k : Fin p) :
    expWeight wt (coordinateJenningsExponent (p := p) i k) = k.val * wt i := by
  unfold expWeight
  rw [Finset.sum_eq_single i]
  · simp [coordinate_jennings_self]
  · intro j _hj hji
    have hne : j ≠ i := by
      intro h
      exact hji h
    simp [coordinateJenningsExponent, hne]
  · intro hi
    exact False.elim (hi (Finset.mem_univ i))

/-- The total degree of a one-coordinate exponent is its chosen finite value. -/
lemma exponent_total_jennings
    {p r : ℕ}
    [NeZero p]
    (i : Fin r)
    (k : Fin p) :
    exponentTotalDegree (coordinateJenningsExponent (p := p) i k) = k.val := by
  unfold exponentTotalDegree
  rw [Finset.sum_eq_single i]
  · simp [coordinate_jennings_self]
  · intro j _hj hji
    have hne : j ≠ i := by
      intro h
      exact hji h
    simp [coordinateJenningsExponent, hne]
  · intro hi
    exact False.elim (hi (Finset.mem_univ i))

/-- The total degree of a single-variable exponent is one. -/
lemma exponent_total_single
    {p r : ℕ}
    [Fact p.Prime]
    (i : Fin r) :
    exponentTotalDegree (singleJenningsExponent (p := p) i) = 1 := by
  letI : NeZero p := ⟨(Fact.out : Nat.Prime p).ne_zero⟩
  have hp1 : 1 < p := (Fact.out : Nat.Prime p).one_lt
  have hone_mod : 1 % p = 1 := Nat.mod_eq_of_lt hp1
  unfold exponentTotalDegree
  rw [Finset.sum_eq_single i]
  · simp [singleJenningsExponent, hone_mod]
  · intro j _hj hji
    have hne : j ≠ i := by
      intro h
      exact hji h
    simp [singleJenningsExponent, hne]
  · intro hi
    exact False.elim (hi (Finset.mem_univ i))

/-- Coordinatewise comparison with a single-variable exponent means: the chosen coordinate is
at most `1`, and all other coordinates vanish. -/
lemma coordinatewise_single_jennings
    {p r : ℕ}
    [Fact p.Prime]
    {a : Fin r → Fin p}
    (i : Fin r) :
    exponentCoordinatewiseLE a (singleJenningsExponent (p := p) i) ↔
      (a i).val ≤ 1 ∧ ∀ j : Fin r, j ≠ i → a j = 0 := by
  letI : NeZero p := ⟨(Fact.out : Nat.Prime p).ne_zero⟩
  have hp1 : 1 < p := (Fact.out : Nat.Prime p).one_lt
  have hone_mod : 1 % p = 1 := Nat.mod_eq_of_lt hp1
  have hone_val : ((1 : Fin p).val) = 1 := by
    simp [hone_mod]
  constructor
  · intro ha
    constructor
    · have hi :
        (a i).val ≤ ((1 : Fin p).val) := by
        simpa [single_jennings_self (p := p) i] using ha i
      simpa [hone_mod] using hi
    · intro j hji
      have hle : (a j).val ≤ 0 := by
        simpa [single_ne (p := p) hji] using ha j
      exact Fin.ext (Nat.eq_zero_of_le_zero hle)
  · rintro ⟨hi, hzero⟩ j
    by_cases hji : j = i
    · subst j
      rw [single_jennings_self (p := p) i]
      simpa [hone_mod] using hi
    · have hz : a j = 0 := hzero j hji
      simp [hz, single_ne (p := p) hji]

/-- A coordinatewise-below-single exponent has total degree at most one. -/
lemma total_single_jennings
    {p r : ℕ}
    [Fact p.Prime]
    {a : Fin r → Fin p}
    {i : Fin r}
    (ha : exponentCoordinatewiseLE a (singleJenningsExponent (p := p) i)) :
    exponentTotalDegree a ≤ 1 := by
  have hle :
      exponentTotalDegree a ≤
        exponentTotalDegree (singleJenningsExponent (p := p) i) :=
    exponent_coordinatewise_degree ha
  simpa [exponent_total_single (p := p) i] using hle

/-- If an exponent vector lies below a single-variable exponent and has zero chosen coordinate,
then it is the zero exponent vector. -/
lemma jennings_exponent_coord
    {p r : ℕ}
    [Fact p.Prime]
    {a : Fin r → Fin p}
    {i : Fin r}
    (ha : exponentCoordinatewiseLE a (singleJenningsExponent (p := p) i))
    (hi : a i = 0) :
    a = fun _ : Fin r => (0 : Fin p) := by
  have hdesc :=
    (coordinatewise_single_jennings (p := p) i).1 ha
  funext j
  by_cases hji : j = i
  · subst j
    exact hi
  · exact hdesc.2 j hji

/-- If an exponent vector lies below a single-variable exponent and has chosen coordinate `1`,
then it is exactly that single-variable exponent. -/
lemma single_jennings_coord
    {p r : ℕ}
    [Fact p.Prime]
    {a : Fin r → Fin p}
    {i : Fin r}
    (ha : exponentCoordinatewiseLE a (singleJenningsExponent (p := p) i))
    (hi : a i = 1) :
    a = singleJenningsExponent (p := p) i := by
  have hdesc :=
    (coordinatewise_single_jennings (p := p) i).1 ha
  funext j
  by_cases hji : j = i
  · subst j
    simpa [single_jennings_self (p := p) i] using hi
  · rw [hdesc.2 j hji]
    exact (single_ne (p := p) hji).symm

/-- Every exponent vector below a single-variable exponent is either zero or the single exponent
itself. -/
lemma or_single_exponent
    {p r : ℕ}
    [Fact p.Prime]
    {a : Fin r → Fin p}
    {i : Fin r}
    (ha : exponentCoordinatewiseLE a (singleJenningsExponent (p := p) i)) :
    a = (fun _ : Fin r => (0 : Fin p)) ∨
      a = singleJenningsExponent (p := p) i := by
  letI : NeZero p := ⟨(Fact.out : Nat.Prime p).ne_zero⟩
  have hi_le_one : (a i).val ≤ 1 :=
    ((coordinatewise_single_jennings (p := p) i).1 ha).1
  have hi_cases : (a i).val = 0 ∨ (a i).val = 1 := by
    omega
  rcases hi_cases with hi_zero | hi_one
  · left
    exact
      jennings_exponent_coord
        (p := p) ha (Fin.ext hi_zero)
  · right
    have hp1 : 1 < p := (Fact.out : Nat.Prime p).one_lt
    have hone_mod : 1 % p = 1 := Nat.mod_eq_of_lt hp1
    have hone_val : ((1 : Fin p).val) = 1 := by
      simp [hone_mod]
    exact
      single_jennings_coord
        (p := p) ha (Fin.ext (by simpa [hone_mod] using hi_one))

/-- The finite lower set under a single-variable exponent consists only of zero and that
single-variable exponent. -/
lemma finset_single_exponent
    {p r : ℕ}
    [Fact p.Prime]
    {a : Fin r → Fin p}
    (i : Fin r) :
    a ∈ exponentCoordinatewiseFinset (singleJenningsExponent (p := p) i) ↔
      a = (fun _ : Fin r => (0 : Fin p)) ∨
        a = singleJenningsExponent (p := p) i := by
  constructor
  · intro ha
    exact
      or_single_exponent
        (p := p)
        ((exponent_lower_finset
          (e := singleJenningsExponent (p := p) i) (a := a)).1 ha)
  · rintro (rfl | rfl)
    · letI : NeZero p := ⟨(Fact.out : Nat.Prime p).ne_zero⟩
      exact
        coordinatewise_lower_finset
          (singleJenningsExponent (p := p) i)
    · exact
        self_coordinatewise_finset
          (singleJenningsExponent (p := p) i)

/-- A nonzero exponent below a single-variable exponent must be the single exponent itself. -/
lemma single_jennings_ne
    {p r : ℕ}
    [Fact p.Prime]
    {a : Fin r → Fin p}
    {i : Fin r}
    (ha : exponentCoordinatewiseLE a (singleJenningsExponent (p := p) i))
    (hne : a ≠ fun _ : Fin r => (0 : Fin p)) :
    a = singleJenningsExponent (p := p) i := by
  rcases
      or_single_exponent
        (p := p) ha with hzero | hsingle
  · exact False.elim (hne hzero)
  · exact hsingle

/-- A proper exponent below a single-variable exponent must be zero. -/
lemma jennings_exponent_ne
    {p r : ℕ}
    [Fact p.Prime]
    {a : Fin r → Fin p}
    {i : Fin r}
    (ha : exponentCoordinatewiseLE a (singleJenningsExponent (p := p) i))
    (hne : a ≠ singleJenningsExponent (p := p) i) :
    a = fun _ : Fin r => (0 : Fin p) := by
  rcases
      or_single_exponent
        (p := p) ha with hzero | hsingle
  · exact hzero
  · exact False.elim (hne hsingle)

end TJennin
end Towers
