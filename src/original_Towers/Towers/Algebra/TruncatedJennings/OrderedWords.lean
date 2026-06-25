import Towers.Algebra.TruncatedJennings.MonomialBasis
import Towers.Group.ZassenhausExplicit


open Filter
open scoped Pointwise EuclideanGeometry Topology

noncomputable section

universe u v

open NumberField

namespace Towers
namespace TJennin

/-- Ordered products of elements of a subgroup remain in the subgroup. -/
lemma fin_prod_subgroup
    {Q : Type u} [Group Q]
    (H : Subgroup Q)
    {r : ℕ}
    {f : Fin r → Q}
    (hf : ∀ i, f i ∈ H) :
    finOrderedProd r f ∈ H := by
  induction r with
  | zero =>
      simp [finOrderedProd]
  | succ r ih =>
      have hprefix :
          finOrderedProd r (fun i : Fin r => f i.castSucc) ∈ H := by
        exact ih (fun i => hf i.castSucc)
      have hlast : f (Fin.last r) ∈ H := hf (Fin.last r)
      simpa [finOrderedProd] using H.mul_mem hprefix hlast

/-- Ordered words whose letters all lie in a subgroup also lie in that subgroup. -/
lemma ordered_word_subgroup
    {Q : Type u} [Group Q]
    (H : Subgroup Q)
    {r : ℕ}
    {x : Fin r → Q}
    {e : Fin r → ℕ}
    (hx : ∀ i, x i ∈ H) :
    orderedWord x e ∈ H := by
  unfold orderedWord
  exact
    fin_prod_subgroup H
      (fun i => H.pow_mem (hx i) (e i))

/-- Ordered words with exponents in `Fin p` preserve subgroup membership. -/
lemma ordered_fin_subgroup
    {p r : ℕ}
    {Q : Type u} [Group Q]
    (H : Subgroup Q)
    {x : Fin r → Q}
    {e : Fin r → Fin p}
    (hx : ∀ i, x i ∈ H) :
    orderedWordFin x e ∈ H := by
  exact ordered_word_subgroup H hx

/-- Ordered products respect pointwise equality of their factors. -/
lemma fin_prod_congr
    {M : Type*} [Monoid M]
    {r : ℕ}
    {f g : Fin r → M}
    (hfg : ∀ i, f i = g i) :
    finOrderedProd r f = finOrderedProd r g := by
  induction r with
  | zero =>
      simp [finOrderedProd]
  | succ r ih =>
      have hprefix :
          finOrderedProd r (fun i : Fin r => f i.castSucc) =
            finOrderedProd r (fun i : Fin r => g i.castSucc) := by
        exact ih (fun i => hfg i.castSucc)
      have hlast : f (Fin.last r) = g (Fin.last r) := hfg (Fin.last r)
      simp [finOrderedProd, hprefix, hlast]

/-- Ordered products of constant `1` factors are `1`. -/
lemma fin_prod_one
    {M : Type*} [Monoid M]
    (r : ℕ) :
    finOrderedProd r (fun _ : Fin r => (1 : M)) = 1 := by
  induction r with
  | zero =>
      simp [finOrderedProd]
  | succ r ih =>
      simp [finOrderedProd, ih]

/-- An ordered product with only one possibly nontrivial factor is that factor. -/
lemma fin_single_off
    {M : Type*} [Monoid M]
    {r : ℕ}
    (f : Fin r → M)
    (i : Fin r)
    (hoff : ∀ j : Fin r, j ≠ i → f j = 1) :
    finOrderedProd r f = f i := by
  induction r with
  | zero =>
      exact Fin.elim0 i
  | succ r ih =>
      by_cases hi_last : i = Fin.last r
      · subst i
        have hprefix :
            finOrderedProd r (fun j : Fin r => f j.castSucc) = 1 := by
          calc
            finOrderedProd r (fun j : Fin r => f j.castSucc) =
                finOrderedProd r (fun _ : Fin r => (1 : M)) := by
                  apply fin_prod_congr
                  intro j
                  exact hoff j.castSucc (by
                    intro h
                    have hval := congrArg Fin.val h
                    have hjlt : j.val < r := j.isLt
                    simp at hval
                    omega)
            _ = 1 := fin_prod_one r
        simp [finOrderedProd, hprefix]
      · have hi_val_ne : i.val ≠ r := by
          intro hval
          apply hi_last
          ext
          simp [hval]
        have hi_val_lt : i.val < r := by
          omega
        let i' : Fin r := ⟨i.val, hi_val_lt⟩
        have hcast : i'.castSucc = i := by
          ext
          rfl
        have hprefix :
            finOrderedProd r (fun j : Fin r => f j.castSucc) =
              f i'.castSucc := by
          exact ih
            (fun j : Fin r => f j.castSucc)
            i'
            (fun j hj => hoff j.castSucc (by
              intro h
              apply hj
              have hji_cast : j.castSucc = i'.castSucc := h.trans hcast.symm
              exact Fin.ext (by
                have hval := congrArg Fin.val hji_cast
                simpa using hval)))
        have hlast : f (Fin.last r) = 1 :=
          hoff (Fin.last r) (fun h => hi_last h.symm)
        calc
          finOrderedProd (r + 1) f =
              finOrderedProd r (fun j : Fin r => f j.castSucc) * f (Fin.last r) := by
                simp [finOrderedProd]
          _ = f i'.castSucc * 1 := by rw [hprefix, hlast]
          _ = f i := by simp [hcast]

/-- Monoid homomorphisms commute with ordered products. -/
lemma fin_prod
    {M N : Type*} [Monoid M] [Monoid N]
    (φ : M →* N)
    {r : ℕ}
    (f : Fin r → M) :
    φ (finOrderedProd r f) =
      finOrderedProd r (fun i => φ (f i)) := by
  induction r with
  | zero =>
      simp [finOrderedProd]
  | succ r ih =>
      simp [finOrderedProd, map_mul, ih]

/-- Canonical group-algebra basis elements commute with ordered products. -/
lemma algebra_fin_prod
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q]
    {r : ℕ}
    (f : Fin r → Q) :
    denseGeneratorsElement p Q (finOrderedProd r f) =
      finOrderedProd r
        (fun i =>
          denseGeneratorsElement p Q (f i)) := by
  induction r with
  | zero =>
      simp [finOrderedProd]
  | succ r ih =>
      simp [finOrderedProd, ih]

/-- Canonical group-algebra basis elements of ordered words are ordered products of the
corresponding canonical letters. -/
lemma group_algebra_canonical
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q]
    {r : ℕ}
    (x : Fin r → Q)
    (e : Fin r → ℕ) :
    denseGeneratorsElement p Q (orderedWord x e) =
      finOrderedProd r
        (fun i =>
          denseGeneratorsElement p Q (x i) ^ e i) := by
  unfold orderedWord
  rw [algebra_fin_prod]
  apply fin_prod_congr
  intro i
  simp

/-- The same formula for exponent vectors with entries in `Fin p`. -/
lemma group_algebra_fin
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q]
    {r : ℕ}
    (x : Fin r → Q)
    (e : Fin r → Fin p) :
    denseGeneratorsElement p Q (orderedWordFin x e) =
      finOrderedProd r
        (fun i =>
          denseGeneratorsElement p Q (x i) ^ (e i).val) := by
  exact group_algebra_canonical (p := p) (Q := Q) x (fun i => (e i).val)

/-- A one-coordinate ordered word maps to the corresponding power of the canonical generator
in the group algebra. -/
lemma algebra_jennings_exponent
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q]
    {r : ℕ}
    (x : Fin r → Q)
    (i : Fin r)
    (k : Fin p) :
    denseGeneratorsElement p Q
        (orderedWordFin x (coordinateJenningsExponent (p := p) i k)) =
      denseGeneratorsElement p Q (x i) ^ k.val := by
  letI : NeZero p := ⟨(Fact.out : Nat.Prime p).ne_zero⟩
  rw [group_algebra_fin]
  calc
    finOrderedProd r
        (fun j : Fin r =>
          denseGeneratorsElement p Q (x j) ^
            (coordinateJenningsExponent (p := p) i k j).val) =
        denseGeneratorsElement p Q (x i) ^
          (coordinateJenningsExponent (p := p) i k i).val := by
          apply fin_single_off
          intro j hji
          simp [coordinate_jennings_ne (p := p) hji]
    _ = denseGeneratorsElement p Q (x i) ^ k.val := by
          simp [coordinate_jennings_self]

/-- The canonical element of the zero one-coordinate ordered word is the algebra unit. -/
lemma fin_jennings_exponent
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q]
    {r : ℕ}
    (x : Fin r → Q)
    (i : Fin r) :
    denseGeneratorsElement p Q
        (orderedWordFin x (coordinateJenningsExponent (p := p) i 0)) =
      (1 : denseGroupAlgebra p Q) := by
  rw [algebra_jennings_exponent]
  simp

/-- The ordered word attached to a single-variable exponent is the corresponding generator. -/
lemma fin_single_exponent
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q]
    {r : ℕ}
    (x : Fin r → Q)
    (i : Fin r) :
    orderedWordFin x (singleJenningsExponent (p := p) i) = x i := by
  letI : NeZero p := ⟨(Fact.out : Nat.Prime p).ne_zero⟩
  have hp1 : 1 < p := (Fact.out : Nat.Prime p).one_lt
  have hone_mod : 1 % p = 1 := Nat.mod_eq_of_lt hp1
  unfold orderedWordFin orderedWord
  calc
    finOrderedProd r
        (fun j : Fin r => x j ^ (singleJenningsExponent (p := p) i j).val) =
        x i ^ (singleJenningsExponent (p := p) i i).val := by
          apply fin_single_off
          intro j hji
          simp [single_ne (p := p) hji]
    _ = x i := by
          simp [single_jennings_self (p := p) i, hone_mod]

/-- The ordered word attached to a one-coordinate exponent is the corresponding power of that
single generator.

This is the group-word half of the one-factor expansion in Step 7. -/
lemma ordered_fin_exponent
    {p : ℕ} [NeZero p]
    {Q : Type u} [Group Q]
    {r : ℕ}
    (x : Fin r → Q)
    (i : Fin r)
    (k : Fin p) :
    orderedWordFin x (coordinateJenningsExponent (p := p) i k) = x i ^ k.val := by
  unfold orderedWordFin orderedWord
  calc
    finOrderedProd r
        (fun j : Fin r => x j ^ (coordinateJenningsExponent (p := p) i k j).val) =
        x i ^ (coordinateJenningsExponent (p := p) i k i).val := by
          apply fin_single_off
          intro j hji
          simp [coordinate_jennings_ne (p := p) hji]
    _ = x i ^ k.val := by
          simp [coordinate_jennings_self]

/-- The zero one-coordinate ordered word is the identity. -/
lemma ordered_jennings_exponent
    {p : ℕ} [NeZero p]
    {Q : Type u} [Group Q]
    {r : ℕ}
    (x : Fin r → Q)
    (i : Fin r) :
    orderedWordFin x (coordinateJenningsExponent (p := p) i 0) = 1 := by
  rw [ordered_fin_exponent]
  simp

/-- The one-coordinate ordered word with exponent `1` is the chosen generator. -/
lemma ordered_fin_jennings
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q]
    {r : ℕ}
    (x : Fin r → Q)
    (i : Fin r) :
    orderedWordFin x (coordinateJenningsExponent (p := p) i 1) = x i := by
  letI : NeZero p := ⟨(Fact.out : Nat.Prime p).ne_zero⟩
  rw [coordinate_jennings_one]
  exact fin_single_exponent (p := p) x i

/-- The augmentation letter for a generator may be written using the corresponding
single-variable ordered word. -/
lemma single_jennings_exponent
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q]
    {r : ℕ}
    (x : Fin r → Q)
    (i : Fin r) :
    groupAlgebraSub p Q (orderedWordFin x (singleJenningsExponent (p := p) i)) =
      groupAlgebraSub p Q (x i) := by
  rw [fin_single_exponent (p := p) (Q := Q) x i]

/-- The augmentation element attached to a one-coordinate ordered word is the one attached to
the corresponding generator power. -/
lemma sub_jennings_exponent
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q]
    {r : ℕ}
    (x : Fin r → Q)
    (i : Fin r)
    (k : Fin p) :
    groupAlgebraSub p Q (orderedWordFin x (coordinateJenningsExponent (p := p) i k)) =
      groupAlgebraSub p Q (x i ^ k.val) := by
  letI : NeZero p := ⟨(Fact.out : Nat.Prime p).ne_zero⟩
  rw [ordered_fin_exponent]

/-- A canonical group-algebra letter is `1 + ([x]-1)`. -/
lemma algebra_canonical_sub
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q]
    (x : Q) :
    denseGeneratorsElement p Q x =
      1 + groupAlgebraSub p Q x := by
  simp [groupAlgebraSub]

/-- TeX Step 7 identity:
`[x_1^{a_1} ... x_t^{a_t}] = ∏ᵢ (1 + ([x_i]-1))^{a_i}`. -/
lemma algebra_fin_sub
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q]
    {r : ℕ}
    (x : Fin r → Q)
    (e : Fin r → Fin p) :
    denseGeneratorsElement p Q (orderedWordFin x e) =
      finOrderedProd r
        (fun i =>
          (1 + groupAlgebraSub p Q (x i)) ^ (e i).val) := by
  rw [group_algebra_fin]
  apply fin_prod_congr
  intro i
  rw [algebra_canonical_sub]

/-- The ordered Jennings monomial is an ordered product of the augmentation letters with the
same exponents. This is mostly a named unfolding for Step 6. -/
lemma jennings_monomial_prod
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q]
    {r : ℕ}
    (x : Fin r → Q)
    (e : Fin r → Fin p) :
    jenningsMonomialFin p Q x e =
      finOrderedProd r
        (fun i =>
          groupAlgebraSub p Q (x i) ^ (e i).val) := by
  rfl

/-- A single-variable Jennings monomial is the corresponding augmentation letter. -/
lemma monomial_single_exponent
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q]
    {r : ℕ}
    (x : Fin r → Q)
    (i : Fin r) :
    jenningsMonomialFin p Q x (singleJenningsExponent (p := p) i) =
      groupAlgebraSub p Q (x i) := by
  letI : NeZero p := ⟨(Fact.out : Nat.Prime p).ne_zero⟩
  have hp1 : 1 < p := (Fact.out : Nat.Prime p).one_lt
  have hone_mod : 1 % p = 1 := Nat.mod_eq_of_lt hp1
  calc
    jenningsMonomialFin p Q x (singleJenningsExponent (p := p) i) =
        finOrderedProd r
          (fun j : Fin r =>
            groupAlgebraSub p Q (x j) ^
              (singleJenningsExponent (p := p) i j).val) := by
          rw [jennings_monomial_prod]
    _ =
        groupAlgebraSub p Q (x i) ^
          (singleJenningsExponent (p := p) i i).val := by
          apply fin_single_off
          intro j hji
          simp [single_ne (p := p) hji]
    _ = groupAlgebraSub p Q (x i) := by
          simp [single_jennings_self (p := p) i, hone_mod]

/-- The Jennings monomial attached to a one-coordinate exponent is the corresponding power of
one augmentation letter.

This is the monomial half of the one-factor expansion in Step 7. -/
lemma monomial_fin_exponent
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q]
    {r : ℕ}
    (x : Fin r → Q)
    (i : Fin r)
    (k : Fin p) :
    jenningsMonomialFin p Q x (coordinateJenningsExponent (p := p) i k) =
      groupAlgebraSub p Q (x i) ^ k.val := by
  letI : NeZero p := ⟨(Fact.out : Nat.Prime p).ne_zero⟩
  calc
    jenningsMonomialFin p Q x (coordinateJenningsExponent (p := p) i k) =
        finOrderedProd r
          (fun j : Fin r =>
            groupAlgebraSub p Q (x j) ^
              (coordinateJenningsExponent (p := p) i k j).val) := by
          rw [jennings_monomial_prod]
    _ =
        groupAlgebraSub p Q (x i) ^
          (coordinateJenningsExponent (p := p) i k i).val := by
          apply fin_single_off
          intro j hji
          simp [coordinate_jennings_ne (p := p) hji]
    _ = groupAlgebraSub p Q (x i) ^ k.val := by
          simp [coordinate_jennings_self]

/-- The Jennings monomial attached to a zero one-coordinate exponent is the algebra unit. -/
lemma ordered_jennings_monomial
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q]
    {r : ℕ}
    (x : Fin r → Q)
    (i : Fin r) :
    jenningsMonomialFin p Q x (coordinateJenningsExponent (p := p) i 0) =
      (1 : denseGroupAlgebra p Q) := by
  rw [monomial_fin_exponent]
  simp

/-- The one-coordinate Jennings monomial with exponent `1` is the chosen augmentation letter. -/
lemma jennings_monomial_exponent
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q]
    {r : ℕ}
    (x : Fin r → Q)
    (i : Fin r) :
    jenningsMonomialFin p Q x (coordinateJenningsExponent (p := p) i 1) =
      groupAlgebraSub p Q (x i) := by
  letI : NeZero p := ⟨(Fact.out : Nat.Prime p).ne_zero⟩
  rw [coordinate_jennings_one]
  exact monomial_single_exponent (p := p) x i

/-- The constant Jennings monomial is the algebra unit, so `1 ∈ W_0`. This supplies the
`one_mem` field for the abstract high-weight filtration used in Step 11. -/
lemma MBData.onemem_highweight_spanzero
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q] [Finite Q]
    {m : ℕ}
    {R : OZReps p Q m}
    (B : MBData.{u, v} (p := p) (Q := Q) R) :
    (1 : denseGroupAlgebra p Q) ∈ B.highWeightSpan 0 := by
  let e0 : Fin R.r → Fin p := fun _ => 0
  have hbasis_mem :
      B.basis (B.monomialIndex.symm e0) ∈ B.highWeightSpan 0 := by
    exact B.basis_high_span (Nat.zero_le _)
  have hbasis_eq :
      B.basis (B.monomialIndex.symm e0) =
        jenningsMonomialFin p Q R.gen e0 := by
    simpa using B.basis_apply (B.monomialIndex.symm e0)
  have hmonomial_one :
      jenningsMonomialFin p Q R.gen e0 = 1 := by
    unfold jenningsMonomialFin
    simpa [e0] using
      (fin_prod_one
        (M := denseGroupAlgebra p Q) R.r)
  simpa [hbasis_eq, hmonomial_one] using hbasis_mem

/-- A word supported on a single layer of an ordered generator list. -/
def exactWeightWord
    {p r : ℕ}
    {Q : Type u} [Group Q]
    (gen : Fin r → Q)
    (weight : Fin r → ℕ)
    (t : ℕ)
    (e : { i : Fin r // weight i = t } → Fin p) :
    Q :=
  finOrderedProd r
    (fun i =>
      if h : weight i = t then
        gen i ^ (e ⟨i, h⟩).val
      else
        1)

/-- Extend an exponent vector on the generators of exactly weight `t` to a global exponent
vector by putting zero on all other weights. -/
def exactWeightExponent
    {p r : ℕ}
    [NeZero p]
    (weight : Fin r → ℕ)
    (t : ℕ)
    (e : { i : Fin r // weight i = t } → Fin p) :
    Fin r → Fin p :=
  fun i =>
    if h : weight i = t then
      e ⟨i, h⟩
    else
      0

/-- On the chosen layer, the extended exact-weight exponent is the original exponent. -/
lemma exact_weight_exponent
    {p r : ℕ}
    [NeZero p]
    {weight : Fin r → ℕ}
    {t : ℕ}
    {e : { i : Fin r // weight i = t } → Fin p}
    {i : Fin r}
    (hi : weight i = t) :
    exactWeightExponent weight t e i = e ⟨i, hi⟩ := by
  simp [exactWeightExponent, hi]

/-- Off the chosen layer, the extended exact-weight exponent is zero. -/
lemma exact_exponent_ne
    {p r : ℕ}
    [NeZero p]
    {weight : Fin r → ℕ}
    {t : ℕ}
    {e : { i : Fin r // weight i = t } → Fin p}
    {i : Fin r}
    (hi : weight i ≠ t) :
    exactWeightExponent weight t e i = 0 := by
  simp [exactWeightExponent, hi]

/-- In particular, an exact-weight exponent has no coordinates below its chosen weight. -/
lemma exact_exponent_zero
    {p r : ℕ}
    [NeZero p]
    {weight : Fin r → ℕ}
    {t : ℕ}
    {e : { i : Fin r // weight i = t } → Fin p}
    {i : Fin r}
    (hi : weight i < t) :
    exactWeightExponent weight t e i = 0 := by
  exact exact_exponent_ne (ne_of_lt hi)

/-- The single-layer word is just the global ordered word for the exponent vector extended by
zero outside that layer. -/
lemma exact_fin_exponent
    {p r : ℕ}
    [NeZero p]
    {Q : Type u} [Group Q]
    (gen : Fin r → Q)
    (weight : Fin r → ℕ)
    (t : ℕ)
    (e : { i : Fin r // weight i = t } → Fin p) :
    exactWeightWord (p := p) gen weight t e =
      orderedWordFin gen (exactWeightExponent weight t e) := by
  unfold exactWeightWord orderedWordFin orderedWord exactWeightExponent
  congr
  funext i
  by_cases hi : weight i = t
  · simp [hi]
  · simp [hi]

/-- The exact-layer word lies in the layer when every selected generator does. -/
lemma exact_weight_subgroup
    {p r : ℕ}
    {Q : Type u} [Group Q]
    (H : Subgroup Q)
    {gen : Fin r → Q}
    {weight : Fin r → ℕ}
    {t : ℕ}
    {e : { i : Fin r // weight i = t } → Fin p}
    (hgen : ∀ i, weight i = t → gen i ∈ H) :
    exactWeightWord (p := p) gen weight t e ∈ H := by
  unfold exactWeightWord
  refine fin_prod_subgroup H ?_
  intro i
  by_cases hi : weight i = t
  · simpa [hi] using H.pow_mem (hgen i hi) (e ⟨i, hi⟩).val
  · simp [hi]

/-- The exact-layer word built from Zassenhaus generators lies in the corresponding
Zassenhaus term. -/
lemma exact_weight_zassenhaus
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q]
    {r t : ℕ}
    {gen : Fin r → Q}
    {weight : Fin r → ℕ}
    {e : { i : Fin r // weight i = t } → Fin p}
    (hgen : ∀ i, gen i ∈ zassenhausFiltration p Q (weight i)) :
    exactWeightWord (p := p) gen weight t e ∈
      zassenhausFiltration p Q t := by
  refine exact_weight_subgroup
    (zassenhausFiltration p Q t) ?_
  intro i hi
  simpa [hi] using hgen i

/-- If an ordered exponent vector has no coordinates below weight `t`, then its ordered word lies
in `D_t`. This is the formal easy direction behind Step 5 of `S.tex`. -/
lemma ordered_fin_below
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q]
    {r t : ℕ}
    {gen : Fin r → Q}
    {weight : Fin r → ℕ}
    {e : Fin r → Fin p}
    (hgen : ∀ i, gen i ∈ zassenhausFiltration p Q (weight i))
    (hzero : ∀ i, weight i < t → e i = 0) :
    orderedWordFin gen e ∈ zassenhausFiltration p Q t := by
  unfold orderedWordFin orderedWord
  refine fin_prod_subgroup (zassenhausFiltration p Q t) ?_
  intro i
  by_cases hi : weight i < t
  · simp [hzero i hi]
  · have hle : t ≤ weight i := le_of_not_gt hi
    have hgen_t : gen i ∈ zassenhausFiltration p Q t :=
      (zassenhausFiltration_antitone p Q hle) (hgen i)
    exact (zassenhausFiltration p Q t).pow_mem hgen_t (e i).val

/-- Exact-layer words have no lower-weight support, hence lie in their layer by the global
ordered-word criterion. -/
lemma exact_weight_ordered
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q]
    {r t : ℕ}
    {gen : Fin r → Q}
    {weight : Fin r → ℕ}
    {e : { i : Fin r // weight i = t } → Fin p}
    (hgen : ∀ i, gen i ∈ zassenhausFiltration p Q (weight i)) :
    exactWeightWord (p := p) gen weight t e ∈
      zassenhausFiltration p Q t := by
  letI : NeZero p := ⟨(Fact.out : Nat.Prime p).ne_zero⟩
  rw [exact_fin_exponent]
  exact
    ordered_fin_below
      (p := p) (Q := Q) (gen := gen) (weight := weight)
      hgen
      (fun i hi => exact_exponent_zero hi)

/-- For already-packaged ordered Zassenhaus representatives, zero lower coordinates imply
membership in the corresponding Zassenhaus layer. -/
lemma OZReps.orderedword_finmem_zerobelow
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q]
    {m t : ℕ}
    (R : OZReps p Q m)
    {e : Fin R.r → Fin p}
    (hzero : ∀ i, R.weight i < t → e i = 0) :
    orderedWordFin R.gen e ∈ zassenhausFiltration p Q t := by
  exact
    ordered_fin_below
      (p := p) (Q := Q) (gen := R.gen) (weight := R.weight)
      R.gen_mem hzero

/-- The same zero-lower-coordinate criterion, rewritten through the normal-form equivalence. -/
lemma OZReps.word_equivmem_zerobelow
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q]
    {m t : ℕ}
    (R : OZReps p Q m)
    {e : Fin R.r → Fin p}
    (hzero : ∀ i, R.weight i < t → e i = 0) :
    R.wordEquiv e ∈ zassenhausFiltration p Q t := by
  rw [R.wordEquiv_apply e]
  exact OZReps.orderedword_finmem_zerobelow R hzero

/-- A top-layer exact Zassenhaus generator supplies the first cyclic-extension certificate.

If `D_(n+1)` has been killed, the existing exact-generator power estimate gives `x ^ p = 1`.
The characteristic-`p` base constructor then adjoins `[x] - 1` to the scalar filtration with
weight `n`. -/
def base_exact_bot
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q]
    {n : ℕ}
    (hn : 0 < n)
    {x : Q}
    (hx : x ∈ exactGeneratorSet p Q n)
    (hbot : zassenhausFiltration p Q (n + 1) = ⊥) :
    CEDataa p Q (base_weightFiltration p Q) := by
  apply base_cyclic_extension x n
  exact
    one_filtration_bot p Q hbot
      (exact_filtration_succ hn hx)

/-- Step 3 data before the global normal-form count: chosen ordered generators in the surviving
layers, together with the layer-by-layer spanning property in `D_t/D_(t+1)`. -/
structure OLGenera
    (p : ℕ) [Fact p.Prime]
    (Q : Type u) [Group Q]
    (m : ℕ) where
  r : ℕ
  gen : Fin r → Q
  weight : Fin r → ℕ
  weight_pos : ∀ i, 0 < weight i
  weight_lt : ∀ i, weight i < m
  gen_mem : ∀ i, gen i ∈ zassenhausFiltration p Q (weight i)
  layer_surjective :
    ∀ {t : ℕ}, 0 < t → t < m → ∀ {g : Q},
      g ∈ zassenhausFiltration p Q t →
        ∃ e : { i : Fin r // weight i = t } → Fin p,
          g * (exactWeightWord (p := p) gen weight t e)⁻¹ ∈
            zassenhausFiltration p Q (t + 1)

namespace OLGenera

/-- The exact-layer correction word attached to an ordered layer-generator system lies in the
same Zassenhaus layer. -/
lemma exact_weight_word
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q]
    {m t : ℕ}
    (L : OLGenera p Q m)
    (e : { i : Fin L.r // L.weight i = t } → Fin p) :
    exactWeightWord (p := p) L.gen L.weight t e ∈
      zassenhausFiltration p Q t := by
  exact exact_weight_zassenhaus (p := p) (Q := Q) L.gen_mem

/-- A layer-surjectivity correction for `g ∈ D_t`, packaged with the fact that the correction
word itself lies in `D_t`. -/
lemma exists_layer_correction
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q]
    {m t : ℕ}
    (L : OLGenera p Q m)
    (ht_pos : 0 < t)
    (ht_lt : t < m)
    {g : Q}
    (hg : g ∈ zassenhausFiltration p Q t) :
    ∃ e : { i : Fin L.r // L.weight i = t } → Fin p,
      exactWeightWord (p := p) L.gen L.weight t e ∈
        zassenhausFiltration p Q t ∧
      g * (exactWeightWord (p := p) L.gen L.weight t e)⁻¹ ∈
        zassenhausFiltration p Q (t + 1) := by
  obtain ⟨e, he⟩ := L.layer_surjective ht_pos ht_lt hg
  exact ⟨e, L.exact_weight_word e, he⟩

end OLGenera

/-- An exact-layer word whose only nonzero coordinate is `1` at `i₀` is the selected
generator. -/
lemma exact_weight_single
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q]
    {r t : ℕ}
    {gen : Fin r → Q}
    {weight : Fin r → ℕ}
    (i₀ : Fin r)
    (hi₀ : weight i₀ = t) :
    exactWeightWord (p := p) gen weight t
        (fun i : { i : Fin r // weight i = t } =>
          if i.1 = i₀ then (1 : Fin p) else 0) =
      gen i₀ := by
  letI : NeZero p := ⟨(Fact.out : Nat.Prime p).ne_zero⟩
  have hp1 : 1 < p := (Fact.out : Nat.Prime p).one_lt
  have hone_mod : 1 % p = 1 := Nat.mod_eq_of_lt hp1
  unfold exactWeightWord
  calc
    finOrderedProd r
        (fun i =>
          if h : weight i = t then
            gen i ^
              ((fun i : { i : Fin r // weight i = t } =>
                if i.1 = i₀ then (1 : Fin p) else 0) ⟨i, h⟩).val
          else
            1) =
        (if h : weight i₀ = t then
          gen i₀ ^
            ((fun i : { i : Fin r // weight i = t } =>
              if i.1 = i₀ then (1 : Fin p) else 0) ⟨i₀, h⟩).val
        else
          1) := by
          apply fin_single_off
          intro j hj
          by_cases hjt : weight j = t
          · have hji :
                ((⟨j, hjt⟩ : { i : Fin r // weight i = t }).1 : Fin r) ≠ i₀ := hj
            simp [hjt, hji]
          · simp [hjt]
    _ = gen i₀ := by
          simp [hi₀, hone_mod]

/-- Step 3 of `S.tex`: choose ordered representatives whose images span each elementary
Zassenhaus layer. -/
theorem generators_d_bot
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q] [Finite Q]
    {n : ℕ}
    (hn : 1 < n)
    (hbot : zassenhausFiltration p Q (n + 1) = ⊥) :
    Nonempty (OLGenera p Q (n + 1)) := by
  classical
  have hn_pos : 0 < n := by
    omega
  have hm_pos : 0 < n + 1 := Nat.succ_pos n
  have hsucc_mem_iff :
      ∀ {g : Q}, g ∈ zassenhausFiltration p Q (n + 1) ↔ g = 1 := by
    intro g
    exact killed_succ_one (p := p) (Q := Q) (n := n) hbot
  -- It is enough for this package to choose every element in every surviving finite layer:
  -- the layer-surjectivity correction for `g ∈ D_t` then uses the coordinate for `g` itself.
  letI : NeZero p := ⟨(Fact.out : Nat.Prime p).ne_zero⟩
  let LayerIndex : Type u :=
    Sigma fun t : { t : Fin (n + 1) // 0 < (t : ℕ) } =>
      { g : Q // g ∈ zassenhausFiltration p Q (t.1 : ℕ) }
  haveI : Finite LayerIndex := by
    dsimp [LayerIndex]
    infer_instance
  letI : Fintype LayerIndex := Fintype.ofFinite LayerIndex
  let toFin : LayerIndex ≃ Fin (Fintype.card LayerIndex) :=
    Fintype.equivFin LayerIndex
  let fromFin : Fin (Fintype.card LayerIndex) → LayerIndex :=
    toFin.symm
  refine
    ⟨{
      r := Fintype.card LayerIndex
      gen := fun i => (fromFin i).2.1
      weight := fun i => ((fromFin i).1.1 : ℕ)
      weight_pos := ?_
      weight_lt := ?_
      gen_mem := ?_
      layer_surjective := ?_
    }⟩
  · intro i
    exact (fromFin i).1.2
  · intro i
    exact (fromFin i).1.1.2
  · intro i
    exact (fromFin i).2.2
  · intro t ht_pos ht_lt g hg
    let idx : LayerIndex :=
      ⟨⟨⟨t, ht_lt⟩, ht_pos⟩, ⟨g, hg⟩⟩
    let i₀ : Fin (Fintype.card LayerIndex) := toFin idx
    have hi₀_weight : ((fromFin i₀).1.1 : ℕ) = t := by
      change ((fromFin (toFin idx)).1.1 : ℕ) = t
      simp [fromFin, idx]
    let e : { i : Fin (Fintype.card LayerIndex) // ((fromFin i).1.1 : ℕ) = t } → Fin p :=
      fun i => if i.1 = i₀ then (1 : Fin p) else 0
    refine ⟨e, ?_⟩
    have hgen_i₀ : (fromFin i₀).2.1 = g := by
      have hfrom_idx : fromFin i₀ = idx := by
        dsimp [fromFin, i₀]
        exact toFin.symm_apply_apply idx
      simpa [idx] using congrArg (fun x : LayerIndex => (x.2 : Q)) hfrom_idx
    have hword :
        exactWeightWord (p := p)
            (fun i : Fin (Fintype.card LayerIndex) => (fromFin i).2.1)
            (fun i : Fin (Fintype.card LayerIndex) => ((fromFin i).1.1 : ℕ))
            t e =
          g := by
      calc
        exactWeightWord (p := p)
            (fun i : Fin (Fintype.card LayerIndex) => (fromFin i).2.1)
            (fun i : Fin (Fintype.card LayerIndex) => ((fromFin i).1.1 : ℕ))
            t e =
            (fromFin i₀).2.1 := by
              simpa [e] using
                exact_weight_single
                  (p := p) (Q := Q)
                  (gen := fun i : Fin (Fintype.card LayerIndex) => (fromFin i).2.1)
                  (weight := fun i : Fin (Fintype.card LayerIndex) => ((fromFin i).1.1 : ℕ))
                  (t := t) i₀ hi₀_weight
        _ = g := hgen_i₀
    simp [hword]
end TJennin
end Towers
