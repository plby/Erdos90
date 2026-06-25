import Submission.Algebra.TruncatedJennings.Exponents


open Filter
open scoped Pointwise EuclideanGeometry Topology

noncomputable section

universe u v

open NumberField

namespace Submission
namespace TJennin

namespace MBData

instance instFintype
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q] [Finite Q]
    {m : ℕ}
    {R : OZReps p Q m}
    (B : MBData.{u, v} (p := p) (Q := Q) R) :
    Fintype B.ι :=
  Fintype.ofEquiv (Fin R.r → Fin p) B.monomialIndex.symm

instance instDecidableEq
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q] [Finite Q]
    {m : ℕ}
    {R : OZReps p Q m}
    (B : MBData.{u, v} (p := p) (Q := Q) R) :
    DecidableEq B.ι :=
  B.decEq

/-- A basis vector belongs to the high-weight span as soon as its Jennings weight is above the
cutoff. -/
lemma basis_high_span
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q] [Finite Q]
    {m : ℕ}
    {R : OZReps p Q m}
    (B : MBData.{u, v} (p := p) (Q := Q) R)
    {s : ℕ}
    {e : B.ι}
    (he : s ≤ B.weight e) :
    B.basis e ∈
      basisHighSpan (p := p) (Q := Q) B.basis B.weight s := by
  exact basis_high_weight (B := B.basis) (wt := B.weight) he

/-- The basis vector indexed by an exponent vector has the high-weight membership predicted by
`expWeight`. -/
lemma basis_high_exp
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q] [Finite Q]
    {m : ℕ}
    {R : OZReps p Q m}
    (B : MBData.{u, v} (p := p) (Q := Q) R)
    {s : ℕ}
    {e : Fin R.r → Fin p}
    (he : s ≤ expWeight R.weight e) :
    B.basis (B.monomialIndex.symm e) ∈
      basisHighSpan (p := p) (Q := Q) B.basis B.weight s := by
  apply B.basis_high_span
  simpa [B.weight_apply] using he

/-- Ordered Jennings monomials inherit high-weight membership through the monomial basis. -/
lemma monomial_high_exp
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q] [Finite Q]
    {m : ℕ}
    {R : OZReps p Q m}
    (B : MBData.{u, v} (p := p) (Q := Q) R)
    {s : ℕ}
    {e : Fin R.r → Fin p}
    (he : s ≤ expWeight R.weight e) :
    jenningsMonomialFin p Q R.gen e ∈
      basisHighSpan (p := p) (Q := Q) B.basis B.weight s := by
  have hbasis :
      B.basis (B.monomialIndex.symm e) ∈
        basisHighSpan (p := p) (Q := Q) B.basis B.weight s :=
    B.basis_high_exp he
  have hbasis_eq :
      B.basis (B.monomialIndex.symm e) =
        jenningsMonomialFin p Q R.gen e := by
    simpa using B.basis_apply (B.monomialIndex.symm e)
  simpa [hbasis_eq] using hbasis

/-- Step 9 arithmetic-to-linear bridge: a nonconstant ordered Jennings monomial with no
variables below weight `s` belongs to the high-weight span `W_s`. -/
lemma monomial_nonzero_below
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q] [Finite Q]
    {m : ℕ}
    {R : OZReps p Q m}
    (B : MBData.{u, v} (p := p) (Q := Q) R)
    {s : ℕ}
    {e : Fin R.r → Fin p}
    (hzeroBelow : ∀ i, R.weight i < s → e i = 0)
    (hne : ∃ i, e i ≠ 0) :
    jenningsMonomialFin p Q R.gen e ∈
      basisHighSpan (p := p) (Q := Q) B.basis B.weight s := by
  letI : NeZero p := ⟨(Fact.out : Nat.Prime p).ne_zero⟩
  exact
    B.monomial_high_exp
      (exp_ne_below hzeroBelow hne)

/-- If a Jennings monomial has weight below `s` while all lower-weight coordinates vanish, then
it is the constant monomial. -/
lemma forall_exp_reps
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q] [Finite Q]
    {m : ℕ}
    {R : OZReps p Q m}
    {s : ℕ}
    {e : Fin R.r → Fin p}
    (hzeroBelow : ∀ i, R.weight i < s → e i = 0)
    (hlt : expWeight R.weight e < s) :
    ∀ i, e i = 0 := by
  letI : NeZero p := ⟨(Fact.out : Nat.Prime p).ne_zero⟩
  exact forall_exp_below hzeroBelow hlt

/-- The high-weight span contains zero. -/
lemma zero_high_span
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q] [Finite Q]
    {m : ℕ}
    {R : OZReps p Q m}
    (B : MBData.{u, v} (p := p) (Q := Q) R)
    (s : ℕ) :
    (0 : denseGroupAlgebra p Q) ∈
      basisHighSpan (p := p) (Q := Q) B.basis B.weight s := by
  exact (basisHighSpan (p := p) (Q := Q) B.basis B.weight s).zero_mem

/-- The high-weight span is closed under addition. -/
lemma add_high_span
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q] [Finite Q]
    {m s : ℕ}
    {R : OZReps p Q m}
    (B : MBData.{u, v} (p := p) (Q := Q) R)
    {a b : denseGroupAlgebra p Q}
    (ha :
      a ∈ basisHighSpan (p := p) (Q := Q) B.basis B.weight s)
    (hb :
      b ∈ basisHighSpan (p := p) (Q := Q) B.basis B.weight s) :
    a + b ∈ basisHighSpan (p := p) (Q := Q) B.basis B.weight s := by
  exact (basisHighSpan (p := p) (Q := Q) B.basis B.weight s).add_mem ha hb

/-- The high-weight span is closed under negation. -/
lemma neg_high_span
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q] [Finite Q]
    {m s : ℕ}
    {R : OZReps p Q m}
    (B : MBData.{u, v} (p := p) (Q := Q) R)
    {a : denseGroupAlgebra p Q}
    (ha :
      a ∈ basisHighSpan (p := p) (Q := Q) B.basis B.weight s) :
    -a ∈ basisHighSpan (p := p) (Q := Q) B.basis B.weight s := by
  exact (basisHighSpan (p := p) (Q := Q) B.basis B.weight s).neg_mem ha

/-- The high-weight span is closed under subtraction. -/
lemma sub_weight_span
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q] [Finite Q]
    {m s : ℕ}
    {R : OZReps p Q m}
    (B : MBData.{u, v} (p := p) (Q := Q) R)
    {a b : denseGroupAlgebra p Q}
    (ha :
      a ∈ basisHighSpan (p := p) (Q := Q) B.basis B.weight s)
    (hb :
      b ∈ basisHighSpan (p := p) (Q := Q) B.basis B.weight s) :
    a - b ∈ basisHighSpan (p := p) (Q := Q) B.basis B.weight s := by
  exact (basisHighSpan (p := p) (Q := Q) B.basis B.weight s).sub_mem ha hb

/-- The high-weight span is closed under scalar multiplication. -/
lemma smul_high_span
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q] [Finite Q]
    {m s : ℕ}
    {R : OZReps p Q m}
    (B : MBData.{u, v} (p := p) (Q := Q) R)
    (c : ZMod p)
    {a : denseGroupAlgebra p Q}
    (ha :
      a ∈ basisHighSpan (p := p) (Q := Q) B.basis B.weight s) :
    c • a ∈ basisHighSpan (p := p) (Q := Q) B.basis B.weight s := by
  exact (basisHighSpan (p := p) (Q := Q) B.basis B.weight s).smul_mem c ha

/-- A finite sum of elements of the high-weight span remains in the high-weight span. -/
lemma finset_high_span
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q] [Finite Q]
    {m s : ℕ}
    {R : OZReps p Q m}
    (B : MBData.{u, v} (p := p) (Q := Q) R)
    {α : Type*}
    (T : Finset α)
    (f : α → denseGroupAlgebra p Q)
    (hf :
      ∀ a ∈ T,
        f a ∈ basisHighSpan (p := p) (Q := Q) B.basis B.weight s) :
    (∑ a ∈ T, f a) ∈
      basisHighSpan (p := p) (Q := Q) B.basis B.weight s := by
  exact
    (basisHighSpan (p := p) (Q := Q) B.basis B.weight s).sum_mem
      (fun a ha => hf a ha)

/-- A finite linear combination of high-weight Jennings monomials lies in the high-weight span.
This is the linear-combination form of Step 8. -/
lemma finset_monomial_exp
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q] [Finite Q]
    {m s : ℕ}
    {R : OZReps p Q m}
    (B : MBData.{u, v} (p := p) (Q := Q) R)
    {α : Type*}
    (T : Finset α)
    (c : α → ZMod p)
    (e : α → Fin R.r → Fin p)
    (he : ∀ a ∈ T, s ≤ expWeight R.weight (e a)) :
    (∑ a ∈ T, c a • jenningsMonomialFin p Q R.gen (e a)) ∈
      basisHighSpan (p := p) (Q := Q) B.basis B.weight s := by
  refine B.finset_high_span T
    (fun a => c a • jenningsMonomialFin p Q R.gen (e a)) ?_
  intro a ha
  exact
    B.smul_high_span (c a)
      (B.monomial_high_exp (he a ha))

/-- A finite linear combination of nonconstant monomials with no lower-weight variables lies in
the high-weight span. This is the form needed after expanding
`∏ᵢ (1 + u_i)^{a_i}` and discarding the constant term. -/
lemma finset_nonzero_below
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q] [Finite Q]
    {m s : ℕ}
    {R : OZReps p Q m}
    (B : MBData.{u, v} (p := p) (Q := Q) R)
    {α : Type*}
    (T : Finset α)
    (c : α → ZMod p)
    (e : α → Fin R.r → Fin p)
    (hzeroBelow : ∀ a ∈ T, ∀ i, R.weight i < s → e a i = 0)
    (hne : ∀ a ∈ T, ∃ i, e a i ≠ 0) :
    (∑ a ∈ T, c a • jenningsMonomialFin p Q R.gen (e a)) ∈
      basisHighSpan (p := p) (Q := Q) B.basis B.weight s := by
  refine B.finset_high_span T
    (fun a => c a • jenningsMonomialFin p Q R.gen (e a)) ?_
  intro a ha
  exact
    B.smul_high_span (c a)
      (B.monomial_nonzero_below
        (hzeroBelow a ha) (hne a ha))

/-- A compact name for the high-weight span attached to a monomial basis. -/
abbrev highWeightSpan
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q] [Finite Q]
    {m : ℕ}
    {R : OZReps p Q m}
    (B : MBData.{u, v} (p := p) (Q := Q) R)
    (s : ℕ) :
    Submodule (ZMod p) (denseGroupAlgebra p Q) :=
  basisHighSpan (p := p) (Q := Q) B.basis B.weight s

/-- The additive Jennings weight of a finite ordered product, defined with the same recursion as
`finOrderedProd`. This avoids fighting finite-sum reindexing while formalizing the induction
used in Step 10 of `S.tex`. -/
def finWeightSum : (r : ℕ) → (Fin r → ℕ) → ℕ
  | 0, _ => 0
  | r + 1, wt =>
      finWeightSum r (fun i : Fin r => wt i.castSucc) + wt (Fin.last r)

/-- The recursive product weight is monotone in each factor weight. -/
lemma fin_sum_mono
    {r : ℕ}
    {wt wt' : Fin r → ℕ}
    (hwt : ∀ i, wt i ≤ wt' i) :
    finWeightSum r wt ≤ finWeightSum r wt' := by
  induction r with
  | zero =>
      simp [finWeightSum]
  | succ r ih =>
      have hprefix :
          finWeightSum r (fun i : Fin r => wt i.castSucc) ≤
            finWeightSum r (fun i : Fin r => wt' i.castSucc) := by
        exact ih (fun i => hwt i.castSucc)
      have hlast : wt (Fin.last r) ≤ wt' (Fin.last r) := hwt (Fin.last r)
      simpa [finWeightSum] using Nat.add_le_add hprefix hlast

/-- A product of `r` factors all carrying weight `1` has recursive total weight `r`. -/
lemma fin_sum_const
    (r : ℕ) :
    finWeightSum r (fun _ : Fin r => 1) = r := by
  induction r with
  | zero =>
      simp [finWeightSum]
  | succ r ih =>
      simp [finWeightSum, ih]

/-- Step 10 data: the high-weight subspaces attached to the Jennings monomial basis multiply
with the expected weight, together with the Step 11 input that the augmentation ideal is
contained in `W_1`.

The hard part still to be formalized is constructing this package from the commutator and
`p`-power collection argument in `S.tex`. Once it is constructed, the lemmas below give the
inductive algebra consequences without further group-theoretic reasoning. -/
structure HMData
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q] [Finite Q]
    {m : ℕ}
    {R : OZReps p Q m}
    (B : MBData.{u, v} (p := p) (Q := Q) R) :
    Type (max (u + 1) (v + 1)) where
  one_high_zero :
    (1 : denseGroupAlgebra p Q) ∈ B.highWeightSpan 0
  mul_mem_high :
    ∀ {s t : ℕ} {x y : denseGroupAlgebra p Q},
      x ∈ B.highWeightSpan s →
      y ∈ B.highWeightSpan t →
        x * y ∈ B.highWeightSpan (s + t)
  aug_power_high :
    augmentationIdealPower p Q 1 ≤ B.highWeightSpan 1

namespace HMData

/-- A product in `W_a W_b` also lies in any lower cutoff `W_s` with `s ≤ a+b`. -/
lemma mul_high
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q] [Finite Q]
    {m : ℕ}
    {R : OZReps p Q m}
    {B : MBData.{u, v} (p := p) (Q := Q) R}
    (M : HMData (p := p) (Q := Q) B)
    {a b s : ℕ}
    {x y : denseGroupAlgebra p Q}
    (hs : s ≤ a + b)
    (hx : x ∈ B.highWeightSpan a)
    (hy : y ∈ B.highWeightSpan b) :
    x * y ∈ B.highWeightSpan s := by
  exact
    basis_high_antitone
      (p := p) (Q := Q) (B := B.basis) (wt := B.weight) hs
      (M.mul_mem_high hx hy)

/-- Ordered products of high-weight elements have high weight equal to the recursive sum of the
factor weights. This is the formal induction behind the repeated collection process in
Step 10. -/
lemma fin_prod_high
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q] [Finite Q]
    {m : ℕ}
    {R : OZReps p Q m}
    {B : MBData.{u, v} (p := p) (Q := Q) R}
    (M : HMData (p := p) (Q := Q) B)
    {r : ℕ}
    (f : Fin r → denseGroupAlgebra p Q)
    (wt : Fin r → ℕ)
    (hf : ∀ i, f i ∈ B.highWeightSpan (wt i)) :
    finOrderedProd r f ∈ B.highWeightSpan (finWeightSum r wt) := by
  induction r with
  | zero =>
      simpa [finOrderedProd, finWeightSum] using M.one_high_zero
  | succ r ih =>
      have hprefix :
          finOrderedProd r (fun i : Fin r => f i.castSucc) ∈
            B.highWeightSpan (finWeightSum r (fun i : Fin r => wt i.castSucc)) := by
        exact ih
          (fun i : Fin r => f i.castSucc)
          (fun i : Fin r => wt i.castSucc)
          (fun i => hf i.castSucc)
      have hlast :
          f (Fin.last r) ∈ B.highWeightSpan (wt (Fin.last r)) :=
        hf (Fin.last r)
      simpa [finOrderedProd, finWeightSum] using
        M.mul_mem_high hprefix hlast

/-- Ordered products of high-weight elements remain in every lower cutoff below their total
recursive weight. -/
lemma prod_high_span
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q] [Finite Q]
    {m : ℕ}
    {R : OZReps p Q m}
    {B : MBData.{u, v} (p := p) (Q := Q) R}
    (M : HMData (p := p) (Q := Q) B)
    {r s : ℕ}
    (f : Fin r → denseGroupAlgebra p Q)
    (wt : Fin r → ℕ)
    (hs : s ≤ finWeightSum r wt)
    (hf : ∀ i, f i ∈ B.highWeightSpan (wt i)) :
    finOrderedProd r f ∈ B.highWeightSpan s := by
  exact
    basis_high_antitone
      (p := p) (Q := Q) (B := B.basis) (wt := B.weight) hs
      (M.fin_prod_high f wt hf)

/-- If the factor cutoffs are only lower bounds for stronger memberships, the product still
lands in the span predicted by the lower bounds. -/
lemma fin_high_pointwise
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q] [Finite Q]
    {m : ℕ}
    {R : OZReps p Q m}
    {B : MBData.{u, v} (p := p) (Q := Q) R}
    (M : HMData (p := p) (Q := Q) B)
    {r s : ℕ}
    (f : Fin r → denseGroupAlgebra p Q)
    (actual lower : Fin r → ℕ)
    (hlower : ∀ i, lower i ≤ actual i)
    (hs : s ≤ finWeightSum r lower)
    (hf : ∀ i, f i ∈ B.highWeightSpan (actual i)) :
    finOrderedProd r f ∈ B.highWeightSpan s := by
  have hsum : finWeightSum r lower ≤ finWeightSum r actual :=
    fin_sum_mono hlower
  exact M.prod_high_span f actual (le_trans hs hsum) hf

/-- A product of `r` elements of `W_1` lies in `W_r`. This is the formal `W_1^r ⊆ W_r`
consequence of Step 10. -/
lemma fin_high_span
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q] [Finite Q]
    {m : ℕ}
    {R : OZReps p Q m}
    {B : MBData.{u, v} (p := p) (Q := Q) R}
    (M : HMData (p := p) (Q := Q) B)
    {r : ℕ}
    (f : Fin r → denseGroupAlgebra p Q)
    (hf : ∀ i, f i ∈ B.highWeightSpan 1) :
    finOrderedProd r f ∈ B.highWeightSpan r := by
  have hprod :
      finOrderedProd r f ∈
        B.highWeightSpan (finWeightSum r (fun _ : Fin r => 1)) :=
    M.fin_prod_high f (fun _ : Fin r => 1) hf
  simpa [fin_sum_const] using hprod

/-- A product of `r` elements of the augmentation ideal lies in `W_r`, once `I ≤ W_1` is known.
This isolates the forward inclusion `I^r ⊆ W_r` from Step 11 at the level of ordered products. -/
lemma high_span_aug
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q] [Finite Q]
    {m : ℕ}
    {R : OZReps p Q m}
    {B : MBData.{u, v} (p := p) (Q := Q) R}
    (M : HMData (p := p) (Q := Q) B)
    {r : ℕ}
    (f : Fin r → denseGroupAlgebra p Q)
    (hf : ∀ i, f i ∈ augmentationIdealPower p Q 1) :
    finOrderedProd r f ∈ B.highWeightSpan r := by
  refine M.fin_high_span f ?_
  intro i
  exact M.aug_power_high (hf i)

/-- The same augmentation-ideal product estimate, weakened to any lower cutoff `s ≤ r`. -/
lemma fin_high_aug
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q] [Finite Q]
    {m : ℕ}
    {R : OZReps p Q m}
    {B : MBData.{u, v} (p := p) (Q := Q) R}
    (M : HMData (p := p) (Q := Q) B)
    {r s : ℕ}
    (f : Fin r → denseGroupAlgebra p Q)
    (hs : s ≤ r)
    (hf : ∀ i, f i ∈ augmentationIdealPower p Q 1) :
    finOrderedProd r f ∈ B.highWeightSpan s := by
  exact
    basis_high_antitone
      (p := p) (Q := Q) (B := B.basis) (wt := B.weight) hs
      (M.high_span_aug f hf)

/-- The high-weight spans, together with Step 10 multiplicativity, form an abstract
`WFilt` in the sense of `S0.lean`. This lets us reuse the already-proven general
augmentation-power estimate there. -/
def toWFilt
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q] [Finite Q]
    {m : ℕ}
    {R : OZReps p Q m}
    {B : MBData.{u, v} (p := p) (Q := Q) R}
    (M : HMData (p := p) (Q := Q) B) :
    WFilt p Q where
  J := B.highWeightSpan
  anti := by
    intro s t hst
    exact basis_high_antitone
      (p := p) (Q := Q) (B := B.basis) (wt := B.weight) hst
  one_mem := M.one_high_zero
  mul_mem := by
    intro s t x y hx hy
    exact M.mul_mem_high hx hy

/-- Every basic group-algebra difference lies in `W_1` once `I ≤ W_1` is part of the
multiplicative data. This is the `W_1 = I` input from Step 11, used only in the easy direction
needed by the general S0 lemma. -/
lemma algebra_sub_high
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q] [Finite Q]
    {m : ℕ}
    {R : OZReps p Q m}
    {B : MBData.{u, v} (p := p) (Q := Q) R}
    (M : HMData (p := p) (Q := Q) B)
    (x : Q) :
    groupAlgebraSub p Q x ∈ B.highWeightSpan 1 := by
  exact
    M.aug_power_high
      (group_algebra_sub p Q x)

/-- Step 11 forward inclusion for positive powers: `I^(s+1) ≤ W_(s+1)`.

This is now a formal consequence of S0's general theorem for multiplicative weight filtrations,
after converting the high-weight spans to that interface. -/
lemma succ_high_span
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q] [Finite Q]
    {m : ℕ}
    {R : OZReps p Q m}
    {B : MBData.{u, v} (p := p) (Q := Q) R}
    (M : HMData (p := p) (Q := Q) B)
    (s : ℕ) :
    augmentationIdealPower p Q (s + 1) ≤ B.highWeightSpan (s + 1) := by
  exact
    augmentation_ideal_filtration
      (p := p) (G := Q)
      (W := M.toWFilt)
      (fun x => M.algebra_sub_high x)
      s

end HMData

/-- The recursive weight sum is the ordinary finite sum over `Fin r`. -/
lemma fin_weight_sum
    {r : ℕ}
    (wt : Fin r → ℕ) :
    finWeightSum r wt = ∑ i : Fin r, wt i := by
  induction r with
  | zero =>
      simp [finWeightSum]
  | succ r ih =>
      rw [finWeightSum, ih]
      exact (Fin.sum_univ_castSucc (fun i : Fin (r + 1) => wt i)).symm

/-- The zeroth augmentation power is the whole algebra, in submodule form. -/
lemma augmentation_ideal_zero
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q] :
    (1 : denseGroupAlgebra p Q) ∈ augmentationIdealPower p Q 0 := by
  let I : Ideal (denseGroupAlgebra p Q) :=
    denseGeneratorsIdeal p Q
  exact
    (Submodule.restrictScalars_mem (ZMod p) (I ^ 0)
      (1 : denseGroupAlgebra p Q)).mpr
      (by
        rw [Submodule.pow_zero, Ideal.one_eq_top]
        exact Submodule.mem_top)

/-- If an element lies in `I^s`, then its `k`th power lies in `I^(k*s)`. This is the algebraic
core of the reverse inclusion in Step 11 of `S.tex`. -/
lemma pow_augmentation_mul
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q]
    {s : ℕ}
    {x : denseGroupAlgebra p Q}
    (hx : x ∈ augmentationIdealPower p Q s)
    (k : ℕ) :
    x ^ k ∈ augmentationIdealPower p Q (k * s) := by
  induction k with
  | zero =>
      simpa using augmentation_ideal_zero (p := p) (Q := Q)
  | succ k ih =>
      have hmul :
          x ^ k * x ∈ augmentationIdealPower p Q (k * s + s) :=
        augmentation_ideal_mul (p := p) (G := Q) ih hx
      simpa [pow_succ, Nat.succ_mul] using hmul

/-- Ordered products of elements with prescribed augmentation depths lie in the augmentation
power indexed by the recursive sum of those depths. -/
lemma fin_ordered_prod
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q]
    {r : ℕ}
    (f : Fin r → denseGroupAlgebra p Q)
    (depth : Fin r → ℕ)
    (hf : ∀ i, f i ∈ augmentationIdealPower p Q (depth i)) :
    finOrderedProd r f ∈ augmentationIdealPower p Q (finWeightSum r depth) := by
  induction r with
  | zero =>
      simpa [finOrderedProd, finWeightSum] using
        augmentation_ideal_zero (p := p) (Q := Q)
  | succ r ih =>
      have hprefix :
          finOrderedProd r (fun i : Fin r => f i.castSucc) ∈
            augmentationIdealPower p Q
              (finWeightSum r (fun i : Fin r => depth i.castSucc)) := by
        exact ih
          (fun i : Fin r => f i.castSucc)
          (fun i : Fin r => depth i.castSucc)
          (fun i => hf i.castSucc)
      have hlast :
          f (Fin.last r) ∈ augmentationIdealPower p Q (depth (Fin.last r)) :=
        hf (Fin.last r)
      simpa [finOrderedProd, finWeightSum] using
        augmentation_ideal_mul (p := p) (G := Q) hprefix hlast

/-- A Jennings monomial belongs to the augmentation power indexed by its Jennings weight. This
is the formal version of `u_i ∈ I^{w_i}` implies `u^a ∈ I^{Σ a_i w_i}` in Step 11. -/
lemma jennings_monomial_exp
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q] [Finite Q]
    {m : ℕ}
    {R : OZReps p Q m}
    (hgen :
      ∀ i : Fin R.r,
        groupAlgebraSub p Q (R.gen i) ∈
          augmentationIdealPower p Q (R.weight i))
    (e : Fin R.r → Fin p) :
    jenningsMonomialFin p Q R.gen e ∈
      augmentationIdealPower p Q (expWeight R.weight e) := by
  have hfactor :
      ∀ i : Fin R.r,
        groupAlgebraSub p Q (R.gen i) ^ (e i).val ∈
          augmentationIdealPower p Q ((e i).val * R.weight i) := by
    intro i
    exact pow_augmentation_mul (p := p) (Q := Q) (hgen i) (e i).val
  have hprod :
      finOrderedProd R.r
          (fun i : Fin R.r => groupAlgebraSub p Q (R.gen i) ^ (e i).val) ∈
        augmentationIdealPower p Q
          (finWeightSum R.r (fun i : Fin R.r => (e i).val * R.weight i)) :=
    fin_ordered_prod
      (p := p) (Q := Q)
      (fun i : Fin R.r => groupAlgebraSub p Q (R.gen i) ^ (e i).val)
      (fun i : Fin R.r => (e i).val * R.weight i)
      hfactor
  simpa [jenningsMonomialFin, expWeight, fin_weight_sum] using hprod

/-- A Jennings basis vector whose basis weight is at least `s` lies in `I^s`. -/
lemma basis_augmentation_weight
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q] [Finite Q]
    {m : ℕ}
    {R : OZReps p Q m}
    (B : MBData.{u, v} (p := p) (Q := Q) R)
    {s : ℕ}
    {e : B.ι}
    (he : s ≤ B.weight e) :
    B.basis e ∈ augmentationIdealPower p Q s := by
  have hgen :
      ∀ i : Fin R.r,
        groupAlgebraSub p Q (R.gen i) ∈
          augmentationIdealPower p Q (R.weight i) := by
    intro i
    exact
      zassenhaus_implies_sub
        (p := p) (G := Q) (n := R.weight i) (g := R.gen i)
        (R.gen_mem i)
  have hweight :
      s ≤ expWeight R.weight (B.monomialIndex e) := by
    simpa [B.weight_apply] using he
  have hmonomial :
      jenningsMonomialFin p Q R.gen (B.monomialIndex e) ∈
        augmentationIdealPower p Q s :=
    augmentation_ideal_antitone
      (p := p) (G := Q) hweight
      (jennings_monomial_exp
        (p := p) (Q := Q) (R := R) hgen (B.monomialIndex e))
  have hbasis :
      B.basis e =
        jenningsMonomialFin p Q R.gen (B.monomialIndex e) :=
    B.basis_apply e
  simpa [hbasis] using hmonomial

/-- Step 11 reverse inclusion: the high-weight span `W_s` is contained in the augmentation power
`I^s`. The proof is span induction from the preceding monomial estimate. -/
lemma high_span_power
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q] [Finite Q]
    {m : ℕ}
    {R : OZReps p Q m}
    (B : MBData.{u, v} (p := p) (Q := Q) R)
    (s : ℕ) :
    B.highWeightSpan s ≤ augmentationIdealPower p Q s := by
  intro x hx
  change x ∈ basisHighSpan (p := p) (Q := Q) B.basis B.weight s at hx
  unfold basisHighSpan at hx
  refine Submodule.span_induction
    (s := B.basis '' { e : B.ι | s ≤ B.weight e })
    (p := fun y _ => y ∈ augmentationIdealPower p Q s)
    ?mem ?zero ?add ?smul hx
  · rintro y ⟨e, he, rfl⟩
    exact B.basis_augmentation_weight he
  · exact (augmentationIdealPower p Q s).zero_mem
  · intro y z _hy _hz hy_mem hz_mem
    exact (augmentationIdealPower p Q s).add_mem hy_mem hz_mem
  · intro c y _hy hy_mem
    exact (augmentationIdealPower p Q s).smul_mem c hy_mem

/-- Canonical Step 9: if `g ∈ D_s`, then `[g] - 1` lies in the canonical high-weight span
`W_s`. -/
lemma canonical_sub_high
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q] [Finite Q]
    {m s : ℕ}
    (R : OZReps p Q m)
    (hs : s ≤ m)
    {g : Q}
    (hg : g ∈ zassenhausFiltration p Q s) :
    groupAlgebraSub p Q g ∈
      (canonical (p := p) (Q := Q) R).highWeightSpan s := by
  change
    groupAlgebraSub p Q g ∈
      basisHighSpan (p := p) (Q := Q) R.jenningsMonomialBasis
        (fun a : Fin R.r → Fin p =>
          expWeight (p := p) (r := R.r) R.weight a) s
  exact
    R.subone_membasishigh_weightspanmem
      R.jenningsMonomialBasis hs
      (fun e => R.jennings_monomial_basis e)
      hg

/-- The canonical high-weight span contains the algebra unit in weight zero. -/
lemma canonical_high_zero
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q] [Finite Q]
    {m : ℕ}
    (R : OZReps p Q m) :
    (1 : denseGroupAlgebra p Q) ∈
      (canonical (p := p) (Q := Q) R).highWeightSpan 0 := by
  let e0 : Fin R.r → Fin p := fun _ => 0
  have hbasis_mem :
      (canonical (p := p) (Q := Q) R).basis e0 ∈
        (canonical (p := p) (Q := Q) R).highWeightSpan 0 := by
    exact
      (canonical (p := p) (Q := Q) R).basis_high_span
        (Nat.zero_le _)
  have hbasis_eq :
      (canonical (p := p) (Q := Q) R).basis e0 =
        jenningsMonomialFin p Q R.gen e0 :=
    (canonical (p := p) (Q := Q) R).basis_apply e0
  have hmonomial_one :
      jenningsMonomialFin p Q R.gen e0 =
        (1 : denseGroupAlgebra p Q) := by
    unfold jenningsMonomialFin
    simpa [e0] using
      (fin_ordered_forall
        (M := denseGroupAlgebra p Q) R.r
        (fun _ : Fin R.r => (1 : denseGroupAlgebra p Q))
        (fun _ => rfl))
  simpa [hbasis_eq, hmonomial_one] using hbasis_mem

/-- The first augmentation power is contained in the canonical high-weight span `W₁`. -/
lemma canonical_high_span
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q] [Finite Q]
    {m : ℕ}
    (R : OZReps p Q m)
    (hm : 1 ≤ m) :
    augmentationIdealPower p Q 1 ≤
      (canonical (p := p) (Q := Q) R).highWeightSpan 1 := by
  intro x hx
  have hxI :
      x ∈ denseGeneratorsIdeal p Q := by
    have hxpow :
        x ∈ denseGeneratorsIdeal p Q ^ 1 :=
      (Submodule.restrictScalars_mem (ZMod p)
        (denseGeneratorsIdeal p Q ^ 1) x).mp
        (by simpa [augmentationIdealPower] using hx)
    simpa [Submodule.pow_one] using hxpow
  have hxletter :
      x ∈ denseLetterSpan p Q :=
    (dense_letter_span
      (p := p) (Λ := Q)).1 hxI
  let S : Set (denseGroupAlgebra p Q) :=
    { y | ∃ g : Q, denseGeneratorsElement p Q g - 1 = y }
  let W : Submodule (ZMod p) (denseGroupAlgebra p Q) :=
    (canonical (p := p) (Q := Q) R).highWeightSpan 1
  have hxspan : x ∈ Submodule.span (ZMod p) S := by
    simpa [denseLetterSpan, S] using hxletter
  refine Submodule.span_induction
    (s := S)
    (p := fun y _ => y ∈ W)
    ?mem ?zero ?add ?smul hxspan
  · rintro y ⟨g, rfl⟩
    change groupAlgebraSub p Q g ∈ W
    exact
      canonical_sub_high
        (p := p) (Q := Q) (s := 1) R hm
        (g := g)
        (zassenhaus_filtration_one p Q (by norm_num) g)
  · exact W.zero_mem
  · intro y z _hy _hz hy_mem hz_mem
    exact W.add_mem hy_mem hz_mem
  · intro c y _hy hy_mem
    exact W.smul_mem c hy_mem

/-- Coordinate vanishing for all ordered augmentation words implies the canonical high-weight
product law. -/
lemma high_low_coordinates
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q] [Finite Q]
    {m : ℕ}
    (R : OZReps p Q m)
    (H :
      ∀ w : List (Fin R.r),
        R.LowWeightcoordsVanishword (R.wordWeight w) w)
    {s t : ℕ}
    {x y : denseGroupAlgebra p Q}
    (hx : x ∈ (canonical (p := p) (Q := Q) R).highWeightSpan s)
    (hy : y ∈ (canonical (p := p) (Q := Q) R).highWeightSpan t) :
    x * y ∈ (canonical (p := p) (Q := Q) R).highWeightSpan (s + t) := by
  classical
  let B : MBData.{u, 0} (p := p) (Q := Q) R :=
    canonical (p := p) (Q := Q) R
  let Xset : Set (denseGroupAlgebra p Q) :=
    B.basis '' {e : B.ι | s ≤ B.weight e}
  let Yset : Set (denseGroupAlgebra p Q) :=
    B.basis '' {e : B.ι | t ≤ B.weight e}
  let Zset : Set (denseGroupAlgebra p Q) :=
    B.basis '' {e : B.ι | s + t ≤ B.weight e}
  have h_basis_mul :
      ∀ {e f : B.ι}, s ≤ B.weight e → t ≤ B.weight f →
        B.basis e * B.basis f ∈ Submodule.span (ZMod p) Zset := by
    intro e f he hf
    let e' : Fin R.r → Fin p := B.monomialIndex e
    let f' : Fin R.r → Fin p := B.monomialIndex f
    let w : List (Fin R.r) := orderedExponentList R.r e' ++ orderedExponentList R.r f'
    have he_weight : s ≤ expWeight (p := p) (r := R.r) R.weight e' := by
      simpa [B.weight_apply, e'] using he
    have hf_weight : t ≤ expWeight (p := p) (r := R.r) R.weight f' := by
      simpa [B.weight_apply, f'] using hf
    have hword_weight : s + t ≤ R.wordWeight w := by
      calc
        s + t ≤
            expWeight (p := p) (r := R.r) R.weight e' +
              expWeight (p := p) (r := R.r) R.weight f' :=
          Nat.add_le_add he_weight hf_weight
        _ = R.wordWeight w := by
          simp [w, R.wordWeight_append, R.ordered_exponent_list]
    have hprod :
        B.basis e * B.basis f = R.wordEval w := by
      calc
        B.basis e * B.basis f =
              jenningsMonomialFin p Q R.gen e' *
                jenningsMonomialFin p Q R.gen f' := by
                rw [B.basis_apply e, B.basis_apply f]
        _ = R.wordEval (orderedExponentList R.r e') *
              R.wordEval (orderedExponentList R.r f') := by
                rw [R.word_exponent_list e',
                  R.word_exponent_list f']
        _ = R.wordEval w := by
                rw [← R.wordEval_append]
    rw [hprod]
    change R.wordEval w ∈ B.highWeightSpan (s + t)
    refine
      (basis_high_repr
        (p := p) (Q := Q) (B := B.basis) (wt := B.weight)
        (s := s + t) (a := R.wordEval w)).2 ?_
    intro a ha
    have ha_exp :
        expWeight (p := p) (r := R.r) R.weight (B.monomialIndex a) <
          R.wordWeight w := by
      exact lt_of_lt_of_le (by simpa [B.weight_apply] using ha) hword_weight
    have hzero :
        R.jenningsMonomialBasis.repr (R.wordEval w) (B.monomialIndex a) = 0 :=
      H w (B.monomialIndex a) ha_exp
    simpa [B, MBData.canonical] using hzero
  change x ∈ Submodule.span (ZMod p) Xset at hx
  change y ∈ Submodule.span (ZMod p) Yset at hy
  change x * y ∈ Submodule.span (ZMod p) Zset
  refine Submodule.span_induction
    (s := Xset)
    (p := fun x _ =>
      ∀ y,
        y ∈ Submodule.span (ZMod p) Yset →
          x * y ∈ Submodule.span (ZMod p) Zset)
    ?mem ?zero ?add ?smul hx y hy
  · rintro _x ⟨e, he, rfl⟩ y hy
    refine Submodule.span_induction
      (s := Yset)
      (p := fun y _ => B.basis e * y ∈ Submodule.span (ZMod p) Zset)
      ?mem_y ?zero_y ?add_y ?smul_y hy
    · rintro _y ⟨f, hf, rfl⟩
      exact h_basis_mul he hf
    · simp
    · intro y₁ y₂ _hy₁ _hy₂ hy₁_mem hy₂_mem
      simpa [mul_add] using
        (Submodule.span (ZMod p) Zset).add_mem hy₁_mem hy₂_mem
    · intro c y _hy hy_mem
      simpa [mul_smul_comm] using
        (Submodule.span (ZMod p) Zset).smul_mem c hy_mem
  · intro y hy
    simp
  · intro x₁ x₂ _hx₁ _hx₂ hx₁_mem hx₂_mem y hy
    simpa [add_mul] using
      (Submodule.span (ZMod p) Zset).add_mem (hx₁_mem y hy) (hx₂_mem y hy)
  · intro c x _hx hx_mem y hy
    simpa [smul_mul_assoc] using
      (Submodule.span (ZMod p) Zset).smul_mem c (hx_mem y hy)

namespace HMData

/-- Step 11 equality for positive powers, combining the forward inclusion from multiplicativity
with the reverse inclusion proved from the Zassenhaus-to-augmentation estimate for generators. -/
lemma augmentation_high_span
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q] [Finite Q]
    {m : ℕ}
    {R : OZReps p Q m}
    {B : MBData.{u, v} (p := p) (Q := Q) R}
    (M : HMData (p := p) (Q := Q) B)
    (s : ℕ) :
    augmentationIdealPower p Q (s + 1) = B.highWeightSpan (s + 1) := by
  apply le_antisymm
  · exact M.succ_high_span s
  · exact high_span_power B (s + 1)

/-- Build canonical high-weight multiplicative data from the single remaining multiplication
law `W_s * W_t ⊆ W_(s+t)`. -/
def canonicalMulHigh
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q] [Finite Q]
    {m : ℕ}
    (hm : 1 ≤ m)
    (R : OZReps p Q m)
    (Hmul :
      ∀ {s t : ℕ} {x y : denseGroupAlgebra p Q},
        x ∈ (MBData.canonical (p := p) (Q := Q) R).highWeightSpan s →
        y ∈ (MBData.canonical (p := p) (Q := Q) R).highWeightSpan t →
          x * y ∈
            (MBData.canonical (p := p) (Q := Q) R).highWeightSpan (s + t)) :
    HMData (p := p) (Q := Q)
      (MBData.canonical (p := p) (Q := Q) R) where
  one_high_zero :=
    MBData.canonical_high_zero
      (p := p) (Q := Q) R
  mul_mem_high := by
    intro s t x y hx hy
    exact Hmul hx hy
  aug_power_high :=
    MBData.canonical_high_span
      (p := p) (Q := Q) R hm

/-- Nonempty wrapper for `canonicalMulHigh`. -/
theorem nonempty_canonical_high
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q] [Finite Q]
    {m : ℕ}
    (hm : 1 ≤ m)
    (R : OZReps p Q m)
    (Hmul :
      ∀ {s t : ℕ} {x y : denseGroupAlgebra p Q},
        x ∈ (MBData.canonical (p := p) (Q := Q) R).highWeightSpan s →
        y ∈ (MBData.canonical (p := p) (Q := Q) R).highWeightSpan t →
          x * y ∈
            (MBData.canonical (p := p) (Q := Q) R).highWeightSpan (s + t)) :
    Nonempty (HMData (p := p) (Q := Q)
      (MBData.canonical (p := p) (Q := Q) R)) :=
  ⟨canonicalMulHigh (p := p) (Q := Q) hm R Hmul⟩

/-- Canonical high-weight multiplicative data from low-coordinate vanishing for every ordered
augmentation word. -/
theorem nonempty_low_coordinates
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q] [Finite Q]
    {m : ℕ}
    (hm : 1 ≤ m)
    (R : OZReps p Q m)
    (H :
      ∀ w : List (Fin R.r),
        R.LowWeightcoordsVanishword (R.wordWeight w) w) :
    Nonempty (HMData (p := p) (Q := Q)
      (MBData.canonical (p := p) (Q := Q) R)) :=
  nonempty_canonical_high
    (p := p) (Q := Q) hm R
    (fun hx hy =>
      MBData.high_low_coordinates
        (p := p) (Q := Q) R H hx hy)

/-- Under canonical high-weight multiplicativity, each ordered augmentation word has the
expected high weight. -/
lemma eval_high_span
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q] [Finite Q]
    {m : ℕ}
    (R : OZReps p Q m)
    (M : HMData (p := p) (Q := Q)
      (MBData.canonical (p := p) (Q := Q) R))
    (w : List (Fin R.r)) :
    R.wordEval w ∈
      (MBData.canonical (p := p) (Q := Q) R).highWeightSpan
        (R.wordWeight w) := by
  induction w with
  | nil =>
      simpa [OZReps.wordEval, OZReps.wordWeight] using
        M.one_high_zero
  | cons i w ih =>
      have hletter :
          groupAlgebraSub p Q (R.gen i) ∈
            (MBData.canonical (p := p) (Q := Q) R).highWeightSpan
              (R.weight i) :=
        MBData.canonical_sub_high
          (p := p) (Q := Q) (s := R.weight i) R
          (le_of_lt (R.weight_lt i))
          (g := R.gen i)
          (R.gen_mem i)
      have hmul :
          groupAlgebraSub p Q (R.gen i) * R.wordEval w ∈
            (MBData.canonical (p := p) (Q := Q) R).highWeightSpan
              (R.weight i + R.wordWeight w) :=
        M.mul_mem_high hletter ih
      simpa [OZReps.wordEval, OZReps.wordWeight] using hmul

/-- Canonical high-weight multiplicativity implies the all-word PBW low-coordinate
vanishing statement. -/
lemma low_coordinates_multiplicative
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q] [Finite Q]
    {m : ℕ}
    (R : OZReps p Q m)
    (M : HMData (p := p) (Q := Q)
      (MBData.canonical (p := p) (Q := Q) R)) :
    ∀ w : List (Fin R.r),
      R.LowWeightcoordsVanishword (R.wordWeight w) w := by
  intro w a ha
  have hhigh :
      R.wordEval w ∈
        (MBData.canonical (p := p) (Q := Q) R).highWeightSpan
          (R.wordWeight w) :=
    eval_high_span (p := p) (Q := Q) R M w
  exact
    basis_repr_high
      (B := (MBData.canonical (p := p) (Q := Q) R).basis)
      (wt := (MBData.canonical (p := p) (Q := Q) R).weight)
      hhigh
      (by simpa [MBData.canonical] using ha)

end HMData

end MBData

/-- Step 9--11 data: the high-weight spans attached to the Jennings monomial basis contain the
expected Zassenhaus differences and agree with the corresponding augmentation powers. -/
structure WSData
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q] [Finite Q]
    {m : ℕ}
    {R : OZReps p Q m}
    (B : MBData.{u, v} (p := p) (Q := Q) R) :
    Type (max (u + 1) (v + 1)) where
  sub_high_zassenhaus :
    ∀ {s : ℕ}, s ≤ m → ∀ {g : Q},
      g ∈ zassenhausFiltration p Q s →
        groupAlgebraSub p Q g ∈
          basisHighSpan (p := p) (Q := Q) B.basis B.weight s
  aug_high :
    augmentationIdealPower p Q m =
      basisHighSpan (p := p) (Q := Q) B.basis B.weight m

namespace WSData

/-- Assemble Step 9 and the positive-power form of Steps 10--11 into the `WSData`
package used by the final kernel argument.

The positivity hypothesis is exactly what is needed in the final theorem, where the killed
level is `n+1`. It lets us use the positive-power equality delivered by the multiplicative
high-weight filtration. -/
def subOneMultiplicative
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q] [Finite Q]
    {m : ℕ}
    {R : OZReps p Q m}
    {B : MBData.{u, v} (p := p) (Q := Q) R}
    (hm : 0 < m)
    (H9 :
      ∀ {s : ℕ}, s ≤ m → ∀ {g : Q},
        g ∈ zassenhausFiltration p Q s →
          groupAlgebraSub p Q g ∈ B.highWeightSpan s)
    (M : MBData.HMData (p := p) (Q := Q) B) :
    WSData (p := p) (Q := Q) B where
  sub_high_zassenhaus := by
    intro s hs g hg
    exact H9 hs hg
  aug_high := by
    rcases Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hm) with ⟨k, rfl⟩
    exact
      MBData.HMData.augmentation_high_span
        (p := p) (Q := Q) (B := B) M k

/-- Nonempty wrapper around `subOneMultiplicative`, convenient for reducing Step 9--11 to
two smaller construction tasks: prove the Step 9 Zassenhaus membership statement, and construct
the Step 10 multiplicative high-weight data. -/
theorem nonempty_sub_multiplicative
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q] [Finite Q]
    {m : ℕ}
    {R : OZReps p Q m}
    {B : MBData.{u, v} (p := p) (Q := Q) R}
    (hm : 0 < m)
    (H9 :
      ∀ {s : ℕ}, s ≤ m → ∀ {g : Q},
        g ∈ zassenhausFiltration p Q s →
          groupAlgebraSub p Q g ∈ B.highWeightSpan s)
    (M : MBData.HMData (p := p) (Q := Q) B) :
    Nonempty (WSData (p := p) (Q := Q) B) := by
  exact ⟨subOneMultiplicative (p := p) (Q := Q) (B := B) hm H9 M⟩

/-- Canonical weight-subspace data from the multiplicative high-weight package alone.

The Zassenhaus-to-high-weight containment field is supplied by
`MBData.canonical_sub_high`. -/
def ofCanonicalMultiplicative
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q] [Finite Q]
    {m : ℕ}
    (hm : 0 < m)
    (R : OZReps p Q m)
    (M : MBData.HMData
      (p := p) (Q := Q)
      (MBData.canonical (p := p) (Q := Q) R)) :
    WSData (p := p) (Q := Q)
      (MBData.canonical (p := p) (Q := Q) R) :=
  subOneMultiplicative
    (p := p) (Q := Q) (B := MBData.canonical (p := p) (Q := Q) R)
    hm
    (fun {s} hs {g} hg =>
      MBData.canonical_sub_high
        (p := p) (Q := Q) (s := s) R hs (g := g) hg)
    M

/-- Nonempty wrapper for `ofCanonicalMultiplicative`. -/
theorem nonempty_canonical_multiplicative
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q] [Finite Q]
    {m : ℕ}
    (hm : 0 < m)
    (R : OZReps p Q m)
    (M : MBData.HMData
      (p := p) (Q := Q)
      (MBData.canonical (p := p) (Q := Q) R)) :
    Nonempty (WSData (p := p) (Q := Q)
      (MBData.canonical (p := p) (Q := Q) R)) :=
  ⟨ofCanonicalMultiplicative (p := p) (Q := Q) hm R M⟩

end WSData

/-- The shared coefficient data obtained by expanding one ordered normal-form word.

This packages the three coefficient facts about
`[orderedWordFin e] - 1 = prod_i (1 + u_i)^(e_i) - 1` that are used in Steps 9 and 12 of
`S.tex`:

* every appearing Jennings exponent is coordinatewise bounded by the input exponent `e`;
* the zero exponent coordinate vanishes after subtracting the constant term;
* the coefficient of the single-variable monomial `u_i` is the scalar `e_i`.

Keeping these facts in one structure prevents the formalization from treating the same ordered
binomial expansion as three unrelated hard lemmas. -/
structure OEData
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q] [Finite Q]
    {m : ℕ}
    {R : OZReps p Q m}
    (B : MBData.{u, v} (p := p) (Q := Q) R)
    (e : Fin R.r → Fin p) : Type (max (u + 1) (v + 1)) where
  coeff_support_le :
    ∀ {i : B.ι},
      B.basis.repr (groupAlgebraSub p Q (orderedWordFin R.gen e)) i ≠ 0 →
        ∀ j : Fin R.r, (B.monomialIndex i j).val ≤ (e j).val
  coeff_zeroExponent :
    B.basis.repr (groupAlgebraSub p Q (orderedWordFin R.gen e))
        (B.monomialIndex.symm (fun _ : Fin R.r => (0 : Fin p))) = 0
  linear_coeff_input :
    ∀ i : Fin R.r,
      B.basis.repr (groupAlgebraSub p Q (orderedWordFin R.gen e))
          (B.monomialIndex.symm (singleJenningsExponent (p := p) i)) =
        ((e i).val : ZMod p)

namespace OEData

/-- Build the ordered-word coefficient package from the explicit formal binomial coefficient
formula for all monomial coordinates. -/
def subExpansionCoeff
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q] [Finite Q]
    {m : ℕ}
    {R : OZReps p Q m}
    (B : MBData.{u, v} (p := p) (Q := Q) R)
    (e : Fin R.r → Fin p)
    (Hcoeff :
      ∀ a : Fin R.r → Fin p,
        B.basis.repr (groupAlgebraSub p Q (orderedWordFin R.gen e))
            (B.monomialIndex.symm a) =
          orderedJenningsCoeff (p := p) e a) :
    OEData (p := p) (Q := Q) B e where
  coeff_support_le := by
    intro i hi j
    have hrepr :
        B.basis.repr (groupAlgebraSub p Q (orderedWordFin R.gen e)) i =
          orderedJenningsCoeff (p := p) e (B.monomialIndex i) := by
      simpa using Hcoeff (B.monomialIndex i)
    have hcoeff :
        orderedJenningsCoeff (p := p) e (B.monomialIndex i) ≠ 0 := by
      rwa [← hrepr]
    exact ordered_jennings_coord hcoeff j
  coeff_zeroExponent := by
    rw [Hcoeff (fun _ : Fin R.r => (0 : Fin p))]
    exact ordered_jennings_coeff (p := p) e
  linear_coeff_input := by
    intro i
    have hsingle :
        singleJenningsExponent (p := p) i = jenningsExpFin (p := p) i := by
      funext j
      by_cases hji : j = i
      · subst j
        rw [single_jennings_self, jennings_exp_self]
        apply Fin.ext
        exact Nat.mod_eq_of_lt (Fact.out : Nat.Prime p).one_lt
      · rw [single_ne (p := p) hji,
          jennings_exp_ne (p := p) hji]
        apply Fin.ext
        exact Nat.zero_mod p
    rw [Hcoeff (singleJenningsExponent (p := p) i), hsingle]
    exact jennings_coeff_single (p := p) e i

end OEData

namespace OEData

/-- The canonical ordered Jennings monomial basis carries the explicit ordered-word
`[word] - 1` binomial expansion. -/
noncomputable def canonical
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q] [Finite Q]
    {m : ℕ}
    (R : OZReps p Q m)
    (e : Fin R.r → Fin p) :
    OEData (p := p) (Q := Q)
      (MBData.canonical (p := p) (Q := Q) R) e := by
  classical
  refine
    subExpansionCoeff
      (p := p) (Q := Q)
      (B := MBData.canonical (p := p) (Q := Q) R) e ?_
  intro a
  have hsum :
      groupAlgebraSub p Q (orderedWordFin R.gen e) =
        ∑ b : Fin R.r → Fin p,
          orderedJenningsCoeff (p := p) e b • R.jenningsMonomialBasis b := by
    rw [← R.wordEquiv_apply e]
    exact R.jennings_monomial_basis e
  have hrepr :
      R.jenningsMonomialBasis.repr
          (groupAlgebraSub p Q (orderedWordFin R.gen e)) a =
        orderedJenningsCoeff (p := p) e a :=
    basis_repr_fintype
      R.jenningsMonomialBasis
      (fun b : Fin R.r → Fin p =>
        orderedJenningsCoeff (p := p) e b)
      hsum a
  change
    R.jenningsMonomialBasis.repr
        (groupAlgebraSub p Q (orderedWordFin R.gen e)) a =
      orderedJenningsCoeff (p := p) e a
  exact hrepr

end OEData

/-- The concrete finite ingredients needed to build `NFData`.

This is the construction target left by the truncated Jennings argument: ordered Zassenhaus
representatives, a monomial basis, high-weight/augmentation equality, and the coefficient
expansion of each ordered normal-form word. -/
structure FCData
    (p : ℕ) [Fact p.Prime]
    (Q : Type u) [Group Q] [Finite Q]
    (m : ℕ) : Type (max (u + 1) (v + 1)) where
  reps : OZReps p Q m
  monomial :
    MBData.{u, v} (p := p) (Q := Q) reps
  weightSubspace :
    WSData (p := p) (Q := Q) monomial
  orderedWordExpansion :
    ∀ e : Fin reps.r → Fin p,
      OEData (p := p) (Q := Q) monomial e

/-- Assemble the finite truncated Jennings normal-form package from the concrete monomial-basis
ingredients.

The remaining mathematical construction is now exactly the construction of the inputs to this
lemma: the high-weight/augmentation equality and the binomial coefficient expansion for each
ordered normal-form word. Once those are available, the nontrivial-element separation is forced
by the linear coefficient of a nonzero normal-form coordinate. -/
def NFData.weight_datao_worde
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q] [Finite Q]
    {m : ℕ}
    {R : OZReps p Q m}
    {B : MBData.{u, v} (p := p) (Q := Q) R}
    (hbot : zassenhausFiltration p Q m = ⊥)
    (W : WSData (p := p) (Q := Q) B)
    (Hexp :
      ∀ e : Fin R.r → Fin p,
        OEData (p := p) (Q := Q) B e) :
    NFData.{u, v} (p := p) Q m where
  reps := R
  ι := B.ι
  decEq := B.decEq
  basis := B.basis
  weight := B.weight
  aug_high := W.aug_high
  separates_nontrivial := by
    classical
    intro q hq
    rcases
      Submission.OZReps.exists_nonzerocoord_neone
        (p := p) (Q := Q) (m := m) R hbot hq with
      ⟨i, hi_weight, hi_ne⟩
    let e : Fin R.r → Fin p := R.wordEquiv.symm q
    let a : B.ι := B.monomialIndex.symm (singleJenningsExponent (p := p) i)
    refine ⟨a, ?_, ?_⟩
    · have ha_weight : B.weight a = R.weight i := by
        calc
          B.weight a = expWeight R.weight (B.monomialIndex a) := B.weight_apply a
          _ = expWeight R.weight (singleJenningsExponent (p := p) i) := by
                simp [a]
          _ = R.weight i := exp_single_exponent (p := p) R.weight i
      simpa [ha_weight] using hi_weight
    · have hword : orderedWordFin R.gen e = q := by
        rw [← R.wordEquiv_apply e]
        simp [e]
      have hcoeff :
          B.basis.repr (groupAlgebraSub p Q q) a =
            ((e i).val : ZMod p) := by
        simpa [a, hword] using (Hexp e).linear_coeff_input i
      have hscalar :
          ((e i).val : ZMod p) ≠ 0 := by
        exact
          zmod_cast_val
            (p := p) (a := e i) (by simpa [e] using hi_ne)
      rw [hcoeff]
      exact hscalar

/-- Nonempty wrapper for `NFData.weight_datao_worde`. -/
theorem nonempty_subspace_expansion
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q] [Finite Q]
    {m : ℕ}
    {R : OZReps p Q m}
    {B : MBData.{u, v} (p := p) (Q := Q) R}
    (hbot : zassenhausFiltration p Q m = ⊥)
    (W : WSData (p := p) (Q := Q) B)
    (Hexp :
      ∀ e : Fin R.r → Fin p,
        OEData (p := p) (Q := Q) B e) :
    Nonempty (NFData.{u, v} (p := p) Q m) :=
  ⟨NFData.weight_datao_worde
    (p := p) (Q := Q) (R := R) (B := B) hbot W Hexp⟩

namespace FCData

/-- Build the concrete normal-form component package from the separated finite ingredients:
Step 9 Zassenhaus-to-high-weight containment, Step 10 multiplicativity of high-weight spans, and
the ordered-word coefficient expansion from Step 12. -/
def subMultiplicativeExpansion
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q] [Finite Q]
    {m : ℕ}
    (hm : 0 < m)
    (R : OZReps p Q m)
    (B : MBData.{u, v} (p := p) (Q := Q) R)
    (H9 :
      ∀ {s : ℕ}, s ≤ m → ∀ {g : Q},
        g ∈ zassenhausFiltration p Q s →
          groupAlgebraSub p Q g ∈ B.highWeightSpan s)
    (M : MBData.HMData (p := p) (Q := Q) B)
    (Hexp :
      ∀ e : Fin R.r → Fin p,
        OEData (p := p) (Q := Q) B e) :
    FCData.{u, v} (p := p) Q m where
  reps := R
  monomial := B
  weightSubspace :=
    WSData.subOneMultiplicative
      (p := p) (Q := Q) (m := m) (B := B) hm H9 M
  orderedWordExpansion := Hexp

/-- Nonempty wrapper around `subMultiplicativeExpansion`. -/
theorem nonempty_multiplicative_expansion
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q] [Finite Q]
    {m : ℕ}
    (hm : 0 < m)
    (R : OZReps p Q m)
    (B : MBData.{u, v} (p := p) (Q := Q) R)
    (H9 :
      ∀ {s : ℕ}, s ≤ m → ∀ {g : Q},
        g ∈ zassenhausFiltration p Q s →
          groupAlgebraSub p Q g ∈ B.highWeightSpan s)
    (M : MBData.HMData (p := p) (Q := Q) B)
    (Hexp :
      ∀ e : Fin R.r → Fin p,
        OEData (p := p) (Q := Q) B e) :
    Nonempty (FCData.{u, v} (p := p) Q m) :=
  ⟨subMultiplicativeExpansion
    (p := p) (Q := Q) (m := m) hm R B H9 M Hexp⟩

/-- Component data yields the `NFData` consumed by the finite Jennings kernel theorem. -/
def normalFormData
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q] [Finite Q]
    {m : ℕ}
    (C : FCData.{u, v} (p := p) Q m)
    (hbot : zassenhausFiltration p Q m = ⊥) :
    NFData.{u, v} (p := p) Q m :=
  NFData.weight_datao_worde
    (p := p) (Q := Q) (m := m) (R := C.reps) (B := C.monomial)
    hbot C.weightSubspace C.orderedWordExpansion

/-- Nonempty component data gives nonempty normal-form data. -/
theorem nonempty_form_data
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q] [Finite Q]
    {m : ℕ}
    (hbot : zassenhausFiltration p Q m = ⊥)
    (hC : Nonempty (FCData.{u, v} (p := p) Q m)) :
    Nonempty (NFData.{u, v} (p := p) Q m) := by
  rcases hC with ⟨C⟩
  exact ⟨C.normalFormData hbot⟩

end FCData

namespace FCData

/-- Canonical component data from a canonical high-weight/augmentation package.

The ordered-word coefficient expansion is supplied by
`OEData.canonical`, so the only remaining inputs for the canonical
ordered Jennings basis are the ordered representatives and the high-weight subspace data. -/
def canonicalWeightSubspace
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q] [Finite Q]
    {m : ℕ}
    (R : OZReps p Q m)
    (W : WSData (p := p) (Q := Q)
      (MBData.canonical (p := p) (Q := Q) R)) :
    FCData.{u, 0} (p := p) Q m where
  reps := R
  monomial := MBData.canonical (p := p) (Q := Q) R
  weightSubspace := W
  orderedWordExpansion := OEData.canonical R

/-- Nonempty wrapper for `canonicalWeightSubspace`. -/
theorem nonempty_canonical_subspace
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q] [Finite Q]
    {m : ℕ}
    (R : OZReps p Q m)
    (W : WSData (p := p) (Q := Q)
      (MBData.canonical (p := p) (Q := Q) R)) :
    Nonempty (FCData.{u, 0} (p := p) Q m) :=
  ⟨canonicalWeightSubspace (p := p) (Q := Q) R W⟩

end FCData

namespace NFData

/-- Canonical normal-form data from a canonical high-weight/augmentation package. -/
theorem nonempty_canonical_subspace
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q] [Finite Q]
    {m : ℕ}
    (R : OZReps p Q m)
    (hbot : zassenhausFiltration p Q m = ⊥)
    (W : WSData (p := p) (Q := Q)
      (MBData.canonical (p := p) (Q := Q) R)) :
    Nonempty (NFData.{u, 0} (p := p) Q m) :=
  FCData.nonempty_form_data
    (p := p) (Q := Q) (m := m) hbot
    (FCData.nonempty_canonical_subspace
      (p := p) (Q := Q) R W)

/-- The normal-form package is exactly the data needed by the kernel interface already present in
`S0.lean`. -/
def toSeparationData
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q] [Finite Q]
    {m : ℕ}
    (T : NFData.{u, v} (p := p) Q m) :
    JSData.{u, v} (p := p) Q m where
  ι := T.ι
  decEq := T.decEq
  basis := T.basis
  weight := T.weight
  aug_power := by
    intro a ha
    rw [← T.aug_high]
    exact ha
  separates := by
    intro q hq
    exact T.separates_nontrivial hq

/-- The kernel consequence of the Jennings normal-form package. -/
theorem kernel
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q] [Finite Q]
    {m : ℕ}
    (T : NFData (p := p) Q m)
    {q : Q}
    (hqI : groupAlgebraSub p Q q ∈ augmentationIdealPower p Q m) :
    q = 1 := by
  have hkernel :=
    (T.toSeparationData).kernel
      (p := p) (Q := Q) (m := m) (q := q)
  exact hkernel hqI

end NFData

/-- Convert the TeX normal-form package into the packaged separation data used by `S0.lean`. -/
theorem separation_data_form
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q] [Finite Q]
    {m : ℕ}
    (hT : Nonempty (NFData.{u, v} (p := p) Q m)) :
    Nonempty (JSData.{u, v} (p := p) Q m) := by
  rcases hT with ⟨T⟩
  exact ⟨T.toSeparationData⟩

/-- Canonical high-weight/augmentation data for ordered representatives gives the packaged
Jennings separation data consumed by the finite-kernel theorem. -/
theorem separation_data_subspace
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q] [Finite Q]
    {m : ℕ}
    (R : OZReps p Q m)
    (hbot : zassenhausFiltration p Q m = ⊥)
    (W : WSData (p := p) (Q := Q)
      (MBData.canonical (p := p) (Q := Q) R)) :
    Nonempty (JSData.{u, 0} (p := p) Q m) :=
  separation_data_form
    (p := p) (Q := Q) (m := m)
    (NFData.nonempty_canonical_subspace
      (p := p) (Q := Q) R hbot W)

/-- Canonical all-word PBW low-coordinate vanishing gives the finite Jennings separation data. -/
theorem separation_low_coordinates
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q] [Finite Q]
    {m : ℕ}
    (hm : 1 ≤ m)
    (R : OZReps p Q m)
    (hbot : zassenhausFiltration p Q m = ⊥)
    (H :
      ∀ w : List (Fin R.r),
        R.LowWeightcoordsVanishword (R.wordWeight w) w) :
    Nonempty (JSData.{u, 0} (p := p) Q m) := by
  have hm_pos : 0 < m := lt_of_lt_of_le Nat.zero_lt_one hm
  rcases
    MBData.HMData.nonempty_low_coordinates
      (p := p) (Q := Q) hm R H with
    ⟨M⟩
  exact
    separation_data_subspace
      (p := p) (Q := Q) R hbot
      (WSData.ofCanonicalMultiplicative
        (p := p) (Q := Q) hm_pos R M)

/-- Separation data produces the fixed-layer Jennings certificate for the step
`D_n ∩ (1 + I^(n+1)) ≤ D_(n+1)`. -/
def certificateSeparationData
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q] [Finite Q]
    {n : ℕ}
    (hdata : Nonempty (JSData (p := p) Q (n + 1))) :
    JenningsLayerCertificate p Q n where
  drop_sub_next := by
    intro g _hgD hgI
    rcases hdata with ⟨Dsep⟩
    have hg_one : g = 1 :=
      Dsep.kernel (p := p) (Q := Q) (m := n + 1) (q := g) hgI
    rw [hg_one]
    exact (zassenhausFiltration p Q (n + 1)).one_mem

/-- Separation data gives the one-step Zassenhaus drop used in the final contradiction. -/
theorem step_separation_data
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q] [Finite Q]
    {n : ℕ}
    (hdata : Nonempty (JSData (p := p) Q (n + 1))) :
    ∀ {x : Q},
      x ∈ zassenhausFiltration p Q n →
      groupAlgebraSub p Q x ∈ augmentationIdealPower p Q (n + 1) →
        x ∈ zassenhausFiltration p Q (n + 1) := by
  intro x hxD hxI
  let C : JenningsLayerCertificate p Q n :=
    certificateSeparationData (p := p) (Q := Q) (n := n) hdata
  exact C.drop_sub_next hxD hxI

/-- Once separation data for the killed level is available, the target theorem is formal subgroup
bookkeeping. -/
theorem separation_data
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q] [Finite Q]
    {n : ℕ}
    (hn : 0 < n)
    (hbot : zassenhausFiltration p Q (n + 1) = ⊥)
    (hdata : Nonempty (JSData (p := p) Q (n + 1)))
    {q : Q}
    (hqD : q ∈ zassenhausFiltration p Q n)
    (hqI :
      groupAlgebraSub p Q q ∈ augmentationIdealPower p Q (n + 1)) :
    q = 1 := by
  exact
    separation_d_step
      (p := p) (Q := Q) (n := n) hn hbot
      (step_separation_data (p := p) (Q := Q) (n := n) hdata)
      hqD hqI
end TJennin
end Submission
