import Towers.Group.HallRecursiveCollection
import Mathlib.GroupTheory.FreeGroup.Basic

open scoped commutatorElement

namespace Towers

namespace CWord

/-- Number of occurrences of the left Hall-pair atom in a commutator word. -/
def pairLeftDegree : CWord HPAtom → ℕ
  | .atom .left => 1
  | .atom .right => 0
  | .commutator u v => u.pairLeftDegree + v.pairLeftDegree

/-- Number of occurrences of the right Hall-pair atom in a commutator word. -/
def pairRightDegree : CWord HPAtom → ℕ
  | .atom .left => 0
  | .atom .right => 1
  | .commutator u v => u.pairRightDegree + v.pairRightDegree

@[simp]
lemma pair_left_atom :
    (CWord.atom HPAtom.left).pairLeftDegree = 1 := rfl

@[simp]
lemma pair_atom_right :
    (CWord.atom HPAtom.right).pairLeftDegree = 0 := rfl

@[simp]
lemma pair_left_commutator (u v : CWord HPAtom) :
    (CWord.commutator u v).pairLeftDegree =
      u.pairLeftDegree + v.pairLeftDegree := rfl

@[simp]
lemma pair_atom_left :
    (CWord.atom HPAtom.left).pairRightDegree = 0 := rfl

@[simp]
lemma pair_degree_atom :
    (CWord.atom HPAtom.right).pairRightDegree = 1 := rfl

@[simp]
lemma pair_degree_commutator (u v : CWord HPAtom) :
    (CWord.commutator u v).pairRightDegree =
      u.pairRightDegree + v.pairRightDegree := rfl

@[simp]
lemma pair_left_base :
    hallPairBase.pairLeftDegree = 1 := rfl

@[simp]
lemma pair_degree_base :
    hallPairBase.pairRightDegree = 1 := rfl

@[simp]
lemma pair_left_iterate :
    ∀ n : ℕ, (pairLeftIterate n).pairLeftDegree = n + 1
  | 0 => rfl
  | n + 1 => by
      rw [pairLeftIterate, pair_left_commutator,
        pair_left_atom, pair_left_iterate]
      omega

@[simp]
lemma pair_degree_iterate :
    ∀ n : ℕ, (pairLeftIterate n).pairRightDegree = 1
  | 0 => rfl
  | n + 1 => by
      rw [pairLeftIterate, pair_degree_commutator,
        pair_atom_left, pair_degree_iterate,
        zero_add]

@[simp]
lemma pair_pairwise_error (r s : ℕ) :
    (iteratePairwiseError r s).pairLeftDegree = r + s + 2 := by
  simp [iteratePairwiseError]
  omega

@[simp]
lemma iterate_pairwise_error (r s : ℕ) :
    (iteratePairwiseError r s).pairRightDegree = 2 := by
  simp [iteratePairwiseError]

/-- Substitution into a Hall-pair word distributes its left bidegree over
the two substituted words. -/
@[simp]
lemma pair_left_bind
    (u v : CWord HPAtom) :
    ∀ w : CWord HPAtom,
      (hallPairBind u v w).pairLeftDegree =
        w.pairLeftDegree * u.pairLeftDegree +
          w.pairRightDegree * v.pairLeftDegree
  | .atom .left => by
      simp [hallPairBind]
  | .atom .right => by
      simp [hallPairBind]
  | .commutator a b => by
      change
        (hallPairBind u v a).pairLeftDegree +
              (hallPairBind u v b).pairLeftDegree =
          (a.pairLeftDegree + b.pairLeftDegree) *
                u.pairLeftDegree +
            (a.pairRightDegree + b.pairRightDegree) *
                v.pairLeftDegree
      rw [pair_left_bind u v a,
        pair_left_bind u v b]
      simp only [Nat.add_mul]
      ac_rfl

/-- Substitution into a Hall-pair word distributes its right bidegree over
the two substituted words. -/
@[simp]
lemma pair_degree_bind
    (u v : CWord HPAtom) :
    ∀ w : CWord HPAtom,
      (hallPairBind u v w).pairRightDegree =
        w.pairLeftDegree * u.pairRightDegree +
          w.pairRightDegree * v.pairRightDegree
  | .atom .left => by
      simp [hallPairBind]
  | .atom .right => by
      simp [hallPairBind]
  | .commutator a b => by
      change
        (hallPairBind u v a).pairRightDegree +
              (hallPairBind u v b).pairRightDegree =
          (a.pairLeftDegree + b.pairLeftDegree) *
                u.pairRightDegree +
            (a.pairRightDegree + b.pairRightDegree) *
                v.pairRightDegree
      rw [pair_degree_bind u v a,
        pair_degree_bind u v b]
      simp only [Nat.add_mul]
      ac_rfl

/-- The left bidegree of a substituted repeated-left Hall word is the
expected linear combination of the parent bidegrees. -/
@[simp]
lemma degree_bind_iterate
    (u v : CWord HPAtom)
    (r : ℕ) :
    (hallPairBind u v (pairLeftIterate r)).pairLeftDegree =
      (r + 1) * u.pairLeftDegree + v.pairLeftDegree := by
  rw [pair_left_bind]
  simp

/-- The right bidegree of a substituted repeated-left Hall word is the
expected linear combination of the parent bidegrees. -/
@[simp]
lemma pair_bind_iterate
    (u v : CWord HPAtom)
    (r : ℕ) :
    (hallPairBind u v (pairLeftIterate r)).pairRightDegree =
      (r + 1) * u.pairRightDegree + v.pairRightDegree := by
  rw [pair_degree_bind]
  simp

/-- Swap the two atoms in a Hall-pair commutator word. -/
def hallPairSwap : CWord HPAtom → CWord HPAtom
  | .atom .left => .atom .right
  | .atom .right => .atom .left
  | .commutator u v => .commutator u.hallPairSwap v.hallPairSwap

@[simp]
lemma pair_left_swap :
    ∀ w : CWord HPAtom,
      w.hallPairSwap.pairLeftDegree = w.pairRightDegree
  | .atom .left => rfl
  | .atom .right => rfl
  | .commutator u v => by
      rw [hallPairSwap, pair_left_commutator,
        pair_left_swap u, pair_left_swap v,
        pair_degree_commutator]

@[simp]
lemma pair_degree_swap :
    ∀ w : CWord HPAtom,
      w.hallPairSwap.pairRightDegree = w.pairLeftDegree
  | .atom .left => rfl
  | .atom .right => rfl
  | .commutator u v => by
      rw [hallPairSwap, pair_degree_commutator,
        pair_degree_swap u, pair_degree_swap v,
        pair_left_commutator]

@[simp]
lemma eval_pair_swap
    {G : Type*} [Group G]
    (x y : G) :
    ∀ w : CWord HPAtom,
      w.hallPairSwap.eval (HPAtom.eval x y) =
        w.eval (HPAtom.eval y x)
  | .atom .left => rfl
  | .atom .right => rfl
  | .commutator u v => by
      simp [hallPairSwap, eval_pair_swap x y u, eval_pair_swap x y v]

@[simp]
lemma pair_atom_degree (U V : ℕ) :
    ∀ w : CWord HPAtom,
      w.weight (HPAtom.weight U V) =
        w.pairLeftDegree * U + w.pairRightDegree * V
  | .atom .left => by simp [HPAtom.weight, CWord.weight]
  | .atom .right => by simp [HPAtom.weight, CWord.weight]
  | .commutator u v => by
      simp only [CWord.weight, pair_left_commutator,
        pair_degree_commutator, pair_atom_degree U V u,
        pair_atom_degree U V v]
      simp only [Nat.add_mul]
      omega

end CWord

/--
The Hall-Petresco divisibility invariant for a powered Hall word.

For a factor `w ^ c` arising while collecting `[x ^ p ^ A, y ^ p ^ B]`,
each original atom direction contributes enough divisibility to pay for its
initial prime power.
-/
def HPGood (p A B : ℕ) (w : CWord HPAtom) (c : ℤ) : Prop :=
  0 < w.pairLeftDegree ∧
    0 < w.pairRightDegree ∧
      (p ^ A : ℤ) ∣ (w.pairLeftDegree : ℤ) * c ∧
        (p ^ B : ℤ) ∣ (w.pairRightDegree : ℤ) * c

namespace HPGood

lemma dvd_choose_nat
    {p A k : ℕ} [Fact p.Prime] :
    p ^ A ∣ k * Nat.choose (p ^ A) k := by
  cases k with
  | zero =>
      simp
  | succ k =>
      have hpPos : 0 < p ^ A := pow_pos (Fact.out : Nat.Prime p).pos _
      have hpSucc : p ^ A - 1 + 1 = p ^ A := by omega
      have hchoose := Nat.add_one_mul_choose_eq (p ^ A - 1) k
      rw [hpSucc] at hchoose
      rw [Nat.mul_comm, ← hchoose]
      exact dvd_mul_right _ _

lemma pair_iterate_choose
    {p A r : ℕ} [Fact p.Prime] :
    HPGood p A 0 (CWord.pairLeftIterate r)
      (Nat.choose (p ^ A) (r + 1) : ℤ) := by
  refine ⟨by simp, by simp, ?_, ?_⟩
  · norm_cast
    simpa using
      (dvd_choose_nat (p := p) (A := A) (k := r + 1))
  · simp

lemma neg {p A B : ℕ} {w : CWord HPAtom} {c : ℤ}
    (h : HPGood p A B w c) :
    HPGood p A B w (-c) := by
  simpa [HPGood] using h

lemma add_same {p A B : ℕ} {w : CWord HPAtom} {c d : ℤ}
    (hc : HPGood p A B w c)
    (hd : HPGood p A B w d) :
    HPGood p A B w (c + d) := by
  refine ⟨hc.1, hc.2.1, ?_, ?_⟩
  · simpa [mul_add] using dvd_add hc.2.2.1 hd.2.2.1
  · simpa [mul_add] using dvd_add hc.2.2.2 hd.2.2.2

lemma mul_right {p A B : ℕ} {w : CWord HPAtom} {c : ℤ}
    (hc : HPGood p A B w c)
    (d : ℤ) :
    HPGood p A B w (c * d) := by
  refine ⟨hc.1, hc.2.1, ?_, ?_⟩
  · simpa [mul_assoc] using dvd_mul_of_dvd_left hc.2.2.1 d
  · simpa [mul_assoc] using dvd_mul_of_dvd_left hc.2.2.2 d

lemma commutator
    {p A B : ℕ}
    {u v : CWord HPAtom}
    {c d : ℤ}
    (hu : HPGood p A B u c)
    (hv : HPGood p A B v d) :
    HPGood p A B (.commutator u v) (c * d) := by
  refine ⟨by simp [hu.1, hv.1], by simp [hu.2.1, hv.2.1], ?_, ?_⟩
  · have hlu := dvd_mul_of_dvd_left hu.2.2.1 d
    have hlv := dvd_mul_of_dvd_left hv.2.2.1 c
    convert dvd_add hlu hlv using 1 ;
      simp only [CWord.pair_left_commutator, Nat.cast_add] ; ring
  · have hru := dvd_mul_of_dvd_left hu.2.2.2 d
    have hrv := dvd_mul_of_dvd_left hv.2.2.2 c
    convert dvd_add hru hrv using 1 ;
      simp only [CWord.pair_degree_commutator, Nat.cast_add] ; ring

lemma padic_val_dvd
    {p A d k : ℕ} [Fact p.Prime]
    (hd : 0 < d)
    (hk : k ≠ 0)
    (hdiv : p ^ A ∣ d * k) :
    p ^ A ≤ d * p ^ padicValNat p k := by
  apply Nat.le_of_dvd (mul_pos hd (pow_pos (Fact.out : Nat.Prime p).pos _))
  apply
    (padicValNat_dvd_iff_le
      (p := p)
      (mul_ne_zero (Nat.ne_of_gt hd) (pow_ne_zero _ (Fact.out : Nat.Prime p).ne_zero))).2
  have hval :
      A ≤ padicValNat p (d * k) :=
    (padicValNat_dvd_iff_le
      (p := p)
      (mul_ne_zero (Nat.ne_of_gt hd) hk)).1 hdiv
  simpa [padicValNat.mul (Nat.ne_of_gt hd) hk,
    padicValNat.mul (Nat.ne_of_gt hd) (pow_ne_zero _ (Fact.out : Nat.Prime p).ne_zero),
    padicValNat.prime_pow] using hval

/--
An admissible powered Hall word belongs to the weighted-power commutator subgroup at the
expected Hall-Petresco cutoff.
-/
lemma zpow_weighted_subgroup
    {p A B U V : ℕ} [Fact p.Prime]
    {G : Type*} [Group G]
    {f : HPAtom → G}
    {w : CWord HPAtom}
    {c : ℤ}
    (hgood : HPGood p A B w c) :
    w.eval f ^ c ∈
      weightedCommutatorSubgroup p f (HPAtom.weight U V)
        (U * p ^ A + V * p ^ B) := by
  by_cases hc : c = 0
  · subst c
    simp
  let e : ℕ := padicValNat p c.natAbs
  have hcAbs : c.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hc
  have hleft :
      p ^ A ≤ w.pairLeftDegree * p ^ e :=
    padic_val_dvd
      hgood.1 hcAbs (by
        simpa [Int.natAbs_mul] using Int.natCast_dvd.mp hgood.2.2.1)
  have hright :
      p ^ B ≤ w.pairRightDegree * p ^ e :=
    padic_val_dvd
      hgood.2.1 hcAbs (by
        simpa [Int.natAbs_mul] using Int.natCast_dvd.mp hgood.2.2.2)
  have hweight :
      U * p ^ A + V * p ^ B ≤
        w.weight (HPAtom.weight U V) * p ^ e := by
    rw [w.pair_atom_degree]
    calc
      U * p ^ A + V * p ^ B ≤
          U * (w.pairLeftDegree * p ^ e) +
            V * (w.pairRightDegree * p ^ e) :=
        Nat.add_le_add (Nat.mul_le_mul_left U hleft) (Nat.mul_le_mul_left V hright)
      _ = (w.pairLeftDegree * U + w.pairRightDegree * V) * p ^ e := by
        ring
  have hediv : p ^ e ∣ c.natAbs :=
    (padicValNat_dvd_iff_le hcAbs).2 le_rfl
  have hpow :
      w.eval f ^ c.natAbs ∈
        weightedCommutatorSubgroup p f (HPAtom.weight U V)
          (U * p ^ A + V * p ^ B) :=
    w.evalpowmem_weightpowercomm_wordsubgroupdvd hweight hediv
  cases c with
  | ofNat n =>
      simpa using hpow
  | negSucc n =>
      simpa using
        (weightedCommutatorSubgroup p f (HPAtom.weight U V)
          (U * p ^ A + V * p ^ B)).inv_mem hpow

end HPGood

namespace HACoeff

/-- A sign attached to one original Hall-Petresco input block. -/
inductive Sign
  | positive
  | negative
  deriving DecidableEq

/-- Integer value of a signed Hall-Petresco input block. -/
def Sign.intValue : Sign → ℤ
  | .positive => 1
  | .negative => -1

/--
The generalized binomial coefficient attached to a signed block of size `M`.

For a negative block this uses the standard identity
`choose (-M) k = (-1) ^ k * choose (M + k - 1) k`.
-/
def signedChoose : Sign → ℕ → ℕ → ℤ
  | .positive, M, k => Nat.choose M k
  | .negative, M, k => Int.negOnePow k * Nat.choose (M + k - 1) k

lemma signed_choose_ring
    (sign : Sign) (M k : ℕ) :
    signedChoose sign M k =
      Ring.choose (sign.intValue * (M : ℤ)) k := by
  cases sign with
  | positive =>
      simp [signedChoose, Sign.intValue, Ring.choose_natCast]
  | negative =>
      cases k with
      | zero =>
          simp [signedChoose, Sign.intValue]
      | succ k =>
          have hcast :
              ((M + (k + 1) - 1 : ℕ) : ℤ) =
                (M : ℤ) + (k + 1 : ℕ) - 1 := by
            omega
          rw [show Sign.negative.intValue * (M : ℤ) = -(M : ℤ) by
            simp [Sign.intValue]]
          rw [Ring.choose_neg]
          rw [← hcast, Ring.choose_natCast]
          simp [signedChoose, Units.smul_def]

/-- One signed input block together with the number of selected labels. -/
structure Block where
  sign : Sign
  degree : ℕ

/-- Total number of labels selected from a list of signed input blocks. -/
def degreeSum (blocks : List Block) : ℕ :=
  (blocks.map Block.degree).sum

/-- Product of the generalized binomial coefficients attached to a block list. -/
def blockProduct (M : ℕ) (blocks : List Block) : ℤ :=
  (blocks.map fun block => signedChoose block.sign M block.degree).prod

/--
The products whose integral span is the admissible coefficient set
`A_{r,s}(M,N)` from Lemma 2.
-/
def generatorSet (M N r s : ℕ) : Set ℤ :=
  { E |
    ∃ left right : List Block,
      degreeSum left = r ∧
        degreeSum right = s ∧
          blockProduct M left * blockProduct N right = E }

/-- The admissible coefficient set `A_{r,s}(M,N)` from Lemma 2. -/
def submodule (M N r s : ℕ) : Submodule ℤ ℤ :=
  Submodule.span ℤ (generatorSet M N r s)

lemma dvd_mul_choose (M k : ℕ) :
    M ∣ k * Nat.choose M k := by
  cases k with
  | zero =>
      simp
  | succ k =>
      by_cases hM : M = 0
      · subst M
        simp
      · have hMpos : 0 < M := Nat.pos_of_ne_zero hM
        have hsucc : M - 1 + 1 = M := by omega
        have hchoose := Nat.add_one_mul_choose_eq (M - 1) k
        rw [hsucc] at hchoose
        rw [Nat.mul_comm, ← hchoose]
        exact dvd_mul_right _ _

lemma dvd_multichoose_nat (M k : ℕ) :
    M ∣ k * Nat.choose (M + k - 1) k := by
  cases k with
  | zero =>
      simp
  | succ k =>
      have hchoose := Nat.choose_succ_right_eq (M + k) k
      have hsub : M + k - k = M := by omega
      rw [show M + (k + 1) - 1 = M + k by omega, Nat.mul_comm, hchoose, hsub]
      exact dvd_mul_left _ _

lemma nat_cast_choose
    (sign : Sign) (M k : ℕ) :
    (M : ℤ) ∣ (k : ℤ) * signedChoose sign M k := by
  cases sign with
  | positive =>
      simpa [signedChoose] using
        (show (M : ℤ) ∣ (k * Nat.choose M k : ℕ) by
          exact_mod_cast dvd_mul_choose M k)
  | negative =>
      have hcast :
          (M : ℤ) ∣
            (k : ℤ) * (Nat.choose (M + k - 1) k : ℤ) := by
        exact_mod_cast dvd_multichoose_nat M k
      simpa [signedChoose, mul_assoc, mul_left_comm, mul_comm] using
        dvd_mul_of_dvd_left hcast (Int.negOnePow k)

lemma nat_cast_dvd
    (M : ℕ) :
    ∀ blocks : List Block,
      (M : ℤ) ∣ (degreeSum blocks : ℤ) * blockProduct M blocks
  | [] => by
      simp [degreeSum, blockProduct]
  | block :: blocks => by
      have hhead :=
        nat_cast_choose block.sign M block.degree
      have htail := nat_cast_dvd M blocks
      convert
        dvd_add
          (dvd_mul_of_dvd_left hhead (blockProduct M blocks))
          (dvd_mul_of_dvd_left htail (signedChoose block.sign M block.degree)) using 1
      simp [degreeSum, blockProduct]
      ring

/--
Lemma 2: every admissible Hall-Petresco coefficient has the expected
divisibility in each atom direction.
-/
lemma basic_divisibility
    {M N r s : ℕ}
    {E : ℤ}
    (hE : E ∈ submodule M N r s) :
    (M : ℤ) ∣ (r : ℤ) * E ∧
      (N : ℤ) ∣ (s : ℤ) * E := by
  induction hE using Submodule.span_induction with
  | mem E hE =>
      rcases hE with ⟨left, right, hr, hs, rfl⟩
      constructor
      · convert
          dvd_mul_of_dvd_left
            (nat_cast_dvd M left)
            (blockProduct N right) using 1
        simp [hr]
        ring
      · convert
          dvd_mul_of_dvd_left
            (nat_cast_dvd N right)
            (blockProduct M left) using 1
        simp [hs]
        ring
  | zero =>
      simp
  | add E F _ _ hE hF =>
      constructor
      · simpa [mul_add] using dvd_add hE.1 hF.1
      · simpa [mul_add] using dvd_add hE.2 hF.2
  | smul c E _ hE =>
      constructor
      · convert dvd_mul_of_dvd_left hE.1 c using 1
        simp
        ring
      · convert dvd_mul_of_dvd_left hE.2 c using 1
        simp
        ring

/--
Lemma 3: an admissible coefficient for prime-power block sizes gives the
Hall-Petresco `Good` condition for a positive-bidegree commutator word.

The primality of `p` is not needed for this arithmetic implication.
-/
lemma good_submodule_pow
    {p A B : ℕ}
    {w : CWord HPAtom}
    {E : ℤ}
    (hleft : 0 < w.pairLeftDegree)
    (hright : 0 < w.pairRightDegree)
    (hE :
      E ∈ submodule
        (p ^ A) (p ^ B)
        w.pairLeftDegree w.pairRightDegree) :
    HPGood p A B w E := by
  rcases basic_divisibility hE with ⟨hleftDiv, hrightDiv⟩
  exact ⟨hleft, hright, hleftDiv, hrightDiv⟩

end HACoeff

/-!
## Prime-power Hall-pair collection certificates

The divisibility predicate above is deliberately independent of the mechanical
Hall collection procedure.  This section packages the remaining interface as a
certificate: a `Trace` carries both a finite raw Hall expansion of one powered
commutator and the bidegree divisibility invariant for every factor in that
specific expansion.

The remaining collection obligations are local: one raw factor must be
refined when either atomic input is replaced by its `p`th power.  Everything
else, including complete trace construction, is assembled below from those
pointwise prime-step refinements.  In particular, the Zassenhaus boundary
argument does not need to inspect the collector once these smaller statements
are available.
-/

namespace PPColl

/-- One raw factor in a collected Hall-pair expansion.

Unlike `WCFactor`, this structure does not carry a target
cutoff.  The cutoff certificate is recovered later from `HPGood`.
Keeping the raw collector and the divisibility proof separate makes the
remaining group-theoretic obligations explicit. -/
structure RFactor
    (G : Type*) [Group G] where
  word : CWord HPAtom
  multiplicity : ℤ
  conjugator : G

namespace RFactor

/-- Evaluate a raw Hall factor at a chosen pair of group elements. -/
def eval
    {G : Type*} [Group G]
    (x y : G)
    (F : RFactor G) :
    G :=
  F.conjugator *
      F.word.eval (HPAtom.eval x y) ^ F.multiplicity *
    F.conjugator⁻¹

lemma eval_def
    {G : Type*} [Group G]
    (x y : G)
    (F : RFactor G) :
    F.eval x y =
      F.conjugator *
          F.word.eval (HPAtom.eval x y) ^ F.multiplicity *
        F.conjugator⁻¹ :=
  rfl

/-- Transport a raw Hall factor through a group homomorphism.  The Hall word
and its integral multiplicity are universal; only the outer conjugator is
mapped. -/
def mapHom
    {G H : Type*} [Group G] [Group H]
    (φ : G →* H)
    (F : RFactor G) :
    RFactor H where
  word := F.word
  multiplicity := F.multiplicity
  conjugator := φ F.conjugator

/-- Evaluation of a transported raw factor is the image of its original
evaluation. -/
@[simp]
lemma eval_mapHom
    {G H : Type*} [Group G] [Group H]
    (φ : G →* H)
    (x y : G)
    (F : RFactor G) :
    (F.mapHom φ).eval (φ x) (φ y) =
      φ (F.eval x y) := by
  have hatoms :
      HPAtom.eval (φ x) (φ y) =
        fun a => φ (HPAtom.eval x y a) := by
    funext a
    cases a <;> rfl
  simp [mapHom, eval, CWord.map_eval, hatoms]

/-- The bidegree divisibility certificate required of a raw factor collected
from `[x^(p^a), y^(p^b)]`. -/
def Good
    (p a b : ℕ)
    {G : Type*} [Group G]
    (F : RFactor G) :
    Prop :=
  HPGood p a b F.word F.multiplicity

/-- Transport does not alter the Hall-Petresco arithmetic certificate of a
raw factor. -/
@[simp]
lemma good_mapHom
    {p a b : ℕ}
    {G H : Type*} [Group G] [Group H]
    (φ : G →* H)
    (F : RFactor G) :
    (F.mapHom φ).Good p a b ↔ F.Good p a b :=
  Iff.rfl

/-- Expose the underlying `HPGood` predicate when applying the
arithmetic API. -/
lemma good_iff
    {p a b : ℕ}
    {G : Type*} [Group G]
    {F : RFactor G} :
    F.Good p a b ↔
      HPGood p a b F.word F.multiplicity :=
  Iff.rfl

/-- Conjugate a raw collected factor. -/
def conjugate
    {G : Type*} [Group G]
    (c : G)
    (F : RFactor G) :
    RFactor G :=
  { F with conjugator := c * F.conjugator }

@[simp]
lemma eval_conjugate
    {G : Type*} [Group G]
    (x y c : G)
    (F : RFactor G) :
    (F.conjugate c).eval x y =
      c * F.eval x y * c⁻¹ := by
  simp only [conjugate, eval]
  group

/-- Invert a raw collected factor by negating its integral multiplicity. -/
def inv
    {G : Type*} [Group G]
    (F : RFactor G) :
    RFactor G :=
  { F with multiplicity := -F.multiplicity }

@[simp]
lemma eval_inv
    {G : Type*} [Group G]
    (x y : G)
    (F : RFactor G) :
    F.inv.eval x y = (F.eval x y)⁻¹ := by
  simp [inv, eval, mul_assoc]

/-- Conjugating a factor does not change its Hall-Petresco divisibility
certificate. -/
lemma Good.conjugate
    {p a b : ℕ}
    {G : Type*} [Group G]
    {F : RFactor G}
    (hF : F.Good p a b)
    (c : G) :
    (F.conjugate c).Good p a b :=
  hF

/-- Inverting a factor preserves its Hall-Petresco divisibility certificate. -/
lemma Good.inv
    {p a b : ℕ}
    {G : Type*} [Group G]
    {F : RFactor G}
    (hF : F.Good p a b) :
    F.inv.Good p a b :=
  HPGood.neg hF

/-- Swap the two Hall-pair atoms in a raw factor. -/
def swap
    {G : Type*} [Group G]
    (F : RFactor G) :
    RFactor G where
  word := F.word.hallPairSwap
  multiplicity := F.multiplicity
  conjugator := F.conjugator

@[simp]
lemma eval_swap
    {G : Type*} [Group G]
    (x y : G)
    (F : RFactor G) :
    F.swap.eval x y = F.eval y x := by
  simp [swap, eval]

/-- Swapping a factor exchanges its left and right divisibility exponents. -/
lemma Good.swap
    {p a b : ℕ}
    {G : Type*} [Group G]
    {F : RFactor G}
    (hF : F.Good p a b) :
    F.swap.Good p b a := by
  rw [Good, HPGood]
  change
    0 < F.word.hallPairSwap.pairLeftDegree ∧
      0 < F.word.hallPairSwap.pairRightDegree ∧
        (p ^ b : ℤ) ∣ (F.word.hallPairSwap.pairLeftDegree : ℤ) * F.multiplicity ∧
          (p ^ a : ℤ) ∣ (F.word.hallPairSwap.pairRightDegree : ℤ) * F.multiplicity
  simpa using ⟨hF.2.1, hF.1, hF.2.2.2, hF.2.2.1⟩

/-- A certified raw factor belongs to the weighted-power Hall-pair subgroup at
the exact two-sided prime-power cutoff. -/
lemma eval_weighted_pair
    {p a b A B : ℕ} [Fact p.Prime]
    {G : Type*} [Group G]
    {x y : G}
    {F : RFactor G}
    (hF : F.Good p a b) :
    F.eval x y ∈
      weightedPairSubgroup p x y A B
        (A * p ^ a + B * p ^ b) := by
  have hword :
      F.word.eval (HPAtom.eval x y) ^ F.multiplicity ∈
        weightedPairSubgroup p x y A B
          (A * p ^ a + B * p ^ b) :=
    HPGood.zpow_weighted_subgroup
      (U := A) (V := B) hF
  exact
    (inferInstance :
      (weightedPairSubgroup p x y A B
        (A * p ^ a + B * p ^ b)).Normal).conj_mem
          (F.word.eval (HPAtom.eval x y) ^ F.multiplicity)
          hword
          F.conjugator

end RFactor

/-- Evaluate a finite list of raw Hall factors in collection order. -/
def listEval
    {G : Type*} [Group G]
    (x y : G)
    (L : List (RFactor G)) :
    G :=
  (L.map (RFactor.eval x y)).prod

@[simp]
lemma listEval_nil
    {G : Type*} [Group G]
    (x y : G) :
    listEval x y ([] : List (RFactor G)) = 1 :=
  rfl

@[simp]
lemma listEval_cons
    {G : Type*} [Group G]
    (x y : G)
    (F : RFactor G)
    (L : List (RFactor G)) :
    listEval x y (F :: L) =
      F.eval x y * listEval x y L :=
  rfl

@[simp]
lemma listEval_append
    {G : Type*} [Group G]
    (x y : G)
    (L M : List (RFactor G)) :
    listEval x y (L ++ M) =
      listEval x y L * listEval x y M := by
  simp [listEval]

namespace RFactor

/-- Transport an ordered raw-factor list through a group homomorphism. -/
def listMapHom
    {G H : Type*} [Group G] [Group H]
    (φ : G →* H)
    (L : List (RFactor G)) :
    List (RFactor H) :=
  L.map (mapHom φ)

@[simp]
lemma list_hom_nil
    {G H : Type*} [Group G] [Group H]
    (φ : G →* H) :
    listMapHom φ ([] : List (RFactor G)) = [] :=
  rfl

@[simp]
lemma list_hom_cons
    {G H : Type*} [Group G] [Group H]
    (φ : G →* H)
    (F : RFactor G)
    (L : List (RFactor G)) :
    listMapHom φ (F :: L) =
      F.mapHom φ :: listMapHom φ L :=
  rfl

@[simp]
lemma list_hom_append
    {G H : Type*} [Group G] [Group H]
    (φ : G →* H)
    (L M : List (RFactor G)) :
    listMapHom φ (L ++ M) =
      listMapHom φ L ++ listMapHom φ M := by
  simp [listMapHom]

/-- Evaluation of an ordered raw-factor list commutes with transport. -/
@[simp]
lemma list_eval_hom
    {G H : Type*} [Group G] [Group H]
    (φ : G →* H)
    (x y : G)
    (L : List (RFactor G)) :
    PPColl.listEval (φ x) (φ y) (listMapHom φ L) =
      φ (PPColl.listEval x y L) := by
  induction L with
  | nil =>
      simp
  | cons F L ih =>
      change
        (F.mapHom φ).eval (φ x) (φ y) *
            PPColl.listEval (φ x) (φ y) (listMapHom φ L) =
          φ (F.eval x y * PPColl.listEval x y L)
      rw [eval_mapHom, ih, map_mul]

end RFactor

/-- Conjugate each factor in an explicit raw collection. -/
def listConjugate
    {G : Type*} [Group G]
    (c : G)
    (L : List (RFactor G)) :
    List (RFactor G) :=
  L.map (RFactor.conjugate c)

@[simp]
lemma list_eval_conjugate
    {G : Type*} [Group G]
    (x y c : G)
    (L : List (RFactor G)) :
    listEval x y (listConjugate c L) =
      c * listEval x y L * c⁻¹ := by
  induction L with
  | nil =>
      simp [listConjugate]
  | cons F L ih =>
      change
        (F.conjugate c).eval x y *
            listEval x y (listConjugate c L) =
          c * (F.eval x y * listEval x y L) * c⁻¹
      rw [RFactor.eval_conjugate, ih]
      group

/-- Reverse and invert a raw collection so that its evaluation is the inverse
of the original product. -/
def listInv
    {G : Type*} [Group G] :
    List (RFactor G) → List (RFactor G)
  | [] => []
  | F :: L => listInv L ++ [F.inv]

@[simp]
lemma list_eval_inv
    {G : Type*} [Group G]
    (x y : G)
    (L : List (RFactor G)) :
    listEval x y (listInv L) =
      (listEval x y L)⁻¹ := by
  induction L with
  | nil =>
      simp [listInv]
  | cons F L ih =>
      simp only [listInv, listEval_append, listEval_cons, listEval_nil,
        RFactor.eval_inv, ih, mul_one, mul_inv_rev]

/-- Conjugation preserves the pointwise Hall-Petresco invariant on a list. -/
lemma forall_good_conjugate
    {p a b : ℕ}
    {G : Type*} [Group G]
    {L : List (RFactor G)}
    (hL : ∀ F ∈ L, F.Good p a b)
    (c : G) :
    ∀ F ∈ listConjugate c L, F.Good p a b := by
  intro F hF
  rcases List.mem_map.mp hF with ⟨E, hE, rfl⟩
  exact (hL E hE).conjugate c

/-- Reversal and inversion preserve the pointwise Hall-Petresco invariant on a
list. -/
lemma forall_good_inv
    {p a b : ℕ}
    {G : Type*} [Group G]
    {L : List (RFactor G)}
    (hL : ∀ F ∈ L, F.Good p a b) :
    ∀ F ∈ listInv L, F.Good p a b := by
  intro F hF
  induction L with
  | nil =>
      change F ∈ ([] : List (RFactor G)) at hF
      contradiction
  | cons E L ih =>
      change F ∈ listInv L ++ [E.inv] at hF
      rw [List.mem_append, List.mem_singleton] at hF
      rcases hF with hF | hF
      · exact ih (fun Z hZ => hL Z (by simp [hZ])) hF
      · subst F
        exact (hL E (by simp)).inv

/-- Swap the two Hall-pair atoms in every factor of a raw collection. -/
def listSwap
    {G : Type*} [Group G]
    (L : List (RFactor G)) :
    List (RFactor G) :=
  L.map RFactor.swap

@[simp]
lemma list_eval_swap
    {G : Type*} [Group G]
    (x y : G)
    (L : List (RFactor G)) :
    listEval x y (listSwap L) = listEval y x L := by
  induction L with
  | nil =>
      rfl
  | cons F L ih =>
      change F.swap.eval x y * listEval x y (listSwap L) =
        F.eval y x * listEval y x L
      rw [RFactor.eval_swap, ih]

/-- Swapping a list exchanges its left and right divisibility exponents. -/
lemma forall_good_swap
    {p a b : ℕ}
    {G : Type*} [Group G]
    {L : List (RFactor G)}
    (hL : ∀ F ∈ L, F.Good p a b) :
    ∀ F ∈ listSwap L, F.Good p b a := by
  intro F hF
  rcases List.mem_map.mp hF with ⟨E, hE, rfl⟩
  exact (hL E hE).swap

/-- A finite list of certified raw factors belongs to the weighted-power
Hall-pair subgroup at the exact two-sided cutoff. -/
lemma weighted_pair_subgroup
    {p a b A B : ℕ} [Fact p.Prime]
    {G : Type*} [Group G]
    {x y : G}
    {L : List (RFactor G)}
    (hL : ∀ F ∈ L, F.Good p a b) :
    listEval x y L ∈
      weightedPairSubgroup p x y A B
        (A * p ^ a + B * p ^ b) := by
  apply Subgroup.list_prod_mem
  intro z hz
  rcases List.mem_map.mp hz with ⟨F, hF, rfl⟩
  exact RFactor.eval_weighted_pair (hL F hF)

namespace RFactor

/-- The single raw factor representing the hallPair Hall-pair commutator. -/
def hallPair
    {G : Type*} [Group G] :
    RFactor G where
  word := CWord.hallPairBase
  multiplicity := 1
  conjugator := 1

@[simp]
lemma eval_basic
    {G : Type*} [Group G]
    (x y : G) :
    (hallPair : RFactor G).eval x y = ⁅x, y⁆ := by
  simp [hallPair, eval]

@[simp]
lemma good_basic
    {p : ℕ}
    {G : Type*} [Group G] :
    (hallPair : RFactor G).Good p 0 0 := by
  simp [hallPair, Good, HPGood]

end RFactor

/-- A finite Hall collection trace for the powered commutator
`[x^(p^a), y^(p^b)]`.

The trace records both the pure group identity and the pointwise arithmetic
invariant for the factors in that exact expansion.  Bundling these fields keeps
the invariant attached to the witness selected by `Classical.choice`. -/
structure Trace
    (p : ℕ)
    {G : Type*} [Group G]
    (x y : G)
    (a b : ℕ) where
  factors : List (RFactor G)
  eval_eq :
    listEval x y factors =
      ⁅x ^ (p ^ a), y ^ (p ^ b)⁆
  factors_good :
    ∀ F ∈ factors, F.Good p a b

/--
A pointwise refinement replaces one old raw factor by a finite list of new raw
factors.  The source and destination pairs are kept explicit: this is the
small interface needed when one atomic input is replaced by its `p`th power.

The destination bidegrees are also explicit.  A refinement therefore records
exactly the two facts used by the recursive trace construction:

* the replacement list evaluates to the old factor at the substituted pair;
* every replacement factor satisfies the stronger destination divisibility
  invariant.
-/
structure RFactor.Refa
    (p a b : ℕ)
    {G : Type*} [Group G]
    (x y x' y' : G)
    (F : RFactor G) where
  factors : List (RFactor G)
  eval_eq :
    listEval x y factors =
      F.eval x' y'
  factors_good :
    ∀ E ∈ factors, E.Good p a b

namespace RFactor.Refa

/-- The evaluation equality carried by a single-factor refinement. -/
lemma eval_factors
    {p a b : ℕ}
    {G : Type*} [Group G]
    {x y x' y' : G}
    {F : RFactor G}
    (R : RFactor.Refa p a b x y x' y' F) :
    listEval x y R.factors =
      F.eval x' y' :=
  R.eval_eq

/-- The pointwise divisibility invariant carried by a single-factor
refinement. -/
lemma factor_good
    {p a b : ℕ}
    {G : Type*} [Group G]
    {x y x' y' : G}
    {F E : RFactor G}
    (R : RFactor.Refa p a b x y x' y' F)
    (hE : E ∈ R.factors) :
    E.Good p a b :=
  R.factors_good E hE

/-- A refinement may be conjugated together with its source factor. -/
def conjugate
    {p a b : ℕ}
    {G : Type*} [Group G]
    {x y x' y' : G}
    {F : RFactor G}
    (R : RFactor.Refa p a b x y x' y' F)
    (c : G) :
    RFactor.Refa p a b x y x' y' (F.conjugate c) where
  factors := listConjugate c R.factors
  eval_eq := by
    rw [list_eval_conjugate, R.eval_eq, RFactor.eval_conjugate]
  factors_good :=
    forall_good_conjugate R.factors_good c

/-- A refinement may be inverted together with its source factor. -/
def inv
    {p a b : ℕ}
    {G : Type*} [Group G]
    {x y x' y' : G}
    {F : RFactor G}
    (R : RFactor.Refa p a b x y x' y' F) :
    RFactor.Refa p a b x y x' y' F.inv where
  factors := listInv R.factors
  eval_eq := by
    rw [list_eval_inv, R.eval_eq, RFactor.eval_inv]
  factors_good :=
    forall_good_inv R.factors_good

end RFactor.Refa

/--
A list refinement is the finite-product version of `RFactor.Refa`.
It packages the flattening step needed after pointwise Hall collection.
-/
structure LRef
    (p a b : ℕ)
    {G : Type*} [Group G]
    (x y x' y' : G)
    (L : List (RFactor G)) where
  factors : List (RFactor G)
  eval_eq :
    listEval x y factors =
      listEval x' y' L
  factors_good :
    ∀ E ∈ factors, E.Good p a b

namespace LRef

/-- The empty source product refines to the empty destination product. -/
def nil
    {p a b : ℕ}
    {G : Type*} [Group G]
    (x y x' y' : G) :
    LRef p a b x y x' y' [] where
  factors := []
  eval_eq := rfl
  factors_good := by
    simp

/-- Regard a single-factor refinement as a one-element list refinement. -/
def singleton
    {p a b : ℕ}
    {G : Type*} [Group G]
    {x y x' y' : G}
    {F : RFactor G}
    (R : RFactor.Refa p a b x y x' y' F) :
    LRef p a b x y x' y' [F] where
  factors := R.factors
  eval_eq := by
    simpa using R.eval_eq
  factors_good :=
    R.factors_good

/-- Prepend a refined factor to an already-refined tail. -/
def cons
    {p a b : ℕ}
    {G : Type*} [Group G]
    {x y x' y' : G}
    {F : RFactor G}
    {L : List (RFactor G)}
    (R : RFactor.Refa p a b x y x' y' F)
    (S : LRef p a b x y x' y' L) :
    LRef p a b x y x' y' (F :: L) where
  factors := R.factors ++ S.factors
  eval_eq := by
    rw [listEval_append, R.eval_eq, S.eval_eq, listEval_cons]
  factors_good := by
    intro E hE
    rw [List.mem_append] at hE
    rcases hE with hE | hE
    · exact R.factors_good E hE
    · exact S.factors_good E hE

/-- Concatenate refinements of two adjacent source lists. -/
def append
    {p a b : ℕ}
    {G : Type*} [Group G]
    {x y x' y' : G}
    {L M : List (RFactor G)}
    (R : LRef p a b x y x' y' L)
    (S : LRef p a b x y x' y' M) :
    LRef p a b x y x' y' (L ++ M) where
  factors := R.factors ++ S.factors
  eval_eq := by
    rw [listEval_append, R.eval_eq, S.eval_eq, listEval_append]
  factors_good := by
    intro E hE
    rw [List.mem_append] at hE
    rcases hE with hE | hE
    · exact R.factors_good E hE
    · exact S.factors_good E hE

/-- The evaluation equality carried by a list refinement. -/
lemma eval_factors
    {p a b : ℕ}
    {G : Type*} [Group G]
    {x y x' y' : G}
    {L : List (RFactor G)}
    (R : LRef p a b x y x' y' L) :
    listEval x y R.factors =
      listEval x' y' L :=
  R.eval_eq

/-- Every factor produced by a list refinement has the destination
Hall-Petresco invariant. -/
lemma factor_good
    {p a b : ℕ}
    {G : Type*} [Group G]
    {x y x' y' : G}
    {L : List (RFactor G)}
    {E : RFactor G}
    (R : LRef p a b x y x' y' L)
    (hE : E ∈ R.factors) :
    E.Good p a b :=
  R.factors_good E hE

end LRef

/--
A left prime refinement expands one already-collected factor after replacing
the left atom by its `p`th power.  Its destination factors gain one unit of
left prime-power divisibility.
-/
abbrev LeftPrimeRefinement
    (p a b : ℕ)
    {G : Type*} [Group G]
    (x y : G)
    (F : RFactor G) :=
  RFactor.Refa p (a + 1) b x y (x ^ p) y F

/--
A right prime refinement expands one already-collected factor after replacing
the right atom by its `p`th power.  Its destination factors gain one unit of
right prime-power divisibility.
-/
abbrev RightPrimeRefinement
    (p a b : ℕ)
    {G : Type*} [Group G]
    (x y : G)
    (F : RFactor G) :=
  RFactor.Refa p a (b + 1) x y x (y ^ p) F

/-!
## Local coefficient flow for one right-prime substitution

The remaining Hall collector has two rather different jobs:

* it rewrites the group element obtained after substituting `y ^ p` for the
  right atom as a finite product of raw Hall factors;
* it proves that each new multiplicity has inherited the old left
  divisibility and gained one extra right factor of `p`.

The accumulated exponents `a` and `b` are irrelevant to the local collection
algorithm.  They only enter after collection, when the coefficient-flow
certificate below is composed with the old `HPGood` witness.  Keeping
that local certificate explicit makes the remaining admitted step materially
smaller: it is an incremental normalized collection step with no arbitrary
outer conjugator and no accumulated prime-power bookkeeping.
-/

end PPColl

namespace CWord

/-- Both Hall-pair atoms occur in a commutator word.  This is the part of the
Hall-Petresco invariant needed by the normalized one-step collector before any
prime-power exponent is considered. -/
def PBPos
    (w : CWord HPAtom) :
    Prop :=
  0 < w.pairLeftDegree ∧
    0 < w.pairRightDegree

namespace PBPos

/-- The left-degree projection of a positive Hall-pair bidegree. -/
lemma left
    {w : CWord HPAtom}
    (hw : w.PBPos) :
    0 < w.pairLeftDegree :=
  hw.1

/-- The right-degree projection of a positive Hall-pair bidegree. -/
lemma right
    {w : CWord HPAtom}
    (hw : w.PBPos) :
    0 < w.pairRightDegree :=
  hw.2

/-- Swapping the Hall-pair atoms preserves positivity of both bidegrees. -/
lemma swap
    {w : CWord HPAtom}
    (hw : w.PBPos) :
    w.hallPairSwap.PBPos := by
  exact ⟨by simpa using hw.right, by simpa using hw.left⟩

end PBPos

end CWord

namespace HPGood

/-- Forget the accumulated prime powers and retain only the positivity needed
by a local Hall-pair collection step. -/
lemma pairBidegreePositive
    {p a b : ℕ}
    {w : CWord HPAtom}
    {c : ℤ}
    (h : HPGood p a b w c) :
    w.PBPos :=
  ⟨h.1, h.2.1⟩

end HPGood

namespace PPColl

namespace RFactor

/-- Remove the outer conjugator from a raw factor while retaining its Hall word
and integral multiplicity.  The local collector only needs to solve this
normalized case; the original conjugator is restored afterwards. -/
def withoutConjugator
    {G : Type*} [Group G]
    (F : RFactor G) :
    RFactor G :=
  { F with conjugator := 1 }

@[simp]
lemma word_withoutConjugator
    {G : Type*} [Group G]
    (F : RFactor G) :
    F.withoutConjugator.word = F.word :=
  rfl

@[simp]
lemma multiplicity_withoutConjugator
    {G : Type*} [Group G]
    (F : RFactor G) :
    F.withoutConjugator.multiplicity = F.multiplicity :=
  rfl

@[simp]
lemma conjugator_withoutConjugator
    {G : Type*} [Group G]
    (F : RFactor G) :
    F.withoutConjugator.conjugator = 1 :=
  rfl

/-- Normalizing a factor does not alter its Hall-Petresco invariant. -/
@[simp]
lemma good_withoutConjugator
    {p a b : ℕ}
    {G : Type*} [Group G]
    (F : RFactor G) :
    F.withoutConjugator.Good p a b ↔
      F.Good p a b :=
  Iff.rfl

/-- A normalized factor evaluates to the bare powered Hall word. -/
@[simp]
lemma eval_withoutConjugator
    {G : Type*} [Group G]
    (x y : G)
    (F : RFactor G) :
    F.withoutConjugator.eval x y =
      F.word.eval (HPAtom.eval x y) ^ F.multiplicity := by
  simp [withoutConjugator, eval]

/-- Restoring the old conjugator after normalization recovers the original raw
factor exactly. -/
@[simp]
lemma withoutConjugator_conjugate
    {G : Type*} [Group G]
    (F : RFactor G) :
    F.withoutConjugator.conjugate F.conjugator = F := by
  cases F
  simp [withoutConjugator, conjugate]

/-- The original factor evaluation is the conjugate of its normalized
evaluation. -/
lemma conjugate_without_conjugator
    {G : Type*} [Group G]
    (x y : G)
    (F : RFactor G) :
    F.eval x y =
      F.conjugator * F.withoutConjugator.eval x y * F.conjugator⁻¹ := by
  rw [← eval_conjugate, withoutConjugator_conjugate]

end RFactor

/--
The coefficient relation produced by one normalized right-prime collection.

For every output factor `E`, the old left coefficient divides the new left
coefficient unchanged.  On the right, `p` times the old coefficient divides the
new coefficient.  The latter is exactly the one-unit right-prime gain needed
when a previously collected factor is evaluated at `(x, y ^ p)`.

This relation intentionally has no accumulated exponents `a` or `b`, and it
does not mention evaluation in a group.
-/
structure RCFlow
    (p : ℕ)
    (w : CWord HPAtom)
    (c : ℤ)
    {G : Type*} [Group G]
    (E : RFactor G) :
    Prop where
  target_positive :
    E.word.PBPos
  left_dvd :
    (w.pairLeftDegree : ℤ) * c ∣
      (E.word.pairLeftDegree : ℤ) * E.multiplicity
  right_dvd :
    (p : ℤ) * ((w.pairRightDegree : ℤ) * c) ∣
      (E.word.pairRightDegree : ℤ) * E.multiplicity

namespace RCFlow

/-- The output factor of a coefficient-flow certificate has positive left
Hall-pair degree. -/
lemma leftDegree_pos
    {p : ℕ}
    {w : CWord HPAtom}
    {c : ℤ}
    {G : Type*} [Group G]
    {E : RFactor G}
    (hE : RCFlow p w c E) :
    0 < E.word.pairLeftDegree :=
  hE.target_positive.left

/-- The output factor of a coefficient-flow certificate has positive right
Hall-pair degree. -/
lemma rightDegree_pos
    {p : ℕ}
    {w : CWord HPAtom}
    {c : ℤ}
    {G : Type*} [Group G]
    {E : RFactor G}
    (hE : RCFlow p w c E) :
    0 < E.word.pairRightDegree :=
  hE.target_positive.right

/-- Local coefficient flow upgrades an old Hall-Petresco invariant by one
right-prime unit.  This is the arithmetic composition step that keeps the
collector independent of the accumulated exponents. -/
lemma good
    {p a b : ℕ}
    {w : CWord HPAtom}
    {c : ℤ}
    {G : Type*} [Group G]
    {E : RFactor G}
    (hsource : HPGood p a b w c)
    (hE : RCFlow p w c E) :
    E.Good p a (b + 1) := by
  rw [RFactor.good_iff]
  refine ⟨hE.leftDegree_pos, hE.rightDegree_pos, ?_, ?_⟩
  · exact dvd_trans hsource.2.2.1 hE.left_dvd
  · apply dvd_trans ?_ hE.right_dvd
    rcases hsource.2.2.2 with ⟨k, hk⟩
    refine ⟨k, ?_⟩
    simp only [pow_succ]
    rw [hk]
    ring

/-- Conjugating an output factor leaves its local coefficient-flow certificate
unchanged. -/
lemma conjugate
    {p : ℕ}
    {w : CWord HPAtom}
    {c : ℤ}
    {G : Type*} [Group G]
    {E : RFactor G}
    (hE : RCFlow p w c E)
    (q : G) :
    RCFlow p w c (E.conjugate q) := by
  exact ⟨hE.target_positive, hE.left_dvd, hE.right_dvd⟩

/-- Negating both the source multiplicity and an output factor multiplicity
preserves coefficient flow.  This is the local arithmetic input for reducing
integer multiplicities to natural multiplicities. -/
lemma inv
    {p : ℕ}
    {w : CWord HPAtom}
    {c : ℤ}
    {G : Type*} [Group G]
    {E : RFactor G}
    (hE : RCFlow p w c E) :
    RCFlow p w (-c) E.inv := by
  refine ⟨hE.target_positive, ?_, ?_⟩
  · simpa [RFactor.inv] using hE.left_dvd
  · simpa [RFactor.inv] using hE.right_dvd

/-- Pointwise coefficient flow implies the upgraded Hall-Petresco invariant on
an entire collected list. -/
lemma forall_good
    {p a b : ℕ}
    {w : CWord HPAtom}
    {c : ℤ}
    {G : Type*} [Group G]
    {L : List (RFactor G)}
    (hsource : HPGood p a b w c)
    (hL : ∀ E ∈ L, RCFlow p w c E) :
    ∀ E ∈ L, E.Good p a (b + 1) := by
  intro E hE
  exact (hL E hE).good hsource

/-- Conjugating every output factor preserves pointwise coefficient flow. -/
lemma forall_listConjugate
    {p : ℕ}
    {w : CWord HPAtom}
    {c : ℤ}
    {G : Type*} [Group G]
    {L : List (RFactor G)}
    (hL : ∀ E ∈ L, RCFlow p w c E)
    (q : G) :
    ∀ E ∈ listConjugate q L, RCFlow p w c E := by
  intro E hE
  rcases List.mem_map.mp hE with ⟨D, hD, rfl⟩
  exact (hL D hD).conjugate q

/-- Reversing and inverting a collection negates its source multiplicity while
preserving pointwise coefficient flow. -/
lemma forall_listInv
    {p : ℕ}
    {w : CWord HPAtom}
    {c : ℤ}
    {G : Type*} [Group G]
    {L : List (RFactor G)}
    (hL : ∀ E ∈ L, RCFlow p w c E) :
    ∀ E ∈ listInv L, RCFlow p w (-c) E := by
  intro E hE
  induction L with
  | nil =>
      change E ∈ ([] : List (RFactor G)) at hE
      contradiction
  | cons D L ih =>
      change E ∈ listInv L ++ [D.inv] at hE
      rw [List.mem_append, List.mem_singleton] at hE
      rcases hE with hE | hE
      · exact ih (fun Z hZ => hL Z (by simp [hZ])) hE
      · subst E
        exact (hL D (by simp)).inv

end RCFlow

/--
A normalized local right-prime collection.

The source is a bare powered Hall word rather than a `RFactor`: arbitrary
outer conjugation is deliberately absent.  The semantic group identity and the
local coefficient-flow invariant are recorded separately so later arithmetic
transport does not inspect the collection procedure.
-/
structure RCColl
    (p : ℕ)
    {G : Type*} [Group G]
    (x y : G)
    (w : CWord HPAtom)
    (c : ℤ) where
  factors :
    List (RFactor G)
  eval_eq :
    listEval x y factors =
      w.eval (HPAtom.eval x (y ^ p)) ^ c
  factors_flow :
    ∀ E ∈ factors, RCFlow p w c E

namespace RCColl

/-- The semantic equality carried by a normalized local collection. -/
lemma eval_factors
    {p : ℕ}
    {G : Type*} [Group G]
    {x y : G}
    {w : CWord HPAtom}
    {c : ℤ}
    (C : RCColl p x y w c) :
    listEval x y C.factors =
      w.eval (HPAtom.eval x (y ^ p)) ^ c :=
  C.eval_eq

/-- The pointwise local coefficient certificate carried by a normalized
collection. -/
lemma factor_flow
    {p : ℕ}
    {G : Type*} [Group G]
    {x y : G}
    {w : CWord HPAtom}
    {c : ℤ}
    {E : RFactor G}
    (C : RCColl p x y w c)
    (hE : E ∈ C.factors) :
    RCFlow p w c E :=
  C.factors_flow E hE

/-- Multiplicity zero has the empty normalized collection. -/
def zero
    (p : ℕ)
    {G : Type*} [Group G]
    (x y : G)
    (w : CWord HPAtom) :
    RCColl p x y w 0 where
  factors := []
  eval_eq := by
    simp
  factors_flow := by
    simp

/-- Invert a normalized collection.  This discharges negative integral
multiplicities once positive natural multiplicities have been collected. -/
def neg
    {p : ℕ}
    {G : Type*} [Group G]
    {x y : G}
    {w : CWord HPAtom}
    {c : ℤ}
    (C : RCColl p x y w c) :
    RCColl p x y w (-c) where
  factors := listInv C.factors
  eval_eq := by
    rw [list_eval_inv, C.eval_eq]
    simp
  factors_flow :=
    RCFlow.forall_listInv C.factors_flow

/-!
### Successor-kernel decomposition

The normalized successor step has two independent responsibilities:

* produce a finite raw-factor list with the required group evaluation;
* certify the four scalar facts needed for local coefficient flow on every
  output factor.

The structural recursion driver is implemented below using marked right-power
occurrences and a well-founded `markCount` descent.  Its remaining primitive
is one local Hall rewrite under an explicit commutator-word context.  The
declarations here package the resolved frontier for the rest of the
Hall-Petresco argument.
-/

/-- Positivity data for one output factor of the normalized successor
collector.  Keeping the two coordinates separate matches the recursive
Hall-word cases: a future collector proof may establish them independently. -/
structure SPCert
    {G : Type*} [Group G]
    (E : RFactor G) :
    Prop where
  left_degree_pos :
    0 < E.word.pairLeftDegree
  right_degree_pos :
    0 < E.word.pairRightDegree

namespace SPCert

/-- Repackage coordinatewise positivity as the bidegree predicate used by
`RCFlow`. -/
lemma pairBidegreePositive
    {G : Type*} [Group G]
    {E : RFactor G}
    (hE : SPCert E) :
    E.word.PBPos :=
  ⟨hE.left_degree_pos, hE.right_degree_pos⟩

/-- The left coordinate of a successor-factor positivity certificate. -/
lemma left
    {G : Type*} [Group G]
    {E : RFactor G}
    (hE : SPCert E) :
    0 < E.word.pairLeftDegree :=
  hE.left_degree_pos

/-- The right coordinate of a successor-factor positivity certificate. -/
lemma right
    {G : Type*} [Group G]
    {E : RFactor G}
    (hE : SPCert E) :
    0 < E.word.pairRightDegree :=
  hE.right_degree_pos

end SPCert

/-- Divisibility data for one output factor of a normalized successor
collection.

The source multiplicity is the new natural multiplicity `n + 1`.  The left
coordinate is inherited unchanged, while the right coordinate has gained the
single prime factor introduced by substituting `y ^ p` for the right atom. -/
structure SDCerta
    (p : ℕ)
    (w : CWord HPAtom)
    (n : ℕ)
    {G : Type*} [Group G]
    (E : RFactor G) :
    Prop where
  left_dvd :
    (w.pairLeftDegree : ℤ) * ((n + 1 : ℕ) : ℤ) ∣
      (E.word.pairLeftDegree : ℤ) * E.multiplicity
  right_dvd :
    (p : ℤ) * ((w.pairRightDegree : ℤ) * ((n + 1 : ℕ) : ℤ)) ∣
      (E.word.pairRightDegree : ℤ) * E.multiplicity

namespace SDCerta

/-- The unchanged left-coordinate divisibility produced by the successor
collector. -/
lemma left
    {p : ℕ}
    {w : CWord HPAtom}
    {n : ℕ}
    {G : Type*} [Group G]
    {E : RFactor G}
    (hE : SDCerta p w n E) :
    (w.pairLeftDegree : ℤ) * ((n + 1 : ℕ) : ℤ) ∣
      (E.word.pairLeftDegree : ℤ) * E.multiplicity :=
  hE.left_dvd

/-- The strengthened right-coordinate divisibility produced by the successor
collector. -/
lemma right
    {p : ℕ}
    {w : CWord HPAtom}
    {n : ℕ}
    {G : Type*} [Group G]
    {E : RFactor G}
    (hE : SDCerta p w n E) :
    (p : ℤ) * ((w.pairRightDegree : ℤ) * ((n + 1 : ℕ) : ℤ)) ∣
      (E.word.pairRightDegree : ℤ) * E.multiplicity :=
  hE.right_dvd

end SDCerta

/-- The complete scalar certificate for one output factor of the normalized
successor collector.

This structure deliberately contains no group-evaluation statement and no
list traversal.  It is the pointwise arithmetic leaf from which local
coefficient flow is assembled. -/
structure NSCert
    (p : ℕ)
    (w : CWord HPAtom)
    (n : ℕ)
    {G : Type*} [Group G]
    (E : RFactor G) :
    Prop where
  positivity :
    SPCert E
  divisibility :
    SDCerta p w n E

namespace NSCert

/-- The positive target bidegree carried by one successor-factor
certificate. -/
lemma target_positive
    {p : ℕ}
    {w : CWord HPAtom}
    {n : ℕ}
    {G : Type*} [Group G]
    {E : RFactor G}
    (hE : NSCert p w n E) :
    E.word.PBPos :=
  hE.positivity.pairBidegreePositive

/-- The inherited left divisibility carried by one successor-factor
certificate. -/
lemma left_dvd
    {p : ℕ}
    {w : CWord HPAtom}
    {n : ℕ}
    {G : Type*} [Group G]
    {E : RFactor G}
    (hE : NSCert p w n E) :
    (w.pairLeftDegree : ℤ) * ((n + 1 : ℕ) : ℤ) ∣
      (E.word.pairLeftDegree : ℤ) * E.multiplicity :=
  hE.divisibility.left

/-- The new right-prime divisibility carried by one successor-factor
certificate. -/
lemma right_dvd
    {p : ℕ}
    {w : CWord HPAtom}
    {n : ℕ}
    {G : Type*} [Group G]
    {E : RFactor G}
    (hE : NSCert p w n E) :
    (p : ℤ) * ((w.pairRightDegree : ℤ) * ((n + 1 : ℕ) : ℤ)) ∣
      (E.word.pairRightDegree : ℤ) * E.multiplicity :=
  hE.divisibility.right

/-- Convert the four scalar successor facts into the local coefficient-flow
predicate consumed by the Hall-Petresco arithmetic composition layer. -/
lemma coefficientFlow
    {p : ℕ}
    {w : CWord HPAtom}
    {n : ℕ}
    {G : Type*} [Group G]
    {E : RFactor G}
    (hE : NSCert p w n E) :
    RCFlow p w ((n + 1 : ℕ) : ℤ) E :=
  ⟨hE.target_positive, hE.left_dvd, hE.right_dvd⟩

/-- Transporting a factor through a group homomorphism preserves its four
successor-certificate fields.  Only the outer conjugator changes. -/
lemma mapHom
    {p : ℕ}
    {w : CWord HPAtom}
    {n : ℕ}
    {G H : Type*} [Group G] [Group H]
    {E : RFactor G}
    (hE : NSCert p w n E)
    (φ : G →* H) :
    NSCert p w n (E.mapHom φ) := by
  exact {
    positivity := {
      left_degree_pos :=
        hE.positivity.left_degree_pos
      right_degree_pos :=
        hE.positivity.right_degree_pos }
    divisibility := {
      left_dvd :=
        hE.divisibility.left_dvd
      right_dvd :=
        hE.divisibility.right_dvd } }

end NSCert

/-- Pointwise successor certificates for an entire collected list.

This layer performs no Hall collection itself.  It only packages the finite
list traversal needed when a pointwise recursive proof has been completed. -/
structure RSCertb
    (p : ℕ)
    (w : CWord HPAtom)
    (n : ℕ)
    {G : Type*} [Group G]
    (L : List (RFactor G)) :
    Prop where
  factor_certificate :
    ∀ E ∈ L, NSCert p w n E

namespace RSCertb

/-- Read the successor certificate for one member of a certified list. -/
lemma factor
    {p : ℕ}
    {w : CWord HPAtom}
    {n : ℕ}
    {G : Type*} [Group G]
    {L : List (RFactor G)}
    (hL : RSCertb p w n L)
    {E : RFactor G}
    (hE : E ∈ L) :
    NSCert p w n E :=
  hL.factor_certificate E hE

/-- Every member of a certified successor list has positive left degree. -/
lemma leftDegree_pos
    {p : ℕ}
    {w : CWord HPAtom}
    {n : ℕ}
    {G : Type*} [Group G]
    {L : List (RFactor G)}
    (hL : RSCertb p w n L) :
    ∀ E ∈ L, 0 < E.word.pairLeftDegree := by
  intro E hE
  exact (hL.factor hE).positivity.left

/-- Every member of a certified successor list has positive right degree. -/
lemma rightDegree_pos
    {p : ℕ}
    {w : CWord HPAtom}
    {n : ℕ}
    {G : Type*} [Group G]
    {L : List (RFactor G)}
    (hL : RSCertb p w n L) :
    ∀ E ∈ L, 0 < E.word.pairRightDegree := by
  intro E hE
  exact (hL.factor hE).positivity.right

/-- Every member of a certified successor list inherits left-coordinate
divisibility. -/
lemma forall_left_dvd
    {p : ℕ}
    {w : CWord HPAtom}
    {n : ℕ}
    {G : Type*} [Group G]
    {L : List (RFactor G)}
    (hL : RSCertb p w n L) :
    ∀ E ∈ L,
      (w.pairLeftDegree : ℤ) * ((n + 1 : ℕ) : ℤ) ∣
        (E.word.pairLeftDegree : ℤ) * E.multiplicity := by
  intro E hE
  exact (hL.factor hE).left_dvd

/-- Every member of a certified successor list gains right-coordinate
divisibility by `p`. -/
lemma forall_right_dvd
    {p : ℕ}
    {w : CWord HPAtom}
    {n : ℕ}
    {G : Type*} [Group G]
    {L : List (RFactor G)}
    (hL : RSCertb p w n L) :
    ∀ E ∈ L,
      (p : ℤ) * ((w.pairRightDegree : ℤ) * ((n + 1 : ℕ) : ℤ)) ∣
        (E.word.pairRightDegree : ℤ) * E.multiplicity := by
  intro E hE
  exact (hL.factor hE).right_dvd

/-- A certified successor list satisfies coefficient flow pointwise. -/
lemma forall_coefficientFlow
    {p : ℕ}
    {w : CWord HPAtom}
    {n : ℕ}
    {G : Type*} [Group G]
    {L : List (RFactor G)}
    (hL : RSCertb p w n L) :
    ∀ E ∈ L, RCFlow p w ((n + 1 : ℕ) : ℤ) E := by
  intro E hE
  exact (hL.factor hE).coefficientFlow

/-- Transport an exact list certificate through a group homomorphism.
The destination list is the image of the certified source list in its
original order. -/
lemma mapHom
    {p : ℕ}
    {w : CWord HPAtom}
    {n : ℕ}
    {G H : Type*} [Group G] [Group H]
    {L : List (RFactor G)}
    (hL : RSCertb p w n L)
    (φ : G →* H) :
    RSCertb p w n (RFactor.listMapHom φ L) := by
  refine ⟨?_⟩
  intro E hE
  rcases List.mem_map.mp hE with ⟨D, hD, rfl⟩
  exact (hL.factor hD).mapHom φ

end RSCertb

/-- Output of one normalized natural-successor collection step.

The semantic equality and the scalar list certificate are separated so that
future recursive Hall collection work can prove them by different inductions
while the public `RCColl` interface remains compact. -/
structure NSKern
    (p : ℕ)
    {G : Type*} [Group G]
    (x y : G)
    (w : CWord HPAtom)
    (n : ℕ) where
  factors :
    List (RFactor G)
  eval_eq :
    listEval x y factors =
      w.eval (HPAtom.eval x (y ^ p)) ^ ((n + 1 : ℕ) : ℤ)
  factors_certificate :
    RSCertb p w n factors

namespace NSKern

/-- The semantic equality carried by a normalized successor kernel. -/
lemma eval_factors
    {p : ℕ}
    {G : Type*} [Group G]
    {x y : G}
    {w : CWord HPAtom}
    {n : ℕ}
    (K : NSKern p x y w n) :
    listEval x y K.factors =
      w.eval (HPAtom.eval x (y ^ p)) ^ ((n + 1 : ℕ) : ℤ) :=
  K.eval_eq

/-- The scalar certificate for one factor produced by a successor kernel. -/
lemma factor_certificate
    {p : ℕ}
    {G : Type*} [Group G]
    {x y : G}
    {w : CWord HPAtom}
    {n : ℕ}
    (K : NSKern p x y w n)
    {E : RFactor G}
    (hE : E ∈ K.factors) :
    NSCert p w n E :=
  K.factors_certificate.factor hE

/-- Every factor produced by a successor kernel has positive left degree. -/
lemma factor_left_pos
    {p : ℕ}
    {G : Type*} [Group G]
    {x y : G}
    {w : CWord HPAtom}
    {n : ℕ}
    (K : NSKern p x y w n) :
    ∀ E ∈ K.factors, 0 < E.word.pairLeftDegree :=
  K.factors_certificate.leftDegree_pos

/-- Every factor produced by a successor kernel has positive right degree. -/
lemma factor_degree_pos
    {p : ℕ}
    {G : Type*} [Group G]
    {x y : G}
    {w : CWord HPAtom}
    {n : ℕ}
    (K : NSKern p x y w n) :
    ∀ E ∈ K.factors, 0 < E.word.pairRightDegree :=
  K.factors_certificate.rightDegree_pos

/-- Every factor produced by a successor kernel inherits left-coordinate
divisibility. -/
lemma factor_left_dvd
    {p : ℕ}
    {G : Type*} [Group G]
    {x y : G}
    {w : CWord HPAtom}
    {n : ℕ}
    (K : NSKern p x y w n) :
    ∀ E ∈ K.factors,
      (w.pairLeftDegree : ℤ) * ((n + 1 : ℕ) : ℤ) ∣
        (E.word.pairLeftDegree : ℤ) * E.multiplicity :=
  K.factors_certificate.forall_left_dvd

/-- Every factor produced by a successor kernel gains right-coordinate
divisibility by `p`. -/
lemma factor_right_dvd
    {p : ℕ}
    {G : Type*} [Group G]
    {x y : G}
    {w : CWord HPAtom}
    {n : ℕ}
    (K : NSKern p x y w n) :
    ∀ E ∈ K.factors,
      (p : ℤ) * ((w.pairRightDegree : ℤ) * ((n + 1 : ℕ) : ℤ)) ∣
        (E.word.pairRightDegree : ℤ) * E.multiplicity :=
  K.factors_certificate.forall_right_dvd

/-- Every factor produced by a successor kernel satisfies local coefficient
flow for the new multiplicity. -/
lemma factor_flow
    {p : ℕ}
    {G : Type*} [Group G]
    {x y : G}
    {w : CWord HPAtom}
    {n : ℕ}
    (K : NSKern p x y w n) :
    ∀ E ∈ K.factors,
      RCFlow p w ((n + 1 : ℕ) : ℤ) E :=
  K.factors_certificate.forall_coefficientFlow

/-- Forget the internal decomposition and expose the public normalized
collection interface. -/
def toCoreCollection
    {p : ℕ}
    {G : Type*} [Group G]
    {x y : G}
    {w : CWord HPAtom}
    {n : ℕ}
    (K : NSKern p x y w n) :
    RCColl p x y w ((n + 1 : ℕ) : ℤ) where
  factors := K.factors
  eval_eq := K.eval_eq
  factors_flow := K.factor_flow

/-- A successor kernel supplies a normalized successor collection. -/
lemma nonempty_coreCollection
    {p : ℕ}
    {G : Type*} [Group G]
    {x y : G}
    {w : CWord HPAtom}
    {n : ℕ}
    (K : NSKern p x y w n) :
    Nonempty (RCColl p x y w ((n + 1 : ℕ) : ℤ)) :=
  ⟨K.toCoreCollection⟩

end NSKern

/-!
### Structural marked-power collector

The public successor kernel above is assembled from a genuinely recursive
collector below.  A marked word records precisely which occurrences of the
right Hall-pair atom still stand for `y ^ p`.  One local rewrite expands one
marked occurrence under an explicit commutator context.  Every pending branch
returned by that rewrite has strictly fewer marks, so recursive resolution is
well-founded on `markCount`.

Only the one-occurrence rewrite remains admitted.  List traversal, flow
composition, terminal erasure, recursive frontier resolution, and the initial
marked-word construction are implemented here.
-/

/-- Coefficient flow composes through an intermediate factor.

Each local marked-power rewrite contributes at least one right-prime factor.
Following a pending branch through more rewrites may contribute additional
prime factors; the public interface only needs the first one. -/
lemma coefficientFlow_trans
    {p : ℕ}
    {u : CWord HPAtom}
    {c : ℤ}
    {G : Type*} [Group G]
    {D E : RFactor G}
    (hD : RCFlow p u c D)
    (hE : RCFlow p D.word D.multiplicity E) :
    RCFlow p u c E := by
  refine ⟨hE.target_positive, dvd_trans hD.left_dvd hE.left_dvd, ?_⟩
  apply dvd_trans hD.right_dvd
  apply dvd_trans (dvd_mul_left _ (p : ℤ))
  exact hE.right_dvd

/-- A Hall-pair commutator word with explicit markers for right atoms that
still denote `y ^ p`.

Ordinary right atoms may also occur: local rewriting removes markers while
retaining the unpowered Hall-pair alphabet used by final `RFactor`s. -/
inductive RMWord where
  | atom : HPAtom → RMWord
  | markedRight : RMWord
  | commutator : RMWord → RMWord →
      RMWord

namespace RMWord

/-- Forget which right atoms are still marked. -/
def erase : RMWord → CWord HPAtom
  | .atom a => .atom a
  | .markedRight => .atom .right
  | .commutator u v => .commutator u.erase v.erase

/-- Evaluate a marked word, interpreting each remaining marker as `y ^ p`. -/
def eval
    {G : Type*} [Group G]
    (x y : G)
    (p : ℕ) :
    RMWord → G
  | .atom .left => x
  | .atom .right => y
  | .markedRight => y ^ p
  | .commutator u v => ⁅u.eval x y p, v.eval x y p⁆

/-- Number of right-power markers still requiring local Hall collection. -/
def markCount : RMWord → ℕ
  | .atom _ => 0
  | .markedRight => 1
  | .commutator u v => u.markCount + v.markCount

/-- Number of ordinary, already-unpowered right atoms in a marked word. -/
def ordinaryRightDegree : RMWord → ℕ
  | .atom .left => 0
  | .atom .right => 1
  | .markedRight => 0
  | .commutator u v => u.ordinaryRightDegree + v.ordinaryRightDegree

/-- Effective right degree of a pending word.  Ordinary right atoms count once,
while markers still interpreted as `y ^ p` count with a factor of `p`. -/
def weightedRightDegree (p : ℕ) (u : RMWord) : ℕ :=
  u.ordinaryRightDegree + p * u.markCount

/-- Replace every right atom in an ordinary Hall-pair word by a marked right
power. -/
def markRight : CWord HPAtom → RMWord
  | .atom .left => .atom .left
  | .atom .right => .markedRight
  | .commutator u v => .commutator (markRight u) (markRight v)

@[simp]
lemma erase_atom
    (a : HPAtom) :
    (atom a).erase = .atom a :=
  rfl

@[simp]
lemma erase_markedRight :
    markedRight.erase = .atom .right :=
  rfl

@[simp]
lemma erase_commutator
    (u v : RMWord) :
    (commutator u v).erase = .commutator u.erase v.erase :=
  rfl

@[simp]
lemma markCount_atom
    (a : HPAtom) :
    (atom a).markCount = 0 :=
  rfl

@[simp]
lemma mark_count_marked :
    markedRight.markCount = 1 :=
  rfl

@[simp]
lemma markCount_commutator
    (u v : RMWord) :
    (commutator u v).markCount = u.markCount + v.markCount :=
  rfl

@[simp]
lemma ordinary_degree_atom
    (a : HPAtom) :
    (atom a).ordinaryRightDegree =
      match a with
      | .left => 0
      | .right => 1 :=
  by cases a <;> rfl

@[simp]
lemma ordinary_degree_marked :
    markedRight.ordinaryRightDegree = 0 :=
  rfl

@[simp]
lemma ordinary_degree_commutator
    (u v : RMWord) :
    (commutator u v).ordinaryRightDegree =
      u.ordinaryRightDegree + v.ordinaryRightDegree :=
  rfl

@[simp]
lemma erase_markRight :
    ∀ w : CWord HPAtom, (markRight w).erase = w
  | .atom .left => rfl
  | .atom .right => rfl
  | .commutator u v => by
      simp [markRight, erase_markRight u, erase_markRight v]

@[simp]
lemma mark_count_right :
    ∀ w : CWord HPAtom,
      (markRight w).markCount = w.pairRightDegree
  | .atom .left => rfl
  | .atom .right => rfl
  | .commutator u v => by
      simp [markRight, mark_count_right u, mark_count_right v]

@[simp]
lemma ordinary_degree_mark :
    ∀ w : CWord HPAtom,
      (markRight w).ordinaryRightDegree = 0
  | .atom .left => rfl
  | .atom .right => rfl
  | .commutator u v => by
      simp [markRight, ordinary_degree_mark u,
        ordinary_degree_mark v]

@[simp]
lemma weighted_degree_mark
    (p : ℕ)
    (w : CWord HPAtom) :
    (markRight w).weightedRightDegree p = p * w.pairRightDegree := by
  simp [weightedRightDegree]

@[simp]
lemma pair_degree_erase :
    ∀ u : RMWord,
      u.erase.pairRightDegree = u.ordinaryRightDegree + u.markCount
  | .atom .left => rfl
  | .atom .right => rfl
  | .markedRight => rfl
  | .commutator u v => by
      simp only [erase_commutator, CWord.pair_degree_commutator,
        ordinary_degree_commutator, markCount_commutator,
        pair_degree_erase u, pair_degree_erase v]
      omega

/-- Without markers, weighted right degree is the ordinary right degree of the
erased word. -/
lemma weighted_erase_mark
    (p : ℕ)
    (u : RMWord)
    (hzero : u.markCount = 0) :
    u.weightedRightDegree p = u.erase.pairRightDegree := by
  rw [pair_degree_erase]
  simp [weightedRightDegree, hzero]

@[simp]
lemma eval_markRight
    {G : Type*} [Group G]
    (x y : G)
    (p : ℕ) :
    ∀ w : CWord HPAtom,
      (markRight w).eval x y p =
        w.eval (HPAtom.eval x (y ^ p))
  | .atom .left => rfl
  | .atom .right => rfl
  | .commutator u v => by
      simp [markRight, eval, eval_markRight x y p u,
        eval_markRight x y p v]

/-- Once no markers remain, marked evaluation agrees with ordinary
Hall-pair evaluation of the erased word. -/
lemma erase_mark_count
    {G : Type*} [Group G]
    (x y : G)
    (p : ℕ) :
    ∀ u : RMWord,
      u.markCount = 0 →
        u.eval x y p = u.erase.eval (HPAtom.eval x y)
  | .atom .left, _ => rfl
  | .atom .right, _ => rfl
  | .markedRight, h => by
      simp at h
  | .commutator u v, h => by
      have hu : u.markCount = 0 := by
        simp only [markCount_commutator] at h
        omega
      have hv : v.markCount = 0 := by
        simp only [markCount_commutator] at h
        omega
      simp [eval, erase,
        erase_mark_count x y p u hu,
        erase_mark_count x y p v hv]

end RMWord

/-- A one-hole marked commutator-word context.  The local Hall rewrite below
is parameterized by the path to the selected marked right atom. -/
inductive RMContex where
  | hole : RMContex
  | commutatorLeft :
      RMContex → RMWord →
        RMContex
  | commutatorRight :
      RMWord → RMContex →
        RMContex

namespace RMContex

/-- Fill the unique hole in a marked commutator-word context. -/
def plug :
    RMContex → RMWord → RMWord
  | .hole, u => u
  | .commutatorLeft K v, u => .commutator (K.plug u) v
  | .commutatorRight u K, v => .commutator u (K.plug v)

@[simp]
lemma plug_hole
    (u : RMWord) :
    hole.plug u = u :=
  rfl

@[simp]
lemma plug_commutatorLeft
    (K : RMContex)
    (u v : RMWord) :
    (commutatorLeft K v).plug u = .commutator (K.plug u) v :=
  rfl

@[simp]
lemma plug_commutatorRight
    (K : RMContex)
    (u v : RMWord) :
    (commutatorRight u K).plug v = .commutator u (K.plug v) :=
  rfl

end RMContex

namespace RMWord

/-- A positive marker count exposes an actual marked-right occurrence under a
concrete one-hole commutator context. -/
lemma plug_marked_mark :
    ∀ u : RMWord,
      0 < u.markCount →
        ∃ K : RMContex,
          u = K.plug .markedRight
  | .atom _, h => by
      simp at h
  | .markedRight, _ =>
      ⟨.hole, rfl⟩
  | .commutator u v, h => by
      by_cases hu : 0 < u.markCount
      · rcases
          plug_marked_mark u hu with
          ⟨K, hK⟩
        exact ⟨.commutatorLeft K v, by simp [hK]⟩
      · have hv : 0 < v.markCount := by
          simp only [markCount_commutator] at h
          omega
        rcases
          plug_marked_mark v hv with
          ⟨K, hK⟩
        exact ⟨.commutatorRight u K, by simp [hK]⟩

end RMWord

/-- A conjugated integral multiple of a marked Hall-pair commutator word. -/
structure RMFactor
    (G : Type*) [Group G] where
  word :
    RMWord
  multiplicity :
    ℤ
  conjugator :
    G

namespace RMFactor

/-- Forget the right-power markers in a pending factor. -/
def erase
    {G : Type*} [Group G]
    (F : RMFactor G) :
    RFactor G where
  word := F.word.erase
  multiplicity := F.multiplicity
  conjugator := F.conjugator

/-- Evaluate a pending factor while its markers still denote `y ^ p`. -/
def eval
    {G : Type*} [Group G]
    (p : ℕ)
    (x y : G)
    (F : RMFactor G) :
    G :=
  F.conjugator * F.word.eval x y p ^ F.multiplicity * F.conjugator⁻¹

/-- A marker-free pending factor evaluates exactly as its erased raw factor. -/
lemma erase_mark_count
    {G : Type*} [Group G]
    (p : ℕ)
    (x y : G)
    (F : RMFactor G)
    (hF : F.word.markCount = 0) :
    F.eval p x y = F.erase.eval x y := by
  simp [eval, erase, RFactor.eval,
    RMWord.erase_mark_count x y p F.word hF]

/-- Initial marked factor for collecting one powered Hall word after the
right-prime substitution. -/
def initial
    {G : Type*} [Group G]
    (w : CWord HPAtom)
  (c : ℤ) :
    RMFactor G where
  word := RMWord.markRight w
  multiplicity := c
  conjugator := 1

@[simp]
lemma erase_initial
    {G : Type*} [Group G]
    (w : CWord HPAtom)
    (c : ℤ) :
    (initial (G := G) w c).erase =
      { word := w, multiplicity := c, conjugator := 1 } := by
  simp [initial, erase]

@[simp]
lemma markCount_initial
    {G : Type*} [Group G]
    (w : CWord HPAtom)
    (c : ℤ) :
    (initial (G := G) w c).word.markCount =
      w.pairRightDegree := by
  simp [initial]

@[simp]
lemma eval_initial
    {G : Type*} [Group G]
    (p : ℕ)
    (x y : G)
    (w : CWord HPAtom)
    (c : ℤ) :
    (initial (G := G) w c).eval p x y =
      w.eval (HPAtom.eval x (y ^ p)) ^ c := by
  simp [initial, eval]

end RMFactor

/-- Coefficient flow for a branch that still contains marked right powers.

The target's right degree is weighted according to its current semantics:
ordinary right atoms contribute once, while each remaining marker contributes
`p` because it still evaluates to `y ^ p`. -/
structure PCFlow
    (p : ℕ)
    {G : Type*} [Group G]
    (root : RFactor G)
    (F : RMFactor G) :
    Prop where
  target_positive :
    F.erase.word.PBPos
  left_dvd :
    (root.word.pairLeftDegree : ℤ) * root.multiplicity ∣
      (F.erase.word.pairLeftDegree : ℤ) * F.multiplicity
  right_dvd :
    (p : ℤ) * ((root.word.pairRightDegree : ℤ) * root.multiplicity) ∣
      (F.word.weightedRightDegree p : ℤ) * F.multiplicity

namespace PCFlow

/-- Once a pending branch has no markers, its weighted certificate is exactly
the ordinary final coefficient-flow certificate. -/
lemma coefficient_flow_mark
    {p : ℕ}
    {G : Type*} [Group G]
    {root : RFactor G}
    {F : RMFactor G}
    (hF : PCFlow p root F)
    (hzero : F.word.markCount = 0) :
    RCFlow p root.word root.multiplicity F.erase := by
  refine ⟨hF.target_positive, hF.left_dvd, ?_⟩
  have hright := hF.right_dvd
  rw [RMWord.weighted_erase_mark
    p F.word hzero] at hright
  exact hright

/-- A fully marked initial factor has pending flow relative to its erased
source: every right occurrence contributes its initial factor of `p`. -/
lemma initial
    {p : ℕ}
    {G : Type*} [Group G]
    (w : CWord HPAtom)
    (c : ℤ)
    (hw : w.PBPos) :
    PCFlow p
      (RMFactor.initial (G := G) w c).erase
      (RMFactor.initial (G := G) w c) := by
  refine ⟨?_, dvd_refl _, ?_⟩
  · simpa using hw
  · simp [RMFactor.initial, RMFactor.erase, mul_assoc]

/-- Rebase pending flow along an already-established final coefficient-flow
edge. -/
lemma rebase
    {p : ℕ}
    {G : Type*} [Group G]
    {root source : RFactor G}
    {F : RMFactor G}
    (hF : PCFlow p source F)
    (hsource :
      RCFlow p root.word root.multiplicity source) :
    PCFlow p root F := by
  refine ⟨hF.target_positive, dvd_trans hsource.left_dvd hF.left_dvd, ?_⟩
  exact dvd_trans hsource.right_dvd
    (dvd_trans (dvd_mul_left _ (p : ℤ)) hF.right_dvd)

end PCFlow

/-- One entry in a local marked-power rewrite frontier.

An output factor is ready for the final raw list.  A pending factor still
contains marked right powers, and carries weighted pending flow from the
frontier root. -/
inductive RFEntry
    (p : ℕ)
    {G : Type*} [Group G]
    (root : RFactor G) where
  | output
      (factor : RFactor G)
      (flow :
        RCFlow p root.word root.multiplicity factor) :
      RFEntry p root
  | pending
      (factor : RMFactor G)
      (flow :
        PCFlow p root factor) :
      RFEntry p root

namespace RFEntry

/-- Evaluate one frontier entry, using ordinary evaluation for completed
outputs and marked evaluation for pending branches. -/
def eval
    {p : ℕ}
    {G : Type*} [Group G]
    {root : RFactor G}
    (x y : G) :
    RFEntry p root → G
  | .output E _ => E.eval x y
  | .pending F _ => F.eval p x y

/-- Rebase a frontier entry along already-established coefficient flow. -/
def rebase
    {p : ℕ}
    {G : Type*} [Group G]
    {root source : RFactor G}
    (hsource :
      RCFlow p root.word root.multiplicity source) :
    RFEntry p source →
      RFEntry p root
  | .output E hE => .output E (coefficientFlow_trans hsource hE)
  | .pending F hF => .pending F (hF.rebase hsource)

@[simp]
lemma eval_rebase
    {p : ℕ}
    {G : Type*} [Group G]
    {root source : RFactor G}
    (x y : G)
    (hsource :
      RCFlow p root.word root.multiplicity source)
    (E : RFEntry p source) :
    (E.rebase hsource).eval x y = E.eval x y := by
  cases E <;> rfl

/-- Evaluate a frontier list in collection order. -/
def listEval
    {p : ℕ}
    {G : Type*} [Group G]
    {root : RFactor G}
    (x y : G)
    (L : List (RFEntry p root)) :
    G :=
  (L.map (eval x y)).prod

@[simp]
lemma listEval_nil
    {p : ℕ}
    {G : Type*} [Group G]
    {root : RFactor G}
    (x y : G) :
    listEval x y ([] : List (RFEntry p root)) = 1 :=
  rfl

@[simp]
lemma listEval_cons
    {p : ℕ}
    {G : Type*} [Group G]
    {root : RFactor G}
    (x y : G)
    (E : RFEntry p root)
    (L : List (RFEntry p root)) :
    listEval x y (E :: L) = E.eval x y * listEval x y L :=
  rfl

/-- Pending marked factors contained in a frontier, in collection order. -/
def pendingFactors
    {p : ℕ}
    {G : Type*} [Group G]
    {root : RFactor G} :
    List (RFEntry p root) →
      List (RMFactor G)
  | [] => []
  | .output _ _ :: L => pendingFactors L
  | .pending F _ :: L => F :: pendingFactors L

/-- Rebase every entry of a frontier list. -/
def listRebase
    {p : ℕ}
    {G : Type*} [Group G]
    {root source : RFactor G}
    (hsource :
      RCFlow p root.word root.multiplicity source)
    (L : List (RFEntry p source)) :
    List (RFEntry p root) :=
  L.map (rebase hsource)

@[simp]
lemma list_eval_rebase
    {p : ℕ}
    {G : Type*} [Group G]
    {root source : RFactor G}
    (x y : G)
    (hsource :
      RCFlow p root.word root.multiplicity source)
    (L : List (RFEntry p source)) :
    listEval x y (listRebase hsource L) = listEval x y L := by
  induction L with
  | nil =>
      rfl
  | cons E L ih =>
      change
        (E.rebase hsource).eval x y *
            listEval x y (listRebase hsource L) =
          E.eval x y * listEval x y L
      rw [eval_rebase, ih]

@[simp]
lemma pending_factors_rebase
    {p : ℕ}
    {G : Type*} [Group G]
    {root source : RFactor G}
    (hsource :
      RCFlow p root.word root.multiplicity source)
    (L : List (RFEntry p source)) :
    pendingFactors (listRebase hsource L) = pendingFactors L := by
  induction L with
  | nil =>
      rfl
  | cons E L ih =>
      cases E with
      | output E hE =>
          simpa only [listRebase, List.map_cons, rebase, pendingFactors] using ih
      | pending F hF =>
          simpa only [listRebase, List.map_cons, rebase, pendingFactors] using
            congrArg (List.cons F) ih

/-- Membership in the pending-factor projection retains coefficient flow from
the frontier root. -/
lemma flow_pending_factors
    {p : ℕ}
    {G : Type*} [Group G]
    {root : RFactor G} :
    ∀ {L : List (RFEntry p root)}
      {F : RMFactor G},
      F ∈ pendingFactors L →
        PCFlow p root F
  | [], _, hF => by
      simp [pendingFactors] at hF
  | .output _ _ :: L, F, hF =>
      flow_pending_factors (by simpa [pendingFactors] using hF)
  | .pending D hD :: L, F, hF => by
      rw [pendingFactors, List.mem_cons] at hF
      rcases hF with rfl | hF
      · exact hD
      · exact flow_pending_factors hF

end RFEntry

/-- One structural marked-power rewrite.

The rewrite preserves evaluation, emits factors with flow from `root`, and
records a strict decrease in `markCount` for every pending branch. -/
structure RFExp
    (p : ℕ)
    {G : Type*} [Group G]
    (x y : G)
    (root : RFactor G)
    (F : RMFactor G) where
  entries :
    List (RFEntry p root)
  eval_eq :
    RFEntry.listEval x y entries = F.eval p x y
  pending_mark_count :
    ∀ D ∈ RFEntry.pendingFactors entries,
      D.word.markCount < F.word.markCount

/-- A local expansion starts with coefficient flow from the factor being
rewritten. -/
abbrev RightLocalExpansion
    (p : ℕ)
    {G : Type*} [Group G]
    (x y : G)
    (F : RMFactor G) :=
  RFExp p x y F.erase F

namespace RFExp

/-- Rebase a structural frontier after following a previously certified
pending edge. -/
def rebase
    {p : ℕ}
    {G : Type*} [Group G]
    {x y : G}
    {root source : RFactor G}
    {F : RMFactor G}
    (S : RFExp p x y source F)
    (hsource :
      RCFlow p root.word root.multiplicity source) :
    RFExp p x y root F where
  entries :=
    RFEntry.listRebase hsource S.entries
  eval_eq := by
    rw [RFEntry.list_eval_rebase, S.eval_eq]
  pending_mark_count := by
    intro D hD
    apply S.pending_mark_count D
    simpa using hD

end RFExp

/-- Resolution of one pending marked factor into final raw factors, all
certified relative to the original root factor. -/
structure RPResolu
    (p : ℕ)
    {G : Type*} [Group G]
    (x y : G)
    (root : RFactor G)
    (F : RMFactor G) where
  factors :
    List (RFactor G)
  eval_eq :
    listEval x y factors = F.eval p x y
  factors_flow :
    ∀ E ∈ factors,
      RCFlow p root.word root.multiplicity E

/-- Resolution of a whole structural frontier into final raw factors. -/
structure RFResolu
    (p : ℕ)
    {G : Type*} [Group G]
    (x y : G)
    (root : RFactor G)
    (L : List (RFEntry p root)) where
  factors :
    List (RFactor G)
  eval_eq :
    listEval x y factors = RFEntry.listEval x y L
  factors_flow :
    ∀ E ∈ factors,
      RCFlow p root.word root.multiplicity E

namespace RPResolu

/-- Erase a terminal pending factor once its marker count reaches zero. -/
def terminal
    {p : ℕ}
    {G : Type*} [Group G]
    (x y : G)
    (root : RFactor G)
    (F : RMFactor G)
    (hflow :
      PCFlow p root F)
    (hzero : F.word.markCount = 0) :
    RPResolu p x y root F where
  factors := [F.erase]
  eval_eq := by
    simp [F.erase_mark_count p x y hzero]
  factors_flow := by
    intro E hE
    simp only [List.mem_singleton] at hE
    subst E
    exact hflow.coefficient_flow_mark hzero

end RPResolu

namespace RFResolu

/-- Resolve the empty structural frontier. -/
def nil
    {p : ℕ}
    {G : Type*} [Group G]
    (x y : G)
    (root : RFactor G) :
    RFResolu p x y root [] where
  factors := []
  eval_eq := rfl
  factors_flow := by
    simp

/-- Prepend a completed output entry to a resolved tail. -/
def consOutput
    {p : ℕ}
    {G : Type*} [Group G]
    {x y : G}
    {root : RFactor G}
    (E : RFactor G)
    (hE :
      RCFlow p root.word root.multiplicity E)
    {L : List (RFEntry p root)}
    (R : RFResolu p x y root L) :
    RFResolu p x y root
      (.output E hE :: L) where
  factors := E :: R.factors
  eval_eq := by
    simp [R.eval_eq, RFEntry.eval]
  factors_flow := by
    intro D hD
    rw [List.mem_cons] at hD
    rcases hD with rfl | hD
    · exact hE
    · exact R.factors_flow D hD

/-- Prepend a recursively resolved pending entry to a resolved tail. -/
def consPending
    {p : ℕ}
    {G : Type*} [Group G]
    {x y : G}
    {root : RFactor G}
    (F : RMFactor G)
    (hF :
      PCFlow p root F)
    {L : List (RFEntry p root)}
    (RF : RPResolu p x y root F)
    (RL : RFResolu p x y root L) :
    RFResolu p x y root
      (.pending F hF :: L) where
  factors := RF.factors ++ RL.factors
  eval_eq := by
    rw [listEval_append, RF.eval_eq, RL.eval_eq]
    rfl
  factors_flow := by
    intro E hE
    rw [List.mem_append] at hE
    rcases hE with hE | hE
    · exact RF.factors_flow E hE
    · exact RL.factors_flow E hE

/-- Resolve a frontier list by structural recursion once each pending entry
has a recursive resolution. -/
def ofList
    {p : ℕ}
    {G : Type*} [Group G]
    (x y : G)
    (root : RFactor G) :
    (L : List (RFEntry p root)) →
      (∀ F ∈ RFEntry.pendingFactors L,
        RPResolu p x y root F) →
      RFResolu p x y root L
  | [], _ =>
      nil x y root
  | .output E hE :: L, solve => by
      apply consOutput E hE
      apply ofList x y root L
      intro F hF
      exact solve F (by simpa [RFEntry.pendingFactors] using hF)
  | .pending F hF :: L, solve => by
      apply consPending F hF
      · exact solve F (by simp [RFEntry.pendingFactors])
      · apply ofList x y root L
        intro D hD
        exact solve D (by simp [RFEntry.pendingFactors, hD])

end RFResolu

namespace RFExp

/-- Resolve a structural expansion once every strictly smaller pending branch
has been recursively resolved. -/
def resolve
    {p : ℕ}
    {G : Type*} [Group G]
    {x y : G}
    {root : RFactor G}
    {F : RMFactor G}
    (S : RFExp p x y root F)
    (solve :
      ∀ D ∈ RFEntry.pendingFactors S.entries,
        RPResolu p x y root D) :
    RPResolu p x y root F := by
  let R :=
    RFResolu.ofList x y root S.entries solve
  exact {
    factors := R.factors
    eval_eq := by
      rw [R.eval_eq, S.eval_eq]
    factors_flow := R.factors_flow }

end RFExp

namespace RPAggreg

/-!
### Aggregate Hall frontier

The selected-marker recursion is intentionally not used below.  A first Hall
collection pass may produce a marker-free pairwise error whose weighted degree
has not yet reached the final cutoff.  Such an error is neither a completed
raw output nor a recursively marked child.

The aggregate interface records those errors explicitly.  It reuses
`WCFactor.PERaw` from
`HallRecursiveCollection`: each pending factor remembers its substituted
pairwise-error origin, and recursive refinement is measured by
`cutoff - word.weight`.
-/

/-- Hall-pair weights for one right-prime substitution.  The left atom keeps
weight one and the substituted right atom receives weight `p`. -/
def weight
    (p : ℕ) :
    HPAtom → ℕ :=
  HPAtom.weight 1 p

/-- Both aggregate Hall-pair weights are positive at a prime. -/
lemma weight_pos
    {p : ℕ} [Fact p.Prime] :
    ∀ a : HPAtom, 0 < weight p a := by
  intro a
  cases a <;> simp [weight, HPAtom.weight, (Fact.out : Nat.Prime p).pos]

/-- Aggregate weighted degree of one ordinary Hall-pair word. -/
def wordWeight
    (p : ℕ)
    (w : CWord HPAtom) :
    ℕ :=
  w.weight (weight p)

/-- The natural aggregate cutoff attached to one ordinary Hall-pair word. -/
def cutoff
    (p : ℕ)
    (w : CWord HPAtom) :
    ℕ :=
  wordWeight p w

/-- A cutoff-zero factor retained for another aggregate Hall pass. -/
abbrev PendingFactor
    (p : ℕ)
    {G : Type*} [Group G]
    (x y : G) :=
  WCFactor p
    (HPAtom.eval x y)
    (weight p)
    0

/-- A weighted factor already admitted at the aggregate cutoff. -/
abbrev AdmittedFactor
    (p : ℕ)
    {G : Type*} [Group G]
    (x y : G)
    (cutoff : ℕ) :=
  WCFactor p
    (HPAtom.eval x y)
    (weight p)
    cutoff

/-- Extract an explicit pending-factor list from the imported pairwise-error
normal closure.  Every list entry keeps its exact pairwise-error origin. -/
lemma pending_factor_list
    {p : ℕ}
    {G : Type*} [Group G]
    {x y : G}
    {u v : CWord HPAtom}
    {g : G}
    (hg :
      g ∈
        iteratedPairwiseComm
          (u.eval (HPAtom.eval x y))
          ⁅u.eval (HPAtom.eval x y),
            v.eval (HPAtom.eval x y)⁆) :
    ∃ L : List (PendingFactor p x y),
      WCFactor.listEval L = g ∧
        ∀ F ∈ L,
          WCFactor.PERaw u v F :=
  WCFactor.pairwise_error_raw hg

/-- Extract an explicit pending-factor list together with the imported strict
`cutoff - weight` descent for every member. -/
lemma pending_factor_measure
    {p : ℕ} [Fact p.Prime]
    {G : Type*} [Group G]
    {x y : G}
    {u v : CWord HPAtom}
    {g : G}
    (hg :
      g ∈
        iteratedPairwiseComm
          (u.eval (HPAtom.eval x y))
          ⁅u.eval (HPAtom.eval x y),
            v.eval (HPAtom.eval x y)⁆)
    (finalCutoff : ℕ)
    (hbelow :
      u.weight (weight p) + v.weight (weight p) < finalCutoff) :
    ∃ L : List (PendingFactor p x y),
      WCFactor.listEval L = g ∧
        ∀ F ∈ L,
          finalCutoff - F.word.weight (weight p) <
            finalCutoff -
              (u.weight (weight p) + v.weight (weight p)) := by
  exact
    WCFactor.pairwise_error_measure
      hg weight_pos finalCutoff hbelow

/-
The imported recursive collector exposes the choose-powered suffix only
through subgroup membership.  That is enough for filtration estimates, but it
is too coarse for an aggregate collector: once the suffix has been converted
to arbitrary weighted subgroup factors, the index responsible for each
binomial coefficient is gone.

The next layer keeps those indices.  It deliberately models only products and
inverses, because `leftIteratedChoose` is an ordinary
subgroup closure rather than a normal closure.  In particular, no independent
conjugation of choose-powered terms is introduced here.
-/

/-- One explicit choose-powered term from a left-conjugate orbit.

The `index` field remembers which repeated-left commutator supplied the
binomial coefficient.  The integral multiplicity records products and
inverses introduced while extracting a finite list from subgroup closure. -/
structure CPTerm
    {G : Type*} [Group G]
    (x c : G)
    (orbitSize : ℕ) where
  index :
    ℕ
  index_lt :
    index < orbitSize
  multiplicity :
    ℤ

namespace CPTerm

/-- Evaluate one explicit choose-powered term. -/
def eval
    {G : Type*} [Group G]
    {x c : G}
    {orbitSize : ℕ}
    (T : CPTerm x c orbitSize) :
    G :=
  (leftIteratedElement x c T.index ^
      Nat.choose orbitSize (T.index + 1)) ^
    T.multiplicity

/-- The generator term attached to one valid choose index. -/
def generator
    {G : Type*} [Group G]
    (x c : G)
    (orbitSize index : ℕ)
    (hindex : index < orbitSize) :
    CPTerm x c orbitSize where
  index := index
  index_lt := hindex
  multiplicity := 1

/-- Invert an explicit choose-powered term without losing its index. -/
def inv
    {G : Type*} [Group G]
    {x c : G}
    {orbitSize : ℕ}
    (T : CPTerm x c orbitSize) :
    CPTerm x c orbitSize where
  index := T.index
  index_lt := T.index_lt
  multiplicity := -T.multiplicity

/-- Read the choose index retained by a term. -/
lemma index_orbit_size
    {G : Type*} [Group G]
    {x c : G}
    {orbitSize : ℕ}
    (T : CPTerm x c orbitSize) :
    T.index < orbitSize :=
  T.index_lt

/-- A generator term evaluates to its original choose-powered orbit factor. -/
@[simp]
lemma eval_generator
    {G : Type*} [Group G]
    (x c : G)
    (orbitSize index : ℕ)
    (hindex : index < orbitSize) :
    (generator x c orbitSize index hindex).eval =
      leftIteratedElement x c index ^
        Nat.choose orbitSize (index + 1) := by
  simp [generator, eval]

/-- Inverting a term negates its integral multiplicity and inverts its
evaluation. -/
@[simp]
lemma eval_inv
    {G : Type*} [Group G]
    {x c : G}
    {orbitSize : ℕ}
    (T : CPTerm x c orbitSize) :
    T.inv.eval = T.eval⁻¹ := by
  simp [inv, eval]

/-- Evaluate an explicit choose-powered suffix in collection order. -/
def listEval
    {G : Type*} [Group G]
    {x c : G}
    {orbitSize : ℕ}
    (L : List (CPTerm x c orbitSize)) :
    G :=
  (L.map eval).prod

@[simp]
lemma listEval_nil
    {G : Type*} [Group G]
    {x c : G}
    {orbitSize : ℕ} :
    listEval ([] : List (CPTerm x c orbitSize)) = 1 :=
  rfl

@[simp]
lemma listEval_cons
    {G : Type*} [Group G]
    {x c : G}
    {orbitSize : ℕ}
    (T : CPTerm x c orbitSize)
    (L : List (CPTerm x c orbitSize)) :
    listEval (T :: L) = T.eval * listEval L :=
  rfl

@[simp]
lemma listEval_append
    {G : Type*} [Group G]
    {x c : G}
    {orbitSize : ℕ}
    (L M : List (CPTerm x c orbitSize)) :
    listEval (L ++ M) = listEval L * listEval M := by
  simp [listEval]

/-- Reverse and invert a choose-powered suffix while retaining every source
index. -/
def listInv
    {G : Type*} [Group G]
    {x c : G}
    {orbitSize : ℕ} :
    List (CPTerm x c orbitSize) →
      List (CPTerm x c orbitSize)
  | [] => []
  | T :: L => listInv L ++ [T.inv]

@[simp]
lemma list_eval_inv
    {G : Type*} [Group G]
    {x c : G}
    {orbitSize : ℕ}
    (L : List (CPTerm x c orbitSize)) :
    listEval (listInv L) = (listEval L)⁻¹ := by
  induction L with
  | nil =>
      simp [listInv]
  | cons T L ih =>
      simp only [listInv, listEval_append, listEval_cons, listEval_nil,
        eval_inv, ih, mul_one, mul_inv_rev]

/-- Reify one indexed choose term as a raw Hall factor over the original
Hall-pair coordinates.

The substituted repeated-left word retains the local Hall parent, while the
integral multiplicity retains the exact binomial coefficient and the
subgroup-closure multiplicity. -/
def toRFactor
    {G : Type*} [Group G]
    {x c : G}
    {orbitSize : ℕ}
    (left right : CWord HPAtom)
    (T : CPTerm x c orbitSize) :
    RFactor G where
  word :=
    CWord.hallPairBind left right
      (CWord.pairLeftIterate T.index)
  multiplicity :=
    (Nat.choose orbitSize (T.index + 1) : ℤ) * T.multiplicity
  conjugator :=
    1

/-- Reifying an indexed choose term does not change its evaluation when its
local coordinates are the evaluations of the retained Hall parent. -/
lemma eval_raw_factor
    {G : Type*} [Group G]
    {x y : G}
    {orbitSize : ℕ}
    (left right : CWord HPAtom)
    (T :
      CPTerm
        (left.eval (HPAtom.eval x y))
        ⁅left.eval (HPAtom.eval x y),
          right.eval (HPAtom.eval x y)⁆
        orbitSize) :
    (T.toRFactor left right).eval x y =
      T.eval := by
  simp [toRFactor, RFactor.eval, eval, zpow_mul]

/-- Reify an ordered choose suffix without changing its collection order. -/
def rawFactors
    {G : Type*} [Group G]
    {x c : G}
    {orbitSize : ℕ}
    (left right : CWord HPAtom)
    (L : List (CPTerm x c orbitSize)) :
    List (RFactor G) :=
  L.map (toRFactor left right)

@[simp]
lemma rawFactors_nil
    {G : Type*} [Group G]
    {x c : G}
    {orbitSize : ℕ}
    (left right : CWord HPAtom) :
    rawFactors left right ([] : List (CPTerm x c orbitSize)) = [] :=
  rfl

@[simp]
lemma rawFactors_cons
    {G : Type*} [Group G]
    {x c : G}
    {orbitSize : ℕ}
    (left right : CWord HPAtom)
    (T : CPTerm x c orbitSize)
    (L : List (CPTerm x c orbitSize)) :
    rawFactors left right (T :: L) =
      T.toRFactor left right :: rawFactors left right L :=
  rfl

/-- Reifying an ordered choose suffix does not change its Hall-pair
evaluation. -/
lemma list_raw_factors
    {G : Type*} [Group G]
    {x y : G}
    {orbitSize : ℕ}
    (left right : CWord HPAtom)
    (L :
      List
        (CPTerm
          (left.eval (HPAtom.eval x y))
          ⁅left.eval (HPAtom.eval x y),
            right.eval (HPAtom.eval x y)⁆
          orbitSize)) :
    PPColl.listEval x y (rawFactors left right L) =
      listEval L := by
  induction L with
  | nil =>
      rfl
  | cons T L ih =>
      change
        (T.toRFactor left right).eval x y *
            PPColl.listEval x y
              (rawFactors left right L) =
          T.eval * listEval L
      rw [eval_raw_factor, ih]

/-- Membership in the raw suffix view comes from one exact indexed choose
term. -/
lemma raw_factors
    {G : Type*} [Group G]
    {x c : G}
    {orbitSize : ℕ}
    (left right : CWord HPAtom)
    (L : List (CPTerm x c orbitSize))
    (F : RFactor G) :
    F ∈ rawFactors left right L ↔
      ∃ T ∈ L, T.toRFactor left right = F := by
  simp [rawFactors]

/-- A reified choose factor remembers the repeated-left source index in its
Hall word. -/
lemma word_raw_factor
    {G : Type*} [Group G]
    {x c : G}
    {orbitSize : ℕ}
    (left right : CWord HPAtom)
    (T : CPTerm x c orbitSize) :
    (T.toRFactor left right).word =
      CWord.hallPairBind left right
        (CWord.pairLeftIterate T.index) :=
  rfl

/-- A reified choose factor remembers the binomial coefficient responsible
for its multiplicity. -/
lemma multip_raw_facto
    {G : Type*} [Group G]
    {x c : G}
    {orbitSize : ℕ}
    (left right : CWord HPAtom)
    (T : CPTerm x c orbitSize) :
    (T.toRFactor left right).multiplicity =
      (Nat.choose orbitSize (T.index + 1) : ℤ) * T.multiplicity :=
  rfl

/-- A reified choose factor introduces no independent conjugation. -/
lemma conjugator_raw_factor
    {G : Type*} [Group G]
    {x c : G}
    {orbitSize : ℕ}
    (left right : CWord HPAtom)
    (T : CPTerm x c orbitSize) :
    (T.toRFactor left right).conjugator = 1 :=
  rfl

/-- Every member of an inverted suffix retains a valid choose index. -/
lemma index_list_inv
    {G : Type*} [Group G]
    {x c : G}
    {orbitSize : ℕ}
    {L : List (CPTerm x c orbitSize)}
    {T : CPTerm x c orbitSize}
    (_hT : T ∈ listInv L) :
    T.index < orbitSize :=
  T.index_lt

/-- Extract an explicit choose-powered suffix from choose-power subgroup
membership.

This is the ordinary-closure analogue of
`WCFactor.pairwise_error_raw`.
The returned list retains the exact choose index for every factor, including
factors introduced by inversion. -/
lemma list_eval
    {G : Type*} [Group G]
    {x c g : G}
    {orbitSize : ℕ}
    (hg :
      g ∈
        leftIteratedChoose x c orbitSize) :
    ∃ L : List (CPTerm x c orbitSize),
      listEval L = g := by
  change
    g ∈ Subgroup.closure
      { z : G |
        ∃ r : ℕ, r < orbitSize ∧
          z =
            leftIteratedElement x c r ^
              Nat.choose orbitSize (r + 1) } at hg
  induction hg using Subgroup.closure_induction with
  | mem z hz =>
      rcases hz with ⟨index, hindex, rfl⟩
      refine ⟨[generator x c orbitSize index hindex], ?_⟩
      simp
  | one =>
      exact ⟨[], rfl⟩
  | mul x y _hx _hy ihx ihy =>
      rcases ihx with ⟨L, hL⟩
      rcases ihy with ⟨M, hM⟩
      exact ⟨L ++ M, by simp [hL, hM]⟩
  | inv x _hx ih =>
      rcases ih with ⟨L, hL⟩
      exact ⟨listInv L, by simp [hL]⟩

end CPTerm

/-- An ordered pending-error prefix extracted from the unequal-pairwise-error
normal closure.

The list remains a single noncommutative prefix.  Each member carries its
exact substituted pairwise-error origin; this interface does not normalize
the members independently. -/
structure PEPrefix
    (p : ℕ)
    {G : Type*} [Group G]
    (x y : G)
    (left right : CWord HPAtom) where
  factors :
    List (PendingFactor p x y)
  factors_origin :
    ∀ F ∈ factors,
      WCFactor.PERaw left right F

namespace PEPrefix

/-- Evaluate the retained pending-error prefix in its original order. -/
def eval
    {p : ℕ}
    {G : Type*} [Group G]
    {x y : G}
    {left right : CWord HPAtom}
    (E : PEPrefix p x y left right) :
    G :=
  WCFactor.listEval E.factors

/-- Read pairwise-error provenance for one member of a retained prefix. -/
lemma origin_of_mem
    {p : ℕ}
    {G : Type*} [Group G]
    {x y : G}
    {left right : CWord HPAtom}
    (E : PEPrefix p x y left right)
    {F : PendingFactor p x y}
    (hF : F ∈ E.factors) :
    WCFactor.PERaw left right F :=
  E.factors_origin F hF

/-- Package the imported normal-closure extraction as one ordered
pending-error prefix. -/
lemma exists_eq_mem
    {p : ℕ}
    {G : Type*} [Group G]
    {x y : G}
    {left right : CWord HPAtom}
    {g : G}
    (hg :
      g ∈
        iteratedPairwiseComm
          (left.eval (HPAtom.eval x y))
          ⁅left.eval (HPAtom.eval x y),
            right.eval (HPAtom.eval x y)⁆) :
    ∃ E : PEPrefix p x y left right,
      E.eval = g := by
  rcases pending_factor_list (p := p) hg with
    ⟨L, hL, hLorigin⟩
  exact ⟨⟨L, hLorigin⟩, hL⟩

end PEPrefix

/-- One honest prime-power orbit pass.

The pass keeps both pieces discarded by the older weighted-subgroup shortcut:
the ordered pending-error prefix and the explicit choose-powered suffix with
its source indices.  It is a local orbit decomposition only; it does not
claim that either piece can be normalized independently. -/
structure OPass
    (p : ℕ) [Fact p.Prime]
    {G : Type*} [Group G]
    (x y : G)
    (left right : CWord HPAtom)
    (a : ℕ) where
  pendingPrefix :
    PEPrefix p x y left right
  chooseSuffix :
    List
      (CPTerm
        (left.eval (HPAtom.eval x y))
        ⁅left.eval (HPAtom.eval x y),
          right.eval (HPAtom.eval x y)⁆
        (p ^ a))
  eval_eq :
    pendingPrefix.eval *
        CPTerm.listEval chooseSuffix =
      leftConjugateProduct
        (left.eval (HPAtom.eval x y))
        ⁅left.eval (HPAtom.eval x y),
          right.eval (HPAtom.eval x y)⁆
        (p ^ a)

namespace OPass

/-- Read the exact orbit identity retained by one pass. -/
lemma pending_mul_choose
    {p : ℕ} [Fact p.Prime]
    {G : Type*} [Group G]
    {x y : G}
    {left right : CWord HPAtom}
    {a : ℕ}
    (P : OPass p x y left right a) :
    P.pendingPrefix.eval *
        CPTerm.listEval P.chooseSuffix =
      leftConjugateProduct
        (left.eval (HPAtom.eval x y))
        ⁅left.eval (HPAtom.eval x y),
          right.eval (HPAtom.eval x y)⁆
        (p ^ a) :=
  P.eval_eq

/-- Every pending prefix member retains its substituted pairwise-error
origin. -/
lemma pending_origin
    {p : ℕ} [Fact p.Prime]
    {G : Type*} [Group G]
    {x y : G}
    {left right : CWord HPAtom}
    {a : ℕ}
    (P : OPass p x y left right a)
    {F : PendingFactor p x y}
    (hF : F ∈ P.pendingPrefix.factors) :
    WCFactor.PERaw left right F :=
  P.pendingPrefix.origin_of_mem hF

/-- Every choose suffix member retains the exact index bound of the orbit
pass that produced it. -/
lemma choose_index
    {p : ℕ} [Fact p.Prime]
    {G : Type*} [Group G]
    {x y : G}
    {left right : CWord HPAtom}
    {a : ℕ}
    (P : OPass p x y left right a)
    {T :
      CPTerm
        (left.eval (HPAtom.eval x y))
        ⁅left.eval (HPAtom.eval x y),
          right.eval (HPAtom.eval x y)⁆
        (p ^ a)}
    (_hT : T ∈ P.chooseSuffix) :
    T.index < p ^ a :=
  T.index_lt

end OPass

/-- Construct one actual orbit pass without routing the choose suffix through
opaque weighted subgroup membership. -/
lemma nonempty_orbitPass
    {p : ℕ} [Fact p.Prime]
    {G : Type*} [Group G]
    (x y : G)
    (left right : CWord HPAtom)
    (a : ℕ) :
    Nonempty (OPass p x y left right a) := by
  rcases
      conjugate_pairwise_comm
        (left.eval (HPAtom.eval x y))
        ⁅left.eval (HPAtom.eval x y),
          right.eval (HPAtom.eval x y)⁆
        (p ^ a) with
    ⟨e, he, z, hz, horbit⟩
  rcases PEPrefix.exists_eq_mem (p := p) he with
    ⟨E, hE⟩
  rcases CPTerm.list_eval hz with
    ⟨Z, hZ⟩
  exact ⟨{
    pendingPrefix := E
    chooseSuffix := Z
    eval_eq := by
      rw [hE, hZ, ← horbit] }⟩

/-- A correlated provider chooses one honest orbit pass for every local
Hall-pair parent and every prime-power orbit exponent. -/
abbrev OrbitPassProvider
    (p : ℕ) [Fact p.Prime]
    {G : Type*} [Group G]
    (x y : G) :=
  ∀ (left right : CWord HPAtom) (a : ℕ),
    OPass p x y left right a

/-- Choose honest local orbit passes while retaining their pending prefixes
and choose-index provenance. -/
noncomputable def orbitPassProvider
    (p : ℕ) [Fact p.Prime]
    {G : Type*} [Group G]
    (x y : G) :
    OrbitPassProvider p x y :=
  fun left right a =>
    Classical.choice (nonempty_orbitPass (p := p) x y left right a)

/--
One explicit pending pairwise Hall error.

This structure deliberately permits marker-free low-weight factors.  The
factor remains pending because its parent weighted degree is still below the
final cutoff, not because its syntax contains a selected marker.
-/
structure PError
    (p : ℕ) [Fact p.Prime]
    {G : Type*} [Group G]
    (x y : G)
    (finalCutoff : ℕ) where
  left :
    CWord HPAtom
  right :
    CWord HPAtom
  factor :
    PendingFactor p x y
  origin :
    WCFactor.PERaw left right factor
  parent_below :
    left.weight (weight p) + right.weight (weight p) < finalCutoff

namespace PError

/-- Evaluate one explicit cutoff-zero pending error. -/
def eval
    {p : ℕ} [Fact p.Prime]
    {G : Type*} [Group G]
    {x y : G}
    {finalCutoff : ℕ}
    (E : PError p x y finalCutoff) :
    G :=
  E.factor.eval

/-- The aggregate measure before descending into the selected pairwise
error. -/
def parentMeasure
    {p : ℕ} [Fact p.Prime]
    {G : Type*} [Group G]
    {x y : G}
    {finalCutoff : ℕ}
    (E : PError p x y finalCutoff) :
    ℕ :=
  finalCutoff -
    (E.left.weight (weight p) + E.right.weight (weight p))

/-- The aggregate measure after descending into the selected pairwise
error. -/
def childMeasure
    {p : ℕ} [Fact p.Prime]
    {G : Type*} [Group G]
    {x y : G}
    {finalCutoff : ℕ}
    (E : PError p x y finalCutoff) :
    ℕ :=
  finalCutoff - E.factor.word.weight (weight p)

/-- Imported pairwise-error provenance gives strict aggregate descent. -/
lemma child_measure_parent
    {p : ℕ} [Fact p.Prime]
    {G : Type*} [Group G]
    {x y : G}
    {finalCutoff : ℕ}
    (E : PError p x y finalCutoff) :
    E.childMeasure < E.parentMeasure := by
  exact
    E.origin.cutoff_sub_weightlt weight_pos finalCutoff E.parent_below

/-- Expose the imported pairwise-error origin certificate. -/
lemma pairwiseRaw
    {p : ℕ} [Fact p.Prime]
    {G : Type*} [Group G]
    {x y : G}
    {finalCutoff : ℕ}
    (E : PError p x y finalCutoff) :
    WCFactor.PERaw
      E.left E.right E.factor :=
  E.origin

/-- Expose the below-cutoff premise that keeps an error pending. -/
lemma parentBelow
    {p : ℕ} [Fact p.Prime]
    {G : Type*} [Group G]
    {x y : G}
    {finalCutoff : ℕ}
    (E : PError p x y finalCutoff) :
    E.left.weight (weight p) + E.right.weight (weight p) < finalCutoff :=
  E.parent_below

end PError

/-- Evaluate explicit pending aggregate errors in collection order. -/
def errorListEval
    {p : ℕ} [Fact p.Prime]
    {G : Type*} [Group G]
    {x y : G}
    {finalCutoff : ℕ}
    (L : List (PError p x y finalCutoff)) :
    G :=
  (L.map PError.eval).prod

@[simp]
lemma error_list_nil
    {p : ℕ} [Fact p.Prime]
    {G : Type*} [Group G]
    {x y : G}
    {finalCutoff : ℕ} :
    errorListEval ([] : List (PError p x y finalCutoff)) = 1 :=
  rfl

@[simp]
lemma error_list_cons
    {p : ℕ} [Fact p.Prime]
    {G : Type*} [Group G]
    {x y : G}
    {finalCutoff : ℕ}
    (E : PError p x y finalCutoff)
    (L : List (PError p x y finalCutoff)) :
    errorListEval (E :: L) = E.eval * errorListEval L :=
  rfl

@[simp]
lemma error_list_append
    {p : ℕ} [Fact p.Prime]
    {G : Type*} [Group G]
    {x y : G}
    {finalCutoff : ℕ}
    (L M : List (PError p x y finalCutoff)) :
    errorListEval (L ++ M) = errorListEval L * errorListEval M := by
  simp [errorListEval]

/--
One aggregate Hall-collection state.

Admitted factors have reached the final weighted cutoff.  Pending errors are
kept as explicit pairwise-error values for later recursive refinement.
-/
structure State
    (p : ℕ) [Fact p.Prime]
    {G : Type*} [Group G]
    (x y : G)
    (finalCutoff : ℕ) where
  admitted :
    List (AdmittedFactor p x y finalCutoff)
  pending :
    List (PError p x y finalCutoff)

namespace State

/-- Evaluate an aggregate state: pending pairwise errors first, followed by
admitted factors in collection order.

This order matches the imported orbit frontier
`pairwiseErrorListEval * admittedListEval`.  No commutation or independent
conjugation of pending errors is used. -/
def eval
    {p : ℕ} [Fact p.Prime]
    {G : Type*} [Group G]
    {x y : G}
    {finalCutoff : ℕ}
    (S : State p x y finalCutoff) :
    G :=
  errorListEval S.pending *
    WCFactor.listEval S.admitted

/-- The empty aggregate state evaluates to one. -/
@[simp]
lemma eval_empty
    {p : ℕ} [Fact p.Prime]
    {G : Type*} [Group G]
    {x y : G}
    {finalCutoff : ℕ} :
    (State.mk [] [] : State p x y finalCutoff).eval = 1 := by
  simp [eval]

/-- Every pending member of an aggregate state remembers its imported
pairwise-error origin. -/
lemma origin_pending
    {p : ℕ} [Fact p.Prime]
    {G : Type*} [Group G]
    {x y : G}
    {finalCutoff : ℕ}
    (S : State p x y finalCutoff)
    (E : PError p x y finalCutoff)
    (_hE : E ∈ S.pending) :
    WCFactor.PERaw
      E.left E.right E.factor :=
  E.origin

/-- Every pending member of an aggregate state supports a strict recursive
cutoff-minus-weight descent. -/
lemma child_measure_pending
    {p : ℕ} [Fact p.Prime]
    {G : Type*} [Group G]
    {x y : G}
    {finalCutoff : ℕ}
    (S : State p x y finalCutoff)
    (E : PError p x y finalCutoff)
    (_hE : E ∈ S.pending) :
    E.childMeasure < E.parentMeasure :=
  E.child_measure_parent

end State

/--
One aggregate refinement frontier for a group value.

The strict decrease is attached to every pending error in the returned state.
This is the recursive contract required by a future complete aggregate Hall
collector.
-/
structure Frontier
    (p : ℕ) [Fact p.Prime]
    {G : Type*} [Group G]
    (x y : G)
    (finalCutoff : ℕ)
    (value : G)
    (parentMeasure : ℕ) where
  state :
    State p x y finalCutoff
  eval_eq :
    state.eval = value
  pending_decrease :
    ∀ E ∈ state.pending, E.childMeasure < parentMeasure

namespace Frontier

/-- A terminal frontier has no pending pairwise errors. -/
def terminal
    {p : ℕ} [Fact p.Prime]
    {G : Type*} [Group G]
    {x y : G}
    {finalCutoff parentMeasure : ℕ}
    (L : List (AdmittedFactor p x y finalCutoff)) :
    Frontier p x y finalCutoff
      (WCFactor.listEval L)
      parentMeasure where
  state := ⟨L, []⟩
  eval_eq := by simp [State.eval]
  pending_decrease := by simp

/-- Read the imported pairwise-error origin of one pending frontier member. -/
lemma origin_pending
    {p : ℕ} [Fact p.Prime]
    {G : Type*} [Group G]
    {x y : G}
    {finalCutoff parentMeasure : ℕ}
    {value : G}
    (F : Frontier p x y finalCutoff value parentMeasure)
    (E : PError p x y finalCutoff)
    (hE : E ∈ F.state.pending) :
    WCFactor.PERaw
      E.left E.right E.factor :=
  F.state.origin_pending E hE

/-- Read strict recursive descent for one pending frontier member. -/
lemma childMeasure_lt
    {p : ℕ} [Fact p.Prime]
    {G : Type*} [Group G]
    {x y : G}
    {finalCutoff parentMeasure : ℕ}
    {value : G}
    (F : Frontier p x y finalCutoff value parentMeasure)
    (E : PError p x y finalCutoff)
    (hE : E ∈ F.state.pending) :
    E.childMeasure < parentMeasure :=
  F.pending_decrease E hE

end Frontier

/-- A recursive aggregate refinement starts after descending into one
explicit pending pairwise error.  The next frontier is measured from the
child word, not from the pairwise-error parent.

This convenience alias records the corrected child measure for future
constructive work.  The universal aggregate boundary below does not assume
that an arbitrary value of this type can be refined. -/
abbrev ErrorRefinement
    {p : ℕ} [Fact p.Prime]
    {G : Type*} [Group G]
    {x y : G}
    {finalCutoff : ℕ}
    (E : PError p x y finalCutoff) :=
  Frontier p x y finalCutoff E.eval E.childMeasure

/--
A correlated pending batch from one aggregate Hall pass.

The list is kept intact and in collection order.  Every member has the same
pairwise-error parent, but retains its own substituted Hall word, integral
multiplicity, and conjugator.

This is only a geometric diagnostic record.  It does not carry the
coefficient budget needed for a recursive Hall transition, and no recursive
existence theorem below consumes it.  In particular, a fabricated singleton
batch is not treated as independently collectable.
-/
structure CPBatch
    (p : ℕ) [Fact p.Prime]
    {G : Type*} [Group G]
    (x y : G)
    (finalCutoff : ℕ) where
  left :
    CWord HPAtom
  right :
    CWord HPAtom
  parent_below :
    left.weight (weight p) + right.weight (weight p) < finalCutoff
  errors :
    List (PError p x y finalCutoff)
  same_parent :
    ∀ E ∈ errors, E.left = left ∧ E.right = right

namespace CPBatch

/-- Evaluate a correlated pending batch without splitting its ordered Hall
product into independently normalized errors. -/
def eval
    {p : ℕ} [Fact p.Prime]
    {G : Type*} [Group G]
    {x y : G}
    {finalCutoff : ℕ}
    (B : CPBatch p x y finalCutoff) :
    G :=
  errorListEval B.errors

/-- The recursive measure of a correlated pending batch is the
cutoff-minus-weight measure of its common pairwise-error parent. -/
def measure
    {p : ℕ} [Fact p.Prime]
    {G : Type*} [Group G]
    {x y : G}
    {finalCutoff : ℕ}
    (B : CPBatch p x y finalCutoff) :
    ℕ :=
  finalCutoff -
    (B.left.weight (weight p) + B.right.weight (weight p))

/-- A correlated pending batch remains below the final cutoff. -/
lemma parentBelow
    {p : ℕ} [Fact p.Prime]
    {G : Type*} [Group G]
    {x y : G}
    {finalCutoff : ℕ}
    (B : CPBatch p x y finalCutoff) :
    B.left.weight (weight p) + B.right.weight (weight p) < finalCutoff :=
  B.parent_below

/-- The common parent weight of a correlated pending batch is strictly
positive as a cutoff-minus-weight recursive measure. -/
lemma measure_pos
    {p : ℕ} [Fact p.Prime]
    {G : Type*} [Group G]
    {x y : G}
    {finalCutoff : ℕ}
    (B : CPBatch p x y finalCutoff) :
    0 < B.measure := by
  exact Nat.sub_pos_of_lt B.parent_below

/-- Read the common parent equations for one member of a correlated pending
batch. -/
lemma same_of_mem
    {p : ℕ} [Fact p.Prime]
    {G : Type*} [Group G]
    {x y : G}
    {finalCutoff : ℕ}
    (B : CPBatch p x y finalCutoff)
    (E : PError p x y finalCutoff)
    (hE : E ∈ B.errors) :
    E.left = B.left ∧ E.right = B.right :=
  B.same_parent E hE

/-- Every member of a correlated pending batch retains its imported
pairwise-error origin. -/
lemma origin_of_mem
    {p : ℕ} [Fact p.Prime]
    {G : Type*} [Group G]
    {x y : G}
    {finalCutoff : ℕ}
    (B : CPBatch p x y finalCutoff)
    (E : PError p x y finalCutoff)
    (_hE : E ∈ B.errors) :
    WCFactor.PERaw
      E.left E.right E.factor :=
  E.origin

/-- Every member of a correlated batch has strictly lower
cutoff-minus-weight measure than the common parent. -/
lemma child_measure
    {p : ℕ} [Fact p.Prime]
    {G : Type*} [Group G]
    {x y : G}
    {finalCutoff : ℕ}
    (B : CPBatch p x y finalCutoff)
    (E : PError p x y finalCutoff)
    (hE : E ∈ B.errors) :
    E.childMeasure < B.measure := by
  have hsame := B.same_of_mem E hE
  simpa [PError.parentMeasure, measure, hsame.1, hsame.2] using
    E.child_measure_parent

end CPBatch

/-
The local orbit interface above still presents its error prefix and choose
suffix in two different representations.  The next adapters keep the exact
ordered product while moving both pieces into the aggregate collector's raw
vocabulary.

This layer remains deliberately local: it converts one honest orbit pass and
does not claim that arbitrary correlated batches can be normalized.
-/

namespace PEPrefix

/-- Convert one retained prefix factor into a cutoff-indexed pairwise error.
The imported origin certificate and the common parent bound are carried
forward unchanged. -/
def pairwiseErrorFactor
    {p : ℕ} [Fact p.Prime]
    {G : Type*} [Group G]
    {x y : G}
    {left right : CWord HPAtom}
    (finalCutoff : ℕ)
    (hbelow :
      left.weight (weight p) + right.weight (weight p) < finalCutoff)
    (F : PendingFactor p x y)
    (hF :
      WCFactor.PERaw left right F) :
    PError p x y finalCutoff where
  left :=
    left
  right :=
    right
  factor :=
    F
  origin :=
    hF
  parent_below :=
    hbelow

/-- The cutoff-indexed view of one retained factor has the same underlying
weighted factor. -/
@[simp]
lemma factor_pairw_error
    {p : ℕ} [Fact p.Prime]
    {G : Type*} [Group G]
    {x y : G}
    {left right : CWord HPAtom}
    (finalCutoff : ℕ)
    (hbelow :
      left.weight (weight p) + right.weight (weight p) < finalCutoff)
    (F : PendingFactor p x y)
    (hF :
      WCFactor.PERaw left right F) :
    (pairwiseErrorFactor finalCutoff hbelow F hF).factor = F :=
  rfl

/-- The cutoff-indexed view of one retained factor has the same group
evaluation. -/
@[simp]
lemma pairwi_error_facta
    {p : ℕ} [Fact p.Prime]
    {G : Type*} [Group G]
    {x y : G}
    {left right : CWord HPAtom}
    (finalCutoff : ℕ)
    (hbelow :
      left.weight (weight p) + right.weight (weight p) < finalCutoff)
    (F : PendingFactor p x y)
    (hF :
      WCFactor.PERaw left right F) :
    (pairwiseErrorFactor finalCutoff hbelow F hF).eval =
      F.eval :=
  rfl

/-- Convert an ordered retained factor list into cutoff-indexed pairwise
errors without changing order. -/
def pairwi_error_facto
    {p : ℕ} [Fact p.Prime]
    {G : Type*} [Group G]
    {x y : G}
    {left right : CWord HPAtom}
    (finalCutoff : ℕ)
    (hbelow :
      left.weight (weight p) + right.weight (weight p) < finalCutoff) :
    (L : List (PendingFactor p x y)) →
      (∀ F ∈ L,
        WCFactor.PERaw left right F) →
        List (PError p x y finalCutoff)
  | [], _ =>
      []
  | F :: L, horigin =>
      pairwiseErrorFactor finalCutoff hbelow F
          (horigin F (by simp)) ::
        pairwi_error_facto finalCutoff hbelow L
          (fun E hE => horigin E (by simp [hE]))

/-- Converting a retained list to pairwise errors leaves its ordered group
product unchanged. -/
lemma error_pairw_error
    {p : ℕ} [Fact p.Prime]
    {G : Type*} [Group G]
    {x y : G}
    {left right : CWord HPAtom}
    (finalCutoff : ℕ)
    (hbelow :
      left.weight (weight p) + right.weight (weight p) < finalCutoff) :
    ∀ (L : List (PendingFactor p x y))
      (horigin :
        ∀ F ∈ L,
          WCFactor.PERaw left right F),
      errorListEval
          (pairwi_error_facto finalCutoff hbelow L horigin) =
        WCFactor.listEval L
  | [], _ =>
      rfl
  | F :: L, horigin => by
      change
        F.eval *
            errorListEval
              (pairwi_error_facto finalCutoff hbelow L
                (fun E hE => horigin E (by simp [hE]))) =
          F.eval * WCFactor.listEval L
      rw [error_pairw_error]

/-- Every converted prefix error retains the same local Hall parent. -/
lemma same_pairwise_errors
    {p : ℕ} [Fact p.Prime]
    {G : Type*} [Group G]
    {x y : G}
    {left right : CWord HPAtom}
    (finalCutoff : ℕ)
    (hbelow :
      left.weight (weight p) + right.weight (weight p) < finalCutoff) :
    ∀ (L : List (PendingFactor p x y))
      (horigin :
        ∀ F ∈ L,
          WCFactor.PERaw left right F)
      (E : PError p x y finalCutoff),
      E ∈ pairwi_error_facto finalCutoff hbelow L horigin →
        E.left = left ∧ E.right = right
  | [], _, E => by
      intro hE
      change E ∈ ([] : List (PError p x y finalCutoff)) at hE
      exact (List.not_mem_nil hE).elim
  | F :: L, horigin, E => by
      intro hE
      change
        E ∈
          pairwiseErrorFactor finalCutoff hbelow F
              (horigin F (by simp)) ::
            pairwi_error_facto finalCutoff hbelow L
              (fun D hD => horigin D (by simp [hD])) at hE
      rw [List.mem_cons] at hE
      rcases hE with rfl | hE
      · exact ⟨rfl, rfl⟩
      · exact
          same_pairwise_errors finalCutoff hbelow L
            (fun D hD => horigin D (by simp [hD])) E hE

/-- Convert an ordered retained prefix into the correlated aggregate batch
expected by the recursive collector. -/
def correlatedBatch
    {p : ℕ} [Fact p.Prime]
    {G : Type*} [Group G]
    {x y : G}
    {left right : CWord HPAtom}
    (E : PEPrefix p x y left right)
    (finalCutoff : ℕ)
    (hbelow :
      left.weight (weight p) + right.weight (weight p) < finalCutoff) :
    CPBatch p x y finalCutoff where
  left :=
    left
  right :=
    right
  parent_below :=
    hbelow
  errors :=
    pairwi_error_facto finalCutoff hbelow E.factors E.factors_origin
  same_parent :=
    same_pairwise_errors finalCutoff hbelow E.factors
      E.factors_origin

/-- Converting a retained prefix to a correlated aggregate batch leaves its
ordered group product unchanged. -/
lemma eval_corre_batch
    {p : ℕ} [Fact p.Prime]
    {G : Type*} [Group G]
    {x y : G}
    {left right : CWord HPAtom}
    (E : PEPrefix p x y left right)
    (finalCutoff : ℕ)
    (hbelow :
      left.weight (weight p) + right.weight (weight p) < finalCutoff) :
    (E.correlatedBatch finalCutoff hbelow).eval =
      E.eval := by
  exact
    error_pairw_error finalCutoff hbelow E.factors
      E.factors_origin

/-- The correlated aggregate view retains the original local Hall parent. -/
@[simp]
lemma left_corre_batch
    {p : ℕ} [Fact p.Prime]
    {G : Type*} [Group G]
    {x y : G}
    {left right : CWord HPAtom}
    (E : PEPrefix p x y left right)
    (finalCutoff : ℕ)
    (hbelow :
      left.weight (weight p) + right.weight (weight p) < finalCutoff) :
    (E.correlatedBatch finalCutoff hbelow).left = left :=
  rfl

/-- The correlated aggregate view retains the original right Hall parent. -/
@[simp]
lemma right_corre_batch
    {p : ℕ} [Fact p.Prime]
    {G : Type*} [Group G]
    {x y : G}
    {left right : CWord HPAtom}
    (E : PEPrefix p x y left right)
    (finalCutoff : ℕ)
    (hbelow :
      left.weight (weight p) + right.weight (weight p) < finalCutoff) :
    (E.correlatedBatch finalCutoff hbelow).right = right :=
  rfl

end PEPrefix

/-- One raw aggregate split obtained from an honest local orbit pass.

The pending prefix remains correlated, the admitted suffix remains ordered,
and the exact noncommutative orbit identity is retained.  This is a local
normalization record only; it does not claim a universal traversal. -/
structure ROSplit
    (p : ℕ) [Fact p.Prime]
    {G : Type*} [Group G]
    (x y : G)
    (left right : CWord HPAtom)
    (a finalCutoff : ℕ) where
  pending :
    CPBatch p x y finalCutoff
  admitted :
    List (RFactor G)
  eval_eq :
    pending.eval *
        PPColl.listEval x y admitted =
      leftConjugateProduct
        (left.eval (HPAtom.eval x y))
        ⁅left.eval (HPAtom.eval x y),
          right.eval (HPAtom.eval x y)⁆
        (p ^ a)

namespace OPass

/-- Repackage one honest orbit pass as a raw aggregate split at any cutoff
strictly above its local Hall parent. -/
def rawOrbitSplit
    {p : ℕ} [Fact p.Prime]
    {G : Type*} [Group G]
    {x y : G}
    {left right : CWord HPAtom}
    {a : ℕ}
    (P : OPass p x y left right a)
    (finalCutoff : ℕ)
    (hbelow :
      left.weight (weight p) + right.weight (weight p) < finalCutoff) :
    ROSplit p x y left right a finalCutoff where
  pending :=
    P.pendingPrefix.correlatedBatch finalCutoff hbelow
  admitted :=
    CPTerm.rawFactors left right P.chooseSuffix
  eval_eq := by
    rw [PEPrefix.eval_corre_batch,
      CPTerm.list_raw_factors]
    exact P.eval_eq

/-- The raw split keeps the exact correlated prefix converted from the orbit
pass. -/
@[simp]
lemma pending_raw_split
    {p : ℕ} [Fact p.Prime]
    {G : Type*} [Group G]
    {x y : G}
    {left right : CWord HPAtom}
    {a : ℕ}
    (P : OPass p x y left right a)
    (finalCutoff : ℕ)
    (hbelow :
      left.weight (weight p) + right.weight (weight p) < finalCutoff) :
    (P.rawOrbitSplit finalCutoff hbelow).pending =
      P.pendingPrefix.correlatedBatch finalCutoff hbelow :=
  rfl

/-- The raw split keeps the exact ordered choose suffix converted from the
orbit pass. -/
@[simp]
lemma admitted_raw_split
    {p : ℕ} [Fact p.Prime]
    {G : Type*} [Group G]
    {x y : G}
    {left right : CWord HPAtom}
    {a : ℕ}
    (P : OPass p x y left right a)
    (finalCutoff : ℕ)
    (hbelow :
      left.weight (weight p) + right.weight (weight p) < finalCutoff) :
    (P.rawOrbitSplit finalCutoff hbelow).admitted =
      CPTerm.rawFactors left right P.chooseSuffix :=
  rfl

end OPass

namespace ROSplit

/-- Read the exact noncommutative orbit identity retained by a raw split. -/
lemma pending_mul_admitted
    {p : ℕ} [Fact p.Prime]
    {G : Type*} [Group G]
    {x y : G}
    {left right : CWord HPAtom}
    {a finalCutoff : ℕ}
    (S : ROSplit p x y left right a finalCutoff) :
    S.pending.eval *
        PPColl.listEval x y S.admitted =
      leftConjugateProduct
        (left.eval (HPAtom.eval x y))
        ⁅left.eval (HPAtom.eval x y),
          right.eval (HPAtom.eval x y)⁆
        (p ^ a) :=
  S.eval_eq

/-- The pending batch of a raw orbit split remains below the requested
aggregate cutoff. -/
lemma pending_parentBelow
    {p : ℕ} [Fact p.Prime]
    {G : Type*} [Group G]
    {x y : G}
    {left right : CWord HPAtom}
    {a finalCutoff : ℕ}
    (S : ROSplit p x y left right a finalCutoff) :
    S.pending.left.weight (weight p) +
        S.pending.right.weight (weight p) <
      finalCutoff :=
  S.pending.parentBelow

/-- Every pending member of a raw orbit split retains imported pairwise
error provenance. -/
lemma pending_origin
    {p : ℕ} [Fact p.Prime]
    {G : Type*} [Group G]
    {x y : G}
    {left right : CWord HPAtom}
    {a finalCutoff : ℕ}
    (S : ROSplit p x y left right a finalCutoff)
    (E : PError p x y finalCutoff)
    (hE : E ∈ S.pending.errors) :
    WCFactor.PERaw
      E.left E.right E.factor :=
  S.pending.origin_of_mem E hE

/-- Every pending member of a raw orbit split strictly descends from the
common local Hall parent. -/
lemma pendin_child_measu
    {p : ℕ} [Fact p.Prime]
    {G : Type*} [Group G]
    {x y : G}
    {left right : CWord HPAtom}
    {a finalCutoff : ℕ}
    (S : ROSplit p x y left right a finalCutoff)
    (E : PError p x y finalCutoff)
    (hE : E ∈ S.pending.errors) :
    E.childMeasure < S.pending.measure :=
  S.pending.child_measure E hE

end ROSplit

/-- A raw orbit-split provider chooses one honest local split whenever the
caller supplies a cutoff strictly above the local Hall parent.

The provider does not claim a global traversal.  It is only the local
geometric oracle consumed by the remaining aggregate construction. -/
abbrev RawSplitProvider
    (p : ℕ) [Fact p.Prime]
    {G : Type*} [Group G]
    (x y : G) :=
  ∀ (left right : CWord HPAtom)
    (a finalCutoff : ℕ),
      left.weight (weight p) + right.weight (weight p) < finalCutoff →
        ROSplit p x y left right a finalCutoff

/-- Choose honest raw local splits by converting the already-constructed
orbit-pass provider. -/
noncomputable def rawSplitProvider
    (p : ℕ) [Fact p.Prime]
    {G : Type*} [Group G]
    (x y : G) :
    RawSplitProvider p x y :=
  fun left right a finalCutoff hbelow =>
    (orbitPassProvider p x y left right a).rawOrbitSplit
      finalCutoff hbelow

/-- Every split selected by the canonical provider retains its exact local
orbit identity. -/
lemma provider_pending_admitted
    {p : ℕ} [Fact p.Prime]
    {G : Type*} [Group G]
    (x y : G)
    (left right : CWord HPAtom)
    (a finalCutoff : ℕ)
    (hbelow :
      left.weight (weight p) + right.weight (weight p) < finalCutoff) :
    let S :=
      rawSplitProvider p x y left right a finalCutoff hbelow
    S.pending.eval *
        PPColl.listEval x y S.admitted =
      leftConjugateProduct
        (left.eval (HPAtom.eval x y))
        ⁅left.eval (HPAtom.eval x y),
          right.eval (HPAtom.eval x y)⁆
        (p ^ a) := by
  exact
    (rawSplitProvider p x y left right a finalCutoff hbelow).eval_eq

/--
The aggregate weighted cutoff used while constructing one normalized
successor kernel.

It records the complete substituted weight of the source word and the source
multiplicity together.  Pending Hall errors may lie below this cutoff; they
may be retained in correlated diagnostic batches while a constructive Hall
pass is being designed.  The universal aggregate boundary below does not
derive a transition from this numeric cutoff alone.
-/
def kernelCutoff
    (p : ℕ)
    (w : CWord HPAtom)
    (n : ℕ) :
    ℕ :=
  wordWeight p w * (n + 1)

/-- A diagnostic initial measure leaving room above every proper
cutoff-minus-weight descent arising during a first aggregate pass. -/
def initialMeasure
    (p : ℕ)
    (w : CWord HPAtom)
    (n : ℕ) :
    ℕ :=
  kernelCutoff p w n + 1

/-- The initial aggregate measure is positive. -/
lemma initialMeasure_pos
    (p : ℕ)
    (w : CWord HPAtom)
    (n : ℕ) :
    0 < initialMeasure p w n := by
  simp [initialMeasure]

/-- The pending-batch type specialized to one normalized successor kernel. -/
abbrev KernelPendingBatch
    (p : ℕ) [Fact p.Prime]
    {G : Type*} [Group G]
    (x y : G)
    (w : CWord HPAtom)
    (n : ℕ) :=
  CPBatch p x y (kernelCutoff p w n)

/--
One admitted normalized successor factor.

Unlike a pending pairwise error, an admitted factor already carries the full
coordinatewise Hall-Petresco certificate required by
`NSKern`.  Pending batches deliberately do not claim this
certificate for any of their members.
-/
structure CFactor
    (p : ℕ)
    {G : Type*} [Group G]
    (x y : G)
    (w : CWord HPAtom)
    (n : ℕ) where
  factor :
    RFactor G
  certificate :
    NSCert p w n factor

namespace CFactor

/-- Evaluate one admitted successor factor. -/
def eval
    {p : ℕ}
    {G : Type*} [Group G]
    {x y : G}
    {w : CWord HPAtom}
    {n : ℕ}
    (F : CFactor p x y w n) :
    G :=
  F.factor.eval x y

/-- Evaluate admitted successor factors in collection order. -/
def listEval
    {p : ℕ}
    {G : Type*} [Group G]
    {x y : G}
    {w : CWord HPAtom}
    {n : ℕ}
    (L : List (CFactor p x y w n)) :
    G :=
  (L.map eval).prod

@[simp]
lemma listEval_nil
    {p : ℕ}
    {G : Type*} [Group G]
    {x y : G}
    {w : CWord HPAtom}
    {n : ℕ} :
    listEval ([] : List (CFactor p x y w n)) = 1 :=
  rfl

@[simp]
lemma listEval_cons
    {p : ℕ}
    {G : Type*} [Group G]
    {x y : G}
    {w : CWord HPAtom}
    {n : ℕ}
    (F : CFactor p x y w n)
    (L : List (CFactor p x y w n)) :
    listEval (F :: L) = F.eval * listEval L :=
  rfl

@[simp]
lemma listEval_append
    {p : ℕ}
    {G : Type*} [Group G]
    {x y : G}
    {w : CWord HPAtom}
    {n : ℕ}
    (L M : List (CFactor p x y w n)) :
    listEval (L ++ M) = listEval L * listEval M := by
  simp [listEval]

/-- Forget the certificates while retaining the admitted raw factors in
their exact collection order. -/
def rawFactors
    {p : ℕ}
    {G : Type*} [Group G]
    {x y : G}
    {w : CWord HPAtom}
    {n : ℕ}
    (L : List (CFactor p x y w n)) :
    List (RFactor G) :=
  L.map factor

/-- Forgetting admitted certificates does not change evaluation. -/
@[simp]
lemma raw_list_factors
    {p : ℕ}
    {G : Type*} [Group G]
    {x y : G}
    {w : CWord HPAtom}
    {n : ℕ}
    (L : List (CFactor p x y w n)) :
    PPColl.listEval x y (rawFactors L) =
      listEval L := by
  induction L with
  | nil =>
      rfl
  | cons F L ih =>
      change F.factor.eval x y *
          PPColl.listEval x y (rawFactors L) =
        F.eval * listEval L
      rw [ih]
      rfl

/-- Every raw factor obtained by forgetting admitted certificates still has
its successor certificate. -/
lemma certif_raw_facto
    {p : ℕ}
    {G : Type*} [Group G]
    {x y : G}
    {w : CWord HPAtom}
    {n : ℕ}
    (L : List (CFactor p x y w n)) :
    ∀ E ∈ rawFactors L,
      NSCert p w n E := by
  intro E hE
  rcases List.mem_map.mp hE with ⟨F, hF, rfl⟩
  exact F.certificate

/-- Transport one admitted successor factor through a group homomorphism.
The coordinatewise certificate is unchanged because its Hall word and
integral multiplicity are unchanged. -/
def mapHom
    {p : ℕ}
    {G H : Type*} [Group G] [Group H]
    {x y : G}
    {w : CWord HPAtom}
    {n : ℕ}
    (φ : G →* H)
    (F : CFactor p x y w n) :
    CFactor p (φ x) (φ y) w n where
  factor := F.factor.mapHom φ
  certificate := {
    positivity := {
      left_degree_pos :=
        F.certificate.positivity.left_degree_pos
      right_degree_pos :=
        F.certificate.positivity.right_degree_pos }
    divisibility := {
      left_dvd :=
        F.certificate.divisibility.left_dvd
      right_dvd :=
        F.certificate.divisibility.right_dvd } }

/-- Evaluation of a transported admitted factor is the homomorphic image of
its original evaluation. -/
@[simp]
lemma eval_mapHom
    {p : ℕ}
    {G H : Type*} [Group G] [Group H]
    {x y : G}
    {w : CWord HPAtom}
    {n : ℕ}
    (φ : G →* H)
    (F : CFactor p x y w n) :
    (F.mapHom φ).eval = φ F.eval := by
  exact RFactor.eval_mapHom φ x y F.factor

/-- Transport a complete admitted list through a group homomorphism without
changing collection order. -/
def listMapHom
    {p : ℕ}
    {G H : Type*} [Group G] [Group H]
    {x y : G}
    {w : CWord HPAtom}
    {n : ℕ}
    (φ : G →* H)
    (L : List (CFactor p x y w n)) :
    List (CFactor p (φ x) (φ y) w n) :=
  L.map (mapHom φ)

/-- Evaluation of an admitted list commutes with transport. -/
@[simp]
lemma list_eval_hom
    {p : ℕ}
    {G H : Type*} [Group G] [Group H]
    {x y : G}
    {w : CWord HPAtom}
    {n : ℕ}
    (φ : G →* H)
    (L : List (CFactor p x y w n)) :
    listEval (listMapHom φ L) = φ (listEval L) := by
  induction L with
  | nil =>
      simp [listMapHom]
  | cons F L ih =>
      change
        (F.mapHom φ).eval * listEval (listMapHom φ L) =
          φ (F.eval * listEval L)
      rw [eval_mapHom, ih, map_mul]

end CFactor

/-- Evaluate an optional correlated pending batch. -/
def pendingEval
    {p : ℕ} [Fact p.Prime]
    {G : Type*} [Group G]
    {x y : G}
    {w : CWord HPAtom}
    {n : ℕ} :
    Option (KernelPendingBatch p x y w n) →
      G
  | none => 1
  | some B => B.eval

/--
One conditional aggregate normalized successor frontier.

There is at most one pending batch.  It stays before the admitted suffix in
the exact noncommutative collection order supplied by a Hall pass.  This
structure records the result of a pass when such a result has been
constructed; it does not claim that geometric pending-batch data is
sufficient to construct another pass.
-/
structure KFront
    (p : ℕ) [Fact p.Prime]
    {G : Type*} [Group G]
    (x y : G)
    (w : CWord HPAtom)
    (n : ℕ)
    (value : G)
    (parentMeasure : ℕ) where
  pending :
    Option (KernelPendingBatch p x y w n)
  admitted :
    List (CFactor p x y w n)
  eval_eq :
    pendingEval pending * CFactor.listEval admitted = value
  pending_decrease :
    ∀ B, pending = some B → B.measure < parentMeasure

namespace KFront

/-- A frontier with no pending batch is terminal. -/
def terminal
    {p : ℕ} [Fact p.Prime]
    {G : Type*} [Group G]
    (x y : G)
    (w : CWord HPAtom)
    (n : ℕ)
    (parentMeasure : ℕ)
    (L : List (CFactor p x y w n)) :
    KFront p x y w n (CFactor.listEval L) parentMeasure where
  pending := none
  admitted := L
  eval_eq := by
    simp [pendingEval]
  pending_decrease := by
    simp

/-- Read the strict recursive decrease of the optional correlated batch. -/
lemma measure_lt
    {p : ℕ} [Fact p.Prime]
    {G : Type*} [Group G]
    {x y : G}
    {w : CWord HPAtom}
    {n : ℕ}
    {value : G}
    {parentMeasure : ℕ}
    (F : KFront p x y w n value parentMeasure)
    (B : KernelPendingBatch p x y w n)
    (hB : F.pending = some B) :
    B.measure < parentMeasure :=
  F.pending_decrease B hB

end KFront

/-- A complete resolution of one aggregate value into admitted normalized
successor factors. -/
structure KResolu
    (p : ℕ)
    {G : Type*} [Group G]
    (x y : G)
    (w : CWord HPAtom)
    (n : ℕ)
    (value : G) where
  factors :
    List (CFactor p x y w n)
  eval_eq :
    CFactor.listEval factors = value

namespace KResolu

/-- An admitted list is already a complete aggregate resolution. -/
def ofList
    {p : ℕ}
    {G : Type*} [Group G]
    (x y : G)
    (w : CWord HPAtom)
    (n : ℕ)
    (L : List (CFactor p x y w n)) :
    KResolu p x y w n (CFactor.listEval L) where
  factors := L
  eval_eq := rfl

/-- Append an admitted suffix after resolving the correlated pending prefix. -/
def appendAdmitted
    {p : ℕ}
    {G : Type*} [Group G]
    {x y : G}
    {w : CWord HPAtom}
    {n : ℕ}
    {value : G}
    (R : KResolu p x y w n value)
    (L : List (CFactor p x y w n)) :
    KResolu p x y w n
      (value * CFactor.listEval L) where
  factors := R.factors ++ L
  eval_eq := by
    rw [CFactor.listEval_append, R.eval_eq]

/-- Transport a completed aggregate resolution through a group homomorphism.
This is the only ambient-group transport required by the universal
free-group collector. -/
def mapHom
    {p : ℕ}
    {G H : Type*} [Group G] [Group H]
    {x y : G}
    {w : CWord HPAtom}
    {n : ℕ}
    {value : G}
    (R : KResolu p x y w n value)
    (φ : G →* H) :
    KResolu p (φ x) (φ y) w n (φ value) where
  factors := CFactor.listMapHom φ R.factors
  eval_eq := by
    rw [CFactor.list_eval_hom, R.eval_eq]

/-- Forget the aggregate bookkeeping and expose the normalized successor
kernel consumed by the existing Hall-Petresco layer. -/
def natSuccKernel
    {p : ℕ}
    {G : Type*} [Group G]
    {x y : G}
    {w : CWord HPAtom}
    {n : ℕ}
    (R :
      KResolu p x y w n
        (w.eval (HPAtom.eval x (y ^ p)) ^ ((n + 1 : ℕ) : ℤ))) :
    NSKern p x y w n where
  factors := CFactor.rawFactors R.factors
  eval_eq := by
    rw [CFactor.raw_list_factors, R.eval_eq]
  factors_certificate := by
    exact ⟨CFactor.certif_raw_facto R.factors⟩

end KResolu

namespace KFront

/-- Conditionally resolve one aggregate frontier after a caller supplies a
resolution of its single correlated pending batch, if present. -/
def resolve
    {p : ℕ} [Fact p.Prime]
    {G : Type*} [Group G]
    {x y : G}
    {w : CWord HPAtom}
    {n : ℕ}
    {value : G}
    {parentMeasure : ℕ}
    (F : KFront p x y w n value parentMeasure)
    (solve :
      ∀ B, F.pending = some B →
        KResolu p x y w n B.eval) :
    KResolu p x y w n value := by
  cases hpending : F.pending with
  | none =>
      exact {
        factors := F.admitted
        eval_eq := by
          simpa [pendingEval, hpending] using F.eval_eq }
  | some B =>
      let R := solve B hpending
      exact {
        factors := R.factors ++ F.admitted
        eval_eq := by
          rw [CFactor.listEval_append, R.eval_eq]
          simpa [pendingEval, hpending] using F.eval_eq }

end KFront

/-!
### Universal aggregate boundary

The recursive Hall combinatorics are isolated in the free group on the
Hall-pair alphabet.  The remaining admitted boundary returns one exact final
factor list together with both:

* the free-group evaluation identity for that list;
* the coordinatewise certificate for every factor in that same list.

No recursive existence theorem is asserted for a fabricated geometric
pairwise-error batch.  Once the universal final list has been constructed,
`FreeGroup.lift` transports the exact same ordered list into an arbitrary
ambient group by mapping only the recorded conjugators.
-/

/-- The universal ambient group for normalized right-prime collection. -/
abbrev UniversalGroup :=
  FreeGroup HPAtom

/-- The universal left Hall-pair generator. -/
def universalLeft :
    UniversalGroup :=
  FreeGroup.of HPAtom.left

/-- The universal right Hall-pair generator. -/
def universalRight :
    UniversalGroup :=
  FreeGroup.of HPAtom.right

/-- Specialize the universal Hall-pair generators to an arbitrary pair of
group elements. -/
def specialize
    {G : Type*} [Group G]
    (x y : G) :
    UniversalGroup →* G :=
  FreeGroup.lift (HPAtom.eval x y)

@[simp]
lemma specialize_universalLeft
    {G : Type*} [Group G]
    (x y : G) :
    specialize x y universalLeft = x := by
  simp [specialize, universalLeft, HPAtom.eval]

@[simp]
lemma specialize_universalRight
    {G : Type*} [Group G]
    (x y : G) :
    specialize x y universalRight = y := by
  simp [specialize, universalRight, HPAtom.eval]

/-- Universal Hall-word evaluation specializes to ordinary Hall-word
evaluation after the right-prime substitution. -/
@[simp]
lemma specialize_right_prime
    {G : Type*} [Group G]
    (x y : G)
    (p : ℕ)
    (w : CWord HPAtom) :
    specialize x y
        (w.eval
          (HPAtom.eval universalLeft (universalRight ^ p))) =
      w.eval (HPAtom.eval x (y ^ p)) := by
  rw [CWord.map_eval]
  congr 1
  funext a
  cases a <;> simp [HPAtom.eval]

/-- The universal source value whose certified collection is required by a
right-prime natural successor kernel. -/
def universalSourceValue
    (p : ℕ)
    (w : CWord HPAtom)
    (n : ℕ) :
    UniversalGroup :=
  w.eval
      (HPAtom.eval universalLeft (universalRight ^ p)) ^
    ((n + 1 : ℕ) : ℤ)

/-- A pending batch in the universal free group for one fixed source word and
source multiplicity. -/
abbrev UPBatch
    (p : ℕ) [Fact p.Prime]
    (w : CWord HPAtom)
    (n : ℕ) :=
  KernelPendingBatch p universalLeft universalRight w n

/-!
### Budget-bearing universal pass

The geometric pending-batch record keeps exact collection order and strict
weight descent.  The records below add the coefficient provenance required by
the public successor kernel.  They deliberately describe only the concrete
optional batch emitted by one selected initial Hall pass.
-/

namespace UPBatch

/-- Forget the weighted-subgroup wrapper on one pending pairwise error while
preserving its exact group evaluation. -/
def rawFactorError
    {p : ℕ} [Fact p.Prime]
    {w : CWord HPAtom}
    {n : ℕ}
    (E :
      PError p universalLeft universalRight
        (kernelCutoff p w n)) :
    RFactor UniversalGroup where
  word :=
    E.factor.word
  multiplicity :=
    ((p ^ E.factor.primeExponent : ℕ) : ℤ) *
      E.factor.multiplicity
  conjugator :=
    E.factor.conjugator

/-- The raw view of one pending error has exactly the weighted-wrapper
evaluation. -/
lemma raw_factor_error
    {p : ℕ} [Fact p.Prime]
    {w : CWord HPAtom}
    {n : ℕ}
    (E :
      PError p universalLeft universalRight
        (kernelCutoff p w n)) :
    (rawFactorError E).eval universalLeft universalRight =
      E.eval := by
  simp [rawFactorError, PError.eval,
    WCFactor.eval, RFactor.eval, zpow_mul]
  norm_cast

/-- Convert an ordered pending batch to the exact ordered raw-factor list it
represents. -/
def rawFactors
    {p : ℕ} [Fact p.Prime]
    {w : CWord HPAtom}
    {n : ℕ}
    (B : UPBatch p w n) :
    List (RFactor UniversalGroup) :=
  B.errors.map rawFactorError

/-- Membership in the raw view comes from one exact pending error. -/
lemma raw_factors
    {p : ℕ} [Fact p.Prime]
    {w : CWord HPAtom}
    {n : ℕ}
    (B : UPBatch p w n)
    (F : RFactor UniversalGroup) :
    F ∈ B.rawFactors ↔
      ∃ E ∈ B.errors, rawFactorError E = F := by
  simp [rawFactors]

/-- Converting a pending batch to raw factors does not change its ordered
free-group product. -/
lemma list_raw_factors
    {p : ℕ} [Fact p.Prime]
    {w : CWord HPAtom}
    {n : ℕ}
    (B : UPBatch p w n) :
    PPColl.listEval
        universalLeft universalRight B.rawFactors =
      B.eval := by
  change
    PPColl.listEval universalLeft universalRight
        (B.errors.map rawFactorError) =
      errorListEval B.errors
  induction B.errors with
  | nil =>
      rfl
  | cons E L ih =>
      change
        (rawFactorError E).eval universalLeft universalRight *
            PPColl.listEval
              universalLeft universalRight (L.map rawFactorError) =
          E.eval * errorListEval L
      rw [raw_factor_error, ih]

end UPBatch

/-- The coefficient budget missing from a purely geometric pending batch. -/
structure UPBudget
    {p : ℕ} [Fact p.Prime]
    (w : CWord HPAtom)
    (n : ℕ)
    (B : UPBatch p w n) :
    Prop where
  factor_certificate :
    ∀ E ∈ B.errors,
      NSCert p w n
        (UPBatch.rawFactorError E)

namespace UPBudget

/-- Read the certificate attached to one represented pending error. -/
lemma certificate_errors
    {p : ℕ} [Fact p.Prime]
    {w : CWord HPAtom}
    {n : ℕ}
    {B : UPBatch p w n}
    (hB : UPBudget w n B)
    (E :
      PError p universalLeft universalRight
        (kernelCutoff p w n))
    (hE : E ∈ B.errors) :
    NSCert p w n
      (UPBatch.rawFactorError E) :=
  hB.factor_certificate E hE

/-- A batch budget induces certificates on its exact ordered raw-factor
view. -/
lemma certif_raw_facto
    {p : ℕ} [Fact p.Prime]
    {w : CWord HPAtom}
    {n : ℕ}
    {B : UPBatch p w n}
    (hB : UPBudget w n B) :
    ∀ F ∈ B.rawFactors,
      NSCert p w n F := by
  intro F hF
  rcases (B.raw_factors F).mp hF with ⟨E, hE, rfl⟩
  exact hB.certificate_errors E hE

end UPBudget

/-- A collectable pending task is a diagnostic batch plus its coefficient
budget. -/
structure UPTask
    (p : ℕ) [Fact p.Prime]
    (w : CWord HPAtom)
    (n : ℕ) where
  batch :
    UPBatch p w n
  budget :
    UPBudget w n batch

/-- The ordered raw output of the first aggregate Hall traversal. -/
structure URPass
    (p : ℕ) [Fact p.Prime]
    (w : CWord HPAtom)
    (n : ℕ) where
  pending :
    Option (UPBatch p w n)
  admitted :
    List (RFactor UniversalGroup)
  eval_eq :
    pendingEval pending *
        PPColl.listEval
          universalLeft universalRight admitted =
      universalSourceValue p w n

namespace URPass

/-- Pointwise arithmetic certification for the raw admitted suffix. -/
def SuffixCertified
    {p : ℕ} [Fact p.Prime]
    {w : CWord HPAtom}
    {n : ℕ}
    (P : URPass p w n) :
    Prop :=
  ∀ E ∈ P.admitted,
    NSCert p w n E

/-- Arithmetic certification for the concrete optional pending prefix. -/
def PendingCertified
    {p : ℕ} [Fact p.Prime]
    {w : CWord HPAtom}
    {n : ℕ}
    (P : URPass p w n) :
    Prop :=
  ∀ B, P.pending = some B →
    UPBudget w n B

/-- Flatten the concrete optional pending prefix and the admitted suffix in
their original noncommutative order. -/
def rawFactors
    {p : ℕ} [Fact p.Prime]
    {w : CWord HPAtom}
    {n : ℕ}
    (P : URPass p w n) :
    List (RFactor UniversalGroup) :=
  match P.pending with
  | none =>
      P.admitted
  | some B =>
      B.rawFactors ++ P.admitted

/-- Flattening a raw first pass preserves its universal free-group value. -/
lemma list_raw_factors
    {p : ℕ} [Fact p.Prime]
    {w : CWord HPAtom}
    {n : ℕ}
    (P : URPass p w n) :
    PPColl.listEval
        universalLeft universalRight P.rawFactors =
      universalSourceValue p w n := by
  cases hPending : P.pending with
  | none =>
      simpa [rawFactors, hPending, pendingEval] using P.eval_eq
  | some B =>
      rw [rawFactors, hPending,
        PPColl.listEval_append,
        UPBatch.list_raw_factors]
      simpa [pendingEval, hPending] using P.eval_eq

/-- Flattening a certified raw first pass preserves every pointwise successor
certificate. -/
lemma certif_raw_facto
    {p : ℕ} [Fact p.Prime]
    {w : CWord HPAtom}
    {n : ℕ}
    (P : URPass p w n)
    (hSuffix : P.SuffixCertified)
    (hPending : P.PendingCertified) :
    ∀ E ∈ P.rawFactors,
      NSCert p w n E := by
  intro E hE
  cases hpending : P.pending with
  | none =>
      exact hSuffix E (by simpa [rawFactors, hpending] using hE)
  | some B =>
      rcases (by simpa [rawFactors, hpending] using hE) with hE | hE
      · exact (hPending B hpending).certif_raw_facto E hE
      · exact hSuffix E hE

/-- Flattening a certified raw first pass produces the exact list certificate
consumed by the public boundary. -/
def listCertificate
    {p : ℕ} [Fact p.Prime]
    {w : CWord HPAtom}
    {n : ℕ}
    (P : URPass p w n)
    (hSuffix : P.SuffixCertified)
    (hPending : P.PendingCertified) :
    RSCertb p w n P.rawFactors :=
  ⟨P.certif_raw_facto hSuffix hPending⟩

end URPass

/-
### Normal-closure reduction

The final certified list can be extracted after proving membership in the
normal closure generated by certified factors.  This isolates the remaining
Hall-combinatorial argument from list packaging and keeps products, inverses,
and conjugates correlated until the last step.
-/

/-- Construct a certified initial pass from one exact certified list. -/
lemma certified_pass_list
    (p : ℕ) [Fact p.Prime]
    (w : CWord HPAtom)
    (n : ℕ)
    (h :
      ∃ L : List (RFactor UniversalGroup),
        pendingEval (p := p) (x := universalLeft) (y := universalRight)
            (w := w) (n := n) none *
            PPColl.listEval universalLeft universalRight L =
          universalSourceValue p w n ∧
        ∀ E ∈ L, NSCert p w n E) :
    ∃ P : URPass p w n,
      P.SuffixCertified ∧ P.PendingCertified := by
  obtain ⟨L, hEval, hCert⟩ := h
  refine ⟨{
    pending := none
    admitted := L
    eval_eq := hEval
  }, ?_, ?_⟩
  · exact hCert
  · intro B hB
    simp at hB

/-- A certified initial pass is equivalent to one exact certified universal
factor list. -/
lemma certified_pass_universal
    (p : ℕ) [Fact p.Prime]
    (w : CWord HPAtom)
    (n : ℕ) :
    (∃ P : URPass p w n,
        P.SuffixCertified ∧ P.PendingCertified) ↔
      ∃ L : List (RFactor UniversalGroup),
        PPColl.listEval universalLeft universalRight L =
            universalSourceValue p w n ∧
          RSCertb p w n L := by
  constructor
  · rintro ⟨P, hSuffix, hPending⟩
    exact
      ⟨P.rawFactors, P.list_raw_factors,
        P.listCertificate hSuffix hPending⟩
  · rintro ⟨L, hEval, hCert⟩
    refine ⟨{
      pending := none
      admitted := L
      eval_eq := by
        simpa [pendingEval] using hEval
    }, ?_, ?_⟩
    · exact hCert.factor_certificate
    · intro B hB
      simp at hB

namespace CNClos

/-- Evaluations of normalized successor-certified factors. -/
def generatorSet
    (p : ℕ)
    (w : CWord HPAtom)
    (n : ℕ) :
    Set UniversalGroup :=
  { g |
    ∃ E : RFactor UniversalGroup,
      E.conjugator = 1 ∧
        NSCert p w n E ∧
          E.eval universalLeft universalRight = g }

/-- The normal closure generated by normalized successor-certified factors. -/
def subgroup
    (p : ℕ)
    (w : CWord HPAtom)
    (n : ℕ) :
    Subgroup UniversalGroup :=
  Subgroup.normalClosure (generatorSet p w n)

instance subgro_normal
    (p : ℕ)
    (w : CWord HPAtom)
    (n : ℕ) :
    (subgroup p w n).Normal :=
  Subgroup.normalClosure_normal

/-- Every successor-certified raw factor belongs to the certified normal
closure, including factors with an arbitrary outer conjugator. -/
lemma eval_mem
    {p : ℕ}
    {w : CWord HPAtom}
    {n : ℕ}
    (E : RFactor UniversalGroup)
    (hE : NSCert p w n E) :
    E.eval universalLeft universalRight ∈ subgroup p w n := by
  have hbase :
      ({ E with conjugator := 1 } : RFactor UniversalGroup).eval
          universalLeft universalRight ∈ subgroup p w n := by
    apply Subgroup.subset_normalClosure
    exact ⟨{ E with conjugator := 1 }, rfl, {
      positivity := {
        left_degree_pos := by
          simpa using hE.positivity.left_degree_pos
        right_degree_pos := by
          simpa using hE.positivity.right_degree_pos }
      divisibility := {
        left_dvd := by
          simpa using hE.left_dvd
        right_dvd := by
          simpa using hE.right_dvd } }, rfl⟩
  simpa [RFactor.eval] using
    (inferInstance : (subgroup p w n).Normal).conj_mem
      (({ E with conjugator := 1 } : RFactor UniversalGroup).eval
        universalLeft universalRight)
      hbase E.conjugator

/-- Integral powers of a certified raw-factor evaluation remain in the
certified normal closure. -/
lemma zpow_eval_mem
    {p : ℕ}
    {w : CWord HPAtom}
    {n : ℕ}
    {E : RFactor UniversalGroup}
    (hE : NSCert p w n E)
    (c : ℤ) :
    (E.eval universalLeft universalRight) ^ c ∈ subgroup p w n :=
  (subgroup p w n).zpow_mem (eval_mem E hE) c

/-- A bare Hall-word power with the required coordinatewise divisibility
belongs to the certified normal closure. -/
lemma zpow_word_eval
    {p : ℕ}
    {w : CWord HPAtom}
    {n : ℕ}
    (u : CWord HPAtom)
    (c : ℤ)
    (hpositive : u.PBPos)
    (hleft :
      (w.pairLeftDegree : ℤ) * ((n + 1 : ℕ) : ℤ) ∣
        (u.pairLeftDegree : ℤ) * c)
    (hright :
      (p : ℤ) * ((w.pairRightDegree : ℤ) * ((n + 1 : ℕ) : ℤ)) ∣
        (u.pairRightDegree : ℤ) * c) :
    u.eval (HPAtom.eval universalLeft universalRight) ^ c ∈
      subgroup p w n := by
  let E : RFactor UniversalGroup := {
    word := u
    multiplicity := c
    conjugator := 1
  }
  have hE : NSCert p w n E := {
    positivity := {
      left_degree_pos := hpositive.left
      right_degree_pos := hpositive.right }
    divisibility := {
      left_dvd := hleft
      right_dvd := hright } }
  simpa [E, RFactor.eval] using eval_mem E hE

/-- The certified normal closure absorbs commutators with a certified left
input. -/
lemma commutator_mem_left
    {p : ℕ}
    {w : CWord HPAtom}
    {n : ℕ}
    {a : UniversalGroup}
    (ha : a ∈ subgroup p w n)
    (b : UniversalGroup) :
    ⁅a, b⁆ ∈ subgroup p w n := by
  exact
    Subgroup.commutator_le_left (subgroup p w n) ⊤
      (Subgroup.commutator_mem_commutator
        ha
        (Subgroup.mem_top b))

/-- The certified normal closure absorbs commutators with a certified right
input. -/
lemma commutator_mem_right
    {p : ℕ}
    {w : CWord HPAtom}
    {n : ℕ}
    (a : UniversalGroup)
    {b : UniversalGroup}
    (hb : b ∈ subgroup p w n) :
    ⁅a, b⁆ ∈ subgroup p w n := by
  exact
    Subgroup.commutator_le_right ⊤ (subgroup p w n)
      (Subgroup.commutator_mem_commutator
        (Subgroup.mem_top a)
        hb)

/-- Inverting a raw factor preserves its successor certificate. -/
lemma certificate_inv
    {p : ℕ}
    {w : CWord HPAtom}
    {n : ℕ}
    {E : RFactor UniversalGroup}
    (hE : NSCert p w n E) :
    NSCert p w n E.inv := by
  exact {
    positivity := {
      left_degree_pos := by
        simpa [RFactor.inv] using hE.positivity.left_degree_pos
      right_degree_pos := by
        simpa [RFactor.inv] using hE.positivity.right_degree_pos }
    divisibility := {
      left_dvd := by
        simpa [RFactor.inv] using hE.left_dvd
      right_dvd := by
        simpa [RFactor.inv] using hE.right_dvd } }

/-- Conjugating a raw factor preserves its successor certificate. -/
lemma certificate_conjugate
    {p : ℕ}
    {w : CWord HPAtom}
    {n : ℕ}
    {E : RFactor UniversalGroup}
    (hE : NSCert p w n E)
    (q : UniversalGroup) :
    NSCert p w n (E.conjugate q) := by
  exact {
    positivity := {
      left_degree_pos := by
        simpa [RFactor.conjugate] using hE.positivity.left_degree_pos
      right_degree_pos := by
        simpa [RFactor.conjugate] using hE.positivity.right_degree_pos }
    divisibility := {
      left_dvd := by
        simpa [RFactor.conjugate] using hE.left_dvd
      right_dvd := by
        simpa [RFactor.conjugate] using hE.right_dvd } }

/-- Reversing and inverting a certified raw-factor list preserves every
certificate. -/
lemma forall_certificate_inv
    {p : ℕ}
    {w : CWord HPAtom}
    {n : ℕ}
    {L : List (RFactor UniversalGroup)}
    (hL : ∀ E ∈ L, NSCert p w n E) :
    ∀ E ∈ PPColl.listInv L,
      NSCert p w n E := by
  revert hL
  induction L with
  | nil =>
      simp [PPColl.listInv]
  | cons D L ih =>
      intro hL E hE
      rw [PPColl.listInv, List.mem_append,
        List.mem_singleton] at hE
      rcases hE with hE | rfl
      · exact ih (fun F hF => hL F (List.mem_cons_of_mem D hF)) E hE
      · exact certificate_inv (hL D List.mem_cons_self)

/-- Membership in the certified normal closure can be extracted as an exact
ordered certified factor list. -/
lemma list_eval
    {p : ℕ}
    {w : CWord HPAtom}
    {n : ℕ}
    {g : UniversalGroup}
    (hg : g ∈ subgroup p w n) :
    ∃ L : List (RFactor UniversalGroup),
      PPColl.listEval universalLeft universalRight L = g ∧
        ∀ E ∈ L, NSCert p w n E := by
  change
    g ∈ Subgroup.closure (Group.conjugatesOfSet (generatorSet p w n)) at hg
  induction hg using Subgroup.closure_induction with
  | mem z hz =>
      rcases Group.mem_conjugatesOfSet_iff.mp hz with ⟨x, hx, hconj⟩
      rcases hx with ⟨E, hEone, hEcert, hEval⟩
      rcases isConj_iff.mp hconj with ⟨q, rfl⟩
      refine ⟨[E.conjugate q], ?_, ?_⟩
      · simp [hEval]
      · intro D hD
        simp only [List.mem_singleton] at hD
        subst D
        exact certificate_conjugate hEcert q
  | one =>
      exact ⟨[], rfl, by simp⟩
  | mul x y _hx _hy ihx ihy =>
      rcases ihx with ⟨L, hL, hLcert⟩
      rcases ihy with ⟨M, hM, hMcert⟩
      refine ⟨L ++ M, by simp [hL, hM], ?_⟩
      intro E hE
      rcases List.mem_append.mp hE with hE | hE
      · exact hLcert E hE
      · exact hMcert E hE
  | inv x _hx ih =>
      rcases ih with ⟨L, hL, hLcert⟩
      exact
        ⟨PPColl.listInv L, by simp [hL],
          forall_certificate_inv hLcert⟩

/-- Certified normal-closure membership of the source value is enough to
construct the required initial pass. -/
lemma certified_pass_source
    (p : ℕ) [Fact p.Prime]
    (w : CWord HPAtom)
    (n : ℕ)
    (hsource : universalSourceValue p w n ∈ subgroup p w n) :
    ∃ P : URPass p w n,
      P.SuffixCertified ∧ P.PendingCertified := by
  rcases list_eval hsource with ⟨L, hL, hLcert⟩
  apply certified_pass_list p w n
  exact ⟨L, by simpa [pendingEval] using hL, hLcert⟩

end CNClos

/-
The next presentation forgets the fixed source word and packages only the two
coordinate divisors.  Its endomorphism transport statement is the remaining
generator-level Hall-Petresco obligation.
-/
namespace BNClos

/-- Evaluated positive Hall-word powers satisfying two coordinate divisors. -/
def generatorSet
    (A B : ℤ) :
    Set UniversalGroup :=
  { g |
    ∃ u : CWord HPAtom, ∃ c : ℤ,
      u.PBPos ∧
        A ∣ (u.pairLeftDegree : ℤ) * c ∧
          B ∣ (u.pairRightDegree : ℤ) * c ∧
            u.eval (HPAtom.eval universalLeft universalRight) ^ c = g }

/-- Normal closure of bidegree-divisible positive Hall-word powers. -/
def subgroup
    (A B : ℤ) :
    Subgroup UniversalGroup :=
  Subgroup.normalClosure (generatorSet A B)

instance subgro_normal
    (A B : ℤ) :
    (subgroup A B).Normal :=
  Subgroup.normalClosure_normal

/-- One bidegree-divisible Hall-word power belongs to its normal closure. -/
lemma zpow_word_eval
    {A B : ℤ}
    (u : CWord HPAtom)
    (c : ℤ)
    (hpositive : u.PBPos)
    (hleft : A ∣ (u.pairLeftDegree : ℤ) * c)
    (hright : B ∣ (u.pairRightDegree : ℤ) * c) :
    u.eval (HPAtom.eval universalLeft universalRight) ^ c ∈
      subgroup A B := by
  apply Subgroup.subset_normalClosure
  exact ⟨u, c, hpositive, hleft, hright, rfl⟩

/-- Universal free-group endomorphism implementing the substitution
`right ↦ right ^ p`. -/
def rightPrimeHom
    (p : ℕ) :
    UniversalGroup →* UniversalGroup :=
  FreeGroup.lift (HPAtom.eval universalLeft (universalRight ^ p))

@[simp]
lemma right_universal_left
    (p : ℕ) :
    rightPrimeHom p universalLeft = universalLeft := by
  simp [rightPrimeHom, universalLeft, HPAtom.eval]

@[simp]
lemma right_hom_universal
    (p : ℕ) :
    rightPrimeHom p universalRight = universalRight ^ p := by
  simp [rightPrimeHom, universalRight, HPAtom.eval]

/-- Applying the right-prime endomorphism to an evaluated Hall word performs
right-prime substitution in its alphabet. -/
lemma right_hom_eval
    (p : ℕ)
    (u : CWord HPAtom) :
    rightPrimeHom p
        (u.eval (HPAtom.eval universalLeft universalRight)) =
      u.eval (HPAtom.eval universalLeft (universalRight ^ p)) := by
  rw [CWord.map_eval]
  congr 1
  funext a
  cases a <;> simp [HPAtom.eval]

/-- The universal source is a right-prime endomorphic image. -/
lemma source_right_hom
    (p : ℕ)
    (w : CWord HPAtom)
    (n : ℕ) :
    universalSourceValue p w n =
      rightPrimeHom p
        (w.eval (HPAtom.eval universalLeft universalRight) ^
          ((n + 1 : ℕ) : ℤ)) := by
  simp [universalSourceValue, map_zpow, right_hom_eval]

/-- The unsubstituted source power belongs to the bidegree normal closure
defined by its own two coordinates. -/
lemma base_mem
    (w : CWord HPAtom)
    (hw : w.PBPos)
    (n : ℕ) :
    w.eval (HPAtom.eval universalLeft universalRight) ^
        ((n + 1 : ℕ) : ℤ) ∈
      subgroup
        ((w.pairLeftDegree : ℤ) * ((n + 1 : ℕ) : ℤ))
        ((w.pairRightDegree : ℤ) * ((n + 1 : ℕ) : ℤ)) := by
  apply zpow_word_eval w ((n + 1 : ℕ) : ℤ) hw
  · exact dvd_refl _
  · exact dvd_refl _

/-- To transport a bidegree normal closure through right-prime substitution,
it suffices to transport each normalized generator. -/
lemma right_hom_generator
    (p : ℕ)
    {A B : ℤ}
    (hgenerator :
      ∀ (u : CWord HPAtom) (c : ℤ),
        u.PBPos →
          A ∣ (u.pairLeftDegree : ℤ) * c →
            B ∣ (u.pairRightDegree : ℤ) * c →
              rightPrimeHom p
                  (u.eval
                      (HPAtom.eval universalLeft universalRight) ^ c) ∈
                subgroup A ((p : ℤ) * B)) :
    ∀ {g : UniversalGroup},
      g ∈ subgroup A B →
        rightPrimeHom p g ∈ subgroup A ((p : ℤ) * B) := by
  intro g hg
  change
    g ∈
      Subgroup.closure
        (Group.conjugatesOfSet (generatorSet A B)) at hg
  induction hg using Subgroup.closure_induction with
  | mem z hz =>
      rcases Group.mem_conjugatesOfSet_iff.mp hz with ⟨x, hx, hconj⟩
      rcases hx with ⟨u, c, hpositive, hleft, hright, rfl⟩
      rcases isConj_iff.mp hconj with ⟨q, rfl⟩
      simpa only [map_mul, map_inv] using
        (inferInstance : (subgroup A ((p : ℤ) * B)).Normal).conj_mem
          (rightPrimeHom p
            (u.eval
                (HPAtom.eval universalLeft universalRight) ^ c))
          (hgenerator u c hpositive hleft hright)
          (rightPrimeHom p q)
  | one =>
      simp
  | mul x y _hx _hy ihx ihy =>
      simpa only [map_mul] using
        (subgroup A ((p : ℤ) * B)).mul_mem ihx ihy
  | inv x _hx ih =>
      simpa only [map_inv] using
        (subgroup A ((p : ℤ) * B)).inv_mem ih

end BNClos

/-- The fixed successor-certificate normal closure is the corresponding
bidegree-divisibility normal closure. -/
lemma certified_closure_bidegree
    (p : ℕ)
    (w : CWord HPAtom)
    (n : ℕ) :
    CNClos.subgroup p w n =
      BNClos.subgroup
        ((w.pairLeftDegree : ℤ) * ((n + 1 : ℕ) : ℤ))
        ((p : ℤ) * ((w.pairRightDegree : ℤ) * ((n + 1 : ℕ) : ℤ))) := by
  apply congrArg Subgroup.normalClosure
  ext g
  constructor
  · rintro ⟨E, hEone, hEcert, hEval⟩
    exact
      ⟨E.word, E.multiplicity, hEcert.target_positive, hEcert.left_dvd,
        hEcert.right_dvd, by simpa [RFactor.eval, hEone] using hEval⟩
  · rintro ⟨u, c, hpositive, hleft, hright, hEval⟩
    let E : RFactor UniversalGroup := {
      word := u
      multiplicity := c
      conjugator := 1
    }
    exact ⟨E, rfl, {
      positivity := {
        left_degree_pos := hpositive.left
        right_degree_pos := hpositive.right }
      divisibility := {
        left_dvd := hleft
        right_dvd := hright } }, by simpa [E, RFactor.eval] using hEval⟩

/-- The initial-pass theorem follows from stability of the bidegree normal
closure under right-prime substitution. -/
lemma certified_raw_pass
    (p : ℕ) [Fact p.Prime]
    (w : CWord HPAtom)
    (hw : w.PBPos)
    (n : ℕ)
    (htransport :
      ∀ {A B : ℤ} {g : UniversalGroup},
        g ∈ BNClos.subgroup A B →
          BNClos.rightPrimeHom p g ∈
            BNClos.subgroup A ((p : ℤ) * B)) :
    ∃ P : URPass p w n,
      P.SuffixCertified ∧ P.PendingCertified := by
  apply CNClos.certified_pass_source p w n
  rw [certified_closure_bidegree]
  rw [BNClos.source_right_hom]
  exact htransport (BNClos.base_mem w hw n)

/--
One universal aggregate Hall witness for a normalized successor source.

The `factors` field is the final collection list in the free group.  Its
evaluation identity and its arithmetic list certificate are stored together,
so specialization cannot choose a different list for the group identity and
for coefficient divisibility.
-/
structure FAggreg
    (p : ℕ)
    (w : CWord HPAtom)
    (n : ℕ) where
  factors :
    List (RFactor UniversalGroup)
  eval_eq :
    listEval universalLeft universalRight factors =
      w.eval
          (HPAtom.eval universalLeft (universalRight ^ p)) ^
        ((n + 1 : ℕ) : ℤ)
  factors_certificate :
    RSCertb p w n factors

namespace FAggreg

/-- Read the universal free-group identity carried by an aggregate witness. -/
lemma eval_factors
    {p : ℕ}
    {w : CWord HPAtom}
    {n : ℕ}
    (A : FAggreg p w n) :
    listEval universalLeft universalRight A.factors =
      w.eval
          (HPAtom.eval universalLeft (universalRight ^ p)) ^
        ((n + 1 : ℕ) : ℤ) :=
  A.eval_eq

/-- Read the exact list certificate carried by a universal aggregate
witness. -/
lemma factor_certificate
    {p : ℕ}
    {w : CWord HPAtom}
    {n : ℕ}
    (A : FAggreg p w n)
    {E : RFactor UniversalGroup}
    (hE : E ∈ A.factors) :
    NSCert p w n E :=
  A.factors_certificate.factor hE

/-- Every universal aggregate factor has positive left Hall-pair degree. -/
lemma factor_left_pos
    {p : ℕ}
    {w : CWord HPAtom}
    {n : ℕ}
    (A : FAggreg p w n) :
    ∀ E ∈ A.factors, 0 < E.word.pairLeftDegree :=
  A.factors_certificate.leftDegree_pos

/-- Every universal aggregate factor has positive right Hall-pair degree. -/
lemma factor_degree_pos
    {p : ℕ}
    {w : CWord HPAtom}
    {n : ℕ}
    (A : FAggreg p w n) :
    ∀ E ∈ A.factors, 0 < E.word.pairRightDegree :=
  A.factors_certificate.rightDegree_pos

/-- Every universal aggregate factor inherits the left-coordinate
divisibility required by the successor kernel. -/
lemma factor_left_dvd
    {p : ℕ}
    {w : CWord HPAtom}
    {n : ℕ}
    (A : FAggreg p w n) :
    ∀ E ∈ A.factors,
      (w.pairLeftDegree : ℤ) * ((n + 1 : ℕ) : ℤ) ∣
        (E.word.pairLeftDegree : ℤ) * E.multiplicity :=
  A.factors_certificate.forall_left_dvd

/-- Every universal aggregate factor gains the right-prime divisibility
required by the successor kernel. -/
lemma factor_right_dvd
    {p : ℕ}
    {w : CWord HPAtom}
    {n : ℕ}
    (A : FAggreg p w n) :
    ∀ E ∈ A.factors,
      (p : ℤ) * ((w.pairRightDegree : ℤ) * ((n + 1 : ℕ) : ℤ)) ∣
        (E.word.pairRightDegree : ℤ) * E.multiplicity :=
  A.factors_certificate.forall_right_dvd

/-- Forget the aggregate packaging and expose the universal successor
kernel. -/
def toUniversalKernel
    {p : ℕ}
    {w : CWord HPAtom}
    {n : ℕ}
    (A : FAggreg p w n) :
    NSKern p universalLeft universalRight w n where
  factors := A.factors
  eval_eq := A.eval_eq
  factors_certificate := A.factors_certificate

/-- Specialize the universal aggregate factor list to an arbitrary group.

The same ordered list is used after applying `FreeGroup.lift`; its
conjugators are mapped, while its Hall words and multiplicities remain
unchanged. -/
def specializeKernel
    {p : ℕ}
    {G : Type*} [Group G]
    (w : CWord HPAtom)
    {n : ℕ}
    (A : FAggreg p w n)
    (x y : G) :
    NSKern p x y w n where
  factors :=
    RFactor.listMapHom (specialize x y) A.factors
  eval_eq := by
    calc
      listEval x y (RFactor.listMapHom (specialize x y) A.factors) =
          listEval
            ((specialize x y) universalLeft)
            ((specialize x y) universalRight)
            (RFactor.listMapHom (specialize x y) A.factors) := by
        simp
      _ = specialize x y (listEval universalLeft universalRight A.factors) := by
        rw [RFactor.list_eval_hom]
      _ =
          specialize x y
            (w.eval
                (HPAtom.eval universalLeft (universalRight ^ p)) ^
              ((n + 1 : ℕ) : ℤ)) := by
        rw [A.eval_eq]
      _ = w.eval (HPAtom.eval x (y ^ p)) ^ ((n + 1 : ℕ) : ℤ) := by
        rw [map_zpow, specialize_right_prime]
  factors_certificate :=
    A.factors_certificate.mapHom (specialize x y)

/-- Specialization preserves the exact factor-list evaluation identity. -/
lemma specia_list_facto
    {p : ℕ}
    {G : Type*} [Group G]
    (w : CWord HPAtom)
    {n : ℕ}
    (A : FAggreg p w n)
    (x y : G) :
    listEval x y (A.specializeKernel w x y).factors =
      w.eval (HPAtom.eval x (y ^ p)) ^ ((n + 1 : ℕ) : ℤ) :=
  (A.specializeKernel w x y).eval_eq

/-- Specialization preserves the exact factor-list arithmetic
certificate. -/
lemma specia_facto_certi
    {p : ℕ}
    {G : Type*} [Group G]
    (w : CWord HPAtom)
    {n : ℕ}
    (A : FAggreg p w n)
    (x y : G)
    {E : RFactor G}
    (hE : E ∈ (A.specializeKernel w x y).factors) :
    NSCert p w n E :=
  (A.specializeKernel w x y).factor_certificate hE

end FAggreg

/-
### Traced universal first pass

The raw-orbit adapters above isolate the geometric unit of work.  The final
universal traversal still has two independent responsibilities:

* assemble honest local orbit splits into one exact source identity;
* compose the retained choose indices and pairwise-error origins into the
  scalar successor certificates.

The trace below keeps these responsibilities separate.  In particular, the
geometric trace contains no coefficient certificate, and the two arithmetic
leaves do not construct a group identity.
-/

/-- One honest raw local split used by a universal first traversal.

The witness fixes the aggregate cutoff to the source kernel cutoff, so every
pending batch can be compared directly with the optional batch stored in the
eventual universal first pass. -/
structure USWitnes
    (p : ℕ) [Fact p.Prime]
    (w : CWord HPAtom)
    (n : ℕ) where
  left :
    CWord HPAtom
  right :
    CWord HPAtom
  exponent :
    ℕ
  parent_below :
    left.weight (weight p) + right.weight (weight p) <
      kernelCutoff p w n
  split :
    ROSplit p universalLeft universalRight left right exponent
      (kernelCutoff p w n)

namespace USWitnes

/-- Read the exact orbit identity carried by one local universal split. -/
lemma pending_mul_admitted
    {p : ℕ} [Fact p.Prime]
    {w : CWord HPAtom}
    {n : ℕ}
    (S : USWitnes p w n) :
    S.split.pending.eval *
        PPColl.listEval
          universalLeft universalRight S.split.admitted =
      leftConjugateProduct
        (S.left.eval (HPAtom.eval universalLeft universalRight))
        ⁅S.left.eval (HPAtom.eval universalLeft universalRight),
          S.right.eval (HPAtom.eval universalLeft universalRight)⁆
        (p ^ S.exponent) :=
  S.split.eval_eq

/-- The pending prefix of one local universal split stays below the source
kernel cutoff. -/
lemma pending_parentBelow
    {p : ℕ} [Fact p.Prime]
    {w : CWord HPAtom}
    {n : ℕ}
    (S : USWitnes p w n) :
    S.split.pending.left.weight (weight p) +
        S.split.pending.right.weight (weight p) <
      kernelCutoff p w n :=
  S.split.pending.parentBelow

/-- Every pending member of one local universal split descends strictly
below its common parent measure. -/
lemma pendin_child_measu
    {p : ℕ} [Fact p.Prime]
    {w : CWord HPAtom}
    {n : ℕ}
    (S : USWitnes p w n)
    (E :
      PError p universalLeft universalRight
        (kernelCutoff p w n))
    (hE : E ∈ S.split.pending.errors) :
    E.childMeasure < S.split.pending.measure :=
  S.split.pending.child_measure E hE

end USWitnes

/-- A geometric universal first-pass traversal with explicit local orbit
provenance.

This record contains the exact first-pass identity through `pass`, together
with local split origins for both retained pieces.  It deliberately carries
no successor coefficient certificate. -/
structure URTraver
    (p : ℕ) [Fact p.Prime]
    (w : CWord HPAtom)
    (n : ℕ) where
  pass :
    URPass p w n
  localSplits :
    List (USWitnes p w n)
  admitted_from_local :
    ∀ F ∈ pass.admitted,
      ∃ S ∈ localSplits, F ∈ S.split.admitted
  pending_from_local :
    ∀ B, pass.pending = some B →
      ∃ S ∈ localSplits, S.split.pending = B

namespace URTraver

/-- Read the exact universal source identity retained by a traced first
pass. -/
lemma pending_mul_admitted
    {p : ℕ} [Fact p.Prime]
    {w : CWord HPAtom}
    {n : ℕ}
    (T : URTraver p w n) :
    pendingEval T.pass.pending *
        PPColl.listEval
          universalLeft universalRight T.pass.admitted =
      universalSourceValue p w n :=
  T.pass.eval_eq

/-- Locate one admitted raw suffix factor in an honest local orbit split. -/
lemma local_split_admitted
    {p : ℕ} [Fact p.Prime]
    {w : CWord HPAtom}
    {n : ℕ}
    (T : URTraver p w n)
    (F : RFactor UniversalGroup)
    (hF : F ∈ T.pass.admitted) :
    ∃ S ∈ T.localSplits, F ∈ S.split.admitted :=
  T.admitted_from_local F hF

/-- Locate the concrete optional pending prefix in the honest local orbit
split that emitted it. -/
lemma split_pending_some
    {p : ℕ} [Fact p.Prime]
    {w : CWord HPAtom}
    {n : ℕ}
    (T : URTraver p w n)
    (B : UPBatch p w n)
    (hB : T.pass.pending = some B) :
    ∃ S ∈ T.localSplits, S.split.pending = B :=
  T.pending_from_local B hB

end URTraver


end RPAggreg
end RCColl
end PPColl
end Towers
