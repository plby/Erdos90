import Towers.Group.Zassenhaus.PGroupCore
import Towers.Group.HallBasic.Word
import Mathlib.GroupTheory.FreeGroup.GeneratorEquiv
import Mathlib.RingTheory.Binomial

namespace Towers

universe u

open scoped commutatorElement IsMulCommutative

-- Lean 4.30's unbundled commutativity instances take longer to resolve for the
-- nested lower-central subgroups and quotients used throughout this file.

namespace TCTex

/--
The TeX proof works with "at most `k` normalized values" before the final
padding step turns that list into a fixed repeated schedule.  This predicate is
the local list-level form used below to keep the quotient lift and residual
completion statements readable.
-/
def BNZass
    (p d n k : ℕ) [Fact p.Prime]
    {G : Type u} [Group G]
    (x : G) :
    Prop :=
  ∃ L : List (BSValue p d n G),
    L.length ≤ k ∧
      (L.map BSValue.eval).prod = x

/--
The empty normalized list is the bound-zero witness for the identity.  This is
the list-level identity padding used implicitly in TeX Lemma 15.
-/
lemma bounded_normalized_one
    (p d n : ℕ) [Fact p.Prime]
    {G : Type u} [Group G] :
    BNZass p d n 0 (1 : G) := by
  exact ⟨[], by simp⟩

/--
Concatenating two normalized lists adds their length budgets and multiplies
their evaluated products in the same order.
-/
lemma BNZass.mul
    {p d n k l : ℕ} [Fact p.Prime]
    {G : Type u} [Group G]
    {x y : G}
    (hx : BNZass p d n k x)
    (hy : BNZass p d n l y) :
    BNZass p d n (k + l) (x * y) := by
  rcases hx with ⟨L, hLlen, hLprod⟩
  rcases hy with ⟨M, hMlen, hMprod⟩
  refine ⟨L ++ M, ?_, ?_⟩
  · simpa [List.length_append] using Nat.add_le_add hLlen hMlen
  · rw [List.map_append, List.prod_append, hLprod, hMprod]

/--
TeX Lemma 5 uses the varying-right-input left-normed commutator word
`[[...[x₁,x₂],x₃],...,xᵣ]`.  The existing `leftIteratedElement`
records the repeated-left Hall shape instead, so the residual-completion proof
needs its own explicit commutator word.
-/
def LNWord :
    (s : ℕ) → CWord (Fin (s + 1))
  | 0 => .atom 0
  | s + 1 =>
      .commutator
        ((LNWord s).bind fun i => .atom i.castSucc)
        (.atom (Fin.last (s + 1)))

/--
Value-level version of `LNWord`.  The parameter `s` counts
the tail length, so this is the `(s + 1)`-fold left-normed commutator value.
-/
def leftNormedValue
    {G : Type u} [Group G] :
    (s : ℕ) → (Fin (s + 1) → G) → G
  | 0, a => a 0
  | s + 1, a =>
      ⁅leftNormedValue s (fun i => a i.castSucc),
        a (Fin.last (s + 1))⁆

/--
The explicit word and its value-level recursion agree.
-/
lemma LNWord.evaleq_leftnormed_commvalue
    {G : Type u} [Group G]
    (s : ℕ)
    (a : Fin (s + 1) → G) :
    (LNWord s).eval a =
      leftNormedValue s a := by
  induction s with
  | zero =>
      rfl
  | succ s ih =>
      simp [LNWord, leftNormedValue,
        CWord.eval_bind, ih]

/--
The left-normed `(s + 1)`-fold word has exactly `s + 1` leaves.
-/
lemma LNWord.weight_one
    (s : ℕ) :
    (LNWord s).weight (fun _ => 1) = s + 1 := by
  induction s with
  | zero =>
      rfl
  | succ s ih =>
      simp [LNWord, CWord.weight_bind, ih]

/--
TeX Lemma 5 indexes its fixed ordered family by the `s` right-tail generator
choices in an `(s + 1)`-fold left-normed commutator.
-/
abbrev LowerTailTuple
    (d s : ℕ) :
    Type :=
  Fin s → Fin d

/--
Choose the TeX fixed order on the right-tail generator tuples by transporting
the canonical `Fin` order across `Fintype.equivFin`.
-/
noncomputable def lowerTailTuple
    (d s : ℕ)
    (i : Fin (Fintype.card (LowerTailTuple d s))) :
    LowerTailTuple d s :=
  (Fintype.equivFin (LowerTailTuple d s)).symm i

/--
Assemble the first free argument and the fixed generator tail chosen by `I`.
-/
def lowerTupleArguments
    {G : Type u}
    {d s : ℕ}
    (t : Fin d → G)
    (u : G)
    (I : LowerTailTuple d s) :
    Fin (s + 1) → G :=
  Fin.cons u fun j => t (I j)

/--
The fixed ordered list of TeX Lemma 5 commutator values, one slot for each
right-tail generator tuple.
-/
noncomputable def orderedNormedValues
    {G : Type u} [Group G]
    (d s : ℕ)
    (t : Fin d → G)
    (u : LowerTailTuple d s → G) :
    List G :=
  List.ofFn fun i : Fin (Fintype.card (LowerTailTuple d s)) =>
    leftNormedValue s
      (lowerTupleArguments t (u (lowerTailTuple d s i))
        (lowerTailTuple d s i))

/--
The exact list-level normal form asserted in TeX Lemma 5, with the fixed tuple
order made explicit.
-/
def ONFacta
    {G : Type u} [Group G]
    (d s : ℕ)
    (t : Fin d → G)
    (x : G) :
    Prop :=
  ∃ u : LowerTailTuple d s → G,
    (orderedNormedValues d s t u).prod = x

/--
The ordered TeX family has one list entry for each right-tail tuple.
-/
lemma normed_values_length
    {G : Type u} [Group G]
    (d s : ℕ)
    (t : Fin d → G)
    (u : LowerTailTuple d s → G) :
    (orderedNormedValues d s t u).length =
      Fintype.card (LowerTailTuple d s) := by
  simp [orderedNormedValues]

/--
At tail length zero, the unique ordered TeX slot is the identity word value
chosen by its free first argument.
-/
lemma ordered_normed_factorization
    {G : Type u} [Group G]
    (d : ℕ)
    (t : Fin d → G)
    (x : G) :
    ONFacta d 0 t x := by
  refine ⟨fun _ => x, ?_⟩
  simp [orderedNormedValues, leftNormedValue,
    lowerTupleArguments]

/--
If the free first argument of a left-normed commutator is trivial, the whole
left-normed value is trivial regardless of the fixed generator tail.
-/
lemma left_normed_value
    {G : Type u} [Group G] :
    ∀ (s : ℕ) (a : Fin (s + 1) → G),
      a 0 = 1 →
        leftNormedValue s a = 1
  | 0, a, ha => by
      simpa [leftNormedValue] using ha
  | s + 1, a, ha => by
      have htail :
          leftNormedValue s (fun i => a i.castSucc) = 1 := by
        apply left_normed_value s
        simpa using ha
      simp [leftNormedValue, htail]

/--
Feeding identity free arguments into every ordered slot gives the identity
product; this is the trivial lower-central factorization used when the target
term has already vanished.
-/
lemma normed_lower_factorization
    {G : Type u} [Group G]
    (d s : ℕ)
    (t : Fin d → G) :
    ONFacta d s t (1 : G) := by
  refine ⟨fun _ => 1, ?_⟩
  apply List.prod_eq_one
  intro y hy
  rcases List.mem_ofFn.mp hy with ⟨i, rfl⟩
  apply left_normed_value
  simp [lowerTupleArguments]

/--
Each explicit left-normed `(s + 1)`-fold commutator value lies in the expected
zero-based lower-central term `γ_(s + 1)`.
-/
lemma normed_value_series
    {G : Type u} [Group G]
    (s : ℕ)
    (a : Fin (s + 1) → G) :
    leftNormedValue s a ∈ Subgroup.lowerCentralSeries G s := by
  rw [← LNWord.evaleq_leftnormed_commvalue]
  have hweight :
      (LNWord s).weight (fun _ => 1) - 1 = s := by
    rw [LNWord.weight_one, Nat.succ_sub_one]
  simpa [hweight] using
    (CWord.eval_lower_series
      a (fun _ => 1) (fun _ => by norm_num) (fun _ => by simp)
      (LNWord s))

/--
If the free first argument starts in a deeper lower-central term, the explicit
left-normed word lands in the correspondingly deeper term after its fixed tail
is appended.  This is the zero-based Lean translation of the depth count used
for TeX Lemma 5's witnesses `v_I ∈ γ_(c-r+1)(G)`.
-/
lemma left_normed_series
    {G : Type u} [Group G]
    {i : ℕ} :
    ∀ (s : ℕ) (a : Fin (s + 1) → G),
      a 0 ∈ Subgroup.lowerCentralSeries G i →
        leftNormedValue s a ∈ Subgroup.lowerCentralSeries G (i + s)
  | 0, a, ha => by
      simpa [leftNormedValue] using ha
  | s + 1, a, ha => by
      have hprefix :
          leftNormedValue s (fun j => a j.castSucc) ∈
            Subgroup.lowerCentralSeries G (i + s) :=
        left_normed_series
          s (fun j => a j.castSucc) (by simpa using ha)
      have hcomm :
          ⁅leftNormedValue s (fun j => a j.castSucc),
            a (Fin.last (s + 1))⁆ ∈
            Subgroup.lowerCentralSeries G ((i + s) + 0 + 1) :=
        lower_commutator_succ (i + s) 0
          (Subgroup.commutator_mem_commutator hprefix (by simp))
      have hindex : (i + s) + 0 + 1 = i + (s + 1) := by
        omega
      simpa [leftNormedValue, hindex] using hcomm

/--
The TeX Lemma 5 depth hypothesis on a free first argument forces the completed
left-normed factor into the last nontrivial lower-central term.
-/
lemma left_normed_last
    {G : Type u} [Group G]
    {c s : ℕ}
    (hsLe : s ≤ c - 1)
    (a : Fin (s + 1) → G)
    (ha : a 0 ∈ Subgroup.lowerCentralSeries G (c - (s + 1))) :
    leftNormedValue s a ∈ Subgroup.lowerCentralSeries G (c - 1) := by
  have hmem :
      leftNormedValue s a ∈
        Subgroup.lowerCentralSeries G (c - (s + 1) + s) :=
    left_normed_series s a ha
  have hindex : c - (s + 1) + s = c - 1 := by
    omega
  simpa [hindex] using hmem

/--
If a subgroup commutes with the whole group modulo another normal subgroup,
then its image in that quotient lies in the center.  This is the quotient
form of the "higher commutator error becomes central modulo the next
lower-central term" step used below.
-/
lemma quotient_mk_center
    {G : Type u} [Group G]
    {K L : Subgroup G} [K.Normal] [L.Normal]
    (hKL : ⁅K, (⊤ : Subgroup G)⁆ ≤ L)
    {x : G}
    (hx : x ∈ K) :
    QuotientGroup.mk' L x ∈ Subgroup.center (G ⧸ L) := by
  rw [Subgroup.mem_center_iff, QuotientGroup.forall_mk]
  intro y
  have hcomm : Commute (QuotientGroup.mk' L x) (QuotientGroup.mk' L y) := by
    rw [← commutatorElement_eq_one_iff_commute, ← map_commutatorElement]
    exact (QuotientGroup.eq_one_iff (N := L) ⁅x, y⁆).mpr
      (hKL (Subgroup.commutator_mem_commutator hx (by simp)))
  exact hcomm.eq.symm

/--
If two left inputs agree modulo `K`, then their commutators with one fixed
right input agree modulo any quotient where `K` has become central.
-/
lemma element_congr_inv
    {G : Type u} [Group G]
    {K L : Subgroup G} [K.Normal] [L.Normal]
    (hKL : ⁅K, (⊤ : Subgroup G)⁆ ≤ L)
    {x y z : G}
    (hxy : x * y⁻¹ ∈ K) :
    ⁅x, z⁆ * ⁅y, z⁆⁻¹ ∈ L := by
  rw [mul_inv_quotient L]
  let q : G →* G ⧸ L := QuotientGroup.mk' L
  have hkCenter :
      q (x * y⁻¹) ∈ Subgroup.center (G ⧸ L) := by
    exact quotient_mk_center hKL hxy
  have hkCenter' :
      ∀ g : G ⧸ L, g * q (x * y⁻¹) = q (x * y⁻¹) * g :=
    Subgroup.mem_center_iff.mp hkCenter
  have hkComm :
      Commute (q (x * y⁻¹)) (q z) := by
    exact (show Commute (q z) (q (x * y⁻¹)) from hkCenter' (q z)).symm
  have hxyq : q x = q (x * y⁻¹) * q y := by
    simp only [map_mul, map_inv]
    group
  have hconj :
      q (x * y⁻¹) * ⁅q y, q z⁆ * (q (x * y⁻¹))⁻¹ =
        ⁅q y, q z⁆ := by
    have hcenterComm :
        q (x * y⁻¹) * ⁅q y, q z⁆ =
          ⁅q y, q z⁆ * q (x * y⁻¹) := by
      exact (hkCenter' _).symm
    calc
      q (x * y⁻¹) * ⁅q y, q z⁆ * (q (x * y⁻¹))⁻¹ =
          ⁅q y, q z⁆ * q (x * y⁻¹) * (q (x * y⁻¹))⁻¹ := by
            rw [hcenterComm]
      _ = ⁅q y, q z⁆ := by group
  calc
    q ⁅x, z⁆ = ⁅q x, q z⁆ := by rw [map_commutatorElement]
    _ = ⁅q (x * y⁻¹) * q y, q z⁆ := by rw [← hxyq]
    _ =
        q (x * y⁻¹) * ⁅q y, q z⁆ * (q (x * y⁻¹))⁻¹ *
          ⁅q (x * y⁻¹), q z⁆ := by
          rw [element_mul_left]
    _ = ⁅q y, q z⁆ * ⁅q (x * y⁻¹), q z⁆ := by rw [hconj]
    _ = ⁅q y, q z⁆ := by
          rw [commutatorElement_eq_one_iff_commute.mpr hkComm, mul_one]
    _ = q ⁅y, z⁆ := by rw [map_commutatorElement]

/--
Right-coset congruence modulo a normal subgroup is transitive.
-/
lemma mul_inv_trans
    {G : Type u} [Group G]
    (K : Subgroup G) [K.Normal]
    {x y z : G}
    (hxy : x * y⁻¹ ∈ K)
    (hyz : y * z⁻¹ ∈ K) :
    x * z⁻¹ ∈ K := by
  rw [mul_inv_quotient K] at hxy hyz ⊢
  exact hxy.trans hyz

/--
Unfold one tail step of the explicit left-normed word after writing its tuple
as a free first argument followed by a right tail.
-/
lemma normed_cons_succ
    {G : Type u} [Group G]
    {s : ℕ}
    (u : G)
    (tail : Fin (s + 1) → G) :
    leftNormedValue (s + 1) (Fin.cons u tail) =
      ⁅leftNormedValue s
          (Fin.cons u fun j : Fin s => tail j.castSucc),
        tail (Fin.last s)⁆ := by
  have hprefix :
      (fun i : Fin (s + 1) =>
        (@Fin.cons (s + 1) (fun _ : Fin (s + 2) => G) u tail) i.castSucc) =
        @Fin.cons s (fun _ : Fin (s + 1) => G) u
          (fun j : Fin s => tail j.castSucc) := by
    funext j
    cases j using Fin.cases <;> simp
  simp only [leftNormedValue, Fin.cons_last, hprefix]

/--
Elementwise form of strong lower-central centrality.
-/
lemma element_lower_series
    {G : Type u} [Group G]
    {i j : ℕ}
    {x y : G}
    (hx : x ∈ Subgroup.lowerCentralSeries G i)
    (hy : y ∈ Subgroup.lowerCentralSeries G j) :
    ⁅x, y⁆ ∈ Subgroup.lowerCentralSeries G (i + j + 1) :=
  lower_commutator_succ i j
    (Subgroup.commutator_mem_commutator hx hy)

/--
Changing the free first argument of a left-normed word by an element of
`γ_i(G)` changes its value only modulo `γ_(i+s+1)(G)`.  This is the formal
commutator-error estimate behind TeX Lemma 5's central-tail absorption.
-/
lemma normed_inv_series
    {G : Type u} [Group G]
    {i : ℕ} :
    ∀ (s : ℕ) (u v : G) (tail : Fin s → G),
      v ∈ Subgroup.lowerCentralSeries G i →
        leftNormedValue s (Fin.cons (u * v) tail) *
            (leftNormedValue s (Fin.cons v tail) *
              leftNormedValue s (Fin.cons u tail))⁻¹ ∈
          Subgroup.lowerCentralSeries G (i + s + 1)
  | 0, u, v, _tail, hv => by
      simpa only [leftNormedValue, Fin.cons_zero, mul_inv_rev,
        Nat.zero_add, commutatorElement_def, mul_assoc] using
        element_lower_series
          (i := 0) (j := i) (x := u) (y := v) (by simp) hv
  | s + 1, u, v, tail, hv => by
      let tail' : Fin s → G := fun j => tail j.castSucc
      let a : G := leftNormedValue s (Fin.cons u tail')
      let b : G := leftNormedValue s (Fin.cons v tail')
      let ab : G := leftNormedValue s (Fin.cons (u * v) tail')
      let y : G := tail (Fin.last s)
      let L : Subgroup G := Subgroup.lowerCentralSeries G (i + (s + 1) + 1)
      have hab :
          ab * (b * a)⁻¹ ∈ Subgroup.lowerCentralSeries G (i + s + 1) := by
        simpa [ab, a, b, tail'] using
          normed_inv_series
            (i := i) s u v tail' hv
      have hcommConj :
          ⁅ab, y⁆ * ⁅b * a, y⁆⁻¹ ∈ L := by
        apply
          element_congr_inv
            (K := Subgroup.lowerCentralSeries G (i + s + 1))
            (L := L)
        · simpa [L, Nat.add_assoc] using
            (lower_commutator_succ
              (G := G) (i + s + 1) 0)
        · exact hab
      have ha : a ∈ Subgroup.lowerCentralSeries G s := by
        simpa [a] using
          normed_value_series
            s (Fin.cons u tail')
      have hb : b ∈ Subgroup.lowerCentralSeries G (i + s) := by
        simpa [b] using
          left_normed_series
            (i := i) s (Fin.cons v tail') (by simpa using hv)
      have hay :
          ⁅a, y⁆ ∈ Subgroup.lowerCentralSeries G (s + 1) := by
        simpa using
          element_lower_series
            (i := s) (j := 0) ha (by simp)
      have hby :
          ⁅b, y⁆ ∈ Subgroup.lowerCentralSeries G (i + s + 1) := by
        simpa [Nat.add_assoc] using
          element_lower_series
            (i := i + s) (j := 0) hb (by simp)
      have hb_comm_hay :
          ⁅b, ⁅a, y⁆⁆ ∈ L := by
        have hmem :
            ⁅b, ⁅a, y⁆⁆ ∈ Subgroup.lowerCentralSeries G ((i + s) + (s + 1) + 1) :=
          element_lower_series hb hay
        exact
          Subgroup.lowerCentralSeries_antitone (G := G)
            (by omega : i + (s + 1) + 1 ≤ (i + s) + (s + 1) + 1)
            hmem
      have hconj :
          b * ⁅a, y⁆ * b⁻¹ * ⁅a, y⁆⁻¹ ∈ L := by
        simpa [commutatorElement_def] using hb_comm_hay
      have hmulConj :
          (b * ⁅a, y⁆ * b⁻¹ * ⁅b, y⁆) *
              (⁅a, y⁆ * ⁅b, y⁆)⁻¹ ∈ L := by
        exact
          inv_of_mem L hconj
            (by
              simpa only [mul_inv_cancel] using L.one_mem)
      have hswap :
          (⁅a, y⁆ * ⁅b, y⁆) * (⁅b, y⁆ * ⁅a, y⁆)⁻¹ ∈ L := by
        have hmem :
            ⁅⁅a, y⁆, ⁅b, y⁆⁆ ∈
              Subgroup.lowerCentralSeries G ((s + 1) + (i + s + 1) + 1) :=
          element_lower_series hay hby
        have hmemL : ⁅⁅a, y⁆, ⁅b, y⁆⁆ ∈ L :=
          Subgroup.lowerCentralSeries_antitone (G := G)
            (by omega : i + (s + 1) + 1 ≤ (s + 1) + (i + s + 1) + 1)
            hmem
        simpa only [commutatorElement_def, mul_inv_rev, mul_assoc] using hmemL
      have hmul :
          ⁅b * a, y⁆ * (⁅b, y⁆ * ⁅a, y⁆)⁻¹ ∈ L := by
        apply mul_inv_trans L
        · rw [element_mul_left]
          exact hmulConj
        · exact hswap
      have htotal :
          ⁅ab, y⁆ * (⁅b, y⁆ * ⁅a, y⁆)⁻¹ ∈ L :=
        mul_inv_trans L hcommConj hmul
      simpa [normed_cons_succ, ab, a, b, y, L] using htotal

/--
When `γ_c(G)` has vanished, the previous congruence becomes the exact
source-depth-controlled multiplication law used in TeX Lemma 5.
-/
lemma left_normed_zero
    {G : Type u} [Group G]
    {c s : ℕ}
    (hsLe : s ≤ c - 1)
    (hcPos : 0 < c)
    (hcBot : Subgroup.lowerCentralSeries G c = ⊥)
    (u v : G)
    (tail : Fin s → G)
    (hv : v ∈ Subgroup.lowerCentralSeries G (c - (s + 1))) :
    leftNormedValue s (Fin.cons (u * v) tail) =
      leftNormedValue s (Fin.cons v tail) *
        leftNormedValue s (Fin.cons u tail) := by
  have hmem :
      leftNormedValue s (Fin.cons (u * v) tail) *
          (leftNormedValue s (Fin.cons v tail) *
            leftNormedValue s (Fin.cons u tail))⁻¹ ∈
        Subgroup.lowerCentralSeries G (c - (s + 1) + s + 1) :=
    normed_inv_series
      (i := c - (s + 1)) s u v tail hv
  have hsSuccLe : s + 1 ≤ c := by
    exact Nat.succ_le_iff.mpr (Nat.lt_of_le_sub_one hcPos hsLe)
  have hindex : c - (s + 1) + s + 1 = c := by
    calc
      c - (s + 1) + s + 1 = c - (s + 1) + (s + 1) := by omega
      _ = c := Nat.sub_add_cancel hsSuccLe
  apply mul_inv_eq_one.mp
  exact eq_bot_iff.mp hcBot (by simpa [hindex] using hmem)

/--
If the next lower-central term is trivial, the last nontrivial term is central.
This is the Lean form of TeX Lemma 5's `Z = γ_c(G)` sentence.
-/
lemma last_term_center
    {G : Type u} [Group G]
    {c : ℕ}
    (hcPos : 0 < c)
    (hcBot : Subgroup.lowerCentralSeries G c = ⊥) :
    Subgroup.lowerCentralSeries G (c - 1) ≤ Subgroup.center G := by
  intro z hz
  rw [Subgroup.mem_center_iff]
  intro g
  have hcomm :
      ⁅z, g⁆ ∈ Subgroup.lowerCentralSeries G ((c - 1) + 0 + 1) :=
    lower_commutator_succ (c - 1) 0
      (Subgroup.commutator_mem_commutator hz (by simp))
  have hindex : (c - 1) + 0 + 1 = c := by
    omega
  have hcommOne : ⁅z, g⁆ = 1 := by
    exact eq_bot_iff.mp hcBot (by simpa [hindex] using hcomm)
  exact (commutatorElement_eq_one_iff_commute.mp hcommOne).eq.symm

/--
If the left factor in each fixed ordered slot is central, the pointwise
product list recollects as the product of the left list followed by the
product of the right list.
-/
lemma fn_forall_center
    {G : Type u} [Group G] :
    ∀ {m : ℕ} (a b : Fin m → G),
      (∀ i : Fin m, a i ∈ Subgroup.center G) →
        (List.ofFn fun i : Fin m => a i * b i).prod =
          (List.ofFn a).prod * (List.ofFn b).prod
  | 0, _a, _b, _ha => by simp
  | m + 1, a, b, ha => by
      have htail :
          (List.ofFn fun i : Fin m => a i.succ * b i.succ).prod =
            (List.ofFn fun i : Fin m => a i.succ).prod *
              (List.ofFn fun i : Fin m => b i.succ).prod :=
        fn_forall_center
          (fun i : Fin m => a i.succ)
          (fun i : Fin m => b i.succ)
          (fun i => ha i.succ)
      have htailCenter :
          (List.ofFn fun i : Fin m => a i.succ).prod ∈ Subgroup.center G := by
        apply Subgroup.list_prod_mem
        intro x hx
        rcases List.mem_ofFn.mp hx with ⟨i, rfl⟩
        exact ha i.succ
      have htailComm :
          (List.ofFn fun i : Fin m => a i.succ).prod * b 0 =
            b 0 * (List.ofFn fun i : Fin m => a i.succ).prod :=
        (Subgroup.mem_center_iff.mp htailCenter (b 0)).symm
      simp only [List.ofFn_succ, List.prod_cons, htail]
      calc
        a 0 * b 0 *
            ((List.ofFn fun i : Fin m => a i.succ).prod *
              (List.ofFn fun i : Fin m => b i.succ).prod) =
            a 0 * (b 0 * (List.ofFn fun i : Fin m => a i.succ).prod) *
              (List.ofFn fun i : Fin m => b i.succ).prod := by group
        _ =
            a 0 * ((List.ofFn fun i : Fin m => a i.succ).prod * b 0) *
              (List.ofFn fun i : Fin m => b i.succ).prod := by rw [htailComm]
        _ =
            (a 0 * (List.ofFn fun i : Fin m => a i.succ).prod) *
              (b 0 * (List.ofFn fun i : Fin m => b i.succ).prod) := by group

/--
For one fixed right tail, TeX Lemma 5's source-depth condition makes the
left-normed value a homomorphism from the source lower-central term into the
center.
-/
def valueMonoidHom
    {G : Type u} [Group G]
    {d s c : ℕ}
    (hsLe : s ≤ c - 1)
    (hcPos : 0 < c)
    (hcBot : Subgroup.lowerCentralSeries G c = ⊥)
    (t : Fin d → G)
    (I : LowerTailTuple d s) :
    Subgroup.lowerCentralSeries G (c - (s + 1)) →* Subgroup.center G where
  toFun v :=
    ⟨leftNormedValue s
        (lowerTupleArguments t (v : G) I),
      last_term_center hcPos hcBot
        (left_normed_last
          hsLe _ v.property)⟩
  map_one' := by
    ext
    simp [lowerTupleArguments,
      left_normed_value]
  map_mul' x y := by
    ext
    change
      leftNormedValue s
          (lowerTupleArguments t ((x : G) * (y : G)) I) =
        leftNormedValue s
            (lowerTupleArguments t (x : G) I) *
          leftNormedValue s
            (lowerTupleArguments t (y : G) I)
    calc
      leftNormedValue s
          (lowerTupleArguments t ((x : G) * (y : G)) I) =
          leftNormedValue s
              (lowerTupleArguments t (y : G) I) *
            leftNormedValue s
              (lowerTupleArguments t (x : G) I) := by
            simpa [lowerTupleArguments] using
              left_normed_zero
                hsLe hcPos hcBot (x : G) (y : G)
                (fun j : Fin s => t (I j)) y.property
      _ =
          leftNormedValue s
              (lowerTupleArguments t (x : G) I) *
            leftNormedValue s
              (lowerTupleArguments t (y : G) I) :=
            Subgroup.mem_center_iff.mp
              (last_term_center hcPos hcBot
                (left_normed_last
                  hsLe (lowerTupleArguments t (x : G) I) x.property))
              (leftNormedValue s
                (lowerTupleArguments t (y : G) I))

/--
Multiplying the fixed-slot central-tail homomorphisms gives the full TeX fixed
ordered family, now viewed inside the center where the slot order is harmless.
-/
def centralMonoidHom
    {G : Type u} [Group G]
    {d s c : ℕ}
    (hsLe : s ≤ c - 1)
    (hcPos : 0 < c)
    (hcBot : Subgroup.lowerCentralSeries G c = ⊥)
    (t : Fin d → G) :
    (LowerTailTuple d s → Subgroup.lowerCentralSeries G (c - (s + 1))) →*
      Subgroup.center G where
  toFun v :=
    ∏ I : LowerTailTuple d s,
      valueMonoidHom hsLe hcPos hcBot t I (v I)
  map_one' := by simp
  map_mul' v w := by
    simp [map_mul, Finset.prod_mul_distrib]

/--
Ambient-group image of the fixed central-tail product homomorphism.
-/
def tailRangeSubgroup
    {G : Type u} [Group G]
    {d s c : ℕ}
    (hsLe : s ≤ c - 1)
    (hcPos : 0 < c)
    (hcBot : Subgroup.lowerCentralSeries G c = ⊥)
    (t : Fin d → G) :
    Subgroup G :=
  Subgroup.map (Subgroup.center G).subtype
    (centralMonoidHom hsLe hcPos hcBot t).range

/--
Every fixed central-tail product lies in the center.
-/
lemma tail_range_center
    {G : Type u} [Group G]
    {d s c : ℕ}
    (hsLe : s ≤ c - 1)
    (hcPos : 0 < c)
    (hcBot : Subgroup.lowerCentralSeries G c = ⊥)
    (t : Fin d → G) :
    tailRangeSubgroup hsLe hcPos hcBot t ≤ Subgroup.center G := by
  rintro z ⟨w, _hw, rfl⟩
  exact w.property

/--
The fixed central-tail range is normal because it is central.
-/
lemma tail_range_normal
    {G : Type u} [Group G]
    {d s c : ℕ}
    (hsLe : s ≤ c - 1)
    (hcPos : 0 < c)
    (hcBot : Subgroup.lowerCentralSeries G c = ⊥)
    (t : Fin d → G) :
    (tailRangeSubgroup hsLe hcPos hcBot t).Normal := by
  constructor
  intro z hz g
  have hzCenter :
      z ∈ Subgroup.center G :=
    tail_range_center hsLe hcPos hcBot t hz
  rw [Subgroup.mem_center_iff] at hzCenter
  rw [hzCenter g, mul_inv_cancel_right]
  exact hz

/--
The center-valued product homomorphism evaluates to the original raw ordered
TeX product after forgetting the center subtype.
-/
lemma coe_monoid_prod
    {G : Type u} [Group G]
    {d s c : ℕ}
    (hsLe : s ≤ c - 1)
    (hcPos : 0 < c)
    (hcBot : Subgroup.lowerCentralSeries G c = ⊥)
    (t : Fin d → G)
    (v : LowerTailTuple d s → Subgroup.lowerCentralSeries G (c - (s + 1))) :
    ((centralMonoidHom hsLe hcPos hcBot t v :
        Subgroup.center G) : G) =
      (orderedNormedValues d s t fun I => (v I : G)).prod := by
  let f : LowerTailTuple d s → Subgroup.center G :=
    fun I => valueMonoidHom hsLe hcPos hcBot t I (v I)
  have henum :
      (List.ofFn fun i : Fin (Fintype.card (LowerTailTuple d s)) =>
        f (lowerTailTuple d s i)).prod =
        ∏ I : LowerTailTuple d s, f I := by
    rw [List.prod_ofFn]
    simpa [lowerTailTuple] using
      (Fintype.prod_equiv (Fintype.equivFin (LowerTailTuple d s)).symm
        (fun i : Fin (Fintype.card (LowerTailTuple d s)) =>
          f (lowerTailTuple d s i))
        f
        (fun _ => rfl))
  calc
    ((centralMonoidHom hsLe hcPos hcBot t v :
        Subgroup.center G) : G) =
        ((∏ I : LowerTailTuple d s, f I : Subgroup.center G) : G) := rfl
    _ =
        ((List.ofFn fun i : Fin (Fintype.card (LowerTailTuple d s)) =>
          f (lowerTailTuple d s i)).prod :
          Subgroup.center G) := congrArg Subtype.val henum.symm
    _ =
        (orderedNormedValues d s t fun I => (v I : G)).prod := by
          change
            (Subgroup.center G).subtype
                (List.ofFn fun i : Fin (Fintype.card (LowerTailTuple d s)) =>
                  f (lowerTailTuple d s i)).prod =
              _
          rw [map_list_prod, List.map_ofFn]
          rfl

/--
One explicit full-tail left-normed value is already in the fixed central-tail
range by turning on only that slot.
-/
lemma tail_range_value
    {G : Type u} [Group G]
    {d s c : ℕ}
    (hsLe : s ≤ c - 1)
    (hcPos : 0 < c)
    (hcBot : Subgroup.lowerCentralSeries G c = ⊥)
    (t : Fin d → G)
    (I : LowerTailTuple d s)
    (v : Subgroup.lowerCentralSeries G (c - (s + 1))) :
    leftNormedValue s
        (lowerTupleArguments t (v : G) I) ∈
      tailRangeSubgroup hsLe hcPos hcBot t := by
  let delta :
      LowerTailTuple d s → Subgroup.lowerCentralSeries G (c - (s + 1)) :=
    Function.update (fun _ => 1) I v
  refine ⟨centralMonoidHom hsLe hcPos hcBot t delta, ⟨delta, rfl⟩, ?_⟩
  change
    ((centralMonoidHom hsLe hcPos hcBot t delta :
        Subgroup.center G) : G) =
      leftNormedValue s
        (lowerTupleArguments t (v : G) I)
  have hprod :
      centralMonoidHom hsLe hcPos hcBot t delta =
        valueMonoidHom hsLe hcPos hcBot t I v := by
    change
      (∏ J : LowerTailTuple d s,
        valueMonoidHom hsLe hcPos hcBot t J (delta J)) =
        valueMonoidHom hsLe hcPos hcBot t I v
    calc
      (∏ J : LowerTailTuple d s,
        valueMonoidHom hsLe hcPos hcBot t J (delta J)) =
          ∏ J : LowerTailTuple d s,
            if I = J then valueMonoidHom hsLe hcPos hcBot t I v else 1 := by
              apply Fintype.prod_congr
              intro J
              by_cases h : I = J
              · subst J
                simp [delta]
              · have h' : ¬ J = I := by simpa [eq_comm] using h
                simp [delta, h, h']
      _ = valueMonoidHom hsLe hcPos hcBot t I v := by
            simp
  exact congrArg Subtype.val hprod

/--
If every individual commutator with one fixed right input is central, then the
commutator of a raw list product is the product of those individual
commutators in the original list order.
-/
lemma commutator_forall_center
    {G : Type u} [Group G]
    (L : List G)
    (g : G)
    (hL : ∀ x ∈ L, ⁅x, g⁆ ∈ Subgroup.center G) :
    ⁅L.prod, g⁆ = (L.map fun x => ⁅x, g⁆).prod := by
  induction L with
  | nil =>
      simp
  | cons x L ih =>
      have hxCenter : ⁅x, g⁆ ∈ Subgroup.center G :=
        hL x (by simp)
      have htail :
          ∀ y ∈ L, ⁅y, g⁆ ∈ Subgroup.center G := by
        intro y hy
        exact hL y (by simp [hy])
      have htailProdCenter :
          (L.map fun y => ⁅y, g⁆).prod ∈ Subgroup.center G := by
        apply Subgroup.list_prod_mem
        intro y hy
        rcases List.mem_map.mp hy with ⟨z, hz, rfl⟩
        exact htail z hz
      have hconj :
          x * (L.map fun y => ⁅y, g⁆).prod * x⁻¹ =
            (L.map fun y => ⁅y, g⁆).prod := by
        rw [Subgroup.mem_center_iff.mp htailProdCenter x, mul_inv_cancel_right]
      have hswap :
          (L.map fun y => ⁅y, g⁆).prod * ⁅x, g⁆ =
            ⁅x, g⁆ * (L.map fun y => ⁅y, g⁆).prod :=
        Subgroup.mem_center_iff.mp hxCenter _
      rw [List.prod_cons, element_mul_left, ih htail,
        List.map_cons, List.prod_cons, hconj, hswap]

/--
One more commutator step from the predecessor lower-central term lands in the
central last nontrivial lower-central term.
-/
lemma last_center_pred
    {G : Type u} [Group G]
    {c : ℕ}
    (hcTwo : 2 ≤ c)
    (hcPos : 0 < c)
    (hcBot : Subgroup.lowerCentralSeries G c = ⊥)
    {x y : G}
    (hx : x ∈ Subgroup.lowerCentralSeries G (c - 2)) :
    ⁅x, y⁆ ∈ Subgroup.center G := by
  apply last_term_center hcPos hcBot
  have hmem :
      ⁅x, y⁆ ∈ Subgroup.lowerCentralSeries G ((c - 2) + 0 + 1) :=
    element_lower_series
      (i := c - 2) (j := 0) hx (by simp)
  have hindex : (c - 2) + 0 + 1 = c - 1 := by
    omega
  simpa [hindex] using hmem

/--
If commutators with a fixed left input land in a normal subgroup on a
generating set, they land there on the subgroup generated by that set.
-/
lemma element_closure_generator
    {G : Type u} [Group G]
    (R : Subgroup G) [R.Normal]
    {A : Set G}
    {y g : G}
    (hgen : ∀ {a : G}, a ∈ A → ⁅y, a⁆ ∈ R)
    (hg : g ∈ Subgroup.closure A) :
    ⁅y, g⁆ ∈ R := by
  let P : (g : G) → g ∈ Subgroup.closure A → Prop :=
    fun g _ => ⁅y, g⁆ ∈ R
  exact
    Subgroup.closure_induction
      (p := P)
      (fun x hx => hgen hx)
      (by
        change ⁅y, 1⁆ ∈ R
        simp)
      (by
        intro g₁ g₂ _hg₁ _hg₂ hg₁R hg₂R
        change ⁅y, g₁ * g₂⁆ ∈ R
        rw [element_mul_right]
        simpa [mul_assoc] using
          R.mul_mem hg₁R
            ((inferInstance : R.Normal).conj_mem ⁅y, g₂⁆ hg₂R g₁))
      (by
        intro g₁ _hg₁ hg₁R
        change ⁅y, g₁⁻¹⁆ ∈ R
        have hinv :
            ⁅y, g₁⁻¹⁆ = g₁⁻¹ * ⁅y, g₁⁆⁻¹ * g₁ := by
          simp [commutatorElement_def]
          group
        rw [hinv]
        simpa using
          ((inferInstance : R.Normal).conj_mem
            ⁅y, g₁⁆⁻¹ (R.inv_mem hg₁R) g₁⁻¹))
      hg

/--
If the right side of a subgroup commutator is generated by a chosen tuple,
generator-level commutator membership suffices for the whole commutator
subgroup.
-/
lemma commutator_generator
    {G : Type u} [Group G]
    {d : ℕ}
    (R K : Subgroup G) [R.Normal]
    (t : Fin d → G)
    (ht : GeneratedBy t)
    (hgen : ∀ {y : G}, y ∈ K → ∀ j : Fin d, ⁅y, t j⁆ ∈ R) :
    ⁅K, (⊤ : Subgroup G)⁆ ≤ R := by
  rw [Subgroup.commutator_le]
  intro y hy g _hg
  apply element_closure_generator
    (A := Set.range t) R
  · intro x hx
    rcases hx with ⟨j, rfl⟩
    exact hgen hy j
  · rw [ht]
    exact Subgroup.mem_top g

/--
The last nontrivial lower-central term is the commutator of its predecessor
with the whole group.
-/
lemma commutator_last_term
    {G : Type u} [Group G]
    {c : ℕ}
    (hcTwo : 2 ≤ c)
    {z : G}
    (hz : z ∈ Subgroup.lowerCentralSeries G (c - 1)) :
    z ∈ ⁅Subgroup.lowerCentralSeries G (c - 2), (⊤ : Subgroup G)⁆ := by
  have hindex : c - 1 = (c - 2) + 1 := by
    omega
  rw [hindex, Subgroup.lowerCentralSeries_succ] at hz
  exact hz

/--
Appending one fixed generator to the right tail is exactly one more
left-normed commutator step.
-/
lemma normed_snoc_tail
    {G : Type u} [Group G]
    {d s : ℕ}
    (t : Fin d → G)
    (u : G)
    (I : LowerTailTuple d s)
    (j : Fin d) :
    ⁅leftNormedValue s
        (lowerTupleArguments t u I),
      t j⁆ =
      leftNormedValue (s + 1)
        (lowerTupleArguments t u
          (@Fin.snoc s (fun _ : Fin (s + 1) => Fin d) I j)) := by
  simp only [lowerTupleArguments]
  rw [normed_cons_succ]
  congr 1
  · congr 1
    funext k
    simp
  · simp

/--
One TeX Lemma 5 left-normed commutator value is one normalized Zassenhaus
scheduled value at the matching depth.
-/
lemma bounded_normalized_normed
    {p d s : ℕ} [Fact p.Prime]
    {G : Type u} [Group G]
    (a : Fin (s + 1) → G) :
    BNZass
      p d (s + 1) 1
      (leftNormedValue s a) := by
  have hlevel :
      s + 1 ≤
        (LNWord s).weight (fun _ => 1) * p ^ 0 := by
    rw [LNWord.weight_one]
    simp
  obtain ⟨i, b, hb⟩ :=
    bounded_slot_commutator
      p d (s + 1) 0 (Nat.succ_pos s) a (LNWord s) hlevel
  refine ⟨[⟨i, b⟩], by simp, ?_⟩
  simp [BSValue.eval,
    LNWord.evaleq_leftnormed_commvalue, hb]

/--
If each factor in a raw group list is one normalized scheduled value, the whole
list product has a normalized list whose length budget is the raw list length.
-/
lemma bounded_normalized_forall
    {p d n : ℕ} [Fact p.Prime]
    {G : Type u} [Group G]
    {L : List G}
    (hL :
      ∀ x ∈ L,
        BNZass p d n 1 x) :
    BNZass p d n L.length L.prod := by
  induction L with
  | nil =>
      simpa using bounded_normalized_one p d n
  | cons x L ih =>
      have hx : BNZass p d n 1 x :=
        hL x (by simp)
      have htail :
          BNZass p d n L.length L.prod :=
        ih (by
          intro y hy
          exact hL y (by simp [hy]))
      simpa [Nat.add_comm] using hx.mul htail

/--
The ordered TeX Lemma 5 normal form packages into a uniformly bounded
normalized Zassenhaus list.
-/
lemma normalized_normed_factorization
    {p d s : ℕ} [Fact p.Prime]
    {G : Type u} [Group G]
    {t : Fin d → G}
    {x : G}
    (hx : ONFacta d s t x) :
    BNZass
      p d (s + 1) (Fintype.card (LowerTailTuple d s)) x := by
  rcases hx with ⟨u, rfl⟩
  simpa [normed_values_length] using
    bounded_normalized_forall
      (p := p) (d := d) (n := s + 1)
      (L := orderedNormedValues d s t u)
      (by
        intro y hy
        rcases List.mem_ofFn.mp hy with ⟨i, rfl⟩
        exact
          bounded_normalized_normed
            (p := p) (d := d) _)

/--
Surjective homomorphisms send a chosen generating tuple to another generating
tuple.  This is the local non-Restricted-Burnside quotient-generation bridge
needed by TeX Lemma 5's induction.
-/
lemma generated_surjective
    {G H : Type u} [Group G] [Group H]
    {d : ℕ}
    {t : Fin d → G}
    (ht : GeneratedBy t)
    (φ : G →* H)
    (hφ : Function.Surjective φ) :
    GeneratedBy (fun i : Fin d => φ (t i)) := by
  rw [GeneratedBy] at ht ⊢
  have hrange : Set.range (fun i : Fin d => φ (t i)) = φ '' Set.range t := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨t i, ⟨i, rfl⟩, rfl⟩
    · rintro ⟨y, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, rfl⟩
  rw [hrange, ← MonoidHom.map_closure, ht,
    Subgroup.map_top_of_surjective φ hφ]

/--
TeX Lemma 2 in the exact equality form needed for quotient lifting: a
surjective homomorphism maps each lower-central term onto the target term.
-/
lemma central_series_surjective
    {G H : Type u} [Group G] [Group H]
    (φ : G →* H)
    (hφ : Function.Surjective φ)
    (i : ℕ) :
    Subgroup.map φ (Subgroup.lowerCentralSeries G i) = Subgroup.lowerCentralSeries H i := by
  apply le_antisymm
  · exact Subgroup.lowerCentralSeries.map φ i
  · induction i with
    | zero =>
        rw [Subgroup.lowerCentralSeries_zero, Subgroup.lowerCentralSeries_zero]
        exact (Subgroup.map_top_of_surjective φ hφ).ge
    | succ i ih =>
        rw [Subgroup.lowerCentralSeries_succ, Subgroup.lowerCentralSeries_succ]
        exact
          Subgroup.commutator_le_map_commutator ih
            ((Subgroup.map_top_of_surjective φ hφ).ge)

/--
Elementwise lift form of surjective preservation of lower-central terms.
-/
lemma lower_series_surjective
    {G H : Type u} [Group G] [Group H]
    (φ : G →* H)
    (hφ : Function.Surjective φ)
    {i : ℕ}
    {x : H}
    (hx : x ∈ Subgroup.lowerCentralSeries H i) :
    ∃ y : G,
      y ∈ Subgroup.lowerCentralSeries G i ∧
        φ y = x := by
  rw [← central_series_surjective φ hφ i] at hx
  rcases hx with ⟨y, hy, rfl⟩
  exact ⟨y, hy, rfl⟩

/--
The explicit left-normed commutator value is natural under group
homomorphisms.
-/
lemma normed_commutator_value
    {G H : Type u} [Group G] [Group H]
    (φ : G →* H) :
    ∀ (s : ℕ) (a : Fin (s + 1) → G),
      φ (leftNormedValue s a) =
        leftNormedValue s (fun i => φ (a i))
  | 0, _ => rfl
  | s + 1, a => by
      simp [leftNormedValue, map_commutatorElement,
        normed_commutator_value φ s]

/--
The fixed ordered TeX list maps slotwise through a group homomorphism.
-/
lemma normed_values_prod
    {G H : Type u} [Group G] [Group H]
    (φ : G →* H)
    (d s : ℕ)
    (t : Fin d → G)
    (u : LowerTailTuple d s → G) :
    φ (orderedNormedValues d s t u).prod =
      (orderedNormedValues d s
        (fun i => φ (t i))
        (fun I => φ (u I))).prod := by
  rw [map_list_prod, orderedNormedValues,
    orderedNormedValues, List.map_ofFn]
  congr 1
  apply congrArg List.ofFn
  funext i
  change
    φ (leftNormedValue s
      (lowerTupleArguments t (u (lowerTailTuple d s i))
        (lowerTailTuple d s i))) =
      _
  rw [normed_commutator_value]
  congr 1
  funext j
  cases j using Fin.cases <;> rfl

/--
Ordered TeX factorizations descend along group homomorphisms.
-/
lemma ONFacta.map
    {G H : Type u} [Group G] [Group H]
    {d s : ℕ}
    {t : Fin d → G}
    {x : G}
    (hx : ONFacta d s t x)
    (φ : G →* H) :
    ONFacta d s (fun i => φ (t i)) (φ x) := by
  rcases hx with ⟨u, rfl⟩
  refine ⟨fun I => φ (u I), ?_⟩
  exact (normed_values_prod φ d s t u).symm

/--
Choose arbitrary lifts of the free TeX Lemma 5 arguments through a quotient
map, keeping the fixed generator tail unchanged.
-/
noncomputable def liftTailArguments
    {G : Type u} [Group G]
    (N : Subgroup G) [N.Normal]
    {d s : ℕ}
    (u : LowerTailTuple d s → G ⧸ N) :
    LowerTailTuple d s → G :=
  fun I => Classical.choose (QuotientGroup.mk'_surjective N (u I))

/--
The chosen free-argument lifts recover the quotient free arguments.
-/
lemma lift_arguments_mk
    {G : Type u} [Group G]
    (N : Subgroup G) [N.Normal]
    {d s : ℕ}
    (u : LowerTailTuple d s → G ⧸ N)
    (I : LowerTailTuple d s) :
    QuotientGroup.mk' N (liftTailArguments N u I) = u I := by
  exact Classical.choose_spec (QuotientGroup.mk'_surjective N (u I))

/--
Lifting the free TeX arguments through a quotient gives a factorization whose
image is the original quotient factorization.
-/
lemma lift_normed_factorization
    {G : Type u} [Group G]
    (N : Subgroup G) [N.Normal]
    {d s : ℕ}
    (t : Fin d → G)
    {x : G}
    (hx :
      ONFacta
        d s (fun i => QuotientGroup.mk' N (t i)) (QuotientGroup.mk' N x)) :
    ∃ u : LowerTailTuple d s → G,
      ONFacta d s t
        (orderedNormedValues d s t u).prod ∧
        x * (orderedNormedValues d s t u).prod⁻¹ ∈ N := by
  rcases hx with ⟨ubar, hubar⟩
  let u : LowerTailTuple d s → G :=
    liftTailArguments N ubar
  refine ⟨u, ⟨u, rfl⟩, ?_⟩
  apply
    (QuotientGroup.eq_one_iff
      (N := N)
      (x * (orderedNormedValues d s t u).prod⁻¹)).mp
  have hmap :
      QuotientGroup.mk' N (orderedNormedValues d s t u).prod =
        (orderedNormedValues d s
          (fun i => QuotientGroup.mk' N (t i)) ubar).prod := by
    have hu :
        (fun I : LowerTailTuple d s =>
          QuotientGroup.mk' N (u I)) =
        ubar := by
      funext I
      exact lift_arguments_mk N ubar I
    calc
      QuotientGroup.mk' N (orderedNormedValues d s t u).prod =
          (orderedNormedValues d s
            (fun i => QuotientGroup.mk' N (t i))
            (fun I => QuotientGroup.mk' N (u I))).prod :=
            normed_values_prod
              (QuotientGroup.mk' N) d s t u
      _ =
          (orderedNormedValues d s
            (fun i => QuotientGroup.mk' N (t i)) ubar).prod := by
            rw [hu]
  calc
    QuotientGroup.mk' N
        (x * (orderedNormedValues d s t u).prod⁻¹) =
        QuotientGroup.mk' N x *
          (QuotientGroup.mk' N
            (orderedNormedValues d s t u).prod)⁻¹ := by
          simp only [map_mul, map_inv]
    _ =
        QuotientGroup.mk' N x *
          ((orderedNormedValues d s
            (fun i => QuotientGroup.mk' N (t i)) ubar).prod)⁻¹ := by
          rw [hmap]
    _ = 1 := by
          simp only [hubar, mul_inv_cancel]

/--
The central tail form needed by TeX Lemma 5's last-lower-central absorption
step.  The witness remembers TeX's stronger source-depth condition
`v_I ∈ γ_(c-r+1)(G)`, written in zero-based Lean indexing as
`Subgroup.lowerCentralSeries G (c - (s + 1))`.
-/
def NTFact
    {G : Type u} [Group G]
    (d s c : ℕ)
    (t : Fin d → G)
    (z : G) :
    Prop :=
  ∃ v : LowerTailTuple d s → G,
    (∀ I : LowerTailTuple d s,
      v I ∈ Subgroup.lowerCentralSeries G (c - (s + 1))) ∧
      (orderedNormedValues d s t v).prod = z

/--
Forget the source-depth certificate from a central-tail factorization.
-/
lemma NTFact.toFactorization
    {G : Type u} [Group G]
    {d s c : ℕ}
    {t : Fin d → G}
    {z : G}
    (hz : NTFact d s c t z) :
    ONFacta d s t z := by
  rcases hz with ⟨v, _hvMem, hvProd⟩
  exact ⟨v, hvProd⟩

/--
Membership in the ambient central-tail range unwraps to the original TeX
source-depth witness function.
-/
lemma normed_factorization_range
    {G : Type u} [Group G]
    {d s c : ℕ}
    (hsLe : s ≤ c - 1)
    (hcPos : 0 < c)
    (hcBot : Subgroup.lowerCentralSeries G c = ⊥)
    (t : Fin d → G)
    {z : G}
    (hz : z ∈ tailRangeSubgroup hsLe hcPos hcBot t) :
    NTFact d s c t z := by
  rcases hz with ⟨w, ⟨v, rfl⟩, rfl⟩
  refine ⟨fun I => (v I : G), fun I => (v I).property, ?_⟩
  exact (coe_monoid_prod hsLe hcPos hcBot t v).symm

/--
Quotienting by the last lower-central term kills that term in the quotient.
-/
lemma lower_last_bot
    {G : Type u} [Group G]
    {c : ℕ} :
    Subgroup.lowerCentralSeries
        (G ⧸ Subgroup.lowerCentralSeries G (c - 1))
        (c - 1) =
      ⊥ := by
  let q : G →* G ⧸ Subgroup.lowerCentralSeries G (c - 1) :=
    QuotientGroup.mk' (Subgroup.lowerCentralSeries G (c - 1))
  rw [← central_series_surjective
      q (QuotientGroup.mk'_surjective _) (c - 1)]
  apply (Subgroup.map_eq_bot_iff _).2
  simp [q, QuotientGroup.ker_mk']

/--
The last-lower-central quotient has strictly smaller nilpotency class, giving
the induction measure decrease in TeX Lemma 5.
-/
lemma last_nilpotency_class
    {G : Type u} [Group G] [Group.IsNilpotent G]
    {c : ℕ}
    (hcPos : 0 < c) :
    Group.nilpotencyClass
        (G ⧸ Subgroup.lowerCentralSeries G (c - 1)) <
      c := by
  letI :
      Group.IsNilpotent (G ⧸ Subgroup.lowerCentralSeries G (c - 1)) :=
    Group.nilpotent_quotient_of_nilpotent (Subgroup.lowerCentralSeries G (c - 1))
  have hbot :
      Subgroup.lowerCentralSeries
          (G ⧸ Subgroup.lowerCentralSeries G (c - 1))
          (c - 1) =
        ⊥ :=
    lower_last_bot (G := G)
  have hle :
      Group.nilpotencyClass
          (G ⧸ Subgroup.lowerCentralSeries G (c - 1)) ≤
        c - 1 :=
    Subgroup.lowerCentralSeries_eq_bot_iff_nilpotencyClass_le.mp hbot
  omega

/--
TeX Lemma 5's central-tail collection subclaim: once the last nontrivial lower
central term is central, each of its elements is already a fixed ordered
product of left-normed commutators with factors remaining in that central term.
-/
theorem normed_factorization_last
    {G : Type u} [Group G]
    {d s c : ℕ}
    (_hd : 0 < d)
    (hsLe : s ≤ c - 1)
    (hcPos : 0 < c)
    (hcBot : Subgroup.lowerCentralSeries G c = ⊥)
    (t : Fin d → G)
    (ht : GeneratedBy t)
    {z : G}
    (hz : z ∈ Subgroup.lowerCentralSeries G (c - 1)) :
    NTFact d s c t z := by
  classical
  let P : ℕ → Prop :=
    fun s =>
      ∀ (H : Type u) [Group H],
        ∀ {c : ℕ},
          s ≤ c - 1 →
            0 < c →
              Subgroup.lowerCentralSeries H c = ⊥ →
                ∀ (tH : Fin d → H),
                  GeneratedBy tH →
                    ∀ {z : H},
                      z ∈ Subgroup.lowerCentralSeries H (c - 1) →
                        NTFact d s c tH z
  have hP : ∀ s : ℕ, P s := by
    intro s
    induction s with
    | zero =>
        dsimp [P]
        intro H _instGroupH c _hsLeH _hcPosH _hcBotH tH _htH z hzH
        refine ⟨fun _ => z, ?_, ?_⟩
        · intro I
          exact hzH
        · simp [orderedNormedValues,
            leftNormedValue, lowerTupleArguments]
    | succ s ih =>
        dsimp [P] at ih ⊢
        intro H _instGroupH c hsLeH hcPosH hcBotH tH htH z hzH
        have hcTwo : 2 ≤ c := by omega
        let R : Subgroup H := tailRangeSubgroup hsLeH hcPosH hcBotH tH
        letI : R.Normal := by
          simpa [R] using tail_range_normal hsLeH hcPosH hcBotH tH
        have hRmem : z ∈ R := by
          have hcommLe :
              ⁅Subgroup.lowerCentralSeries H (c - 2), (⊤ : Subgroup H)⁆ ≤ R := by
            rw [Subgroup.commutator_le]
            intro y hy g _hg
            have hgen :
                ∀ j : Fin d, ⁅y, tH j⁆ ∈ R := by
              intro j
              let Z : Subgroup H := Subgroup.lowerCentralSeries H (c - 1)
              letI : Z.Normal := by
                dsimp [Z]
                infer_instance
              let q : H →* H ⧸ Z := QuotientGroup.mk' Z
              have hqGenerated :
                  GeneratedBy (fun i : Fin d => q (tH i)) :=
                generated_surjective htH q (QuotientGroup.mk'_surjective Z)
              have hsLeQuot : s ≤ (c - 1) - 1 := by omega
              have hcPredPos : 0 < c - 1 := by omega
              have hqBot :
                  Subgroup.lowerCentralSeries (H ⧸ Z) (c - 1) = ⊥ := by
                simpa [Z] using lower_last_bot (G := H) (c := c)
              have hyQuot :
                  q y ∈ Subgroup.lowerCentralSeries (H ⧸ Z) ((c - 1) - 1) := by
                have hmap :
                    q y ∈ Subgroup.lowerCentralSeries (H ⧸ Z) (c - 2) :=
                  Subgroup.lowerCentralSeries.map q (c - 2) (Subgroup.mem_map_of_mem q hy)
                simpa using hmap
              have hquotCentral :
                  NTFact
                    d s (c - 1) (fun i : Fin d => q (tH i)) (q y) :=
                ih (H ⧸ Z) (c := c - 1) hsLeQuot hcPredPos hqBot
                  (fun i : Fin d => q (tH i)) hqGenerated hyQuot
              rcases hquotCentral with ⟨vbar, hvbarMem, hvbarProd⟩
              have hsourceIndex :
                  (c - 1) - (s + 1) = c - ((s + 1) + 1) := by
                omega
              let liftData :
                  ∀ I : LowerTailTuple d s,
                    ∃ v : H,
                      v ∈ Subgroup.lowerCentralSeries H (c - ((s + 1) + 1)) ∧
                        q v = vbar I :=
                fun I =>
                  lower_series_surjective
                    q (QuotientGroup.mk'_surjective Z)
                    (by simpa [hsourceIndex] using hvbarMem I)
              let v : LowerTailTuple d s → H :=
                fun I => Classical.choose (liftData I)
              have hvMem :
                  ∀ I : LowerTailTuple d s,
                    v I ∈ Subgroup.lowerCentralSeries H (c - ((s + 1) + 1)) := by
                intro I
                exact (Classical.choose_spec (liftData I)).1
              have hvMap :
                  ∀ I : LowerTailTuple d s,
                    q (v I) = vbar I := by
                intro I
                exact (Classical.choose_spec (liftData I)).2
              let collected : List H := orderedNormedValues d s tH v
              have hvMapFun :
                  (fun I : LowerTailTuple d s => q (v I)) = vbar := by
                funext I
                exact hvMap I
              have hprefixMap : q collected.prod = q y := by
                calc
                  q collected.prod =
                      (orderedNormedValues d s
                        (fun i : Fin d => q (tH i))
                        (fun I : LowerTailTuple d s => q (v I))).prod := by
                        simpa [collected] using
                          normed_values_prod q d s tH v
                  _ =
                      (orderedNormedValues d s
                        (fun i : Fin d => q (tH i)) vbar).prod := by
                        rw [hvMapFun]
                  _ = q y := hvbarProd
              let residual : H := y * collected.prod⁻¹
              have hresidualMem : residual ∈ Z := by
                apply (QuotientGroup.eq_one_iff (N := Z) residual).mp
                calc
                  q residual = q y * (q collected.prod)⁻¹ := by
                    simp [residual]
                  _ = 1 := by rw [hprefixMap]; simp
              have hresidualCenter : residual ∈ Subgroup.center H := by
                simpa [Z] using last_term_center hcPosH hcBotH hresidualMem
              have hcommResidual :
                  ⁅y, tH j⁆ = ⁅collected.prod, tH j⁆ := by
                have hyDecomp : y = residual * collected.prod := by
                  dsimp [residual]
                  group
                rw [hyDecomp, element_mul_left]
                have hconj :
                    residual * ⁅collected.prod, tH j⁆ * residual⁻¹ =
                      ⁅collected.prod, tH j⁆ := by
                  have hcomm :
                      residual * ⁅collected.prod, tH j⁆ =
                        ⁅collected.prod, tH j⁆ * residual :=
                    (Subgroup.mem_center_iff.mp hresidualCenter _).symm
                  rw [hcomm, mul_inv_cancel_right]
                have hresComm : Commute residual (tH j) := by
                  exact
                    (show Commute (tH j) residual from
                      Subgroup.mem_center_iff.mp hresidualCenter (tH j)).symm
                rw [hconj, commutatorElement_eq_one_iff_commute.mpr hresComm,
                  mul_one]
              have hprefixFactorMem :
                  ∀ x ∈ collected, x ∈ Subgroup.lowerCentralSeries H (c - 2) := by
                intro x hx
                dsimp [collected, orderedNormedValues] at hx
                rcases List.mem_ofFn.mp hx with ⟨i, rfl⟩
                have hmem :
                    leftNormedValue s
                        (lowerTupleArguments tH
                          (v (lowerTailTuple d s i))
                          (lowerTailTuple d s i)) ∈
                      Subgroup.lowerCentralSeries H (c - ((s + 1) + 1) + s) :=
                  left_normed_series
                    s _ (hvMem (lowerTailTuple d s i))
                have hindex : c - ((s + 1) + 1) + s = c - 2 := by omega
                simpa [hindex] using hmem
              have hcommCenter :
                  ∀ x ∈ collected, ⁅x, tH j⁆ ∈ Subgroup.center H := by
                intro x hx
                exact
                  last_center_pred
                    hcTwo hcPosH hcBotH (hprefixFactorMem x hx)
              have hcommProd :
                  ⁅collected.prod, tH j⁆ =
                    (collected.map fun x => ⁅x, tH j⁆).prod :=
                commutator_forall_center
                  collected (tH j) hcommCenter
              have hmapMem :
                  ∀ w ∈ collected.map (fun x => ⁅x, tH j⁆), w ∈ R := by
                intro w hw
                rcases List.mem_map.mp hw with ⟨x, hx, rfl⟩
                dsimp [collected, orderedNormedValues] at hx
                rcases List.mem_ofFn.mp hx with ⟨i, rfl⟩
                let I : LowerTailTuple d s := lowerTailTuple d s i
                let fullI : LowerTailTuple d (s + 1) :=
                  @Fin.snoc s (fun _ : Fin (s + 1) => Fin d) I j
                let vI : Subgroup.lowerCentralSeries H (c - ((s + 1) + 1)) :=
                  ⟨v I, by simpa [I] using hvMem I⟩
                have hbasic :
                    leftNormedValue (s + 1)
                        (lowerTupleArguments tH (v I) fullI) ∈ R := by
                  simpa [R, vI] using
                    tail_range_value
                      (s := s + 1) hsLeH hcPosH hcBotH tH fullI vI
                rw [normed_snoc_tail tH (v I) I j]
                exact hbasic
              have hmapProdMem :
                  (collected.map fun x => ⁅x, tH j⁆).prod ∈ R := by
                apply Subgroup.list_prod_mem
                exact hmapMem
              rw [hcommResidual, hcommProd]
              exact hmapProdMem
            apply element_closure_generator
              (A := Set.range tH) R
            · intro x hx
              rcases hx with ⟨j, rfl⟩
              exact hgen j
            · rw [htH]
              exact Subgroup.mem_top g
          have hzComm :
              z ∈ ⁅Subgroup.lowerCentralSeries H (c - 2), (⊤ : Subgroup H)⁆ := by
            exact commutator_last_term hcTwo hzH
          exact hcommLe hzComm
        exact
          normed_factorization_range
            hsLeH hcPosH hcBotH tH hRmem
  exact hP s G hsLe hcPos hcBot t ht hz

/--
TeX Lemma 5's absorption subclaim: source-depth controlled ordered tail
factors can be folded into the free first arguments of an existing ordered
factorization once the next lower-central term vanishes.
-/
theorem NTFact.absorb_left
    {G : Type u} [Group G]
    {d s c : ℕ}
    {t : Fin d → G}
    {z x : G}
    (hsLe : s ≤ c - 1)
    (hcPos : 0 < c)
    (hcBot : Subgroup.lowerCentralSeries G c = ⊥)
    (hz : NTFact d s c t z)
    (hx : ONFacta d s t x) :
    ONFacta d s t (z * x) := by
  classical
  rcases hz with ⟨v, hvMem, hvProd⟩
  rcases hx with ⟨u, huProd⟩
  let m : ℕ := Fintype.card (LowerTailTuple d s)
  let I : Fin m → LowerTailTuple d s :=
    lowerTailTuple d s
  let a : Fin m → G :=
    fun i =>
      leftNormedValue s
        (lowerTupleArguments t (v (I i)) (I i))
  let b : Fin m → G :=
    fun i =>
      leftNormedValue s
        (lowerTupleArguments t (u (I i)) (I i))
  refine ⟨fun J => u J * v J, ?_⟩
  have hnew :
      (orderedNormedValues d s t (fun J => u J * v J)).prod =
        (List.ofFn fun i : Fin m => a i * b i).prod := by
    unfold orderedNormedValues
    congr 1
    apply congrArg List.ofFn
    funext i
    simpa [a, b, I, lowerTupleArguments] using
      left_normed_zero
        hsLe hcPos hcBot (u (I i)) (v (I i))
        (fun j : Fin s => t (I i j))
        (hvMem (I i))
  have haCenter :
      ∀ i : Fin m, a i ∈ Subgroup.center G := by
    intro i
    apply last_term_center hcPos hcBot
    apply left_normed_last hsLe
    simpa [a, I, lowerTupleArguments] using hvMem (I i)
  calc
    (orderedNormedValues d s t (fun J => u J * v J)).prod =
        (List.ofFn fun i : Fin m => a i * b i).prod :=
          hnew
    _ = (List.ofFn a).prod * (List.ofFn b).prod :=
          fn_forall_center a b haCenter
    _ = (orderedNormedValues d s t v).prod *
          (orderedNormedValues d s t u).prod := by
          simp [a, b, I, m, orderedNormedValues]
    _ = z * x := by rw [hvProd, huProd]

/--
TeX Lemma 5 itself, now isolated as the pure nilpotent fixed-family width
statement.  The surrounding p-group and normalized-schedule packaging has
already been discharged above.
-/
theorem normed_factorization_nilpotent
    {G : Type u} [Group G] [Group.IsNilpotent G]
    {d s : ℕ}
    (hd : 0 < d)
    (t : Fin d → G)
    (ht : GeneratedBy t)
    {x : G}
    (hx : x ∈ Subgroup.lowerCentralSeries G s) :
    ONFacta d s t x := by
  classical
  let P : ℕ → Prop :=
    fun c =>
      ∀ (H : Type u) [Group H] [Group.IsNilpotent H],
        Group.nilpotencyClass H = c →
          ∀ (tH : Fin d → H),
            GeneratedBy tH →
              ∀ {y : H},
                y ∈ Subgroup.lowerCentralSeries H s →
                  ONFacta d s tH y
  have hP : ∀ c : ℕ, P c := by
    intro c
    induction c using Nat.strong_induction_on with
    | h c ih =>
        intro H _instGroupH _instNilpotentH hcClass tH htH y hy
        by_cases htermBot : Subgroup.lowerCentralSeries H s = ⊥
        · have hyOne : y = 1 := eq_bot_iff.mp htermBot hy
          subst y
          exact normed_lower_factorization d s tH
        have hcPos : 0 < c := by
          by_contra hcNotPos
          have hcZero : c = 0 := Nat.eq_zero_of_not_pos hcNotPos
          have hSubsingleton : Subsingleton H :=
            Group.nilpotencyClass_zero_iff_subsingleton.mp (hcClass.trans hcZero)
          have hbot : Subgroup.lowerCentralSeries H s = ⊥ := Subsingleton.elim _ _
          exact htermBot hbot
        have hcBot : Subgroup.lowerCentralSeries H c = ⊥ := by
          simpa [hcClass] using
            (Subgroup.lowerCentralSeries_nilpotencyClass (G := H))
        have hsLt : s < c := by
          by_contra hsNotLt
          have hcLeS : c ≤ s := Nat.le_of_not_gt hsNotLt
          have hbot : Subgroup.lowerCentralSeries H s = ⊥ := by
            rw [eq_bot_iff]
            intro z hz
            exact eq_bot_iff.mp hcBot (Subgroup.lowerCentralSeries_antitone hcLeS hz)
          exact htermBot hbot
        let Z : Subgroup H := Subgroup.lowerCentralSeries H (c - 1)
        let q : H →* H ⧸ Z := QuotientGroup.mk' Z
        letI : Group.IsNilpotent (H ⧸ Z) :=
          Group.nilpotent_quotient_of_nilpotent Z
        have hqClassLt : Group.nilpotencyClass (H ⧸ Z) < c := by
          simpa [Z] using
            (last_nilpotency_class
              (G := H) hcPos)
        have hqGenerated :
            GeneratedBy (fun i : Fin d => q (tH i)) :=
          generated_surjective htH q (QuotientGroup.mk'_surjective Z)
        have hyQuot :
            q y ∈ Subgroup.lowerCentralSeries (H ⧸ Z) s :=
          Subgroup.lowerCentralSeries.map q s (Subgroup.mem_map_of_mem q hy)
        have hquotFactor :
            ONFacta
              d s (fun i : Fin d => q (tH i)) (q y) :=
          ih (Group.nilpotencyClass (H ⧸ Z)) hqClassLt
            (H ⧸ Z) rfl (fun i : Fin d => q (tH i)) hqGenerated hyQuot
        obtain ⟨u, huFactor, hresidualMem⟩ :=
          lift_normed_factorization Z tH hquotFactor
        let residual : H :=
          y * (orderedNormedValues d s tH u).prod⁻¹
        have hsLe : s ≤ c - 1 := by
          omega
        have hcentralTail :
            NTFact d s c tH residual := by
          simpa [Z, residual] using
            normed_factorization_last
              hd hsLe hcPos hcBot tH htH hresidualMem
        have habsorb :
            ONFacta
              d s tH
              (residual * (orderedNormedValues d s tH u).prod) :=
          hcentralTail.absorb_left hsLe hcPos hcBot huFactor
        have hresidualMul :
            residual * (orderedNormedValues d s tH u).prod = y := by
          dsimp [residual]
          group
        simpa [hresidualMul] using habsorb
  exact hP (Group.nilpotencyClass G) G rfl t ht hx

/--
For TeX Lemmas 11-12 we quotient by `γ_n(Q)`.  With Lean's one-based lower
central indexing this is `Subgroup.lowerCentralSeries Q (n - 1)`.
-/
abbrev LowerCentralTruncation
    (Q : Type u) [Group Q]
    (n : ℕ) :
    Type u :=
  Q ⧸ Subgroup.lowerCentralSeries Q (n - 1)

/--
The quotient map `Q -> Q / γ_n(Q)` used in TeX Lemmas 11-12.
-/
abbrev lowerCentralTruncation
    (Q : Type u) [Group Q]
    (n : ℕ) :
    Q →* LowerCentralTruncation Q n :=
  QuotientGroup.mk' (Subgroup.lowerCentralSeries Q (n - 1))

/--
Lift one normalized scheduled value through an arbitrary quotient map by
choosing a lift for each argument of its selected slot.
-/
noncomputable def liftScheduledValue
    {p d n : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q]
    (N : Subgroup Q) [N.Normal]
    (z : BSValue p d n (Q ⧸ N)) :
    BSValue p d n Q :=
  ⟨z.1, fun j => Classical.choose (QuotientGroup.mk'_surjective N (z.2 j))⟩

/--
The chosen argument lifts recover the original quotient scheduled value after
evaluation.  This is the formal content of the "choose arbitrary lifts of the
coset arguments" sentence in TeX Lemma 12.
-/
lemma lift_bounded_scheduled
    {p d n : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q]
    (N : Subgroup Q) [N.Normal]
    (z : BSValue p d n (Q ⧸ N)) :
    QuotientGroup.mk' N
        (liftScheduledValue N z).eval =
      z.eval := by
  change
    QuotientGroup.mk' N
        (((boundedZassenhausSchedule p d n).slot z.1).eval
          (fun j => Classical.choose (QuotientGroup.mk'_surjective N (z.2 j)))) =
      ((boundedZassenhausSchedule p d n).slot z.1).eval z.2
  rw [ZWScheme.eval_map]
  congr 1
  funext j
  exact Classical.choose_spec (QuotientGroup.mk'_surjective N (z.2 j))

/--
Lift an entire normalized quotient list entrywise.
-/
noncomputable def liftScheduledList
    {p d n : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q]
    (N : Subgroup Q) [N.Normal]
    (L : List (BSValue p d n (Q ⧸ N))) :
    List (BSValue p d n Q) :=
  L.map (liftScheduledValue N)

/--
Entrywise quotient lifts preserve list length.
-/
lemma lift_scheduled_length
    {p d n : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q]
    (N : Subgroup Q) [N.Normal]
    (L : List (BSValue p d n (Q ⧸ N))) :
    (liftScheduledList N L).length = L.length := by
  simp [liftScheduledList]

/--
Evaluating the lifted list and then quotienting gives the original quotient
product.  This is the list-level form of TeX Lemma 12's lifted factorization.
-/
lemma lift_scheduled_prod
    {p d n : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q]
    (N : Subgroup Q) [N.Normal]
    (L : List (BSValue p d n (Q ⧸ N))) :
    QuotientGroup.mk' N
        ((liftScheduledList N L).map
          BSValue.eval).prod =
      (L.map BSValue.eval).prod := by
  induction L with
  | nil =>
      simp [liftScheduledList]
  | cons z L ih =>
      simp only [liftScheduledList, List.map_cons,
        List.prod_cons, map_mul]
      have htail :
          QuotientGroup.mk' N
              (List.map BSValue.eval
                (List.map (liftScheduledValue N) L)).prod =
            (L.map BSValue.eval).prod := by
          simpa [liftScheduledList] using ih
      rw [lift_bounded_scheduled, htail]

/--
Map one normalized scheduled value through a group homomorphism by applying
the homomorphism to its chosen slot arguments.
-/
def boundedScheduledValue
    {p d n : ℕ} [Fact p.Prime]
    {G H : Type u} [Group G] [Group H]
    (φ : G →* H)
    (z : BSValue p d n G) :
    BSValue p d n H :=
  ⟨z.1, fun j => φ (z.2 j)⟩

/--
Evaluation of a normalized scheduled value commutes with homomorphisms.
-/
lemma bounded_scheduled_eval
    {p d n : ℕ} [Fact p.Prime]
    {G H : Type u} [Group G] [Group H]
    (φ : G →* H)
    (z : BSValue p d n G) :
    (boundedScheduledValue φ z).eval = φ z.eval := by
  change
    ((boundedZassenhausSchedule p d n).slot z.1).eval
        (fun j => φ (z.2 j)) =
      φ (((boundedZassenhausSchedule p d n).slot z.1).eval z.2)
  exact (ZWScheme.eval_map _ φ z.2).symm

/--
Map a normalized scheduled list entrywise through a group homomorphism.
-/
def boundedScheduledList
    {p d n : ℕ} [Fact p.Prime]
    {G H : Type u} [Group G] [Group H]
    (φ : G →* H)
    (L : List (BSValue p d n G)) :
    List (BSValue p d n H) :=
  L.map (boundedScheduledValue φ)

/--
Entrywise homomorphic images preserve normalized-list length.
-/
lemma bounded_scheduled_length
    {p d n : ℕ} [Fact p.Prime]
    {G H : Type u} [Group G] [Group H]
    (φ : G →* H)
    (L : List (BSValue p d n G)) :
    (boundedScheduledList φ L).length = L.length := by
  simp [boundedScheduledList]

/--
Evaluating a homomorphic image of a normalized list gives the homomorphic
image of its evaluated product.
-/
lemma bounded_scheduled_prod
    {p d n : ℕ} [Fact p.Prime]
    {G H : Type u} [Group G] [Group H]
    (φ : G →* H)
    (L : List (BSValue p d n G)) :
    ((boundedScheduledList φ L).map
      BSValue.eval).prod =
      φ ((L.map BSValue.eval).prod) := by
  induction L with
  | nil =>
      simp [boundedScheduledList]
  | cons z L ih =>
      simp [boundedScheduledList,
        bounded_scheduled_eval]
      simpa only [boundedScheduledList, List.map_map] using ih

/--
A bounded normalized factorization transports through a group homomorphism
without increasing its list budget.
-/
lemma BNZass.mapHom
    {p d n k : ℕ} [Fact p.Prime]
    {G H : Type u} [Group G] [Group H]
    {x : G}
    (φ : G →* H)
    (hx : BNZass p d n k x) :
    BNZass p d n k (φ x) := by
  rcases hx with ⟨L, hLlen, hLprod⟩
  refine ⟨boundedScheduledList φ L, ?_, ?_⟩
  · simpa [bounded_scheduled_length] using hLlen
  · rw [bounded_scheduled_prod, hLprod]

/--
TeX Lemma 11, isolated as the quotient-level hard leaf: after passing from
`Q` to `Q / γ_n(Q)`, every image of a `D_n(Q)` element has a uniformly bounded
normalized factorization.  The full Hall-coordinate proof in the TeX file
should eventually discharge this proposition from Lemmas 6-10.
-/
def TruncatedCollectionBound
    (p d n k : ℕ) [Fact p.Prime] :
    Prop :=
  ∀ (Q : Type u) [Group Q] [Finite Q],
    IsPGroup p Q →
      ∀ t : Fin d → Q,
        GeneratedBy t →
          ∀ x : Q,
            x ∈ zassenhausFiltration p Q n →
              BNZass
                p d n k
                (lowerCentralTruncation Q n x)

/--
Universe-lifted free generators corresponding to the `d` chosen generators in
an ambient group of universe `u`.
-/
abbrev FreeGenerator
    (d : ℕ) :
    Type u :=
  ULift.{u} (Fin d)

/--
The TeX layer `γ_r(G) / γ_(r+1)(G)`, translated through Lean's zero-based
`lowerCentralSeries` convention.  This is an abelian quotient even before a
Hall basis is chosen.
-/
abbrev AssociatedGradedLayer
    (G : Type u) [Group G]
    (r : ℕ) :
    Type u :=
  (Subgroup.lowerCentralSeries G (r - 1)) ⧸
    ((Subgroup.lowerCentralSeries G r).subgroupOf (Subgroup.lowerCentralSeries G (r - 1)))

/--
The commutator of `γ_r(G)` with itself lands in `γ_(r+1)(G)`, in the
one-based TeX indexing used by Claim 1.
-/
lemma lower_self_succ
    {G : Type u} [Group G]
    (r : ℕ) :
    ⁅Subgroup.lowerCentralSeries G (r - 1), Subgroup.lowerCentralSeries G (r - 1)⁆ ≤
      Subgroup.lowerCentralSeries G r := by
  by_cases hr : r = 0
  · subst r
    simp
  · have hrPos : 0 < r := Nat.pos_of_ne_zero hr
    have hcomm :
        ⁅Subgroup.lowerCentralSeries G (r - 1), Subgroup.lowerCentralSeries G 0⁆ ≤
          Subgroup.lowerCentralSeries G ((r - 1) + 0 + 1) :=
      lower_commutator_succ (r - 1) 0
    simpa [Subgroup.lowerCentralSeries_zero, Nat.sub_add_cancel hrPos] using
      (Subgroup.commutator_mono le_rfl
        (show Subgroup.lowerCentralSeries G (r - 1) ≤ Subgroup.lowerCentralSeries G 0 by
          simp)).trans
        hcomm

instance associated_graded_commutative
    {G : Type u} [Group G]
    (r : ℕ) :
    IsMulCommutative (AssociatedGradedLayer G r) := by
  rw [Subgroup.Normal.quotient_commutative_iff_commutator_le]
  let A : Subgroup G := Subgroup.lowerCentralSeries G (r - 1)
  let B : Subgroup G := Subgroup.lowerCentralSeries G r
  change _root_.commutator A ≤ B.comap A.subtype
  rw [← Subgroup.map_le_iff_le_comap]
  rw [_root_.commutator_def, Subgroup.map_commutator]
  rw [← MonoidHom.range_eq_map, A.range_subtype]
  exact lower_self_succ r

/-- The bundled commutative-group structure on a lower-central graded
layer, assembled directly to avoid expensive scoped instance search. -/
noncomputable instance associated_graded_comm
    {G : Type u} [Group G]
    (r : ℕ) :
    CommGroup (AssociatedGradedLayer G r) :=
  { (inferInstance : Group (AssociatedGradedLayer G r)) with
    mul_comm := mul_comm' }

/--
Restrict a homomorphism to one lower-central term.
-/
def lowerSeriesRestriction
    {G H : Type u} [Group G] [Group H]
    (φ : G →* H)
    (i : ℕ) :
    Subgroup.lowerCentralSeries G i →* Subgroup.lowerCentralSeries H i :=
  (φ.comp (Subgroup.lowerCentralSeries G i).subtype).codRestrict
    (Subgroup.lowerCentralSeries H i)
    (fun x =>
      Subgroup.lowerCentralSeries.map φ i
        (Subgroup.mem_map_of_mem φ x.property))

/--
A homomorphism induces a map on one lower-central associated-graded layer.
-/
def centralAssociatedGraded
    {G H : Type u} [Group G] [Group H]
    (φ : G →* H)
    (r : ℕ) :
    AssociatedGradedLayer G r →*
      AssociatedGradedLayer H r := by
  let sourceTerm : Subgroup G := Subgroup.lowerCentralSeries G (r - 1)
  let sourceNext : Subgroup G := Subgroup.lowerCentralSeries G r
  let targetTerm : Subgroup H := Subgroup.lowerCentralSeries H (r - 1)
  let targetNext : Subgroup H := Subgroup.lowerCentralSeries H r
  let φr : sourceTerm →* targetTerm :=
    lowerSeriesRestriction φ (r - 1)
  apply QuotientGroup.map (sourceNext.subgroupOf sourceTerm)
    (targetNext.subgroupOf targetTerm) φr
  intro x hx
  change φ x ∈ targetNext
  exact Subgroup.lowerCentralSeries.map φ r
    (Subgroup.mem_map_of_mem φ (show (x : G) ∈ sourceNext from hx))

/--
The induced lower-central graded map sends a represented class to the class of
its homomorphic image.
-/
lemma lower_graded_mk
    {G H : Type u} [Group G] [Group H]
    (φ : G →* H)
    (r : ℕ)
    (x : Subgroup.lowerCentralSeries G (r - 1)) :
    centralAssociatedGraded φ r
        (QuotientGroup.mk'
          ((Subgroup.lowerCentralSeries G r).subgroupOf (Subgroup.lowerCentralSeries G (r - 1)))
            x) =
      QuotientGroup.mk'
        ((Subgroup.lowerCentralSeries H r).subgroupOf (Subgroup.lowerCentralSeries H (r - 1)))
        (lowerSeriesRestriction φ (r - 1) x) :=
  rfl

/--
One chosen Hall basic commutator of ordinary weight `r` in the free generators.
Claim 1 only consumes the representing binary word and its weight certificate;
later Hall-coordinate claims can add the collection/order data around this
carrier.
-/
structure BCWt
    (d r : ℕ) where
  word : CWord (FreeGenerator.{u} d)
  word_weight : word.weight (fun _ => 1) = r

/--
The finite ordered family of Hall basic commutators of one fixed ordinary
weight.  The order is the fixed Hall order from the TeX setup, restricted to
this weight.
-/
structure BCWta
    (d r : ℕ) where
  index : Type u
  [fintypeIndex : Fintype index]
  [linearOrderIndex : LinearOrder index]
  commutator : index → BCWt.{u} d r

attribute [instance] BCWta.fintypeIndex
attribute [instance] BCWta.linearOrderIndex

/--
The canonical Hall basic commutators of fixed weight used internally by the
collection-bound endpoint.  This is the same Hall-tree enumeration used by the
concrete Hall basis files, but kept here so the final free-truncation bound can
depend on the Hall-Petresco theorem without creating an import cycle.
-/
noncomputable def collectionConcreteCommutators
    (d r : ℕ) :
    BCWta.{u} d r where
  index := ULift.{u} (HallTree.BasicIndex (α := FreeGenerator.{u} d) r)
  commutator i :=
    { word := HallTree.indexedCommutatorWord i.down
      word_weight := HallTree.indexed_commutator_weight i.down }

/--
The image in `F_d / γ_n(F_d)` of one free generator from the TeX setup.
-/
def freeTruncationValue
    (d n : ℕ)
    (i : FreeGenerator.{u} d) :
    LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n :=
  lowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n (FreeGroup.of i)

/--
Evaluate one chosen Hall basic commutator in `F_d / γ_n(F_d)`.
-/
def BCWt.freeLowerTruncation
    {d n r : ℕ}
    (h : BCWt.{u} d r) :
    LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n :=
  h.word.eval (freeTruncationValue d n)

/--
Evaluate one chosen Hall basic commutator in the free group before truncation.
-/
def BCWt.eval_in_freegroup
    {d r : ℕ}
    (h : BCWt.{u} d r) :
    FreeGroup (FreeGenerator.{u} d) :=
  h.word.eval FreeGroup.of

/--
A weight-`r` Hall basic commutator evaluates in `γ_r(F_d)`.
-/
lemma BCWt.evalin_freegroupmem_lowecentseri
    {d r : ℕ}
    (h : BCWt.{u} d r) :
    h.eval_in_freegroup ∈
      Subgroup.lowerCentralSeries (FreeGroup (FreeGenerator.{u} d)) (r - 1) := by
  simpa [BCWt.eval_in_freegroup, h.word_weight] using
    (CWord.eval_lower_series
      FreeGroup.of
      (fun _ : FreeGenerator.{u} d => 1)
      (fun _ => by norm_num)
      (fun _ => by simp)
      h.word)

/--
A weight-`r` Hall basic commutator evaluates in `γ_r`, so it has a class in the
TeX associated graded layer `γ_r / γ_(r+1)`.
-/
lemma BCWt.free_truncation_series
    {d n r : ℕ}
    (h : BCWt.{u} d r) :
    h.freeLowerTruncation (n := n) ∈
      Subgroup.lowerCentralSeries
        (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n) (r - 1) := by
  simpa [BCWt.freeLowerTruncation, h.word_weight] using
    (CWord.eval_lower_series
      (freeTruncationValue d n)
      (fun _ : FreeGenerator.{u} d => 1)
      (fun _ => by norm_num)
      (fun _ => by simp)
      h.word)

/--
The associated-graded image of one chosen Hall basic commutator.
-/
def BCWt.associatedGradedClass
    {d n r : ℕ}
    (h : BCWt.{u} d r) :
    Additive
      (AssociatedGradedLayer
        (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n) r) :=
  Additive.ofMul
    (QuotientGroup.mk'
      ((Subgroup.lowerCentralSeries
        (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n) r).subgroupOf
          (Subgroup.lowerCentralSeries
            (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n) (r - 1)))
      ⟨h.freeLowerTruncation (n := n),
        h.free_truncation_series⟩)

/--
The associated-graded image of one chosen Hall basic commutator before passing
to `F_d / γ_n(F_d)`.
-/
def BCWt.free_groupassoc_gradedclass
    {d r : ℕ}
    (h : BCWt.{u} d r) :
    Additive
      (AssociatedGradedLayer (FreeGroup (FreeGenerator.{u} d)) r) :=
  Additive.ofMul
    (QuotientGroup.mk'
      ((Subgroup.lowerCentralSeries (FreeGroup (FreeGenerator.{u} d)) r).subgroupOf
        (Subgroup.lowerCentralSeries (FreeGroup (FreeGenerator.{u} d)) (r - 1)))
      ⟨h.eval_in_freegroup, h.evalin_freegroupmem_lowecentseri⟩)

/--
Formal statement of the classical basic-commutator theorem in the free group
layer before TeX Claim 1 passes to `F_d / γ_n(F_d)`.
-/
def BCWta.FormsfreeGroupassocGradedbasis
    {d r : ℕ}
    (H : BCWta.{u} d r) :
    Prop :=
  ∃ b : Module.Basis H.index ℤ
      (Additive
        (AssociatedGradedLayer (FreeGroup (FreeGenerator.{u} d)) r)),
    ∀ i, b i = (H.commutator i).free_groupassoc_gradedclass

/--
Formal statement that the associated-graded images of the chosen weight-`r`
Hall basic commutators form a `ℤ`-basis.
-/
def BCWta.FormsAssocGradedbasis
    {d n r : ℕ}
    (H : BCWta.{u} d r) :
    Prop :=
  ∃ b : Module.Basis H.index ℤ
      (Additive
        (AssociatedGradedLayer
          (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n) r)),
    ∀ i, b i = (H.commutator i).associatedGradedClass (n := n)

/--
For `r < n`, passing from `F_d` to `F_d / γ_n(F_d)` does not change the
weight-`r` lower-central associated-graded layer.
-/
noncomputable def truncationAssociatedGraded
    (d n r : ℕ)
    (hrn : r < n) :
    AssociatedGradedLayer (FreeGroup (FreeGenerator.{u} d)) r ≃*
    AssociatedGradedLayer
        (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n) r := by
  let F : Type u := FreeGroup (FreeGenerator.{u} d)
  letI : Group F := by
    dsimp [F]
    infer_instance
  let N : Type u := LowerCentralTruncation F n
  letI : Group N := by
    dsimp [N, LowerCentralTruncation]
    infer_instance
  let q : F →* N := lowerCentralTruncation F n
  let φ :
      AssociatedGradedLayer F r →*
        AssociatedGradedLayer N r :=
    centralAssociatedGraded q r
  have hq : Function.Surjective q := QuotientGroup.mk'_surjective _
  have hqTerm :
      Function.Surjective (lowerSeriesRestriction q (r - 1)) := by
    intro x
    obtain ⟨y, hy, hyMap⟩ :=
      lower_series_surjective q hq x.property
    exact ⟨⟨y, hy⟩, Subtype.ext hyMap⟩
  have hφSurj : Function.Surjective φ := by
    intro x
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective _ x
    obtain ⟨z, rfl⟩ := hqTerm y
    exact
      ⟨QuotientGroup.mk'
        ((Subgroup.lowerCentralSeries F r).subgroupOf (Subgroup.lowerCentralSeries F (r - 1))) z,
        lower_graded_mk q r z⟩
  have hqKernelLeNext :
      (Subgroup.lowerCentralSeries F (n - 1)).subgroupOf (Subgroup.lowerCentralSeries F (r - 1)) ≤
        (Subgroup.lowerCentralSeries F r).subgroupOf (Subgroup.lowerCentralSeries F (r - 1)) := by
    intro x hx
    exact Subgroup.lowerCentralSeries_antitone (by omega : r ≤ n - 1) hx
  have hcomap :
      ((Subgroup.lowerCentralSeries N r).subgroupOf (Subgroup.lowerCentralSeries N (r - 1))).comap
          (lowerSeriesRestriction q (r - 1)) =
        (Subgroup.lowerCentralSeries F r).subgroupOf (Subgroup.lowerCentralSeries F (r - 1)) := by
    apply le_antisymm
    · intro x hx
      obtain ⟨y, hy, hyMap⟩ :=
        lower_series_surjective q hq
          (show q x ∈ Subgroup.lowerCentralSeries N r from hx)
      let yTerm : Subgroup.lowerCentralSeries F (r - 1) :=
        ⟨y, Subgroup.lowerCentralSeries_antitone (Nat.sub_le r 1) hy⟩
      have hxyKernel :
          x * yTerm⁻¹ ∈
            (Subgroup.lowerCentralSeries F (n - 1)).subgroupOf
              (Subgroup.lowerCentralSeries F (r - 1)) := by
        change (x : F) * y⁻¹ ∈ Subgroup.lowerCentralSeries F (n - 1)
        rw [← QuotientGroup.eq_one_iff]
        change q ((x : F) * y⁻¹) = 1
        rw [map_mul, ← hyMap]
        exact mul_inv_cancel _
      have hxyNext :
          x * yTerm⁻¹ ∈
            (Subgroup.lowerCentralSeries F r).subgroupOf (Subgroup.lowerCentralSeries F (r - 1)) :=
        hqKernelLeNext hxyKernel
      have hyNext :
          yTerm ∈
            (Subgroup.lowerCentralSeries F r).subgroupOf (Subgroup.lowerCentralSeries F (r - 1))
              := by
        exact hy
      have hxEq : x * yTerm⁻¹ * yTerm = x := by
        simp only [mul_assoc, inv_mul_cancel, mul_one]
      rw [← hxEq]
      exact
        ((Subgroup.lowerCentralSeries F r).subgroupOf (Subgroup.lowerCentralSeries F (r -
          1))).mul_mem
          hxyNext hyNext
    · intro x hx
      change q x ∈ Subgroup.lowerCentralSeries N r
      exact Subgroup.lowerCentralSeries.map q r
        (Subgroup.mem_map_of_mem q (show (x : F) ∈ Subgroup.lowerCentralSeries F r from hx))
  have hφInj : Function.Injective φ := by
    rw [← MonoidHom.ker_eq_bot_iff]
    dsimp [φ, centralAssociatedGraded]
    rw [QuotientGroup.ker_map, hcomap]
    exact QuotientGroup.map_mk'_self _
  exact MulEquiv.ofBijective φ ⟨hφInj, hφSurj⟩

/--
The underlying homomorphism of the quotient-layer equivalence is the induced
lower-central graded map.
-/
lemma associated_graded_monoid
    (d n r : ℕ)
    (hrn : r < n) :
    (truncationAssociatedGraded d n r hrn).toMonoidHom =
      centralAssociatedGraded
        (lowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n) r :=
  rfl

/--
Truncating after evaluating a free Hall word agrees with evaluating the same
word on the truncated free generators.
-/
lemma BCWt.mapevalinfree_groupeqevalin_frelowcentru
    {d n r : ℕ}
    (h : BCWt.{u} d r) :
    lowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n h.eval_in_freegroup =
      h.freeLowerTruncation (n := n) := by
  change
    lowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n
        (h.word.eval FreeGroup.of) =
      h.word.eval
        (fun i =>
          lowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n
            (FreeGroup.of i))
  exact CWord.map_eval _ _ _

/--
The quotient-layer equivalence carries each free-group Hall class to its class
in `F_d / γ_n(F_d)`.
-/
lemma truncation_associated_graded
    {d n r : ℕ}
    (hrn : r < n)
    (h : BCWt.{u} d r) :
    MulEquiv.toAdditive (truncationAssociatedGraded d n r hrn)
        h.free_groupassoc_gradedclass =
      h.associatedGradedClass (n := n) := by
  apply Additive.ofMul.injective
  change
    truncationAssociatedGraded d n r hrn
        (QuotientGroup.mk' _ ⟨h.eval_in_freegroup, h.evalin_freegroupmem_lowecentseri⟩) =
      QuotientGroup.mk' _
        ⟨h.freeLowerTruncation (n := n),
          h.free_truncation_series⟩
  change
    (truncationAssociatedGraded d n r hrn).toMonoidHom
        (QuotientGroup.mk' _ ⟨h.eval_in_freegroup, h.evalin_freegroupmem_lowecentseri⟩) =
      QuotientGroup.mk' _
        ⟨h.freeLowerTruncation (n := n),
          h.free_truncation_series⟩
  rw [associated_graded_monoid]
  rw [lower_graded_mk]
  congr 1
  exact Subtype.ext h.mapevalinfree_groupeqevalin_frelowcentru

/--
TeX Claim 1: for `1 ≤ r < n`, the Hall basic commutators of weight `r` give a
`ℤ`-basis of `γ_r(F_d / γ_n(F_d)) / γ_(r+1)(F_d / γ_n(F_d))`, once the classical
free-group basic-commutator basis theorem is supplied.
-/
theorem
    BCWta.formassograd_basisformsfree_groassgrabas
    {d n r : ℕ}
    (H : BCWta.{u} d r)
    (_hr : 1 ≤ r)
    (hrn : r < n)
    (hH : H.FormsfreeGroupassocGradedbasis) :
    H.FormsAssocGradedbasis (n := n) := by
  rcases hH with ⟨b, hb⟩
  let e :
      Additive
          (AssociatedGradedLayer (FreeGroup (FreeGenerator.{u} d)) r) ≃ₗ[ℤ]
        Additive
          (AssociatedGradedLayer
            (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n) r) :=
    (MulEquiv.toAdditive
      (truncationAssociatedGraded d n r hrn)).toIntLinearEquiv
  refine ⟨b.map e, ?_⟩
  intro i
  rw [Module.Basis.map_apply, hb]
  exact truncation_associated_graded hrn (H.commutator i)

/--
TeX Claim 2: interchanging elements from `γ_r` and `γ_s` only introduces a
correction in `γ_(r+s)`.  The correction is written on the right, matching the
TeX equation `ba = ab c`.
-/
lemma lower_series_interchange
    {G : Type u} [Group G]
    {r s : ℕ}
    (_hr : 1 ≤ r)
    (_hs : 1 ≤ s)
    {a b : G}
    (ha : a ∈ Subgroup.lowerCentralSeries G (r - 1))
    (hb : b ∈ Subgroup.lowerCentralSeries G (s - 1)) :
    ∃ c : G,
      c ∈ Subgroup.lowerCentralSeries G (r + s - 1) ∧
        b * a = a * b * c := by
  refine ⟨⁅b⁻¹, a⁻¹⁆, ?_, ?_⟩
  · have hc :
        ⁅b⁻¹, a⁻¹⁆ ∈ Subgroup.lowerCentralSeries G ((s - 1) + (r - 1) + 1) :=
      element_lower_series
        ((Subgroup.lowerCentralSeries G (s - 1)).inv_mem hb)
        ((Subgroup.lowerCentralSeries G (r - 1)).inv_mem ha)
    have hindex : (s - 1) + (r - 1) + 1 = r + s - 1 := by
      omega
    rw [hindex] at hc
    exact hc
  · simp [commutatorElement_def, mul_assoc]

/--
In particular, evaluated Hall basic commutators of weights `r` and `s` in the
free nilpotent truncation interchange with only a weight-`r+s` correction.
-/
lemma BCWt.interchangeeval_infreelower_centtrunexis
    {d n r s : ℕ}
    (_hr : 1 ≤ r)
    (_hs : 1 ≤ s)
    (a : BCWt.{u} d r)
    (b : BCWt.{u} d s) :
    ∃ c : LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n,
      c ∈ Subgroup.lowerCentralSeries
          (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n) (r + s - 1) ∧
        b.freeLowerTruncation (n := n) *
            a.freeLowerTruncation (n := n) =
          a.freeLowerTruncation (n := n) *
            b.freeLowerTruncation (n := n) * c :=
  lower_series_interchange
    _hr _hs
    a.free_truncation_series
    b.free_truncation_series

/--
The evaluated Hall commutator, regarded as an element of the lower-central
term for its ordinary weight.
-/
def BCWt.evalin_freelower_centtrunterm
    {d n r : ℕ}
    (h : BCWt.{u} d r) :
    Subgroup.lowerCentralSeries
      (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n) (r - 1) :=
  ⟨h.freeLowerTruncation (n := n),
    h.free_truncation_series⟩

/--
One collected Hall segment of fixed ordinary weight, ordered by the chosen Hall
order on that weight layer.
-/
def BCWta.collected_lower_centralterm
    {d n r : ℕ}
    (H : BCWta.{u} d r)
    (e : H.index → ℤ) :
    Subgroup.lowerCentralSeries
      (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n) (r - 1) :=
  ((Finset.univ.sort fun i j : H.index => i ≤ j).map fun i =>
    (H.commutator i).evalin_freelower_centtrunterm (n := n) ^ e i).prod

/--
The ambient-group value of one collected fixed-weight Hall segment.
-/
def BCWta.collectedWeightProduct
    {d n r : ℕ}
    (H : BCWta.{u} d r)
    (e : H.index → ℤ) :
    LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n :=
  H.collected_lower_centralterm (n := n) e

/--
Finite products in a commutative target can be read from the chosen ordered
list without changing their value.
-/
lemma sort_univ_fintype
    {G : Type u} [CommMonoid G]
    {ι : Type u} [Fintype ι] [LinearOrder ι]
    (f : ι → G) :
    ((Finset.univ.sort fun i j : ι => i ≤ j).map f).prod =
      ∏ i, f i := by
  rw [← List.prod_toFinset]
  · simp
  · exact Finset.sort_nodup _ _

set_option synthInstance.maxHeartbeats 100000 in
-- big synth
/--
The associated-graded class of one collected weight segment is the linear
combination of its Hall basis classes with the chosen integer exponents.
-/
lemma BCWta.collectedlower_centtermclas_eqmulsum
    {d n r : ℕ}
    (H : BCWta.{u} d r)
    (e : H.index → ℤ) :
    QuotientGroup.mk'
        ((Subgroup.lowerCentralSeries
          (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n) r).subgroupOf
            (Subgroup.lowerCentralSeries
              (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n) (r - 1)))
        (H.collected_lower_centralterm (n := n) e) =
      Additive.toMul
        (∑ i, e i • (H.commutator i).associatedGradedClass (n := n)) := by
  let N : Type u := LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n
  let A : Subgroup N := Subgroup.lowerCentralSeries N (r - 1)
  let B : Subgroup A := (Subgroup.lowerCentralSeries N r).subgroupOf A
  letI : IsMulCommutative (A ⧸ B) :=
    associated_graded_commutative r
  let q : A →* A ⧸ B := QuotientGroup.mk' B
  change
    q (H.collected_lower_centralterm (n := n) e) =
      Additive.toMul
        (∑ i, e i • (H.commutator i).associatedGradedClass (n := n))
  rw [BCWta.collected_lower_centralterm, map_list_prod,
    List.map_map, sort_univ_fintype]
  simp only [Function.comp_apply, map_zpow, toMul_sum, toMul_zsmul]
  apply Finset.prod_congr rfl
  intro i _hi
  congr 1

/--
Claim 1 lets one remove one collected weight-`r` Hall segment from any element
of `γ_r`, leaving a residual in `γ_(r+1)`.
-/
lemma BCWta.existscollected_weigprodinv_mulmemnext
    {d n r : ℕ}
    (H : BCWta.{u} d r)
    (hH : H.FormsAssocGradedbasis (n := n))
    {x : LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n}
    (hx :
      x ∈ Subgroup.lowerCentralSeries
        (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n) (r - 1)) :
    ∃ e : H.index → ℤ,
      (H.collectedWeightProduct (n := n) e)⁻¹ * x ∈
        Subgroup.lowerCentralSeries
          (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n) r := by
  let N : Type u := LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n
  let A : Subgroup N := Subgroup.lowerCentralSeries N (r - 1)
  let B : Subgroup A := (Subgroup.lowerCentralSeries N r).subgroupOf A
  let q : A →* A ⧸ B := QuotientGroup.mk' B
  let xTerm : A := ⟨x, hx⟩
  rcases hH with ⟨b, hb⟩
  let e : H.index → ℤ :=
    fun i => b.repr (Additive.ofMul (q xTerm)) i
  have hsum :
      ∑ i, e i • (H.commutator i).associatedGradedClass (n := n) =
        Additive.ofMul (q xTerm) := by
    rw [← b.sum_repr (Additive.ofMul (q xTerm))]
    simp [e, hb]
  have hclass :
      q (H.collected_lower_centralterm (n := n) e) =
        q xTerm := by
    rw [BCWta.collectedlower_centtermclas_eqmulsum]
    exact congrArg Additive.toMul hsum
  have hresidual :
      (H.collected_lower_centralterm (n := n) e)⁻¹ * xTerm ∈ B := by
    apply (QuotientGroup.eq_one_iff
      (N := B)
      ((H.collected_lower_centralterm (n := n) e)⁻¹ * xTerm)).mp
    change q ((H.collected_lower_centralterm (n := n) e)⁻¹ * xTerm) = 1
    rw [map_mul, map_inv, hclass, inv_mul_cancel]
  refine ⟨e, ?_⟩
  exact hresidual

/--
Integer Hall coordinates for one chosen Hall family in every ordinary weight.
-/
abbrev HEFam
    {d : ℕ}
    (H : ∀ r : ℕ, BCWta.{u} d r) :
    Type u :=
  ∀ r : ℕ, (H r).index → ℤ

/--
The collected Hall prefix through ordinary weight `k`, with weights ordered
increasingly and each fixed-weight segment ordered by its Hall order.
-/
def collectedPrefixProduct
    {d n : ℕ}
    (H : ∀ r : ℕ, BCWta.{u} d r)
    (e : HEFam H)
    (k : ℕ) :
    LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n :=
  ((List.range k).map fun j =>
    (H (j + 1)).collectedWeightProduct (n := n) (e (j + 1))).prod

/--
The full collected Hall product of all ordinary weights `< n`.
-/
def collectedHallProduct
    {d n : ℕ}
    (H : ∀ r : ℕ, BCWta.{u} d r)
    (e : HEFam H) :
    LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n :=
  collectedPrefixProduct (n := n) H e (n - 1)

/--
Appending the next ordinary weight extends a collected Hall prefix on the
right by exactly that fixed-weight Hall segment.
-/
lemma collected_prefix_succ
    {d n : ℕ}
    (H : ∀ r : ℕ, BCWta.{u} d r)
    (e : HEFam H)
    (k : ℕ) :
    collectedPrefixProduct (n := n) H e (k + 1) =
      collectedPrefixProduct (n := n) H e k *
        (H (k + 1)).collectedWeightProduct (n := n) (e (k + 1)) := by
  simp [collectedPrefixProduct, List.range_succ, List.map_append,
    List.prod_append]

/--
Updating the coordinates at the next weight does not change an already
collected lower-weight prefix.
-/
lemma collected_update_next
    {d n : ℕ}
    (H : ∀ r : ℕ, BCWta.{u} d r)
    (e : HEFam H)
    (k : ℕ)
    (ek : (H (k + 1)).index → ℤ) :
    collectedPrefixProduct (n := n) H (Function.update e (k + 1) ek) k =
      collectedPrefixProduct (n := n) H e k := by
  unfold collectedPrefixProduct
  congr 1
  apply List.map_congr_left
  intro j hj
  have hjlt : j < k := List.mem_range.mp hj
  have hne : j + 1 ≠ k + 1 := by omega
  rw [Function.update_of_ne hne]

/--
After collecting through ordinary weight `k`, every element has a residual in
the next lower-central term.
-/
lemma collected_prefix_series
    {d n : ℕ}
    (H : ∀ r : ℕ, BCWta.{u} d r)
    (hH :
      ∀ r : ℕ,
        1 ≤ r →
          r < n →
            (H r).FormsAssocGradedbasis (n := n))
    (k : ℕ)
    (hk : k ≤ n - 1)
    (y : LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n) :
    ∃ e : HEFam H,
      ∃ z : LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n,
        z ∈ Subgroup.lowerCentralSeries
            (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n) k ∧
          collectedPrefixProduct (n := n) H e k * z = y := by
  induction k with
  | zero =>
      refine ⟨fun _ _ => 0, y, by simp, ?_⟩
      simp [collectedPrefixProduct]
  | succ k ih =>
      obtain ⟨e, z, hz, hprod⟩ := ih (by omega)
      obtain ⟨ek, hresidual⟩ :=
        (H (k + 1)).existscollected_weigprodinv_mulmemnext
          (hH (k + 1) (by omega) (by omega))
          hz
      let e' : HEFam H := Function.update e (k + 1) ek
      let segment :
          LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n :=
        (H (k + 1)).collectedWeightProduct (n := n) ek
      let residual :
          LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n :=
        segment⁻¹ * z
      refine ⟨e', residual, ?_, ?_⟩
      · simpa [residual, segment] using hresidual
      · have hprefix :
            collectedPrefixProduct (n := n) H e' k =
              collectedPrefixProduct (n := n) H e k := by
          simpa [e'] using collected_update_next (n := n) H e k ek
        have hsegment :
            (H (k + 1)).collectedWeightProduct (n := n) (e' (k + 1)) =
              segment := by
          simp [e', segment]
        rw [collected_prefix_succ, hprefix, hsegment]
        calc
          collectedPrefixProduct (n := n) H e k * segment * residual =
              collectedPrefixProduct (n := n) H e k * z := by
                simp [residual, mul_assoc]
          _ = y := hprod

/--
TeX Claim 3: once Claim 1 supplies Hall bases in every layer below `n`, every
element of `F_d / γ_n(F_d)` has a collected Hall product with integer
coordinates, ordered by increasing ordinary weight.
-/
theorem collected_hall_product
    {d n : ℕ}
    (_hn : 2 ≤ n)
    (H : ∀ r : ℕ, BCWta.{u} d r)
    (hH :
      ∀ r : ℕ,
        1 ≤ r →
          r < n →
            (H r).FormsAssocGradedbasis (n := n))
    (y : LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n) :
    ∃ e : HEFam H,
      collectedHallProduct (n := n) H e = y := by
  obtain ⟨e, z, hz, hprod⟩ :=
    collected_prefix_series
      (n := n) H hH (n - 1) (by omega) y
  have hbot :
      Subgroup.lowerCentralSeries
          (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n) (n - 1) =
        ⊥ := by
    simpa [LowerCentralTruncation] using
      (lower_last_bot
        (G := FreeGroup (FreeGenerator.{u} d)) (c := n))
  have hzOne : z = 1 := eq_bot_iff.mp hbot hz
  refine ⟨e, ?_⟩
  simpa [collectedHallProduct, hzOne] using hprod

/--
Every collected fixed-weight Hall segment lies in the lower-central term
dictated by its ordinary weight.
-/
lemma BCWta.collectedweight_productmem_lowecentseri
    {d n r : ℕ}
    (H : BCWta.{u} d r)
    (e : H.index → ℤ) :
    H.collectedWeightProduct (n := n) e ∈
      Subgroup.lowerCentralSeries
        (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n) (r - 1) :=
  (H.collected_lower_centralterm (n := n) e).property

/--
The collected fixed-weight Hall segment with every exponent zero is trivial.
-/
lemma BCWta.collected_weight_productzero
    {d n r : ℕ}
    (H : BCWta.{u} d r) :
    H.collectedWeightProduct (n := n) (0 : H.index → ℤ) = 1 := by
  simp [BCWta.collectedWeightProduct,
    BCWta.collected_lower_centralterm, zpow_zero]

/--
If two collected fixed-weight Hall segments agree modulo the next
lower-central term, Claim 1's basis coordinates agree exactly.
-/
lemma BCWta.collweigprod_coordseqinv_mulmemnext
    {d n r : ℕ}
    (H : BCWta.{u} d r)
    (hH : H.FormsAssocGradedbasis (n := n))
    (e f : H.index → ℤ)
    (hsegment :
      (H.collectedWeightProduct (n := n) f)⁻¹ *
          H.collectedWeightProduct (n := n) e ∈
        Subgroup.lowerCentralSeries
          (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n) r) :
    e = f := by
  let N : Type u := LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n
  let A : Subgroup N := Subgroup.lowerCentralSeries N (r - 1)
  let B : Subgroup A := (Subgroup.lowerCentralSeries N r).subgroupOf A
  let q : A →* A ⧸ B := QuotientGroup.mk' B
  let eTerm : A := H.collected_lower_centralterm (n := n) e
  let fTerm : A := H.collected_lower_centralterm (n := n) f
  have hsegmentTerm : fTerm⁻¹ * eTerm ∈ B := by
    exact hsegment
  have hclass : q eTerm = q fTerm := by
    have hqOne :
        q (fTerm⁻¹ * eTerm) = 1 :=
      (QuotientGroup.eq_one_iff (N := B) (fTerm⁻¹ * eTerm)).2 hsegmentTerm
    rw [map_mul, map_inv] at hqOne
    exact (inv_mul_eq_one.mp hqOne).symm
  have hsum :
      ∑ i, e i • (H.commutator i).associatedGradedClass (n := n) =
        ∑ i, f i • (H.commutator i).associatedGradedClass (n := n) := by
    apply Additive.toMul.injective
    rw [← H.collectedlower_centtermclas_eqmulsum (n := n) e,
      ← H.collectedlower_centtermclas_eqmulsum (n := n) f]
    exact hclass
  rcases hH with ⟨b, hb⟩
  have hsumBasis : ∑ i, e i • b i = ∑ i, f i • b i := by
    simpa only [hb] using hsum
  have hzero : ∑ i, (e i - f i) • b i = 0 := by
    calc
      ∑ i, (e i - f i) • b i = ∑ i, (e i • b i - f i • b i) := by
        congr 1
        simp only [sub_eq_add_neg, add_zsmul, neg_zsmul]
      _ = ∑ i, e i • b i - ∑ i, f i • b i := by
        simpa only using
          (Finset.sum_sub_distrib (s := Finset.univ)
            (fun i => e i • b i) (fun i => f i • b i))
      _ = 0 := sub_eq_zero.mpr hsumBasis
  have hcoeff :
      ∀ i, e i - f i = 0 :=
    Fintype.linearIndependent_iff.mp b.linearIndependent (fun i => e i - f i) hzero
  funext i
  exact sub_eq_zero.mp (hcoeff i)

/--
The collected Hall tail after the first `k` ordinary weights.
-/
def collectedTailProduct
    {d n : ℕ}
    (H : ∀ r : ℕ, BCWta.{u} d r)
    (e : HEFam H)
    (k : ℕ) :
    LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n :=
  ((List.range' k (n - 1 - k)).map fun j =>
    (H (j + 1)).collectedWeightProduct (n := n) (e (j + 1))).prod

/--
The collected Hall prefix and complementary tail multiply back to the full
collected Hall product.
-/
lemma collected_prefix_tail
    {d n : ℕ}
    (H : ∀ r : ℕ, BCWta.{u} d r)
    (e : HEFam H)
    (k : ℕ)
    (hk : k ≤ n - 1) :
    collectedPrefixProduct (n := n) H e k *
        collectedTailProduct (n := n) H e k =
      collectedHallProduct (n := n) H e := by
  have hrange :
      List.range k ++ List.range' k (n - 1 - k) = List.range (n - 1) := by
    rw [List.range_eq_range', List.range_eq_range']
    simpa [Nat.add_sub_of_le hk] using
      (List.range'_append (s := 0) (m := k) (n := n - 1 - k) (step := 1))
  unfold collectedHallProduct collectedPrefixProduct collectedTailProduct
  rw [← List.prod_append, ← List.map_append, hrange]

/--
Every Hall tail after the first `k` ordinary weights lies in `γ_(k+1)`.
-/
lemma collected_tail_series
    {d n : ℕ}
    (H : ∀ r : ℕ, BCWta.{u} d r)
    (e : HEFam H)
    (k : ℕ) :
    collectedTailProduct (n := n) H e k ∈
      Subgroup.lowerCentralSeries
        (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n) k := by
  unfold collectedTailProduct
  apply Subgroup.list_prod_mem
  intro x hx
  rw [List.mem_map] at hx
  rcases hx with ⟨j, hj, rfl⟩
  exact Subgroup.lowerCentralSeries_antitone (List.left_le_of_mem_range' hj)
    ((H (j + 1)).collectedweight_productmem_lowecentseri (n := n) (e (j + 1)))

/--
Equal Hall coordinates through ordinary weight `k` give equal collected
prefixes through weight `k`.
-/
lemma collected_product_coordinates
    {d n : ℕ}
    (H : ∀ r : ℕ, BCWta.{u} d r)
    (e f : HEFam H)
    (k : ℕ)
    (hcoordinates :
      ∀ r : ℕ,
        1 ≤ r →
          r ≤ k →
            e r = f r) :
    collectedPrefixProduct (n := n) H e k =
      collectedPrefixProduct (n := n) H f k := by
  induction k with
  | zero =>
      simp [collectedPrefixProduct]
  | succ k ih =>
      rw [collected_prefix_succ, collected_prefix_succ,
        ih (fun r hr hrk => hcoordinates r hr (by omega)),
        hcoordinates (k + 1) (by omega) le_rfl]

/--
If all Hall coordinates through ordinary weight `k` vanish, the collected
prefix through weight `k` is trivial.
-/
lemma collected_prefix_coordinates
    {d n : ℕ}
    (H : ∀ r : ℕ, BCWta.{u} d r)
    (e : HEFam H)
    (k : ℕ)
    (hcoordinates :
      ∀ r : ℕ,
        1 ≤ r →
          r ≤ k →
            e r = 0) :
    collectedPrefixProduct (n := n) H e k = 1 := by
  induction k with
  | zero =>
      simp [collectedPrefixProduct]
  | succ k ih =>
      rw [collected_prefix_succ,
        ih (fun r hr hrk => hcoordinates r hr (by omega)),
        hcoordinates (k + 1) (by omega) le_rfl,
        BCWta.collected_weight_productzero, one_mul]

/--
TeX Claim 4, relation form: a collected Hall product equal to `1` has every
Hall coordinate of ordinary weight `< n` equal to zero.
-/
theorem collected_imp_coordinates
    {d n : ℕ}
    (_hn : 2 ≤ n)
    (H : ∀ r : ℕ, BCWta.{u} d r)
    (hH :
      ∀ r : ℕ,
        1 ≤ r →
          r < n →
            (H r).FormsAssocGradedbasis (n := n))
    (e : HEFam H)
    (hproduct : collectedHallProduct (n := n) H e = 1) :
    ∀ r : ℕ,
      1 ≤ r →
        r < n →
          e r = 0 := by
  have hzeroThrough :
      ∀ k : ℕ,
        k ≤ n - 1 →
          ∀ r : ℕ,
            1 ≤ r →
              r ≤ k →
                e r = 0 := by
    intro k hk
    induction k with
    | zero =>
        intro r hr hrk
        omega
    | succ k ih =>
        intro r hr hrk
        by_cases hrCurrent : r = k + 1
        · subst r
          have hprevious :
              ∀ s : ℕ,
                1 ≤ s →
                  s ≤ k →
                    e s = 0 :=
            ih (by omega)
          have hprefix :
              collectedPrefixProduct (n := n) H e k = 1 :=
            collected_prefix_coordinates H e k hprevious
          let segment :
              LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n :=
            (H (k + 1)).collectedWeightProduct (n := n) (e (k + 1))
          let tail :
              LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n :=
            collectedTailProduct (n := n) H e (k + 1)
          have hsegmentTail : segment * tail = 1 := by
            calc
              segment * tail =
                  collectedPrefixProduct (n := n) H e (k + 1) * tail := by
                    rw [collected_prefix_succ, hprefix, one_mul]
              _ = collectedHallProduct (n := n) H e :=
                collected_prefix_tail
                  H e (k + 1) (by omega)
              _ = 1 := hproduct
          have htail :
              tail ∈ Subgroup.lowerCentralSeries
                (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n) (k + 1) :=
            collected_tail_series H e (k + 1)
          have hsegmentNext :
              segment ∈ Subgroup.lowerCentralSeries
                (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n) (k + 1) := by
            have hsegmentEq : segment = tail⁻¹ := by
              calc
                segment = segment * tail * tail⁻¹ := by simp [mul_assoc]
                _ = tail⁻¹ := by rw [hsegmentTail, one_mul]
            rw [hsegmentEq]
            exact (Subgroup.lowerCentralSeries
              (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n) (k + 1)).inv_mem
              htail
          have hsegmentInvMul :
              ((H (k + 1)).collectedWeightProduct (n := n) 0)⁻¹ *
                  (H (k + 1)).collectedWeightProduct (n := n) (e (k + 1)) ∈
                Subgroup.lowerCentralSeries
                  (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n) (k + 1) := by
            rw [BCWta.collected_weight_productzero]
            simpa [segment] using hsegmentNext
          exact (H (k + 1)).collweigprod_coordseqinv_mulmemnext
            (hH (k + 1) (by omega) (by omega))
            (e (k + 1))
            0
            hsegmentInvMul
        · exact ih (by omega) r hr (by omega)
  intro r hr hrn
  exact hzeroThrough r (by omega) r hr le_rfl

/--
TeX Claim 4, uniqueness form: two collected Hall products for the same element
have the same Hall coordinates in every ordinary weight `< n`.
-/
theorem collected_hall_coordinates
    {d n : ℕ}
    (_hn : 2 ≤ n)
    (H : ∀ r : ℕ, BCWta.{u} d r)
    (hH :
      ∀ r : ℕ,
        1 ≤ r →
          r < n →
            (H r).FormsAssocGradedbasis (n := n))
    (e f : HEFam H)
    (hproduct :
      collectedHallProduct (n := n) H e =
        collectedHallProduct (n := n) H f) :
    ∀ r : ℕ,
      1 ≤ r →
        r < n →
          e r = f r := by
  have hcoordinatesThrough :
      ∀ k : ℕ,
        k ≤ n - 1 →
          ∀ r : ℕ,
            1 ≤ r →
              r ≤ k →
                e r = f r := by
    intro k hk
    induction k with
    | zero =>
        intro r hr hrk
        omega
    | succ k ih =>
        intro r hr hrk
        by_cases hrCurrent : r = k + 1
        · subst r
          have hprevious :
              ∀ s : ℕ,
                1 ≤ s →
                  s ≤ k →
                    e s = f s :=
            ih (by omega)
          have hprefix :
              collectedPrefixProduct (n := n) H e k =
                collectedPrefixProduct (n := n) H f k :=
            collected_product_coordinates H e f k hprevious
          let eSegment :
              LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n :=
            (H (k + 1)).collectedWeightProduct (n := n) (e (k + 1))
          let fSegment :
              LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n :=
            (H (k + 1)).collectedWeightProduct (n := n) (f (k + 1))
          let eTail :
              LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n :=
            collectedTailProduct (n := n) H e (k + 1)
          let fTail :
              LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n :=
            collectedTailProduct (n := n) H f (k + 1)
          have hsegmentTail : eSegment * eTail = fSegment * fTail := by
            calc
              eSegment * eTail =
                  (collectedPrefixProduct (n := n) H e k)⁻¹ *
                    (collectedPrefixProduct (n := n) H e (k + 1) * eTail) := by
                      rw [collected_prefix_succ]
                      simp [eSegment, mul_assoc]
              _ = (collectedPrefixProduct (n := n) H e k)⁻¹ *
                    collectedHallProduct (n := n) H e := by
                      rw [collected_prefix_tail
                        H e (k + 1) (by omega)]
              _ = (collectedPrefixProduct (n := n) H f k)⁻¹ *
                    collectedHallProduct (n := n) H f := by
                      rw [hprefix, hproduct]
              _ = fSegment * fTail := by
                    rw [← collected_prefix_tail
                      H f (k + 1) (by omega), collected_prefix_succ]
                    simp [fSegment, fTail, mul_assoc]
          have htailE :
              eTail ∈ Subgroup.lowerCentralSeries
                (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n) (k + 1) :=
            collected_tail_series H e (k + 1)
          have htailF :
              fTail ∈ Subgroup.lowerCentralSeries
                (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n) (k + 1) :=
            collected_tail_series H f (k + 1)
          have hsegmentInvMul :
              fSegment⁻¹ * eSegment ∈ Subgroup.lowerCentralSeries
                (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n) (k + 1) := by
            have hsegmentEq : fSegment⁻¹ * eSegment = fTail * eTail⁻¹ := by
              calc
                fSegment⁻¹ * eSegment =
                    fSegment⁻¹ * (eSegment * eTail) * eTail⁻¹ := by simp [mul_assoc]
                _ = fSegment⁻¹ * (fSegment * fTail) * eTail⁻¹ := by rw [hsegmentTail]
                _ = fTail * eTail⁻¹ := by simp
            rw [hsegmentEq]
            exact (Subgroup.lowerCentralSeries
              (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n) (k + 1)).mul_mem
              htailF
              ((Subgroup.lowerCentralSeries
                (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n) (k + 1)).inv_mem
                htailE)
          exact (H (k + 1)).collweigprod_coordseqinv_mulmemnext
            (hH (k + 1) (by omega) (by omega))
            (e (k + 1))
            (f (k + 1))
            hsegmentInvMul
        · exact ih (by omega) r hr (by omega)
  intro r hr hrn
  exact hcoordinatesThrough r (by omega) r hr le_rfl

/--
An integer-valued polynomial on natural inputs, recorded by a rational
polynomial whose evaluated values are the given integers.
-/
def IVMost
    (f : ℕ → ℤ)
    (degreeBound : ℕ) :
    Prop :=
  ∃ P : Polynomial ℚ,
    P.natDegree ≤ degreeBound ∧
      ∀ q : ℕ, P.eval (q : ℚ) = (f q : ℚ)

/--
Choose the Hall coordinates of one element from Claim 3.  Claim 4 proves that
the coordinates below weight `n` do not depend on this choice.
-/
noncomputable def normalFormCoordinates
    {d n : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ r : ℕ, BCWta.{u} d r)
    (hH :
      ∀ r : ℕ,
        1 ≤ r →
          r < n →
            (H r).FormsAssocGradedbasis (n := n))
    (y : LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n) :
    HEFam H :=
  Classical.choose (collected_hall_product hn H hH y)

/--
The chosen Hall coordinates collect back to the original element.
-/
lemma collected_form_coordinates
    {d n : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ r : ℕ, BCWta.{u} d r)
    (hH :
      ∀ r : ℕ,
        1 ≤ r →
          r < n →
            (H r).FormsAssocGradedbasis (n := n))
    (y : LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n) :
    collectedHallProduct (n := n) H (normalFormCoordinates hn H hH y) = y :=
  Classical.choose_spec (collected_hall_product hn H hH y)

/--
The integer Hall coordinate of `y` at the chosen weight-`s` Hall commutator.
-/
noncomputable def hallCoordinate
    {d n s : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ r : ℕ, BCWta.{u} d r)
    (hH :
      ∀ r : ℕ,
        1 ≤ r →
          r < n →
            (H r).FormsAssocGradedbasis (n := n))
    (y : LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
    (i : (H s).index) :
    ℤ :=
  normalFormCoordinates hn H hH y s i

/--
Any collected Hall coordinates for `y` agree with the chosen coordinates in
ordinary weights below the truncation class.
-/
lemma form_coordinates_collected
    {d n : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ r : ℕ, BCWta.{u} d r)
    (hH :
      ∀ r : ℕ,
        1 ≤ r →
          r < n →
            (H r).FormsAssocGradedbasis (n := n))
    (e : HEFam H)
    (y : LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
    (hproduct : collectedHallProduct (n := n) H e = y) :
    ∀ r : ℕ,
      1 ≤ r →
        r < n →
          normalFormCoordinates hn H hH y r = e r :=
  collected_hall_coordinates
    hn H hH
    (normalFormCoordinates hn H hH y)
    e
    ((collected_form_coordinates hn H hH y).trans hproduct.symm)

/--
If a collected Hall product lies in `γ_r`, then its Hall coordinates of
ordinary weights strictly below `r` vanish.
-/
lemma imp_coordinates_below
    {d n r : ℕ}
    (_hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    (e : HEFam H)
    (hproduct :
      collectedHallProduct (n := n) H e ∈
        Subgroup.lowerCentralSeries
          (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n) (r - 1)) :
    ∀ s : ℕ,
      1 ≤ s →
        s < r →
          s < n →
            e s = 0 := by
  have hzeroThrough :
      ∀ k : ℕ,
        k < r →
          k ≤ n - 1 →
            ∀ s : ℕ,
              1 ≤ s →
                s ≤ k →
                  e s = 0 := by
    intro k hkr hkn
    induction k with
    | zero =>
        intro s hs hsk
        omega
    | succ k ih =>
        intro s hs hsk
        by_cases hsCurrent : s = k + 1
        · subst s
          have hprevious :
              ∀ t : ℕ,
                1 ≤ t →
                  t ≤ k →
                    e t = 0 :=
            ih (by omega) (by omega)
          have hprefix :
              collectedPrefixProduct (n := n) H e k = 1 :=
            collected_prefix_coordinates H e k hprevious
          let segment :
              LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n :=
            (H (k + 1)).collectedWeightProduct (n := n) (e (k + 1))
          let tail :
              LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n :=
            collectedTailProduct (n := n) H e (k + 1)
          have hsegmentTail :
              segment * tail = collectedHallProduct (n := n) H e := by
            calc
              segment * tail =
                  collectedPrefixProduct (n := n) H e (k + 1) * tail := by
                    rw [collected_prefix_succ, hprefix, one_mul]
              _ = collectedHallProduct (n := n) H e :=
                collected_prefix_tail
                  H e (k + 1) (by omega)
          have htail :
              tail ∈ Subgroup.lowerCentralSeries
                (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n) (k + 1) :=
            collected_tail_series H e (k + 1)
          have hproductNext :
              collectedHallProduct (n := n) H e ∈
                Subgroup.lowerCentralSeries
                  (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n) (k + 1) :=
            Subgroup.lowerCentralSeries_antitone (by omega : k + 1 ≤ r - 1) hproduct
          have hsegmentNext :
              segment ∈ Subgroup.lowerCentralSeries
                (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n) (k + 1) := by
            have hsegmentEq :
                segment = collectedHallProduct (n := n) H e * tail⁻¹ := by
              calc
                segment = segment * tail * tail⁻¹ := by simp [mul_assoc]
                _ = collectedHallProduct (n := n) H e * tail⁻¹ := by rw [hsegmentTail]
            rw [hsegmentEq]
            exact (Subgroup.lowerCentralSeries
              (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n) (k + 1)).mul_mem
              hproductNext
              ((Subgroup.lowerCentralSeries
                (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n) (k + 1)).inv_mem
                htail)
          have hsegmentInvMul :
              ((H (k + 1)).collectedWeightProduct (n := n) 0)⁻¹ *
                  (H (k + 1)).collectedWeightProduct (n := n) (e (k + 1)) ∈
                Subgroup.lowerCentralSeries
                  (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n) (k + 1) := by
            rw [BCWta.collected_weight_productzero]
            simpa [segment] using hsegmentNext
          exact (H (k + 1)).collweigprod_coordseqinv_mulmemnext
            (hH (k + 1) (by omega) (by omega))
            (e (k + 1))
            0
            hsegmentInvMul
        · exact ih (by omega) (by omega) s hs (by omega)
  intro s hs hsr hsn
  exact hzeroThrough s hsr (by omega) s hs le_rfl

/--
The universal collection-polynomial input for powers of one collected Hall
normal form whose nonzero ordinary weights begin at `r`.
-/
def CollectedPolynomialData
    {d n : ℕ}
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (e : HEFam H)
    (r : ℕ) :
    Prop :=
  (∀ s : ℕ, 1 ≤ s → s < r → s < n → e s = 0) →
    ∃ E : ℕ → HEFam H,
      (∀ q : ℕ,
        collectedHallProduct (n := n) H (E q) =
          collectedHallProduct (n := n) H e ^ q) ∧
        ∀ s : ℕ,
          1 ≤ s →
            s < n →
              ∀ i : (H s).index,
                IVMost
                  (fun q : ℕ => E q s i)
                  (s / r)

/--
TeX Claim 5: once universal collection polynomials are supplied for repeated
collected products, the Hall coordinate of `u^q` at ordinary weight `s < n`
is an integer-valued polynomial in `q` of degree at most `⌊s / r⌋` whenever
`u ∈ γ_r`.
-/
theorem integer_valued_most
    {d n r s : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ t : ℕ, BCWta.{u} d t)
    (hH :
      ∀ t : ℕ,
        1 ≤ t →
          t < n →
            (H t).FormsAssocGradedbasis (n := n))
    (hpower :
      ∀ (e : HEFam H) (t : ℕ),
        1 ≤ t →
          CollectedPolynomialData (n := n) H e t)
    (u : LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
    (hu :
      u ∈ Subgroup.lowerCentralSeries
        (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n) (r - 1))
    (hr : 1 ≤ r)
    (hs : 1 ≤ s)
    (hsn : s < n)
    (i : (H s).index) :
    IVMost
      (fun q : ℕ => hallCoordinate hn H hH (u ^ q) i)
      (s / r) := by
  let e : HEFam H := normalFormCoordinates hn H hH u
  have heProduct : collectedHallProduct (n := n) H e = u :=
    collected_form_coordinates hn H hH u
  have heMem :
      collectedHallProduct (n := n) H e ∈
        Subgroup.lowerCentralSeries
          (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n) (r - 1) := by
    rw [heProduct]
    exact hu
  have heBelow :
      ∀ t : ℕ,
        1 ≤ t →
          t < r →
            t < n →
              e t = 0 :=
    imp_coordinates_below
      hn H hH e heMem
  obtain ⟨E, hEproduct, hEpolynomial⟩ := hpower e r hr heBelow
  rcases hEpolynomial s hs hsn i with ⟨P, hPdegree, hPeval⟩
  refine ⟨P, hPdegree, ?_⟩
  intro q
  have hEqProduct : collectedHallProduct (n := n) H (E q) = u ^ q := by
    rw [hEproduct q, heProduct]
  have hcoordinates :
      normalFormCoordinates hn H hH (u ^ q) s = E q s :=
    form_coordinates_collected
      hn H hH (E q) (u ^ q) hEqProduct s hs hsn
  simpa [hallCoordinate, hcoordinates] using hPeval q

/--
The rational polynomial whose natural values are ordinary binomial
coefficients.
-/
noncomputable def natChoosePolynomial
    (k : ℕ) :
    Polynomial ℚ :=
  (k.factorial : ℚ)⁻¹ • (descPochhammer ℤ k).map (Int.castRingHom ℚ)

lemma int_cast_smul :
    Int.castRingHom ℚ = RingHom.smulOneHom := by
  ext z
  simp

lemma eval_nat_choose
    (q k : ℕ) :
    (natChoosePolynomial k).eval (q : ℚ) = (Nat.choose q k : ℚ) := by
  rw [natChoosePolynomial, Polynomial.eval_smul, Polynomial.eval_map,
    int_cast_smul, Polynomial.eval₂_smulOneHom_eq_smeval]
  rw [← Ring.choose_eq_smul]
  exact Ring.choose_natCast q k

/-- The same binomial polynomial evaluates generalized binomial coefficients
on signed integer inputs. -/
lemma collection_choose_int
    (z : ℤ)
    (k : ℕ) :
    (natChoosePolynomial k).eval (z : ℚ) =
      ((Ring.choose z k : ℤ) : ℚ) := by
  rw [natChoosePolynomial, Polynomial.eval_smul, Polynomial.eval_map,
    int_cast_smul, Polynomial.eval₂_smulOneHom_eq_smeval]
  rw [← Ring.choose_eq_smul]
  exact (Ring.map_choose (Int.castRingHom ℚ) z k).symm

lemma degree_choose_polynomial
    (k : ℕ) :
    (natChoosePolynomial k).natDegree ≤ k := by
  exact (Polynomial.natDegree_smul_le _ _).trans
    (Polynomial.natDegree_map_le.trans_eq (descPochhammer_natDegree ℤ k))

/--
The Newton coefficient selected by the first `k + 1` natural values.
-/
def natBinomialCoefficient
    (f : ℕ → ℤ) :
    ℕ → ℤ
  | 0 => f 0
  | k + 1 =>
      f (k + 1) -
        ∑ i : Fin (k + 1),
          natBinomialCoefficient f i * (Nat.choose (k + 1) i : ℤ)
termination_by k => k
decreasing_by
  omega

lemma binomial_coefficient_range
    (f : ℕ → ℤ)
    (q : ℕ) :
    ∑ k ∈ Finset.range (q + 1),
        natBinomialCoefficient f k * (Nat.choose q k : ℤ) =
      f q := by
  cases q with
  | zero =>
      simp [natBinomialCoefficient]
  | succ q =>
      rw [Finset.sum_range_succ, natBinomialCoefficient]
      have hfin :
          ∑ i : Fin (q + 1),
              natBinomialCoefficient f i * (Nat.choose (q + 1) i : ℤ) =
            ∑ i ∈ Finset.range (q + 1),
              natBinomialCoefficient f i * (Nat.choose (q + 1) i : ℤ) :=
        Fin.sum_univ_eq_sum_range
          (fun i : ℕ =>
            natBinomialCoefficient f i * (Nat.choose (q + 1) i : ℤ))
          (q + 1)
      rw [hfin]
      simp [Nat.choose_self]

lemma nat_binomial_range
    (f : ℕ → ℤ)
    {q m : ℕ}
    (hqm : q ≤ m) :
    ∑ k ∈ Finset.range (m + 1),
        natBinomialCoefficient f k * (Nat.choose q k : ℤ) =
      f q := by
  have htail :
      ∑ k ∈ Finset.Ico (q + 1) (m + 1),
          natBinomialCoefficient f k * (Nat.choose q k : ℤ) = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    have hqk : q < k := by
      exact (Finset.mem_Ico.mp hk).1
    simp [Nat.choose_eq_zero_of_lt hqk]
  calc
    ∑ k ∈ Finset.range (m + 1),
        natBinomialCoefficient f k * (Nat.choose q k : ℤ) =
        (∑ k ∈ Finset.range (q + 1),
          natBinomialCoefficient f k * (Nat.choose q k : ℤ)) +
          ∑ k ∈ Finset.Ico (q + 1) (m + 1),
            natBinomialCoefficient f k * (Nat.choose q k : ℤ) :=
      (Finset.sum_range_add_sum_Ico _ (Nat.succ_le_succ hqm)).symm
    _ = ∑ k ∈ Finset.range (q + 1),
          natBinomialCoefficient f k * (Nat.choose q k : ℤ) := by
            rw [htail, add_zero]
    _ = f q := binomial_coefficient_range f q

noncomputable def natBinomialExpansion
    (f : ℕ → ℤ)
    (m : ℕ) :
    Polynomial ℚ :=
  ∑ k ∈ Finset.range (m + 1),
    Polynomial.C (natBinomialCoefficient f k : ℚ) * natChoosePolynomial k

lemma nat_binomial_expansion
    (f : ℕ → ℤ)
    (m : ℕ) :
    (natBinomialExpansion f m).natDegree ≤ m := by
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro k hk
  have hkm : k ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  calc
    (Polynomial.C (natBinomialCoefficient f k : ℚ) * natChoosePolynomial k).natDegree ≤
        (Polynomial.C (natBinomialCoefficient f k : ℚ)).natDegree +
          (natChoosePolynomial k).natDegree :=
      Polynomial.natDegree_mul_le
    _ ≤ 0 + k := by
      gcongr
      · simp
      · exact degree_choose_polynomial k
    _ ≤ m := by simpa using hkm

lemma binomial_expansion_polynomial
    (f : ℕ → ℤ)
    (m q : ℕ) :
    (natBinomialExpansion f m).eval (q : ℚ) =
      ((∑ k ∈ Finset.range (m + 1),
        natBinomialCoefficient f k * (Nat.choose q k : ℤ)) : ℤ) := by
  rw [natBinomialExpansion, Polynomial.eval_finsetSum]
  simp_rw [Polynomial.eval_C_mul, eval_nat_choose]
  norm_cast

lemma IVMost.nat_binomial_basisexpansion
    {f : ℕ → ℤ}
    {m : ℕ}
    (hP : IVMost f m) :
    ∀ q : ℕ,
      f q =
        ∑ k ∈ Finset.range (m + 1),
          natBinomialCoefficient f k * (Nat.choose q k : ℤ) := by
  rcases hP with ⟨P, hPdegree, hPeval⟩
  let Q : Polynomial ℚ := natBinomialExpansion f m
  have hQdegree : Q.natDegree ≤ m :=
    nat_binomial_expansion f m
  have hPQ : P = Q := by
    by_contra hPQ
    let R : Polynomial ℚ := P - Q
    have hR : R ≠ 0 := sub_ne_zero.mpr hPQ
    let S : Finset ℚ := (Finset.range (m + 1)).image fun q : ℕ => (q : ℚ)
    have hScard : S.card = m + 1 := by
      dsimp [S]
      rw [Finset.card_image_iff.mpr
        (Set.injOn_of_injective
          (Nat.cast_injective : Function.Injective (fun q : ℕ => (q : ℚ))))]
      exact Finset.card_range _
    have hRdegree : R.natDegree ≤ m := by
      dsimp [R]
      simpa using Polynomial.natDegree_sub_le_of_le hPdegree hQdegree
    have hSroots : ∀ x ∈ S, R.eval x = 0 := by
      intro x hx
      rcases Finset.mem_image.mp hx with ⟨q, hq, rfl⟩
      have hqm : q ≤ m := by
        have hq' := Finset.mem_range.mp hq
        omega
      dsimp [R]
      rw [Polynomial.eval_sub, hPeval q,
        show Q = natBinomialExpansion f m by rfl,
        binomial_expansion_polynomial,
        nat_binomial_range f hqm]
      simp
    have hroots : R.roots = S.val :=
      Polynomial.roots_eq_of_natDegree_le_card_of_ne_zero
        hSroots
        (hRdegree.trans (by rw [hScard]; exact Nat.le_succ m))
        hR
    have hrootCard : R.roots.card = m + 1 := by
      rw [hroots]
      simpa using hScard
    have hrootBound := Polynomial.card_roots' R
    rw [hrootCard] at hrootBound
    omega
  intro q
  have hcast :
      (f q : ℚ) =
        ((∑ k ∈ Finset.range (m + 1),
          natBinomialCoefficient f k * (Nat.choose q k : ℤ)) : ℤ) := by
    rw [← hPeval q, hPQ, show Q = natBinomialExpansion f m by rfl,
      binomial_expansion_polynomial]
  exact_mod_cast hcast

/--
For a positive binomial index below `m`, the binomial coefficient at a prime
power carries every `p`-power left after paying for `⌊log_p m⌋`.
-/
lemma log_cast_choose
    {p a k m : ℕ}
    [Fact p.Prime]
    (hk : 0 < k)
    (hkm : k ≤ m) :
    ((p ^ (a - Nat.log p m) : ℕ) : ℤ) ∣
      (Nat.choose (p ^ a) k : ℤ) := by
  by_cases hka : k ≤ p ^ a
  · have hchoose : Nat.choose (p ^ a) k ≠ 0 :=
      Nat.choose_ne_zero hka
    have hproduct :
        p ^ a ∣ k * Nat.choose (p ^ a) k :=
      HPGood.dvd_choose_nat
    have hproductVal :
        a ≤ padicValNat p (k * Nat.choose (p ^ a) k) :=
      (padicValNat_dvd_iff_le (Nat.mul_ne_zero hk.ne' hchoose)).mp hproduct
    rw [padicValNat.mul hk.ne' hchoose] at hproductVal
    have hkVal : padicValNat p k ≤ Nat.log p m :=
      (padicValNat_le_nat_log k).trans (Nat.log_mono_right hkm)
    have hchooseVal :
        a - Nat.log p m ≤ padicValNat p (Nat.choose (p ^ a) k) := by
      omega
    exact_mod_cast (padicValNat_dvd_iff_le hchoose).mpr hchooseVal
  · have hchoose : Nat.choose (p ^ a) k = 0 :=
      Nat.choose_eq_zero_of_lt (Nat.lt_of_not_ge hka)
    simp [hchoose]

/--
TeX Claim 6: an integer-valued polynomial of degree at most `m` that vanishes
at `0` takes a value at `p ^ a` divisible by
`p ^ (a - ⌊log_p m⌋)`.  Natural subtraction records the convention that a
negative requested exponent imposes no condition.
-/
theorem integer_valued_dvd
    {p : ℕ}
    [Fact p.Prime]
    {f : ℕ → ℤ}
    {m : ℕ}
    (hP : IVMost f m)
    (hPzero : f 0 = 0)
    (a : ℕ) :
    ((p ^ (a - Nat.log p m) : ℕ) : ℤ) ∣ f (p ^ a) := by
  rw [hP.nat_binomial_basisexpansion (p ^ a)]
  apply Finset.dvd_sum
  intro k hk
  by_cases hkZero : k = 0
  · subst k
    simp [natBinomialCoefficient, hPzero]
  · have hkPos : 0 < k := Nat.pos_of_ne_zero hkZero
    have hkm : k ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    exact dvd_mul_of_dvd_right
      (log_cast_choose hkPos hkm)
      (natBinomialCoefficient f k)

/--
The TeX exponent `alpha(s)`: the least prime-power exponent whose weighted
Hall coordinate of ordinary weight `s` reaches the requested Zassenhaus level.
The `max 1 s` keeps the definition total; Claim 7 only uses positive `s`.
-/
noncomputable def leastWeightedExponent
    (p n s : ℕ) [Fact p.Prime] :
    ℕ :=
  Nat.find (show ∃ j : ℕ, n ≤ max 1 s * p ^ j by
    refine ⟨leastPrimeExponent p n, ?_⟩
    calc
      n ≤ p ^ leastPrimeExponent p n :=
        pow_least_exponent p n
      _ = 1 * p ^ leastPrimeExponent p n := by simp
      _ ≤ max 1 s * p ^ leastPrimeExponent p n := by
        gcongr
        exact Nat.le_max_left 1 s)

lemma mul_least_exponent
    (p n s : ℕ) [Fact p.Prime]
    (hs : 1 ≤ s) :
    n ≤ s * p ^ leastWeightedExponent p n s := by
  simpa [leastWeightedExponent, Nat.max_eq_right hs] using
    (Nat.find_spec (show ∃ j : ℕ, n ≤ max 1 s * p ^ j by
      refine ⟨leastPrimeExponent p n, ?_⟩
      calc
        n ≤ p ^ leastPrimeExponent p n :=
          pow_least_exponent p n
        _ = 1 * p ^ leastPrimeExponent p n := by simp
        _ ≤ max 1 s * p ^ leastPrimeExponent p n := by
          gcongr
          exact Nat.le_max_left 1 s))

lemma least_prime_exponent
    {p n s j : ℕ} [Fact p.Prime]
    (hs : 1 ≤ s)
    (hlevel : n ≤ s * p ^ j) :
    leastWeightedExponent p n s ≤ j := by
  apply Nat.find_min'
  simpa [Nat.max_eq_right hs] using hlevel

/--
The chosen Hall coordinates of the identity vanish in every ordinary weight
strictly below the truncation class.
-/
lemma coordinate_one_zero
    {d n s : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ t : ℕ, BCWta.{u} d t)
    (hH :
      ∀ t : ℕ,
        1 ≤ t →
          t < n →
            (H t).FormsAssocGradedbasis (n := n))
    (hs : 1 ≤ s)
    (hsn : s < n)
    (i : (H s).index) :
    hallCoordinate hn H hH
        (1 : LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n) i = 0 := by
  let e : HEFam H :=
    normalFormCoordinates hn H hH
      (1 : LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
  have heProduct : collectedHallProduct (n := n) H e = 1 :=
    collected_form_coordinates hn H hH 1
  have heZero : e s = 0 :=
    collected_imp_coordinates hn H hH e heProduct s hs hsn
  change normalFormCoordinates hn H hH
      (1 : LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n) s i = 0
  simpa [e] using congrFun heZero i

/--
A Hall coordinate below the lower-central depth of an element is zero.
-/
lemma lower_central_series
    {d n r s : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ t : ℕ, BCWta.{u} d t)
    (hH :
      ∀ t : ℕ,
        1 ≤ t →
          t < n →
            (H t).FormsAssocGradedbasis (n := n))
    (y : LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
    (hy :
      y ∈ Subgroup.lowerCentralSeries
        (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n) (r - 1))
    (hs : 1 ≤ s)
    (hsr : s < r)
    (hsn : s < n)
    (i : (H s).index) :
    hallCoordinate hn H hH y i = 0 := by
  let e : HEFam H := normalFormCoordinates hn H hH y
  have heMem :
      collectedHallProduct (n := n) H e ∈
        Subgroup.lowerCentralSeries
          (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n) (r - 1) := by
    rw [collected_form_coordinates hn H hH y]
    exact hy
  have heZero : e s = 0 :=
    imp_coordinates_below
      hn H hH e heMem s hs hsr hsn
  change normalFormCoordinates hn H hH y s i = 0
  simpa [e] using congrFun heZero i

/--
TeX Claim 7, the weight-`s` divisibility statement when `s ≥ r`: Claim 5
gives the coordinate polynomial, the coordinate at `0` is the identity
coordinate, and Claim 6 supplies the prime-power divisibility.
-/
theorem hall_coordinate_dvd
    {p d n r s : ℕ}
    [Fact p.Prime]
    (hn : 2 ≤ n)
    (H : ∀ t : ℕ, BCWta.{u} d t)
    (hH :
      ∀ t : ℕ,
        1 ≤ t →
          t < n →
            (H t).FormsAssocGradedbasis (n := n))
    (hpower :
      ∀ (e : HEFam H) (t : ℕ),
        1 ≤ t →
          CollectedPolynomialData (n := n) H e t)
    (u : LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
    (hu :
      u ∈ Subgroup.lowerCentralSeries
        (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n) (r - 1))
    (hr : 1 ≤ r)
    (hs : 1 ≤ s)
    (hsn : s < n)
    (_hrs : r ≤ s)
    (a : ℕ)
    (i : (H s).index) :
    ((p ^ (a - Nat.log p (s / r)) : ℕ) : ℤ) ∣
      hallCoordinate hn H hH (u ^ (p ^ a)) i := by
  have hP :
      IVMost
        (fun q : ℕ => hallCoordinate hn H hH (u ^ q) i)
        (s / r) :=
    integer_valued_most
      hn H hH hpower u hu hr hs hsn i
  have hPzero :
      hallCoordinate hn H hH (u ^ 0) i = 0 := by
    simpa using coordinate_one_zero hn H hH hs hsn i
  exact integer_valued_dvd hP hPzero a

/--
TeX Claim 7, the low-weight vanishing statement: powers stay in the same
lower-central subgroup, so all Hall coordinates below that depth vanish.
-/
theorem hall_coordinate_zero
    {p d n r s : ℕ}
    [Fact p.Prime]
    (hn : 2 ≤ n)
    (H : ∀ t : ℕ, BCWta.{u} d t)
    (hH :
      ∀ t : ℕ,
        1 ≤ t →
          t < n →
            (H t).FormsAssocGradedbasis (n := n))
    (u : LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
    (hu :
      u ∈ Subgroup.lowerCentralSeries
        (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n) (r - 1))
    (hs : 1 ≤ s)
    (hsr : s < r)
    (hsn : s < n)
    (a : ℕ)
    (i : (H s).index) :
    hallCoordinate hn H hH (u ^ (p ^ a)) i = 0 := by
  exact lower_central_series
    hn H hH (u ^ (p ^ a))
    ((Subgroup.lowerCentralSeries
      (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n) (r - 1)).pow_mem
      hu (p ^ a))
    hs hsr hsn i

lemma mul_sub_log
    {p n r s a : ℕ}
    [Fact p.Prime]
    (hr : 1 ≤ r)
    (hrs : r ≤ s)
    (hsn : s < n)
    (hlevel : n ≤ r * p ^ a) :
    n ≤ s * p ^ (a - Nat.log p (s / r)) := by
  let m : ℕ := s / r
  have hrPos : 0 < r := hr
  have hmPos : 0 < m := by
    dsimp [m]
    exact Nat.div_pos hrs hrPos
  have hmLtPow : m < p ^ a := by
    dsimp [m]
    rw [Nat.div_lt_iff_lt_mul hrPos]
    exact hsn.trans_le (by simpa [Nat.mul_comm] using hlevel)
  have hlogLe : Nat.log p m ≤ a :=
    (Nat.log_lt_of_lt_pow hmPos.ne' hmLtPow).le
  have hpowLog : p ^ Nat.log p m ≤ m :=
    Nat.pow_log_le_self p hmPos.ne'
  calc
    n ≤ r * p ^ a := hlevel
    _ = r * (p ^ Nat.log p m * p ^ (a - Nat.log p m)) := by
      rw [← pow_add, Nat.add_comm, Nat.sub_add_cancel hlogLe]
    _ = (r * p ^ Nat.log p m) * p ^ (a - Nat.log p m) := by
      rw [mul_assoc]
    _ ≤ (r * m) * p ^ (a - Nat.log p m) := by
      gcongr
    _ ≤ s * p ^ (a - Nat.log p m) := by
      gcongr
      simpa [m, Nat.mul_comm] using Nat.div_mul_le_self s r

/--
TeX Claim 7, the final `alpha(s)` consequence: if the original weight `r`
already reaches level `n` after `p ^ a`, then every weight-`s` Hall
coordinate is divisible by the least weighted exponent for `s`.
-/
theorem least_weighted_exponent
    {p d n r s : ℕ}
    [Fact p.Prime]
    (hn : 2 ≤ n)
    (H : ∀ t : ℕ, BCWta.{u} d t)
    (hH :
      ∀ t : ℕ,
        1 ≤ t →
          t < n →
            (H t).FormsAssocGradedbasis (n := n))
    (hpower :
      ∀ (e : HEFam H) (t : ℕ),
        1 ≤ t →
          CollectedPolynomialData (n := n) H e t)
    (u : LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
    (hu :
      u ∈ Subgroup.lowerCentralSeries
        (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n) (r - 1))
    (hr : 1 ≤ r)
    (hs : 1 ≤ s)
    (hsn : s < n)
    (a : ℕ)
    (hlevel : n ≤ r * p ^ a)
    (i : (H s).index) :
    ((p ^ leastWeightedExponent p n s : ℕ) : ℤ) ∣
      hallCoordinate hn H hH (u ^ (p ^ a)) i := by
  by_cases hrs : r ≤ s
  · have hmain :
        ((p ^ (a - Nat.log p (s / r)) : ℕ) : ℤ) ∣
          hallCoordinate hn H hH (u ^ (p ^ a)) i :=
      hall_coordinate_dvd
        hn H hH hpower u hu hr hs hsn hrs a i
    have halphaLe :
        leastWeightedExponent p n s ≤ a - Nat.log p (s / r) :=
      least_prime_exponent hs
        (mul_sub_log hr hrs hsn hlevel)
    exact
      (Int.ofNat_dvd.mpr (pow_dvd_pow p halphaLe)).trans hmain
  · rw [hall_coordinate_zero
      hn H hH u hu hs (Nat.lt_of_not_ge hrs) hsn a i]
    exact dvd_zero _

/--
One Hall exponent address: an ordinary weight together with one Hall
commutator index in that weight layer.
-/
abbrev HEAddres
    {d : ℕ}
    (H : ∀ r : ℕ, BCWta.{u} d r) :
    Type u :=
  Σ r : ℕ, (H r).index

/--
One TeX Claim 8 binomial monomial.  The `input` field picks one collected Hall
input, `address` picks one Hall exponent in that input, and `binomialIndex`
records the positive binomial coefficient index used there.
-/
structure WHMono
    {d : ℕ}
    (H : ∀ r : ℕ, BCWta.{u} d r)
    (ι : Type)
    (s : ℕ) where
  length : ℕ
  length_pos : 0 < length
  input : Fin length → ι
  address : Fin length → HEAddres H
  binomialIndex : Fin length → ℕ
  binomialIndex_pos : ∀ ν, 0 < binomialIndex ν
  weightedWeight_le :
    ∑ ν, binomialIndex ν * (address ν).1 ≤ s

/--
Evaluate one TeX Claim 8 binomial monomial on the chosen input Hall exponent
families.
-/
def WHMono.eval
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {s : ℕ}
    (m : WHMono H ι s)
    (e : ι → HEFam H) :
    ℤ :=
  ∏ ν,
    Ring.choose
      (e (m.input ν) (m.address ν).1 (m.address ν).2)
      (m.binomialIndex ν)

/--
One genuinely mixed binary correction monomial for a Hall product law.  The
two inputs are indexed by `Fin 2`: side `0` is the left collected word and
side `1` is the right collected word.  The `has_left` and `has_right` fields
rule out constant and one-sided terms, which is the precise triangular feature
needed for the power recurrence.
-/
structure BCMono
    {d : ℕ}
    (H : ∀ r : ℕ, BCWta.{u} d r)
    (s : ℕ) where
  length : ℕ
  length_pos : 0 < length
  side : Fin length → Fin 2
  address : Fin length → HEAddres H
  binomialIndex : Fin length → ℕ
  binomialIndex_pos : ∀ ν, 0 < binomialIndex ν
  weightedWeight_le :
    ∑ ν, binomialIndex ν * (address ν).1 ≤ s
  has_left : ∃ ν, side ν = 0
  has_right : ∃ ν, side ν = 1

/-- Evaluate one mixed binary correction monomial on a pair of Hall families. -/
def BCMono.eval
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {s : ℕ}
    (m : BCMono H s)
    (left right : HEFam H) :
    ℤ :=
  ∏ ν,
    Ring.choose
      ((if m.side ν = 0 then left else right)
        (m.address ν).1 (m.address ν).2)
      (m.binomialIndex ν)

/-- A finite integer combination of mixed binary correction monomials. -/
structure BCComb
    {d : ℕ}
    (H : ∀ r : ℕ, BCWta.{u} d r)
    (s : ℕ) where
  length : ℕ
  monomial : Fin length → BCMono H s
  coefficient : Fin length → ℤ

/-- Evaluate a finite mixed binary correction combination. -/
def BCComb.eval
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {s : ℕ}
    (C : BCComb H s)
    (left right : HEFam H) :
    ℤ :=
  ∑ ν, C.coefficient ν * (C.monomial ν).eval left right

/--
TeX Claim 8's phrase "an integer linear combination of expressions" is the
`ℤ`-span of the admissible weighted binomial monomials.
-/
def ICMonomi
    {d : ℕ}
    (H : ∀ r : ℕ, BCWta.{u} d r)
    {ι : Type}
    (s : ℕ)
    (e : ι → HEFam H)
    (z : ℤ) :
    Prop :=
  z ∈ Submodule.span ℤ
    (Set.range fun m : WHMono H ι s => m.eval e)

/--
The coordinate language used below contains the zero coefficient.

This is kept local to this file to avoid changing the later symbolic
collection namespace, which provides a richer API with the same mathematical
content.
-/
lemma int_combination_monomials
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {s : ℕ}
    (e : ι → HEFam H) :
    ICMonomi H s e 0 :=
  (Submodule.span ℤ _).zero_mem

/-- The coordinate language is closed under addition. -/
lemma combination_monomials_add
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {s : ℕ}
    {e : ι → HEFam H}
    {x y : ℤ}
    (hx : ICMonomi H s e x)
    (hy : ICMonomi H s e y) :
    ICMonomi H s e (x + y) :=
  (Submodule.span ℤ _).add_mem hx hy

/-- The coordinate language is closed under integer scaling. -/
lemma combination_monomials_smul
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {s : ℕ}
    {e : ι → HEFam H}
    (c : ℤ)
    {x : ℤ}
    (hx : ICMonomi H s e x) :
    ICMonomi H s e (c * x) := by
  simpa [smul_eq_mul] using (Submodule.span ℤ _).smul_mem c hx

/-- The coordinate language is closed under negation. -/
lemma combination_monomials_neg
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {s : ℕ}
    {e : ι → HEFam H}
    {x : ℤ}
    (hx : ICMonomi H s e x) :
    ICMonomi H s e (-x) := by
  simpa using combination_monomials_smul (-1) hx

/-- The coordinate language is closed under subtraction. -/
lemma combination_monomials_sub
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {s : ℕ}
    {e : ι → HEFam H}
    {x y : ℤ}
    (hx : ICMonomi H s e x)
    (hy : ICMonomi H s e y) :
    ICMonomi H s e (x - y) := by
  simpa [sub_eq_add_neg] using
    combination_monomials_add hx
      (combination_monomials_neg hy)

/-- A singleton weighted binomial monomial representing one raw input coordinate. -/
def weighted_monomial_single
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {s : ℕ}
    (j : ι)
    (a : HEAddres H)
    (ha : a.1 ≤ s) :
    WHMono H ι s where
  length := 1
  length_pos := by simp
  input := fun _ => j
  address := fun _ => a
  binomialIndex := fun _ => 1
  binomialIndex_pos := by simp
  weightedWeight_le := by simpa using ha

@[simp]
lemma binomial_monomial_single
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {s : ℕ}
    (e : ι → HEFam H)
    (j : ι)
    (a : HEAddres H)
    (ha : a.1 ≤ s) :
    (weighted_monomial_single j a ha).eval e =
      e j a.1 a.2 := by
  simp [weighted_monomial_single,
    WHMono.eval]

/-- Relabel the source inputs of a weighted binomial monomial. -/
def weighted_monomial_input
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι κ : Type}
    {s : ℕ}
    (f : ι → κ)
    (m : WHMono H ι s) :
    WHMono H κ s where
  length := m.length
  length_pos := m.length_pos
  input := f ∘ m.input
  address := m.address
  binomialIndex := m.binomialIndex
  binomialIndex_pos := m.binomialIndex_pos
  weightedWeight_le := m.weightedWeight_le

@[simp]
lemma binomial_monomial_input
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι κ : Type}
    {s : ℕ}
    (e : κ → HEFam H)
    (f : ι → κ)
    (m : WHMono H ι s) :
    (weighted_monomial_input f m).eval e =
      m.eval (e ∘ f) :=
  rfl

/-- Each raw Hall exponent is one admissible singleton binomial monomial. -/
lemma combination_monomials_input
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {s : ℕ}
    (e : ι → HEFam H)
    (j : ι)
    (a : HEAddres H)
    (ha : a.1 ≤ s) :
    ICMonomi H s e (e j a.1 a.2) := by
  apply Submodule.subset_span
  exact
    ⟨weighted_monomial_single j a ha, by simp⟩

/--
Relabelling source inputs preserves the integer span of admissible weighted
binomial monomials.
-/
lemma binomial_monomials_input
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι κ : Type}
    {s : ℕ}
    (e : κ → HEFam H)
    (f : ι → κ)
    {x : ℤ}
    (hx :
      ICMonomi H s (e ∘ f) x) :
    ICMonomi H s e x := by
  refine Submodule.span_induction
    (p := fun x _ => ICMonomi H s e x)
    ?_ (int_combination_monomials e)
    (fun _ _ _ _ hx hy => (Submodule.span ℤ _).add_mem hx hy)
    (fun c x _ hx => (Submodule.span ℤ _).smul_mem c hx) hx
  · rintro _ ⟨m, rfl⟩
    apply Submodule.subset_span
    exact
      ⟨weighted_monomial_input f m, by simp⟩

/--
All coordinates of a Hall exponent family are weighted-binomial combinations
of a chosen ambient family of input Hall exponent families.
-/
def WeightedBinomialCombinations
    {d n : ℕ}
    (H : ∀ r : ℕ, BCWta.{u} d r)
    {ι : Type}
    (input : ι → HEFam H)
    (e : HEFam H) :
    Prop :=
  ∀ s : ℕ,
    1 ≤ s →
      s < n →
        ∀ i : (H s).index,
          ICMonomi H s input (e s i)

/--
The product of a finite list of already collected Hall products, before
recollection back into one collected Hall product.
-/
def collectedHallProducts
    {d n : ℕ}
    (H : ∀ r : ℕ, BCWta.{u} d r)
    (e : List (HEFam H)) :
    LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n :=
  (e.map fun f => collectedHallProduct (n := n) H f).prod

/--
Negating every Hall exponent records the raw exponent list appearing after
reversing a collected Hall product to form its inverse.
-/
def negExponentFamily
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (e : HEFam H) :
    HEFam H :=
  fun r i => -e r i

/--
The universal TeX Claim 8 collection-polynomial input for recollecting a finite
product of collected Hall products.
-/
def CollectedCoordinateData
    {d n : ℕ}
    (H : ∀ r : ℕ, BCWta.{u} d r)
    (e : List (HEFam H)) :
    Prop :=
  ∃ E : HEFam H,
    collectedHallProduct (n := n) H E = collectedHallProducts (n := n) H e ∧
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            ∀ i : (H s).index,
              ICMonomi
                (ι := Fin e.length) H s (fun j : Fin e.length => e.get j) (E s i)

/--
The universal TeX Claim 8 collection-polynomial input for recollecting the
inverse of one collected Hall product.
-/
def CollectedInverseData
    {d n : ℕ}
    (H : ∀ r : ℕ, BCWta.{u} d r)
    (e : HEFam H) :
    Prop :=
  ∃ E : HEFam H,
    collectedHallProduct (n := n) H E = (collectedHallProduct (n := n) H e)⁻¹ ∧
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            ∀ i : (H s).index,
              ICMonomi
                (ι := Fin 1) H s (fun _ : Fin 1 => negExponentFamily e) (E s i)

/--
TeX Claim 8, product form: once the symbolic collection-polynomial data for a
finite product is supplied, each canonical Hall coordinate of the recollected
product is a `ℤ`-linear combination of admissible weighted binomial monomials.
-/
theorem products_combination_monomials
    {d n s : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ r : ℕ, BCWta.{u} d r)
    (hH :
      ∀ r : ℕ,
        1 ≤ r →
          r < n →
            (H r).FormsAssocGradedbasis (n := n))
    (e : List (HEFam H))
    (hcollection : CollectedCoordinateData (n := n) H e)
    (hs : 1 ≤ s)
    (hsn : s < n)
    (i : (H s).index) :
    ICMonomi
      (ι := Fin e.length) H s (fun j : Fin e.length => e.get j)
      (hallCoordinate hn H hH (collectedHallProducts (n := n) H e) i) := by
  rcases hcollection with ⟨E, hEproduct, hEcoordinate⟩
  have hcoordinates :
      normalFormCoordinates hn H hH (collectedHallProducts (n := n) H e) s =
        E s :=
    form_coordinates_collected
      hn H hH E (collectedHallProducts (n := n) H e) hEproduct s hs hsn
  simpa [hallCoordinate, hcoordinates] using hEcoordinate s hs hsn i

/--
TeX Claim 8, inverse form: once the symbolic collection-polynomial data for an
inverse is supplied, each canonical Hall coordinate of the recollected inverse
is a `ℤ`-linear combination of admissible weighted binomial monomials in the
raw exponents `-E_i`.
-/
theorem weighted_binomial_combination
    {d n s : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ r : ℕ, BCWta.{u} d r)
    (hH :
      ∀ r : ℕ,
        1 ≤ r →
          r < n →
            (H r).FormsAssocGradedbasis (n := n))
    (e : HEFam H)
    (hcollection : CollectedInverseData (n := n) H e)
    (hs : 1 ≤ s)
    (hsn : s < n)
    (i : (H s).index) :
    ICMonomi
      (ι := Fin 1) H s (fun _ : Fin 1 => negExponentFamily e)
      (hallCoordinate hn H hH (collectedHallProduct (n := n) H e)⁻¹ i) := by
  rcases hcollection with ⟨E, hEproduct, hEcoordinate⟩
  have hcoordinates :
      normalFormCoordinates hn H hH (collectedHallProduct (n := n) H e)⁻¹ s =
        E s :=
    form_coordinates_collected
      hn H hH E (collectedHallProduct (n := n) H e)⁻¹ hEproduct s hs hsn
  simpa [hallCoordinate, hcoordinates] using hEcoordinate s hs hsn i

/--
Every Hall basic commutator has positive ordinary weight, because its atoms
all have ordinary weight one.
-/
lemma BCWt.weight_pos
    {d r : ℕ}
    (h : BCWt.{u} d r) :
    0 < r := by
  rw [← h.word_weight]
  exact CWord.weight_pos (fun _ => 1) (fun _ => by simp) h.word

/--
If `p ^ a` divides an integer `A`, then the generalized binomial coefficient
`choose A k` retains the `p`-power left after paying for the `p`-part of `k`.
-/
lemma log_dvd_choose
    {p a k : ℕ}
    [Fact p.Prime]
    {A : ℤ}
    (hk : 0 < k)
    (hA : ((p ^ a : ℕ) : ℤ) ∣ A) :
    ((p ^ (a - Nat.log p k) : ℕ) : ℤ) ∣ Ring.choose A k := by
  by_cases hchoose : Ring.choose A k = 0
  · rw [hchoose]
    exact dvd_zero _
  have hkCast : (k : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr hk.ne'
  have hchooseProduct :
      (k : ℤ) * Ring.choose A k =
        A * Ring.choose (A - 1) (k - 1) := by
    have hchooseSmul :=
      Ring.choose_smul_choose (R := ℤ) A (n := k) (k := 1) hk
    simpa [nsmul_eq_mul, Ring.choose_one_right, Nat.choose_one_right] using hchooseSmul
  have hproductDvd :
      (p : ℤ) ^ a ∣ (k : ℤ) * Ring.choose A k := by
    rw [hchooseProduct]
    simpa only [Nat.cast_pow] using dvd_mul_of_dvd_left hA _
  have hproductVal :
      a ≤ padicValInt p ((k : ℤ) * Ring.choose A k) := by
    exact
      ((padicValInt_dvd_iff a ((k : ℤ) * Ring.choose A k)).mp hproductDvd).resolve_left
        (mul_ne_zero hkCast hchoose)
  rw [padicValInt.mul hkCast hchoose] at hproductVal
  have hkVal : padicValInt p (k : ℤ) ≤ Nat.log p k := by
    rw [padicValInt.of_nat]
    exact padicValNat_le_nat_log k
  have hchooseVal : a - Nat.log p k ≤ padicValInt p (Ring.choose A k) := by
    omega
  simpa only [Nat.cast_pow] using
    (padicValInt_dvd_iff (a - Nat.log p k) (Ring.choose A k)).mpr
      (Or.inr hchooseVal)

/--
A family of Hall exponents satisfies the TeX lattice divisibility condition
when every positive ordinary weight below `n` is divisible by the weighted
prime power assigned to that weight.
-/
def EWCoordi
    {d : ℕ}
    (p n : ℕ)
    [Fact p.Prime]
    (H : ∀ r : ℕ, BCWta.{u} d r)
    (e : HEFam H) :
    Prop :=
  ∀ s : ℕ,
    1 ≤ s →
      s < n →
        ∀ i : (H s).index,
          ((p ^ leastWeightedExponent p n s : ℕ) : ℤ) ∣ e s i

/--
Divisibility by one integer is closed under the `ℤ`-span used in Claim 8.
-/
lemma combination_binomial_monomials
    {p d n s : ℕ}
    [Fact p.Prime]
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {e : ι → HEFam H}
    {z : ℤ}
    (hgenerator :
      ∀ m : WHMono H ι s,
        ((p : ℤ) ^ leastWeightedExponent p n s) ∣ m.eval e)
    (hz : ICMonomi H s e z) :
    ((p : ℤ) ^ leastWeightedExponent p n s) ∣ z := by
  refine Submodule.span_induction
    (p := fun x _ => ((p : ℤ) ^ leastWeightedExponent p n s) ∣ x)
    ?_ (dvd_zero _) (fun _ _ _ _ hx hy => dvd_add hx hy)
    (fun c x _ hx => ?_) hz
  · rintro _ ⟨m, rfl⟩
    exact hgenerator m
  · simpa [smul_eq_mul, mul_comm] using dvd_mul_of_dvd_right hx c

/--
The ordinary weight selected by one monomial factor is positive.
-/
lemma WHMono.commutatorWeight_pos
    {d s : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (m : WHMono H ι s)
    (ν : Fin m.length) :
    0 < (m.address ν).1 :=
  (H (m.address ν).1).commutator (m.address ν).2 |>.weight_pos

/-- The ordinary weight selected by one binary correction factor is positive. -/
lemma BCMono.commutatorWeight_pos
    {d s : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (m : BCMono H s)
    (ν : Fin m.length) :
    0 < (m.address ν).1 :=
  (H (m.address ν).1).commutator (m.address ν).2 |>.weight_pos

/--
The prime-power divisibility attached to one Hall exponent survives one
generalized binomial coefficient with positive binomial index.
-/
lemma WHMono.factordvd_primepow_sublog
    {p d n s : ℕ}
    [Fact p.Prime]
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {e : ι → HEFam H}
    (he : ∀ j : ι, EWCoordi p n H (e j))
    (hsn : s < n)
    (m : WHMono H ι s)
    (ν : Fin m.length) :
    ((p ^ (leastWeightedExponent p n (m.address ν).1 -
        Nat.log p (m.binomialIndex ν)) : ℕ) : ℤ) ∣
      Ring.choose
        (e (m.input ν) (m.address ν).1 (m.address ν).2)
        (m.binomialIndex ν) := by
  have hr : 1 ≤ (m.address ν).1 := Nat.succ_le_iff.mpr (m.commutatorWeight_pos ν)
  have htermLe :
      m.binomialIndex ν * (m.address ν).1 ≤ s :=
    (Finset.single_le_sum
      (fun μ _ => Nat.zero_le (m.binomialIndex μ * (m.address μ).1))
      (Finset.mem_univ ν)).trans m.weightedWeight_le
  have hrn : (m.address ν).1 < n := by
    have hrLeTerm :
        (m.address ν).1 ≤ m.binomialIndex ν * (m.address ν).1 := by
      calc
        (m.address ν).1 = 1 * (m.address ν).1 := by simp
        _ ≤ m.binomialIndex ν * (m.address ν).1 := by
          gcongr
          exact m.binomialIndex_pos ν
    exact (hrLeTerm.trans htermLe).trans_lt hsn
  exact log_dvd_choose
    (m.binomialIndex_pos ν)
    (he (m.input ν) (m.address ν).1 hr hrn (m.address ν).2)

/--
Multiplying coordinatewise prime-power divisors gives the divisor attached to
the sum of their exponents.
-/
lemma int_dvd_prod
    {ι : Type}
    (p : ℕ)
    (t : Finset ι)
    (a : ι → ℕ)
    (z : ι → ℤ)
    (hz : ∀ i ∈ t, (p : ℤ) ^ a i ∣ z i) :
    (p : ℤ) ^ ∑ i ∈ t, a i ∣ ∏ i ∈ t, z i := by
  classical
  induction t using Finset.induction_on with
  | empty =>
      simp
  | @insert i t hi ih =>
      rw [Finset.sum_insert hi, Finset.prod_insert hi, pow_add]
      exact mul_dvd_mul
        (hz i (Finset.mem_insert_self i t))
        (ih (fun j hj => hz j (Finset.mem_insert_of_mem hj)))

/--
The TeX inequality `alpha(s) ≤ V` for one admissible weighted binomial
monomial.
-/
lemma WHMono.lesum_primepower_exponentsublog
    {p d n s : ℕ}
    [Fact p.Prime]
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (hs : 1 ≤ s)
    (hsn : s < n)
    (m : WHMono H ι s) :
    leastWeightedExponent p n s ≤
      ∑ ν,
        (leastWeightedExponent p n (m.address ν).1 -
          Nat.log p (m.binomialIndex ν)) := by
  let ν0 : Fin m.length := ⟨0, m.length_pos⟩
  let r0 : ℕ := (m.address ν0).1
  let k0 : ℕ := m.binomialIndex ν0
  let a0 : ℕ := leastWeightedExponent p n r0
  let V : ℕ :=
    ∑ ν,
      (leastWeightedExponent p n (m.address ν).1 -
        Nat.log p (m.binomialIndex ν))
  have hr0 : 1 ≤ r0 := by
    dsimp [r0]
    exact Nat.succ_le_iff.mpr (m.commutatorWeight_pos ν0)
  have hk0 : 0 < k0 := by
    dsimp [k0]
    exact m.binomialIndex_pos ν0
  have htermLe :
      k0 * r0 ≤ s := by
    dsimp [k0, r0]
    exact
      (Finset.single_le_sum
        (fun μ _ => Nat.zero_le (m.binomialIndex μ * (m.address μ).1))
        (Finset.mem_univ ν0)).trans m.weightedWeight_le
  have hr0n : r0 < n := by
    have hr0LeTerm : r0 ≤ k0 * r0 := by
      calc
        r0 = 1 * r0 := by simp
        _ ≤ k0 * r0 := by
          gcongr
          exact hk0
    exact (hr0LeTerm.trans htermLe).trans_lt hsn
  have hlevel0 : n ≤ r0 * p ^ a0 := by
    dsimp [a0]
    exact mul_least_exponent p n r0 hr0
  have hk0LtPow : k0 < p ^ a0 := by
    apply (Nat.mul_lt_mul_right hr0).mp
    exact htermLe.trans_lt hsn |>.trans_le (by simpa [Nat.mul_comm] using hlevel0)
  have hlog0Lt : Nat.log p k0 < a0 :=
    Nat.log_lt_of_lt_pow hk0.ne' hk0LtPow
  have hlog0Le : Nat.log p k0 ≤ a0 := hlog0Lt.le
  have hpowLog0 : p ^ Nat.log p k0 ≤ k0 :=
    Nat.pow_log_le_self p hk0.ne'
  have hpowAlpha0Le :
      p ^ a0 ≤ k0 * p ^ (a0 - Nat.log p k0) := by
    calc
      p ^ a0 = p ^ (Nat.log p k0 + (a0 - Nat.log p k0)) := by
        rw [Nat.add_sub_of_le hlog0Le]
      _ = p ^ Nat.log p k0 * p ^ (a0 - Nat.log p k0) := by
        rw [pow_add]
      _ ≤ k0 * p ^ (a0 - Nat.log p k0) := by
        gcongr
  have htermLeV :
      a0 - Nat.log p k0 ≤ V := by
    dsimp [a0, k0, V]
    exact Finset.single_le_sum
      (fun ν _ => Nat.zero_le
        (leastWeightedExponent p n (m.address ν).1 -
          Nat.log p (m.binomialIndex ν)))
      (Finset.mem_univ ν0)
  have hpowTermLeV :
      p ^ (a0 - Nat.log p k0) ≤ p ^ V :=
    Nat.pow_le_pow_right (Fact.out : Nat.Prime p).pos htermLeV
  apply least_prime_exponent hs
  calc
    n ≤ r0 * p ^ a0 := hlevel0
    _ ≤ r0 * (k0 * p ^ (a0 - Nat.log p k0)) := by
      gcongr
    _ = k0 * r0 * p ^ (a0 - Nat.log p k0) := by
      ac_rfl
    _ ≤ k0 * r0 * p ^ V := by
      gcongr
    _ ≤ s * p ^ V := by
      gcongr

/--
Every admissible Claim 8 weighted Hall binomial monomial is divisible by the
prime power assigned to its output Hall weight.
-/
lemma WHMono.evaldvd_leastweight_primpoweexpo
    {p d n s : ℕ}
    [Fact p.Prime]
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {e : ι → HEFam H}
    (he : ∀ j : ι, EWCoordi p n H (e j))
    (hs : 1 ≤ s)
    (hsn : s < n)
    (m : WHMono H ι s) :
    ((p ^ leastWeightedExponent p n s : ℕ) : ℤ) ∣ m.eval e := by
  let V : ℕ :=
    ∑ ν,
      (leastWeightedExponent p n (m.address ν).1 -
        Nat.log p (m.binomialIndex ν))
  have hprodDvd :
      (p : ℤ) ^ V ∣ m.eval e := by
    dsimp [WHMono.eval, V]
    exact int_dvd_prod p Finset.univ
      (fun ν =>
        leastWeightedExponent p n (m.address ν).1 -
          Nat.log p (m.binomialIndex ν))
      (fun ν =>
        Ring.choose
          (e (m.input ν) (m.address ν).1 (m.address ν).2)
          (m.binomialIndex ν))
      (fun ν _ => by
        simpa only [Nat.cast_pow] using m.factordvd_primepow_sublog he hsn ν)
  have halphaLe :
      leastWeightedExponent p n s ≤ V :=
    m.lesum_primepower_exponentsublog hs hsn
  simpa only [Nat.cast_pow] using
    (pow_dvd_pow (p : ℤ) halphaLe).trans hprodDvd

/--
Claim 8 correction coordinates inherit the Hall-coordinate lattice
divisibility from all input Hall exponent families.
-/
lemma dvd_combination_monomials
    {p d n s : ℕ}
    [Fact p.Prime]
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {e : ι → HEFam H}
    {z : ℤ}
    (he : ∀ j : ι, EWCoordi p n H (e j))
    (hs : 1 ≤ s)
    (hsn : s < n)
    (hz : ICMonomi H s e z) :
    ((p ^ leastWeightedExponent p n s : ℕ) : ℤ) ∣ z := by
  simpa only [Nat.cast_pow] using
    combination_binomial_monomials
      (p := p)
      (n := n)
      (hgenerator := fun m => by
        simpa only [Nat.cast_pow] using
          m.evaldvd_leastweight_primpoweexpo he hs hsn)
      hz

/--
The TeX subset `L_n`: elements whose canonical Hall coordinates satisfy the
weighted prime-power divisibility assigned to each ordinary Hall weight.
-/
def HallCoordinateLattice
    {p d n : ℕ}
    [Fact p.Prime]
    (hn : 2 ≤ n)
    (H : ∀ r : ℕ, BCWta.{u} d r)
    (hH :
      ∀ r : ℕ,
        1 ≤ r →
          r < n →
            (H r).FormsAssocGradedbasis (n := n))
    (y : LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n) :
    Prop :=
  EWCoordi p n H
    (normalFormCoordinates hn H hH y)

/--
The identity has zero Hall coordinates, hence lies in the TeX lattice.
-/
lemma coordinate_lattice_one
    {p d n : ℕ}
    [Fact p.Prime]
    (hn : 2 ≤ n)
    (H : ∀ r : ℕ, BCWta.{u} d r)
    (hH :
      ∀ r : ℕ,
        1 ≤ r →
          r < n →
            (H r).FormsAssocGradedbasis (n := n)) :
    HallCoordinateLattice (p := p) hn H hH
      (1 : LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n) := by
  intro s hs hsn i
  rw [show normalFormCoordinates hn H hH
      (1 : LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n) s i =
        hallCoordinate hn H hH
          (1 : LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n) i by rfl,
    coordinate_one_zero hn H hH hs hsn i]
  exact dvd_zero _

/--
Negating a lattice Hall exponent family preserves every divisibility
condition, as required by the raw inverse word in Claim 9.
-/
lemma EWCoordi.neg
    {p d n : ℕ}
    [Fact p.Prime]
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {e : HEFam H}
    (he : EWCoordi p n H e) :
    EWCoordi p n H (negExponentFamily e) := by
  intro s hs hsn i
  rcases he s hs hsn i with ⟨c, hc⟩
  refine ⟨-c, ?_⟩
  rw [negExponentFamily, hc]
  ring

/--
Products of Hall-coordinate lattice elements stay in the lattice once Claim
8 supplies collection-polynomial data for their two collected normal forms.
-/
lemma coordinate_lattice_mul
    {p d n : ℕ}
    [Fact p.Prime]
    (hn : 2 ≤ n)
    (H : ∀ r : ℕ, BCWta.{u} d r)
    (hH :
      ∀ r : ℕ,
        1 ≤ r →
          r < n →
            (H r).FormsAssocGradedbasis (n := n))
    (hproduct :
      ∀ e : List (HEFam H),
        CollectedCoordinateData (n := n) H e)
    {y z : LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n}
    (hy : HallCoordinateLattice (p := p) hn H hH y)
    (hz : HallCoordinateLattice (p := p) hn H hH z) :
    HallCoordinateLattice (p := p) hn H hH (y * z) := by
  let ey : HEFam H := normalFormCoordinates hn H hH y
  let ez : HEFam H := normalFormCoordinates hn H hH z
  have hey : collectedHallProduct (n := n) H ey = y :=
    collected_form_coordinates hn H hH y
  have hez : collectedHallProduct (n := n) H ez = z :=
    collected_form_coordinates hn H hH z
  have hproductEq : collectedHallProducts (n := n) H [ey, ez] = y * z := by
    simp [collectedHallProducts, hey, hez]
  have hinput :
      ∀ j : Fin ([ey, ez].length),
        EWCoordi p n H ([ey, ez].get j) := by
    intro j
    fin_cases j
    · exact hy
    · exact hz
  intro s hs hsn i
  rw [← hproductEq]
  exact dvd_combination_monomials
    hinput hs hsn
    (products_combination_monomials
      hn H hH [ey, ez] (hproduct [ey, ez]) hs hsn i)

/--
Inverses of Hall-coordinate lattice elements stay in the lattice once Claim
8 supplies collection-polynomial data for the reversed negated raw exponents.
-/
lemma coordinate_lattice_inv
    {p d n : ℕ}
    [Fact p.Prime]
    (hn : 2 ≤ n)
    (H : ∀ r : ℕ, BCWta.{u} d r)
    (hH :
      ∀ r : ℕ,
        1 ≤ r →
          r < n →
            (H r).FormsAssocGradedbasis (n := n))
    (hinverse :
      ∀ e : HEFam H,
        CollectedInverseData (n := n) H e)
    {y : LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n}
    (hy : HallCoordinateLattice (p := p) hn H hH y) :
    HallCoordinateLattice (p := p) hn H hH y⁻¹ := by
  let e : HEFam H := normalFormCoordinates hn H hH y
  have he : EWCoordi p n H e := hy
  have hproductEq : collectedHallProduct (n := n) H e = y :=
    collected_form_coordinates hn H hH y
  intro s hs hsn i
  rw [← hproductEq]
  exact dvd_combination_monomials
    (fun _ => he.neg) hs hsn
    (weighted_binomial_combination
      hn H hH e (hinverse e) hs hsn i)

/--
TeX Claim 9: the Hall-coordinate lattice `L_n` is a subgroup of the free
nilpotent truncation once Claim 8 supplies product and inverse collection
polynomials.
-/
def hallCoordinateLattice
    {p d n : ℕ}
    [Fact p.Prime]
    (hn : 2 ≤ n)
    (H : ∀ r : ℕ, BCWta.{u} d r)
    (hH :
      ∀ r : ℕ,
        1 ≤ r →
          r < n →
            (H r).FormsAssocGradedbasis (n := n))
    (hproduct :
      ∀ e : List (HEFam H),
        CollectedCoordinateData (n := n) H e)
    (hinverse :
      ∀ e : HEFam H,
        CollectedInverseData (n := n) H e) :
    Subgroup (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n) where
  carrier := {y | HallCoordinateLattice (p := p) hn H hH y}
  one_mem' := coordinate_lattice_one hn H hH
  mul_mem' := coordinate_lattice_mul hn H hH hproduct
  inv_mem' := coordinate_lattice_inv hn H hH hinverse

/--
A fixed-weight collected Hall segment whose exponents satisfy the lattice
divisibility condition lies in the corresponding Zassenhaus term.
-/
lemma BCWta.collectedweight_productmem_zassfiltdvd
    {p d n r : ℕ}
    [Fact p.Prime]
    (H : BCWta.{u} d r)
    (hr : 1 ≤ r)
    (e : H.index → ℤ)
    (he :
      ∀ i,
        ((p ^ leastWeightedExponent p n r : ℕ) : ℤ) ∣ e i) :
    H.collectedWeightProduct (n := n) e ∈
      zassenhausFiltration
        p (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n) n := by
  let N : Type u := LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n
  let a : ℕ := leastWeightedExponent p n r
  have hlevel : n ≤ r * p ^ a := by
    exact mul_least_exponent p n r hr
  have hfactor :
      ∀ i : H.index,
        (H.commutator i).freeLowerTruncation (n := n) ^ e i ∈
          zassenhausFiltration p N n := by
    intro i
    rcases he i with ⟨m, hm⟩
    let g : N := (H.commutator i).freeLowerTruncation (n := n)
    have hg : g ∈ Subgroup.lowerCentralSeries N (r - 1) := by
      exact (H.commutator i).free_truncation_series
    have hbaseExact :
        g ^ (p ^ a) ∈ zassenhausFiltration p N (((r - 1) + 1) * p ^ a) :=
      lower_central_filtration (p := p) hg
    have hbase :
        g ^ (p ^ a) ∈ zassenhausFiltration p N n := by
      exact
        (zassenhausFiltration_antitone p N
          (by simpa [Nat.sub_add_cancel hr] using hlevel)) hbaseExact
    change g ^ e i ∈ zassenhausFiltration p N n
    rw [hm, zpow_mul, zpow_natCast]
    exact (zassenhausFiltration p N n).zpow_mem hbase m
  rw [BCWta.collectedWeightProduct,
    BCWta.collected_lower_centralterm,
    SubmonoidClass.coe_list_prod]
  apply Subgroup.list_prod_mem
  intro x hx
  rcases List.mem_map.mp hx with ⟨z, hz, rfl⟩
  rcases List.mem_map.mp hz with ⟨i, _hi, rfl⟩
  simpa using hfactor i

/--
TeX Claim 10: in the free nilpotent truncation, the Zassenhaus subgroup is
exactly the Hall-coordinate lattice.
-/
theorem zassenhaus_filtration_lattice
    {p d n : ℕ}
    [Fact p.Prime]
    (hn : 2 ≤ n)
    (H : ∀ r : ℕ, BCWta.{u} d r)
    (hH :
      ∀ r : ℕ,
        1 ≤ r →
          r < n →
            (H r).FormsAssocGradedbasis (n := n))
    (hpower :
      ∀ (e : HEFam H) (t : ℕ),
        1 ≤ t →
          CollectedPolynomialData (n := n) H e t)
    (hproduct :
      ∀ e : List (HEFam H),
        CollectedCoordinateData (n := n) H e)
    (hinverse :
      ∀ e : HEFam H,
        CollectedInverseData (n := n) H e) :
    zassenhausFiltration
        p (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n) n =
      hallCoordinateLattice (p := p) hn H hH hproduct hinverse := by
  let N : Type u := LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n
  apply le_antisymm
  · apply filtration_generator_set
    rintro y ⟨i, a, x, hx, hlevel, rfl⟩
    intro s hs hsn j
    exact
      least_weighted_exponent
        (r := i + 1) (s := s)
        hn H hH hpower x (by simpa using hx) (by omega) hs hsn a
        (by simpa using hlevel) j
  · intro y hy
    change HallCoordinateLattice (p := p) hn H hH y at hy
    rw [← collected_form_coordinates hn H hH y]
    unfold collectedHallProduct collectedPrefixProduct
    apply Subgroup.list_prod_mem
    intro x hx
    rcases List.mem_map.mp hx with ⟨j, hj, rfl⟩
    have hjlt : j + 1 < n := by
      have hjRange : j < n - 1 := List.mem_range.mp hj
      omega
    exact
      (H (j + 1)).collectedweight_productmem_zassfiltdvd
        (p := p) (by omega)
        (normalFormCoordinates hn H hH y (j + 1))
        (hy (j + 1) (by omega) hjlt)

/--
Replace the repeated atom labels of a commutator word by fresh slots, one for
each leaf.  Claim 11 varies one occurrence of one free generator, so its word
map needs occurrence-level rather than generator-level arguments.
-/
def CWord.freshen
  {α : Type*} :
    (w : CWord α) →
      CWord (Fin (w.weight fun _ => 1))
  | .atom _ => .atom ⟨0, by simp [CWord.weight]⟩
  | .commutator u v =>
      CWord.finAppend (CWord.freshen u) (CWord.freshen v)

/--
Fill the freshly indexed leaves with the values carried by the original atom
labels.
-/
def CWord.freshArguments
    {α G : Type*}
    (f : α → G) :
    (w : CWord α) →
      Fin (w.weight fun _ => 1) → G
  | .atom a => fun _ => f a
  | .commutator u v =>
      Fin.addCases (CWord.freshArguments f u) (CWord.freshArguments f v)

/--
Fill fresh leaves as usual except for the leftmost occurrence, which is
replaced by its integral power.
-/
def CWord.fresh_argumenleftmos_zpow
    {α G : Type*} [Group G]
    (f : α → G)
    (m : ℤ) :
    (w : CWord α) →
      Fin (w.weight fun _ => 1) → G
  | .atom a => fun _ => f a ^ m
  | .commutator u v =>
      Fin.addCases
        (CWord.fresh_argumenleftmos_zpow f m u)
        (CWord.freshArguments f v)

@[simp]
lemma CWord.freshen_weight
    {α : Type*}
    (w : CWord α) :
    (CWord.freshen w).weight (fun _ => 1) = w.weight (fun _ => 1) := by
  induction w with
  | atom =>
      rfl
  | commutator u v ihu ihv =>
      simp [CWord.freshen, ihu, ihv]

@[simp]
lemma CWord.freshen_eval_fresharguments
    {α G : Type*} [Group G]
    (f : α → G)
    (w : CWord α) :
    (CWord.freshen w).eval (CWord.freshArguments f w) = w.eval f := by
  induction w with
  | atom =>
      rfl
  | commutator u v ihu ihv =>
      simp [CWord.freshen, CWord.freshArguments, ihu, ihv]

/--
If two left commutator inputs agree modulo `γ_(i+1)`, then commutating them
with an element of `γ_(j+1)` gives values agreeing modulo `γ_(i+j+2)`.
-/
lemma congr_inv_series
    {G : Type u} [Group G]
    {i j : ℕ}
    {x y z : G}
    (hxy : x * y⁻¹ ∈ Subgroup.lowerCentralSeries G i)
    (hz : z ∈ Subgroup.lowerCentralSeries G j) :
    ⁅x, z⁆ * ⁅y, z⁆⁻¹ ∈ Subgroup.lowerCentralSeries G (i + j + 1) := by
  let L : Subgroup G := Subgroup.lowerCentralSeries G (i + j + 1)
  let q : G →* G ⧸ L := QuotientGroup.mk' L
  let k : G := x * y⁻¹
  have hkz :
      ⁅k, z⁆ ∈ L := by
    simpa [L, k] using
      element_lower_series hxy hz
  have hyz :
      ⁅y, z⁆ ∈ Subgroup.lowerCentralSeries G (j + 1) := by
    simpa using
      element_lower_series
        (i := 0) (j := j) (x := y) (y := z) (by simp) hz
  have hkyz :
      ⁅k, ⁅y, z⁆⁆ ∈ L := by
    have hmem :
        ⁅k, ⁅y, z⁆⁆ ∈ Subgroup.lowerCentralSeries G (i + (j + 1) + 1) :=
      element_lower_series hxy hyz
    exact Subgroup.lowerCentralSeries_antitone (by omega) hmem
  have hkzComm : Commute (q k) (q z) := by
    rw [← commutatorElement_eq_one_iff_commute, ← map_commutatorElement]
    exact (QuotientGroup.eq_one_iff ⁅k, z⁆).mpr hkz
  have hkyzComm : Commute (q k) ⁅q y, q z⁆ := by
    rw [← commutatorElement_eq_one_iff_commute, ← map_commutatorElement,
      ← map_commutatorElement]
    exact (QuotientGroup.eq_one_iff ⁅k, ⁅y, z⁆⁆).mpr hkyz
  have hx : q x = q k * q y := by
    simp [q, k]
  rw [mul_inv_quotient L]
  calc
    q ⁅x, z⁆ = ⁅q x, q z⁆ := by rw [map_commutatorElement]
    _ = ⁅q k * q y, q z⁆ := by rw [hx]
    _ = q k * ⁅q y, q z⁆ * (q k)⁻¹ * ⁅q k, q z⁆ := by
      rw [element_mul_left]
    _ = ⁅q y, q z⁆ := by
      rw [commutatorElement_eq_one_iff_commute.mpr hkzComm, mul_one,
        hkyzComm.eq, mul_inv_cancel_right]
    _ = q ⁅y, z⁆ := by rw [map_commutatorElement]

/--
If `x` commutes with `[x,y]`, integral powers in the left input pull out of
the commutator.
-/
lemma commutator_zpow_commute
    {G : Type*} [Group G]
    {x y : G}
    (hcomm : Commute x ⁅x, y⁆) :
    ∀ m : ℤ, ⁅x ^ m, y⁆ = ⁅x, y⁆ ^ m
  | .ofNat m => by
      simpa only [Int.ofNat_eq_natCast, zpow_natCast] using
        element_left_commute hcomm m
  | .negSucc m => by
      have hinv :
          ⁅x⁻¹, y⁆ = ⁅x, y⁆⁻¹ := by
        calc
          ⁅x⁻¹, y⁆ = x⁻¹ * ⁅x, y⁆⁻¹ * x := by
            simp only [commutatorElement_def, inv_inv, mul_inv_rev]
            group
          _ = ⁅x, y⁆⁻¹ := by
            rw [(hcomm.inv_left.inv_right).eq]
            simp
      have hcommInv :
          Commute x⁻¹ ⁅x⁻¹, y⁆ := by
        rw [hinv]
        exact hcomm.inv_left.inv_right
      simpa only [zpow_negSucc, ← inv_pow, hinv] using
        element_left_commute hcommInv (m + 1)

/--
The class-two collection error for an integral power in the left commutator
input belongs to the next relevant lower-central term.
-/
lemma inv_zpow_series
    {G : Type*} [Group G]
    {i j : ℕ}
    {x y : G}
    (hx : x ∈ Subgroup.lowerCentralSeries G i)
    (hy : y ∈ Subgroup.lowerCentralSeries G j)
    (m : ℤ) :
    ⁅x ^ m, y⁆ * (⁅x, y⁆ ^ m)⁻¹ ∈
      Subgroup.lowerCentralSeries G (2 * i + j + 2) := by
  let K : Subgroup G := Subgroup.lowerCentralSeries G (2 * i + j + 2)
  let q : G →* G ⧸ K := QuotientGroup.mk' K
  have hxy :
      ⁅x, y⁆ ∈ Subgroup.lowerCentralSeries G (i + j + 1) :=
    element_lower_series hx hy
  have hnested :
      ⁅x, ⁅x, y⁆⁆ ∈ K := by
    have hmem :
        ⁅x, ⁅x, y⁆⁆ ∈
          Subgroup.lowerCentralSeries G (i + (i + j + 1) + 1) :=
      element_lower_series hx hxy
    simpa [K, two_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hmem
  have hcomm :
      Commute (q x) ⁅q x, q y⁆ := by
    rw [← commutatorElement_eq_one_iff_commute, ← map_commutatorElement,
      ← map_commutatorElement]
    exact (QuotientGroup.eq_one_iff ⁅x, ⁅x, y⁆⁆).mpr hnested
  rw [mul_inv_quotient K]
  simpa only [map_commutatorElement, map_zpow] using
    commutator_zpow_commute hcomm m

/--
Scaling the leftmost fresh leaf of a commutator word by `m` scales its leading
lower-central class by `m`; all errors move to the next lower-central term.
-/
lemma CWord.freevafrearg_lezpomuzp_inmelocese
    {α G : Type*} [Group G]
    (f : α → G) :
    ∀ (w : CWord α) (m : ℤ),
      (CWord.freshen w).eval
            (CWord.fresh_argumenleftmos_zpow f m w) *
          (w.eval f ^ m)⁻¹ ∈
        Subgroup.lowerCentralSeries G (w.weight fun _ => 1)
  | .atom _, m => by
      simp [CWord.freshen, CWord.fresh_argumenleftmos_zpow]
  | .commutator u v, m => by
      let wu : ℕ := u.weight fun _ => 1
      let wv : ℕ := v.weight fun _ => 1
      have hwu : 0 < wu :=
        CWord.weight_pos (fun _ => 1) (fun _ => by simp) u
      have hwv : 0 < wv :=
        CWord.weight_pos (fun _ => 1) (fun _ => by simp) v
      have hu :
          (CWord.freshen u).eval
                (CWord.fresh_argumenleftmos_zpow f m u) *
              (u.eval f ^ m)⁻¹ ∈ Subgroup.lowerCentralSeries G wu := by
        simpa [wu] using
          CWord.freevafrearg_lezpomuzp_inmelocese
            f u m
      have hv :
          v.eval f ∈ Subgroup.lowerCentralSeries G (wv - 1) := by
        simpa [wv] using
          (CWord.eval_lower_series
            f (fun _ => 1) (fun _ => by simp) (fun _ => by simp) v)
      have hcongr :
          ⁅(CWord.freshen u).eval
              (CWord.fresh_argumenleftmos_zpow f m u), v.eval f⁆ *
              ⁅u.eval f ^ m, v.eval f⁆⁻¹ ∈
            Subgroup.lowerCentralSeries G (wu + wv) := by
        have hindex : wu + (wv - 1) + 1 = wu + wv := by omega
        simpa only [hindex] using
          congr_inv_series hu hv
      have huMem :
          u.eval f ∈ Subgroup.lowerCentralSeries G (wu - 1) := by
        simpa [wu] using
          (CWord.eval_lower_series
            f (fun _ => 1) (fun _ => by simp) (fun _ => by simp) u)
      have hpowerRaw :
          ⁅u.eval f ^ m, v.eval f⁆ * (⁅u.eval f, v.eval f⁆ ^ m)⁻¹ ∈
            Subgroup.lowerCentralSeries G (2 * (wu - 1) + (wv - 1) + 2) :=
        inv_zpow_series
          huMem hv m
      have hpower :
          ⁅u.eval f ^ m, v.eval f⁆ * (⁅u.eval f, v.eval f⁆ ^ m)⁻¹ ∈
            Subgroup.lowerCentralSeries G (wu + wv) :=
        Subgroup.lowerCentralSeries_antitone (by omega) hpowerRaw
      simpa [CWord.freshen, CWord.fresh_argumenleftmos_zpow,
        CWord.freshArguments] using
          mul_inv_trans (Subgroup.lowerCentralSeries G (wu + wv)) hcongr hpower

/--
Read one fixed-weight Hall coordinate family from an element of `γ_r` once a
collected weight-`r` segment has been identified modulo `γ_(r+1)`.
-/
lemma form_coordinates_next
    {d n r : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    (hr : 1 ≤ r)
    (hrn : r < n)
    (y : LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
    (hy :
      y ∈ Subgroup.lowerCentralSeries
        (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n) (r - 1))
    (e : (H r).index → ℤ)
    (he :
      ((H r).collectedWeightProduct (n := n) e)⁻¹ * y ∈
        Subgroup.lowerCentralSeries
          (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n) r) :
    normalFormCoordinates hn H hH y r = e := by
  let c : HEFam H := normalFormCoordinates hn H hH y
  have hcProduct : collectedHallProduct (n := n) H c = y :=
    collected_form_coordinates hn H hH y
  have hcBelow :
      ∀ s : ℕ,
        1 ≤ s →
          s < r →
            s < n →
              c s = 0 :=
    imp_coordinates_below
      hn H hH c (by simpa [hcProduct] using hy)
  have hprefix :
      collectedPrefixProduct (n := n) H c (r - 1) = 1 :=
    collected_prefix_coordinates
      H c (r - 1) (fun s hs hsr => hcBelow s hs (by omega) (by omega))
  let segment :
      LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n :=
    (H r).collectedWeightProduct (n := n) (c r)
  let tail :
      LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n :=
    collectedTailProduct (n := n) H c r
  have hrPred : r - 1 + 1 = r := Nat.sub_add_cancel hr
  have hprefixR :
      collectedPrefixProduct (n := n) H c r = segment := by
    rw [← hrPred, collected_prefix_succ, hprefix, one_mul]
    rw [hrPred]
  have hsegmentTail : segment * tail = y := by
    calc
      segment * tail =
          collectedPrefixProduct (n := n) H c r * tail := by
            rw [hprefixR]
      _ = collectedHallProduct (n := n) H c :=
        collected_prefix_tail
          H c r (by omega)
      _ = y := hcProduct
  have htail :
      tail ∈ Subgroup.lowerCentralSeries
        (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n) r :=
    collected_tail_series H c r
  have hsegmentInvMul :
      ((H r).collectedWeightProduct (n := n) e)⁻¹ * segment ∈
        Subgroup.lowerCentralSeries
          (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n) r := by
    have heq :
        ((H r).collectedWeightProduct (n := n) e)⁻¹ * segment =
          (((H r).collectedWeightProduct (n := n) e)⁻¹ * y) * tail⁻¹ := by
      rw [← hsegmentTail]
      group
    rw [heq]
    exact
      (Subgroup.lowerCentralSeries
        (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n) r).mul_mem
        he
        ((Subgroup.lowerCentralSeries
          (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n) r).inv_mem
          htail)
  exact
    (H r).collweigprod_coordseqinv_mulmemnext
      (hH r hr hrn) (c r) e (by simpa [segment] using hsegmentInvMul)

/--
TeX Claim 11: freshening the leaves of one Hall word and replacing its
leftmost leaf by an integral power creates exactly the prescribed leading
Hall coordinate.  Lower-weight coordinates vanish, the selected weight-`r`
coordinate is `m`, and every other coordinate of weight `r` is zero.
-/
theorem BCWta.exists_evalp_leadh
    {d n r : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    (hr : 1 ≤ r)
    (hrn : r < n)
    (i : (H r).index)
    (m : ℤ) :
    ∃ a : Fin (((H r).commutator i).word.weight (fun _ => 1)) →
        LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n,
      let y := (CWord.freshen ((H r).commutator i).word).eval a
      (∀ s : ℕ,
        1 ≤ s →
          s < r →
            s < n →
              ∀ j : (H s).index,
                hallCoordinate hn H hH y j = 0) ∧
        ∀ j : (H r).index,
          hallCoordinate hn H hH y j = if j = i then m else 0 := by
  let h := (H r).commutator i
  let f := freeTruncationValue d n
  let a := CWord.fresh_argumenleftmos_zpow f m h.word
  let y := (CWord.freshen h.word).eval a
  refine ⟨a, ?_, ?_⟩
  · intro s hs hsr hsn j
    exact
      lower_central_series
        hn H hH y
        (by
          simpa [y, a, h.word_weight] using
            (CWord.eval_lower_series
              a (fun _ => 1) (fun _ => by simp) (fun _ => by simp)
              (CWord.freshen h.word)))
        hs hsr hsn j
  · let e : (H r).index → ℤ := fun j => if j = i then m else 0
    have hy :
        y ∈ Subgroup.lowerCentralSeries
          (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n) (r - 1) := by
      simpa [y, a, h.word_weight] using
        (CWord.eval_lower_series
          a (fun _ => 1) (fun _ => by simp) (fun _ => by simp)
          (CWord.freshen h.word))
    let N : Type u := LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n
    let A : Subgroup N := Subgroup.lowerCentralSeries N (r - 1)
    let B : Subgroup A := (Subgroup.lowerCentralSeries N r).subgroupOf A
    let q : A →* A ⧸ B := QuotientGroup.mk' B
    let yTerm : A := ⟨y, hy⟩
    let hTerm : A :=
      ⟨h.freeLowerTruncation (n := n),
        h.free_truncation_series⟩
    have hscaled :
        y * (h.freeLowerTruncation (n := n) ^ m)⁻¹ ∈
          Subgroup.lowerCentralSeries N r := by
      simpa [y, a, h, f, h.word_weight] using
        CWord.freevafrearg_lezpomuzp_inmelocese
          f h.word m
    have hyClass : q yTerm = q (hTerm ^ m) := by
      apply (mul_inv_quotient B).mp
      exact hscaled
    have hsegmentClass :
        q ((H r).collected_lower_centralterm (n := n) e) = q (hTerm ^ m) := by
      rw [(H r).collectedlower_centtermclas_eqmulsum (n := n) e]
      have hsum :
          (∑ j,
              e j • ((H r).commutator j).associatedGradedClass (n := n)) =
            m • h.associatedGradedClass (n := n) := by
        classical
        simp [e, h]
      rw [hsum]
      change Additive.toMul (m • Additive.ofMul (q hTerm)) = q (hTerm ^ m)
      rw [map_zpow]
      rfl
    have hsegmentInvY :
        ((H r).collectedWeightProduct (n := n) e)⁻¹ * y ∈
          Subgroup.lowerCentralSeries N r := by
      apply (QuotientGroup.eq_one_iff
        (N := B)
        (((H r).collected_lower_centralterm (n := n) e)⁻¹ * yTerm)).mp
      change
        q (((H r).collected_lower_centralterm (n := n) e)⁻¹ * yTerm) = 1
      rw [map_mul, map_inv, hsegmentClass, hyClass, inv_mul_cancel]
    have hcoordinates :
        normalFormCoordinates hn H hH y r = e :=
      form_coordinates_next
        hn H hH hr hrn y hy e hsegmentInvY
    intro j
    change normalFormCoordinates hn H hH y r j = if j = i then m else 0
    rw [hcoordinates]

/--
Taking a natural power multiplies the Hall coordinates in the first
nonvanishing lower-central layer by that power.
-/
lemma form_coordinates_series
    {d n r : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    (hr : 1 ≤ r)
    (hrn : r < n)
    (y : LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
    (hy :
      y ∈ Subgroup.lowerCentralSeries
        (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n) (r - 1))
    (q : ℕ) :
    normalFormCoordinates hn H hH (y ^ q) r =
      fun i => (q : ℤ) * normalFormCoordinates hn H hH y r i := by
  obtain ⟨e, he⟩ :=
    (H r).existscollected_weigprodinv_mulmemnext (hH r hr hrn) hy
  have hcoordinates :
      normalFormCoordinates hn H hH y r = e :=
    form_coordinates_next
      hn H hH hr hrn y hy e he
  let eq : (H r).index → ℤ := fun i => (q : ℤ) * e i
  let N : Type u := LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n
  let A : Subgroup N := Subgroup.lowerCentralSeries N (r - 1)
  let B : Subgroup A := (Subgroup.lowerCentralSeries N r).subgroupOf A
  let quotientMap : A →* A ⧸ B := QuotientGroup.mk' B
  let yTerm : A := ⟨y, hy⟩
  let eTerm : A := (H r).collected_lower_centralterm (n := n) e
  let eqTerm : A := (H r).collected_lower_centralterm (n := n) eq
  have heClass : quotientMap eTerm = quotientMap yTerm := by
    have hone :
        quotientMap (eTerm⁻¹ * yTerm) = 1 :=
      (QuotientGroup.eq_one_iff (N := B) (eTerm⁻¹ * yTerm)).mpr he
    rw [map_mul, map_inv] at hone
    exact inv_mul_eq_one.mp hone
  have heqClass : quotientMap eqTerm = quotientMap (eTerm ^ q) := by
    rw [(H r).collectedlower_centtermclas_eqmulsum (n := n) eq,
      map_pow,
      (H r).collectedlower_centtermclas_eqmulsum (n := n) e]
    have hsum :
        (∑ i, eq i • ((H r).commutator i).associatedGradedClass (n := n)) =
          (q : ℤ) •
            ∑ i, e i • ((H r).commutator i).associatedGradedClass (n := n) := by
      rw [Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro i _hi
      simp [eq, mul_smul]
    rw [hsum]
    change
      Additive.toMul
          ((q : ℤ) •
            ∑ i, e i • ((H r).commutator i).associatedGradedClass (n := n)) =
        Additive.toMul
            (∑ i, e i • ((H r).commutator i).associatedGradedClass (n := n)) ^ q
    rw [toMul_zsmul, zpow_natCast]
  have heqYClass : quotientMap eqTerm = quotientMap (yTerm ^ q) := by
    rw [heqClass, map_pow, heClass, ← map_pow]
  have heqY :
      ((H r).collectedWeightProduct (n := n) eq)⁻¹ * y ^ q ∈
        Subgroup.lowerCentralSeries N r := by
    apply (QuotientGroup.eq_one_iff (N := B) (eqTerm⁻¹ * yTerm ^ q)).mp
    change quotientMap (eqTerm⁻¹ * yTerm ^ q) = 1
    rw [map_mul, map_inv, heqYClass, inv_mul_cancel]
  have hpowCoordinates :
      normalFormCoordinates hn H hH (y ^ q) r = eq :=
    form_coordinates_next
      hn H hH hr hrn (y ^ q)
        ((Subgroup.lowerCentralSeries N (r - 1)).pow_mem hy q)
        eq heqY
  rw [hpowCoordinates, hcoordinates]

/--
The admissible powered freshened Hall word used in TeX Claim 12.
-/
noncomputable def BCWt.freshenleast_weightprime_powerscheme
    {p d n r : ℕ}
    [Fact p.Prime]
    (h : BCWt.{u} d r)
    (hr : 1 ≤ r) :
    ZWScheme p n where
  arity := h.word.weight fun _ => 1
  word := CWord.freshen h.word
  frobenius := leastWeightedExponent p n r
  level_bound := by
    rw [CWord.freshen_weight, h.word_weight]
    exact mul_least_exponent p n r hr

/--
TeX Claim 12: powering the Claim 11 Hall-word value by the least admissible
prime power creates its prescribed divisible leading coordinate.  The value
is an evaluation of an admissible Zassenhaus word scheme, so it lies in the
requested Zassenhaus filtration term.
-/
theorem BCWta.existsfreshen_primepower_evalprescoor
    {p d n r : ℕ}
    [Fact p.Prime]
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    (hr : 1 ≤ r)
    (hrn : r < n)
    (i : (H r).index)
    (m : ℤ) :
    ∃ a : Fin (((H r).commutator i).word.weight (fun _ => 1)) →
        LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n,
      let S :=
        ((H r).commutator i).freshenleast_weightprime_powerscheme
          (p := p) (n := n) hr
      let y := S.eval a
      (∀ s : ℕ,
        1 ≤ s →
          s < r →
            s < n →
              ∀ j : (H s).index,
                hallCoordinate hn H hH y j = 0) ∧
        (∀ j : (H r).index,
          hallCoordinate hn H hH y j =
            if j = i then
              ((p ^ leastWeightedExponent p n r : ℕ) : ℤ) * m
            else 0) ∧
        y ∈ zassenhausFiltration
          p (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n) n := by
  obtain ⟨a, _haBelow, haWeight⟩ :=
    BCWta.exists_evalp_leadh
      hn H hH hr hrn i m
  let h := (H r).commutator i
  let u := (CWord.freshen h.word).eval a
  let S := h.freshenleast_weightprime_powerscheme (p := p) (n := n) hr
  let y := S.eval a
  have hu :
      u ∈ Subgroup.lowerCentralSeries
        (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n) (r - 1) := by
    simpa [u, h, h.word_weight] using
      (CWord.eval_lower_series
        a (fun _ => 1) (fun _ => by simp) (fun _ => by simp)
        (CWord.freshen h.word))
  have hy :
      y =
        u ^ (p ^ leastWeightedExponent p n r) := by
    rfl
  refine ⟨a, ?_, ?_, ?_⟩
  · intro s hs hsr hsn j
    change hallCoordinate hn H hH y j = 0
    rw [hy]
    exact
      lower_central_series
        hn H hH _ ((Subgroup.lowerCentralSeries
          (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n) (r - 1)).pow_mem
            hu _) hs hsr hsn j
  · intro j
    change
      hallCoordinate hn H hH y j =
        if j = i then
          ((p ^ leastWeightedExponent p n r : ℕ) : ℤ) * m
        else 0
    rw [hy]
    have hcoordinates :=
      congrFun
        (form_coordinates_series
          hn H hH hr hrn u hu
            (p ^ leastWeightedExponent p n r))
        j
    change
      normalFormCoordinates hn H hH
          (u ^ (p ^ leastWeightedExponent p n r)) r j =
        _
    have huWeight :
        normalFormCoordinates hn H hH u r j =
          if j = i then m else 0 := by
      simpa [hallCoordinate, u, h] using haWeight j
    rw [hcoordinates, huWeight]
    split_ifs <;> simp_all
  · exact S.eval_zassenhaus_filtration a

/--
Multiplication adds the full family of Hall coordinates in the first
nonvanishing lower-central layer.
-/
lemma normal_form_coordinates
    {d n r : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    (hr : 1 ≤ r)
    (hrn : r < n)
    (x y : LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
    (hx :
      x ∈ Subgroup.lowerCentralSeries
        (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n) (r - 1))
    (hy :
      y ∈ Subgroup.lowerCentralSeries
        (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n) (r - 1)) :
    normalFormCoordinates hn H hH (x * y) r =
      fun i =>
        normalFormCoordinates hn H hH x r i +
          normalFormCoordinates hn H hH y r i := by
  obtain ⟨ex, hex⟩ :=
    (H r).existscollected_weigprodinv_mulmemnext (hH r hr hrn) hx
  obtain ⟨ey, hey⟩ :=
    (H r).existscollected_weigprodinv_mulmemnext (hH r hr hrn) hy
  have hxCoordinates :
      normalFormCoordinates hn H hH x r = ex :=
    form_coordinates_next
      hn H hH hr hrn x hx ex hex
  have hyCoordinates :
      normalFormCoordinates hn H hH y r = ey :=
    form_coordinates_next
      hn H hH hr hrn y hy ey hey
  let exy : (H r).index → ℤ := fun i => ex i + ey i
  let N : Type u := LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n
  let A : Subgroup N := Subgroup.lowerCentralSeries N (r - 1)
  let B : Subgroup A := (Subgroup.lowerCentralSeries N r).subgroupOf A
  let quotientMap : A →* A ⧸ B := QuotientGroup.mk' B
  let xTerm : A := ⟨x, hx⟩
  let yTerm : A := ⟨y, hy⟩
  let exTerm : A := (H r).collected_lower_centralterm (n := n) ex
  let eyTerm : A := (H r).collected_lower_centralterm (n := n) ey
  let exyTerm : A := (H r).collected_lower_centralterm (n := n) exy
  have hexClass : quotientMap exTerm = quotientMap xTerm := by
    have hone :
        quotientMap (exTerm⁻¹ * xTerm) = 1 :=
      (QuotientGroup.eq_one_iff (N := B) (exTerm⁻¹ * xTerm)).mpr hex
    rw [map_mul, map_inv] at hone
    exact inv_mul_eq_one.mp hone
  have heyClass : quotientMap eyTerm = quotientMap yTerm := by
    have hone :
        quotientMap (eyTerm⁻¹ * yTerm) = 1 :=
      (QuotientGroup.eq_one_iff (N := B) (eyTerm⁻¹ * yTerm)).mpr hey
    rw [map_mul, map_inv] at hone
    exact inv_mul_eq_one.mp hone
  have hexyClass : quotientMap exyTerm = quotientMap (xTerm * yTerm) := by
    rw [(H r).collectedlower_centtermclas_eqmulsum (n := n) exy,
      map_mul, ← hexClass, ← heyClass,
      (H r).collectedlower_centtermclas_eqmulsum (n := n) ex,
      (H r).collectedlower_centtermclas_eqmulsum (n := n) ey]
    have hsum :
        (∑ i, exy i • ((H r).commutator i).associatedGradedClass (n := n)) =
          (∑ i, ex i • ((H r).commutator i).associatedGradedClass (n := n)) +
            ∑ i, ey i • ((H r).commutator i).associatedGradedClass (n := n) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _hi
      simp [exy, add_smul]
    rw [hsum]
    rfl
  have hexy :
      ((H r).collectedWeightProduct (n := n) exy)⁻¹ * (x * y) ∈
        Subgroup.lowerCentralSeries N r := by
    apply (QuotientGroup.eq_one_iff (N := B) (exyTerm⁻¹ * (xTerm * yTerm))).mp
    change quotientMap (exyTerm⁻¹ * (xTerm * yTerm)) = 1
    rw [map_mul, map_inv, hexyClass, inv_mul_cancel]
  have hxyCoordinates :
      normalFormCoordinates hn H hH (x * y) r = exy :=
    form_coordinates_next
      hn H hH hr hrn (x * y)
        ((Subgroup.lowerCentralSeries N (r - 1)).mul_mem hx hy)
        exy hexy
  rw [hxyCoordinates, hxCoordinates, hyCoordinates]

/--
TeX Claim 13: once lower Hall coordinates vanish, multiplication is
triangular.  In fact, membership in `γ_r` suffices to make every weight-`r`
Hall coordinate additive; no assumptions on earlier coordinates within the
same weight layer are needed.
-/
theorem coordinate_lower_series
    {d n r : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    (hr : 1 ≤ r)
    (hrn : r < n)
    (x y : LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
    (hx :
      x ∈ Subgroup.lowerCentralSeries
        (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n) (r - 1))
    (hy :
      y ∈ Subgroup.lowerCentralSeries
        (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n) (r - 1))
    (i : (H r).index) :
    hallCoordinate hn H hH (x * y) i =
      hallCoordinate hn H hH x i + hallCoordinate hn H hH y i := by
  exact congrFun
    (normal_form_coordinates
      hn H hH hr hrn x y hx hy)
    i

/--
The sum of a function over the sorted list of all elements of a finite linear
order is its ordinary `Fintype` sum.
-/
lemma list_sort_univ
    {M : Type*} [AddCommMonoid M]
    {ι : Type u} [Fintype ι] [LinearOrder ι]
    (f : ι → M) :
    ((Finset.univ.sort fun i j : ι => i ≤ j).map f).sum =
      ∑ i, f i := by
  rw [← List.sum_toFinset]
  · simp
  · exact Finset.sort_nodup _ _

/--
Claim 13 iterated over a list: if every factor starts in `γ_r`, the
weight-`r` coordinate of the product is the sum of the factor coordinates.
-/
lemma forall_lower_series
    {d n r : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    (hr : 1 ≤ r)
    (hrn : r < n)
    (L : List (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n))
    (hL :
      ∀ x ∈ L,
        x ∈ Subgroup.lowerCentralSeries
          (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n) (r - 1))
    (i : (H r).index) :
    hallCoordinate hn H hH L.prod i =
      (L.map fun x => hallCoordinate hn H hH x i).sum := by
  induction L with
  | nil =>
      simpa using coordinate_one_zero hn H hH hr hrn i
  | cons x L ih =>
      rw [List.prod_cons, List.map_cons, List.sum_cons,
        coordinate_lower_series
          hn H hH hr hrn x L.prod
          (hL x (by simp))
          (by
            apply Subgroup.list_prod_mem
            intro y hy
            exact hL y (by simp [hy])),
        ih (fun y hy => hL y (by simp [hy]))]

/--
Equal weight-`r` Hall coordinates for two elements of `γ_r` mean that their
quotient starts in `γ_(r+1)`.
-/
lemma inv_form_coordinates
    {d n r : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    (hr : 1 ≤ r)
    (hrn : r < n)
    (x y : LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
    (hx :
      x ∈ Subgroup.lowerCentralSeries
        (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n) (r - 1))
    (hy :
      y ∈ Subgroup.lowerCentralSeries
        (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n) (r - 1))
    (hcoordinates :
      normalFormCoordinates hn H hH x r =
        normalFormCoordinates hn H hH y r) :
    x⁻¹ * y ∈
      Subgroup.lowerCentralSeries
        (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n) r := by
  obtain ⟨e, he⟩ :=
    (H r).existscollected_weigprodinv_mulmemnext (hH r hr hrn) hx
  have hxCoordinates :
      normalFormCoordinates hn H hH x r = e :=
    form_coordinates_next
      hn H hH hr hrn x hx e he
  have hey :
      ((H r).collectedWeightProduct (n := n) e)⁻¹ * y ∈
        Subgroup.lowerCentralSeries
          (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n) r := by
    obtain ⟨f, hf⟩ :=
      (H r).existscollected_weigprodinv_mulmemnext (hH r hr hrn) hy
    have hyCoordinates :
        normalFormCoordinates hn H hH y r = f :=
      form_coordinates_next
        hn H hH hr hrn y hy f hf
    have hef : e = f := by
      rw [← hxCoordinates, hcoordinates, hyCoordinates]
    simpa [hef] using hf
  have hrewrite :
      x⁻¹ * y =
        (((H r).collectedWeightProduct (n := n) e)⁻¹ * x)⁻¹ *
          (((H r).collectedWeightProduct (n := n) e)⁻¹ * y) := by
    group
  rw [hrewrite]
  exact
    (Subgroup.lowerCentralSeries
      (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n) r).mul_mem
      ((Subgroup.lowerCentralSeries
        (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n) r).inv_mem he)
      hey

/--
The number of Hall commutator slots in the consecutive weights
`k + 1, ..., k + t`.
-/
def hallCommutatorCount
    {d : ℕ}
    (H : ∀ r : ℕ, BCWta.{u} d r) :
    ℕ → ℕ → ℕ
  | _, 0 => 0
  | k, t + 1 => Fintype.card (H (k + 1)).index +
      hallCommutatorCount H (k + 1) t

/--
The number of Hall commutator slots of ordinary weight strictly below `n`.
-/
def commutatorCountBelow
    {d : ℕ}
    (H : ∀ r : ℕ, BCWta.{u} d r)
    (n : ℕ) :
    ℕ :=
  hallCommutatorCount H 0 (n - 1)

/--
Absorb one complete weight-`r` Hall layer of a lattice element using one
admissible powered freshened Hall-word value for each weight-`r` basis slot.
The residual moves from `γ_r` into `γ_(r+1)`.
-/
theorem bounded_normalized_series
    {p d n r : ℕ}
    [Fact p.Prime]
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    (hpower :
      ∀ (e : HEFam H) (t : ℕ),
        1 ≤ t →
          CollectedPolynomialData (n := n) H e t)
    (hproduct :
      ∀ e : List (HEFam H),
        CollectedCoordinateData (n := n) H e)
    (hinverse :
      ∀ e : HEFam H,
        CollectedInverseData (n := n) H e)
    (hr : 1 ≤ r)
    (hrn : r < n)
    (y : LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
    (hyZassenhaus :
      y ∈ zassenhausFiltration
        p (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n) n)
    (hyLower :
      y ∈ Subgroup.lowerCentralSeries
        (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n) (r - 1)) :
    ∃ L : List
        (BSValue p d n
          (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)),
      L.length ≤ Fintype.card (H r).index ∧
        let z := (L.map BSValue.eval).prod⁻¹ * y
        z ∈ zassenhausFiltration
            p (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n) n ∧
          z ∈ Subgroup.lowerCentralSeries
            (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n) r := by
  let N : Type u := LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n
  have hyLattice :
      HallCoordinateLattice (p := p) hn H hH y := by
    change y ∈ hallCoordinateLattice (p := p) hn H hH hproduct hinverse
    rw [← zassenhaus_filtration_lattice
      hn H hH hpower hproduct hinverse]
    exact hyZassenhaus
  choose m hm using fun i : (H r).index => hyLattice r hr hrn i
  choose a _haBelow haWeight haZassenhaus using fun i : (H r).index =>
    BCWta.existsfreshen_primepower_evalprescoor
      (p := p) hn H hH hr hrn i (m i)
  let S : (H r).index → ZWScheme p n :=
    fun i =>
      ((H r).commutator i).freshenleast_weightprime_powerscheme
        (p := p) (n := n) hr
  choose z hz using fun i : (H r).index =>
    bounded_scheduled_scheme
      (p := p) (d := d) (by omega : 0 < n) (S i) (a i)
  let L :
      List
        (BSValue p d n
          (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)) :=
    (Finset.univ.sort fun i j : (H r).index => i ≤ j).map z
  let P : N := (L.map BSValue.eval).prod
  have hzLower :
      ∀ i : (H r).index,
        (z i).eval ∈ Subgroup.lowerCentralSeries N (r - 1) := by
    intro i
    rw [hz i]
    rw [ZWScheme.eval_def]
    apply (Subgroup.lowerCentralSeries N (r - 1)).pow_mem
    have hweight : (S i).word.weight (fun _ => 1) = r := by
      simp [S,
        BCWt.freshenleast_weightprime_powerscheme,
        ((H r).commutator i).word_weight]
    simpa [ZWScheme.lowerLevel, hweight] using
        (S i).word_lower_series (a i)
  have hzZassenhaus :
      ∀ i : (H r).index,
        (z i).eval ∈ zassenhausFiltration p N n := by
    intro i
    rw [hz i]
    exact haZassenhaus i
  have hPLower :
      P ∈ Subgroup.lowerCentralSeries N (r - 1) := by
    apply Subgroup.list_prod_mem
    intro x hx
    rcases List.mem_map.mp hx with ⟨zi, hzi, rfl⟩
    rcases List.mem_map.mp hzi with ⟨i, _hi, rfl⟩
    exact hzLower i
  have hPZassenhaus :
      P ∈ zassenhausFiltration p N n := by
    apply Subgroup.list_prod_mem
    intro x hx
    rcases List.mem_map.mp hx with ⟨zi, hzi, rfl⟩
    rcases List.mem_map.mp hzi with ⟨i, _hi, rfl⟩
    exact hzZassenhaus i
  have hzCoordinate :
      ∀ i j : (H r).index,
        hallCoordinate hn H hH (z i).eval j =
          if j = i then
            ((p ^ leastWeightedExponent p n r : ℕ) : ℤ) * m i
          else 0 := by
    intro i j
    rw [hz i]
    exact haWeight i j
  have hPCoordinates :
      normalFormCoordinates hn H hH P r =
        normalFormCoordinates hn H hH y r := by
    funext j
    change hallCoordinate hn H hH P j = hallCoordinate hn H hH y j
    rw [show P = (L.map BSValue.eval).prod by rfl,
      forall_lower_series
        hn H hH hr hrn
        (L.map BSValue.eval)
        (by
          intro x hx
          rcases List.mem_map.mp hx with ⟨zi, hzi, rfl⟩
          rcases List.mem_map.mp hzi with ⟨i, _hi, rfl⟩
          exact hzLower i)
        j]
    simp only [L, List.map_map]
    rw [list_sort_univ]
    simp only [Function.comp_apply, hzCoordinate]
    simp
    simpa [hallCoordinate] using (hm j).symm
  refine ⟨L, ?_, ?_, ?_⟩
  · simp [L]
  · exact
      (zassenhausFiltration p N n).mul_mem
        ((zassenhausFiltration p N n).inv_mem hPZassenhaus)
        hyZassenhaus
  · exact
      inv_form_coordinates
        hn H hH hr hrn P y hPLower hyLower hPCoordinates

/--
TeX Claim 14: every lattice element in the free nilpotent truncation is a
product of at most one admissible powered Hall-word value for each Hall
commutator of ordinary weight below `n`.
-/
theorem bounded_normalized_data
    {p d n : ℕ}
    [Fact p.Prime]
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    (hpower :
      ∀ (e : HEFam H) (t : ℕ),
        1 ≤ t →
          CollectedPolynomialData (n := n) H e t)
    (hproduct :
      ∀ e : List (HEFam H),
        CollectedCoordinateData (n := n) H e)
    (hinverse :
      ∀ e : HEFam H,
        CollectedInverseData (n := n) H e)
    (y : LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
    (hy :
      y ∈ zassenhausFiltration
        p (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n) n) :
    BNZass
      p d n (commutatorCountBelow H n) y := by
  let N : Type u := LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n
  have hcollect :
      ∀ t k : ℕ,
        k + t = n - 1 →
          ∀ z : N,
            z ∈ zassenhausFiltration p N n →
              z ∈ Subgroup.lowerCentralSeries N k →
                BNZass
                  p d n (hallCommutatorCount H k t) z := by
    intro t
    induction t with
    | zero =>
        intro k hk z _hzZassenhaus hzLower
        have hbot : Subgroup.lowerCentralSeries N (n - 1) = ⊥ := by
          simpa [N, LowerCentralTruncation] using
            (lower_last_bot
              (G := FreeGroup (FreeGenerator.{u} d)) (c := n))
        have hzOne : z = 1 := by
          apply eq_bot_iff.mp hbot
          have hk' : k = n - 1 := by omega
          simpa [hk'] using hzLower
        simpa [hallCommutatorCount, hzOne] using
          bounded_normalized_one p d n
    | succ t ih =>
        intro k hk z hzZassenhaus hzLower
        have hr : 1 ≤ k + 1 := by omega
        have hrn : k + 1 < n := by omega
        obtain ⟨L, hLlength, hLZassenhaus, hLLower⟩ :=
          bounded_normalized_series
            hn H hH hpower hproduct hinverse hr hrn z hzZassenhaus
              (by simpa using hzLower)
        let residual : N :=
          (L.map BSValue.eval).prod⁻¹ * z
        have hresidual :
            BNZass
              p d n (hallCommutatorCount H (k + 1) t) residual :=
          ih (k + 1) (by omega) residual
            (by simpa [residual] using hLZassenhaus)
            (by simpa [residual] using hLLower)
        rcases hresidual with ⟨R, hRlength, hRprod⟩
        refine ⟨L ++ R, ?_, ?_⟩
        · simpa [hallCommutatorCount, List.length_append] using
            Nat.add_le_add hLlength hRlength
        · rw [List.map_append, List.prod_append, hRprod]
          simp [residual]
  simpa [commutatorCountBelow] using
    hcollect (n - 1) 0 (by simp) y hy (by simp)

/--
TeX Lemmas 7-10 live entirely in the free nilpotent truncation before Lemma 11
transports the resulting bounded list to an arbitrary generated quotient.
-/
def TruncationCollectionBound
    (p d n k : ℕ) [Fact p.Prime] :
    Prop :=
  ∀ y : LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n,
    y ∈ zassenhausFiltration
        p (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n) n →
      BNZass p d n k y

/-- Hall-Petresco trace existence in the single universal free nilpotent
truncation used at depth `n`. -/
def FreeTruncationLaw
    (p d n : ℕ) [Fact p.Prime] :
    Prop :=
  ∀ (x y : LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
    (a b : ℕ),
    Nonempty (PPColl.Trace p x y a b)

/--
Package Claim 14 as the free-truncation collection bound consumed by the
quotient transport step.
-/
theorem free_truncation_data
    {p d n : ℕ}
    [Fact p.Prime]
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    (hpower :
      ∀ (e : HEFam H) (t : ℕ),
        1 ≤ t →
          CollectedPolynomialData (n := n) H e t)
    (hproduct :
      ∀ e : List (HEFam H),
        CollectedCoordinateData (n := n) H e)
    (hinverse :
      ∀ e : HEFam H,
        CollectedInverseData (n := n) H e) :
    TruncationCollectionBound.{u}
      p d n (commutatorCountBelow H n) := by
  intro y hy
  exact
    bounded_normalized_data
      hn H hH hpower hproduct hinverse y hy

/-- Constant functions are integer-valued polynomials of every degree bound. -/
lemma collection_n_const
    (c : ℤ)
    (degreeBound : ℕ) :
    IVMost (fun _ : ℕ => c) degreeBound := by
  refine ⟨Polynomial.C (c : ℚ), by simp, ?_⟩
  intro q
  simp

/-- Enlarge the recorded degree bound for an integer-valued polynomial. -/
lemma collection_n_mono
    {f : ℕ → ℤ}
    {degreeBound largerBound : ℕ}
    (hdegree : degreeBound ≤ largerBound)
    (hf : IVMost f degreeBound) :
    IVMost f largerBound := by
  rcases hf with ⟨P, hPdegree, hPeval⟩
  exact ⟨P, hPdegree.trans hdegree, hPeval⟩

/-- Sums of integer-valued polynomials with a common degree bound. -/
lemma collection_n_add
    {f g : ℕ → ℤ}
    {degreeBound : ℕ}
    (hf : IVMost f degreeBound)
    (hg : IVMost g degreeBound) :
    IVMost (f + g) degreeBound := by
  rcases hf with ⟨P, hPdegree, hPeval⟩
  rcases hg with ⟨Q, hQdegree, hQeval⟩
  refine ⟨P + Q, Polynomial.natDegree_add_le_of_degree_le hPdegree hQdegree, ?_⟩
  intro q
  simp [Polynomial.eval_add, hPeval q, hQeval q]

/-- Integer-valued polynomials are closed under integer scalar multiplication. -/
lemma collection_n_smul
    (c : ℤ)
    {f : ℕ → ℤ}
    {degreeBound : ℕ}
    (hf : IVMost f degreeBound) :
    IVMost (fun q : ℕ => c * f q) degreeBound := by
  rcases hf with ⟨P, hPdegree, hPeval⟩
  refine ⟨Polynomial.C (c : ℚ) * P, ?_, ?_⟩
  · exact Polynomial.natDegree_mul_le.trans
      (by
        calc
          (Polynomial.C (c : ℚ)).natDegree + P.natDegree ≤ 0 + degreeBound :=
            Nat.add_le_add (by simp) hPdegree
          _ = degreeBound := by simp)
  · intro q
    simp [Polynomial.eval_mul, hPeval q]

/-- Integer-valued polynomials are closed under multiplication. -/
lemma collection_n_mul
    {f g : ℕ → ℤ}
    {leftDegree rightDegree : ℕ}
    (hf : IVMost f leftDegree)
    (hg : IVMost g rightDegree) :
    IVMost
      (fun q : ℕ => f q * g q)
      (leftDegree + rightDegree) := by
  rcases hf with ⟨P, hPdegree, hPeval⟩
  rcases hg with ⟨Q, hQdegree, hQeval⟩
  refine ⟨P * Q, Polynomial.natDegree_mul_le.trans ?_, ?_⟩
  · exact Nat.add_le_add hPdegree hQdegree
  · intro q
    simp [Polynomial.eval_mul, hPeval q, hQeval q]

/-- Finite sums of integer-valued polynomials with a common degree bound. -/
lemma n_finset_sum
    {ι : Type}
    (S : Finset ι)
    (F : ι → ℕ → ℤ)
    {degreeBound : ℕ}
    (hF : ∀ i ∈ S, IVMost (F i) degreeBound) :
    IVMost
      (fun q : ℕ => ∑ i ∈ S, F i q)
      degreeBound := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      simpa using collection_n_const 0 degreeBound
  | insert a S ha ih =>
      have haF : IVMost (F a) degreeBound :=
        hF a (by simp)
      have hSF :
          IVMost
            (fun q : ℕ => ∑ i ∈ S, F i q)
            degreeBound :=
        ih (fun i hi => hF i (by simp [hi]))
      have hadd := collection_n_add haF hSF
      convert hadd using 1
      ext q
      simp [Finset.sum_insert, ha]

/-- Finite products of integer-valued polynomials, with additive degree bounds. -/
lemma n_finset_prod
    {ι : Type}
    (S : Finset ι)
    (F : ι → ℕ → ℤ)
    (degree : ι → ℕ)
    (hF : ∀ i ∈ S, IVMost (F i) (degree i)) :
    IVMost
      (fun q : ℕ => ∏ i ∈ S, F i q)
      (∑ i ∈ S, degree i) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      simpa using collection_n_const 1 0
  | insert a S ha ih =>
      have haF : IVMost (F a) (degree a) :=
        hF a (by simp)
      have hSF :
          IVMost
            (fun q : ℕ => ∏ i ∈ S, F i q)
            (∑ i ∈ S, degree i) :=
        ih (fun i hi => hF i (by simp [hi]))
      have hmul := collection_n_mul haF hSF
      simpa [Finset.prod_insert, Finset.sum_insert, ha] using hmul

/-- Generalized binomial coefficients of an integer-valued polynomial. -/
lemma collection_n_choose
    {f : ℕ → ℤ}
    {degreeBound : ℕ}
    (hf : IVMost f degreeBound)
    (k : ℕ) :
    IVMost
      (fun q : ℕ => Ring.choose (f q) k)
      (k * degreeBound) := by
  rcases hf with ⟨P, hPdegree, hPeval⟩
  refine ⟨(natChoosePolynomial k).comp P, ?_, ?_⟩
  · exact Polynomial.natDegree_comp_le.trans
      (Nat.mul_le_mul (degree_choose_polynomial k) hPdegree)
  · intro q
    rw [Polynomial.eval_comp, hPeval q]
    exact collection_choose_int (f q) k

lemma p_collection_div
    (k w r : ℕ)
    (hr : 0 < r) :
    k * (w / r) ≤ (k * w) / r := by
  rw [Nat.le_div_iff_mul_le hr]
  calc
    k * (w / r) * r = k * ((w / r) * r) := by rw [mul_assoc]
    _ ≤ k * w := Nat.mul_le_mul_left k (Nat.div_mul_le_self w r)

lemma collection_sum_div
    {ι : Type}
    (S : Finset ι)
    (F : ι → ℕ)
    (r : ℕ) :
    ∑ i ∈ S, F i / r ≤ (∑ i ∈ S, F i) / r := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      simp
  | insert a S ha ih =>
      calc
        ∑ i ∈ insert a S, F i / r =
            F a / r + ∑ i ∈ S, F i / r := by
              simp [Finset.sum_insert, ha]
        _ ≤ F a / r + (∑ i ∈ S, F i) / r :=
            Nat.add_le_add_left ih _
        _ ≤ (F a + ∑ i ∈ S, F i) / r :=
            Nat.add_div_le_add_div (F a) (∑ i ∈ S, F i) r
        _ = (∑ i ∈ insert a S, F i) / r := by
            simp [Finset.sum_insert, ha]

/-- The shifted Newton-binomial expansion for partial sums. -/
noncomputable def collection_partial_polynomial
    (f : ℕ → ℤ)
    (degreeBound : ℕ) :
    Polynomial ℚ :=
  ∑ k ∈ Finset.range (degreeBound + 1),
    Polynomial.C (natBinomialCoefficient f k : ℚ) *
      natChoosePolynomial (k + 1)

lemma collection_nat_partial
    (f : ℕ → ℤ)
    (degreeBound : ℕ) :
    (collection_partial_polynomial f degreeBound).natDegree ≤
      degreeBound + 1 := by
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro k hk
  have hkdegree : k + 1 ≤ degreeBound + 1 :=
    Nat.succ_le_succ (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))
  calc
    (Polynomial.C (natBinomialCoefficient f k : ℚ) *
        natChoosePolynomial (k + 1)).natDegree ≤
        (Polynomial.C (natBinomialCoefficient f k : ℚ)).natDegree +
          (natChoosePolynomial (k + 1)).natDegree :=
      Polynomial.natDegree_mul_le
    _ ≤ 0 + (k + 1) := by
      gcongr
      · simp
      · exact degree_choose_polynomial (k + 1)
    _ ≤ degreeBound + 1 := by simpa using hkdegree

lemma collection_range_choose
    (steps k : ℕ) :
    ∑ j ∈ Finset.range steps, j.choose k =
      steps.choose (k + 1) := by
  induction steps with
  | zero =>
      simp
  | succ steps ih =>
      rw [Finset.sum_range_succ, ih, Nat.choose_succ_succ']
      simp [Nat.add_comm]

lemma range_choose_int
    (steps k : ℕ) :
    ∑ j ∈ Finset.range steps, (j.choose k : ℤ) =
      (steps.choose (k + 1) : ℤ) := by
  exact_mod_cast collection_range_choose steps k

lemma p_collection_partial
    {f : ℕ → ℤ}
    {degreeBound : ℕ}
    (hf : IVMost f degreeBound)
    (steps : ℕ) :
    (collection_partial_polynomial f degreeBound).eval (steps : ℚ) =
      ((∑ j ∈ Finset.range steps, f j : ℤ) : ℚ) := by
  rw [collection_partial_polynomial, Polynomial.eval_finsetSum]
  simp_rw [Polynomial.eval_C_mul, eval_nat_choose]
  norm_cast
  calc
    ∑ k ∈ Finset.range (degreeBound + 1),
        natBinomialCoefficient f k * (steps.choose (k + 1) : ℤ) =
        ∑ k ∈ Finset.range (degreeBound + 1),
          natBinomialCoefficient f k *
            (∑ j ∈ Finset.range steps, (j.choose k : ℤ)) := by
      apply Finset.sum_congr rfl
      intro k _hk
      rw [range_choose_int]
    _ = ∑ j ∈ Finset.range steps,
          ∑ k ∈ Finset.range (degreeBound + 1),
            natBinomialCoefficient f k * (j.choose k : ℤ) := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
    _ = ∑ j ∈ Finset.range steps, f j := by
      apply Finset.sum_congr rfl
      intro j _hj
      exact (hf.nat_binomial_basisexpansion j).symm

/-- Partial sums raise the degree bound by one. -/
lemma n_partial_sum
    {f : ℕ → ℤ}
    {degreeBound : ℕ}
    (hf : IVMost f degreeBound) :
    IVMost
      (fun steps : ℕ => ∑ j ∈ Finset.range steps, f j)
      (degreeBound + 1) :=
  ⟨collection_partial_polynomial f degreeBound,
    collection_nat_partial f degreeBound,
    p_collection_partial hf⟩

/-- The collected Hall product of the zero coordinate family is trivial. -/
lemma collection_collected_zero
    {d n : ℕ}
    (H : ∀ r : ℕ, BCWta.{u} d r) :
    collectedHallProduct (n := n) H (0 : HEFam H) = 1 := by
  simp [collectedHallProduct, collectedPrefixProduct,
    BCWta.collected_weight_productzero]

/--
Coordinates of one Hall exponent family below a target weight are expressed in
the weighted-binomial language attached to an ambient input family.
-/
def CoordinatesBinomialCombinations
    {d n : ℕ}
    (H : ∀ r : ℕ, BCWta.{u} d r)
    {ι : Type}
    (input : ι → HEFam H)
    (e : HEFam H)
    (s : ℕ) :
    Prop :=
  ∀ t : ℕ,
    1 ≤ t →
      t < s →
        t < n →
          ∀ i : (H t).index,
            ICMonomi H t input (e t i)

lemma BCMono.eval_power_n
    {d n r s : ℕ}
    {H : ∀ t : ℕ, BCWta.{u} d t}
    (m : BCMono H s)
    (A : ℕ → HEFam H)
    (e : HEFam H)
    (hr : 1 ≤ r)
    (hrs : r ≤ s)
    (hsn : s < n)
    (heBelow : ∀ t : ℕ, 1 ≤ t → t < r → t < n → e t = 0)
    (hABelow : ∀ q t : ℕ, 1 ≤ t → t < r → t < n → A q t = 0)
    (hpolyBelow :
      ∀ t : ℕ,
        1 ≤ t →
          t < s →
            t < n →
              ∀ i : (H t).index,
                IVMost (fun q : ℕ => A q t i) (t / r)) :
    IVMost
      (fun q : ℕ => m.eval (A q) e)
      (s / r - 1) := by
  classical
  let factorWeight : Fin m.length → ℕ :=
    fun ν => m.binomialIndex ν * (m.address ν).1
  have haddress_le_s : ∀ ν : Fin m.length, (m.address ν).1 ≤ s := by
    intro ν
    have hfactor_le_s : factorWeight ν ≤ s := by
      exact
        (Finset.single_le_sum
          (fun μ _ => Nat.zero_le (factorWeight μ))
          (by simp : ν ∈ (Finset.univ : Finset (Fin m.length)))).trans
          m.weightedWeight_le
    have hweight_le_factor : (m.address ν).1 ≤ factorWeight ν := by
      calc
        (m.address ν).1 = 1 * (m.address ν).1 := by simp
        _ ≤ m.binomialIndex ν * (m.address ν).1 := by
          exact Nat.mul_le_mul_right _ (m.binomialIndex_pos ν)
    exact hweight_le_factor.trans hfactor_le_s
  have haddress_lt_n : ∀ ν : Fin m.length, (m.address ν).1 < n := by
    intro ν
    exact lt_of_le_of_lt (haddress_le_s ν) hsn
  by_cases hrightSmall :
      ∃ ν : Fin m.length, m.side ν = 1 ∧ (m.address ν).1 < r
  · rcases hrightSmall with ⟨ν, hνside, hνr⟩
    have hzero : ∀ q : ℕ, m.eval (A q) e = 0 := by
      intro q
      dsimp [BCMono.eval]
      apply Finset.prod_eq_zero (i := ν)
      · simp
      · have hνpos : 1 ≤ (m.address ν).1 :=
          Nat.succ_le_iff.mpr (m.commutatorWeight_pos ν)
        have hνe := heBelow (m.address ν).1 hνpos hνr (haddress_lt_n ν)
        simp [hνside, hνe, Ring.choose_zero_pos ℤ (m.binomialIndex_pos ν)]
    convert collection_n_const 0 (s / r - 1) using 1
    ext q
    exact hzero q
  · have hrightLarge :
        ∀ ν : Fin m.length,
          m.side ν = 1 →
            r ≤ (m.address ν).1 := by
      intro ν hνside
      by_contra hνr
      exact hrightSmall ⟨ν, hνside, Nat.lt_of_not_ge hνr⟩
    let factorDegree : Fin m.length → ℕ :=
      fun ν =>
        if m.side ν = 0 then
          m.binomialIndex ν * ((m.address ν).1 / r)
        else
          0
    let factorFunction : Fin m.length → ℕ → ℤ :=
      fun ν q =>
        Ring.choose
          ((if m.side ν = 0 then A q else e)
            (m.address ν).1 (m.address ν).2)
          (m.binomialIndex ν)
    have hleft_address_lt_s :
        ∀ ν : Fin m.length,
          m.side ν = 0 →
            (m.address ν).1 < s := by
      intro ν hνleft
      rcases m.has_right with ⟨μ, hμright⟩
      have hμν : μ ≠ ν := by
        intro h
        subst μ
        rw [hνleft] at hμright
        norm_num at hμright
      have hfactor_lt_sum : factorWeight ν < ∑ μ, factorWeight μ := by
        exact
          Finset.single_lt_sum hμν
            (by simp : ν ∈ (Finset.univ : Finset (Fin m.length)))
            (by simp : μ ∈ (Finset.univ : Finset (Fin m.length)))
            (Nat.mul_pos (m.binomialIndex_pos μ) (m.commutatorWeight_pos μ))
            (fun κ _ _ => Nat.zero_le (factorWeight κ))
      have hfactor_lt_s : factorWeight ν < s :=
        hfactor_lt_sum.trans_le m.weightedWeight_le
      have hweight_le_factor : (m.address ν).1 ≤ factorWeight ν := by
        calc
          (m.address ν).1 = 1 * (m.address ν).1 := by simp
          _ ≤ m.binomialIndex ν * (m.address ν).1 := by
            exact Nat.mul_le_mul_right _ (m.binomialIndex_pos ν)
      exact lt_of_le_of_lt hweight_le_factor hfactor_lt_s
    have hfactor :
        ∀ ν ∈ (Finset.univ : Finset (Fin m.length)),
          IVMost
            (factorFunction ν)
            (factorDegree ν) := by
      intro ν _hν
      by_cases hνleft : m.side ν = 0
      · by_cases hνr : (m.address ν).1 < r
        · have hνzero : ∀ q : ℕ, A q (m.address ν).1 (m.address ν).2 = 0 := by
            intro q
            exact congrFun
              (hABelow q (m.address ν).1
                (Nat.succ_le_iff.mpr (m.commutatorWeight_pos ν))
                hνr (haddress_lt_n ν))
              (m.address ν).2
          convert collection_n_const 0 (factorDegree ν) using 1
          ext q
          simp [factorFunction, hνleft, hνzero q,
            Ring.choose_zero_pos ℤ (m.binomialIndex_pos ν)]
        · have hνpoly :=
            hpolyBelow (m.address ν).1
              (Nat.succ_le_iff.mpr (m.commutatorWeight_pos ν))
              (hleft_address_lt_s ν hνleft)
              (haddress_lt_n ν)
              (m.address ν).2
          simpa [factorFunction, factorDegree, hνleft] using
            collection_n_choose hνpoly (m.binomialIndex ν)
      · convert
          collection_n_const
            (Ring.choose
              (e (m.address ν).1 (m.address ν).2)
              (m.binomialIndex ν))
            (factorDegree ν) using 1
        ext q
        simp [factorFunction, hνleft]
    have hproduct :=
      n_finset_prod
        (Finset.univ : Finset (Fin m.length))
        factorFunction factorDegree hfactor
    have hproductEval :
        IVMost
          (fun q : ℕ => m.eval (A q) e)
          (∑ ν, factorDegree ν) := by
      simpa [BCMono.eval, factorFunction] using hproduct
    have hdegree_le : ∑ ν, factorDegree ν ≤ s / r - 1 := by
      let leftWeight : Fin m.length → ℕ :=
        fun ν => if m.side ν = 0 then factorWeight ν else 0
      let rightWeight : Fin m.length → ℕ :=
        fun ν => if m.side ν = 1 then factorWeight ν else 0
      have hdegree_left_weight :
          ∑ ν, factorDegree ν ≤ (∑ ν, leftWeight ν) / r := by
        calc
          ∑ ν, factorDegree ν ≤
              ∑ ν, (if m.side ν = 0 then factorWeight ν / r else 0) := by
                apply Finset.sum_le_sum
                intro ν _hν
                by_cases hνleft : m.side ν = 0
                · simp [factorDegree, factorWeight, hνleft,
                    p_collection_div
                      (m.binomialIndex ν) (m.address ν).1 r hr]
                · simp [factorDegree, hνleft]
          _ = ∑ ν, leftWeight ν / r := by
                apply Finset.sum_congr rfl
                intro ν _hν
                by_cases hνleft : m.side ν = 0 <;>
                  simp [leftWeight, factorWeight, hνleft]
          _ ≤ (∑ ν, leftWeight ν) / r :=
                collection_sum_div
                  (Finset.univ : Finset (Fin m.length)) leftWeight r
      have hsplit :
          ∑ ν, factorWeight ν = ∑ ν, leftWeight ν + ∑ ν, rightWeight ν := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro ν _hν
        by_cases hνleft : m.side ν = 0
        · have hνnotRight : m.side ν ≠ 1 := by
            intro hright
            rw [hνleft] at hright
            norm_num at hright
          simp [leftWeight, rightWeight, hνleft]
        · have hνright : m.side ν = 1 := by
            apply Fin.ext
            have hvalne : (m.side ν).val ≠ 0 := by
              intro hzero
              apply hνleft
              apply Fin.ext
              simpa using hzero
            omega
          simp [leftWeight, rightWeight, hνright]
      have hrightWeight_ge : r ≤ ∑ ν, rightWeight ν := by
        rcases m.has_right with ⟨ν, hνright⟩
        have hr_le_factor : r ≤ factorWeight ν := by
          calc
            r ≤ (m.address ν).1 := hrightLarge ν hνright
            _ = 1 * (m.address ν).1 := by simp
            _ ≤ m.binomialIndex ν * (m.address ν).1 := by
              exact Nat.mul_le_mul_right _ (m.binomialIndex_pos ν)
        have hsingle :
            rightWeight ν ≤ ∑ μ, rightWeight μ :=
          Finset.single_le_sum
            (fun μ _ => Nat.zero_le (rightWeight μ))
            (by simp : ν ∈ (Finset.univ : Finset (Fin m.length)))
        have hrightWeightν : rightWeight ν = factorWeight ν := by
          simp [rightWeight, hνright]
        exact hr_le_factor.trans (by simpa [hrightWeightν] using hsingle)
      have hleft_le_sub : ∑ ν, leftWeight ν ≤ s - r := by
        have hleft_add_r_le_s : ∑ ν, leftWeight ν + r ≤ s := by
          calc
            ∑ ν, leftWeight ν + r ≤
                ∑ ν, leftWeight ν + ∑ ν, rightWeight ν :=
              Nat.add_le_add_left hrightWeight_ge _
            _ = ∑ ν, factorWeight ν := hsplit.symm
            _ ≤ s := m.weightedWeight_le
        exact Nat.le_sub_of_add_le hleft_add_r_le_s
      have hleft_div_le :
          (∑ ν, leftWeight ν) / r ≤ (s - r) / r :=
        Nat.div_le_div_right hleft_le_sub
      have hsub_div_le : (s - r) / r ≤ s / r - 1 := by
        have hdivPos : 1 ≤ s / r := Nat.div_pos hrs hr
        have hplus : (s - r) / r + 1 ≤ s / r := by
          have h :=
            Nat.add_div_le_add_div (s - r) r r
          rw [Nat.sub_add_cancel hrs, Nat.div_self hr] at h
          exact h
        omega
      exact hdegree_left_weight.trans (hleft_div_le.trans hsub_div_le)
    exact collection_n_mono hdegree_le hproductEval

lemma BCComb.eval_power_n
    {d n r s : ℕ}
    {H : ∀ t : ℕ, BCWta.{u} d t}
    (C : BCComb H s)
    (A : ℕ → HEFam H)
    (e : HEFam H)
    (hr : 1 ≤ r)
    (hrs : r ≤ s)
    (hsn : s < n)
    (heBelow : ∀ t : ℕ, 1 ≤ t → t < r → t < n → e t = 0)
    (hABelow : ∀ q t : ℕ, 1 ≤ t → t < r → t < n → A q t = 0)
    (hpolyBelow :
      ∀ t : ℕ,
        1 ≤ t →
          t < s →
            t < n →
              ∀ i : (H t).index,
                IVMost (fun q : ℕ => A q t i) (t / r)) :
    IVMost
      (fun q : ℕ => C.eval (A q) e)
      (s / r - 1) := by
  classical
  have hterm :
      ∀ ν ∈ (Finset.univ : Finset (Fin C.length)),
        IVMost
          (fun q : ℕ => C.coefficient ν * (C.monomial ν).eval (A q) e)
          (s / r - 1) := by
    intro ν _hν
    exact collection_n_smul (C.coefficient ν)
      ((C.monomial ν).eval_power_n A e hr hrs hsn
        heBelow hABelow hpolyBelow)
  have hsum :=
    n_finset_sum
      (Finset.univ : Finset (Fin C.length))
      (fun ν q => C.coefficient ν * (C.monomial ν).eval (A q) e)
      hterm
  simpa [BCComb.eval] using hsum

/--
A genuinely binary lower-triangular Hall multiplication law.  It supplies a
binary coordinate operation `mul`, a lower-weight correction term, and the
facts that make the correction triangular.  It does not contain finite-product,
power, or inverse coordinate-polynomial conclusions.
-/
structure LGLaw
    {d n : ℕ}
    (H : ∀ r : ℕ, BCWta.{u} d r) where
  mul : HEFam H → HEFam H → HEFam H
  correction : HEFam H → HEFam H → HEFam H
  correction_formula :
    ∀ s : ℕ, (H s).index → BCComb H s
  product_eq :
    ∀ e f : HEFam H,
      collectedHallProduct (n := n) H (mul e f) =
        collectedHallProduct (n := n) H e *
          collectedHallProduct (n := n) H f
  coordinate_eq :
    ∀ (e f : HEFam H) (s : ℕ),
      1 ≤ s →
        s < n →
          ∀ i : (H s).index,
            mul e f s i = e s i + f s i + correction e f s i
  correction_eq_formula :
    ∀ (e f : HEFam H) (s : ℕ),
      1 ≤ s →
        s < n →
          ∀ i : (H s).index,
            correction e f s i =
              (correction_formula s i).eval e f
  correction_coordinates :
    ∀ {ι : Type}
      (input : ι → HEFam H)
      (e f : HEFam H)
      (s : ℕ),
        1 ≤ s →
          s < n →
            CoordinatesBinomialCombinations
              (n := n) H input e s →
            CoordinatesBinomialCombinations
              (n := n) H input f s →
              ∀ i : (H s).index,
                ICMonomi
                  H s input (correction e f s i)
  mul_zero_below :
    ∀ (e f : HEFam H) (r : ℕ),
      1 ≤ r →
        (∀ s : ℕ, 1 ≤ s → s < r → s < n → e s = 0) →
        (∀ s : ℕ, 1 ≤ s → s < r → s < n → f s = 0) →
          ∀ s : ℕ, 1 ≤ s → s < r → s < n → mul e f s = 0

namespace LGLaw

/-- The binary triangular law preserves the weighted-binomial coordinate language. -/
lemma mul_coordinates
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (law : LGLaw (n := n) H)
    {ι : Type}
    (input : ι → HEFam H)
    (e f : HEFam H)
    (he :
      WeightedBinomialCombinations
        (n := n) H input e)
    (hf :
      WeightedBinomialCombinations
        (n := n) H input f) :
    WeightedBinomialCombinations
      (n := n) H input (law.mul e f) := by
  intro s hs hsn i
  have hec := he s hs hsn i
  have hfc := hf s hs hsn i
  have hcorr :
      ICMonomi
        H s input (law.correction e f s i) :=
    law.correction_coordinates input e f s hs hsn
      (fun t ht hts htn j => he t ht htn j)
      (fun t ht hts htn j => hf t ht htn j)
      i
  rw [law.coordinate_eq e f s hs hsn i]
  exact
    combination_monomials_add
      (combination_monomials_add hec hfc)
      hcorr

/--
A lower-triangular binary `g h` law gives the full finite-list product
coordinate package by induction on the input list.
-/
theorem collectedCoordinateData
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (law : LGLaw (n := n) H) :
    ∀ e : List (HEFam H),
      CollectedCoordinateData (n := n) H e := by
  intro e
  induction e with
  | nil =>
      refine ⟨0, ?_, ?_⟩
      · simp [collectedHallProducts,
          collection_collected_zero]
      · intro s _hs _hsn _i
        exact
          int_combination_monomials
            (fun j : Fin [].length => [].get j)
  | cons e es ih =>
      rcases ih with ⟨Etail, hEtailProduct, hEtailCoordinates⟩
      let inputCons : Fin (e :: es).length → HEFam H :=
        fun j => (e :: es).get j
      have heCoordinates :
          WeightedBinomialCombinations
            (n := n) H inputCons e := by
        intro s _hs _hsn i
        simpa [inputCons] using
          combination_monomials_input
            inputCons (0 : Fin (e :: es).length)
            (⟨s, i⟩ : HEAddres H) le_rfl
      have htailCoordinates :
          WeightedBinomialCombinations
            (n := n) H inputCons Etail := by
        intro s hs hsn i
        have htail := hEtailCoordinates s hs hsn i
        have hmapped :=
          binomial_monomials_input
            inputCons (fun j : Fin es.length => j.succ) htail
        simpa [inputCons, Function.comp_def] using hmapped
      refine ⟨law.mul e Etail, ?_, ?_⟩
      · rw [law.product_eq, hEtailProduct]
        simp [collectedHallProducts]
      · exact law.mul_coordinates inputCons e Etail heCoordinates htailCoordinates

/-- Coordinates obtained by repeated right multiplication by one Hall family. -/
noncomputable def powerCoordinates
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (law : LGLaw (n := n) H)
    (e : HEFam H) :
    ℕ → HEFam H
  | 0 => 0
  | q + 1 => law.mul (powerCoordinates law e q) e

lemma powerCoordinates_product
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (law : LGLaw (n := n) H)
    (e : HEFam H) :
    ∀ q : ℕ,
      collectedHallProduct (n := n) H (powerCoordinates law e q) =
        collectedHallProduct (n := n) H e ^ q := by
  intro q
  induction q with
  | zero =>
      simp [powerCoordinates, collection_collected_zero]
  | succ q ih =>
      rw [powerCoordinates, law.product_eq, ih]
      simp [pow_succ]

lemma power_coordinates_below
    {d n r : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    (law : LGLaw (n := n) H)
    (e : HEFam H)
    (hr : 1 ≤ r)
    (heBelow : ∀ s : ℕ, 1 ≤ s → s < r → s < n → e s = 0) :
    ∀ q s : ℕ,
      1 ≤ s →
        s < r →
          s < n →
            powerCoordinates law e q s = 0 := by
  intro q
  induction q with
  | zero =>
      intro s _hs _hsr _hsn
      simp [powerCoordinates]
  | succ q ih =>
      intro s hs hsr hsn
      exact law.mul_zero_below (powerCoordinates law e q) e r hr
        (fun t ht htr htn => ih t ht htr htn)
        heBelow s hs hsr hsn

lemma coordinates_coordinate_sum
    {d n s : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (law : LGLaw (n := n) H)
    (e : HEFam H)
    (hs : 1 ≤ s)
    (hsn : s < n)
    (i : (H s).index) :
    ∀ q : ℕ,
      powerCoordinates law e q s i =
        ∑ j ∈ Finset.range q,
          (e s i + law.correction (powerCoordinates law e j) e s i) := by
  intro q
  induction q with
  | zero =>
      simp [powerCoordinates]
  | succ q ih =>
      calc
        powerCoordinates law e (q + 1) s i =
            powerCoordinates law e q s i + e s i +
              law.correction (powerCoordinates law e q) e s i := by
                rw [powerCoordinates, law.coordinate_eq _ _ s hs hsn i]
        _ = (∑ j ∈ Finset.range q,
              (e s i + law.correction (powerCoordinates law e j) e s i)) +
              (e s i + law.correction (powerCoordinates law e q) e s i) := by
                rw [ih]
                ring
        _ = ∑ j ∈ Finset.range (q + 1),
              (e s i + law.correction (powerCoordinates law e j) e s i) := by
                rw [Finset.sum_range_succ]

theorem collectedPolynomialData
    {d n : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    (law : LGLaw (n := n) H)
    (e : HEFam H)
    (r : ℕ)
    (hr : 1 ≤ r) :
    CollectedPolynomialData (n := n) H e r := by
  intro heBelow
  let E : ℕ → HEFam H := powerCoordinates law e
  refine ⟨E, ?_, ?_⟩
  · intro q
    exact powerCoordinates_product law e q
  · have hpolyAll :
        ∀ s : ℕ,
          1 ≤ s →
            s < n →
              ∀ i : (H s).index,
                IVMost (fun q : ℕ => E q s i) (s / r) := by
      intro s
      induction s using Nat.strong_induction_on with
      | h s ih =>
          intro hs hsn i
          by_cases hsr : s < r
          · have hzero :
                ∀ q : ℕ, E q s i = 0 := by
              intro q
              exact congrFun
                (power_coordinates_below law e hr heBelow q s hs hsr hsn) i
            convert collection_n_const 0 (s / r) using 1
            ext q
            exact hzero q
          · have hrs : r ≤ s := le_of_not_gt hsr
            have hdivPos : 1 ≤ s / r := Nat.div_pos hrs hr
            have hcorr :
                IVMost
                  (fun q : ℕ => law.correction (E q) e s i) (s / r - 1) :=
              by
                have hformula :
                    IVMost
                      (fun q : ℕ => (law.correction_formula s i).eval (E q) e)
                      (s / r - 1) :=
                  (law.correction_formula s i).eval_power_n E e hr hrs hsn
                    heBelow
                    (fun q t ht htr htn =>
                      power_coordinates_below law e hr heBelow q t ht htr htn)
                    (fun t ht hts htn j => ih t hts ht htn j)
                convert hformula using 1
                ext q
                exact law.correction_eq_formula (E q) e s hs hsn i
            have hconst :
                IVMost (fun _ : ℕ => e s i) (s / r - 1) :=
              collection_n_const (e s i) (s / r - 1)
            have hstep :
                IVMost
                  (fun q : ℕ => e s i + law.correction (E q) e s i)
                  (s / r - 1) := by
              have hsum := collection_n_add hconst hcorr
              convert hsum using 1
            have hpartial :=
              n_partial_sum hstep
            have hdegreeEq : s / r - 1 + 1 = s / r :=
              Nat.sub_add_cancel hdivPos
            have hpartial' :
                IVMost
                  (fun q : ℕ =>
                    ∑ j ∈ Finset.range q,
                      (e s i + law.correction (E j) e s i))
                  (s / r) := by
              simpa [hdegreeEq] using hpartial
            convert hpartial' using 1
            ext q
            simpa [E] using coordinates_coordinate_sum law e hs hsn i q
    intro s hs hsn i
    exact hpolyAll s hs hsn i

theorem collectedInverseData
    {d n : ℕ}
    (hn : 2 ≤ n)
    {H : ∀ s : ℕ, BCWta.{u} d s}
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    (law : LGLaw (n := n) H)
    (e : HEFam H) :
    CollectedInverseData (n := n) H e := by
  let input : Fin 1 → HEFam H :=
    fun _ => negExponentFamily e
  let Y : HEFam H :=
    normalFormCoordinates hn H hH (collectedHallProduct (n := n) H e)⁻¹
  have hYProduct :
      collectedHallProduct (n := n) H Y =
        (collectedHallProduct (n := n) H e)⁻¹ :=
    collected_form_coordinates hn H hH _
  have hmulProduct :
      collectedHallProduct (n := n) H (law.mul e Y) = 1 := by
    rw [law.product_eq, hYProduct]
    simp
  have hmulZero :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            law.mul e Y s = 0 :=
    collected_imp_coordinates
      hn H hH (law.mul e Y) hmulProduct
  refine ⟨Y, hYProduct, ?_⟩
  have heCoordinatesBelow :
      ∀ s : ℕ,
        CoordinatesBinomialCombinations
          (n := n) H input e s := by
    intro s t ht _hts _htn i
    have hraw :
        ICMonomi
          H t input (input 0 t i) :=
      combination_monomials_input
        input (0 : Fin 1) (⟨t, i⟩ : HEAddres H) le_rfl
    have hneg :=
      combination_monomials_neg hraw
    simpa [input, negExponentFamily] using hneg
  have hYThrough :
      ∀ k : ℕ,
        k ≤ n - 1 →
          ∀ s : ℕ,
            1 ≤ s →
              s ≤ k →
                s < n →
                  ∀ i : (H s).index,
                    ICMonomi
                      H s input (Y s i) := by
    intro k hk
    induction k with
    | zero =>
        intro s hs hsk _hsn _i
        omega
    | succ k ih =>
        intro s hs hsk hsn i
        by_cases hcurrent : s = k + 1
        · subst s
          have hYBelow :
              CoordinatesBinomialCombinations
                (n := n) H input Y (k + 1) := by
            intro t ht htk htn j
            exact ih (by omega) t ht (by omega) htn j
          have hcorr :
              ICMonomi
                H (k + 1) input (law.correction e Y (k + 1) i) :=
            law.correction_coordinates input e Y (k + 1)
              (by omega) (by omega)
              (heCoordinatesBelow (k + 1)) hYBelow i
          have hec :
              ICMonomi
                H (k + 1) input (e (k + 1) i) :=
            heCoordinatesBelow (k + 2) (k + 1) (by omega) (by omega) (by omega) i
          have hYeq :
              Y (k + 1) i =
                -e (k + 1) i - law.correction e Y (k + 1) i := by
            have hzero := congrFun (hmulZero (k + 1) (by omega) (by omega)) i
            have hcoord := law.coordinate_eq e Y (k + 1) (by omega) (by omega) i
            have hsumZero :
                e (k + 1) i + Y (k + 1) i +
                    law.correction e Y (k + 1) i = 0 :=
              hcoord.symm.trans hzero
            omega
          rw [hYeq]
          exact
            combination_monomials_sub
              (combination_monomials_neg hec)
              hcorr
        · exact ih (by omega) s hs (by omega) hsn i
  intro s hs hsn i
  exact hYThrough s (by omega) s hs le_rfl hsn i

end LGLaw

end TCTex
end Towers
