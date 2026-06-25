import Submission.Group.LowerCentralStrong
import Submission.Group.ZassenhausExplicit

open scoped commutatorElement

namespace Submission

/-- A binary commutator word over a family of atomic group elements. -/
inductive CWord (α : Type*) where
  | atom : α → CWord α
  | commutator : CWord α → CWord α → CWord α

namespace CWord

/-- Evaluate a binary commutator word in a group. -/
def eval
    {α : Type*}
    {G : Type*} [Group G]
    (f : α → G) :
    CWord α → G
  | atom a => f a
  | commutator u v => ⁅u.eval f, v.eval f⁆

/-- The additive weight of a binary commutator word. -/
def weight
    {α : Type*}
    (wt : α → ℕ) :
    CWord α → ℕ
  | atom a => wt a
  | commutator u v => u.weight wt + v.weight wt

@[simp]
lemma eval_atom
    {α : Type*}
    {G : Type*} [Group G]
    (f : α → G)
    (a : α) :
    (atom a).eval f = f a :=
  rfl

@[simp]
lemma eval_commutator
    {α : Type*}
    {G : Type*} [Group G]
    (f : α → G)
    (u v : CWord α) :
    (commutator u v).eval f = ⁅u.eval f, v.eval f⁆ :=
  rfl

@[simp]
lemma weight_atom
    {α : Type*}
    (wt : α → ℕ)
    (a : α) :
    (atom a).weight wt = wt a :=
  rfl

@[simp]
lemma weight_commutator
    {α : Type*}
    (wt : α → ℕ)
    (u v : CWord α) :
    (commutator u v).weight wt = u.weight wt + v.weight wt :=
  rfl

/-- Positive atomic weights give every binary commutator word positive weight. -/
lemma weight_pos
    {α : Type*}
    (wt : α → ℕ)
    (hwt : ∀ a, 0 < wt a) :
    ∀ w : CWord α, 0 < w.weight wt
  | atom a => hwt a
  | commutator u v =>
      Nat.add_pos_left (weight_pos wt hwt u) (v.weight wt)

/-- Evaluation of binary commutator words is natural under group homomorphisms. -/
lemma map_eval
    {α : Type*}
    {G H : Type*} [Group G] [Group H]
    (φ : G →* H)
    (f : α → G) :
    ∀ w : CWord α,
      φ (w.eval f) = w.eval (fun a => φ (f a))
  | atom _ => rfl
  | commutator u v => by
      rw [eval_commutator, map_commutatorElement, map_eval φ f u,
        map_eval φ f v, eval_commutator]

/-- If each atom lies in the lower-central term prescribed by its positive one-based weight,
then every binary commutator word lies in the term prescribed by its total weight. -/
lemma eval_lower_series
    {α : Type*}
    {G : Type*} [Group G]
    (f : α → G)
    (wt : α → ℕ)
    (hwt : ∀ a, 0 < wt a)
    (hf : ∀ a, f a ∈ Subgroup.lowerCentralSeries G (wt a - 1)) :
    ∀ w : CWord α,
      w.eval f ∈ Subgroup.lowerCentralSeries G (w.weight wt - 1)
  | atom a => hf a
  | commutator u v => by
      have hu :=
        eval_lower_series f wt hwt hf u
      have hv :=
        eval_lower_series f wt hwt hf v
      have hcomm :
          ⁅u.eval f, v.eval f⁆ ∈
            Subgroup.lowerCentralSeries G
              ((u.weight wt - 1) + (v.weight wt - 1) + 1) :=
        lower_commutator_succ
          (u.weight wt - 1) (v.weight wt - 1)
          (Subgroup.commutator_mem_commutator hu hv)
      have hu_pos : 0 < u.weight wt :=
        weight_pos wt hwt u
      have hv_pos : 0 < v.weight wt :=
        weight_pos wt hwt v
      have hindex :
          (u.weight wt - 1) + (v.weight wt - 1) + 1 =
            u.weight wt + v.weight wt - 1 := by
        omega
      simpa [hindex] using hcomm

end CWord

/-- The two atomic letters used in a Hall collection argument. -/
inductive HPAtom where
  | left
  | right

namespace HPAtom

/-- Evaluate the two atomic Hall letters at a chosen pair of group elements. -/
def eval
    {G : Type*} [Group G]
    (x y : G) :
    HPAtom → G
  | left => x
  | right => y

/-- Give the two atomic Hall letters their chosen one-based weights. -/
def weight
    (A B : ℕ) :
    HPAtom → ℕ
  | left => A
  | right => B

lemma weight_pos
    {A B : ℕ}
    (hA : 0 < A)
    (hB : 0 < B) :
    ∀ a : HPAtom, 0 < a.weight A B
  | left => hA
  | right => hB

end HPAtom

namespace CWord

/-- The binary commutator word `[x,y]`. -/
def hallPairBase :
    CWord HPAtom :=
  commutator (atom HPAtom.left) (atom HPAtom.right)

/-- The repeated left Hall word
`[x,y]`, `[x,[x,y]]`, `[x,[x,[x,y]]]`, and so on. -/
def pairLeftIterate :
    ℕ → CWord HPAtom
  | 0 => hallPairBase
  | n + 1 => commutator (atom HPAtom.left) (pairLeftIterate n)

@[simp]
lemma eval_pair_base
    {G : Type*} [Group G]
    (x y : G) :
    hallPairBase.eval (HPAtom.eval x y) = ⁅x, y⁆ :=
  rfl

@[simp]
lemma eval_pair_iterate
    {G : Type*} [Group G]
    (x y : G) :
    ∀ n : ℕ,
      (pairLeftIterate n).eval (HPAtom.eval x y) =
        leftIteratedElement x ⁅x, y⁆ n
  | 0 => rfl
  | n + 1 => by
      rw [pairLeftIterate, eval_commutator,
        eval_atom, HPAtom.eval, eval_pair_iterate,
        iterated_element_succ]

@[simp]
lemma weight_pair_base
    (A B : ℕ) :
    hallPairBase.weight (HPAtom.weight A B) = A + B := by
  simp [hallPairBase, HPAtom.weight]

@[simp]
lemma weight_pair_iterate
    (A B : ℕ) :
    ∀ n : ℕ,
      (pairLeftIterate n).weight (HPAtom.weight A B) =
        (n + 1) * A + B
  | 0 => by simp [pairLeftIterate, hallPairBase, HPAtom.weight]
  | n + 1 => by
      rw [pairLeftIterate, weight_commutator, weight_atom,
        HPAtom.weight, weight_pair_iterate]
      ring

/-- A pairwise error bracket among repeated left Hall factors. -/
def iteratePairwiseError
    (r s : ℕ) :
    CWord HPAtom :=
  commutator (pairLeftIterate r) (pairLeftIterate s)

@[simp]
lemma pair_iterate_error
    {G : Type*} [Group G]
    (x y : G)
    (r s : ℕ) :
    (iteratePairwiseError r s).eval (HPAtom.eval x y) =
      ⁅leftIteratedElement x ⁅x, y⁆ r,
        leftIteratedElement x ⁅x, y⁆ s⁆ := by
  simp [iteratePairwiseError]

@[simp]
lemma weight_pairwise_error
    (A B r s : ℕ) :
    (iteratePairwiseError r s).weight (HPAtom.weight A B) =
      (r + s + 2) * A + 2 * B := by
  simp [iteratePairwiseError]
  ring

/-- A Hall pair word evaluated at lower-central elements lies in its exact weighted
lower-central term. -/
lemma pair_lower_series
    {G : Type*} [Group G]
    {i j : ℕ}
    {x y : G}
    (hx : x ∈ Subgroup.lowerCentralSeries G i)
    (hy : y ∈ Subgroup.lowerCentralSeries G j)
    (w : CWord HPAtom) :
    w.eval (HPAtom.eval x y) ∈
      Subgroup.lowerCentralSeries G
        (w.weight (HPAtom.weight (i + 1) (j + 1)) - 1) := by
  apply
    eval_lower_series
      (HPAtom.eval x y)
      (HPAtom.weight (i + 1) (j + 1))
      (HPAtom.weight_pos (Nat.succ_pos i) (Nat.succ_pos j))
  intro a
  cases a with
  | left =>
      simpa [HPAtom.eval, HPAtom.weight] using hx
  | right =>
      simpa [HPAtom.eval, HPAtom.weight] using hy

end CWord

/-- The normal subgroup generated by evaluated commutator words of weight at least a cutoff. -/
def highCommutatorSubgroup
    {α : Type*}
    {G : Type*} [Group G]
    (f : α → G)
    (wt : α → ℕ)
    (cutoff : ℕ) :
    Subgroup G :=
  Subgroup.normalClosure
    { g : G |
      ∃ w : CWord α,
        cutoff ≤ w.weight wt ∧
          w.eval f = g }

instance high_commutator_normal
    {α : Type*}
    {G : Type*} [Group G]
    (f : α → G)
    (wt : α → ℕ)
    (cutoff : ℕ) :
    (highCommutatorSubgroup f wt cutoff).Normal :=
  Subgroup.normalClosure_normal

/-- Every evaluated commutator word at or above the cutoff belongs to the high-weight
normal subgroup. -/
lemma CWord.evalmem_highweight_commwordsubg
    {α : Type*}
    {G : Type*} [Group G]
    {f : α → G}
    {wt : α → ℕ}
    {cutoff : ℕ}
    {w : CWord α}
    (hw : cutoff ≤ w.weight wt) :
    w.eval f ∈ highCommutatorSubgroup f wt cutoff :=
  Subgroup.subset_normalClosure ⟨w, hw, rfl⟩

/-- Raising the cutoff shrinks the high-weight commutator-word subgroup. -/
lemma high_commutator_antitone
    {α : Type*}
    {G : Type*} [Group G]
    (f : α → G)
    (wt : α → ℕ) :
    Antitone (highCommutatorSubgroup f wt) := by
  intro a b hab
  apply Subgroup.normalClosure_mono
  rintro g ⟨w, hw, rfl⟩
  exact ⟨w, hab.trans hw, rfl⟩

/-- High-weight commutator words vanish in the quotient by their normal closure. -/
lemma CWord.quotmk_evaleq_onehighweight
    {α : Type*}
    {G : Type*} [Group G]
    {f : α → G}
    {wt : α → ℕ}
    {cutoff : ℕ}
    {w : CWord α}
    (hw : cutoff ≤ w.weight wt) :
    QuotientGroup.mk' (highCommutatorSubgroup f wt cutoff) (w.eval f) = 1 := by
  exact
    (QuotientGroup.eq_one_iff (w.eval f)).2
      (w.evalmem_highweight_commwordsubg hw)

/-- The high-weight word subgroup for a Hall pair. -/
abbrev highPairSubgroup
    {G : Type*} [Group G]
    (x y : G)
    (A B cutoff : ℕ) :
    Subgroup G :=
  highCommutatorSubgroup
    (HPAtom.eval x y)
    (HPAtom.weight A B)
    cutoff

/-- A repeated-left Hall pairwise error belongs to the high-weight subgroup once its exact
weight reaches the cutoff. -/
lemma CWord.evahalpailef_itepaierrmem_hiwehapasu
    {G : Type*} [Group G]
    {x y : G}
    {A B cutoff r s : ℕ}
    (hweight : cutoff ≤ (r + s + 2) * A + 2 * B) :
    (iteratePairwiseError r s).eval (HPAtom.eval x y) ∈
      highPairSubgroup x y A B cutoff := by
  apply CWord.evalmem_highweight_commwordsubg
  simpa using hweight

/-- The normal subgroup generated by prime-power powers of evaluated commutator words whose
weighted prime-power degree reaches a cutoff. -/
def weightedCommutatorSubgroup
    (p : ℕ)
    {α : Type*}
    {G : Type*} [Group G]
    (f : α → G)
    (wt : α → ℕ)
    (cutoff : ℕ) :
    Subgroup G :=
  Subgroup.normalClosure
    { g : G |
      ∃ (w : CWord α) (e : ℕ),
        cutoff ≤ w.weight wt * p ^ e ∧
          w.eval f ^ (p ^ e) = g }

instance weighted_commutator_normal
    (p : ℕ)
    {α : Type*}
    {G : Type*} [Group G]
    (f : α → G)
    (wt : α → ℕ)
    (cutoff : ℕ) :
    (weightedCommutatorSubgroup p f wt cutoff).Normal :=
  Subgroup.normalClosure_normal

/-- Every prime-power power of an evaluated commutator word at the requested weighted degree
belongs to the weighted-power word subgroup. -/
lemma CWord.evalpowprime_powermemweight_powcomworsub
    {p : ℕ}
    {α : Type*}
    {G : Type*} [Group G]
    {f : α → G}
    {wt : α → ℕ}
    {cutoff e : ℕ}
    {w : CWord α}
    (hw : cutoff ≤ w.weight wt * p ^ e) :
    w.eval f ^ (p ^ e) ∈
      weightedCommutatorSubgroup p f wt cutoff :=
  Subgroup.subset_normalClosure ⟨w, e, hw, rfl⟩

/-- Any multiple of a sufficient prime-power exponent is also absorbed by the weighted-power
word subgroup. -/
lemma CWord.evalpowmem_weightpowercomm_wordsubgroupdvd
    {p : ℕ}
    {α : Type*}
    {G : Type*} [Group G]
    {f : α → G}
    {wt : α → ℕ}
    {cutoff e k : ℕ}
    {w : CWord α}
    (hw : cutoff ≤ w.weight wt * p ^ e)
    (hk : p ^ e ∣ k) :
    w.eval f ^ k ∈
      weightedCommutatorSubgroup p f wt cutoff := by
  obtain ⟨q, rfl⟩ := hk
  rw [pow_mul]
  exact
    (weightedCommutatorSubgroup p f wt cutoff).pow_mem
      (w.evalpowprime_powermemweight_powcomworsub hw)
      q

/-- Evaluated words at or above the cutoff are the exponent-zero part of the weighted-power
word subgroup. -/
lemma CWord.evalmem_weightpower_commwordsubg
    {p : ℕ}
    {α : Type*}
    {G : Type*} [Group G]
    {f : α → G}
    {wt : α → ℕ}
    {cutoff : ℕ}
    {w : CWord α}
    (hw : cutoff ≤ w.weight wt) :
    w.eval f ∈ weightedCommutatorSubgroup p f wt cutoff := by
  simpa using
    (w.evalpowprime_powermemweight_powcomworsub
      (p := p) (e := 0) (by simpa using hw))

/-- The high-weight word subgroup is contained in the weighted-power word subgroup. -/
lemma high_weighted_power
    (p : ℕ)
    {α : Type*}
    {G : Type*} [Group G]
    (f : α → G)
    (wt : α → ℕ)
    (cutoff : ℕ) :
    highCommutatorSubgroup f wt cutoff ≤
      weightedCommutatorSubgroup p f wt cutoff := by
  apply Subgroup.normalClosure_le_normal
  rintro _ ⟨w, hw, rfl⟩
  exact w.evalmem_weightpower_commwordsubg hw

/-- Weighted-power commutator words built from lower-central atoms belong to the root
Zassenhaus closure at the same cutoff. -/
lemma weighted_commutator_filtration
    {p : ℕ}
    {α : Type*}
    {G : Type*} [Group G]
    (f : α → G)
    (wt : α → ℕ)
    (hwt : ∀ a, 0 < wt a)
    (hf : ∀ a, f a ∈ Subgroup.lowerCentralSeries G (wt a - 1))
    (cutoff : ℕ) :
    weightedCommutatorSubgroup p f wt cutoff ≤
      zassenhausFiltration p G cutoff := by
  letI : (zassenhausFiltration p G cutoff).Normal :=
    zassenhausFiltration_normal p G cutoff
  apply Subgroup.normalClosure_le_normal
  rintro _ ⟨w, e, hw, rfl⟩
  apply Subgroup.subset_closure
  refine ⟨w.weight wt - 1, e, w.eval f, ?_, ?_, rfl⟩
  · exact w.eval_lower_series f wt hwt hf
  · simpa [Nat.sub_add_cancel (Nat.succ_le_iff.mpr (w.weight_pos wt hwt))] using hw

/-- The weighted-power commutator-word subgroup for a Hall pair. -/
abbrev weightedPairSubgroup
    (p : ℕ)
    {G : Type*} [Group G]
    (x y : G)
    (A B cutoff : ℕ) :
    Subgroup G :=
  weightedCommutatorSubgroup
    p
    (HPAtom.eval x y)
    (HPAtom.weight A B)
    cutoff

/-- The high-weight Hall-pair subgroup is contained in its weighted-power refinement. -/
lemma high_pair_weighted
    (p : ℕ)
    {G : Type*} [Group G]
    (x y : G)
    (A B cutoff : ℕ) :
    highPairSubgroup x y A B cutoff ≤
      weightedPairSubgroup p x y A B cutoff :=
  high_weighted_power
    p (HPAtom.eval x y) (HPAtom.weight A B) cutoff

/-- Weighted-power Hall-pair words built from lower-central elements belong to the root
Zassenhaus closure at the same cutoff. -/
lemma weighted_pair_filtration
    {p : ℕ}
    {G : Type*} [Group G]
    {i j cutoff : ℕ}
    {x y : G}
    (hx : x ∈ Subgroup.lowerCentralSeries G i)
    (hy : y ∈ Subgroup.lowerCentralSeries G j) :
    weightedPairSubgroup p x y (i + 1) (j + 1) cutoff ≤
      zassenhausFiltration p G cutoff := by
  apply
    weighted_commutator_filtration
      (HPAtom.eval x y)
      (HPAtom.weight (i + 1) (j + 1))
      (HPAtom.weight_pos (Nat.succ_pos i) (Nat.succ_pos j))
  intro a
  cases a with
  | left =>
      simpa [HPAtom.eval, HPAtom.weight] using hx
  | right =>
      simpa [HPAtom.eval, HPAtom.weight] using hy

end Submission
