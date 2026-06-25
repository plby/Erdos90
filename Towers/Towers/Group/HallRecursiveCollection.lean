import Towers.Group.HallCollection
import Towers.Group.HallFiltered

open scoped commutatorElement

namespace Towers

namespace CWord

/-- Substitute a commutator word for every atomic letter. -/
def bind
    {α β : Type*}
    (σ : α → CWord β) :
    CWord α → CWord β
  | atom a => σ a
  | commutator u v => commutator (u.bind σ) (v.bind σ)

@[simp]
lemma bind_atom
    {α β : Type*}
    (σ : α → CWord β)
    (a : α) :
    (atom a).bind σ = σ a :=
  rfl

@[simp]
lemma bind_commutator
    {α β : Type*}
    (σ : α → CWord β)
    (u v : CWord α) :
    (commutator u v).bind σ =
      commutator (u.bind σ) (v.bind σ) :=
  rfl

/-- Evaluation commutes with substitution of commutator words. -/
@[simp]
lemma eval_bind
    {α β : Type*}
    {G : Type*} [Group G]
    (f : β → G)
    (σ : α → CWord β) :
    ∀ w : CWord α,
      (w.bind σ).eval f = w.eval (fun a => (σ a).eval f)
  | atom _ => rfl
  | commutator u v => by
      simp only [bind_commutator, eval_commutator, eval_bind f σ u,
        eval_bind f σ v]

/-- Additive weight commutes with substitution of commutator words. -/
@[simp]
lemma weight_bind
    {α β : Type*}
    (wt : β → ℕ)
    (σ : α → CWord β) :
    ∀ w : CWord α,
      (w.bind σ).weight wt =
        w.weight (fun a => (σ a).weight wt)
  | atom _ => rfl
  | commutator u v => by
      simp only [bind_commutator, weight_commutator, weight_bind wt σ u,
        weight_bind wt σ v]

/-- Substitute two arbitrary words for the left and right letters of a Hall pair. -/
def hallPairBind
    {α : Type*}
    (u v : CWord α) :
    CWord HPAtom → CWord α :=
  bind fun
    | HPAtom.left => u
    | HPAtom.right => v

@[simp]
lemma bind_atom_left
    {α : Type*}
    (u v : CWord α) :
    hallPairBind u v (atom HPAtom.left) = u :=
  rfl

@[simp]
lemma bind_atom_right
    {α : Type*}
    (u v : CWord α) :
    hallPairBind u v (atom HPAtom.right) = v :=
  rfl

/-- Evaluation of a Hall-pair substitution is evaluation of the outer Hall word at the
evaluated inner pair. -/
@[simp]
lemma eval_pair_bind
    {α : Type*}
    {G : Type*} [Group G]
    (f : α → G)
    (u v : CWord α)
    (w : CWord HPAtom) :
    (hallPairBind u v w).eval f =
      w.eval (HPAtom.eval (u.eval f) (v.eval f)) := by
  rw [hallPairBind, eval_bind]
  congr 1
  funext a
  cases a <;> rfl

/-- The weight of a Hall-pair substitution is the outer Hall weight evaluated at the
weights of the inner pair. -/
@[simp]
lemma weight_pair_bind
    {α : Type*}
    (wt : α → ℕ)
    (u v : CWord α)
    (w : CWord HPAtom) :
    (hallPairBind u v w).weight wt =
      w.weight (HPAtom.weight (u.weight wt) (v.weight wt)) := by
  rw [hallPairBind, weight_bind]
  congr 1
  funext a
  cases a <;> rfl

/-- The substituted basic Hall pair is the bracket of the two substituted words. -/
@[simp]
lemma pair_bind_base
    {α : Type*}
    (u v : CWord α) :
    hallPairBind u v hallPairBase = commutator u v :=
  rfl

/-- Substituted repeated-left Hall words evaluate to repeated-left commutators of the
evaluated inner pair. -/
@[simp]
lemma eval_bind_iterate
    {α : Type*}
    {G : Type*} [Group G]
    (f : α → G)
    (u v : CWord α)
    (r : ℕ) :
    (hallPairBind u v (pairLeftIterate r)).eval f =
      leftIteratedElement (u.eval f) ⁅u.eval f, v.eval f⁆ r := by
  rw [eval_pair_bind]
  simp

/-- Substitution preserves the exact repeated-left Hall weight formula. -/
@[simp]
lemma bind_left_iterate
    {α : Type*}
    (wt : α → ℕ)
    (u v : CWord α)
    (r : ℕ) :
    (hallPairBind u v (pairLeftIterate r)).weight wt =
      (r + 1) * u.weight wt + v.weight wt := by
  rw [weight_pair_bind]
  simp

/-- Substituted pairwise Hall errors remain explicit commutator words over the original
alphabet, with their exact recursive weight. -/
@[simp]
lemma pair_bind_error
    {α : Type*}
    (wt : α → ℕ)
    (u v : CWord α)
    (r s : ℕ) :
    (hallPairBind u v (iteratePairwiseError r s)).weight wt =
      (r + s + 2) * u.weight wt + 2 * v.weight wt := by
  rw [weight_pair_bind]
  simp

/-- A substituted pairwise Hall error has strictly larger weight than the inner basic bracket. -/
lemma bind_pairwise_error
    {α : Type*}
    (wt : α → ℕ)
    (hwt : ∀ z, 0 < wt z)
    (u v : CWord α)
    (r s : ℕ) :
    u.weight wt + v.weight wt <
      (hallPairBind u v (iteratePairwiseError r s)).weight wt := by
  rw [pair_bind_error]
  have hv : 0 < v.weight wt := v.weight_pos wt hwt
  have hcoeff : 1 ≤ r + s + 2 := by omega
  have hu_le :
      u.weight wt ≤ (r + s + 2) * u.weight wt := by
    simpa only [one_mul] using
      Nat.mul_le_mul_right (u.weight wt) hcoeff
  have hv_lt : v.weight wt < 2 * v.weight wt := by omega
  exact Nat.add_lt_add_of_le_of_lt hu_le hv_lt

/-- The natural cutoff-minus-weight measure strictly decreases when collection descends into a
substituted pairwise Hall error below a fixed cutoff. -/
lemma bind_iterate_error
    {α : Type*}
    (wt : α → ℕ)
    (hwt : ∀ z, 0 < wt z)
    (u v : CWord α)
    (cutoff r s : ℕ)
    (hbelow : u.weight wt + v.weight wt < cutoff) :
    cutoff -
          (hallPairBind u v (iteratePairwiseError r s)).weight wt <
      cutoff - (u.weight wt + v.weight wt) := by
  have hincrease :=
    bind_pairwise_error
      wt hwt u v r s
  omega

end CWord

namespace WCFactor

/-- A pending substituted pairwise Hall error.  It is represented at cutoff zero until recursive
collection proves that its weighted degree reaches the final cutoff. -/
def pairwiseErrorRaw
    {p : ℕ}
    {α : Type*}
    {G : Type*} [Group G]
    {f : α → G}
    {wt : α → ℕ}
    (u v : CWord α)
    (r s : ℕ) :
    WCFactor p f wt 0 :=
  raw
    (CWord.hallPairBind u v
      (CWord.iteratePairwiseError r s))
    0
    1
    1

@[simp]
lemma eval_pairwise_error
    {p : ℕ}
    {α : Type*}
    {G : Type*} [Group G]
    {f : α → G}
    {wt : α → ℕ}
    (u v : CWord α)
    (r s : ℕ) :
    (pairwiseErrorRaw (p := p) (f := f) (wt := wt) u v r s).eval =
      ⁅leftIteratedElement (u.eval f) ⁅u.eval f, v.eval f⁆ r,
        leftIteratedElement (u.eval f) ⁅u.eval f, v.eval f⁆ s⁆ := by
  simp [pairwiseErrorRaw, raw, eval]

@[simp]
lemma weight_error_raw
    {p : ℕ}
    {α : Type*}
    {G : Type*} [Group G]
    {f : α → G}
    {wt : α → ℕ}
    (u v : CWord α)
    (r s : ℕ) :
    (pairwiseErrorRaw (p := p) (f := f) (wt := wt) u v r s).word.weight wt =
      (r + s + 2) * u.weight wt + 2 * v.weight wt := by
  simp [pairwiseErrorRaw, raw]

@[simp]
lemma weighted_pairwise_error
    {p : ℕ}
    {α : Type*}
    {G : Type*} [Group G]
    {f : α → G}
    {wt : α → ℕ}
    (u v : CWord α)
    (r s : ℕ) :
    (pairwiseErrorRaw (p := p) (f := f) (wt := wt) u v r s).word.weight wt *
        p ^ (pairwiseErrorRaw (p := p) (f := f) (wt := wt) u v r s).primeExponent =
      (r + s + 2) * u.weight wt + 2 * v.weight wt := by
  simp [pairwiseErrorRaw, raw]

/-- The pending pairwise Hall-error factor strictly decreases the natural recursive
cutoff-minus-weight measure. -/
lemma cutoff_pairwise_error
    {p : ℕ}
    {α : Type*}
    {G : Type*} [Group G]
    {f : α → G}
    {wt : α → ℕ}
    (hwt : ∀ z, 0 < wt z)
    (u v : CWord α)
    (cutoff r s : ℕ)
    (hbelow : u.weight wt + v.weight wt < cutoff) :
    cutoff -
          (pairwiseErrorRaw (p := p) (f := f) (wt := wt) u v r s).word.weight wt <
      cutoff - (u.weight wt + v.weight wt) := by
  simpa [pairwiseErrorRaw, raw] using
    CWord.bind_iterate_error
      wt hwt u v cutoff r s hbelow

/-- Promote a pending substituted pairwise Hall error after its exact weight reaches the desired
cutoff. -/
def pairwiseError
    {p : ℕ}
    {α : Type*}
    {G : Type*} [Group G]
    {f : α → G}
    {wt : α → ℕ}
    {cutoff : ℕ}
    (u v : CWord α)
    (r s : ℕ)
    (hbound : cutoff ≤ (r + s + 2) * u.weight wt + 2 * v.weight wt) :
    WCFactor p f wt cutoff :=
  (pairwiseErrorRaw (p := p) (f := f) (wt := wt) u v r s).rebase (by
    simpa [pairwiseErrorRaw, raw] using hbound)

@[simp]
lemma eval_pairwiseError
    {p : ℕ}
    {α : Type*}
    {G : Type*} [Group G]
    {f : α → G}
    {wt : α → ℕ}
    {cutoff : ℕ}
    (u v : CWord α)
    (r s : ℕ)
    (hbound : cutoff ≤ (r + s + 2) * u.weight wt + 2 * v.weight wt) :
    (pairwiseError (p := p) (f := f) (wt := wt) u v r s hbound).eval =
      ⁅leftIteratedElement (u.eval f) ⁅u.eval f, v.eval f⁆ r,
        leftIteratedElement (u.eval f) ⁅u.eval f, v.eval f⁆ s⁆ := by
  simp [pairwiseError]

/-- A cutoff-zero factor is a pending unequal pairwise Hall error when its word is a substituted
pairwise error, its prime exponent is zero, and its remaining multiplicity and conjugator are
recorded explicitly. -/
def PERaw
    {p : ℕ}
    {α : Type*}
    {G : Type*} [Group G]
    {f : α → G}
    {wt : α → ℕ}
    (u v : CWord α)
    (F : WCFactor p f wt 0) :
    Prop :=
  ∃ r s : ℕ, r ≠ s ∧
    ∃ multiplicity : ℤ, ∃ conjugator : G,
      F =
        raw
          (CWord.hallPairBind u v
            (CWord.iteratePairwiseError r s))
          0
          multiplicity
          conjugator

/-- Inverting a pending pairwise-error factor preserves its origin, changing only the integral
multiplicity. -/
lemma PERaw.inv
    {p : ℕ}
    {α : Type*}
    {G : Type*} [Group G]
    {f : α → G}
    {wt : α → ℕ}
    {u v : CWord α}
    {F : WCFactor p f wt 0}
    (hF : PERaw u v F) :
    PERaw u v F.inv := by
  rcases hF with ⟨r, s, hrs, multiplicity, conjugator, rfl⟩
  exact ⟨r, s, hrs, -multiplicity, conjugator, rfl⟩

/-- Every pending pairwise-error factor strictly lowers the parent cutoff-minus-weight measure.
The recorded conjugator and integral multiplicity do not affect the recursive word weight. -/
lemma PERaw.cutoff_sub_weightlt
    {p : ℕ}
    {α : Type*}
    {G : Type*} [Group G]
    {f : α → G}
    {wt : α → ℕ}
    {u v : CWord α}
    {F : WCFactor p f wt 0}
    (hF : PERaw u v F)
    (hwt : ∀ z, 0 < wt z)
    (cutoff : ℕ)
    (hbelow : u.weight wt + v.weight wt < cutoff) :
    cutoff - F.word.weight wt <
      cutoff - (u.weight wt + v.weight wt) := by
  rcases hF with ⟨r, s, _hrs, multiplicity, conjugator, rfl⟩
  simpa [raw] using
    CWord.bind_iterate_error
      wt hwt u v cutoff r s hbelow

/-- Reversing and inverting a pending-error list preserves the origin certificate on every
entry. -/
lemma PERaw.listInv
    {p : ℕ}
    {α : Type*}
    {G : Type*} [Group G]
    {f : α → G}
    {wt : α → ℕ}
    {u v : CWord α}
    {L : List (WCFactor p f wt 0)}
    (hL : ∀ F ∈ L, PERaw u v F) :
    ∀ F ∈ listInv L, PERaw u v F := by
  intro F hF
  induction L with
  | nil =>
      change F ∈ ([] : List (WCFactor p f wt 0)) at hF
      contradiction
  | cons E L ih =>
      change F ∈ WCFactor.listInv L ++ [E.inv] at hF
      rw [List.mem_append, List.mem_singleton] at hF
      rcases hF with hF | hF
      · exact ih (fun X hX => hL X (by simp [hX])) hF
      · subst F
        exact (hL E (by simp)).inv

/-- Every element of the unequal-pairwise-error normal closure has an explicit pending-factor
list.  Unlike opaque subgroup membership, the returned list remembers that every entry is a
conjugated integral multiple of a substituted unequal pairwise Hall error. -/
lemma pairwise_error_raw
    {p : ℕ}
    {α : Type*}
    {G : Type*} [Group G]
    {f : α → G}
    {wt : α → ℕ}
    {u v : CWord α}
    {g : G}
    (hg :
      g ∈
        iteratedPairwiseComm
          (u.eval f)
          ⁅u.eval f, v.eval f⁆) :
    ∃ L : List (WCFactor p f wt 0),
      listEval L = g ∧
        ∀ F ∈ L, PERaw u v F := by
  change
    g ∈ Subgroup.closure
      (Group.conjugatesOfSet
        { z : G |
          ∃ r s : ℕ, r ≠ s ∧
            z =
              ⁅leftIteratedElement (u.eval f) ⁅u.eval f, v.eval f⁆ r,
                leftIteratedElement (u.eval f) ⁅u.eval f, v.eval f⁆ s⁆ }) at hg
  induction hg using Subgroup.closure_induction with
  | mem z hz =>
      rcases Group.mem_conjugatesOfSet_iff.mp hz with ⟨x, hx, hconj⟩
      rcases hx with ⟨r, s, hrs, rfl⟩
      rcases isConj_iff.mp hconj with ⟨conjugator, rfl⟩
      let F : WCFactor p f wt 0 :=
        raw
          (CWord.hallPairBind u v
            (CWord.iteratePairwiseError r s))
          0
          1
          conjugator
      refine ⟨[F], ?_, ?_⟩
      · simp [F, raw, eval]
      · intro E hE
        simp only [List.mem_singleton] at hE
        subst E
        exact ⟨r, s, hrs, 1, conjugator, rfl⟩
  | one =>
      exact ⟨[], rfl, by simp⟩
  | mul x y _hx _hy ihx ihy =>
      rcases ihx with ⟨L, hL, hLorigin⟩
      rcases ihy with ⟨M, hM, hMorigin⟩
      refine ⟨L ++ M, by simp [hL, hM], ?_⟩
      intro F hF
      rcases List.mem_append.mp hF with hF | hF
      · exact hLorigin F hF
      · exact hMorigin F hF
  | inv x _hx ih =>
      rcases ih with ⟨L, hL, hLorigin⟩
      refine ⟨listInv L, by simp [hL], ?_⟩
      exact PERaw.listInv hLorigin

/-- The explicit pending list extracted from the unequal-pairwise-error normal closure consists
entirely of strictly smaller recursive branches. -/
lemma pairwise_error_measure
    {p : ℕ}
    {α : Type*}
    {G : Type*} [Group G]
    {f : α → G}
    {wt : α → ℕ}
    {u v : CWord α}
    {g : G}
    (hg :
      g ∈
        iteratedPairwiseComm
          (u.eval f)
          ⁅u.eval f, v.eval f⁆)
    (hwt : ∀ z, 0 < wt z)
    (cutoff : ℕ)
    (hbelow : u.weight wt + v.weight wt < cutoff) :
    ∃ L : List (WCFactor p f wt 0),
      listEval L = g ∧
        ∀ F ∈ L,
          cutoff - F.word.weight wt <
            cutoff - (u.weight wt + v.weight wt) := by
  rcases pairwise_error_raw hg with
    ⟨L, hL, hLorigin⟩
  refine ⟨L, hL, ?_⟩
  intro F hF
  exact (hLorigin F hF).cutoff_sub_weightlt hwt cutoff hbelow

/-- Transport an admitted powered factor through substitution of commutator words. -/
def bind
    {p : ℕ}
    {α β : Type*}
    {G : Type*} [Group G]
    {f : β → G}
    {wt : β → ℕ}
    {cutoff : ℕ}
    (σ : α → CWord β)
    (F :
      WCFactor p
        (fun a => (σ a).eval f)
        (fun a => (σ a).weight wt)
        cutoff) :
    WCFactor p f wt cutoff where
  word := F.word.bind σ
  primeExponent := F.primeExponent
  multiplicity := F.multiplicity
  conjugator := F.conjugator
  weight_bound := by
    simpa using F.weight_bound

/-- Evaluation of an admitted powered factor is unchanged by substitution transport. -/
@[simp]
lemma eval_bind
    {p : ℕ}
    {α β : Type*}
    {G : Type*} [Group G]
    {f : β → G}
    {wt : β → ℕ}
    {cutoff : ℕ}
    (σ : α → CWord β)
    (F :
      WCFactor p
        (fun a => (σ a).eval f)
        (fun a => (σ a).weight wt)
        cutoff) :
    (F.bind σ).eval = F.eval := by
  simp [WCFactor.bind,
    WCFactor.eval]

/-- Transport a collected list of admitted powered factors through substitution. -/
def listBind
    {p : ℕ}
    {α β : Type*}
    {G : Type*} [Group G]
    {f : β → G}
    {wt : β → ℕ}
    {cutoff : ℕ}
    (σ : α → CWord β)
    (L :
      List
        (WCFactor p
          (fun a => (σ a).eval f)
          (fun a => (σ a).weight wt)
          cutoff)) :
    List (WCFactor p f wt cutoff) :=
  L.map (bind σ)

/-- Evaluation of a collected factor list is unchanged by substitution transport. -/
@[simp]
lemma list_eval_bind
    {p : ℕ}
    {α β : Type*}
    {G : Type*} [Group G]
    {f : β → G}
    {wt : β → ℕ}
    {cutoff : ℕ}
    (σ : α → CWord β)
    (L :
      List
        (WCFactor p
          (fun a => (σ a).eval f)
          (fun a => (σ a).weight wt)
          cutoff)) :
    listEval (listBind σ L) = listEval L := by
  induction L with
  | nil =>
      rfl
  | cons F L ih =>
      change (F.bind σ).eval * listEval (listBind σ L) =
        F.eval * listEval L
      rw [eval_bind, ih]

end WCFactor

/-- Substitution of commutator words sends every weighted-power word subgroup into the
weighted-power word subgroup over the original alphabet. -/
lemma weighted_commutator_bind
    {p : ℕ}
    {α β : Type*}
    {G : Type*} [Group G]
    (f : β → G)
    (wt : β → ℕ)
    (σ : α → CWord β)
    (cutoff : ℕ) :
    weightedCommutatorSubgroup p
        (fun a => (σ a).eval f)
        (fun a => (σ a).weight wt)
        cutoff ≤
      weightedCommutatorSubgroup p f wt cutoff := by
  apply Subgroup.normalClosure_le_normal
  rintro _ ⟨w, e, hw, rfl⟩
  have hbound :
      cutoff ≤ (w.bind σ).weight wt * p ^ e := by
    simpa using hw
  simpa using
    ((w.bind σ).evalpowprime_powermemweight_powcomworsub
      (f := f) (wt := wt) hbound)

/-- Recursive collection over an evaluated Hall pair transports back to the original
commutator-word subgroup. -/
lemma weighted_pair_word
    {p : ℕ}
    {α : Type*}
    {G : Type*} [Group G]
    (f : α → G)
    (wt : α → ℕ)
    (u v : CWord α)
    (cutoff : ℕ) :
    weightedPairSubgroup p
        (u.eval f)
        (v.eval f)
        (u.weight wt)
        (v.weight wt)
        cutoff ≤
      weightedCommutatorSubgroup p f wt cutoff := by
  let σ : HPAtom → CWord α := fun
    | HPAtom.left => u
    | HPAtom.right => v
  have heval :
      (fun a => (σ a).eval f) =
        HPAtom.eval (u.eval f) (v.eval f) := by
    funext a
    cases a <;> rfl
  have hweight :
      (fun a => (σ a).weight wt) =
        HPAtom.weight (u.weight wt) (v.weight wt) := by
    funext a
    cases a <;> rfl
  change
    weightedCommutatorSubgroup p
        (HPAtom.eval (u.eval f) (v.eval f))
        (HPAtom.weight (u.weight wt) (v.weight wt))
        cutoff ≤
      weightedCommutatorSubgroup p f wt cutoff
  rw [← heval, ← hweight]
  exact weighted_commutator_bind f wt σ cutoff

/-- Exact recursive frontier for a prime-power left-conjugate orbit.

The choose-powered factors are already admitted at the final weighted cutoff.  The remaining
unequal-pairwise error part is returned as an explicit cutoff-zero list whose entries retain their
pairwise-error origin.  A complete Hall collector must recursively refine precisely that pending
list; this statement does not discard it inside an opaque normal closure. -/
lemma pairwise_error_admitted
    {p : ℕ} [Fact p.Prime]
    {α : Type*}
    {G : Type*} [Group G]
    {f : α → G}
    {wt : α → ℕ}
    (u v : CWord α)
    (a : ℕ) :
    ∃ E : List (WCFactor p f wt 0),
      (∀ F ∈ E, WCFactor.PERaw u v F) ∧
        ∃ Z :
            List
              (WCFactor p f wt
                (u.weight wt * p ^ a + v.weight wt)),
          WCFactor.listEval E *
              WCFactor.listEval Z =
            leftConjugateProduct
              (u.eval f)
              ⁅u.eval f, v.eval f⁆
              (p ^ a) := by
  rcases
      conjugate_pairwise_comm
        (u.eval f) ⁅u.eval f, v.eval f⁆ (p ^ a) with
    ⟨e, he, z, hz, horbit⟩
  rcases
      WCFactor.pairwise_error_raw
        (p := p) (f := f) (wt := wt) (u := u) (v := v) he with
    ⟨E, hE, hEorigin⟩
  have hzHall :
      z ∈
        weightedPairSubgroup p
          (u.eval f)
          (v.eval f)
          (u.weight wt)
          (v.weight wt)
          (u.weight wt * p ^ a + v.weight wt) :=
    iterated_choose_pair hz
  have hzOriginal :
      z ∈
        weightedCommutatorSubgroup p f wt
          (u.weight wt * p ^ a + v.weight wt) :=
    weighted_pair_word
      f wt u v (u.weight wt * p ^ a + v.weight wt) hzHall
  rcases
      WCFactor.list_eval hzOriginal with
    ⟨Z, hZ⟩
  refine ⟨E, hEorigin, Z, ?_⟩
  rw [hE, hZ, ← horbit]

namespace CWord

/-- Terminal recursive Hall collection for two arbitrary inner commutator words: once every
unequal pairwise error has reached the requested cutoff, collection over the substituted Hall
pair is absorbed by the weighted-power subgroup over the original alphabet. -/
lemma weighted_pairwise_cutoff
    {p : ℕ} [Fact p.Prime]
    {α : Type*}
    {G : Type*} [Group G]
    {f : α → G}
    {wt : α → ℕ}
    {u v : CWord α}
    {a : ℕ}
    (hpair :
      ∀ r s : ℕ, r ≠ s →
        u.weight wt * p ^ a + v.weight wt ≤
          (r + s + 2) * u.weight wt + 2 * v.weight wt) :
    ⁅u.eval f ^ (p ^ a), v.eval f⁆ ∈
      weightedCommutatorSubgroup p f wt
        (u.weight wt * p ^ a + v.weight wt) := by
  apply
    weighted_pair_word
      f wt u v (u.weight wt * p ^ a + v.weight wt)
  exact
    element_pairwise_cutoff
      hpair

/-- Numerical terminal case for recursive Hall collection over arbitrary substituted words. -/
lemma commutator_weighted_three
    {p : ℕ} [Fact p.Prime]
    {α : Type*}
    {G : Type*} [Group G]
    {f : α → G}
    {wt : α → ℕ}
    {u v : CWord α}
    {a : ℕ}
    (hcutoff :
      u.weight wt * p ^ a + v.weight wt ≤
        3 * u.weight wt + 2 * v.weight wt) :
    ⁅u.eval f ^ (p ^ a), v.eval f⁆ ∈
      weightedCommutatorSubgroup p f wt
        (u.weight wt * p ^ a + v.weight wt) := by
  apply
    weighted_pairwise_cutoff
  intro r s hrs
  apply hcutoff.trans
  have hrs_pos : 1 ≤ r + s := by omega
  have hthree : 3 ≤ r + s + 2 := by omega
  exact
    Nat.add_le_add_right
      (Nat.mul_le_mul_right (u.weight wt) hthree)
      (2 * v.weight wt)

/-- Terminal substituted Hall collection can be unpacked into an explicit finite list of admitted
weighted-power factors. -/
lemma list_pairwise_cutoff
    {p : ℕ} [Fact p.Prime]
    {α : Type*}
    {G : Type*} [Group G]
    {f : α → G}
    {wt : α → ℕ}
    {u v : CWord α}
    {a : ℕ}
    (hpair :
      ∀ r s : ℕ, r ≠ s →
        u.weight wt * p ^ a + v.weight wt ≤
          (r + s + 2) * u.weight wt + 2 * v.weight wt) :
    ∃ L :
        List
          (WCFactor p f wt
            (u.weight wt * p ^ a + v.weight wt)),
      WCFactor.listEval L =
        ⁅u.eval f ^ (p ^ a), v.eval f⁆ :=
  WCFactor.list_eval
    (weighted_pairwise_cutoff
      hpair)

/-- Numerical terminal substituted Hall collection also has an explicit admitted-factor list. -/
lemma list_commutator_three
    {p : ℕ} [Fact p.Prime]
    {α : Type*}
    {G : Type*} [Group G]
    {f : α → G}
    {wt : α → ℕ}
    {u v : CWord α}
    {a : ℕ}
    (hcutoff :
      u.weight wt * p ^ a + v.weight wt ≤
        3 * u.weight wt + 2 * v.weight wt) :
    ∃ L :
        List
          (WCFactor p f wt
            (u.weight wt * p ^ a + v.weight wt)),
      WCFactor.listEval L =
        ⁅u.eval f ^ (p ^ a), v.eval f⁆ :=
  WCFactor.list_eval
    (commutator_weighted_three
      hcutoff)

/-- Terminal recursive Hall collection also gives the expected root-Zassenhaus estimate whenever
the original weighted alphabet consists of lower-central elements. -/
lemma commutator_pairwise_cutoff
    {p : ℕ} [Fact p.Prime]
    {α : Type*}
    {G : Type*} [Group G]
    {f : α → G}
    {wt : α → ℕ}
    {u v : CWord α}
    {a : ℕ}
    (hwt : ∀ z, 0 < wt z)
    (hf : ∀ z, f z ∈ Subgroup.lowerCentralSeries G (wt z - 1))
    (hpair :
      ∀ r s : ℕ, r ≠ s →
        u.weight wt * p ^ a + v.weight wt ≤
          (r + s + 2) * u.weight wt + 2 * v.weight wt) :
    ⁅u.eval f ^ (p ^ a), v.eval f⁆ ∈
      zassenhausFiltration p G (u.weight wt * p ^ a + v.weight wt) :=
  weighted_commutator_filtration
    f wt hwt hf (u.weight wt * p ^ a + v.weight wt)
    (weighted_pairwise_cutoff
      hpair)

/-- Numerical terminal case for the root-Zassenhaus estimate over arbitrary substituted words. -/
lemma eval_filtration_three
    {p : ℕ} [Fact p.Prime]
    {α : Type*}
    {G : Type*} [Group G]
    {f : α → G}
    {wt : α → ℕ}
    {u v : CWord α}
    {a : ℕ}
    (hwt : ∀ z, 0 < wt z)
    (hf : ∀ z, f z ∈ Subgroup.lowerCentralSeries G (wt z - 1))
    (hcutoff :
      u.weight wt * p ^ a + v.weight wt ≤
        3 * u.weight wt + 2 * v.weight wt) :
    ⁅u.eval f ^ (p ^ a), v.eval f⁆ ∈
      zassenhausFiltration p G (u.weight wt * p ^ a + v.weight wt) :=
  weighted_commutator_filtration
    f wt hwt hf (u.weight wt * p ^ a + v.weight wt)
    (commutator_weighted_three
      hcutoff)

end CWord

end Towers
