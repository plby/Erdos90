import Submission.Group.HallWords

namespace Submission

/-- One factor admitted by a weighted-power commutator-word subgroup: an arbitrary conjugate
of an integral multiple of a sufficient prime-power power of a commutator word. -/
structure WCFactor
    (p : ℕ)
    {α : Type*}
    {G : Type*} [Group G]
    (f : α → G)
    (wt : α → ℕ)
    (cutoff : ℕ) where
  word : CWord α
  primeExponent : ℕ
  multiplicity : ℤ
  conjugator : G
  weight_bound : cutoff ≤ word.weight wt * p ^ primeExponent

namespace WCFactor

/-- Evaluate one admitted weighted-power factor in the ambient group. -/
def eval
    {p : ℕ}
    {α : Type*}
    {G : Type*} [Group G]
    {f : α → G}
    {wt : α → ℕ}
    {cutoff : ℕ}
    (F : WCFactor p f wt cutoff) :
    G :=
  F.conjugator *
      (F.word.eval f ^ (p ^ F.primeExponent)) ^ F.multiplicity *
    F.conjugator⁻¹

/-- Rebase a factor at a new cutoff after supplying the required weighted-degree bound. -/
def rebase
    {p : ℕ}
    {α : Type*}
    {G : Type*} [Group G]
    {f : α → G}
    {wt : α → ℕ}
    {cutoff cutoff' : ℕ}
    (F : WCFactor p f wt cutoff)
    (hbound : cutoff' ≤ F.word.weight wt * p ^ F.primeExponent) :
    WCFactor p f wt cutoff' where
  word := F.word
  primeExponent := F.primeExponent
  multiplicity := F.multiplicity
  conjugator := F.conjugator
  weight_bound := hbound

@[simp]
lemma eval_rebase
    {p : ℕ}
    {α : Type*}
    {G : Type*} [Group G]
    {f : α → G}
    {wt : α → ℕ}
    {cutoff cutoff' : ℕ}
    (F : WCFactor p f wt cutoff)
    (hbound : cutoff' ≤ F.word.weight wt * p ^ F.primeExponent) :
    (F.rebase hbound).eval = F.eval :=
  rfl

/-- A raw powered commutator factor, represented at cutoff zero before recursive collection has
proved that it reaches a desired positive cutoff. -/
def raw
    {p : ℕ}
    {α : Type*}
    {G : Type*} [Group G]
    {f : α → G}
    {wt : α → ℕ}
    (word : CWord α)
    (primeExponent : ℕ)
    (multiplicity : ℤ)
    (conjugator : G) :
    WCFactor p f wt 0 where
  word := word
  primeExponent := primeExponent
  multiplicity := multiplicity
  conjugator := conjugator
  weight_bound := Nat.zero_le _

@[simp]
lemma eval_raw
    {p : ℕ}
    {α : Type*}
    {G : Type*} [Group G]
    {f : α → G}
    {wt : α → ℕ}
    (word : CWord α)
    (primeExponent : ℕ)
    (multiplicity : ℤ)
    (conjugator : G) :
    (raw (p := p) (f := f) (wt := wt)
      word primeExponent multiplicity conjugator).eval =
        conjugator *
            (word.eval f ^ (p ^ primeExponent)) ^ multiplicity *
          conjugator⁻¹ :=
  rfl

/-- Every admitted weighted-power factor belongs to the weighted-power word subgroup. -/
lemma eval_mem
    {p : ℕ}
    {α : Type*}
    {G : Type*} [Group G]
    {f : α → G}
    {wt : α → ℕ}
    {cutoff : ℕ}
    (F : WCFactor p f wt cutoff) :
    F.eval ∈ weightedCommutatorSubgroup p f wt cutoff := by
  have hbase :
      F.word.eval f ^ (p ^ F.primeExponent) ∈
        weightedCommutatorSubgroup p f wt cutoff :=
    F.word.evalpowprime_powermemweight_powcomworsub
      F.weight_bound
  exact
    (inferInstance :
      (weightedCommutatorSubgroup p f wt cutoff).Normal).conj_mem
        ((F.word.eval f ^ (p ^ F.primeExponent)) ^ F.multiplicity)
        ((weightedCommutatorSubgroup p f wt cutoff).zpow_mem
          hbase F.multiplicity)
        F.conjugator

/-- Evaluate a finite collected list of admitted factors. -/
def listEval
    {p : ℕ}
    {α : Type*}
    {G : Type*} [Group G]
    {f : α → G}
    {wt : α → ℕ}
    {cutoff : ℕ}
    (L : List (WCFactor p f wt cutoff)) :
    G :=
  (L.map eval).prod

@[simp]
lemma listEval_nil
    {p : ℕ}
    {α : Type*}
    {G : Type*} [Group G]
    {f : α → G}
    {wt : α → ℕ}
    {cutoff : ℕ} :
    listEval ([] : List (WCFactor p f wt cutoff)) = 1 :=
  rfl

@[simp]
lemma listEval_cons
    {p : ℕ}
    {α : Type*}
    {G : Type*} [Group G]
    {f : α → G}
    {wt : α → ℕ}
    {cutoff : ℕ}
    (F : WCFactor p f wt cutoff)
    (L : List (WCFactor p f wt cutoff)) :
    listEval (F :: L) = F.eval * listEval L :=
  rfl

@[simp]
lemma listEval_append
    {p : ℕ}
    {α : Type*}
    {G : Type*} [Group G]
    {f : α → G}
    {wt : α → ℕ}
    {cutoff : ℕ}
    (L M : List (WCFactor p f wt cutoff)) :
    listEval (L ++ M) = listEval L * listEval M := by
  simp [listEval]

/-- Promote a list of factors to a new cutoff after proving the weighted-degree bound for every
entry. -/
def listRebase
    {p : ℕ}
    {α : Type*}
    {G : Type*} [Group G]
    {f : α → G}
    {wt : α → ℕ}
    {cutoff cutoff' : ℕ} :
    (L : List (WCFactor p f wt cutoff)) →
      (∀ F ∈ L, cutoff' ≤ F.word.weight wt * p ^ F.primeExponent) →
        List (WCFactor p f wt cutoff')
  | [], _ => []
  | F :: L, hbound =>
      F.rebase (hbound F (by simp)) ::
        listRebase L (fun E hE => hbound E (by simp [hE]))

@[simp]
lemma list_eval_rebase
    {p : ℕ}
    {α : Type*}
    {G : Type*} [Group G]
    {f : α → G}
    {wt : α → ℕ}
    {cutoff cutoff' : ℕ}
    (L : List (WCFactor p f wt cutoff))
    (hbound : ∀ F ∈ L, cutoff' ≤ F.word.weight wt * p ^ F.primeExponent) :
    listEval (listRebase L hbound) = listEval L := by
  induction L with
  | nil =>
      rfl
  | cons F L ih =>
      change
        (F.rebase _).eval * listEval (listRebase L _) =
          F.eval * listEval L
      rw [eval_rebase, ih]

/-- Conjugate one admitted factor while preserving its weighted-power certificate. -/
def conjugate
    {p : ℕ}
    {α : Type*}
    {G : Type*} [Group G]
    {f : α → G}
    {wt : α → ℕ}
    {cutoff : ℕ}
    (a : G)
    (F : WCFactor p f wt cutoff) :
    WCFactor p f wt cutoff :=
  { F with conjugator := a * F.conjugator }

@[simp]
lemma eval_conjugate
    {p : ℕ}
    {α : Type*}
    {G : Type*} [Group G]
    {f : α → G}
    {wt : α → ℕ}
    {cutoff : ℕ}
    (a : G)
    (F : WCFactor p f wt cutoff) :
    (F.conjugate a).eval = a * F.eval * a⁻¹ := by
  simp only [conjugate, eval]
  group

/-- Conjugate every factor in an explicit collected list. -/
def listConjugate
    {p : ℕ}
    {α : Type*}
    {G : Type*} [Group G]
    {f : α → G}
    {wt : α → ℕ}
    {cutoff : ℕ}
    (a : G)
    (L : List (WCFactor p f wt cutoff)) :
    List (WCFactor p f wt cutoff) :=
  L.map (conjugate a)

@[simp]
lemma list_eval_conjugate
    {p : ℕ}
    {α : Type*}
    {G : Type*} [Group G]
    {f : α → G}
    {wt : α → ℕ}
    {cutoff : ℕ}
    (a : G)
    (L : List (WCFactor p f wt cutoff)) :
    listEval (listConjugate a L) = a * listEval L * a⁻¹ := by
  induction L with
  | nil =>
      simp [listConjugate]
  | cons F L ih =>
      change
        (F.conjugate a).eval * listEval (listConjugate a L) =
          a * (F.eval * listEval L) * a⁻¹
      rw [eval_conjugate, ih]
      group

/-- A finite collected list of admitted factors belongs to the weighted-power word subgroup. -/
lemma listEval_mem
    {p : ℕ}
    {α : Type*}
    {G : Type*} [Group G]
    {f : α → G}
    {wt : α → ℕ}
    {cutoff : ℕ}
    (L : List (WCFactor p f wt cutoff)) :
    listEval L ∈ weightedCommutatorSubgroup p f wt cutoff := by
  apply Subgroup.list_prod_mem
  intro z hz
  rcases List.mem_map.mp hz with ⟨F, _hF, rfl⟩
  exact F.eval_mem

/-- Invert one admitted factor without changing its weighted-power certificate. -/
def inv
    {p : ℕ}
    {α : Type*}
    {G : Type*} [Group G]
    {f : α → G}
    {wt : α → ℕ}
    {cutoff : ℕ}
    (F : WCFactor p f wt cutoff) :
    WCFactor p f wt cutoff :=
  { F with multiplicity := -F.multiplicity }

@[simp]
lemma eval_inv
    {p : ℕ}
    {α : Type*}
    {G : Type*} [Group G]
    {f : α → G}
    {wt : α → ℕ}
    {cutoff : ℕ}
    (F : WCFactor p f wt cutoff) :
    F.inv.eval = F.eval⁻¹ := by
  simp [inv, eval, mul_assoc]

/-- Reverse and invert a collected list so that its evaluation is the inverse product. -/
def listInv
    {p : ℕ}
    {α : Type*}
    {G : Type*} [Group G]
    {f : α → G}
    {wt : α → ℕ}
    {cutoff : ℕ}
    (L : List (WCFactor p f wt cutoff)) :
    List (WCFactor p f wt cutoff) :=
  match L with
  | [] => []
  | F :: L => listInv L ++ [F.inv]

@[simp]
lemma list_eval_inv
    {p : ℕ}
    {α : Type*}
    {G : Type*} [Group G]
    {f : α → G}
    {wt : α → ℕ}
    {cutoff : ℕ}
    (L : List (WCFactor p f wt cutoff)) :
    listEval (listInv L) = (listEval L)⁻¹ := by
  induction L with
  | nil =>
      simp [listInv]
  | cons F L ih =>
      simp [listInv, ih]

/-- Repeat a collected list a natural number of times. -/
def listPow
    {p : ℕ}
    {α : Type*}
    {G : Type*} [Group G]
    {f : α → G}
    {wt : α → ℕ}
    {cutoff : ℕ}
    (L : List (WCFactor p f wt cutoff)) :
    ℕ → List (WCFactor p f wt cutoff)
  | 0 => []
  | n + 1 => listPow L n ++ L

@[simp]
lemma list_pow
    {p : ℕ}
    {α : Type*}
    {G : Type*} [Group G]
    {f : α → G}
    {wt : α → ℕ}
    {cutoff : ℕ}
    (L : List (WCFactor p f wt cutoff))
    (n : ℕ) :
    listEval (listPow L n) = (listEval L) ^ n := by
  induction n with
  | zero =>
      simp [listPow]
  | succ n ih =>
      simp [listPow, ih, pow_succ]

/-- Repeat or invert a collected list according to an integral multiplicity. -/
def listZpow
    {p : ℕ}
    {α : Type*}
    {G : Type*} [Group G]
    {f : α → G}
    {wt : α → ℕ}
    {cutoff : ℕ}
    (L : List (WCFactor p f wt cutoff)) :
    ℤ → List (WCFactor p f wt cutoff)
  | Int.ofNat n => listPow L n
  | Int.negSucc n => listInv (listPow L (n + 1))

@[simp]
lemma list_eval_zpow
    {p : ℕ}
    {α : Type*}
    {G : Type*} [Group G]
    {f : α → G}
    {wt : α → ℕ}
    {cutoff : ℕ}
    (L : List (WCFactor p f wt cutoff))
    (n : ℤ) :
    listEval (listZpow L n) = (listEval L) ^ n := by
  cases n with
  | ofNat n =>
      simp [listZpow]
  | negSucc n =>
      simp [listZpow]

/-- Replace one evaluated factor by an explicitly collected list for its powered base while
preserving its outer conjugator and integral multiplicity. -/
lemma list_eval_pow
    {p : ℕ}
    {α : Type*}
    {G : Type*} [Group G]
    {f : α → G}
    {wt : α → ℕ}
    {cutoff : ℕ}
    (F : WCFactor p f wt cutoff)
    (L : List (WCFactor p f wt cutoff))
    (hL : listEval L = F.word.eval f ^ (p ^ F.primeExponent)) :
    ∃ M : List (WCFactor p f wt cutoff),
      listEval M = F.eval := by
  refine ⟨listConjugate F.conjugator (listZpow L F.multiplicity), ?_⟩
  simp [hL, eval]

/-- Splice an explicit replacement list into a larger collected product. -/
lemma listEval_replace
    {p : ℕ}
    {α : Type*}
    {G : Type*} [Group G]
    {f : α → G}
    {wt : α → ℕ}
    {cutoff : ℕ}
    (L M R : List (WCFactor p f wt cutoff))
    (F : WCFactor p f wt cutoff)
    (hR : listEval R = F.eval) :
    listEval (L ++ R ++ M) = listEval (L ++ F :: M) := by
  simp [hR]

/-- Membership in the weighted-power subgroup can be unpacked as a finite product of admitted
factors.  This is the explicit normal-closure representation used by recursive Hall collection. -/
lemma list_eval
    {p : ℕ}
    {α : Type*}
    {G : Type*} [Group G]
    {f : α → G}
    {wt : α → ℕ}
    {cutoff : ℕ}
    {g : G}
    (hg : g ∈ weightedCommutatorSubgroup p f wt cutoff) :
    ∃ L : List (WCFactor p f wt cutoff),
      listEval L = g := by
  change
    g ∈ Subgroup.closure
      (Group.conjugatesOfSet
        { z : G |
          ∃ (w : CWord α) (e : ℕ),
            cutoff ≤ w.weight wt * p ^ e ∧
              w.eval f ^ (p ^ e) = z }) at hg
  induction hg using Subgroup.closure_induction with
  | mem z hz =>
      rcases Group.mem_conjugatesOfSet_iff.mp hz with ⟨x, hx, hconj⟩
      rcases hx with ⟨w, e, hweight, rfl⟩
      rcases isConj_iff.mp hconj with ⟨c, rfl⟩
      let F : WCFactor p f wt cutoff :=
        { word := w
          primeExponent := e
          multiplicity := 1
          conjugator := c
          weight_bound := hweight }
      refine ⟨[F], ?_⟩
      simp [F, eval]
  | one =>
      exact ⟨[], rfl⟩
  | mul x y _hx _hy ihx ihy =>
      rcases ihx with ⟨L, hL⟩
      rcases ihy with ⟨M, hM⟩
      exact ⟨L ++ M, by simp [hL, hM]⟩
  | inv x _hx ih =>
      rcases ih with ⟨L, hL⟩
      exact ⟨listInv L, by simp [hL]⟩

end WCFactor

end Submission
