import Submission.Group.Petresco.ProjectionCollection

/-!
# Petresco's commutator aggregates

This file supplies the reverse collection argument in Propositions 9.2 and
9.3. It is stated for a finite formal word evaluated in an arbitrary group:
if every projection onto fewer than `ℓ` labels is trivial, collection removes
all blocks of index below `ℓ`.
-/

namespace Submission
namespace Edmonton
namespace P1954

universe u v w

variable {G : Type u} [Group G]

private lemma list_prod_single
    {α M : Type*} [Monoid M]
    (l : List α) (a : α) (ha : a ∈ l) (hnodup : l.Nodup)
    (f : α → M)
    (hone : ∀ b ∈ l, b ≠ a → f b = 1) :
    (l.map f).prod = f a := by
  induction l with
  | nil =>
      simp at ha
  | cons b l ih =>
      rw [List.nodup_cons] at hnodup
      simp only [List.mem_cons] at ha
      rcases ha with rfl | ha
      · have htail : (l.map f).prod = 1 := by
          apply List.prod_eq_one
          intro y hy
          obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hy
          apply hone c (by simp [hc])
          intro hca
          exact hnodup.1 (hca ▸ hc)
        simp [htail]
      · have hba : b ≠ a := by
          intro hba
          exact hnodup.1 (hba ▸ ha)
        rw [List.map_cons, List.prod_cons, hone b (by simp) hba, one_mul]
        exact ih ha hnodup.2 fun c hc hca =>
          hone c (by simp [hc]) hca

private lemma list_prod_filter
    {α M : Type*} [Monoid M]
    (l : List α) (P : α → Prop) [DecidablePred P]
    (f : α → M)
    (hone : ∀ a ∈ l, ¬ P a → f a = 1) :
    (l.map f).prod = ((l.filter P).map f).prod := by
  induction l with
  | nil =>
      simp
  | cons a l ih =>
      by_cases ha : P a
      · simp [ha, ih (fun b hb => hone b (by simp [hb]))]
      · simp [ha, hone a (by simp) ha,
          ih (fun b hb => hone b (by simp [hb]))]

private lemma forall₂_rel_of_mem_zip
    {α β : Type*} {R : α → β → Prop}
    {l : List α} {r : List β} (h : List.Forall₂ R l r)
    {a : α} {b : β} (hab : (a, b) ∈ l.zip r) :
    R a b := by
  induction h with
  | nil =>
      simp only [List.zip_nil_right, List.not_mem_nil] at hab
  | cons hhead htail ih =>
      simp only [List.zip_cons_cons, List.mem_cons, Prod.mk.injEq] at hab
      rcases hab with ⟨rfl, rfl⟩ | hab
      · exact hhead
      · exact ih hab

private lemma cardinality_supports_nodup
    (L : Type w) [Fintype L] [DecidableEq L] :
    (cardinalityNonemptySupports L).Nodup := by
  unfold cardinalityNonemptySupports
  rw [List.nodup_mergeSort]
  exact Finset.nodup_toList _

/-- The canonical exact-projected-support blocks of a formal word. -/
noncomputable def projectedCollectedBlocks
    {X : Type v} {L : Type w} [Fintype L] [DecidableEq L]
    (label : X → L) (l : List (FormalCommutator X)) :
    List (List (FormalCommutator X)) :=
  (splitKeySubsets
      (projectedFormalSupport label)
      (cardinalityNonemptySupports L) l).1

omit [Group G] in
/-- The canonical projected-support collection is independent of the
evaluator and preserves the evaluated product under every evaluator. -/
lemma projected_blocks_spec
    {X : Type v} {L : Type w} [Fintype L] [DecidableEq L]
    {H : Type*} [Group H]
    (label : X → L) (l : List (FormalCommutator X)) (f : X → H) :
    List.Forall₂
        (fun S q => ∀ c ∈ q, projectedFormalSupport label c = S)
        (cardinalityNonemptySupports L)
        (projectedCollectedBlocks label l) ∧
      evalFormalWord f (projectedCollectedBlocks label l).flatten =
        evalFormalWord f l := by
  let qr :=
    splitKeySubsets
      (projectedFormalSupport label)
      (cardinalityNonemptySupports L) l
  have h :=
    key_subsets_exact f
      (projectedFormalSupport label)
      (projected_formal_bracket label)
      (projected_formal_nonempty label)
      (cardinalityNonemptySupports L)
      (fun S hS => (cardinality_nonempty_supports S).mpr hS)
      (cardinality_supports_pairwise L) l
  exact ⟨h.1, h.2.2⟩

private lemma formal_flatten_zip
    {X : Type v} {L : Type w}
    (f : X → G)
    {supports : List (Finset L)}
    {blocks : List (List (FormalCommutator X))}
    (hblocks : List.Forall₂ (fun _ _ => True) supports blocks) :
    evalFormalWord f blocks.flatten =
      ((supports.zip blocks).map fun Sq =>
        evalFormalWord f Sq.2).prod := by
  induction hblocks with
  | nil =>
      simp
  | cons _ _ ih =>
      simp [eval_formal_append, ih]

private lemma formal_flatten_prod
    {X : Type v} (f : X → G)
    (blocks : List (List (FormalCommutator X))) :
    evalFormalWord f blocks.flatten =
      (blocks.map (evalFormalWord f)).prod := by
  induction blocks with
  | nil =>
      simp
  | cons q blocks ih =>
      simp [eval_formal_append, ih]

/-- **Petresco 9.2--9.3, reverse collection direction.** If all
projections of a finite formal word onto fewer than `ℓ` labels are trivial,
then its value is a product of commutator forms of index at least `ℓ`. -/
theorem vanishing_aggregate_word
    {X : Type v} {L : Type w} [Finite L] [DecidableEq L]
    (f : X → G) (label : X → L) (ℓ : ℕ)
    (l : List (FormalCommutator X))
    (hvanish :
      ∀ S : Finset L, S.card < ℓ →
        evalFormalWord
          (retainProjectedVariables label S f) l = 1) :
    ∃ q : List (FormalCommutator X),
      (∀ c ∈ q, ℓ ≤ (projectedFormalSupport label c).card) ∧
        evalFormalWord f l = evalFormalWord f q := by
  classical
  letI := Fintype.ofFinite L
  let supports := cardinalityNonemptySupports L
  let blocks := projectedCollectedBlocks label l
  let pairs := supports.zip blocks
  have hblocks :
      List.Forall₂
        (fun S q => ∀ c ∈ q, projectedFormalSupport label c = S)
        supports blocks :=
    (projected_blocks_spec label l f).1
  have hlength : supports.length = blocks.length :=
    hblocks.length_eq
  have hsupportsNodup : supports.Nodup := by
    exact cardinality_supports_nodup L
  have hfst :
      pairs.map Prod.fst = supports := by
    exact List.map_fst_zip (le_of_eq hlength)
  have hpairsNodup : pairs.Nodup := by
    apply List.Nodup.of_map Prod.fst
    rw [hfst]
    exact hsupportsNodup
  have hfstInjective :
      ∀ p ∈ pairs, ∀ q ∈ pairs, p.1 = q.1 → p = q := by
    exact
      (List.nodup_map_iff_inj_on hpairsNodup).mp
        (by simpa [hfst] using hsupportsNodup)
  have hlow :
      ∀ n : ℕ, ∀ S : Finset L, ∀ q : List (FormalCommutator X),
        S.card = n → (S, q) ∈ pairs → n < ℓ →
          evalFormalWord f q = 1 := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro S q hcard hSq hn
        have hprojection :
            evalFormalWord f
                (blocks.flatten.filter fun c =>
                  projectedFormalSupport label c ⊆ S) = 1 := by
          calc
            evalFormalWord f
                (blocks.flatten.filter fun c =>
                  projectedFormalSupport label c ⊆ S) =
                evalFormalWord
                  (retainProjectedVariables label S f)
                  blocks.flatten := by
              symm
              exact formal_projected_variables
                label S f blocks.flatten
            _ = evalFormalWord
                  (retainProjectedVariables label S f) l :=
              (projected_blocks_spec label l
                (retainProjectedVariables label S f)).2
            _ = 1 := hvanish S (by simpa [hcard] using hn)
        have htriangular :
            (pairs.map fun Tq =>
              if Tq.1 ⊆ S
              then evalFormalWord f Tq.2
              else 1).prod = 1 := by
          rw [← filter_flatten_zip
            f (projectedFormalSupport label) S hblocks]
          exact hprojection
        let value : (Finset L × List (FormalCommutator X)) → G :=
          fun Tq =>
            if Tq.1 ⊆ S
            then evalFormalWord f Tq.2
            else 1
        have hone :
            ∀ Tq ∈ pairs, Tq ≠ (S, q) → value Tq = 1 := by
          rintro ⟨T, r⟩ hTr hne
          by_cases hTS : T ⊆ S
          · simp only [value, if_pos hTS]
            by_cases hT_eq : T = S
            · exfalso
              apply hne
              exact hfstInjective (T, r) hTr (S, q) hSq hT_eq
            · have hproper : T ⊂ S :=
                Finset.ssubset_iff_subset_ne.mpr ⟨hTS, hT_eq⟩
              have hlt : T.card < n := by
                rw [← hcard]
                exact Finset.card_lt_card hproper
              exact ih T.card hlt T r rfl hTr (lt_trans hlt hn)
          · simp [value, hTS]
        have hsingle :
            (pairs.map value).prod = value (S, q) :=
          list_prod_single pairs (S, q) hSq hpairsNodup value hone
        have hvalue : value (S, q) = evalFormalWord f q := by
          simp [value]
        rw [show
          (pairs.map fun Tq =>
            if Tq.1 ⊆ S
            then evalFormalWord f Tq.2
            else 1) = pairs.map value by rfl,
          hsingle, hvalue] at htriangular
        exact htriangular
  let highPairs := pairs.filter fun Sq => ℓ ≤ Sq.1.card
  let q : List (FormalCommutator X) :=
    (highPairs.map Prod.snd).flatten
  refine ⟨q, ?_, ?_⟩
  · intro c hc
    change c ∈ (highPairs.map Prod.snd).flatten at hc
    rw [List.mem_flatten] at hc
    obtain ⟨r, hr, hc⟩ := hc
    rw [List.mem_map] at hr
    obtain ⟨Sq, hSq, rfl⟩ := hr
    have hSqFilter :
        Sq ∈ pairs ∧ ℓ ≤ Sq.1.card := by
      simpa [highPairs] using hSq
    have hexact := forall₂_rel_of_mem_zip hblocks hSqFilter.1
    rw [hexact c hc]
    exact hSqFilter.2
  · have hevalBlocks :
        evalFormalWord f blocks.flatten =
          (pairs.map fun Sq => evalFormalWord f Sq.2).prod :=
      formal_flatten_zip f
        (hblocks.imp fun _ _ _ => True.intro)
    have hdrop :
        (pairs.map fun Sq => evalFormalWord f Sq.2).prod =
          (highPairs.map fun Sq => evalFormalWord f Sq.2).prod := by
      apply list_prod_filter
      intro Sq hSq hnotHigh
      apply hlow Sq.1.card Sq.1 Sq.2 rfl hSq
      exact Nat.lt_of_not_ge hnotHigh
    calc
      evalFormalWord f l =
          evalFormalWord f blocks.flatten :=
        (projected_blocks_spec label l f).2.symm
      _ = (pairs.map fun Sq => evalFormalWord f Sq.2).prod :=
        hevalBlocks
      _ = (highPairs.map fun Sq => evalFormalWord f Sq.2).prod :=
        hdrop
      _ = evalFormalWord f q := by
        change
          (highPairs.map fun Sq => evalFormalWord f Sq.2).prod =
            evalFormalWord f (highPairs.map Prod.snd).flatten
        rw [formal_flatten_prod]
        rw [List.map_map]
        rfl

/-- The commutator aggregate evaluated at a labelled family in `G`. -/
def evaluatedCommutatorAggregate
    {X : Type v} {L : Type w} [DecidableEq L]
    (f : X → G) (label : X → L) (ℓ : ℕ) :
    Subgroup G :=
  Subgroup.normalClosure
    {x | ∃ c : FormalCommutator X,
      ℓ ≤ (projectedFormalSupport label c).card ∧
        formalGroupCommutator f c = x}

/-- Evaluated form of Petresco 9.1. -/
theorem evaluated_aggregate_normal
    {X : Type v} {L : Type w} [DecidableEq L]
    (f : X → G) (label : X → L) (ℓ : ℕ) :
    (evaluatedCommutatorAggregate f label ℓ).Normal :=
  Subgroup.normalClosure_normal

/-- Membership form of the reverse inclusion `E^ℓ ≤ O^ℓ` in Petresco
9.2--9.3. -/
theorem aggregate_projection_vanishing
    {X : Type v} {L : Type w} [Finite L] [DecidableEq L]
    (f : X → G) (label : X → L) (ℓ : ℕ)
    (l : List (FormalCommutator X))
    (hvanish :
      ∀ S : Finset L, S.card < ℓ →
        evalFormalWord
          (retainProjectedVariables label S f) l = 1) :
    evalFormalWord f l ∈
      evaluatedCommutatorAggregate f label ℓ := by
  obtain ⟨q, hq, heval⟩ :=
    vanishing_aggregate_word f label ℓ l hvanish
  rw [heval, evalFormalWord]
  apply Subgroup.list_prod_mem
    (evaluatedCommutatorAggregate f label ℓ)
  intro x hx
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hx
  apply Subgroup.subset_normalClosure
  exact ⟨c, hq c hc, rfl⟩

end P1954
end Edmonton
end Submission
