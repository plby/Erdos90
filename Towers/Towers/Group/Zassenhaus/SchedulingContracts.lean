import Towers.Group.Zassenhaus.PositiveDegreeRecipes

/-!
# Batch scheduling contracts for complete Hall-Petresco block families

The nonterminal Hall-Petresco collector must move complete realization
families, not isolated selected words.  Swapping one selected realization
produces one selected correction; it cannot produce the full pairwise
correction family.  The correct local obligation is therefore a batch swap:
move two complete family packets and recursively repacket every correction
created by the concrete word rewrites.

This file states that obligation, proves its soundness under list contexts,
and records the cutoff-defect invariant needed by a recursive constructor.

The file is intentionally not imported by the existing collection proof.
-/

namespace Towers
namespace TCTex
namespace BBSched

open scoped commutatorElement
open HACoeff
open BRSpec

/-- Concrete labelled Hall word used by one fixed counted-family scheduler. -/
abbrev LabelledWord
    (M N : ℕ) :=
  CWord (LabelledAtom M N)

/-- Concrete correction inserted when one labelled word moves rightward. -/
def labelledWordCorrection
    {M N : ℕ}
    (B A : LabelledWord M N) :
    LabelledWord M N :=
  .commutator B A

/-- One exact adjacent concrete-word rewrite. -/
inductive LWStep
    {M N : ℕ} :
    List (LabelledWord M N) → List (LabelledWord M N) → Prop where
  | obstruction
      (P S : List (LabelledWord M N))
      (B A : LabelledWord M N) :
      LWStep
        (P ++ [B, A] ++ S)
        (P ++ [labelledWordCorrection B A, A, B] ++ S)

/-- Finite sequence of exact adjacent concrete-word rewrites. -/
abbrev LWRw
    {M N : ℕ}
    (L R : List (LabelledWord M N)) :
    Prop :=
  Relation.ReflTransGen (@LWStep M N) L R

/-- One concrete labelled-word rewrite preserves ordered evaluation. -/
lemma LWStep.listEval_eq
    {M N : ℕ}
    {L R : List (LabelledWord M N)}
    (h : LWStep L R) :
    labelledListEval R = labelledListEval L := by
  cases h with
  | obstruction P S B A =>
      simp [labelledListEval, List.prod_append, labelledWordCorrection,
        CWord.eval_commutator, commutatorElement_def]
      group

/-- Every finite concrete labelled-word rewrite preserves ordered evaluation. -/
lemma LWRw.listEval_eq
    {M N : ℕ}
    {L R : List (LabelledWord M N)}
    (h : LWRw L R) :
    labelledListEval R = labelledListEval L := by
  induction h with
  | refl =>
      rfl
  | tail hLR hstep ih =>
      exact hstep.listEval_eq.trans ih

/-- A concrete adjacent step remains valid in a list context. -/
lemma LWStep.context
    {M N : ℕ}
    {L R : List (LabelledWord M N)}
    (h : LWStep L R)
    (P S : List (LabelledWord M N)) :
    LWStep (P ++ L ++ S) (P ++ R ++ S) := by
  cases h with
  | obstruction P0 S0 B A =>
      simpa [List.append_assoc] using
        (LWStep.obstruction (P ++ P0) (S0 ++ S) B A)

/-- A finite concrete rewrite remains valid in a list context. -/
lemma LWRw.context
    {M N : ℕ}
    {L R : List (LabelledWord M N)}
    (h : LWRw L R)
    (P S : List (LabelledWord M N)) :
    LWRw (P ++ L ++ S) (P ++ R ++ S) := by
  induction h with
  | refl =>
      exact Relation.ReflTransGen.refl
  | tail hLR hstep ih =>
      exact Relation.ReflTransGen.tail ih (hstep.context P S)

/--
Correct local nonterminal obligation: swap two complete counted-family
packets, recursively collecting the resulting correction histories into
complete packets.
-/
structure CFSwap
    {M N : ℕ}
    (B A : BFam M N) where
  correctionFamilies :
    List (BFam M N)
  rewrites :
    LWRw
      (B.realizations ++ A.realizations)
      (BFam.realizationList correctionFamilies ++
        A.realizations ++ B.realizations)

namespace CFSwap

/-- A complete batch swap preserves the concrete labelled product. -/
lemma labelled_eval
    {M N : ℕ}
    {B A : BFam M N}
    (swap : CFSwap B A) :
    labelledListEval
        (BFam.realizationList swap.correctionFamilies ++
          A.realizations ++ B.realizations) =
      labelledListEval (B.realizations ++ A.realizations) :=
  swap.rewrites.listEval_eq

end CFSwap

/-- One adjacent family-packet move backed by an exact complete batch swap. -/
inductive CFStep
    {M N : ℕ} :
    List (BFam M N) → List (BFam M N) → Prop where
  | obstruction
      (P S : List (BFam M N))
      (B A : BFam M N)
      (swap : CFSwap B A) :
      CFStep
        (P ++ [B, A] ++ S)
        (P ++ swap.correctionFamilies ++ [A, B] ++ S)

/-- Finite sequence of exact complete-family batch moves. -/
abbrev CFRw
    {M N : ℕ}
    (L R : List (BFam M N)) :
    Prop :=
  Relation.ReflTransGen (@CFStep M N) L R

/-- One complete-family move induces an exact concrete labelled-word rewrite. -/
lemma CFStep.realizationList_rewrites
    {M N : ℕ}
    {L R : List (BFam M N)}
    (h : CFStep L R) :
    LWRw
      (BFam.realizationList L)
      (BFam.realizationList R) := by
  cases h with
  | obstruction P S B A swap =>
      simpa [BFam.realizationList, List.flatMap_append,
        List.append_assoc] using
        swap.rewrites.context
          (BFam.realizationList P)
          (BFam.realizationList S)

/-- Every finite complete-family run induces a concrete labelled-word rewrite. -/
lemma CFRw.realizationList_rewrites
    {M N : ℕ}
    {L R : List (BFam M N)}
    (h : CFRw L R) :
    LWRw
      (BFam.realizationList L)
      (BFam.realizationList R) := by
  induction h with
  | refl =>
      exact Relation.ReflTransGen.refl
  | tail hLR hstep ih =>
      exact Relation.ReflTransGen.trans ih hstep.realizationList_rewrites

/--
Cutoff-specific batch swap invariant.  Every recursively emitted complete
family lies strictly above both parents and below the retained cutoff.
-/
structure TCSwap
    {M N : ℕ}
    (n leftWeight rightWeight : ℕ)
    (B A : BFam M N)
    extends CFSwap B A where
  weighted_weight_left :
    ∀ C ∈ correctionFamilies,
      weightedWordWeight leftWeight rightWeight B.recipe <
        weightedWordWeight leftWeight rightWeight C.recipe
  weighted_weight_right :
    ∀ C ∈ correctionFamilies,
      weightedWordWeight leftWeight rightWeight A.recipe <
        weightedWordWeight leftWeight rightWeight C.recipe
  weighted_weight_cutoff :
    ∀ C ∈ correctionFamilies,
      weightedWordWeight leftWeight rightWeight C.recipe < n

namespace TCSwap

/-- Every retained correction family descends from the left parent recipe. -/
lemma correctionDescends_left
    {M N n leftWeight rightWeight : ℕ}
    {B A : BFam M N}
    (swap : TCSwap n leftWeight rightWeight B A)
    {C : BFam M N}
    (hC : C ∈ swap.correctionFamilies) :
    CorrectionDescends n leftWeight rightWeight C.recipe B.recipe := by
  unfold CorrectionDescends cutoffDefect
  have hleft := swap.weighted_weight_left C hC
  have hcutoff := swap.weighted_weight_cutoff C hC
  omega

/-- Every retained correction family descends from the right parent recipe. -/
lemma correctionDescends_right
    {M N n leftWeight rightWeight : ℕ}
    {B A : BFam M N}
    (swap : TCSwap n leftWeight rightWeight B A)
    {C : BFam M N}
    (hC : C ∈ swap.correctionFamilies) :
    CorrectionDescends n leftWeight rightWeight C.recipe A.recipe := by
  unfold CorrectionDescends cutoffDefect
  have hright := swap.weighted_weight_right C hC
  have hcutoff := swap.weighted_weight_cutoff C hC
  omega

end TCSwap

/--
The immediate pairwise correction family has the recipe descent required by
a recursive batch-swap constructor whenever it remains below the cutoff.
-/
lemma recipe_descends_left
    {M N n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (B A : BFam M N)
    (hcutoff :
      weightedWordWeight leftWeight rightWeight (B.correction A).recipe < n) :
    CorrectionDescends n leftWeight rightWeight
      (B.correction A).recipe B.recipe := by
  rw [BFam.recipe_correction] at hcutoff ⊢
  exact descends_left
    hleftWeight hrightWeight B.recipe A.recipe hcutoff

/--
The immediate pairwise correction family also descends from the right parent.
-/
lemma recipe_descends_right
    {M N n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (B A : BFam M N)
    (hcutoff :
      weightedWordWeight leftWeight rightWeight (B.correction A).recipe < n) :
    CorrectionDescends n leftWeight rightWeight
      (B.correction A).recipe A.recipe := by
  rw [BFam.recipe_correction] at hcutoff ⊢
  exact descends_right
    hleftWeight hrightWeight B.recipe A.recipe hcutoff

end BBSched
end TCTex
end Towers

/-!
# Truncated evaluation for complete Hall-Petresco block families

Exact free-group batch rewrites cannot erase corrections.  A finite scheduler
for a nilpotent truncation also needs the semantic terminal move: once the
weight of a correction reaches the cutoff, it evaluates to the identity and
the two parent packets commute.

This file states that quotient-aware batch contract and constructs its
high-weight terminal branch.  It is intentionally not imported by the existing
collection proof.
-/

namespace Towers
namespace TCTex
namespace BFTrunc

open scoped commutatorElement
open HACoeff
open BRSpec
open BBSched

/-- Evaluate collapsed labelled words at an arbitrary Hall pair. -/
def collapsedList
    {M N : ℕ}
    {G : Type*}
    [Group G]
    (x y : G)
    (L : List (CWord (LabelledAtom M N))) :
    G :=
  (L.map fun w => (collapseWord w).eval (HPAtom.eval x y)).prod

@[simp]
lemma collapsed_list_nil
    {M N : ℕ}
    {G : Type*}
    [Group G]
    (x y : G) :
    collapsedList (M := M) (N := N) x y [] = 1 :=
  rfl

@[simp]
lemma collapsed_list_append
    {M N : ℕ}
    {G : Type*}
    [Group G]
    (x y : G)
    (L R : List (CWord (LabelledAtom M N))) :
    collapsedList x y (L ++ R) =
      collapsedList x y L * collapsedList x y R := by
  simp [collapsedList, List.prod_append]

/-- One exact labelled-word rewrite preserves collapsed evaluation at any Hall pair. -/
lemma collapsed_labelled_step
    {M N : ℕ}
    {G : Type*}
    [Group G]
    (x y : G)
    {L R : List (BBSched.LabelledWord M N)}
    (h : BBSched.LWStep L R) :
    collapsedList x y R = collapsedList x y L := by
  cases h with
  | obstruction P S B A =>
      simp [collapsedList, List.prod_append,
        BBSched.labelledWordCorrection,
        collapseWord, CWord.eval_commutator, commutatorElement_def]
      group

/-- Every finite exact labelled-word rewrite preserves arbitrary collapsed evaluation. -/
lemma collapsed_labelled_rewrites
    {M N : ℕ}
    {G : Type*}
    [Group G]
    (x y : G)
    {L R : List (BBSched.LabelledWord M N)}
    (h : BBSched.LWRw L R) :
    collapsedList x y R = collapsedList x y L := by
  induction h with
  | refl =>
      rfl
  | tail hLR hstep ih =>
      exact (collapsed_labelled_step x y hstep).trans ih

/--
Every concrete realization in a complete block family has the weighted
lower-central depth recorded by the family recipe.
-/
lemma BFam.collap_memlo_centr
    {M N leftWeight rightWeight : ℕ}
    {G : Type*}
    [Group G]
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    {x y : G}
    (hx : x ∈ Subgroup.lowerCentralSeries G (leftWeight - 1))
    (hy : y ∈ Subgroup.lowerCentralSeries G (rightWeight - 1))
    (F : BFam M N)
    {w : CWord (LabelledAtom M N)}
    (hw : w ∈ F.realizations) :
    (collapseWord w).eval (HPAtom.eval x y) ∈
      Subgroup.lowerCentralSeries G
        (weightedWordWeight leftWeight rightWeight F.recipe - 1) := by
  have hmem :
      (collapseWord w).eval (HPAtom.eval x y) ∈
        Subgroup.lowerCentralSeries G
          ((collapseWord w).weight
            (HPAtom.weight leftWeight rightWeight) - 1) := by
    apply CWord.eval_lower_series
      (HPAtom.eval x y)
      (HPAtom.weight leftWeight rightWeight)
      (HPAtom.weight_pos hleftWeight hrightWeight)
    intro a
    cases a with
    | left =>
        simpa [HPAtom.eval, HPAtom.weight] using hx
    | right =>
        simpa [HPAtom.eval, HPAtom.weight] using hy
  simpa [weightedWordWeight, F.collapse_word w hw] using hmem

/-- The evaluated product of one complete family lies in its recipe layer. -/
lemma BFam.collap_evalm_lowec
    {M N leftWeight rightWeight : ℕ}
    {G : Type*}
    [Group G]
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    {x y : G}
    (hx : x ∈ Subgroup.lowerCentralSeries G (leftWeight - 1))
    (hy : y ∈ Subgroup.lowerCentralSeries G (rightWeight - 1))
    (F : BFam M N) :
    collapsedList x y F.realizations ∈
      Subgroup.lowerCentralSeries G
        (weightedWordWeight leftWeight rightWeight F.recipe - 1) := by
  apply Subgroup.list_prod_mem
  intro z hz
  rcases List.mem_map.mp hz with ⟨w, hw, rfl⟩
  exact BFam.collap_memlo_centr
    hleftWeight hrightWeight hx hy F hw

/--
At the nilpotent cutoff, complete family products of sufficiently high recipe
weight evaluate trivially.
-/
lemma BFam.collapsedlist_evaleqone_nleweight
    {M N n leftWeight rightWeight : ℕ}
    {G : Type*}
    [Group G]
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    {x y : G}
    (hx : x ∈ Subgroup.lowerCentralSeries G (leftWeight - 1))
    (hy : y ∈ Subgroup.lowerCentralSeries G (rightWeight - 1))
    (hbot : Subgroup.lowerCentralSeries G (n - 1) = ⊥)
    (F : BFam M N)
    (hweight :
      n ≤ weightedWordWeight leftWeight rightWeight F.recipe) :
    collapsedList x y F.realizations = 1 := by
  apply eq_bot_iff.mp hbot
  exact Subgroup.lowerCentralSeries_antitone (Nat.sub_le_sub_right hweight 1)
    (BFam.collap_evalm_lowec
      hleftWeight hrightWeight hx hy F)

/--
The quotient-aware local obligation for a complete-family swap.  The output
families retain only corrections below the cutoff.
-/
structure STSwap
    {M N : ℕ}
    (n leftWeight rightWeight : ℕ)
    (B A : BFam M N) where
  correctionFamilies :
    List (BFam M N)
  collapsed_list_eval :
    ∀ {G : Type*} [Group G]
      (x y : G),
      x ∈ Subgroup.lowerCentralSeries G (leftWeight - 1) →
      y ∈ Subgroup.lowerCentralSeries G (rightWeight - 1) →
      Subgroup.lowerCentralSeries G (n - 1) = ⊥ →
      collapsedList x y
          (BFam.realizationList correctionFamilies ++
            A.realizations ++ B.realizations) =
        collapsedList x y (B.realizations ++ A.realizations)
  weighted_weight_left :
    ∀ C ∈ correctionFamilies,
      weightedWordWeight leftWeight rightWeight B.recipe <
        weightedWordWeight leftWeight rightWeight C.recipe
  weighted_weight_right :
    ∀ C ∈ correctionFamilies,
      weightedWordWeight leftWeight rightWeight A.recipe <
        weightedWordWeight leftWeight rightWeight C.recipe
  weighted_weight_cutoff :
    ∀ C ∈ correctionFamilies,
      weightedWordWeight leftWeight rightWeight C.recipe < n

namespace STSwap

/--
Every exact below-cutoff complete-family batch swap is also a sound semantic
swap in nilpotent quotients.
-/
def ofExact
    {M N n leftWeight rightWeight : ℕ}
    {B A : BFam M N}
    (swap :
      BBSched.TCSwap
        n leftWeight rightWeight B A) :
    STSwap n leftWeight rightWeight B A where
  correctionFamilies := swap.correctionFamilies
  collapsed_list_eval := by
    intro G _ x y _hx _hy _hbot
    exact collapsed_labelled_rewrites x y swap.rewrites
  weighted_weight_left := swap.weighted_weight_left
  weighted_weight_right := swap.weighted_weight_right
  weighted_weight_cutoff := swap.weighted_weight_cutoff

/-- Every retained semantic correction family descends from the left parent recipe. -/
lemma correctionDescends_left
    {M N n leftWeight rightWeight : ℕ}
    {B A : BFam M N}
    (swap :
      STSwap
        n leftWeight rightWeight B A)
    {C : BFam M N}
    (hC : C ∈ swap.correctionFamilies) :
    CorrectionDescends n leftWeight rightWeight C.recipe B.recipe := by
  unfold CorrectionDescends cutoffDefect
  have hleft := swap.weighted_weight_left C hC
  have hcutoff := swap.weighted_weight_cutoff C hC
  omega

/-- Every retained semantic correction family descends from the right parent recipe. -/
lemma correctionDescends_right
    {M N n leftWeight rightWeight : ℕ}
    {B A : BFam M N}
    (swap :
      STSwap
        n leftWeight rightWeight B A)
    {C : BFam M N}
    (hC : C ∈ swap.correctionFamilies) :
    CorrectionDescends n leftWeight rightWeight C.recipe A.recipe := by
  unfold CorrectionDescends cutoffDefect
  have hright := swap.weighted_weight_right C hC
  have hcutoff := swap.weighted_weight_cutoff C hC
  omega

/--
If the first correction weight reaches the cutoff, both complete packet
products commute in every matching nilpotent quotient and no correction family
is retained.
-/
def empty_n_add
    {M N n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (B A : BFam M N)
    (hcutoff :
      n ≤ weightedWordWeight leftWeight rightWeight B.recipe +
        weightedWordWeight leftWeight rightWeight A.recipe) :
    STSwap n leftWeight rightWeight B A where
  correctionFamilies := []
  collapsed_list_eval := by
    intro G _ x y hx hy hbot
    simp only [BFam.realizationList, List.flatMap_nil,
      List.nil_append, collapsed_list_append]
    have hB :=
      BFam.collap_evalm_lowec
        hleftWeight hrightWeight hx hy B
    have hA :=
      BFam.collap_evalm_lowec
        hleftWeight hrightWeight hx hy A
    have hcommutator :
        ⁅collapsedList x y B.realizations,
            collapsedList x y A.realizations⁆ = 1 := by
      apply eq_bot_iff.mp hbot
      exact Subgroup.lowerCentralSeries_antitone (by
          have hBpos :=
            weighted_weight_pos hleftWeight hrightWeight B.recipe
          have hApos :=
            weighted_weight_pos hleftWeight hrightWeight A.recipe
          omega)
        (element_lower_series hB hA)
    exact (commutatorElement_eq_one_iff_commute.mp hcommutator).eq.symm
  weighted_weight_left := by
    intro C hC
    simp at hC
  weighted_weight_right := by
    intro C hC
    simp at hC
  weighted_weight_cutoff := by
    intro C hC
    simp at hC

end STSwap

end BFTrunc
end TCTex
end Towers

/-!
# Quotient-aware complete-family scheduling steps

A finite Hall-Petresco scheduler uses complete block families and evaluates in
a fixed nilpotent truncation.  This file lifts one quotient-aware family swap
into list contexts, proves soundness for finite runs, and exposes the terminal
high-weight step.

The file is intentionally not imported by the existing collection proof.
-/

namespace Towers
namespace TCTex
namespace BTSteps

universe u

open HACoeff
open BRSpec
open BFTrunc

/-- Evaluate a finite list of complete family packets at an arbitrary Hall pair. -/
def collapsedFamilyEval
    {M N : ℕ}
    {G : Type*}
    [Group G]
    (x y : G)
    (families : List (BFam M N)) :
    G :=
  collapsedList x y (BFam.realizationList families)

@[simp]
lemma collapsed_family_nil
    {M N : ℕ}
    {G : Type*}
    [Group G]
    (x y : G) :
    collapsedFamilyEval (M := M) (N := N) x y [] = 1 := by
  simp [collapsedFamilyEval, BFam.realizationList]

@[simp]
lemma collapsed_family_append
    {M N : ℕ}
    {G : Type*}
    [Group G]
    (x y : G)
    (L R : List (BFam M N)) :
    collapsedFamilyEval x y (L ++ R) =
      collapsedFamilyEval x y L * collapsedFamilyEval x y R := by
  simp [collapsedFamilyEval, BFam.realizationList,
    List.flatMap_append]

/-- One adjacent complete-family move in the nilpotent truncation. -/
inductive SCStep
    {M N : ℕ}
    {G : Type u}
    [Group G]
    (x y : G)
    (n leftWeight rightWeight : ℕ) :
    List (BFam M N) → List (BFam M N) → Prop where
  | obstruction
      (P S : List (BFam M N))
      (B A : BFam M N)
      (swap :
        STSwap.{u}
          n leftWeight rightWeight B A) :
      SCStep x y n leftWeight rightWeight
        (P ++ [B, A] ++ S)
        (P ++ swap.correctionFamilies ++ [A, B] ++ S)

/-- Finite quotient-aware complete-family collection run. -/
abbrev SCRwa
    {M N : ℕ}
    {G : Type u}
    [Group G]
    (x y : G)
    (n leftWeight rightWeight : ℕ)
    (L R : List (BFam M N)) :
    Prop :=
  Relation.ReflTransGen
    (SCStep
      (M := M) (N := N) x y n leftWeight rightWeight) L R

/-- One complete-family step preserves collapsed evaluation in the truncation. -/
lemma SCStep.collapsed_famlist_evaleq
    {M N n leftWeight rightWeight : ℕ}
    {G : Type u}
    [Group G]
    {x y : G}
    {L R : List (BFam M N)}
    (h :
      SCStep
        x y n leftWeight rightWeight L R)
    (hx : x ∈ Subgroup.lowerCentralSeries G (leftWeight - 1))
    (hy : y ∈ Subgroup.lowerCentralSeries G (rightWeight - 1))
    (hbot : Subgroup.lowerCentralSeries G (n - 1) = ⊥) :
    collapsedFamilyEval x y R =
      collapsedFamilyEval x y L := by
  cases h with
  | obstruction P S B A swap =>
      have hswap :
          collapsedFamilyEval x y swap.correctionFamilies *
                collapsedFamilyEval x y [A, B] =
            collapsedFamilyEval x y [B, A] := by
        simpa [collapsedFamilyEval, BFam.realizationList,
          List.flatMap_append, List.append_assoc] using
            swap.collapsed_list_eval x y hx hy hbot
      simp only [List.append_assoc, collapsed_family_append]
      calc
        collapsedFamilyEval x y P *
              (collapsedFamilyEval x y swap.correctionFamilies *
                (collapsedFamilyEval x y [A, B] *
                  collapsedFamilyEval x y S)) =
            collapsedFamilyEval x y P *
              ((collapsedFamilyEval x y swap.correctionFamilies *
                  collapsedFamilyEval x y [A, B]) *
                collapsedFamilyEval x y S) := by
          group
        _ =
            collapsedFamilyEval x y P *
              (collapsedFamilyEval x y [B, A] *
                collapsedFamilyEval x y S) := by
          rw [hswap]

/-- Every finite complete-family run preserves collapsed truncated evaluation. -/
lemma SCRwa.collapsed_famlist_evaleq
    {M N n leftWeight rightWeight : ℕ}
    {G : Type u}
    [Group G]
    {x y : G}
    {L R : List (BFam M N)}
    (h :
      SCRwa
        x y n leftWeight rightWeight L R)
    (hx : x ∈ Subgroup.lowerCentralSeries G (leftWeight - 1))
    (hy : y ∈ Subgroup.lowerCentralSeries G (rightWeight - 1))
    (hbot : Subgroup.lowerCentralSeries G (n - 1) = ⊥) :
    collapsedFamilyEval x y R =
      collapsedFamilyEval x y L := by
  induction h with
  | refl =>
      rfl
  | tail hLR hstep ih =>
      exact (hstep.collapsed_famlist_evaleq hx hy hbot).trans ih

/--
At total parent weight at least the cutoff, the family scheduler performs a
terminal adjacent swap without retaining any correction family.
-/
def SCStep.obstrucempty_nle_addweight
    {M N n leftWeight rightWeight : ℕ}
    {G : Type u}
    [Group G]
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (x y : G)
    (P S : List (BFam M N))
    (B A : BFam M N)
    (hcutoff :
      n ≤ weightedWordWeight leftWeight rightWeight B.recipe +
        weightedWordWeight leftWeight rightWeight A.recipe) :
    SCStep x y n leftWeight rightWeight
      (P ++ [B, A] ++ S)
      (P ++ [A, B] ++ S) := by
  simpa using
    SCStep.obstruction P S B A
      (STSwap.empty_n_add
        hleftWeight hrightWeight B A hcutoff)

end BTSteps
end TCTex
end Towers

/-!
# Class-two terminal packets for complete Hall-Petresco block families

Near the nilpotent cutoff, a complete family swap has no room for nested
corrections.  If the leading pairwise correction survives, its full Cartesian
family is the only retained packet.  If it does not survive, the empty terminal
packet from `ProductInverseCollectionBlockFamilyTruncation` applies.

This file is intentionally not imported by the existing collection proof.
-/

namespace Towers
namespace TCTex
namespace CTPacketa

universe u

open scoped commutatorElement
open HACoeff
open BRSpec
open BFTrunc
open BFTrunc.STSwap

/-- Canonical family evaluation is a power of its single erased recipe shape. -/
lemma BFam.collapsed_listeval_eqpow
    {M N : ℕ}
    {G : Type*}
    [Group G]
    (x y : G)
    (F : BFam M N) :
    collapsedList x y F.realizations =
      F.recipe.erasedShape.eval (HPAtom.eval x y) ^
        F.realizations.length := by
  rw [collapsedList]
  have hmap :
      F.realizations.map
          (fun w => (collapseWord w).eval (HPAtom.eval x y)) =
        List.replicate F.realizations.length
          (F.recipe.erasedShape.eval (HPAtom.eval x y)) := by
    simpa using
      (List.eq_replicate_of_mem
        (a := F.recipe.erasedShape.eval (HPAtom.eval x y))
        (l := F.realizations.map
          fun w => (collapseWord w).eval (HPAtom.eval x y))
        (by
          intro z hz
          rcases List.mem_map.mp hz with ⟨w, hw, rfl⟩
          rw [F.collapse_word w hw]))
  rw [hmap, List.prod_replicate]

/-- One erased recipe shape evaluates in its weighted lower-central layer. -/
lemma BRecipe.erased_shape_series
    {leftWeight rightWeight : ℕ}
    {G : Type*}
    [Group G]
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    {x y : G}
    (hx : x ∈ Subgroup.lowerCentralSeries G (leftWeight - 1))
    (hy : y ∈ Subgroup.lowerCentralSeries G (rightWeight - 1))
    (R : BRecipe) :
    R.erasedShape.eval (HPAtom.eval x y) ∈
      Subgroup.lowerCentralSeries G
        (weightedWordWeight leftWeight rightWeight R - 1) := by
  apply CWord.eval_lower_series
    (HPAtom.eval x y)
    (HPAtom.weight leftWeight rightWeight)
    (HPAtom.weight_pos hleftWeight hrightWeight)
  intro a
  cases a with
  | left =>
      simpa [HPAtom.eval, HPAtom.weight] using hx
  | right =>
      simpa [HPAtom.eval, HPAtom.weight] using hy

/--
When both nested correction weights reach the cutoff, the canonical correction
family evaluates to the commutator of the two canonical parent-family products.
-/
lemma BFam.collap_evalc_commc
    {M N n leftWeight rightWeight : ℕ}
    {G : Type*}
    [Group G]
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    {x y : G}
    (hx : x ∈ Subgroup.lowerCentralSeries G (leftWeight - 1))
    (hy : y ∈ Subgroup.lowerCentralSeries G (rightWeight - 1))
    (hbot : Subgroup.lowerCentralSeries G (n - 1) = ⊥)
    (B A : BFam M N)
    (hleft :
      n ≤
        2 * weightedWordWeight leftWeight rightWeight B.recipe +
          weightedWordWeight leftWeight rightWeight A.recipe)
    (hright :
      n ≤
        weightedWordWeight leftWeight rightWeight B.recipe +
          2 * weightedWordWeight leftWeight rightWeight A.recipe) :
    collapsedList x y (B.correction A).realizations =
      ⁅collapsedList x y B.realizations,
        collapsedList x y A.realizations⁆ := by
  let bValue := B.recipe.erasedShape.eval (HPAtom.eval x y)
  let aValue := A.recipe.erasedShape.eval (HPAtom.eval x y)
  let bWeight := weightedWordWeight leftWeight rightWeight B.recipe
  let aWeight := weightedWordWeight leftWeight rightWeight A.recipe
  have hbWeight : 0 < bWeight := by
    simpa [bWeight] using
      weighted_weight_pos hleftWeight hrightWeight B.recipe
  have haWeight : 0 < aWeight := by
    simpa [aWeight] using
      weighted_weight_pos hleftWeight hrightWeight A.recipe
  have hb :
      bValue ∈ Subgroup.lowerCentralSeries G (bWeight - 1) := by
    simpa [bValue, bWeight] using
      BRecipe.erased_shape_series
        hleftWeight hrightWeight hx hy B.recipe
  have ha :
      aValue ∈ Subgroup.lowerCentralSeries G (aWeight - 1) := by
    simpa [aValue, aWeight] using
      BRecipe.erased_shape_series
        hleftWeight hrightWeight hx hy A.recipe
  have hba :
      ⁅bValue, aValue⁆ ∈
        Subgroup.lowerCentralSeries G ((bWeight - 1) + (aWeight - 1) + 1) :=
    element_lower_series hb ha
  have hbba :
      ⁅bValue, ⁅bValue, aValue⁆⁆ ∈
        Subgroup.lowerCentralSeries G
          ((bWeight - 1) + ((bWeight - 1) + (aWeight - 1) + 1) + 1) :=
    element_lower_series hb hba
  have haba :
      ⁅aValue, ⁅bValue, aValue⁆⁆ ∈
        Subgroup.lowerCentralSeries G
          ((aWeight - 1) + ((bWeight - 1) + (aWeight - 1) + 1) + 1) :=
    element_lower_series ha hba
  have hbbaOne : ⁅bValue, ⁅bValue, aValue⁆⁆ = 1 := by
    apply eq_bot_iff.mp hbot
    exact Subgroup.lowerCentralSeries_antitone (by omega) hbba
  have habaOne : ⁅aValue, ⁅bValue, aValue⁆⁆ = 1 := by
    apply eq_bot_iff.mp hbot
    exact Subgroup.lowerCentralSeries_antitone (by omega) haba
  have hbcomm : Commute bValue ⁅bValue, aValue⁆ := by
    exact commutatorElement_eq_one_iff_commute.mp hbbaOne
  have hacomm : Commute aValue ⁅bValue, aValue⁆ := by
    exact commutatorElement_eq_one_iff_commute.mp habaOne
  have hpow :
      ⁅bValue ^ B.realizations.length, aValue ^ A.realizations.length⁆ =
        ⁅bValue, aValue⁆ ^
          (B.realizations.length * A.realizations.length) := by
    have hleftPow :
        ⁅bValue ^ B.realizations.length, aValue⁆ =
          ⁅bValue, aValue⁆ ^ B.realizations.length :=
      element_left_commute hbcomm _
    have hrightComm :
        Commute aValue ⁅bValue ^ B.realizations.length, aValue⁆ := by
      rw [hleftPow]
      exact hacomm.pow_right _
    rw [commutator_element_commute hrightComm, hleftPow,
      pow_mul]
  rw [BFam.collapsed_listeval_eqpow x y B,
    BFam.collapsed_listeval_eqpow x y A,
    BFam.collapsed_listeval_eqpow x y (B.correction A),
    BFam.recipe_correction, BRecipe.erasedShape_corr]
  change
    ⁅bValue, aValue⁆ ^ (B.correction A).realizations.length =
      ⁅bValue ^ B.realizations.length, aValue ^ A.realizations.length⁆
  rw [show
      (B.correction A).realizations.length =
        B.realizations.length * A.realizations.length by
      simp [BFam.correction, List.length_flatMap]]
  exact hpow.symm

namespace STSwap

/--
In the class-two terminal zone, a surviving leading correction is represented
by exactly its complete Cartesian correction family.
-/
def singleton_correction_two
    {M N n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (B A : BFam M N)
    (hcutoff :
      weightedWordWeight leftWeight rightWeight B.recipe +
          weightedWordWeight leftWeight rightWeight A.recipe < n)
    (hleft :
      n ≤
        2 * weightedWordWeight leftWeight rightWeight B.recipe +
          weightedWordWeight leftWeight rightWeight A.recipe)
    (hright :
      n ≤
        weightedWordWeight leftWeight rightWeight B.recipe +
          2 * weightedWordWeight leftWeight rightWeight A.recipe) :
    STSwap n leftWeight rightWeight B A where
  correctionFamilies := [B.correction A]
  collapsed_list_eval := by
    intro G _ x y hx hy hbot
    simp only [BFam.realizationList, List.flatMap_cons, List.flatMap_nil,
      List.append_nil, collapsed_list_append]
    rw [BFam.collap_evalc_commc
      hleftWeight hrightWeight hx hy hbot B A hleft hright]
    simp [commutatorElement_def]
  weighted_weight_left := by
    intro C hC
    rcases List.mem_singleton.mp hC with rfl
    exact weighted_correction_left
      hleftWeight hrightWeight B.recipe A.recipe
  weighted_weight_right := by
    intro C hC
    rcases List.mem_singleton.mp hC with rfl
    exact weighted_correction_right
      hleftWeight hrightWeight B.recipe A.recipe
  weighted_weight_cutoff := by
    intro C hC
    rcases List.mem_singleton.mp hC with rfl
    rw [BFam.recipe_correction, weighted_weight_correction]
    exact hcutoff

/--
In the class-two zone, choose automa between an empty packet and the
singleton complete correction family.
-/
def of_classTwo
    {M N n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (B A : BFam M N)
    (hleft :
      n ≤
        2 * weightedWordWeight leftWeight rightWeight B.recipe +
          weightedWordWeight leftWeight rightWeight A.recipe)
    (hright :
      n ≤
        weightedWordWeight leftWeight rightWeight B.recipe +
          2 * weightedWordWeight leftWeight rightWeight A.recipe) :
    STSwap n leftWeight rightWeight B A :=
  if hcutoff :
      n ≤ weightedWordWeight leftWeight rightWeight B.recipe +
        weightedWordWeight leftWeight rightWeight A.recipe then
    empty_n_add hleftWeight hrightWeight B A hcutoff
  else
    singleton_correction_two hleftWeight hrightWeight B A
      (Nat.lt_of_not_ge hcutoff) hleft hright

/--
If three times the smaller parent recipe weight reaches the cutoff, the
complete-family swap is already in the class-two terminal zone.
-/
def n_three_min
    {M N n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (B A : BFam M N)
    (hterminal :
      n ≤ 3 * min
        (weightedWordWeight leftWeight rightWeight B.recipe)
        (weightedWordWeight leftWeight rightWeight A.recipe)) :
    STSwap n leftWeight rightWeight B A :=
  of_classTwo hleftWeight hrightWeight B A
    (by
      have hminB :
          min
              (weightedWordWeight leftWeight rightWeight B.recipe)
              (weightedWordWeight leftWeight rightWeight A.recipe) ≤
            weightedWordWeight leftWeight rightWeight B.recipe :=
        Nat.min_le_left _ _
      have hminA :
          min
              (weightedWordWeight leftWeight rightWeight B.recipe)
              (weightedWordWeight leftWeight rightWeight A.recipe) ≤
            weightedWordWeight leftWeight rightWeight A.recipe :=
        Nat.min_le_right _ _
      omega)
    (by
      have hminB :
          min
              (weightedWordWeight leftWeight rightWeight B.recipe)
              (weightedWordWeight leftWeight rightWeight A.recipe) ≤
            weightedWordWeight leftWeight rightWeight B.recipe :=
        Nat.min_le_left _ _
      have hminA :
          min
              (weightedWordWeight leftWeight rightWeight B.recipe)
              (weightedWordWeight leftWeight rightWeight A.recipe) ≤
            weightedWordWeight leftWeight rightWeight A.recipe :=
        Nat.min_le_right _ _
      omega)

end STSwap

namespace BTSteps.SCStep

/-- Perform one automatic class-two complete-family swap inside a scheduler run. -/
def obstruction_class_two
    {M N n leftWeight rightWeight : ℕ}
    {G : Type u}
    [Group G]
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (x y : G)
    (P S : List (BFam M N))
    (B A : BFam M N)
    (hleft :
      n ≤
        2 * weightedWordWeight leftWeight rightWeight B.recipe +
          weightedWordWeight leftWeight rightWeight A.recipe)
    (hright :
      n ≤
        weightedWordWeight leftWeight rightWeight B.recipe +
          2 * weightedWordWeight leftWeight rightWeight A.recipe) :
    let swap :
        BFTrunc.STSwap.{u}
          n leftWeight rightWeight B A :=
      STSwap.of_classTwo
        hleftWeight hrightWeight B A hleft hright
    BTSteps.SCStep
      x y n leftWeight rightWeight
      (P ++ [B, A] ++ S)
      (P ++ swap.correctionFamilies ++ [A, B] ++ S) := by
  let swap :
      BFTrunc.STSwap.{u}
        n leftWeight rightWeight B A :=
    STSwap.of_classTwo
      hleftWeight hrightWeight B A hleft hright
  exact
    BTSteps.SCStep.obstruction
      (x := x) (y := y) P S B A swap

end BTSteps.SCStep

end CTPacketa
end TCTex
end Towers
