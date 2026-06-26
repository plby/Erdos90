import Submission.Group.Petresco.CommutatorAggregates
import Submission.Group.Petresco.SubstitutionsAndWords

/-!
# Petresco's finite families of subgroups

This file gives literal family-of-subgroups versions of Petresco's
Propositions 8.1 and 9.1--9.3.  A letter records both its index and an
arbitrary element of the corresponding subgroup, so inverses and products
inside one member of the family are available exactly as in the paper.
-/

namespace Submission
namespace Edmonton
namespace P1954

universe u v

variable {G : Type u} [Group G]
variable {L : Type v}

/-- A letter chosen from one member of a family of subgroups. -/
abbrev FamilyLetter (A : L → Subgroup G) :=
  Σ i : L, A i

/-- The index of a family letter. -/
def familyLetterLabel {A : L → Subgroup G} :
    FamilyLetter A → L :=
  Sigma.fst

/-- The ambient group value of a family letter. -/
def familyLetterValue {A : L → Subgroup G} :
    FamilyLetter A → G :=
  fun x => x.2

/-- Inversion of a family letter stays in the same member of the family. -/
def familyLetterInv {A : L → Subgroup G}
    (x : FamilyLetter A) : FamilyLetter A :=
  ⟨x.1, x.2⁻¹⟩

@[simp]
lemma letter_label_inv {A : L → Subgroup G}
    (x : FamilyLetter A) :
    familyLetterLabel (familyLetterInv x) = familyLetterLabel x :=
  rfl

@[simp]
lemma family_letter_inv {A : L → Subgroup G}
    (x : FamilyLetter A) :
    familyLetterValue (familyLetterInv x) =
      (familyLetterValue x)⁻¹ :=
  rfl

/-- A finite word in elements drawn from the members of `A`. -/
abbrev FamilyWord (A : L → Subgroup G) :=
  List (FamilyLetter A)

/-- The value of a family word. -/
def familyWordValue {A : L → Subgroup G}
    (w : FamilyWord A) : G :=
  (w.map familyLetterValue).prod

/-- The value after deleting every letter whose index is not in `S`. -/
def familyWordProjection [DecidableEq L] {A : L → Subgroup G}
    (S : Finset L) (w : FamilyWord A) : G :=
  (w.map
    (retainProjectedVariables familyLetterLabel S familyLetterValue)).prod

/-- The inverse word, with every inverse retained in its original family
member. -/
def familyWordInv {A : L → Subgroup G}
    (w : FamilyWord A) : FamilyWord A :=
  (w.map familyLetterInv).reverse

@[simp]
lemma family_value_nil {A : L → Subgroup G} :
    familyWordValue (A := A) [] = 1 :=
  rfl

@[simp]
lemma family_value_append {A : L → Subgroup G}
    (u w : FamilyWord A) :
    familyWordValue (u ++ w) =
      familyWordValue u * familyWordValue w := by
  simp [familyWordValue]

@[simp]
lemma family_projection_nil [DecidableEq L]
    {A : L → Subgroup G} (S : Finset L) :
    familyWordProjection (A := A) S [] = 1 :=
  rfl

@[simp]
lemma family_projection_append [DecidableEq L]
    {A : L → Subgroup G} (S : Finset L)
    (u w : FamilyWord A) :
    familyWordProjection S (u ++ w) =
      familyWordProjection S u * familyWordProjection S w := by
  simp [familyWordProjection]

@[simp]
lemma family_value_inv {A : L → Subgroup G}
    (w : FamilyWord A) :
    familyWordValue (familyWordInv w) =
      (familyWordValue w)⁻¹ := by
  unfold familyWordInv familyWordValue
  rw [List.map_reverse, List.prod_inv_reverse]
  congr 1
  rw [List.map_map, List.map_map]
  apply congrArg List.reverse
  apply List.map_congr_left
  intro x hx
  rfl

@[simp]
lemma family_projection_inv [DecidableEq L]
    {A : L → Subgroup G} (S : Finset L) (w : FamilyWord A) :
    familyWordProjection S (familyWordInv w) =
      (familyWordProjection S w)⁻¹ := by
  classical
  unfold familyWordProjection familyWordInv
  rw [List.map_reverse]
  rw [List.prod_inv_reverse]
  congr 1
  rw [List.map_map, List.map_map]
  apply congrArg List.reverse
  apply List.map_congr_left
  intro x hx
  by_cases hlabel : familyLetterLabel x ∈ S
  · simp [retainProjectedVariables, hlabel]
  · simp [retainProjectedVariables, hlabel]

/-- Regard a raw family word as a product of weight-one formal
commutators. -/
def familyWordFormalization {A : L → Subgroup G}
    (w : FamilyWord A) : List (FormalCommutator (FamilyLetter A)) :=
  w.map FreeMagma.of

lemma eval_family_formalization {A : L → Subgroup G}
    (w : FamilyWord A) :
    evalFormalWord familyLetterValue
        (familyWordFormalization w) =
      familyWordValue w := by
  unfold familyWordFormalization familyWordValue evalFormalWord
  rw [List.map_map]
  congr 1

lemma projected_family_formalization [DecidableEq L]
    {A : L → Subgroup G} (S : Finset L) (w : FamilyWord A) :
    evalFormalWord
        (retainProjectedVariables
          familyLetterLabel S familyLetterValue)
        (familyWordFormalization w) =
      familyWordProjection S w := by
  unfold familyWordFormalization familyWordProjection evalFormalWord
  rw [List.map_map]
  congr 1

/-- Expand a formal commutator into the raw group word obtained from
`[x,y] = x⁻¹y⁻¹xy`. -/
def expandFormalCommutator {A : L → Subgroup G} :
    FormalCommutator (FamilyLetter A) → FamilyWord A
  | FreeMagma.of x => [x]
  | FreeMagma.mul a b =>
      familyWordInv (expandFormalCommutator a) ++
        familyWordInv (expandFormalCommutator b) ++
          expandFormalCommutator a ++ expandFormalCommutator b

lemma expand_formal_commutator
    {A : L → Subgroup G}
    (c : FormalCommutator (FamilyLetter A)) :
    familyWordValue (expandFormalCommutator c) =
      formalGroupCommutator familyLetterValue c := by
  induction c with
  | of x =>
      simp [expandFormalCommutator, familyWordValue,
        familyLetterValue]
  | mul a b iha ihb =>
      change
        familyWordValue (expandFormalCommutator (a * b)) =
          hallCommutator
            (formalGroupCommutator familyLetterValue a)
            (formalGroupCommutator familyLetterValue b)
      simp [expandFormalCommutator, iha, ihb, hallCommutator,
        mul_assoc]

lemma projection_expand_formal
    [DecidableEq L] {A : L → Subgroup G}
    (S : Finset L) (c : FormalCommutator (FamilyLetter A)) :
    familyWordProjection S (expandFormalCommutator c) =
      formalGroupCommutator
        (retainProjectedVariables
          familyLetterLabel S familyLetterValue) c := by
  induction c with
  | of x =>
      simp [expandFormalCommutator, familyWordProjection]
  | mul a b iha ihb =>
      change
        familyWordProjection S (expandFormalCommutator (a * b)) =
          hallCommutator
            (formalGroupCommutator
              (retainProjectedVariables
                familyLetterLabel S familyLetterValue) a)
            (formalGroupCommutator
              (retainProjectedVariables
                familyLetterLabel S familyLetterValue) b)
      simp [expandFormalCommutator, iha, ihb, hallCommutator,
        mul_assoc]

/-- The subgroup generated by a finite family of subgroups. -/
def familyJoin (A : L → Subgroup G) : Subgroup G :=
  ⨆ i, A i

lemma family_value_join
    {A : L → Subgroup G} (w : FamilyWord A) :
    familyWordValue w ∈ familyJoin A := by
  unfold familyWordValue familyJoin
  apply Subgroup.list_prod_mem
  intro x hx
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hx
  exact Subgroup.mem_iSup_of_mem a.1 a.2.2

private lemma family_value_aux
    (A : L → Subgroup G) {x : G} (hx : x ∈ familyJoin A) :
    ∃ w : FamilyWord A, familyWordValue w = x := by
  unfold familyJoin at hx
  refine Subgroup.iSup_induction A
    (C := fun y => ∃ w : FamilyWord A, familyWordValue w = y)
    hx ?_ ?_ ?_
  · intro i y hy
    exact
      ⟨[⟨i, ⟨y, hy⟩⟩],
        by simp [familyWordValue, familyLetterValue]⟩
  · exact ⟨[], by simp⟩
  · rintro y z ⟨u, hu⟩ ⟨w, hw⟩
    exact ⟨u ++ w, by simp [hu, hw]⟩

/-- A family letter, regarded as an element of the subgroup generated by
the whole family. -/
def familyFactorLetter {A : L → Subgroup G}
    (x : FamilyLetter A) : familyJoin A :=
  ⟨familyLetterValue x,
    Subgroup.mem_iSup_of_mem x.1 x.2.2⟩

/-- A raw family word, regarded as a list in the subgroup generated by the
whole family. -/
def familyFactorLetters {A : L → Subgroup G}
    (w : FamilyWord A) : List (familyJoin A) :=
  w.map familyFactorLetter

@[simp]
lemma coe_letters_prod {A : L → Subgroup G}
    (w : FamilyWord A) :
    ((familyFactorLetters w).prod : G) = familyWordValue w := by
  rw [SubmonoidClass.coe_list_prod]
  unfold familyFactorLetters familyWordValue
  rw [List.map_map]
  congr 1

/-- The subword consisting of the letters from one member of the family. -/
def familyWordLabel [DecidableEq L] {A : L → Subgroup G}
    (i : L) (w : FamilyWord A) : FamilyWord A :=
  w.filter fun x => familyLetterLabel x == i

lemma family_label_projection
    [DecidableEq L] {A : L → Subgroup G}
    (i : L) (w : FamilyWord A) :
    familyWordValue (familyWordLabel i w) =
      familyWordProjection {i} w := by
  change
    (List.map familyLetterValue
      (w.filter fun x => familyLetterLabel x == i)).prod =
      (List.map
        (retainProjectedVariables
          familyLetterLabel {i} familyLetterValue) w).prod
  induction w with
  | nil =>
      rfl
  | cons x w ih =>
      by_cases hxi : familyLetterLabel x = i
      · simp [retainProjectedVariables, hxi, ih]
      · simp [retainProjectedVariables, hxi, ih]

lemma family_projection_singleton
    [DecidableEq L] {A : L → Subgroup G}
    (i : L) (w : FamilyWord A) :
    familyWordProjection {i} w ∈ A i := by
  induction w with
  | nil =>
      simp
  | cons x w ih =>
      by_cases hxi : familyLetterLabel x = i
      · subst i
        simpa [familyWordProjection, retainProjectedVariables] using
          (A x.1).mul_mem x.2.2 ih
      · simpa [familyWordProjection, retainProjectedVariables, hxi]
          using ih

/-- Collect a family word by the specified order of its labels. -/
def groupedFamilyWord [DecidableEq L] {A : L → Subgroup G}
    (labels : List L) (w : FamilyWord A) : FamilyWord A :=
  labels.flatMap fun i => familyWordLabel i w

private lemma perm_grouped_labels
    [DecidableEq L] {A : L → Subgroup G}
    (labels : List L) (hnodup : labels.Nodup)
    (w : FamilyWord A)
    (hlabels : ∀ x ∈ w, familyLetterLabel x ∈ labels) :
    w.Perm (groupedFamilyWord labels w) := by
  induction labels generalizing w with
  | nil =>
      have hw : w = [] := by
        cases w with
        | nil => rfl
        | cons x w =>
            simpa using hlabels x (by simp)
      subst w
      simp [groupedFamilyWord]
  | cons i labels ih =>
      rw [List.nodup_cons] at hnodup
      let wi : FamilyWord A := familyWordLabel i w
      let wrest : FamilyWord A :=
        w.filter fun x => !(familyLetterLabel x == i)
      have hsplit : w.Perm (wi ++ wrest) := by
        exact (List.filter_append_perm
          (fun x => familyLetterLabel x == i) w).symm
      have hrestlabels :
          ∀ x ∈ wrest, familyLetterLabel x ∈ labels := by
        intro x hx
        have hxw : x ∈ w := List.mem_of_mem_filter hx
        have hxne : familyLetterLabel x ≠ i := by
          apply beq_eq_false_iff_ne.mp
          simpa using List.of_mem_filter hx
        have hxmem := hlabels x hxw
        simp only [List.mem_cons] at hxmem
        exact hxmem.resolve_left hxne
      have hrest :
          wrest.Perm (groupedFamilyWord labels wrest) :=
        ih hnodup.2 wrest hrestlabels
      have hfilter :
          groupedFamilyWord labels wrest =
            groupedFamilyWord labels w := by
        unfold groupedFamilyWord familyWordLabel wrest
        apply List.flatMap_congr
        intro j hj
        rw [List.filter_filter]
        apply List.filter_congr
        intro x
        have hji : j ≠ i := by
          intro h
          subst j
          exact hnodup.1 hj
        by_cases hxj : familyLetterLabel x = j
        · simp [hxj, hji]
        · simp [hxj]
      calc
        w.Perm (wi ++ wrest) := hsplit
        _ |>.Perm (wi ++ groupedFamilyWord labels wrest) :=
          hrest.append_left wi
        _ = groupedFamilyWord (i :: labels) w := by
          change
            wi ++ groupedFamilyWord labels wrest =
              familyWordLabel i w ++ groupedFamilyWord labels w
          rw [hfilter]

lemma family_perm_grouped
    [Fintype L] [DecidableEq L] {A : L → Subgroup G}
    (w : FamilyWord A) :
    w.Perm (groupedFamilyWord Finset.univ.toList w) := by
  apply perm_grouped_labels
    Finset.univ.toList Finset.univ.nodup_toList w
  intro x hx
  exact Finset.mem_toList.mpr (Finset.mem_univ (familyLetterLabel x))

lemma family_value_grouped
    [DecidableEq L] {A : L → Subgroup G}
    (labels : List L) (w : FamilyWord A) :
    familyWordValue (groupedFamilyWord labels w) =
      (labels.map fun i => familyWordProjection {i} w).prod := by
  induction labels with
  | nil =>
      simp [groupedFamilyWord]
  | cons i labels ih =>
      change
        familyWordValue
            (familyWordLabel i w ++
              groupedFamilyWord labels w) =
          familyWordProjection {i} w *
            (labels.map fun j => familyWordProjection {j} w).prod
      rw [family_value_append,
        family_label_projection, ih]

/-- The finite-family extension stated immediately after Petresco 2.1.
The derived subgroup of the join consists exactly of family words whose
projection to each member lies in that member's derived subgroup. -/
theorem family_join_membership
    [Finite L] [DecidableEq L] (A : L → Subgroup G) (x : G) :
    x ∈ ⁅familyJoin A, familyJoin A⁆ ↔
      ∃ w : FamilyWord A,
        familyWordValue w = x ∧
          ∀ i : L,
            familyWordProjection {i} w ∈ ⁅A i, A i⁆ := by
  letI := Fintype.ofFinite L
  constructor
  · intro hx
    rw [Subgroup.commutator_def] at hx
    induction hx using Subgroup.closure_induction with
    | mem z hz =>
        obtain ⟨y, hy, t, ht, rfl⟩ := hz
        obtain ⟨u, hu⟩ := family_value_aux A hy
        obtain ⟨w, hw⟩ := family_value_aux A ht
        refine
          ⟨u ++ w ++ familyWordInv u ++ familyWordInv w,
            ?_, ?_⟩
        · simp [hu, hw, commutatorElement_def, mul_assoc]
        · intro i
          have hcomm :=
            Subgroup.commutator_mem_commutator
              (family_projection_singleton i u)
              (family_projection_singleton i w)
          simpa [commutatorElement_def, mul_assoc] using hcomm
    | one =>
        exact ⟨[], by simp, by simp⟩
    | mul y z _ _ hy hz =>
        obtain ⟨u, hu, hpu⟩ := hy
        obtain ⟨w, hw, hpw⟩ := hz
        exact
          ⟨u ++ w, by simp [hu, hw], fun i => by
            simpa using (⁅A i, A i⁆ : Subgroup G).mul_mem
              (hpu i) (hpw i)⟩
    | inv y _ hy =>
        obtain ⟨w, hw, hpw⟩ := hy
        exact
          ⟨familyWordInv w, by simp [hw], fun i => by
            simpa using (⁅A i, A i⁆ : Subgroup G).inv_mem (hpw i)⟩
  · rintro ⟨w, rfl, hprojection⟩
    let H : Subgroup G := familyJoin A
    let labels : List L := Finset.univ.toList
    have hdiff :
        familyWordValue w *
            (familyWordValue (groupedFamilyWord labels w))⁻¹ ∈
          ⁅H, H⁆ := by
      have hperm :
          (familyFactorLetters w).Perm
            (familyFactorLetters
              (groupedFamilyWord labels w)) :=
        (family_perm_grouped w).map familyFactorLetter
      have h :=
        coe_inv_perm hperm
      dsimp [H, labels] at h ⊢
      rw [← coe_letters_prod w,
        ← coe_letters_prod
          (groupedFamilyWord Finset.univ.toList w)]
      exact h
    have hgrouped :
        familyWordValue (groupedFamilyWord labels w) ∈ ⁅H, H⁆ := by
      rw [family_value_grouped]
      apply Subgroup.list_prod_mem
      intro y hy
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hy
      exact
        (Subgroup.commutator_mono
          (show A i ≤ H from le_iSup A i)
          (show A i ≤ H from le_iSup A i))
          (hprojection i)
    have hvalue := (⁅H, H⁆ : Subgroup G).mul_mem hdiff hgrouped
    simpa [H, mul_assoc] using hvalue

/-- Petresco's `E^μ(A₁,...,Aν)`: values of raw family words whose
projections onto fewer than `μ` indices are all trivial. -/
def familyProjectionVanishing
    [DecidableEq L] (A : L → Subgroup G) (μ : ℕ) :
    Subgroup G where
  carrier := {x |
    ∃ w : FamilyWord A,
      familyWordValue w = x ∧
        ∀ S : Finset L, S.card < μ →
          familyWordProjection S w = 1}
  one_mem' := ⟨[], by simp⟩
  mul_mem' := by
    rintro x y ⟨u, hu, hpu⟩ ⟨w, hw, hpw⟩
    refine ⟨u ++ w, by simp [hu, hw], ?_⟩
    intro S hS
    simp [hpu S hS, hpw S hS]
  inv_mem' := by
    rintro x ⟨w, hw, hpw⟩
    refine ⟨familyWordInv w, by simp [hw], ?_⟩
    intro S hS
    simp [hpw S hS]

lemma family_projection_vanishing
    [DecidableEq L] (A : L → Subgroup G) (μ : ℕ) (x : G) :
    x ∈ familyProjectionVanishing A μ ↔
      ∃ w : FamilyWord A,
        familyWordValue w = x ∧
          ∀ S : Finset L, S.card < μ →
            familyWordProjection S w = 1 :=
  Iff.rfl

lemma projection_vanishing_join
    [DecidableEq L] (A : L → Subgroup G) (μ : ℕ) :
    familyProjectionVanishing A μ ≤ familyJoin A := by
  rintro x ⟨w, rfl, _⟩
  exact family_value_join w

/-- Petresco's defining boundary case `E¹ = A₁ ∪ ⋯ ∪ Aν`. -/
theorem projection_vanishing_one
    [DecidableEq L] (A : L → Subgroup G) :
    familyProjectionVanishing A 1 = familyJoin A := by
  apply le_antisymm
  · exact projection_vanishing_join A 1
  · intro x hx
    obtain ⟨w, hw⟩ := family_value_aux A hx
    refine ⟨w, hw, ?_⟩
    intro S hS
    have hSempty : S = ∅ := Finset.card_eq_zero.mp (by omega)
    subst S
    unfold familyWordProjection
    apply List.prod_eq_one
    intro y hy
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hy
    simp [retainProjectedVariables]

/-- The projection-vanishing subgroups form Petresco's descending chain. -/
lemma projection_vanishing_antitone
    [DecidableEq L] (A : L → Subgroup G) :
    Antitone (familyProjectionVanishing A) := by
  intro μ ν hμν x hx
  obtain ⟨w, hw, hprojection⟩ := hx
  exact ⟨w, hw, fun S hS => hprojection S (hS.trans_le hμν)⟩

private lemma conjugate_family_word
    [DecidableEq L] {A : L → Subgroup G} {μ : ℕ}
    (a : FamilyLetter A) {x : G}
    (hx : x ∈ familyProjectionVanishing A μ) :
    familyLetterValue a * x * (familyLetterValue a)⁻¹ ∈
      familyProjectionVanishing A μ := by
  obtain ⟨w, rfl, hw⟩ := hx
  refine
    ⟨[a] ++ w ++ [familyLetterInv a],
      by simp [familyWordValue, mul_assoc],
      ?_⟩
  intro S hS
  rw [family_projection_append, family_projection_append,
    hw S hS]
  by_cases ha : familyLetterLabel a ∈ S
  · simp [familyWordProjection, retainProjectedVariables, ha]
  · simp [familyWordProjection, retainProjectedVariables, ha]

/-- **Petresco 8.1, literal family form.** `E^μ` is normal in the
subgroup generated by the family. -/
theorem family_vanishing_normal
    [DecidableEq L] (A : L → Subgroup G) (μ : ℕ) :
    ((familyProjectionVanishing A μ).subgroupOf
      (familyJoin A)).Normal := by
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer
    (projection_vanishing_join A μ)]
  unfold familyJoin
  refine iSup_le fun i => ?_
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    exact conjugate_family_word
      (A := A) ⟨i, g, hg⟩ hx
  · intro hx
    have hback :=
      conjugate_family_word
        (A := A) ⟨i, g⁻¹, (A i).inv_mem hg⟩ hx
    change g⁻¹ * (g * x * g⁻¹) * (g⁻¹)⁻¹ ∈
      familyProjectionVanishing A μ at hback
    simpa [mul_assoc] using hback

/-- **Petresco 8.3, literal family form.** The value of a commutator form
belongs to `E^ℓ` whenever it involves at least `ℓ` distinct family
indices. -/
theorem formal_family_vanishing
    [DecidableEq L] (A : L → Subgroup G) (ℓ : ℕ)
    (c : FormalCommutator (FamilyLetter A))
    (hℓ : ℓ ≤ (projectedFormalSupport familyLetterLabel c).card) :
    formalGroupCommutator familyLetterValue c ∈
      familyProjectionVanishing A ℓ := by
  refine
    ⟨expandFormalCommutator c,
      expand_formal_commutator c, ?_⟩
  intro S hS
  rw [projection_expand_formal]
  exact retain_variables_card familyLetterLabel familyLetterValue c S
    (hS.trans_le hℓ)

/-- **Petresco 8.2, literal family form.** A commutator form involving
every member of a finite family belongs to the top-index
projection-vanishing subgroup. -/
theorem full_projection_vanishing
    [Fintype L] [DecidableEq L] (A : L → Subgroup G)
    (c : FormalCommutator (FamilyLetter A))
    (hc : projectedFormalSupport familyLetterLabel c = Finset.univ) :
    formalGroupCommutator familyLetterValue c ∈
      familyProjectionVanishing A (Fintype.card L) := by
  apply formal_family_vanishing A (Fintype.card L) c
  rw [hc, Finset.card_univ]

/-- Petresco's `O^ℓ(A₁,...,Aν)`, defined as the subgroup generated by
commutator forms involving at least `ℓ` distinct family indices. -/
def familyCommutatorAggregate
    [DecidableEq L] (A : L → Subgroup G) (ℓ : ℕ) :
    Subgroup G :=
  Subgroup.closure
    {x | ∃ c : FormalCommutator (FamilyLetter A),
      ℓ ≤ (projectedFormalSupport familyLetterLabel c).card ∧
        formalGroupCommutator familyLetterValue c = x}

private lemma formal_family_join
    {A : L → Subgroup G}
    (c : FormalCommutator (FamilyLetter A)) :
    formalGroupCommutator familyLetterValue c ∈ familyJoin A := by
  induction c with
  | of x =>
      exact Subgroup.mem_iSup_of_mem x.1 x.2.2
  | mul a b iha ihb =>
      change
        hallCommutator
            (formalGroupCommutator familyLetterValue a)
            (formalGroupCommutator familyLetterValue b) ∈
          familyJoin A
      simpa [hallCommutator, mul_assoc] using
        (familyJoin A).mul_mem
          ((familyJoin A).mul_mem
            ((familyJoin A).mul_mem
              ((familyJoin A).inv_mem iha)
              ((familyJoin A).inv_mem ihb))
            iha)
          ihb

lemma family_aggregate_join
    [DecidableEq L] (A : L → Subgroup G) (ℓ : ℕ) :
    familyCommutatorAggregate A ℓ ≤ familyJoin A := by
  rw [familyCommutatorAggregate, Subgroup.closure_le]
  rintro x ⟨c, hc, rfl⟩
  exact formal_family_join c

/-- Petresco's defining boundary case `O¹ = A₁ ∪ ⋯ ∪ Aν`. -/
theorem family_commutator_aggregate
    [DecidableEq L] (A : L → Subgroup G) :
    familyCommutatorAggregate A 1 = familyJoin A := by
  apply le_antisymm
  · exact family_aggregate_join A 1
  · unfold familyJoin
    refine iSup_le fun i => ?_
    intro g hg
    apply Subgroup.subset_closure
    exact
      ⟨FreeMagma.of (⟨i, ⟨g, hg⟩⟩ : FamilyLetter A),
        by simp [familyLetterLabel], rfl⟩

private lemma conjugate_inv_aggregate
    [DecidableEq L] {A : L → Subgroup G} {ℓ : ℕ}
    (a : FamilyLetter A) {x : G}
    (hx : x ∈ familyCommutatorAggregate A ℓ) :
    (familyLetterValue a)⁻¹ * x * familyLetterValue a ∈
      familyCommutatorAggregate A ℓ := by
  rw [familyCommutatorAggregate] at hx ⊢
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
      obtain ⟨c, hc, rfl⟩ := hx
      have hc_mem :
          formalGroupCommutator familyLetterValue c ∈
            Subgroup.closure
              {x | ∃ d : FormalCommutator (FamilyLetter A),
                ℓ ≤
                  (projectedFormalSupport familyLetterLabel d).card ∧
                    formalGroupCommutator familyLetterValue d = x} :=
        Subgroup.subset_closure ⟨c, hc, rfl⟩
      have hcard :
          ℓ ≤
            (projectedFormalSupport familyLetterLabel
              (formalBracket c (FreeMagma.of a))).card := by
        apply hc.trans
        apply Finset.card_le_card
        exact Finset.subset_union_left
      have hcomm_mem :
          formalGroupCommutator familyLetterValue
              (formalBracket c (FreeMagma.of a)) ∈
            Subgroup.closure
              {x | ∃ d : FormalCommutator (FamilyLetter A),
                ℓ ≤
                  (projectedFormalSupport familyLetterLabel d).card ∧
                    formalGroupCommutator familyLetterValue d = x} :=
        Subgroup.subset_closure
          ⟨formalBracket c (FreeMagma.of a), hcard, rfl⟩
      rw [show
        (familyLetterValue a)⁻¹ *
              formalGroupCommutator familyLetterValue c *
              familyLetterValue a =
            formalGroupCommutator familyLetterValue c *
              formalGroupCommutator familyLetterValue
                (formalBracket c (FreeMagma.of a)) by
          simp [hallCommutator, mul_assoc]]
      exact
        (Subgroup.closure
          {x | ∃ d : FormalCommutator (FamilyLetter A),
            ℓ ≤ (projectedFormalSupport familyLetterLabel d).card ∧
              formalGroupCommutator familyLetterValue d = x}).mul_mem
          hc_mem hcomm_mem
  | one =>
      simp
  | mul x y hx hy ihx ihy =>
      simpa [mul_assoc] using
        (Subgroup.closure
          {x | ∃ d : FormalCommutator (FamilyLetter A),
            ℓ ≤ (projectedFormalSupport familyLetterLabel d).card ∧
              formalGroupCommutator familyLetterValue d = x}).mul_mem
          ihx ihy
  | inv x hx ih =>
      simpa [mul_assoc] using
        (Subgroup.closure
          {x | ∃ d : FormalCommutator (FamilyLetter A),
            ℓ ≤ (projectedFormalSupport familyLetterLabel d).card ∧
              formalGroupCommutator familyLetterValue d = x}).inv_mem ih

/-- **Petresco 9.1, literal family form.** The subgroup generated by
commutator forms of index at least `ℓ` is normal in the join of the family. -/
theorem family_aggregate_normal
    [DecidableEq L] (A : L → Subgroup G) (ℓ : ℕ) :
    ((familyCommutatorAggregate A ℓ).subgroupOf
      (familyJoin A)).Normal := by
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer
    (family_aggregate_join A ℓ)]
  unfold familyJoin
  refine iSup_le fun i => ?_
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    have hforward :=
      conjugate_inv_aggregate
        (A := A) ⟨i, g⁻¹, (A i).inv_mem hg⟩ hx
    change (g⁻¹)⁻¹ * x * g⁻¹ ∈
      familyCommutatorAggregate A ℓ at hforward
    simpa using hforward
  · intro hx
    have hback :=
      conjugate_inv_aggregate
        (A := A) ⟨i, g, hg⟩ hx
    change g⁻¹ * (g * x * g⁻¹) * g ∈
      familyCommutatorAggregate A ℓ at hback
    simpa [mul_assoc] using hback

/-- The inclusion `O^ℓ ≤ E^ℓ` for a literal family of subgroups. -/
theorem family_aggregate_vanishing
    [DecidableEq L] (A : L → Subgroup G) (ℓ : ℕ) :
    familyCommutatorAggregate A ℓ ≤
      familyProjectionVanishing A ℓ := by
  rw [familyCommutatorAggregate, Subgroup.closure_le]
  rintro x ⟨c, hc, rfl⟩
  exact formal_family_vanishing A ℓ c hc

/-- The reverse inclusion `E^ℓ ≤ O^ℓ`, proved by Petresco's collection
argument. -/
theorem vanishing_commutator_aggregate
    [Finite L] [DecidableEq L] (A : L → Subgroup G) (ℓ : ℕ) :
    familyProjectionVanishing A ℓ ≤
      familyCommutatorAggregate A ℓ := by
  classical
  letI := Fintype.ofFinite L
  rintro x ⟨w, hw, hprojection⟩
  let l := familyWordFormalization w
  have hvanish :
      ∀ S : Finset L, S.card < ℓ →
        evalFormalWord
          (retainProjectedVariables
            familyLetterLabel S familyLetterValue) l = 1 := by
    intro S hS
    rw [show
      evalFormalWord
          (retainProjectedVariables
            familyLetterLabel S familyLetterValue) l =
        familyWordProjection S w by
          exact projected_family_formalization S w]
    exact hprojection S hS
  obtain ⟨q, hq, heval⟩ :=
    vanishing_aggregate_word
      familyLetterValue familyLetterLabel ℓ l hvanish
  rw [← hw, ← eval_family_formalization w, heval]
  unfold evalFormalWord
  apply Subgroup.list_prod_mem
  intro y hy
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hy
  apply Subgroup.subset_closure
  exact ⟨c, hq c hc, rfl⟩

/-- **Petresco 9.3.** For a finite family, the projection-vanishing
subgroup and the commutator aggregate are equal. -/
theorem family_vanishing_aggregate
    [Finite L] [DecidableEq L] (A : L → Subgroup G) (ℓ : ℕ) :
    familyProjectionVanishing A ℓ =
      familyCommutatorAggregate A ℓ :=
  le_antisymm
    (vanishing_commutator_aggregate A ℓ)
    (family_aggregate_vanishing A ℓ)

/-- **Petresco 9.2.** The first nontrivial case of the collection theorem. -/
theorem projection_vanishing_aggregate
    [Finite L] [DecidableEq L] (A : L → Subgroup G) :
    familyProjectionVanishing A 2 =
      familyCommutatorAggregate A 2 :=
  family_vanishing_aggregate A 2

/-! ## The support-by-support decomposition -/

/-- The subgroup generated by commutator forms with one precise set of
family indices. -/
def exactSupportAggregate
    [DecidableEq L] (A : L → Subgroup G) (S : Finset L) :
    Subgroup G :=
  Subgroup.closure
    {x | ∃ c : FormalCommutator (FamilyLetter A),
      projectedFormalSupport familyLetterLabel c = S ∧
        formalGroupCommutator familyLetterValue c = x}

lemma exact_support_aggregate
    [DecidableEq L] (A : L → Subgroup G) (S : Finset L) :
    exactSupportAggregate A S ≤
      familyCommutatorAggregate A S.card := by
  rw [exactSupportAggregate, familyCommutatorAggregate,
    Subgroup.closure_le]
  rintro x ⟨c, hc, rfl⟩
  apply Subgroup.subset_closure
  exact ⟨c, by rw [hc], rfl⟩

/-- Every element of the join of a family has a raw family-word
representation. -/
theorem family_word_value
    {A : L → Subgroup G} {x : G} (hx : x ∈ familyJoin A) :
    ∃ w : FamilyWord A, familyWordValue w = x :=
  family_value_aux A hx

private lemma formal_flatten_values
    {X : Type*} (f : X → G)
    (blocks : List (List (FormalCommutator X))) :
    evalFormalWord f blocks.flatten =
      (blocks.map (evalFormalWord f)).prod := by
  induction blocks with
  | nil =>
      rfl
  | cons q blocks ih =>
      simp [eval_formal_append, ih]

/-- **Petresco 9.4, arbitrary within-level order.** If `supports` lists
every nonempty index set and is ordered by nondecreasing cardinality, every
element of the join is the corresponding ordered product of exact-support
aggregate elements.  Thus the order among supports of equal cardinality is
arbitrary, as asserted in the paper. -/
theorem exact_support_order
    [DecidableEq L] (A : L → Subgroup G)
    (supports : List (Finset L))
    (hcomplete : ∀ S : Finset L, S.Nonempty → S ∈ supports)
    (hsorted : supports.Pairwise fun S T => S.card ≤ T.card)
    {x : G} (hx : x ∈ familyJoin A) :
    ∃ values : List G,
      List.Forall₂
          (fun S y => y ∈ exactSupportAggregate A S)
          supports values ∧
        x = values.prod := by
  obtain ⟨w, hw⟩ := family_word_value hx
  let l := familyWordFormalization w
  let qr :=
    splitKeySubsets
      (projectedFormalSupport familyLetterLabel) supports l
  have hcollect :=
    key_subsets_exact
      familyLetterValue
      (projectedFormalSupport familyLetterLabel)
      (projected_formal_bracket familyLetterLabel)
      (projected_formal_nonempty familyLetterLabel)
      supports hcomplete hsorted l
  change
    List.Forall₂
        (fun S q => ∀ c ∈ q,
          projectedFormalSupport familyLetterLabel c = S)
        supports qr.1 ∧
      qr.2 = [] ∧
        evalFormalWord familyLetterValue qr.1.flatten =
          evalFormalWord familyLetterValue l at hcollect
  let values := qr.1.map (evalFormalWord familyLetterValue)
  refine ⟨values, ?_, ?_⟩
  · rw [List.forall₂_map_right_iff]
    exact hcollect.1.imp fun S q hq => by
      rw [exactSupportAggregate]
      unfold evalFormalWord
      apply Subgroup.list_prod_mem
      intro y hy
      obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hy
      apply Subgroup.subset_closure
      exact ⟨c, hq c hc, rfl⟩
  · calc
      x = familyWordValue w := hw.symm
      _ = evalFormalWord familyLetterValue l :=
        (eval_family_formalization w).symm
      _ = evalFormalWord familyLetterValue qr.1.flatten :=
        hcollect.2.2.symm
      _ = values.prod := by
        exact formal_flatten_values
          familyLetterValue qr.1

/-- **Petresco 9.4, canonical cardinality order.** -/
theorem exact_support_collection
    [Fintype L] [DecidableEq L] (A : L → Subgroup G)
    {x : G} (hx : x ∈ familyJoin A) :
    ∃ values : List G,
      List.Forall₂
          (fun S y => y ∈ exactSupportAggregate A S)
          (cardinalityNonemptySupports L) values ∧
        x = values.prod :=
  exact_support_order A
    (cardinalityNonemptySupports L)
    (fun S hS =>
      (cardinality_nonempty_supports S).mpr hS)
    (cardinality_supports_pairwise L) hx

end P1954
end Edmonton
end Submission
