import Towers.Group.Petresco.CommutatorProducts
import Mathlib.Algebra.BigOperators.Group.List.Lemmas
import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Petresco's 1954 paper: substitutions and finite subgroup words

This file formalizes the finite-word descriptions in Sections 1--4.
-/

namespace Towers
namespace Edmonton
namespace P1954

open scoped commutatorElement

universe u

variable {G : Type u} [Group G]

/-- `y` is a substitution of `x` when both are products of two finite lists
which differ only by a permutation. -/
def IsSubstitution (x y : G) : Prop :=
  ∃ l r : List G, l.Perm r ∧ l.prod = x ∧ r.prod = y

/-- Permuting a finite product changes it by an element of the commutator
subgroup. -/
lemma prod_inv_perm
    {l r : List G} (h : l.Perm r) :
    l.prod * r.prod⁻¹ ∈ commutator G := by
  let q : G →* G ⧸ commutator G := QuotientGroup.mk' (commutator G)
  letI : IsMulCommutative (G ⧸ commutator G) :=
    Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr le_rfl
  letI : CommGroup (G ⧸ commutator G) :=
    { (inferInstance : Group (G ⧸ commutator G)) with
      mul_comm := mul_comm' }
  have hprod : q l.prod = q r.prod := by
    rw [map_list_prod, map_list_prod]
    exact (h.map q).prod_eq
  apply (QuotientGroup.eq_one_iff (l.prod * r.prod⁻¹)).mp
  change q (l.prod * r.prod⁻¹) = 1
  rw [map_mul, map_inv, hprod, mul_inv_cancel]

/-- Every element of the commutator subgroup is a substitution of the
identity. -/
lemma perm_prod_commutator
    {x : G} (hx : x ∈ commutator G) :
    ∃ l r : List G, l.Perm r ∧ l.prod = x ∧ r.prod = 1 := by
  rw [commutator_eq_closure] at hx
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
      obtain ⟨a, b, rfl⟩ := hx
      refine
        ⟨[a, b, a⁻¹, b⁻¹], [a, a⁻¹, b, b⁻¹],
          List.Perm.cons a (List.Perm.swap b a⁻¹ [b⁻¹]).symm, ?_, ?_⟩
      · simp [commutatorElement_def, mul_assoc]
      · simp
  | one =>
      exact ⟨[], [], List.Perm.refl [], by simp, by simp⟩
  | mul x y _ _ hx hy =>
      obtain ⟨lx, rx, hpx, hlx, hrx⟩ := hx
      obtain ⟨ly, ry, hpy, hly, hry⟩ := hy
      refine ⟨lx ++ ly, rx ++ ry, hpx.append hpy, ?_, ?_⟩
      · simp [hlx, hly]
      · simp [hrx, hry]
  | inv x _ hx =>
      obtain ⟨l, r, hp, hl, hr⟩ := hx
      refine
        ⟨(l.map fun z => z⁻¹).reverse,
          (r.map fun z => z⁻¹).reverse,
          (List.reverse_perm _).trans
            ((hp.map fun z => z⁻¹).trans (List.reverse_perm _).symm),
          ?_, ?_⟩
      · rw [← List.prod_inv_reverse, hl]
      · rw [← List.prod_inv_reverse, hr]
        simp

/-- **Petresco 1.1.** Substitution equivalence is exactly congruence modulo
the commutator subgroup. -/
theorem substitution_inv_commutator (x y : G) :
    IsSubstitution x y ↔ x * y⁻¹ ∈ commutator G := by
  constructor
  · rintro ⟨l, r, hp, rfl, rfl⟩
    exact prod_inv_perm hp
  · intro hxy
    obtain ⟨l, r, hp, hl, hr⟩ :=
      perm_prod_commutator hxy
    refine ⟨l ++ [y], r ++ [y], hp.append_right [y], ?_, ?_⟩
    · simp [hl, mul_assoc]
    · simp [hr]

/-- The identity class for substitutions is the commutator subgroup. -/
theorem substitution_one_commutator (x : G) :
    IsSubstitution x 1 ↔ x ∈ commutator G := by
  simpa using substitution_inv_commutator x 1

section AlternatingWords

variable (A B : Subgroup G)

/-- A finite alternating word `a₁b₁⋯aₙbₙ`, with membership in `A` and `B`
carried by the types of its letters. -/
abbrev ABWord := List (A × B)

/-- The value `a₁b₁⋯aₙbₙ` of an alternating word. -/
def abWordValue (w : ABWord A B) : G :=
  (w.map fun p => (p.1 : G) * (p.2 : G)).prod

/-- The product `a₁⋯aₙ` of the `A`-letters. -/
def abLeftValue (w : ABWord A B) : G :=
  (w.map fun p => (p.1 : G)).prod

/-- The product `b₁⋯bₙ` of the `B`-letters. -/
def abRightValue (w : ABWord A B) : G :=
  (w.map fun p => (p.2 : G)).prod

/-- An alternating word for the inverse, obtained by reversing the pairs and
replacing `(a,b)⁻¹ = b⁻¹a⁻¹` with the two pairs `(1,b⁻¹),(a⁻¹,1)`. -/
def abWordInv : ABWord A B → ABWord A B
  | [] => []
  | p :: w =>
      abWordInv w ++
        [((1 : A), p.2⁻¹), (p.1⁻¹, (1 : B))]

@[simp]
lemma ab_word_nil : abWordValue A B [] = 1 := by
  simp [abWordValue]

@[simp]
lemma ab_left_nil : abLeftValue A B [] = 1 := by
  simp [abLeftValue]

@[simp]
lemma ab_value_nil : abRightValue A B [] = 1 := by
  simp [abRightValue]

@[simp]
lemma ab_word_append (u v : ABWord A B) :
    abWordValue A B (u ++ v) =
      abWordValue A B u * abWordValue A B v := by
  simp [abWordValue]

@[simp]
lemma ab_left_append (u v : ABWord A B) :
    abLeftValue A B (u ++ v) =
      abLeftValue A B u * abLeftValue A B v := by
  simp [abLeftValue]

@[simp]
lemma ab_value_append (u v : ABWord A B) :
    abRightValue A B (u ++ v) =
      abRightValue A B u * abRightValue A B v := by
  simp [abRightValue]

@[simp]
lemma ab_word_inv (w : ABWord A B) :
    abWordValue A B (abWordInv A B w) = (abWordValue A B w)⁻¹ := by
  induction w with
  | nil =>
      simp [abWordInv]
  | cons p w ih =>
      rw [abWordInv, ab_word_append, ih]
      simp [abWordValue, mul_assoc]

@[simp]
lemma ab_left_inv (w : ABWord A B) :
    abLeftValue A B (abWordInv A B w) = (abLeftValue A B w)⁻¹ := by
  induction w with
  | nil =>
      simp [abWordInv]
  | cons p w ih =>
      rw [abWordInv, ab_left_append, ih]
      simp [abLeftValue]

@[simp]
lemma ab_value_inv (w : ABWord A B) :
    abRightValue A B (abWordInv A B w) = (abRightValue A B w)⁻¹ := by
  induction w with
  | nil =>
      simp [abWordInv]
  | cons p w ih =>
      rw [abWordInv, ab_value_append, ih]
      simp [abRightValue]

lemma ab_left_value (w : ABWord A B) :
    abLeftValue A B w ∈ A := by
  induction w with
  | nil => simp
  | cons p w ih =>
      simpa [abLeftValue] using A.mul_mem p.1.2 ih

lemma ab_right_value (w : ABWord A B) :
    abRightValue A B w ∈ B := by
  induction w with
  | nil => simp
  | cons p w ih =>
      simpa [abRightValue] using B.mul_mem p.2.2 ih

lemma ab_value_sup (w : ABWord A B) :
    abWordValue A B w ∈ A ⊔ B := by
  induction w with
  | nil => simp
  | cons p w ih =>
      exact (A ⊔ B).mul_mem
        ((A ⊔ B).mul_mem (Subgroup.mem_sup_left p.1.2)
          (Subgroup.mem_sup_right p.2.2))
        (by simpa [abWordValue] using ih)

/-- Every element of `A ⊔ B` has a finite alternating-word expression. -/
theorem ab_word_value
    {x : G} (hx : x ∈ A ⊔ B) :
    ∃ w : ABWord A B, abWordValue A B w = x := by
  rw [Subgroup.sup_eq_closure] at hx
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
      rcases hx with hx | hx
      · exact
          ⟨[((⟨x, hx⟩ : A), (1 : B))], by simp [abWordValue]⟩
      · exact
          ⟨[((1 : A), (⟨x, hx⟩ : B))], by simp [abWordValue]⟩
  | one =>
      exact ⟨[], by simp⟩
  | mul x y _ _ hx hy =>
      obtain ⟨u, hu⟩ := hx
      obtain ⟨v, hv⟩ := hy
      exact ⟨u ++ v, by simp [hu, hv]⟩
  | inv x _ hx =>
      obtain ⟨w, hw⟩ := hx
      exact ⟨abWordInv A B w, by simp [hw]⟩

/-- The `A`-letters of an alternating word, regarded as elements of
`A ⊔ B`. -/
def abLeftLetters (w : ABWord A B) : List ↥(A ⊔ B) :=
  w.map fun p => ⟨p.1, Subgroup.mem_sup_left p.1.2⟩

/-- The `B`-letters of an alternating word, regarded as elements of
`A ⊔ B`. -/
def abRightLetters (w : ABWord A B) : List ↥(A ⊔ B) :=
  w.map fun p => ⟨p.2, Subgroup.mem_sup_right p.2.2⟩

/-- The alternating list `a₁,b₁,…,aₙ,bₙ` inside `A ⊔ B`. -/
def abFactorLetters : ABWord A B → List ↥(A ⊔ B)
  | [] => []
  | p :: w =>
      ⟨p.1, Subgroup.mem_sup_left p.1.2⟩ ::
        ⟨p.2, Subgroup.mem_sup_right p.2.2⟩ ::
          abFactorLetters w

@[simp]
lemma ab_left_letters (w : ABWord A B) :
    ((abLeftLetters A B w).prod : G) = abLeftValue A B w := by
  rw [SubmonoidClass.coe_list_prod]
  simp [abLeftLetters, abLeftValue, Function.comp_def]

@[simp]
lemma ab_letters_prod (w : ABWord A B) :
    ((abRightLetters A B w).prod : G) = abRightValue A B w := by
  rw [SubmonoidClass.coe_list_prod]
  simp [abRightLetters, abRightValue, Function.comp_def]

@[simp]
lemma coe_ab_letters (w : ABWord A B) :
    ((abFactorLetters A B w).prod : G) = abWordValue A B w := by
  rw [SubmonoidClass.coe_list_prod]
  induction w with
  | nil =>
      rfl
  | cons p w ih =>
      simp only [abFactorLetters, List.map_cons, List.prod_cons]
      rw [ih]
      simp [abWordValue, mul_assoc]

/-- Grouping all `A`-letters before all `B`-letters is a permutation of the
alternating factor list. -/
lemma ab_letters_grouped (w : ABWord A B) :
    (abFactorLetters A B w).Perm
      (abLeftLetters A B w ++ abRightLetters A B w) := by
  induction w with
  | nil =>
      simp [abFactorLetters, abLeftLetters, abRightLetters]
  | cons p w ih =>
      let a : ↥(A ⊔ B) := ⟨p.1, Subgroup.mem_sup_left p.1.2⟩
      let b : ↥(A ⊔ B) := ⟨p.2, Subgroup.mem_sup_right p.2.2⟩
      have hfirst :
          (a :: b :: abFactorLetters A B w).Perm
            (a :: b :: (abLeftLetters A B w ++ abRightLetters A B w)) :=
        List.Perm.cons a (List.Perm.cons b ih)
      have hswap :
          (b :: abLeftLetters A B w ++ abRightLetters A B w).Perm
            (abLeftLetters A B w ++ b :: abRightLetters A B w) := by
        simpa [List.append_assoc] using
          (List.perm_append_comm
            (l₁ := [b]) (l₂ := abLeftLetters A B w)).append_right
            (abRightLetters A B w)
      simpa [a, b, abFactorLetters, abLeftLetters, abRightLetters,
        List.append_assoc] using hfirst.trans (List.Perm.cons a hswap)

/-- A permutation of lists in a subgroup gives an ambient element of that
subgroup's derived subgroup. -/
lemma coe_inv_perm
    {H : Subgroup G} {l r : List H} (h : l.Perm r) :
    ((l.prod * r.prod⁻¹ : H) : G) ∈ ⁅H, H⁆ := by
  have hsub : l.prod * r.prod⁻¹ ∈ commutator H :=
    prod_inv_perm h
  have hmap :
      ((l.prod * r.prod⁻¹ : H) : G) ∈
        (commutator H).map H.subtype :=
    ⟨l.prod * r.prod⁻¹, hsub, rfl⟩
  simpa [Subgroup.map_subtype_commutator] using hmap

/-- **Petresco 2.1.** The derived subgroup of `A ⊔ B` consists exactly of
alternating words whose `A`-projection lies in `[A,A]` and whose
`B`-projection lies in `[B,B]`. -/
theorem commutator_join_membership (x : G) :
    x ∈ ⁅A ⊔ B, A ⊔ B⁆ ↔
      ∃ w : ABWord A B,
        abWordValue A B w = x ∧
          abLeftValue A B w ∈ ⁅A, A⁆ ∧
          abRightValue A B w ∈ ⁅B, B⁆ := by
  constructor
  · intro hx
    rw [Subgroup.commutator_def] at hx
    induction hx using Subgroup.closure_induction with
    | mem z hz =>
        obtain ⟨x, hx, y, hy, rfl⟩ := hz
        obtain ⟨u, hu⟩ := ab_word_value A B hx
        obtain ⟨v, hv⟩ := ab_word_value A B hy
        refine
          ⟨u ++ v ++ abWordInv A B u ++ abWordInv A B v,
            ?_, ?_, ?_⟩
        · simp [hu, hv, commutatorElement_def, mul_assoc]
        · have hcomm :=
            Subgroup.commutator_mem_commutator
              (ab_left_value A B u) (ab_left_value A B v)
          simpa [commutatorElement_def, mul_assoc] using hcomm
        · have hcomm :=
            Subgroup.commutator_mem_commutator
              (ab_right_value A B u) (ab_right_value A B v)
          simpa [commutatorElement_def, mul_assoc] using hcomm
    | one =>
        exact ⟨[], by simp, by simp, by simp⟩
    | mul x y _ _ hx hy =>
        obtain ⟨u, hu, hlu, hru⟩ := hx
        obtain ⟨v, hv, hlv, hrv⟩ := hy
        exact
          ⟨u ++ v, by simp [hu, hv],
            by simpa using (⁅A, A⁆ : Subgroup G).mul_mem hlu hlv,
            by simpa using (⁅B, B⁆ : Subgroup G).mul_mem hru hrv⟩
    | inv x _ hx =>
        obtain ⟨w, hw, hl, hr⟩ := hx
        exact
          ⟨abWordInv A B w, by simp [hw],
            by simpa using (⁅A, A⁆ : Subgroup G).inv_mem hl,
            by simpa using (⁅B, B⁆ : Subgroup G).inv_mem hr⟩
  · rintro ⟨w, rfl, hleft, hright⟩
    let H : Subgroup G := A ⊔ B
    have hdiff :
        abWordValue A B w *
            (abLeftValue A B w * abRightValue A B w)⁻¹ ∈
          ⁅H, H⁆ := by
      have h :=
        coe_inv_perm
          (ab_letters_grouped A B w)
      have hfactor := coe_ab_letters A B w
      have hleft := ab_left_letters A B w
      have hright := ab_letters_prod A B w
      rw [← hfactor, ← hleft, ← hright]
      simpa [H, List.prod_append] using h
    have hgrouped :
        abLeftValue A B w * abRightValue A B w ∈ ⁅H, H⁆ := by
      apply (⁅H, H⁆ : Subgroup G).mul_mem
      · exact
          (Subgroup.commutator_mono le_sup_left le_sup_left) hleft
      · exact
          (Subgroup.commutator_mono le_sup_right le_sup_right) hright
    have hvalue := (⁅H, H⁆ : Subgroup G).mul_mem hdiff hgrouped
    simpa [H, mul_assoc] using hvalue

/-- Collecting all `A`-letters to the left and all `B`-letters to the
right changes an alternating word by an element of `[A,B]`. -/
lemma ab_inv_commutator
    (w : ABWord A B) :
    abWordValue A B w *
        (abLeftValue A B w * abRightValue A B w)⁻¹ ∈ ⁅A, B⁆ := by
  let H : Subgroup G := A ⊔ B
  let C : Subgroup G := ⁅A, B⁆
  have hCH : C ≤ H := by
    exact
      (Subgroup.commutator_mono le_sup_left le_sup_right).trans
        H.commutator_le_self
  let N : Subgroup H := C.subgroupOf H
  letI : N.Normal := by
    simpa [N, C, H] using commutator_sup A B
  let q : H →* H ⧸ N := QuotientGroup.mk' N
  let wordH : ABWord A B → H := fun v =>
    ⟨abWordValue A B v, ab_value_sup A B v⟩
  let leftH : ABWord A B → H := fun v =>
    ⟨abLeftValue A B v,
      Subgroup.mem_sup_left (ab_left_value A B v)⟩
  let rightH : ABWord A B → H := fun v =>
    ⟨abRightValue A B v,
      Subgroup.mem_sup_right (ab_right_value A B v)⟩
  have hquotient :
      ∀ v : ABWord A B,
        q (wordH v) = q (leftH v) * q (rightH v) := by
    intro v
    induction v with
    | nil =>
        have hword : wordH [] = 1 := by
          ext
          simp [wordH]
        have hleft : leftH [] = 1 := by
          ext
          simp [leftH]
        have hright : rightH [] = 1 := by
          ext
          simp [rightH]
        rw [hword, hleft, hright]
        simp
    | cons p v ih =>
        let a : H := ⟨p.1, Subgroup.mem_sup_left p.1.2⟩
        let b : H := ⟨p.2, Subgroup.mem_sup_right p.2.2⟩
        have hword : wordH (p :: v) = a * b * wordH v := by
          ext
          simp [wordH, a, b, abWordValue, mul_assoc]
        have hleft : leftH (p :: v) = a * leftH v := by
          ext
          simp [leftH, a, abLeftValue]
        have hright : rightH (p :: v) = b * rightH v := by
          ext
          simp [rightH, b, abRightValue]
        have hcomm_mem : ⁅b, leftH v⁆ ∈ N := by
          change ⁅(b : G), (leftH v : G)⁆ ∈ C
          have hbA :
              ⁅(b : G), (leftH v : G)⁆ ∈ ⁅B, A⁆ :=
            Subgroup.commutator_mem_commutator
              (by simp [b])
              (ab_left_value A B v)
          simpa [C, Subgroup.commutator_comm B A] using hbA
        have hcomm_one : ⁅q b, q (leftH v)⁆ = 1 := by
          rw [← map_commutatorElement]
          exact (QuotientGroup.eq_one_iff _).2 hcomm_mem
        have hmul : q b * q (leftH v) = q (leftH v) * q b :=
          commutatorElement_eq_one_iff_mul_comm.mp hcomm_one
        rw [hword, hleft, hright]
        simp only [map_mul]
        rw [ih]
        calc
          q a * q b * (q (leftH v) * q (rightH v)) =
              q a * (q b * q (leftH v)) * q (rightH v) := by
                simp [mul_assoc]
          _ = q a * (q (leftH v) * q b) * q (rightH v) := by
                rw [hmul]
          _ = (q a * q (leftH v)) * (q b * q (rightH v)) := by
                simp [mul_assoc]
  have hone :
      q (wordH w * (leftH w * rightH w)⁻¹) = 1 := by
    rw [map_mul, map_inv, map_mul, hquotient]
    simp
  have hmem :
      wordH w * (leftH w * rightH w)⁻¹ ∈ N :=
    (QuotientGroup.eq_one_iff _).mp hone
  change
    abWordValue A B w *
        (abLeftValue A B w * abRightValue A B w)⁻¹ ∈ C at hmem
  exact hmem

/-- The subgroup of elements admitting an alternating expression whose
two component products lie in prescribed subgroups. -/
def projectedWordSubgroup
    (Astar Bstar : Subgroup G) : Subgroup G where
  carrier := {x |
    ∃ w : ABWord A B,
      abWordValue A B w = x ∧
        abLeftValue A B w ∈ Astar ∧
        abRightValue A B w ∈ Bstar}
  one_mem' := ⟨[], by simp⟩
  mul_mem' := by
    rintro x y ⟨u, hu, hlu, hru⟩ ⟨v, hv, hlv, hrv⟩
    refine ⟨u ++ v, by simp [hu, hv], ?_, ?_⟩
    · simpa using Astar.mul_mem hlu hlv
    · simpa using Bstar.mul_mem hru hrv
  inv_mem' := by
    rintro x ⟨w, hw, hl, hr⟩
    refine ⟨abWordInv A B w, by simp [hw], ?_, ?_⟩
    · simpa using Astar.inv_mem hl
    · simpa using Bstar.inv_mem hr

lemma left_projected_subgroup
    {Astar Bstar : Subgroup G} (hAstar : Astar ≤ A) :
    Astar ≤ projectedWordSubgroup A B Astar Bstar := by
  intro x hx
  exact
    ⟨[((⟨x, hAstar hx⟩ : A), (1 : B))],
      by simp [abWordValue], by simpa [abLeftValue],
      by simp [abRightValue]⟩

lemma right_projected_subgroup
    {Astar Bstar : Subgroup G} (hBstar : Bstar ≤ B) :
    Bstar ≤ projectedWordSubgroup A B Astar Bstar := by
  intro x hx
  exact
    ⟨[((1 : A), (⟨x, hBstar hx⟩ : B))],
      by simp [abWordValue], by simp [abLeftValue],
      by simpa [abRightValue]⟩

lemma commutator_projected_subgroup
    (Astar Bstar : Subgroup G) :
    ⁅A, B⁆ ≤ projectedWordSubgroup A B Astar Bstar := by
  rw [Subgroup.commutator_def]
  rw [Subgroup.closure_le]
  rintro z ⟨a, ha, b, hb, rfl⟩
  refine
    ⟨[((⟨a, ha⟩ : A), (⟨b, hb⟩ : B)),
       ((⟨a⁻¹, A.inv_mem ha⟩ : A), (1 : B)),
       ((1 : A), (⟨b⁻¹, B.inv_mem hb⟩ : B))],
      ?_, ?_, ?_⟩
  · simp [abWordValue, commutatorElement_def, mul_assoc]
  · simp [abLeftValue]
  · simp [abRightValue]

/-- **Petresco 5.1, alternating-word form.** The subgroup
`A* [A,B] B*` consists exactly of alternating words whose `A`- and
`B`-component products lie in `A*` and `B*`. -/
theorem mixed_membership_family
    {Astar Bstar : Subgroup G}
    (hAstar : Astar ≤ A) (hBstar : Bstar ≤ B) (x : G) :
    x ∈ ((Astar ⊔ ⁅A, B⁆) ⊔ Bstar : Subgroup G) ↔
      ∃ w : ABWord A B,
        abWordValue A B w = x ∧
          abLeftValue A B w ∈ Astar ∧
          abRightValue A B w ∈ Bstar := by
  let W := projectedWordSubgroup A B Astar Bstar
  constructor
  · intro hx
    change x ∈ W
    exact
      (sup_le
        (sup_le
          (left_projected_subgroup A B hAstar)
          (commutator_projected_subgroup A B Astar Bstar))
        (right_projected_subgroup A B hBstar)) hx
  · rintro ⟨w, rfl, hleft, hright⟩
    let E : Subgroup G := (Astar ⊔ ⁅A, B⁆) ⊔ Bstar
    have hdiff :=
      ab_inv_commutator A B w
    have hd :
        abWordValue A B w *
            (abLeftValue A B w * abRightValue A B w)⁻¹ ∈ E :=
      Subgroup.mem_sup_left (Subgroup.mem_sup_right hdiff)
    have hl : abLeftValue A B w ∈ E :=
      Subgroup.mem_sup_left (Subgroup.mem_sup_left hleft)
    have hr : abRightValue A B w ∈ E :=
      Subgroup.mem_sup_right hright
    have hprod := E.mul_mem (E.mul_mem hd hl) hr
    simpa [E, mul_assoc] using hprod

/-- **Petresco 3.1.** The relative normal closure of `A` in `A ⊔ B`
consists of alternating words whose `B`-component product is one. -/
theorem relative_closure_membership (x : G) :
    x ∈ relativeNormalClosure (A : Set G) (A ⊔ B) ↔
      ∃ w : ABWord A B,
        abWordValue A B w = x ∧ abRightValue A B w = 1 := by
  rw [relative_sup_commutator A B]
  constructor
  · intro hx
    have h :=
      (mixed_membership_family A B le_rfl bot_le x).mp
        (Subgroup.mem_sup_left hx)
    obtain ⟨w, hw, _hleft, hright⟩ := h
    exact ⟨w, hw, by simpa using hright⟩
  · rintro ⟨w, hw, hright⟩
    have h :=
      (mixed_membership_family A B le_rfl bot_le x).mpr
        ⟨w, hw, ab_left_value A B w,
          by simpa using hright⟩
    have hle :
        ((A ⊔ ⁅A, B⁆) ⊔ (⊥ : Subgroup G)) ≤ A ⊔ ⁅A, B⁆ :=
      sup_le le_rfl bot_le
    exact hle h

/-- **Petresco 4.1.** The subgroup `[A,B]` consists exactly of alternating
words whose two component products are both one. -/
theorem commutator_membership_family (x : G) :
    x ∈ ⁅A, B⁆ ↔
      ∃ w : ABWord A B,
        abWordValue A B w = x ∧
          abLeftValue A B w = 1 ∧
          abRightValue A B w = 1 := by
  constructor
  · intro hx
    have h :=
      (mixed_membership_family A B bot_le bot_le x).mp
        (by simpa using hx)
    obtain ⟨w, hw, hleft, hright⟩ := h
    exact ⟨w, hw, by simpa using hleft, by simpa using hright⟩
  · rintro ⟨w, hw, hleft, hright⟩
    have h :=
      (mixed_membership_family A B bot_le bot_le x).mpr
        ⟨w, hw, by simpa using hleft, by simpa using hright⟩
    simpa using h

end AlternatingWords

end P1954
end Edmonton
end Towers
