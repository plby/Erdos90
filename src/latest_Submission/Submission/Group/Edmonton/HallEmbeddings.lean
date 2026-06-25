import Submission.Group.Edmonton.HallBasicCommutators
import Submission.Group.Edmonton.MinimalNormal
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finite.Prod
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.GroupTheory.FiniteAbelian.Basic
import Mathlib.RingTheory.Binomial

/-!
# The Edmonton Notes on Nilpotent Groups: Section 6 embedding theorems

This file begins Hall's support-collection argument for Petresco words.
-/

namespace Submission
namespace Edmonton

open Group
open scoped commutatorElement Pointwise IsMulCommutative

universe u v w

variable {G : Type u} [Group G]

/-- The variables which occur as components of a formal commutator. -/
def formalSupport {X : Type v} [DecidableEq X] :
    FormalCommutator X → Finset X
  | FreeMagma.of x => {x}
  | FreeMagma.mul a b => formalSupport a ∪ formalSupport b

@[simp]
lemma formalSupport_variable {X : Type v} [DecidableEq X] (x : X) :
    formalSupport (FreeMagma.of x) = {x} :=
  rfl

@[simp]
lemma formalSupport_bracket {X : Type v} [DecidableEq X]
    (a b : FormalCommutator X) :
    formalSupport (formalBracket a b) = formalSupport a ∪ formalSupport b :=
  rfl

/-- Every formal commutator has at least one component. -/
lemma formalSupport_nonempty {X : Type v} [DecidableEq X]
    (c : FormalCommutator X) :
    (formalSupport c).Nonempty := by
  induction c with
  | of x =>
      exact ⟨x, by simp⟩
  | mul a b iha _ =>
      exact iha.mono (Finset.subset_union_left)

/-- The labels occurring in a formal commutator after projecting each
component through `label`. This is the support notion needed for Hall's
expanded Petresco product, whose leaves remember both a generator and a
copy-slot while collection groups factors by copy-slot. -/
def projectedFormalSupport {X : Type v} {L : Type w} [DecidableEq L]
    (label : X → L) :
    FormalCommutator X → Finset L
  | FreeMagma.of x => {label x}
  | FreeMagma.mul a b =>
      projectedFormalSupport label a ∪ projectedFormalSupport label b

@[simp]
lemma projected_formal_variable
    {X : Type v} {L : Type w} [DecidableEq L]
    (label : X → L) (x : X) :
    projectedFormalSupport label (FreeMagma.of x) = {label x} :=
  rfl

@[simp]
lemma projected_formal_bracket
    {X : Type v} {L : Type w} [DecidableEq L]
    (label : X → L) (a b : FormalCommutator X) :
    projectedFormalSupport label (formalBracket a b) =
      projectedFormalSupport label a ∪ projectedFormalSupport label b :=
  rfl

/-- Projected formal support is always nonempty. -/
lemma projected_formal_nonempty
    {X : Type v} {L : Type w} [DecidableEq L]
    (label : X → L) (c : FormalCommutator X) :
    (projectedFormalSupport label c).Nonempty := by
  induction c with
  | of x =>
      exact ⟨label x, by simp⟩
  | mul a b iha _ =>
      exact iha.mono (Finset.subset_union_left)

/-- The number of projected labels is bounded by the number of formal
commutator components. -/
lemma projected_formal_support
    {X : Type v} {L : Type w} [DecidableEq L]
    (label : X → L) (c : FormalCommutator X) :
    (projectedFormalSupport label c).card ≤ formalWeight c := by
  induction c with
  | of x =>
      simp
  | mul a b iha ihb =>
      exact le_trans
        (Finset.card_union_le
          (projectedFormalSupport label a) (projectedFormalSupport label b))
        (Nat.add_le_add iha ihb)

/-- Retain variables whose projected labels lie in `S`, replacing all
other variables by the identity. -/
def retainProjectedVariables
    {X : Type v} {L : Type w} [DecidableEq L]
    (label : X → L) (S : Finset L) (f : X → G) (x : X) : G :=
  if label x ∈ S then f x else 1

@[simp]
lemma retain_variables
    {X : Type v} {L : Type w} [DecidableEq L]
    (label : X → L) (S : Finset L) (f : X → G)
    {x : X} (hx : label x ∈ S) :
    retainProjectedVariables label S f x = f x := by
  simp [retainProjectedVariables, hx]

@[simp]
lemma retain_variables_not
    {X : Type v} {L : Type w} [DecidableEq L]
    (label : X → L) (S : Finset L) (f : X → G)
    {x : X} (hx : label x ∉ S) :
    retainProjectedVariables label S f x = 1 := by
  simp [retainProjectedVariables, hx]

/-- Retaining every projected component of a formal commutator leaves its
value unchanged. -/
lemma retain_projected_variables
    {X : Type v} {L : Type w} [DecidableEq L]
    (label : X → L) (S : Finset L) (f : X → G)
    (c : FormalCommutator X) (hc : projectedFormalSupport label c ⊆ S) :
    formalGroupCommutator (retainProjectedVariables label S f) c =
      formalGroupCommutator f c := by
  induction c with
  | of x =>
      have hx : label x ∈ S := by
        simpa using hc
      simp [retainProjectedVariables, hx]
  | mul a b iha ihb =>
      have hab :
          projectedFormalSupport label a ⊆ S ∧
            projectedFormalSupport label b ⊆ S := by
        constructor
        · intro x hx
          exact hc (Finset.mem_union_left _ hx)
        · intro x hx
          exact hc (Finset.mem_union_right _ hx)
      change
        hallCommutator
            (formalGroupCommutator
              (retainProjectedVariables label S f) a)
            (formalGroupCommutator
              (retainProjectedVariables label S f) b) =
          hallCommutator (formalGroupCommutator f a)
            (formalGroupCommutator f b)
      rw [iha hab.1, ihb hab.2]

/-- A formal commutator becomes trivial when one of its projected
components is replaced by the identity. -/
lemma formal_retain_variables
    {X : Type v} {L : Type w} [DecidableEq L]
    (label : X → L) (S : Finset L) (f : X → G)
    (c : FormalCommutator X) (hc : ¬ projectedFormalSupport label c ⊆ S) :
    formalGroupCommutator (retainProjectedVariables label S f) c = 1 := by
  induction c with
  | of x =>
      have hx : label x ∉ S := by
        simpa using hc
      simp [retainProjectedVariables, hx]
  | mul a b iha ihb =>
      by_cases ha : projectedFormalSupport label a ⊆ S
      · have hb : ¬ projectedFormalSupport label b ⊆ S := by
          intro hb
          apply hc
          intro x hx
          rcases Finset.mem_union.mp hx with hx | hx
          · exact ha hx
          · exact hb hx
        change
          hallCommutator
              (formalGroupCommutator
                (retainProjectedVariables label S f) a)
              (formalGroupCommutator
                (retainProjectedVariables label S f) b) =
            1
        rw [ihb hb]
        exact (hall_commutator_commute _ _).mpr
          (Commute.one_right _)
      · change
          hallCommutator
              (formalGroupCommutator
                (retainProjectedVariables label S f) a)
              (formalGroupCommutator
                (retainProjectedVariables label S f) b) =
            1
        rw [iha ha]
        exact (hall_commutator_commute _ _).mpr
          (Commute.one_left _)

/-- Retain the variables with labels in `S` and replace all other
variables by the identity. This is Hall's operation `p ↦ p_S`. -/
def retainVariables {X : Type v} [DecidableEq X]
    (S : Finset X) (f : X → G) (x : X) : G :=
  if x ∈ S then f x else 1

@[simp]
lemma retain_of_mem {X : Type v} [DecidableEq X]
    (S : Finset X) (f : X → G) {x : X} (hx : x ∈ S) :
    retainVariables S f x = f x := by
  simp [retainVariables, hx]

@[simp]
lemma retain_not {X : Type v} [DecidableEq X]
    (S : Finset X) (f : X → G) {x : X} (hx : x ∉ S) :
    retainVariables S f x = 1 := by
  simp [retainVariables, hx]

/-- Retaining every component of a formal commutator leaves its value
unchanged. -/
lemma retain_variables_self
    {X : Type v} [DecidableEq X]
    (S : Finset X) (f : X → G) (c : FormalCommutator X)
    (hc : formalSupport c ⊆ S) :
    formalGroupCommutator (retainVariables S f) c =
      formalGroupCommutator f c := by
  induction c with
  | of x =>
      have hx : x ∈ S := by
        simpa [formalSupport] using hc
      simp [retainVariables, hx]
  | mul a b iha ihb =>
      have hab : formalSupport a ⊆ S ∧ formalSupport b ⊆ S := by
        constructor
        · intro x hx
          exact hc (Finset.mem_union_left _ hx)
        · intro x hx
          exact hc (Finset.mem_union_right _ hx)
      change
        hallCommutator
            (formalGroupCommutator (retainVariables S f) a)
            (formalGroupCommutator (retainVariables S f) b) =
          hallCommutator (formalGroupCommutator f a)
            (formalGroupCommutator f b)
      rw [iha hab.1, ihb hab.2]

/-- If a component of a formal commutator is replaced by the identity,
the whole commutator becomes the identity. -/
lemma commutator_retain_variables
    {X : Type v} [DecidableEq X]
    (S : Finset X) (f : X → G) (c : FormalCommutator X)
    (hc : ¬ formalSupport c ⊆ S) :
    formalGroupCommutator (retainVariables S f) c = 1 := by
  induction c with
  | of x =>
      have hx : x ∉ S := by
        simpa [formalSupport] using hc
      simp [retainVariables, hx]
  | mul a b iha ihb =>
      by_cases ha : formalSupport a ⊆ S
      · have hb : ¬ formalSupport b ⊆ S := by
          intro hb
          apply hc
          intro x hx
          rcases Finset.mem_union.mp hx with hx | hx
          · exact ha hx
          · exact hb hx
        change
          hallCommutator
              (formalGroupCommutator (retainVariables S f) a)
              (formalGroupCommutator (retainVariables S f) b) =
            1
        rw [ihb hb]
        exact (hall_commutator_commute _ _).mpr
          (Commute.one_right _)
      · change
          hallCommutator
              (formalGroupCommutator (retainVariables S f) a)
              (formalGroupCommutator (retainVariables S f) b) =
            1
        rw [iha ha]
        exact (hall_commutator_commute _ _).mpr
          (Commute.one_left _)

/-- The block-product conclusion used in Hall's Lemma 6.1. Once collection
procedure has arranged the formal commutator factors into blocks indexed by
their supports, the original product is the ordered product of the block
values, and every block consists entirely of commutators with its indicated
support. -/
theorem exactSupportFactorization
    {X : Type v} [DecidableEq X]
    (p : G) (f : X → G) (supports : List (Finset X))
    (blocks : Finset X → List (FormalCommutator X))
    (hblocks :
      ∀ S ∈ supports, ∀ c ∈ blocks S, formalSupport c = S)
    (hfactor :
      p = ((supports.flatMap blocks).map
        (formalGroupCommutator f)).prod) :
    ∃ q : Finset X → G,
      p = (supports.map q).prod ∧
        ∀ S ∈ supports, ∃ l : List (FormalCommutator X),
          (∀ c ∈ l, formalSupport c = S) ∧
            q S = (l.map (formalGroupCommutator f)).prod := by
  refine ⟨fun S => ((blocks S).map (formalGroupCommutator f)).prod,
    ?_, ?_⟩
  · rw [hfactor]
    clear hblocks hfactor p
    induction supports with
    | nil =>
        simp
    | cons S supports ih =>
        simp [ih]
  · intro S hS
    exact ⟨blocks S, hblocks S hS, rfl⟩

/-- **Hall, Lemma 6.2, support-projection form.** After setting all
variables outside `S` equal to one, an ordered product of formal
commutators retains precisely those factors whose supports lie in `S`.

Hall applies this to the factorization supplied by Lemma 6.1. -/
theorem retain_variables_filtered
    {X : Type v} [DecidableEq X]
    (S : Finset X) (f : X → G) (l : List (FormalCommutator X)) :
    (l.map (formalGroupCommutator (retainVariables S f))).prod =
      ((l.filter fun c => formalSupport c ⊆ S).map
        (formalGroupCommutator f)).prod := by
  classical
  induction l with
  | nil =>
      simp
  | cons c l ih =>
      by_cases hc : formalSupport c ⊆ S
      · simp [hc, retain_variables_self
          S f c hc, ih]
      · simp [hc, commutator_retain_variables
          S f c hc, ih]

/-- The recurrence observation following Lemma 6.2: once the preceding
ordered factors and their total product are known, the next factor is
uniquely recovered. -/
lemma recover_prior_product
    (prior : List G) (q p : G) (hp : p = prior.prod * q) :
    q = prior.prod⁻¹ * p := by
  rw [hp]
  simp

/-- The ordered product on the right side of Hall's recurrence defining
the Petresco words. -/
def petrescoBinomialProduct (tau : ℕ → G) (w : ℕ) : G :=
  ((List.finRange w).map fun (j : Fin w) =>
    tau ((j : ℕ) + 1) ^ Nat.choose w ((j : ℕ) + 1)).prod

/-- Hall's binomial product written over ordinary natural indices. -/
lemma petresco_prod_range (tau : ℕ → G) (w : ℕ) :
    petrescoBinomialProduct tau w =
      ((List.range w).map fun j =>
        tau (j + 1) ^ Nat.choose w (j + 1)).prod := by
  unfold petrescoBinomialProduct
  have hmap :=
    congrArg
      (List.map fun j : ℕ => tau (j + 1) ^ Nat.choose w (j + 1))
      (List.map_coe_finRange_eq_range (n := w))
  simp only [List.map_map] at hmap
  exact congrArg List.prod hmap

/-- Extending Hall's binomial product past its upper index only appends
trivial factors, because the additional binomial coefficients vanish. -/
lemma choose_petresco_binomial
    (tau : ℕ → G) {w m : ℕ} (hwm : w ≤ m) :
    ((List.range m).map fun j =>
      tau (j + 1) ^ Nat.choose w (j + 1)).prod =
        petrescoBinomialProduct tau w := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hwm
  induction d with
  | zero =>
      exact (petresco_prod_range tau w).symm
  | succ d ih =>
      rw [show w + (d + 1) = (w + d) + 1 by omega, List.range_succ,
        List.map_append, List.prod_append, ih (by omega)]
      simp only [List.map_singleton, List.prod_singleton]
      rw [Nat.choose_eq_zero_of_lt (by omega)]
      simp

/-- The part of Hall's binomial product involving only the terms preceding
`τ_w`. -/
def petrescoPriorProduct (tau : ℕ → G) (w : ℕ) : G :=
  ((List.finRange (w - 1)).map fun (j : Fin (w - 1)) =>
    tau ((j : ℕ) + 1) ^ Nat.choose w ((j : ℕ) + 1)).prod

/-- Hall's Petresco terms, defined recursively from
`x₁^w ⋯ xₙ^w = τ₁(x)^w τ₂(x)^(w choose 2) ⋯ τ_w(x)`.

The zeroth term is unused. At the successor step all terms occurring in
`petrescoPriorProduct` have smaller positive indices, so strong recursion
defines the family without any choice. -/
def petrescoTerm (x : List G) : ℕ → G :=
  Nat.strongRec fun w previous =>
    match w with
    | 0 => 1
    | n + 1 =>
        (((List.finRange n).map fun (j : Fin n) =>
          previous ((j : ℕ) + 1) (Nat.succ_lt_succ j.isLt) ^
            Nat.choose (n + 1) ((j : ℕ) + 1)).prod)⁻¹ *
            (x.map fun g => g ^ (n + 1)).prod

@[simp]
lemma petrescoTerm_zero (x : List G) :
    petrescoTerm x 0 = 1 := by
  rw [petrescoTerm, Nat.strongRec_eq]

@[simp]
lemma petrescoTerm_succ (x : List G) (w : ℕ) :
    petrescoTerm x (w + 1) =
      (petrescoPriorProduct (petrescoTerm x) (w + 1))⁻¹ *
        (x.map fun g => g ^ (w + 1)).prod := by
  rw [petrescoTerm, Nat.strongRec_eq]
  rfl

/-- The full binomial product is its proper prefix followed by `τ_w`. -/
lemma petresco_binomial_succ (tau : ℕ → G) (w : ℕ) :
    petrescoBinomialProduct tau (w + 1) =
      petrescoPriorProduct tau (w + 1) * tau (w + 1) := by
  simp only [petrescoBinomialProduct, petrescoPriorProduct,
    List.finRange_succ_last, List.map_append, List.prod_append,
    List.map_singleton, List.prod_singleton, Fin.val_last,
    Nat.choose_self, pow_one, List.map_map]
  rw [mul_right_cancel_iff]
  apply congrArg List.prod
  apply List.map_congr_left
  intro j _
  simp

/-- A family satisfies Hall's Petresco recurrence for the finite product
`x₁ ⋯ xₙ` when simultaneous `w`th powers of the factors collect according
to the binomial-product formula. -/
def IPFam (x : List G) (tau : ℕ → G) : Prop :=
  ∀ w : ℕ, (x.map fun g => g ^ w).prod = petrescoBinomialProduct tau w

/-- The recursively defined Petresco terms satisfy Hall's recurrence. -/
theorem petresco_term_family (x : List G) :
    IPFam x (petrescoTerm x) := by
  intro w
  cases w with
  | zero =>
      simp [petrescoBinomialProduct]
  | succ w =>
      rw [petresco_binomial_succ, petrescoTerm_succ]
      simp

/-- Hall's recurrence uniquely determines every positive-index Petresco
term. The value at zero is intentionally irrelevant. -/
theorem IPFam.eq_petresco_termpos
    {x : List G} {tau : ℕ → G} (h : IPFam x tau) :
    ∀ w : ℕ, 0 < w → tau w = petrescoTerm x w := by
  intro w
  induction w using Nat.strong_induction_on with
  | h w ih =>
      intro hw
      obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hw)
      have hgiven := h (n + 1)
      have hcanonical := petresco_term_family x (n + 1)
      rw [petresco_binomial_succ] at hgiven hcanonical
      have hprior :
          petrescoPriorProduct tau (n + 1) =
            petrescoPriorProduct (petrescoTerm x) (n + 1) := by
        unfold petrescoPriorProduct
        congr 1
        apply List.map_congr_left
        intro j _
        rw [ih ((j : ℕ) + 1)]
        · omega
        · omega
      rw [hprior] at hgiven
      exact mul_left_cancel (hgiven.symm.trans hcanonical)

/-- Applying a group homomorphism to a Petresco binomial product applies it
to every term. -/
lemma petresco_binomial_product
    {H : Type*} [Group H] (f : G →* H) (tau : ℕ → G) (w : ℕ) :
    f (petrescoBinomialProduct tau w) =
      petrescoBinomialProduct (fun j => f (tau j)) w := by
  unfold petrescoBinomialProduct
  rw [map_list_prod]
  rw [List.map_map]
  congr 1
  apply List.map_congr_left
  intro j _
  exact map_pow f _ _

/-- Applying a group homomorphism to a Petresco prefix applies it to every
term. -/
lemma petresco_prior_product
    {H : Type*} [Group H] (f : G →* H) (tau : ℕ → G) (w : ℕ) :
    f (petrescoPriorProduct tau w) =
      petrescoPriorProduct (fun j => f (tau j)) w := by
  unfold petrescoPriorProduct
  rw [map_list_prod]
  rw [List.map_map]
  congr 1
  apply List.map_congr_left
  intro j _
  exact map_pow f _ _

/-- Petresco terms commute with group homomorphisms. -/
lemma map_petrescoTerm
    {H : Type*} [Group H] (f : G →* H) (x : List G) :
    ∀ w : ℕ, f (petrescoTerm x w) = petrescoTerm (x.map f) w := by
  intro w
  induction w using Nat.strong_induction_on with
  | h w ih =>
      cases w with
      | zero =>
          simp
      | succ w =>
          rw [petrescoTerm_succ, petrescoTerm_succ, map_mul, map_inv,
            petresco_prior_product]
          rw [map_list_prod]
          simp only [List.map_map]
          congr 2
          · unfold petrescoPriorProduct
            congr 1
            apply List.map_congr_left
            intro j hj
            change
              f (petrescoTerm x ((j : ℕ) + 1)) ^
                  Nat.choose (w + 1) ((j : ℕ) + 1) =
                petrescoTerm (x.map f) ((j : ℕ) + 1) ^
                  Nat.choose (w + 1) ((j : ℕ) + 1)
            rw [ih (j + 1)]
            omega
          · apply List.map_congr_left
            intro g _
            exact map_pow f g (w + 1)

/-- The word-valued Petresco family on an ordered list of variables. -/
def petrescoWord {X : Type v} (x : List X) (w : ℕ) : FreeGroup X :=
  petrescoTerm (x.map FreeGroup.of) w

/-- Evaluating a Petresco word gives the corresponding Petresco term. -/
lemma word_eval_petresco {X : Type v}
    (x : List X) (w : ℕ) (f : X → G) :
    wordEval (petrescoWord x w) f = petrescoTerm (x.map f) w := by
  change FreeGroup.lift f (petrescoTerm (x.map FreeGroup.of) w) =
    petrescoTerm (x.map f) w
  rw [map_petrescoTerm]
  apply congrArg (fun y : List G => petrescoTerm y w)
  rw [List.map_map]
  apply List.map_congr_left
  intro j _
  exact FreeGroup.lift_apply_of

/-- Evaluated Petresco words satisfy Hall's recurrence. -/
theorem petresco_word_family {X : Type v}
    (x : List X) (f : X → G) :
    IPFam (x.map f) (fun w => wordEval (petrescoWord x w) f) := by
  simpa only [word_eval_petresco] using
    petresco_term_family (x.map f)

/-- The first Petresco term is the original ordered product. -/
lemma IPFam.first {x : List G} {tau : ℕ → G}
    (h : IPFam x tau) :
    tau 1 = x.prod := by
  have h1 := h 1
  simpa [petrescoBinomialProduct] using h1.symm

@[simp]
lemma petrescoTerm_one (x : List G) :
    petrescoTerm x 1 = x.prod := by
  exact (petresco_term_family x).first

/-- The second Petresco term vanishes in a commutative group. -/
lemma petresco_term_commutative
    [IsMulCommutative G] (x : List G) :
    petrescoTerm x 2 = 1 := by
  rw [show 2 = 1 + 1 by omega, petrescoTerm_succ]
  have hprod :
      (x.map fun g => g ^ 2).prod = x.prod ^ 2 := by
    calc
      (x.map fun g => g ^ 2).prod =
          (x.map fun g => g * g).prod := by
            congr 2
            funext g
            exact pow_two g
      _ = (x.map fun g => g).prod * (x.map fun g => g).prod :=
        List.prod_map_mul
      _ = x.prod * x.prod := by simp
      _ = x.prod ^ 2 := (pow_two x.prod).symm
  rw [hprod]
  simp only [petrescoPriorProduct, List.finRange_succ,
    List.finRange_zero, List.map_cons, List.map_nil, List.prod_cons,
    List.prod_nil, Fin.val_zero, zero_add, Nat.choose, petrescoTerm_one]
  simp only [Nat.add_zero, pow_two, mul_one]
  rw [show 1 + 1 = (2 : ℕ) by omega, pow_two]
  exact inv_mul_cancel (x.prod * x.prod)

/-- The first nontrivial case of Hall's Theorem 6.3:
`τ₂(x₁,...,xₙ)` belongs to the commutator subgroup. -/
theorem petresco_term_series (x : List G) :
    petrescoTerm x 2 ∈ Subgroup.lowerCentralSeries G 1 := by
  let q : G →* G ⧸ Subgroup.lowerCentralSeries G 1 :=
    QuotientGroup.mk' (Subgroup.lowerCentralSeries G 1)
  apply (QuotientGroup.eq_one_iff (petrescoTerm x 2)).mp
  change q (petrescoTerm x 2) = 1
  rw [map_petrescoTerm]
  letI : IsMulCommutative (G ⧸ Subgroup.lowerCentralSeries G 1) := by
    apply (Subgroup.Normal.quotient_commutative_iff_commutator_le).2
    rfl
  exact petresco_term_commutative (x.map q)

/-! ## The group-side collection rewrite -/

/-- Evaluate a list of formal commutators as an ordered group product. -/
def evalFormalWord {X : Type v} (f : X → G)
    (l : List (FormalCommutator X)) : G :=
  (l.map (formalGroupCommutator f)).prod

@[simp]
lemma eval_formal_nil {X : Type v} (f : X → G) :
    evalFormalWord f [] = 1 :=
  rfl

@[simp]
lemma eval_formal_cons {X : Type v} (f : X → G)
    (c : FormalCommutator X) (l : List (FormalCommutator X)) :
    evalFormalWord f (c :: l) =
      formalGroupCommutator f c * evalFormalWord f l :=
  rfl

@[simp]
lemma eval_formal_append {X : Type v} (f : X → G)
    (l r : List (FormalCommutator X)) :
    evalFormalWord f (l ++ r) =
      evalFormalWord f l * evalFormalWord f r := by
  simp [evalFormalWord]

/-- **Hall, Lemma 6.2, projected-support form.** Retaining projected labels
in `S` keeps exactly the formal factors whose projected supports lie in
`S`. -/
lemma formal_projected_variables
    {X : Type v} {L : Type w} [DecidableEq L]
    (label : X → L) (S : Finset L) (f : X → G)
    (l : List (FormalCommutator X)) :
    evalFormalWord (retainProjectedVariables label S f) l =
      evalFormalWord f
        (l.filter fun c => projectedFormalSupport label c ⊆ S) := by
  induction l with
  | nil =>
      rfl
  | cons c l ih =>
      by_cases hc : projectedFormalSupport label c ⊆ S
      · rw [eval_formal_cons,
          retain_projected_variables
            label S f c hc]
        simp only [List.filter_cons, decide_eq_true_eq, hc, ↓reduceIte,
          eval_formal_cons, ih]
      · rw [eval_formal_cons,
          formal_retain_variables
            label S f c hc]
        simp only [List.filter_cons, decide_eq_true_eq, hc, ↓reduceIte,
          one_mul, ih]

/-- Hall's elementary adjacent collection rewrite `uv = vu[u,v]`. -/
lemma eval_formal_swap {X : Type v} (f : X → G)
    (u v : FormalCommutator X) :
    formalGroupCommutator f u * formalGroupCommutator f v =
      formalGroupCommutator f v * formalGroupCommutator f u *
        formalGroupCommutator f (formalBracket u v) := by
  simp [hallCommutator, mul_assoc]

/-- The adjacent collection rewrite inside an arbitrary formal word. -/
lemma formal_group_swap {X : Type v} (f : X → G)
    (pre post : List (FormalCommutator X)) (u v : FormalCommutator X) :
    evalFormalWord f (pre ++ u :: v :: post) =
      evalFormalWord f
        (pre ++ v :: u :: formalBracket u v :: post) := by
  simp only [eval_formal_append, eval_formal_cons]
  calc
    evalFormalWord f pre *
          (formalGroupCommutator f u *
            (formalGroupCommutator f v * evalFormalWord f post)) =
        evalFormalWord f pre *
          ((formalGroupCommutator f u *
            formalGroupCommutator f v) * evalFormalWord f post) := by
      simp [mul_assoc]
    _ = evalFormalWord f pre *
          ((formalGroupCommutator f v *
              formalGroupCommutator f u *
                formalGroupCommutator f (formalBracket u v)) *
            evalFormalWord f post) := by
      rw [eval_formal_swap]
    _ = evalFormalWord f pre *
          (formalGroupCommutator f v *
            (formalGroupCommutator f u *
              (formalGroupCommutator f (formalBracket u v) *
                evalFormalWord f post))) := by
      simp [mul_assoc]

/-- Extract the first selected factor, bubbling it to the front and
recording the commutator correction introduced at every swap. -/
def extractFormalFactor {X : Type v}
    (selected : FormalCommutator X → Bool) :
    List (FormalCommutator X) →
      Option (FormalCommutator X × List (FormalCommutator X))
  | [] => none
  | u :: l =>
      if selected u then
        some (u, l)
      else
        match extractFormalFactor selected l with
        | none => none
        | some (v, r) => some (v, u :: formalBracket u v :: r)

/-- Bubbling an extracted factor to the front preserves the evaluated
group product exactly. -/
lemma formal_extract_factor
    {X : Type v} (f : X → G) (selected : FormalCommutator X → Bool)
    {l : List (FormalCommutator X)}
    {v : FormalCommutator X} {r : List (FormalCommutator X)}
    (h : extractFormalFactor selected l = some (v, r)) :
    evalFormalWord f l = evalFormalWord f (v :: r) := by
  induction l generalizing v r with
  | nil =>
      simp [extractFormalFactor] at h
  | cons u l ih =>
      by_cases hu : selected u
      · simp only [extractFormalFactor, if_pos hu, Option.some.injEq,
          Prod.mk.injEq] at h
        rcases h with ⟨rfl, rfl⟩
        rfl
      · rw [extractFormalFactor, if_neg hu] at h
        cases hextract : extractFormalFactor selected l with
        | none =>
          simp [hextract] at h
        | some z =>
          rcases z with ⟨w, s⟩
          simp only [hextract] at h
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          rcases h with ⟨rfl, rfl⟩
          have hi := ih hextract
          simp only [eval_formal_cons] at hi ⊢
          calc
            formalGroupCommutator f u * evalFormalWord f l =
                formalGroupCommutator f u *
                  (formalGroupCommutator f w *
                    evalFormalWord f s) := by
              rw [hi]
            _ = (formalGroupCommutator f u *
                  formalGroupCommutator f w) *
                    evalFormalWord f s := by
              simp [mul_assoc]
            _ = (formalGroupCommutator f w *
                    formalGroupCommutator f u *
                      formalGroupCommutator f (formalBracket u w)) *
                        evalFormalWord f s := by
              rw [eval_formal_swap]
            _ = formalGroupCommutator f w *
                  (formalGroupCommutator f u *
                    (formalGroupCommutator f (formalBracket u w) *
                      evalFormalWord f s)) := by
              simp [mul_assoc]

/-- Perform at most `n` leftward factor extractions. The support collector
below supplies a bound and uses the residual word for the next support. -/
def collectFormalAux {X : Type v}
    (selected : FormalCommutator X → Bool) :
    ℕ → List (FormalCommutator X) → List (FormalCommutator X)
  | 0, l => l
  | n + 1, l =>
      match extractFormalFactor selected l with
      | none => l
      | some (v, r) => v :: collectFormalAux selected n r

/-- Every bounded collection pass preserves the evaluated group product. -/
lemma formal_collect_aux
    {X : Type v} (f : X → G) (selected : FormalCommutator X → Bool) :
    ∀ n : ℕ, ∀ l : List (FormalCommutator X),
      evalFormalWord f (collectFormalAux selected n l) =
        evalFormalWord f l := by
  intro n
  induction n with
  | zero =>
      intro l
      rfl
  | succ n ih =>
      intro l
      simp only [collectFormalAux]
      split
      · rfl
      · rename_i v r h
        rw [eval_formal_cons, ih]
        exact (formal_extract_factor f selected h).symm

/-- Extracting a selected factor removes exactly one selected factor when
all correction brackets introduced while bubbling stay unselected. -/
lemma count_extract_formal
    {X : Type v} (selected : FormalCommutator X → Bool)
    (hclosed :
      ∀ u v, ¬ selected u = true → selected v = true →
        ¬ selected (formalBracket u v) = true)
    {l : List (FormalCommutator X)}
    {v : FormalCommutator X} {r : List (FormalCommutator X)}
    (h : extractFormalFactor selected l = some (v, r)) :
    selected v = true ∧ List.countP selected l = List.countP selected r + 1 := by
  induction l generalizing v r with
  | nil =>
      simp [extractFormalFactor] at h
  | cons u l ih =>
      by_cases hu : selected u
      · simp only [extractFormalFactor, if_pos hu, Option.some.injEq,
          Prod.mk.injEq] at h
        rcases h with ⟨rfl, rfl⟩
        constructor
        · exact hu
        · simp [hu]
      · rw [extractFormalFactor, if_neg hu] at h
        cases hextract : extractFormalFactor selected l with
        | none =>
          simp [hextract] at h
        | some z =>
          rcases z with ⟨w, s⟩
          simp only [hextract] at h
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          rcases h with ⟨rfl, rfl⟩
          obtain ⟨hw, hcount⟩ := ih hextract
          have hbracket := hclosed u w hu hw
          constructor
          · exact hw
          · simp [hu, hbracket, hcount]

/-- A word containing a selected factor admits a bubbled extraction. -/
lemma extract_formal_pos
    {X : Type v} (selected : FormalCommutator X → Bool)
    {l : List (FormalCommutator X)} (hpos : 0 < List.countP selected l) :
    ∃ v r, extractFormalFactor selected l = some (v, r) := by
  induction l with
  | nil =>
      simp at hpos
  | cons u l ih =>
      by_cases hu : selected u
      · exact ⟨u, l, by simp [extractFormalFactor, hu]⟩
      · have htail : 0 < List.countP selected l := by
          simpa [List.countP_cons, hu] using hpos
        obtain ⟨v, r, h⟩ := ih htail
        exact ⟨v, u :: formalBracket u v :: r,
          by simp [extractFormalFactor, hu, h]⟩

/-- Collect up to `n` selected factors into a separate leading block,
leaving the residual formal word as the second component. -/
def splitFormalAux {X : Type v}
    (selected : FormalCommutator X → Bool) :
    ℕ → List (FormalCommutator X) →
      List (FormalCommutator X) × List (FormalCommutator X)
  | 0, l => ([], l)
  | n + 1, l =>
      match extractFormalFactor selected l with
      | none => ([], l)
      | some (v, r) =>
          let qr := splitFormalAux selected n r
          (v :: qr.1, qr.2)

/-- The block and residual word produced by a bounded collection pass
evaluate to the original word. -/
lemma formal_split_aux
    {X : Type v} (f : X → G) (selected : FormalCommutator X → Bool) :
    ∀ n : ℕ, ∀ l : List (FormalCommutator X),
      let qr := splitFormalAux selected n l
      evalFormalWord f qr.1 * evalFormalWord f qr.2 =
        evalFormalWord f l := by
  intro n
  induction n with
  | zero =>
      intro l
      simp [splitFormalAux]
  | succ n ih =>
      intro l
      simp only [splitFormalAux]
      split
      · simp
      · rename_i v r h
        simp only [eval_formal_cons]
        rw [mul_assoc, ih]
        simpa only [eval_formal_cons] using
          (formal_extract_factor f selected h).symm

/-- Run enough extraction steps to collect every selected factor. -/
def splitCollectFormal {X : Type v}
    (selected : FormalCommutator X → Bool)
    (l : List (FormalCommutator X)) :
    List (FormalCommutator X) × List (FormalCommutator X) :=
  splitFormalAux selected (List.countP selected l) l

/-- A complete collection pass produces a selected block and a residual
word with no selected factors. -/
lemma split_collect_spec
    {X : Type v} (selected : FormalCommutator X → Bool)
    (hclosed :
      ∀ u v, ¬ selected u = true → selected v = true →
        ¬ selected (formalBracket u v) = true) :
    ∀ l : List (FormalCommutator X),
      let qr := splitCollectFormal selected l
      (∀ c ∈ qr.1, selected c = true) ∧
        List.countP selected qr.2 = 0 := by
  intro l
  unfold splitCollectFormal
  generalize hn : List.countP selected l = n
  induction n using Nat.strong_induction_on generalizing l with
  | h n ih =>
      cases n with
      | zero =>
          simp [splitFormalAux, hn]
      | succ n =>
          obtain ⟨v, r, hextract⟩ :=
            extract_formal_pos selected
              (l := l) (by omega)
          obtain ⟨hv, hcount⟩ :=
            count_extract_formal selected hclosed hextract
          have hr : List.countP selected r = n := by omega
          have hrec := ih n (by omega) r hr
          simp only [splitFormalAux, hextract]
          simpa [hv] using hrec

/-- A complete collection pass preserves the evaluated group product. -/
lemma formal_split_factors
    {X : Type v} (f : X → G) (selected : FormalCommutator X → Bool)
    (l : List (FormalCommutator X)) :
    let qr := splitCollectFormal selected l
    evalFormalWord f qr.1 * evalFormalWord f qr.2 =
      evalFormalWord f l :=
  formal_split_aux f selected
    (List.countP selected l) l

/-- Bubbling a factor preserves any property which is preserved by
bracketing on the right. -/
lemma extract_formal_forall
    {X : Type v} (selected : FormalCommutator X → Bool)
    (P : FormalCommutator X → Prop)
    (hbracket : ∀ u v, P u → P (formalBracket u v))
    {l : List (FormalCommutator X)}
    {v : FormalCommutator X} {r : List (FormalCommutator X)}
    (hl : ∀ c ∈ l, P c)
    (h : extractFormalFactor selected l = some (v, r)) :
    P v ∧ ∀ c ∈ r, P c := by
  induction l generalizing v r with
  | nil =>
      simp [extractFormalFactor] at h
  | cons u l ih =>
      have huP : P u := hl u (by simp)
      have hlP : ∀ c ∈ l, P c := by
        intro c hc
        exact hl c (by simp [hc])
      by_cases hu : selected u
      · simp only [extractFormalFactor, if_pos hu, Option.some.injEq,
          Prod.mk.injEq] at h
        rcases h with ⟨rfl, rfl⟩
        exact ⟨huP, hlP⟩
      · rw [extractFormalFactor, if_neg hu] at h
        cases hextract : extractFormalFactor selected l with
        | none =>
          simp [hextract] at h
        | some z =>
          rcases z with ⟨w, s⟩
          simp only [hextract] at h
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          rcases h with ⟨rfl, rfl⟩
          obtain ⟨hwP, hsP⟩ := ih hlP hextract
          exact ⟨hwP, by
            intro c hc
            simp only [List.mem_cons] at hc
            rcases hc with rfl | rfl | hc
            · exact huP
            · exact hbracket u w huP
            · exact hsP c hc⟩

/-- A bounded split-collection pass preserves a bracket-stable property
on both its leading block and its residual word. -/
lemma split_aux_forall
    {X : Type v} (selected : FormalCommutator X → Bool)
    (P : FormalCommutator X → Prop)
    (hbracket : ∀ u v, P u → P (formalBracket u v)) :
    ∀ n : ℕ, ∀ l : List (FormalCommutator X),
      (∀ c ∈ l, P c) →
      let qr := splitFormalAux selected n l
      (∀ c ∈ qr.1, P c) ∧ ∀ c ∈ qr.2, P c := by
  intro n
  induction n with
  | zero =>
      intro l hl
      exact ⟨(fun _ h => nomatch h), hl⟩
  | succ n ih =>
      intro l hl
      simp only [splitFormalAux]
      split
      · exact ⟨by simp, hl⟩
      · rename_i v r hextract
        obtain ⟨hv, hr⟩ :=
          extract_formal_forall selected P hbracket hl hextract
        obtain ⟨hq, hs⟩ := ih r hr
        exact ⟨by
          intro c hc
          simp only [List.mem_cons] at hc
          rcases hc with rfl | hc
          · exact hv
          · exact hq c hc, hs⟩

/-- A complete split-collection pass preserves a bracket-stable property
on both its leading block and its residual word. -/
lemma split_formal_forall
    {X : Type v} (selected : FormalCommutator X → Bool)
    (P : FormalCommutator X → Prop)
    (hbracket : ∀ u v, P u → P (formalBracket u v))
    (l : List (FormalCommutator X)) (hl : ∀ c ∈ l, P c) :
    let qr := splitCollectFormal selected l
    (∀ c ∈ qr.1, P c) ∧ ∀ c ∈ qr.2, P c :=
  split_aux_forall selected P hbracket
    (List.countP selected l) l hl

/-- Test whether every component of a formal commutator is drawn from
the labels in `S`. -/
def formalSubsetSelector {X : Type v} [DecidableEq X]
    (S : Finset X) (c : FormalCommutator X) : Bool :=
  decide (formalSupport c ⊆ S)

@[simp]
lemma subset_selector_true
    {X : Type v} [DecidableEq X] (S : Finset X)
    (c : FormalCommutator X) :
    formalSubsetSelector S c = true ↔ formalSupport c ⊆ S := by
  simp [formalSubsetSelector]

/-- A bracket remains outside `S` when its left input already has a
component outside `S`. -/
lemma selector_bracket_selected
    {X : Type v} [DecidableEq X] (S : Finset X)
    (u v : FormalCommutator X)
    (hu : ¬ formalSubsetSelector S u = true) :
    ¬ formalSubsetSelector S (formalBracket u v) = true := by
  simp only [subset_selector_true] at hu ⊢
  intro huv
  apply hu
  intro x hx
  exact huv (Finset.mem_union_left _ hx)

/-- Collect the factors supported inside `S` into a leading block. -/
def splitFormalSubset
    {X : Type v} [DecidableEq X] (S : Finset X)
    (l : List (FormalCommutator X)) :
    List (FormalCommutator X) × List (FormalCommutator X) :=
  splitCollectFormal (formalSubsetSelector S) l

/-- A support-subset collection pass has Hall's required shape: every
factor in the leading block is supported inside `S`, every residual
factor has a component outside `S`, and the product is unchanged. -/
lemma split_formal_spec
    {X : Type v} [DecidableEq X] (f : X → G) (S : Finset X)
    (l : List (FormalCommutator X)) :
    let qr := splitFormalSubset S l
    (∀ c ∈ qr.1, formalSupport c ⊆ S) ∧
      (∀ c ∈ qr.2, ¬ formalSupport c ⊆ S) ∧
        evalFormalWord f qr.1 * evalFormalWord f qr.2 =
          evalFormalWord f l := by
  let selected := formalSubsetSelector S
  have hclosed :
      ∀ u v, ¬ selected u = true → selected v = true →
        ¬ selected (formalBracket u v) = true := by
    intro u v hu _
    exact selector_bracket_selected S u v hu
  have hspec := split_collect_spec selected hclosed l
  have heval := formal_split_factors
    f selected l
  change
    let qr := splitCollectFormal selected l
    (∀ c ∈ qr.1, formalSupport c ⊆ S) ∧
      (∀ c ∈ qr.2, ¬ formalSupport c ⊆ S) ∧
        evalFormalWord f qr.1 * evalFormalWord f qr.2 =
          evalFormalWord f l
  generalize hqr : splitCollectFormal selected l = qr at hspec heval ⊢
  rcases qr with ⟨q, r⟩
  simp only at hspec heval ⊢
  refine ⟨?_, ?_, heval⟩
  · intro c hc
    exact (subset_selector_true S c).mp (hspec.1 c hc)
  · have hnone := List.countP_eq_zero.mp hspec.2
    intro c hc
    exact fun hsupport =>
      (hnone c hc) ((subset_selector_true S c).mpr hsupport)

/-- Collect support-subset blocks successively in the supplied order. -/
def splitFormalSubsets
    {X : Type v} [DecidableEq X] :
    List (Finset X) → List (FormalCommutator X) →
      List (List (FormalCommutator X)) × List (FormalCommutator X)
  | [], l => ([], l)
  | S :: supports, l =>
      let qr := splitFormalSubset S l
      let br :=
        splitFormalSubsets supports qr.2
      (qr.1 :: br.1, br.2)

/-- Successive support-subset collection preserves any property stable
under bracketing on the right. -/
lemma split_subsets_forall
    {X : Type v} [DecidableEq X]
    (P : FormalCommutator X → Prop)
    (hbracket : ∀ u v, P u → P (formalBracket u v)) :
    ∀ supports : List (Finset X), ∀ l : List (FormalCommutator X),
      (∀ c ∈ l, P c) →
      let qr := splitFormalSubsets supports l
      (∀ q ∈ qr.1, ∀ c ∈ q, P c) ∧ ∀ c ∈ qr.2, P c := by
  intro supports
  induction supports with
  | nil =>
      intro l hl
      exact ⟨(fun _ h => nomatch h), hl⟩
  | cons S supports ih =>
      intro l hl
      simp only [splitFormalSubsets]
      let qr := splitFormalSubset S l
      obtain ⟨hq, hr⟩ :=
        split_formal_forall
          (formalSubsetSelector S) P hbracket l hl
      let br := splitFormalSubsets supports qr.2
      obtain ⟨hblocks, hresidual⟩ := ih qr.2 hr
      exact ⟨by
        intro q hqmem
        simp only [List.mem_cons] at hqmem
        rcases hqmem with rfl | hqmem
        · exact hq
        · exact hblocks q hqmem, hresidual⟩

/-- Successive collection produces one support-subset block for each
requested support, leaves no residual factor supported inside any requested
set, and preserves the evaluated group product. -/
lemma split_subsets_spec
    {X : Type v} [DecidableEq X] (f : X → G) :
    ∀ supports : List (Finset X), ∀ l : List (FormalCommutator X),
      let qr := splitFormalSubsets supports l
      List.Forall₂
          (fun S q => ∀ c ∈ q, formalSupport c ⊆ S) supports qr.1 ∧
        (∀ c ∈ qr.2, ∀ S ∈ supports, ¬ formalSupport c ⊆ S) ∧
          evalFormalWord f qr.1.flatten * evalFormalWord f qr.2 =
            evalFormalWord f l := by
  intro supports
  induction supports with
  | nil =>
      intro l
      simp [splitFormalSubsets]
  | cons S supports ih =>
      intro l
      simp only [splitFormalSubsets]
      generalize hqr :
        splitFormalSubset S l = qr
      rcases qr with ⟨q, r⟩
      have hsingle :=
        split_formal_spec f S l
      rw [hqr] at hsingle
      generalize hbr :
        splitFormalSubsets supports r = br
      rcases br with ⟨blocks, residual⟩
      have hrec := ih r
      rw [hbr] at hrec
      have houtside :
          ∀ c ∈ residual, ¬ formalSupport c ⊆ S := by
        have hstable :
            ∀ u v : FormalCommutator X,
              (¬ formalSupport u ⊆ S) →
                ¬ formalSupport (formalBracket u v) ⊆ S := by
          intro u v hu huv
          apply hu
          intro x hx
          exact huv (Finset.mem_union_left _ hx)
        have hpersist :=
          split_subsets_forall
            (fun c => ¬ formalSupport c ⊆ S) hstable supports r hsingle.2.1
        rw [hbr] at hpersist
        exact hpersist.2
      refine ⟨List.Forall₂.cons hsingle.1 hrec.1, ?_, ?_⟩
      · intro c hc T hT
        simp only [List.mem_cons] at hT
        rcases hT with rfl | hT
        · exact houtside c hc
        · exact hrec.2.1 c hc T hT
      · simp only [List.flatten_cons, eval_formal_append]
        rw [mul_assoc, hrec.2.2, hsingle.2.2]

/-- If the requested supports contain every nonempty support and are
ordered by nondecreasing cardinality, successive collection produces
exact-support blocks and consumes the entire formal word. -/
lemma split_subsets_exact
    {X : Type v} [DecidableEq X] (f : X → G)
    (supports : List (Finset X))
    (hcomplete : ∀ S : Finset X, S.Nonempty → S ∈ supports)
    (hsorted : supports.Pairwise fun S T => S.card ≤ T.card)
    (l : List (FormalCommutator X)) :
    let qr := splitFormalSubsets supports l
    List.Forall₂
        (fun S q => ∀ c ∈ q, formalSupport c = S) supports qr.1 ∧
      qr.2 = [] ∧ evalFormalWord f qr.1.flatten =
        evalFormalWord f l := by
  have haux :
      ∀ (prior supports : List (Finset X))
          (l : List (FormalCommutator X)),
        (∀ c ∈ l, ∀ S ∈ prior, ¬ formalSupport c ⊆ S) →
        (∀ S : Finset X, S.Nonempty → S ∈ prior ++ supports) →
        supports.Pairwise (fun S T => S.card ≤ T.card) →
        let qr := splitFormalSubsets supports l
        List.Forall₂
            (fun S q => ∀ c ∈ q, formalSupport c = S) supports qr.1 ∧
          qr.2 = [] ∧ evalFormalWord f qr.1.flatten =
            evalFormalWord f l := by
    intro prior supports
    induction supports generalizing prior with
    | nil =>
        intro l houtside hcomplete _
        have hl : l = [] := by
          apply List.eq_nil_iff_forall_not_mem.mpr
          intro c hc
          have hmem := hcomplete (formalSupport c) (formalSupport_nonempty c)
          simp only [List.append_nil] at hmem
          exact (houtside c hc (formalSupport c) hmem) (by rfl)
        subst l
        simp [splitFormalSubsets]
    | cons S supports ih =>
        intro l houtside hcomplete hsorted
        rw [List.pairwise_cons] at hsorted
        generalize hqr :
          splitFormalSubset S l = qr
        rcases qr with ⟨q, r⟩
        have hsingle :=
          split_formal_spec f S l
        rw [hqr] at hsingle
        let P : FormalCommutator X → Prop :=
          fun c => ∀ T ∈ prior, ¬ formalSupport c ⊆ T
        have hPstable :
            ∀ u v : FormalCommutator X, P u → P (formalBracket u v) := by
          intro u v hu T hT huv
          apply hu T hT
          intro x hx
          exact huv (Finset.mem_union_left _ hx)
        have hpass :=
          split_formal_forall
            (formalSubsetSelector S) P hPstable l houtside
        change
          let qr := splitFormalSubset S l
          (∀ c ∈ qr.1, P c) ∧ ∀ c ∈ qr.2, P c at hpass
        rw [hqr] at hpass
        have hqexact : ∀ c ∈ q, formalSupport c = S := by
          intro c hc
          have hcS : formalSupport c ⊆ S := hsingle.1 c hc
          by_contra hne
          have hproper : formalSupport c ⊂ S :=
            Finset.ssubset_iff_subset_ne.mpr ⟨hcS, hne⟩
          have hmem :=
            hcomplete (formalSupport c) (formalSupport_nonempty c)
          simp only [List.mem_append, List.mem_cons] at hmem
          rcases hmem with hprior | hcur | htail
          · exact (hpass.1 c hc (formalSupport c) hprior) (by rfl)
          · exact hne hcur
          · exact (Nat.not_lt_of_ge (hsorted.1 _ htail))
              (Finset.card_lt_card hproper)
        have houtside' :
            ∀ c ∈ r, ∀ T ∈ prior ++ [S], ¬ formalSupport c ⊆ T := by
          intro c hc T hT
          simp only [List.mem_append, List.mem_singleton] at hT
          rcases hT with hprior | rfl
          · exact hpass.2 c hc T hprior
          · exact hsingle.2.1 c hc
        have hcomplete' :
            ∀ T : Finset X, T.Nonempty → T ∈ (prior ++ [S]) ++ supports := by
          intro T hT
          simpa only [List.append_assoc, List.singleton_append] using
            hcomplete T hT
        have hrec := ih (prior ++ [S]) r houtside' hcomplete' hsorted.2
        generalize hbr :
          splitFormalSubsets supports r = br
        rcases br with ⟨blocks, residual⟩
        rw [hbr] at hrec
        simp only [splitFormalSubsets, hqr, hbr]
        refine ⟨List.Forall₂.cons hqexact hrec.1, hrec.2.1, ?_⟩
        simp only [List.flatten_cons, eval_formal_append]
        rw [hrec.2.2, hsingle.2.2]
  exact haux [] supports l (by simp) (by simpa using hcomplete) hsorted

/-- Collecting formal commutator factors in a complete cardinality-ordered
list of nonempty supports produces one exact-support block for each
requested support and preserves the original product. -/
theorem collect_formal_exact
    {X : Type v} [DecidableEq X] (f : X → G)
    (supports : List (Finset X))
    (hcomplete : ∀ S : Finset X, S.Nonempty → S ∈ supports)
    (hsorted : supports.Pairwise fun S T => S.card ≤ T.card)
    (l : List (FormalCommutator X)) :
    ∃ blocks : List (List (FormalCommutator X)),
      List.Forall₂
          (fun S q => ∀ c ∈ q, formalSupport c = S) supports blocks ∧
        evalFormalWord f l = evalFormalWord f blocks.flatten := by
  let qr := splitFormalSubsets supports l
  have h :=
    split_subsets_exact
      f supports hcomplete hsorted l
  exact ⟨qr.1, h.1, h.2.2.symm⟩

/-- The canonical list of nonempty supports, ordered by cardinality. -/
noncomputable def cardinalityNonemptySupports
    (X : Type v) [Fintype X] [DecidableEq X] : List (Finset X) :=
  ((((Finset.univ : Finset X).powerset).erase ∅).toList).mergeSort
    fun S T => decide (S.card ≤ T.card)

@[simp]
lemma cardinality_nonempty_supports
    {X : Type v} [Fintype X] [DecidableEq X] (S : Finset X) :
    S ∈ cardinalityNonemptySupports X ↔ S.Nonempty := by
  simp [cardinalityNonemptySupports, Finset.nonempty_iff_ne_empty]

/-- The canonical support list is ordered by nondecreasing cardinality. -/
lemma cardinality_supports_pairwise
    (X : Type v) [Fintype X] [DecidableEq X] :
    (cardinalityNonemptySupports X).Pairwise
      fun S T => S.card ≤ T.card := by
  unfold cardinalityNonemptySupports
  simpa only [decide_eq_true_eq] using
    (List.pairwise_mergeSort
      (le := fun S T : Finset X => decide (S.card ≤ T.card))
      (fun _ _ _ hab hbc => by
        simp only [decide_eq_true_eq] at hab hbc ⊢
        exact le_trans hab hbc)
      (fun S T => by
        simp only [Bool.or_eq_true, decide_eq_true_eq]
        exact Nat.le_total S.card T.card)
      ((((Finset.univ : Finset X).powerset).erase ∅).toList))

/-- Natural numbers below `n` occur in strictly increasing order in
`List.range n`. -/
lemma range_pairwise_lt : ∀ n : ℕ, (List.range n).Pairwise fun i j => i < j
  | 0 => by simp
  | n + 1 => by
      rw [List.range_succ, List.pairwise_append]
      exact ⟨range_pairwise_lt n, by simp, by
        intro i hi j hj
        simp only [List.mem_singleton] at hj
        subst j
        exact List.mem_range.mp hi⟩

/-- The canonical nonempty supports grouped explicitly by cardinality:
singletons first, then pairs, and so on. -/
noncomputable def levelNonemptySupports
    (X : Type v) [Fintype X] [DecidableEq X] : List (Finset X) :=
  (List.range (Fintype.card X)).flatMap fun k =>
    ((Finset.univ : Finset X).powersetCard (k + 1)).toList

/-- Every nonempty finite support occurs in the level-ordered list. -/
lemma level_nonempty_supports
    {X : Type v} [Fintype X] [DecidableEq X]
    (S : Finset X) (hS : S.Nonempty) :
    S ∈ levelNonemptySupports X := by
  rw [levelNonemptySupports, List.mem_flatMap]
  refine ⟨S.card - 1, ?_, ?_⟩
  · rw [List.mem_range]
    have hcard : 1 ≤ S.card := Finset.one_le_card.mpr hS
    have hle := Finset.card_le_univ S
    omega
  · simp only [Finset.mem_toList, Finset.mem_powersetCard_univ]
    exact (Nat.sub_add_cancel (Finset.one_le_card.mpr hS)).symm

/-- Every support occurring in the explicit level ordering is nonempty. -/
lemma nonempty_level_supports
    {X : Type v} [Fintype X] [DecidableEq X]
    {S : Finset X} (hS : S ∈ levelNonemptySupports X) :
    S.Nonempty := by
  rw [levelNonemptySupports, List.mem_flatMap] at hS
  obtain ⟨k, _, hk⟩ := hS
  simp only [Finset.mem_toList, Finset.mem_powersetCard_univ] at hk
  exact Finset.one_le_card.mp (by omega)

/-- The explicitly level-ordered support list is cardinality sorted. -/
lemma level_supports_pairwise
    (X : Type v) [Fintype X] [DecidableEq X] :
    (levelNonemptySupports X).Pairwise
      fun S T => S.card ≤ T.card := by
  rw [levelNonemptySupports, List.pairwise_flatMap]
  constructor
  · intro k hk
    rw [List.pairwise_iff_get]
    intro i j _
    have hi :=
      List.get_mem (((Finset.univ : Finset X).powersetCard (k + 1)).toList) i
    have hj :=
      List.get_mem (((Finset.univ : Finset X).powersetCard (k + 1)).toList) j
    simp only [Finset.mem_toList, Finset.mem_powersetCard_univ] at hi hj
    omega
  · refine (range_pairwise_lt (Fintype.card X)).imp ?_
    intro k j hkj S hS T hT
    simp only [Finset.mem_toList, Finset.mem_powersetCard_univ] at hS hT
    omega

/-- The explicitly level-ordered support list contains no duplicates. -/
lemma level_supports_nodup
    (X : Type v) [Fintype X] [DecidableEq X] :
    (levelNonemptySupports X).Nodup := by
  rw [levelNonemptySupports, List.nodup_flatMap]
  constructor
  · intro k _
    exact Finset.nodup_toList _
  · refine (range_pairwise_lt (Fintype.card X)).imp ?_
    intro k j hkj
    change
      ((Finset.univ : Finset X).powersetCard (k + 1)).toList.Disjoint
        ((Finset.univ : Finset X).powersetCard (j + 1)).toList
    rw [List.disjoint_left]
    intro S hSk hSj
    simp only [Finset.mem_toList, Finset.mem_powersetCard_univ] at hSk hSj
    omega

/-- Among the `k`-element supports on a finite type, exactly
`choose |S| k` lie inside `S`. -/
lemma powerset_subset_choose
    {X : Type v} [Fintype X] [DecidableEq X]
    (S : Finset X) (k : ℕ) :
    List.countP (fun T => decide (T ⊆ S))
        (((Finset.univ : Finset X).powersetCard k).toList) =
      Nat.choose S.card k := by
  rw [List.countP_eq_length_filter,
    ← List.toFinset_card_of_nodup
      ((Finset.nodup_toList _).filter (fun T => decide (T ⊆ S)))]
  have hfilter :
      ((((Finset.univ : Finset X).powersetCard k).toList.filter
          fun T => decide (T ⊆ S)).toFinset) =
        S.powersetCard k := by
    ext T
    simp only [List.mem_toFinset, List.mem_filter, Finset.mem_toList,
      decide_eq_true_eq, Finset.mem_powersetCard]
    constructor
    · rintro ⟨⟨_, hcard⟩, hsub⟩
      exact ⟨hsub, hcard⟩
    · rintro ⟨hsub, hcard⟩
      exact ⟨⟨Finset.subset_univ T, hcard⟩, hsub⟩
  rw [hfilter, Finset.card_powersetCard]

/-- A list containing `g` in the selected positions and `1` elsewhere has
product `g` to the number of selected positions. -/
lemma prod_ite_p
    {A : Type*} (p : A → Bool) (l : List A) (g : G) :
    (l.map fun a => if p a then g else 1).prod =
      g ^ List.countP p l := by
  induction l with
  | nil =>
      simp
  | cons a l ih =>
      by_cases ha : p a
      · simp [ha, ih, pow_succ']
      · simp [ha, ih]

/-- If every retained `k`-support contributes the same group element `a`,
their ordered product is `a^(choose |S| k)`. -/
lemma powerset_ite_choose
    {X : Type v} [Fintype X] [DecidableEq X]
    (S : Finset X) (k : ℕ) (a : G) :
    ((((Finset.univ : Finset X).powersetCard k).toList.map fun T =>
      if T ⊆ S then a else 1).prod) =
      a ^ Nat.choose S.card k := by
  have hite :
      (((Finset.univ : Finset X).powersetCard k).toList.map fun T =>
          if T ⊆ S then a else 1) =
        (((Finset.univ : Finset X).powersetCard k).toList.map fun T =>
          if decide (T ⊆ S) then a else 1) := by
    apply List.map_congr_left
    intro T _
    by_cases hT : T ⊆ S <;> simp [hT]
  rw [hite, prod_ite_p,
    powerset_subset_choose]

/-- The explicit cardinality layers turn a support-subset product whose
value depends only on support size into the corresponding binomial-power
product. -/
lemma nonempty_supports_ite
    {X : Type v} [Fintype X] [DecidableEq X]
    (S : Finset X) (a : ℕ → G) :
    ((levelNonemptySupports X).map fun T =>
      if T ⊆ S then a T.card else 1).prod =
      ((List.range (Fintype.card X)).map fun k =>
        a (k + 1) ^ Nat.choose S.card (k + 1)).prod := by
  unfold levelNonemptySupports
  have hlayer :
      ∀ k : ℕ,
        (((Finset.univ : Finset X).powersetCard (k + 1)).toList.map
          fun T => if T ⊆ S then a T.card else 1).prod =
            a (k + 1) ^ Nat.choose S.card (k + 1) := by
    intro k
    have hmap :
        (((Finset.univ : Finset X).powersetCard (k + 1)).toList.map
            fun T => if T ⊆ S then a T.card else 1) =
          (((Finset.univ : Finset X).powersetCard (k + 1)).toList.map
            fun T => if T ⊆ S then a (k + 1) else 1) := by
      apply List.map_congr_left
      intro T hT
      have hcard : T.card = k + 1 := by
        simpa only [Finset.mem_toList, Finset.mem_powersetCard_univ] using hT
      rw [hcard]
    rw [hmap]
    exact powerset_ite_choose S (k + 1)
      (a (k + 1))
  induction List.range (Fintype.card X) with
  | nil =>
      simp
  | cons k ks ih =>
      simp only [List.flatMap_cons, List.map_append, List.prod_append,
        List.map_cons, List.prod_cons, hlayer, ih]

/-- **Hall, Lemma 6.1.** Every finite formal group word collects into
exact-support blocks, ordered first by support cardinality. -/
theorem collect_formal_support
    {X : Type v} [Fintype X] [DecidableEq X]
    (f : X → G) (l : List (FormalCommutator X)) :
    ∃ blocks : List (List (FormalCommutator X)),
      List.Forall₂
          (fun S q => ∀ c ∈ q, formalSupport c = S)
          (cardinalityNonemptySupports X) blocks ∧
        evalFormalWord f l = evalFormalWord f blocks.flatten :=
  collect_formal_exact f (cardinalityNonemptySupports X)
    (fun S hS => (cardinality_nonempty_supports S).mpr hS)
    (cardinality_supports_pairwise X) l

/-! ## Collection by projected support -/

/-- Test whether an abstract support key lies inside `S`. -/
def formalKeySelector
    {X : Type v} {L : Type w} [DecidableEq L]
    (key : FormalCommutator X → Finset L)
    (S : Finset L) (c : FormalCommutator X) : Bool :=
  decide (key c ⊆ S)

@[simp]
lemma formal_selector_true
    {X : Type v} {L : Type w} [DecidableEq L]
    (key : FormalCommutator X → Finset L)
    (S : Finset L) (c : FormalCommutator X) :
    formalKeySelector key S c = true ↔ key c ⊆ S := by
  simp [formalKeySelector]

/-- An abstract support key remains outside `S` after bracketing when
brackets take unions and the left input already lies outside `S`. -/
lemma formal_selector_selected
    {X : Type v} {L : Type w} [DecidableEq L]
    (key : FormalCommutator X → Finset L)
    (hkey : ∀ u v, key (formalBracket u v) = key u ∪ key v)
    (S : Finset L) (u v : FormalCommutator X)
    (hu : ¬ formalKeySelector key S u = true) :
    ¬ formalKeySelector key S (formalBracket u v) = true := by
  simp only [formal_selector_true] at hu ⊢
  intro huv
  apply hu
  rw [hkey] at huv
  intro x hx
  exact huv (Finset.mem_union_left _ hx)

/-- Collect the factors whose abstract support keys lie inside `S`. -/
def splitKeySubset
    {X : Type v} {L : Type w} [DecidableEq L]
    (key : FormalCommutator X → Finset L)
    (S : Finset L) (l : List (FormalCommutator X)) :
    List (FormalCommutator X) × List (FormalCommutator X) :=
  splitCollectFormal (formalKeySelector key S) l

/-- One abstract-support collection pass produces a leading inside block,
an outside residual word, and an unchanged evaluated product. -/
lemma split_key_spec
    {X : Type v} {L : Type w} [DecidableEq L]
    (f : X → G) (key : FormalCommutator X → Finset L)
    (hkey : ∀ u v, key (formalBracket u v) = key u ∪ key v)
    (S : Finset L) (l : List (FormalCommutator X)) :
    let qr := splitKeySubset key S l
    (∀ c ∈ qr.1, key c ⊆ S) ∧
      (∀ c ∈ qr.2, ¬ key c ⊆ S) ∧
        evalFormalWord f qr.1 * evalFormalWord f qr.2 =
          evalFormalWord f l := by
  let selected := formalKeySelector key S
  have hclosed :
      ∀ u v, ¬ selected u = true → selected v = true →
        ¬ selected (formalBracket u v) = true := by
    intro u v hu _
    exact formal_selector_selected
      key hkey S u v hu
  have hspec := split_collect_spec selected hclosed l
  have heval := formal_split_factors
    f selected l
  change
    let qr := splitCollectFormal selected l
    (∀ c ∈ qr.1, key c ⊆ S) ∧
      (∀ c ∈ qr.2, ¬ key c ⊆ S) ∧
        evalFormalWord f qr.1 * evalFormalWord f qr.2 =
          evalFormalWord f l
  generalize hqr : splitCollectFormal selected l = qr at hspec heval ⊢
  rcases qr with ⟨q, r⟩
  simp only at hspec heval ⊢
  refine ⟨?_, ?_, heval⟩
  · intro c hc
    exact (formal_selector_true key S c).mp (hspec.1 c hc)
  · have hnone := List.countP_eq_zero.mp hspec.2
    intro c hc
    exact fun hsupport =>
      (hnone c hc)
        ((formal_selector_true key S c).mpr hsupport)

/-- Collect abstract-support blocks successively in the supplied order. -/
def splitKeySubsets
    {X : Type v} {L : Type w} [DecidableEq L]
    (key : FormalCommutator X → Finset L) :
    List (Finset L) → List (FormalCommutator X) →
      List (List (FormalCommutator X)) × List (FormalCommutator X)
  | [], l => ([], l)
  | S :: supports, l =>
      let qr := splitKeySubset key S l
      let br := splitKeySubsets key supports qr.2
      (qr.1 :: br.1, br.2)

/-- Successive abstract-support collection preserves every property stable
under bracketing on the right. -/
lemma key_subsets_forall
    {X : Type v} {L : Type w} [DecidableEq L]
    (key : FormalCommutator X → Finset L)
    (P : FormalCommutator X → Prop)
    (hbracket : ∀ u v, P u → P (formalBracket u v)) :
    ∀ supports : List (Finset L), ∀ l : List (FormalCommutator X),
      (∀ c ∈ l, P c) →
      let qr := splitKeySubsets key supports l
      (∀ q ∈ qr.1, ∀ c ∈ q, P c) ∧ ∀ c ∈ qr.2, P c := by
  intro supports
  induction supports with
  | nil =>
      intro l hl
      exact ⟨(fun _ h => nomatch h), hl⟩
  | cons S supports ih =>
      intro l hl
      simp only [splitKeySubsets]
      let qr := splitKeySubset key S l
      obtain ⟨hq, hr⟩ :=
        split_formal_forall
          (formalKeySelector key S) P hbracket l hl
      let br := splitKeySubsets key supports qr.2
      obtain ⟨hblocks, hresidual⟩ := ih qr.2 hr
      exact ⟨by
        intro q hqmem
        simp only [List.mem_cons] at hqmem
        rcases hqmem with rfl | hqmem
        · exact hq
        · exact hblocks q hqmem, hresidual⟩

/-- Ordered abstract-support collection consumes the entire word when the
key is nonempty and the requested supports form a complete cardinality
ordering. -/
lemma key_subsets_exact
    {X : Type v} {L : Type w} [DecidableEq L]
    (f : X → G) (key : FormalCommutator X → Finset L)
    (hkey : ∀ u v, key (formalBracket u v) = key u ∪ key v)
    (hkey_nonempty : ∀ c, (key c).Nonempty)
    (supports : List (Finset L))
    (hcomplete : ∀ S : Finset L, S.Nonempty → S ∈ supports)
    (hsorted : supports.Pairwise fun S T => S.card ≤ T.card)
    (l : List (FormalCommutator X)) :
    let qr := splitKeySubsets key supports l
    List.Forall₂ (fun S q => ∀ c ∈ q, key c = S) supports qr.1 ∧
      qr.2 = [] ∧ evalFormalWord f qr.1.flatten =
        evalFormalWord f l := by
  have haux :
      ∀ (prior supports : List (Finset L))
          (l : List (FormalCommutator X)),
        (∀ c ∈ l, ∀ S ∈ prior, ¬ key c ⊆ S) →
        (∀ S : Finset L, S.Nonempty → S ∈ prior ++ supports) →
        supports.Pairwise (fun S T => S.card ≤ T.card) →
        let qr := splitKeySubsets key supports l
        List.Forall₂ (fun S q => ∀ c ∈ q, key c = S) supports qr.1 ∧
          qr.2 = [] ∧ evalFormalWord f qr.1.flatten =
            evalFormalWord f l := by
    intro prior supports
    induction supports generalizing prior with
    | nil =>
        intro l houtside hcomplete _
        have hl : l = [] := by
          apply List.eq_nil_iff_forall_not_mem.mpr
          intro c hc
          have hmem := hcomplete (key c) (hkey_nonempty c)
          simp only [List.append_nil] at hmem
          exact (houtside c hc (key c) hmem) (by rfl)
        subst l
        simp [splitKeySubsets]
    | cons S supports ih =>
        intro l houtside hcomplete hsorted
        rw [List.pairwise_cons] at hsorted
        generalize hqr : splitKeySubset key S l = qr
        rcases qr with ⟨q, r⟩
        have hsingle :=
          split_key_spec f key hkey S l
        rw [hqr] at hsingle
        let P : FormalCommutator X → Prop :=
          fun c => ∀ T ∈ prior, ¬ key c ⊆ T
        have hPstable :
            ∀ u v : FormalCommutator X, P u → P (formalBracket u v) := by
          intro u v hu T hT huv
          apply hu T hT
          rw [hkey] at huv
          intro x hx
          exact huv (Finset.mem_union_left _ hx)
        have hpass :=
          split_formal_forall
            (formalKeySelector key S) P hPstable l houtside
        change
          let qr := splitKeySubset key S l
          (∀ c ∈ qr.1, P c) ∧ ∀ c ∈ qr.2, P c at hpass
        rw [hqr] at hpass
        have hqexact : ∀ c ∈ q, key c = S := by
          intro c hc
          have hcS : key c ⊆ S := hsingle.1 c hc
          by_contra hne
          have hproper : key c ⊂ S :=
            Finset.ssubset_iff_subset_ne.mpr ⟨hcS, hne⟩
          have hmem := hcomplete (key c) (hkey_nonempty c)
          simp only [List.mem_append, List.mem_cons] at hmem
          rcases hmem with hprior | hcur | htail
          · exact (hpass.1 c hc (key c) hprior) (by rfl)
          · exact hne hcur
          · exact (Nat.not_lt_of_ge (hsorted.1 _ htail))
              (Finset.card_lt_card hproper)
        have houtside' :
            ∀ c ∈ r, ∀ T ∈ prior ++ [S], ¬ key c ⊆ T := by
          intro c hc T hT
          simp only [List.mem_append, List.mem_singleton] at hT
          rcases hT with hprior | rfl
          · exact hpass.2 c hc T hprior
          · exact hsingle.2.1 c hc
        have hcomplete' :
            ∀ T : Finset L, T.Nonempty → T ∈ (prior ++ [S]) ++ supports := by
          intro T hT
          simpa only [List.append_assoc, List.singleton_append] using
            hcomplete T hT
        have hrec := ih (prior ++ [S]) r houtside' hcomplete' hsorted.2
        generalize hbr :
          splitKeySubsets key supports r = br
        rcases br with ⟨blocks, residual⟩
        rw [hbr] at hrec
        simp only [splitKeySubsets, hqr, hbr]
        refine ⟨List.Forall₂.cons hqexact hrec.1, hrec.2.1, ?_⟩
        simp only [List.flatten_cons, eval_formal_append]
        rw [hrec.2.2, hsingle.2.2]
  exact haux [] supports l (by simp) (by simpa using hcomplete) hsorted

/-- **Hall, Lemma 6.1, projected-support form.** Formal factors collect
into blocks indexed by the projected labels of their components. -/
theorem collect_projected_support
    {X : Type v} {L : Type w} [Fintype L] [DecidableEq L]
    (f : X → G) (label : X → L) (l : List (FormalCommutator X)) :
    ∃ blocks : List (List (FormalCommutator X)),
      List.Forall₂
          (fun S q => ∀ c ∈ q, projectedFormalSupport label c = S)
          (cardinalityNonemptySupports L) blocks ∧
        evalFormalWord f l = evalFormalWord f blocks.flatten := by
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
  exact ⟨qr.1, h.1, h.2.2.symm⟩

/-- Filtering flattened exact-support blocks by `key c ⊆ U` is the same
as multiplying precisely the block values whose support lies in `U`. -/
lemma filter_flatten_zip
    {X : Type v} {L : Type w} [DecidableEq L]
    (f : X → G) (key : FormalCommutator X → Finset L)
    (U : Finset L) {supports : List (Finset L)}
    {blocks : List (List (FormalCommutator X))}
    (hblocks :
      List.Forall₂ (fun S q => ∀ c ∈ q, key c = S) supports blocks) :
    evalFormalWord f
        (blocks.flatten.filter fun c => key c ⊆ U) =
      ((supports.zip blocks).map fun Sq =>
        if Sq.1 ⊆ U then evalFormalWord f Sq.2 else 1).prod := by
  induction supports generalizing blocks with
  | nil =>
      have hnil : blocks = [] := List.forall₂_nil_left_iff.mp hblocks
      subst blocks
      simp
  | cons S supports ih =>
      cases blocks with
      | nil =>
          simp at hblocks
      | cons q blocks =>
          rw [List.forall₂_cons] at hblocks
          obtain ⟨hq, hblocks⟩ := hblocks
          have hfilter :
              q.filter (fun c => key c ⊆ U) =
                if S ⊆ U then q else [] := by
            by_cases hSU : S ⊆ U
            · simp only [if_pos hSU]
              apply List.filter_eq_self.mpr
              intro c hc
              simp only [decide_eq_true_eq]
              rw [hq c hc]
              exact hSU
            · simp only [if_neg hSU]
              apply List.filter_eq_nil_iff.mpr
              intro c hc
              simp only [decide_eq_true_eq]
              rw [hq c hc]
              exact hSU
          simp only [List.flatten_cons, List.filter_append,
            eval_formal_append, List.zip_cons_cons, List.map_cons,
            List.prod_cons, hfilter, ih hblocks]
          by_cases hSU : S ⊆ U <;> simp [hSU]

/-- If an exact support does not occur among the block labels, filtering
the flattened factors for that support yields the empty list. -/
lemma filter_flatten_forall₂_of_not_mem
    {X : Type v} {L : Type w} [DecidableEq L]
    (key : FormalCommutator X → Finset L) (S : Finset L)
    {supports : List (Finset L)}
    {blocks : List (List (FormalCommutator X))}
    (hblocks :
      List.Forall₂ (fun T q => ∀ c ∈ q, key c = T) supports blocks)
    (hS : S ∉ supports) :
    blocks.flatten.filter (fun c => key c = S) = [] := by
  induction supports generalizing blocks with
  | nil =>
      have hnil : blocks = [] := List.forall₂_nil_left_iff.mp hblocks
      subst blocks
      simp
  | cons T supports ih =>
      cases blocks with
      | nil =>
          simp at hblocks
      | cons q blocks =>
          rw [List.forall₂_cons] at hblocks
          obtain ⟨hq, hblocks⟩ := hblocks
          have hST : S ≠ T := by
            intro h
            apply hS
            simp [h]
          have hfilter : q.filter (fun c => key c = S) = [] := by
            apply List.filter_eq_nil_iff.mpr
            intro c hc
            simp only [decide_eq_true_eq]
            rw [hq c hc]
            exact hST.symm
          simp only [List.mem_cons, not_or] at hS
          simp [List.flatten_cons, List.filter_append, hfilter,
            ih hblocks hS.2]

/-- In duplicate-free exact-support blocks, filtering the flattened word
for a support recovers the unique paired block. -/
lemma flatten_zip_forall₂_nodup
    {X : Type v} {L : Type w} [DecidableEq L]
    (key : FormalCommutator X → Finset L)
    {supports : List (Finset L)}
    {blocks : List (List (FormalCommutator X))}
    (hblocks :
      List.Forall₂ (fun T q => ∀ c ∈ q, key c = T) supports blocks)
    (hnodup : supports.Nodup)
    {S : Finset L} {q : List (FormalCommutator X)}
    (hSq : (S, q) ∈ supports.zip blocks) :
    blocks.flatten.filter (fun c => key c = S) = q := by
  induction supports generalizing blocks S q with
  | nil =>
      simp at hSq
  | cons T supports ih =>
      cases blocks with
      | nil =>
          simp at hblocks
      | cons r blocks =>
          rw [List.forall₂_cons] at hblocks
          obtain ⟨hr, hblocks⟩ := hblocks
          rw [List.nodup_cons] at hnodup
          simp only [List.zip_cons_cons, List.mem_cons, Prod.mk.injEq] at hSq
          rcases hSq with ⟨rfl, rfl⟩ | hSq
          · have hfilterHead :
                q.filter (fun c => key c = S) = q := by
              apply List.filter_eq_self.mpr
              intro c hc
              simp only [decide_eq_true_eq]
              exact hr c hc
            have hfilterTail :
                blocks.flatten.filter (fun c => key c = S) = [] :=
              filter_flatten_forall₂_of_not_mem
                key S hblocks hnodup.1
            rw [List.flatten_cons, List.filter_append, hfilterHead,
              hfilterTail, List.append_nil]
          · have hS_mem : S ∈ supports := by
              exact (List.of_mem_zip hSq).1
            have hST : T ≠ S := by
              intro h
              exact hnodup.1 (h ▸ hS_mem)
            have hfilterHead :
                r.filter (fun c => key c = S) = [] := by
              apply List.filter_eq_nil_iff.mpr
              intro c hc
              simp only [decide_eq_true_eq]
              rw [hr c hc]
              exact hST
            rw [List.flatten_cons, List.filter_append, hfilterHead,
              ih hblocks hnodup.2 hSq, List.nil_append]

/-- Hall's expanded product `x₁^(1) ⋯ x₁^(w) x₂^(1) ⋯ xₙ^(w)` as a
formal word. A leaf remembers its group element and its copy-slot. -/
def petrescoExpandedFormal (x : List G) (w : ℕ) :
    List (FormalCommutator (G × Fin w)) :=
  x.flatMap fun g =>
    (List.finRange w).map fun j => FreeMagma.of (g, j)

/-- Evaluating Hall's expanded formal word gives `x₁^w ⋯ xₙ^w`. -/
lemma formal_petresco_expanded
    (x : List G) (w : ℕ) :
    evalFormalWord (fun gj : G × Fin w => gj.1)
        (petrescoExpandedFormal x w) =
      (x.map fun g => g ^ w).prod := by
  induction x with
  | nil =>
      simp [petrescoExpandedFormal, evalFormalWord]
  | cons g x ih =>
      change
        evalFormalWord (fun gj : G × Fin w => gj.1)
            ((List.finRange w).map (fun j => FreeMagma.of (g, j)) ++
              petrescoExpandedFormal x w) =
          g ^ w * (x.map fun h => h ^ w).prod
      rw [eval_formal_append, ih]
      congr 1
      simp [evalFormalWord, Function.comp_def]

/-- Hall's expanded power product collects into blocks indexed by subsets
of copy-slots. -/
theorem petresco_expanded_formal
    (x : List G) (w : ℕ) :
    ∃ blocks : List (List (FormalCommutator (G × Fin w))),
      List.Forall₂
          (fun S q => ∀ c ∈ q,
            projectedFormalSupport (fun gj : G × Fin w => gj.2) c = S)
          (cardinalityNonemptySupports (Fin w)) blocks ∧
        (x.map fun g => g ^ w).prod =
          evalFormalWord (fun gj : G × Fin w => gj.1) blocks.flatten := by
  obtain ⟨blocks, hblocks, heval⟩ :=
    collect_projected_support (G := G)
      (fun gj : G × Fin w => gj.1) (fun gj => gj.2)
      (petrescoExpandedFormal x w)
  refine ⟨blocks, hblocks, ?_⟩
  rw [← formal_petresco_expanded x w]
  exact heval

/-- Every commutator in a projected-support block has at least as many
components as the block has copy-slots. -/
lemma formal_projected_support
    {X : Type v} {L : Type w} [DecidableEq L]
    (label : X → L) (c : FormalCommutator X) (S : Finset L)
    (hc : projectedFormalSupport label c = S) :
    S.card ≤ formalWeight c := by
  rw [← hc]
  exact projected_formal_support label c

/-- A subset of `Fin w` occupies exactly its cardinality many positions in
`List.finRange w`. -/
lemma count_range_card {w : ℕ} (S : Finset (Fin w)) :
    List.countP (fun j => decide (j ∈ S)) (List.finRange w) = S.card := by
  rw [List.countP_eq_length_filter,
    ← List.toFinset_card_of_nodup ((List.nodup_finRange w).filter _)]
  congr 1
  ext j
  simp

/-- Retaining only the copy-slots in `S` turns Hall's expanded word into
`x₁^|S| ⋯ xₙ^|S|`. -/
lemma petresco_retain_slots
    (x : List G) (w : ℕ) (S : Finset (Fin w)) :
    evalFormalWord
        (retainProjectedVariables (fun gj : G × Fin w => gj.2) S
          (fun gj => gj.1))
        (petrescoExpandedFormal x w) =
      (x.map fun g => g ^ S.card).prod := by
  induction x with
  | nil =>
      simp [petrescoExpandedFormal, evalFormalWord]
  | cons g x ih =>
      change
        evalFormalWord
            (retainProjectedVariables (fun gj : G × Fin w => gj.2) S
              (fun gj => gj.1))
            ((List.finRange w).map (fun j => FreeMagma.of (g, j)) ++
              petrescoExpandedFormal x w) =
          g ^ S.card * (x.map fun h => h ^ S.card).prod
      rw [eval_formal_append, ih]
      congr 1
      unfold evalFormalWord
      rw [List.map_map]
      have hmap :
          (List.finRange w).map
              (formalGroupCommutator
                (retainProjectedVariables (fun gj : G × Fin w => gj.2) S
                  (fun gj => gj.1)) ∘
                    fun j => FreeMagma.of (g, j)) =
            (List.finRange w).map fun j =>
              if j ∈ S then g else 1 := by
        apply List.map_congr_left
        intro j _
        simp [retainProjectedVariables]
      rw [hmap]
      have hite :
          (List.finRange w).map (fun j => if j ∈ S then g else 1) =
            (List.finRange w).map
              (fun j => if decide (j ∈ S) then g else 1) := by
        apply List.map_congr_left
        intro j _
        by_cases hj : j ∈ S <;> simp [hj]
      rw [hite]
      rw [prod_ite_p (fun j => decide (j ∈ S)),
        count_range_card]

/-- The canonical projected-support blocks obtained by collecting Hall's
expanded Petresco word. -/
noncomputable def petrescoCollectedBlocks (x : List G) (w : ℕ) :
    List (List (FormalCommutator (G × Fin w))) :=
  (splitKeySubsets
      (projectedFormalSupport fun gj : G × Fin w => gj.2)
      (levelNonemptySupports (Fin w))
      (petrescoExpandedFormal x w)).1

omit [Group G] in
/-- The canonical Petresco blocks have exact projected supports and their
ordered product evaluates to the expanded word under every evaluator. -/
lemma petresco_blocks_spec
    {H : Type*} [Group H] (x : List G) (w : ℕ)
    (f : G × Fin w → H) :
    List.Forall₂
        (fun S q => ∀ c ∈ q,
          projectedFormalSupport (fun gj : G × Fin w => gj.2) c = S)
        (levelNonemptySupports (Fin w))
        (petrescoCollectedBlocks x w) ∧
      evalFormalWord f (petrescoCollectedBlocks x w).flatten =
        evalFormalWord f (petrescoExpandedFormal x w) := by
  let qr :=
    splitKeySubsets
      (projectedFormalSupport fun gj : G × Fin w => gj.2)
      (levelNonemptySupports (Fin w))
      (petrescoExpandedFormal x w)
  have h :=
    key_subsets_exact (G := H) f
      (projectedFormalSupport fun gj : G × Fin w => gj.2)
      (projected_formal_bracket fun gj : G × Fin w => gj.2)
      (projected_formal_nonempty fun gj : G × Fin w => gj.2)
      (levelNonemptySupports (Fin w))
      (fun S hS => level_nonempty_supports S hS)
      (level_supports_pairwise (Fin w))
      (petrescoExpandedFormal x w)
  exact ⟨h.1, h.2.2⟩

/-- Hall's triangular support equation: retaining copy-slots in `S`
evaluates the expanded word as the product of the collected factors whose
projected supports lie inside `S`. -/
lemma blocks_retain_slots
    (x : List G) (w : ℕ) (S : Finset (Fin w)) :
    (x.map fun g => g ^ S.card).prod =
      evalFormalWord (fun gj : G × Fin w => gj.1)
        ((petrescoCollectedBlocks x w).flatten.filter fun c =>
          projectedFormalSupport (fun gj : G × Fin w => gj.2) c ⊆ S) := by
  calc
    (x.map fun g => g ^ S.card).prod =
        evalFormalWord
          (retainProjectedVariables (fun gj : G × Fin w => gj.2) S
            (fun gj => gj.1))
          (petrescoExpandedFormal x w) :=
      (petresco_retain_slots
        x w S).symm
    _ = evalFormalWord
          (retainProjectedVariables (fun gj : G × Fin w => gj.2) S
            (fun gj => gj.1))
          (petrescoCollectedBlocks x w).flatten :=
      (petresco_blocks_spec x w
        (retainProjectedVariables (fun gj : G × Fin w => gj.2) S
          (fun gj => gj.1))).2.symm
    _ = evalFormalWord (fun gj : G × Fin w => gj.1)
          ((petrescoCollectedBlocks x w).flatten.filter fun c =>
            projectedFormalSupport (fun gj : G × Fin w => gj.2) c ⊆ S) :=
      formal_projected_variables
        (fun gj : G × Fin w => gj.2) S (fun gj => gj.1)
          (petrescoCollectedBlocks x w).flatten

/-- Triangular support equation in block form: the retained expanded word
is the ordered product of the values of blocks supported inside `S`. -/
lemma blocks_retain_zip
    (x : List G) (w : ℕ) (S : Finset (Fin w)) :
    (x.map fun g => g ^ S.card).prod =
      (((levelNonemptySupports (Fin w)).zip
          (petrescoCollectedBlocks x w)).map fun Sq =>
        if Sq.1 ⊆ S
        then evalFormalWord (fun gj : G × Fin w => gj.1) Sq.2
        else 1).prod := by
  rw [blocks_retain_slots]
  exact filter_flatten_zip
    (fun gj : G × Fin w => gj.1)
    (projectedFormalSupport fun gj : G × Fin w => gj.2) S
    (petresco_blocks_spec x w (fun gj => gj.1)).1

/-- The collected factors having exactly projected support `S`. -/
noncomputable def petrescoCollectedSupport
    (x : List G) (w : ℕ) (S : Finset (Fin w)) :
    List (FormalCommutator (G × Fin w)) :=
  (petrescoCollectedBlocks x w).flatten.filter fun c =>
    projectedFormalSupport (fun gj : G × Fin w => gj.2) c = S

/-- The value of the collected block with exact projected support `S`. -/
noncomputable def petrescoCollectedValue
    (x : List G) (w : ℕ) (S : Finset (Fin w)) : G :=
  evalFormalWord (fun gj : G × Fin w => gj.1)
    (petrescoCollectedSupport x w S)

/-- A block paired with `S` in the collected list evaluates to the
canonical exact-support value `q_S`. -/
lemma formal_petresco_zip
    (x : List G) (w : ℕ) {S : Finset (Fin w)}
    {q : List (FormalCommutator (G × Fin w))}
    (hSq :
      (S, q) ∈
        (levelNonemptySupports (Fin w)).zip
          (petrescoCollectedBlocks x w)) :
    evalFormalWord (fun gj : G × Fin w => gj.1) q =
      petrescoCollectedValue x w S := by
  unfold petrescoCollectedValue petrescoCollectedSupport
  rw [flatten_zip_forall₂_nodup
    (projectedFormalSupport fun gj : G × Fin w => gj.2)
    (petresco_blocks_spec x w (fun gj => gj.1)).1
    (level_supports_nodup (Fin w)) hSq]

/-- The triangular support equation expressed solely in terms of the
canonical exact-support values `q_T`. -/
lemma blocks_retain_values
    (x : List G) (w : ℕ) (S : Finset (Fin w)) :
    (x.map fun g => g ^ S.card).prod =
      ((levelNonemptySupports (Fin w)).map fun T =>
        if T ⊆ S then petrescoCollectedValue x w T else 1).prod := by
  rw [blocks_retain_zip]
  let supports := levelNonemptySupports (Fin w)
  let blocks := petrescoCollectedBlocks x w
  let value : Finset (Fin w) → G := petrescoCollectedValue x w
  have hblocks :=
    (petresco_blocks_spec x w (fun gj => gj.1)).1
  have hlength : supports.length ≤ blocks.length := by
    exact le_of_eq hblocks.length_eq
  calc
    (((supports.zip blocks).map fun Sq =>
          if Sq.1 ⊆ S
          then evalFormalWord (fun gj : G × Fin w => gj.1) Sq.2
          else 1).prod) =
        (((supports.zip blocks).map fun Sq =>
          if Sq.1 ⊆ S then value Sq.1 else 1).prod) := by
      congr 1
      apply List.map_congr_left
      intro Sq hSq
      by_cases hsub : Sq.1 ⊆ S
      · simp only [hsub, ↓reduceIte]
        exact formal_petresco_zip
          x w hSq
      · simp [hsub]
    _ = ((supports.map fun T =>
          if T ⊆ S then value T else 1).prod) := by
      apply congrArg List.prod
      calc
        (supports.zip blocks).map (fun Sq =>
            if Sq.1 ⊆ S then value Sq.1 else 1) =
          ((supports.zip blocks).map Prod.fst).map (fun T =>
            if T ⊆ S then value T else 1) := by
              rw [List.map_map]
              simp [Function.comp_def]
        _ = supports.map (fun T =>
            if T ⊆ S then value T else 1) := by
              rw [List.map_fst_zip hlength]

/-- Hall's triangular recurrence identifies every nonempty exact-support
block value with the Petresco term indexed by its support cardinality. -/
theorem petresco_collected_term
    (x : List G) (w : ℕ) (S : Finset (Fin w)) (hS : S.Nonempty) :
    petrescoCollectedValue x w S = petrescoTerm x S.card := by
  have haux :
      ∀ n : ℕ, ∀ T : Finset (Fin w), T.card = n → T.Nonempty →
        petrescoCollectedValue x w T = petrescoTerm x T.card := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro T hcard hT
        have hnpos : 0 < n := by
          rw [← hcard]
          exact Finset.card_pos.mpr hT
        obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hnpos)
        change T.card = m + 1 at hcard
        let value : Finset (Fin w) → G := petrescoCollectedValue x w
        let a : ℕ → G := fun k =>
          if k < m + 1 then petrescoTerm x k
          else if k = m + 1 then value T else 1
        have hmap :
            ((levelNonemptySupports (Fin w)).map fun U =>
                if U ⊆ T then value U else 1) =
              ((levelNonemptySupports (Fin w)).map fun U =>
                if U ⊆ T then a U.card else 1) := by
          apply List.map_congr_left
          intro U hU
          by_cases hUT : U ⊆ T
          · simp only [hUT, ↓reduceIte]
            have hcardle : U.card ≤ m + 1 := by
              rw [← hcard]
              exact Finset.card_le_card hUT
            by_cases hlt : U.card < m + 1
            · have hUnonempty :
                  U.Nonempty :=
                nonempty_level_supports hU
              change petrescoCollectedValue x w U = a U.card
              rw [ih U.card hlt U rfl hUnonempty]
              exact (if_pos hlt).symm
            · have hcardeq : U.card = m + 1 := by omega
              have hUTeq : U = T := by
                apply Finset.eq_of_subset_of_card_le hUT
                rw [hcard, hcardeq]
              subst U
              simp [a, hcard]
          · simp [hUT]
        have hnle : m + 1 ≤ w := by
          rw [← hcard]
          simpa using (Finset.card_le_univ T)
        have hproduct :
            ((levelNonemptySupports (Fin w)).map fun U =>
                if U ⊆ T then value U else 1).prod =
              petrescoBinomialProduct a (m + 1) := by
          rw [hmap, nonempty_supports_ite]
          simpa [hcard] using
            (choose_petresco_binomial a hnle)
        have hprior :
            petrescoPriorProduct a (m + 1) =
              petrescoPriorProduct (petrescoTerm x) (m + 1) := by
          unfold petrescoPriorProduct
          congr 1
          apply List.map_congr_left
          intro j _
          simp [a]
        have hbinomial :
            petrescoBinomialProduct a (m + 1) =
              petrescoPriorProduct (petrescoTerm x) (m + 1) * value T := by
          rw [petresco_binomial_succ, hprior]
          simp [a]
        have htriangular :
            (x.map fun g => g ^ (m + 1)).prod =
              ((levelNonemptySupports (Fin w)).map fun U =>
                if U ⊆ T then value U else 1).prod := by
          simpa [value, hcard] using
            (blocks_retain_values x w T)
        have hp :
            (x.map fun g => g ^ (m + 1)).prod =
              petrescoPriorProduct (petrescoTerm x) (m + 1) * value T :=
          htriangular.trans (hproduct.trans hbinomial)
        change value T = petrescoTerm x T.card
        rw [hcard, petrescoTerm_succ, hp]
        simp
  exact haux S.card S rfl hS

omit [Group G] in
/-- Every exact-`S` Petresco factor has at least `|S|` components. -/
lemma petresco_collected_support
    (x : List G) (w : ℕ) (S : Finset (Fin w)) :
    ∀ c ∈ petrescoCollectedSupport x w S,
      S.card ≤ formalWeight c := by
  intro c hc
  simp only [petrescoCollectedSupport, List.mem_filter] at hc
  exact formal_projected_support
    (fun gj : G × Fin w => gj.2) c S (of_decide_eq_true hc.2)

/-- A formal group commutator of weight `r` lies in the `r`th
one-based lower-central term, represented in Mathlib by index `r - 1`. -/
lemma eval_formal_series
    {X : Type v} (f : X → G) (c : FormalCommutator X) :
    formalGroupCommutator f c ∈
      Subgroup.lowerCentralSeries G (formalWeight c - 1) := by
  induction c with
  | of x =>
      simp
  | mul a b iha ihb =>
      have ha : 0 < formalWeight a := by
        exact FreeMagma.length_pos a
      have hb : 0 < formalWeight b := by
        exact FreeMagma.length_pos b
      have hcomm :
          formalGroupCommutator f (formalBracket a b) ∈
            Subgroup.lowerCentralSeries G
              ((formalWeight a - 1) + (formalWeight b - 1) + 1) := by
        exact lower_central_commutator (G := G) (formalWeight a - 1)
          (formalWeight b - 1)
          (hall_commutator iha ihb)
      change
        hallCommutator (formalGroupCommutator f a)
            (formalGroupCommutator f b) ∈
          Subgroup.lowerCentralSeries G (formalWeight a + formalWeight b - 1)
      have haeq : formalWeight a - 1 + 1 = formalWeight a :=
        Nat.sub_add_cancel ha
      have hbeq : formalWeight b - 1 + 1 = formalWeight b :=
        Nat.sub_add_cancel hb
      have hindex :
          (formalWeight a - 1) + (formalWeight b - 1) + 1 =
            formalWeight a + formalWeight b - 1 := by
        omega
      rw [← hindex]
      exact hcomm

/-- A formal commutator with at least `w` components lies in Hall's
one-based lower-central term `γ_w`. -/
lemma formal_series_weight
    {X : Type v} (f : X → G) (c : FormalCommutator X) {w : ℕ}
    (hc : w ≤ formalWeight c) :
    formalGroupCommutator f c ∈ Subgroup.lowerCentralSeries G (w - 1) :=
  Subgroup.lowerCentralSeries_antitone (Nat.sub_le_sub_right hc 1)
    (eval_formal_series f c)

/-- An ordered product of commutators having at least `w` components
lies in `γ_w`. -/
lemma product_formal_series
    {X : Type v} (f : X → G) (l : List (FormalCommutator X)) (w : ℕ)
    (hl : ∀ c ∈ l, w ≤ formalWeight c) :
    (l.map (formalGroupCommutator f)).prod ∈
      Subgroup.lowerCentralSeries G (w - 1) := by
  induction l with
  | nil =>
      simp
  | cons c l ih =>
      have hc : w ≤ formalWeight c := hl c (by simp)
      have htail : ∀ d ∈ l, w ≤ formalWeight d := by
        intro d hd
        exact hl d (by simp [hd])
      exact (Subgroup.lowerCentralSeries G (w - 1)).mul_mem
        (formal_series_weight
          f c hc)
        (ih htail)

/-- The value of an exact-`S` Petresco block belongs to `γ_|S|`. -/
lemma petresco_support_series
    (x : List G) (w : ℕ) (S : Finset (Fin w)) :
    evalFormalWord (fun gj : G × Fin w => gj.1)
        (petrescoCollectedSupport x w S) ∈
      Subgroup.lowerCentralSeries G (S.card - 1) := by
  exact product_formal_series
    (fun gj : G × Fin w => gj.1)
    (petrescoCollectedSupport x w S) S.card
    (petresco_collected_support x w S)

/-- **Hall, Theorem 6.3, pointwise form.** Every `w`th Petresco term lies
in Hall's one-based lower-central term `γ_w`. -/
theorem petresco_lower_series (x : List G) (w : ℕ) :
    petrescoTerm x w ∈ Subgroup.lowerCentralSeries G (w - 1) := by
  cases w with
  | zero =>
      simp
  | succ w =>
      let S : Finset (Fin (w + 1)) := Finset.univ
      have hS : S.Nonempty := by
        exact ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
      have hmem :=
        petresco_support_series
          x (w + 1) S
      change
        petrescoCollectedValue x (w + 1) S ∈
          Subgroup.lowerCentralSeries G (S.card - 1) at hmem
      rw [petresco_collected_term x (w + 1) S hS] at hmem
      simpa [S] using hmem

/-- If every value of a word has a formal factorization into commutators
with at least `w` components, its verbal subgroup lies in `γ_w`. -/
theorem verbal_formal_factorization
    {X : Type v} (tau : FreeGroup X) (w : ℕ)
    (hfactor :
      ∀ f : X → G, ∃ l : List (FormalCommutator X),
        (∀ c ∈ l, w ≤ formalWeight c) ∧
          wordEval tau f =
            (l.map (formalGroupCommutator f)).prod) :
    verbalSubgroup tau G ≤ Subgroup.lowerCentralSeries G (w - 1) := by
  rw [verbalSubgroup, Subgroup.closure_le]
  rintro _ ⟨f, rfl⟩
  obtain ⟨l, hl, heval⟩ := hfactor f
  rw [heval]
  exact product_formal_series f l w hl

/-- **Hall, Theorem 6.3.** The verbal subgroup of the `w`th Petresco word
lies in Hall's one-based lower-central term `γ_w`. -/
theorem petresco_verbal_series
    {X : Type v} (x : List X) (w : ℕ) :
    verbalSubgroup (petrescoWord x w) G ≤ Subgroup.lowerCentralSeries G (w - 1) := by
  rw [verbalSubgroup, Subgroup.closure_le]
  rintro _ ⟨f, rfl⟩
  rw [word_eval_petresco]
  exact petresco_lower_series (x.map f) w

/-- Every Petresco term of weight at least two vanishes in a commutative
group. -/
lemma petresco_comm_group
    {A : Type*} [CommGroup A] (x : List A) {w : ℕ} (hw : 2 ≤ w) :
    petrescoTerm x w = 1 := by
  have hcomm : commutator A = ⊥ :=
    (commutator_eq_bot_iff_center_eq_top (G := A)).mpr
      CommGroup.center_eq_top
  apply Subgroup.mem_bot.mp
  rw [← hcomm, ← Subgroup.lowerCentralSeries_one]
  exact Subgroup.lowerCentralSeries_antitone (show 1 ≤ w - 1 by omega)
    (petresco_lower_series x w)

/-- In a finite group, the lower central series eventually has two
consecutive equal terms. -/
lemma lower_central_succ [Finite G] :
    ∃ n : ℕ,
      Subgroup.lowerCentralSeries G n = Subgroup.lowerCentralSeries G (n + 1) := by
  classical
  obtain ⟨a, b, hab, heq⟩ :=
    Finite.exists_ne_map_eq_of_infinite (Subgroup.lowerCentralSeries G)
  rcases lt_or_gt_of_ne hab with hab | hba
  · exact
      ⟨a, lowerCentralSeries.eq_ge_gt hab (Nat.le_succ a) heq⟩
  · exact
      ⟨b, lowerCentralSeries.eq_ge_gt hba (Nat.le_succ b) heq.symm⟩

/-- If a finite group is not nilpotent, its lower central series stabilizes
at a nontrivial term. -/
lemma nontrivial_not_nilpotent
    [Finite G] (hnil : ¬ Group.IsNilpotent G) :
    ∃ n : ℕ,
      Subgroup.lowerCentralSeries G n ≠ ⊥ ∧
        Subgroup.lowerCentralSeries G n = Subgroup.lowerCentralSeries G (n + 1) := by
  obtain ⟨n, hn⟩ := lower_central_succ (G := G)
  refine ⟨n, ?_, hn⟩
  intro hbot
  exact hnil (Subgroup.nilpotent_iff_lowerCentralSeries.mpr ⟨n, hbot⟩)

/-- A finite nonnilpotent group has a nontrivial normal subgroup `K`
satisfying `[K, G] = K`. -/
lemma nontrivial_point_nilpotent
    [Finite G] (hnil : ¬ Group.IsNilpotent G) :
    ∃ K : Subgroup G,
      K ≠ ⊥ ∧ K.Normal ∧ ⁅K, (⊤ : Subgroup G)⁆ = K := by
  obtain ⟨n, hnne, hn⟩ :=
    nontrivial_not_nilpotent
      (G := G) hnil
  refine ⟨Subgroup.lowerCentralSeries G n, hnne, inferInstance, ?_⟩
  change Subgroup.lowerCentralSeries G (n + 1) = Subgroup.lowerCentralSeries G n
  exact hn.symm

/-- The stabilized lower-central term of a finite nonnilpotent group
contains a minimal normal subgroup of the ambient group. -/
lemma minimal_point_nilpotent
    [Finite G] (hnil : ¬ Group.IsNilpotent G) :
    ∃ K M : Subgroup G,
      K ≠ ⊥ ∧ K.Normal ∧ ⁅K, (⊤ : Subgroup G)⁆ = K ∧
        IMNormal M ∧ M ≤ K := by
  obtain ⟨K, hKne, hKnormal, hKcomm⟩ :=
    nontrivial_point_nilpotent
      (G := G) hnil
  obtain ⟨M, hMminimal, hMK⟩ :=
    minimal_normal (G := G) hKnormal hKne
  exact ⟨K, M, hKne, hKnormal, hKcomm, hMminimal, hMK⟩

/-- The stabilized lower-central term of a finite nonnilpotent group has
a maximal proper ambient-normal subgroup below it. Its quotient is the
chief factor used in the remaining finite structure argument. -/
lemma proper_point_nilpotent
    [Finite G] (hnil : ¬ Group.IsNilpotent G) :
    ∃ K N : Subgroup G,
      K ≠ ⊥ ∧ K.Normal ∧ ⁅K, (⊤ : Subgroup G)⁆ = K ∧
        MPBelow N K := by
  obtain ⟨K, hKne, hKnormal, hKcomm⟩ :=
    nontrivial_point_nilpotent
      (G := G) hnil
  obtain ⟨N, hNmaximal⟩ :=
    maximal_proper_below (G := G) hKne
  exact ⟨K, N, hKne, hKnormal, hKcomm, hNmaximal⟩

/-- If a finite nonnilpotent group admits one pair on which every
positive-weight word in a family is nontrivial, then vanishing of any
one verbal subgroup in that family forces the group to be nilpotent.
Hall's Theorem 6.4 will supply the separator for the Petresco family. -/
theorem nilpotent_petresco_verbal
    [Finite G] (tau : ℕ → FreeGroup Bool)
    (hseparate :
      ¬ Group.IsNilpotent G →
        ∃ x : Bool → G, ∀ n, 0 < n → wordEval (tau n) x ≠ 1)
    {n : ℕ} (hn : 0 < n) (htau : verbalSubgroup (tau n) G = ⊥) :
    Group.IsNilpotent G := by
  by_contra hnil
  obtain ⟨x, hx⟩ := hseparate hnil
  have hvalue : wordEval (tau n) x ∈ verbalSubgroup (tau n) G :=
    Subgroup.subset_closure ⟨x, rfl⟩
  rw [htau] at hvalue
  exact hx n hn (Subgroup.mem_bot.mp hvalue)

/-- Apply a supplied two-generator separator. This isolates the final
implication used by Hall's Theorem 6.4 without claiming the missing
finite-group construction. -/
theorem exists_petrescoSeparator
    [Finite G] (tau : ℕ → FreeGroup Bool)
    (hseparate :
      ¬ Group.IsNilpotent G →
        ∃ x : Bool → G, ∀ n, 0 < n → wordEval (tau n) x ≠ 1)
    (hnil : ¬ Group.IsNilpotent G) :
    ∃ x : Bool → G, ∀ n, 0 < n → wordEval (tau n) x ≠ 1 :=
  hseparate hnil

/-- Expressions generated by integer constants and binomial coefficients
in the coordinate variables. These are the integer-valued polynomials in
the form Hall uses: finite integer linear combinations of products of
binomial polynomials. Unlike arbitrary rational polynomials, the same
expression can be evaluated in every binomial ring. -/
inductive BPoly (ι : Type*) where
  | const (z : ℤ)
  | add (p q : BPoly ι)
  | mul (p q : BPoly ι)
  | choose (i : ι) (n : ℕ)

namespace BPoly

/-- An ordinary coordinate variable, written as its first binomial
coefficient. -/
def var {ι : Type*} (i : ι) : BPoly ι :=
  .choose i 1

def zero {ι : Type*} : BPoly ι :=
  .const 0

def one {ι : Type*} : BPoly ι :=
  .const 1

def neg {ι : Type*} (p : BPoly ι) : BPoly ι :=
  .mul (.const (-1)) p

def sub {ι : Type*} (p q : BPoly ι) : BPoly ι :=
  .add p (neg q)

instance {ι : Type*} : Zero (BPoly ι) :=
  ⟨zero⟩

instance {ι : Type*} : One (BPoly ι) :=
  ⟨one⟩

instance {ι : Type*} : Add (BPoly ι) :=
  ⟨.add⟩

instance {ι : Type*} : Mul (BPoly ι) :=
  ⟨.mul⟩

instance {ι : Type*} : Neg (BPoly ι) :=
  ⟨neg⟩

instance {ι : Type*} : Sub (BPoly ι) :=
  ⟨sub⟩

/-- Evaluate a binomial polynomial over an arbitrary binomial ring. -/
def eval {ι R : Type*} [CommRing R] [BinomialRing R]
    (x : ι → R) : BPoly ι → R
  | .const z => z
  | .add p q => eval x p + eval x q
  | .mul p q => eval x p * eval x q
  | .choose i n => Ring.choose (x i) n

@[simp]
lemma eval_const {ι R : Type*} [CommRing R] [BinomialRing R]
    (x : ι → R) (z : ℤ) :
    eval x (.const z) = z :=
  rfl

@[simp]
lemma eval_add {ι R : Type*} [CommRing R] [BinomialRing R]
    (x : ι → R) (p q : BPoly ι) :
    eval x (p + q) = eval x p + eval x q := by
  rw [show p + q = .add p q by rfl, eval]

@[simp]
lemma eval_mul {ι R : Type*} [CommRing R] [BinomialRing R]
    (x : ι → R) (p q : BPoly ι) :
    eval x (p * q) = eval x p * eval x q := by
  rw [show p * q = .mul p q by rfl, eval]

@[simp]
lemma eval_choose {ι R : Type*} [CommRing R] [BinomialRing R]
    (x : ι → R) (i : ι) (n : ℕ) :
    eval x (.choose i n) = Ring.choose (x i) n :=
  rfl

@[simp]
lemma eval_var {ι R : Type*} [CommRing R] [BinomialRing R]
    (x : ι → R) (i : ι) :
    eval x (var i) = x i := by
  rw [var, eval_choose, Ring.choose_one_right]

@[simp]
lemma eval_zero {ι R : Type*} [CommRing R] [BinomialRing R]
    (x : ι → R) :
    eval x (0 : BPoly ι) = 0 := by
  rw [show (0 : BPoly ι) = zero by rfl, zero, eval_const]
  norm_num

@[simp]
lemma eval_one {ι R : Type*} [CommRing R] [BinomialRing R]
    (x : ι → R) :
    eval x (1 : BPoly ι) = 1 := by
  rw [show (1 : BPoly ι) = one by rfl, one, eval_const]
  norm_num

@[simp]
lemma eval_neg {ι R : Type*} [CommRing R] [BinomialRing R]
    (x : ι → R) (p : BPoly ι) :
    eval x (-p) = -eval x p := by
  rw [show -p = neg p by rfl, neg, eval, eval_const]
  norm_num

@[simp]
lemma eval_sub {ι R : Type*} [CommRing R] [BinomialRing R]
    (x : ι → R) (p q : BPoly ι) :
    eval x (p - q) = eval x p - eval x q := by
  rw [show p - q = sub p q by rfl, sub, eval, neg, eval, eval_const]
  rw [sub_eq_add_neg]
  simp

/-- Rename the variables of a binomial polynomial. -/
def rename {ι κ : Type*} (f : ι → κ) :
    BPoly ι → BPoly κ
  | .const z => .const z
  | .add p q => .add (rename f p) (rename f q)
  | .mul p q => .mul (rename f p) (rename f q)
  | .choose i n => .choose (f i) n

@[simp]
lemma eval_rename {ι κ R : Type*} [CommRing R] [BinomialRing R]
    (f : ι → κ) (x : κ → R) :
    ∀ p : BPoly ι,
      eval x (rename f p) = eval (fun i => x (f i)) p
  | .const z => rfl
  | .add p q => by
      rw [rename, eval, eval, eval_rename f x p, eval_rename f x q]
  | .mul p q => by
      rw [rename, eval, eval, eval_rename f x p, eval_rename f x q]
  | .choose i n => rfl

/-- Evaluation of a binomial polynomial commutes with maps of binomial
rings. -/
theorem map_eval {ι R S F : Type*} [CommRing R] [CommRing S]
    [BinomialRing R] [BinomialRing S] [FunLike F R S]
    [RingHomClass F R S] (f : F) (x : ι → R) :
    ∀ p : BPoly ι,
      f (eval x p) = eval (fun i => f (x i)) p
  | .const z => by simp [eval]
  | .add p q => by simp [eval, map_eval f x p, map_eval f x q]
  | .mul p q => by simp [eval, map_eval f x p, map_eval f x q]
  | .choose i n => by simp [eval, Ring.map_choose]

/-- The rational multivariate polynomial underlying a binomial atom. -/
noncomputable def chooseMvPolynomial {ι : Type*} (i : ι) (n : ℕ) :
    MvPolynomial ι ℚ :=
  (descPochhammer ℚ n).toMvPolynomial i *
    MvPolynomial.C (n.factorial : ℚ)⁻¹

lemma desc_pochhammer_smeval (q : ℚ) :
    ∀ n : ℕ,
      (descPochhammer ℚ n).smeval q =
        (descPochhammer ℤ n).smeval q
  | 0 => by simp
  | n + 1 => by
      rw [descPochhammer_succ_right, descPochhammer_succ_right,
        Polynomial.smeval_mul, Polynomial.smeval_mul,
        desc_pochhammer_smeval q n]
      simp only [Polynomial.smeval_sub, Polynomial.smeval_X,
        Polynomial.smeval_natCast, npow_one, npow_zero, nsmul_one]

lemma choose_mv_polynomial {ι : Type*} (x : ι → ℚ) (i : ι) (n : ℕ) :
    MvPolynomial.eval x (chooseMvPolynomial i n) =
      Ring.choose (x i) n := by
  rw [chooseMvPolynomial, MvPolynomial.eval_mul,
    MvPolynomial.eval_toMvPolynomial, MvPolynomial.eval_C,
    Ring.choose_eq_smul]
  simp [Polynomial.eval_eq_smeval, smul_eq_mul, mul_comm,
    desc_pochhammer_smeval]

/-- Forget the integral binomial basis and retain its rational monomial
polynomial. -/
noncomputable def toMvPolynomial {ι : Type*} :
    BPoly ι → MvPolynomial ι ℚ
  | .const z => MvPolynomial.C z
  | .add p q => toMvPolynomial p + toMvPolynomial q
  | .mul p q => toMvPolynomial p * toMvPolynomial q
  | .choose i n => chooseMvPolynomial i n

lemma eval_mvPolynomial {ι : Type*} (x : ι → ℚ) :
    ∀ p : BPoly ι,
      MvPolynomial.eval x (toMvPolynomial p) = eval x p
  | .const z => by simp [toMvPolynomial, eval]
  | .add p q => by
      simp [toMvPolynomial, eval, eval_mvPolynomial x p,
        eval_mvPolynomial x q]
  | .mul p q => by
      simp [toMvPolynomial, eval, eval_mvPolynomial x p,
        eval_mvPolynomial x q]
  | .choose i n => choose_mv_polynomial x i n

/-- A common positive denominator for the rational multivariate
polynomial underlying a binomial expression. -/
def denominator {ι : Type*} : BPoly ι → ℕ
  | .const _ => 1
  | .add p q => denominator p * denominator q
  | .mul p q => denominator p * denominator q
  | .choose _ n => n.factorial

lemma denominator_ne_zero {ι : Type*} :
    ∀ p : BPoly ι, denominator p ≠ 0
  | .const _ => by simp [denominator]
  | .add p q =>
      Nat.mul_ne_zero (denominator_ne_zero p) (denominator_ne_zero q)
  | .mul p q =>
      Nat.mul_ne_zero (denominator_ne_zero p) (denominator_ne_zero q)
  | .choose _ n => Nat.factorial_ne_zero n

/-- Clear the rational denominators in the monomial polynomial underlying
a binomial expression. -/
noncomputable def clearDenominator {ι : Type*} :
    BPoly ι → MvPolynomial ι ℤ
  | .const z => MvPolynomial.C z
  | .add p q =>
      MvPolynomial.C (denominator q : ℤ) * clearDenominator p +
        MvPolynomial.C (denominator p : ℤ) * clearDenominator q
  | .mul p q => clearDenominator p * clearDenominator q
  | .choose i n => (descPochhammer ℤ n).toMvPolynomial i

/-- Evaluating an integral univariate polynomial embedded in one
multivariate coordinate is the same as scalar evaluation in that
coordinate. -/
lemma eval₂_toMvPolynomial_intCast {ι R : Type*} [CommRing R]
    (x : ι → R) (i : ι) (p : Polynomial ℤ) :
    MvPolynomial.eval₂ (Int.castRingHom R) x (p.toMvPolynomial i) =
      p.smeval (x i) := by
  rw [← Polynomial.aeval_eq_smeval]
  change
    ((MvPolynomial.eval₂Hom (Int.castRingHom R) x).comp
      (Polynomial.toMvPolynomial i).toRingHom) p =
        (Polynomial.aeval (x i)) p
  congr 1
  ext <;> simp

/-- Clearing denominators in the integral monomial model agrees with
multiplying the rational monomial model by the recorded denominator. -/
lemma map_clearDenominator {ι : Type*} :
    ∀ p : BPoly ι,
      MvPolynomial.map (Int.castRingHom ℚ) (clearDenominator p) =
        MvPolynomial.C (denominator p : ℚ) * toMvPolynomial p
  | .const z => by simp [clearDenominator, denominator, toMvPolynomial]
  | .add p q => by
      simp only [clearDenominator, denominator, toMvPolynomial,
        map_add, map_mul, map_clearDenominator p, map_clearDenominator q,
        Nat.cast_mul, map_natCast]
      ring
  | .mul p q => by
      simp only [clearDenominator, denominator, toMvPolynomial,
        map_mul, map_clearDenominator p,
        map_clearDenominator q, Nat.cast_mul]
      ring
  | .choose i n => by
      simp only [clearDenominator, denominator, toMvPolynomial,
        chooseMvPolynomial]
      apply MvPolynomial.funext
      intro x
      rw [MvPolynomial.eval_map, eval₂_toMvPolynomial_intCast,
        MvPolynomial.eval_mul]
      simp only [MvPolynomial.eval_mul, MvPolynomial.eval_C,
        MvPolynomial.eval_toMvPolynomial]
      rw [Polynomial.eval_eq_smeval]
      change
        (descPochhammer ℤ n).smeval (x i) =
          (n.factorial : ℚ) *
            ((descPochhammer ℚ n).smeval (x i) *
              (n.factorial : ℚ)⁻¹)
      rw [desc_pochhammer_smeval,
        mul_comm ((descPochhammer ℤ n).smeval (x i)),
        ← mul_assoc, mul_inv_cancel₀, one_mul]
      exact_mod_cast Nat.factorial_ne_zero n

/-- Evaluating the cleared integral monomial polynomial agrees with
multiplying evaluation of the binomial expression by the recorded
denominator. -/
lemma eval₂_clearDenominator {ι R : Type*} [CommRing R] [BinomialRing R]
    (x : ι → R) :
    ∀ p : BPoly ι,
      MvPolynomial.eval₂ (Int.castRingHom R) x (clearDenominator p) =
        (denominator p : R) * eval x p
  | .const z => by
      rw [clearDenominator, denominator, eval, MvPolynomial.eval₂_C]
      simp
  | .add p q => by
      simp only [clearDenominator, denominator, eval, MvPolynomial.eval₂_add,
        MvPolynomial.eval₂_mul,
        eval₂_clearDenominator x p, eval₂_clearDenominator x q,
        Nat.cast_mul, map_natCast, MvPolynomial.eval₂_natCast]
      ring
  | .mul p q => by
      simp only [clearDenominator, denominator, eval, MvPolynomial.eval₂_mul,
        eval₂_clearDenominator x p, eval₂_clearDenominator x q, Nat.cast_mul]
      ring
  | .choose i n => by
      simp only [clearDenominator, denominator, eval]
      rw [eval₂_toMvPolynomial_intCast]
      change (descPochhammer ℤ n).smeval (x i) =
        (n.factorial : R) * Ring.choose (x i) n
      rw [← nsmul_eq_mul,
        Ring.descPochhammer_eq_factorial_smul_choose]

/-- A rational polynomial identity between binomial expressions remains
valid after evaluation in every binomial ring. -/
theorem eval_mv_polynomial
    {ι R : Type*} [CommRing R] [BinomialRing R]
    (x : ι → R) {p q : BPoly ι}
    (hpq : toMvPolynomial p = toMvPolynomial q) :
    eval x p = eval x q := by
  letI : IsAddTorsionFree R := BinomialRing.toIsAddTorsionFree
  let d := denominator p * denominator q
  have hd : d ≠ 0 :=
    Nat.mul_ne_zero (denominator_ne_zero p) (denominator_ne_zero q)
  apply nsmul_right_injective hd
  have hclear :
      MvPolynomial.C (denominator q : ℤ) * clearDenominator p =
        MvPolynomial.C (denominator p : ℤ) * clearDenominator q := by
    apply MvPolynomial.map_injective (Int.castRingHom ℚ) Int.cast_injective
    simp only [map_mul, map_clearDenominator, map_natCast]
    rw [hpq]
    ring
  calc
    (denominator p * denominator q) • eval x p =
        (denominator q : R) * ((denominator p : R) * eval x p) := by
          simp only [nsmul_eq_mul, Nat.cast_mul]
          ring
    _ = MvPolynomial.eval₂ (Int.castRingHom R) x
          (MvPolynomial.C (denominator q : ℤ) * clearDenominator p) := by
        rw [MvPolynomial.eval₂_mul, MvPolynomial.eval₂_C,
          eval₂_clearDenominator, map_natCast]
    _ = MvPolynomial.eval₂ (Int.castRingHom R) x
          (MvPolynomial.C (denominator p : ℤ) * clearDenominator q) := by
        rw [hclear]
    _ = (denominator p : R) * ((denominator q : R) * eval x q) := by
        rw [MvPolynomial.eval₂_mul, MvPolynomial.eval₂_C,
          eval₂_clearDenominator, map_natCast]
    _ = (denominator p * denominator q) • eval x q := by
        simp only [nsmul_eq_mul, Nat.cast_mul]
        ring

/-- Binomial expressions that agree on all integer coordinate tuples
have the same underlying rational multivariate polynomial. -/
theorem mv_eval_int
    {ι : Type*} {p q : BPoly ι}
    (hpq : ∀ x : ι → ℤ, eval x p = eval x q) :
    toMvPolynomial p = toMvPolynomial q := by
  apply MvPolynomial.funext_set
    (fun _ ↦ Set.range fun z : ℤ => (z : ℚ))
  · intro _
    exact Set.infinite_range_of_injective Int.cast_injective
  · intro x hx
    choose y hy using fun i ↦ hx i (Set.mem_univ i)
    calc
      MvPolynomial.eval x (toMvPolynomial p) =
          MvPolynomial.eval (fun i => (y i : ℚ)) (toMvPolynomial p) := by
            rw [show x = (fun i => (y i : ℚ)) by
              funext i
              exact (hy i).symm]
      _ = eval (fun i => (y i : ℚ)) p :=
        eval_mvPolynomial _ p
      _ = (Int.castRingHom ℚ) (eval y p) := by
        simpa using (map_eval (Int.castRingHom ℚ) y p).symm
      _ = (Int.castRingHom ℚ) (eval y q) := by
        rw [hpq]
      _ = eval (fun i => (y i : ℚ)) q := by
        simpa using map_eval (Int.castRingHom ℚ) y q
      _ = MvPolynomial.eval (fun i => (y i : ℚ)) (toMvPolynomial q) :=
        (eval_mvPolynomial _ q).symm
      _ = MvPolynomial.eval x (toMvPolynomial q) := by
        rw [show (fun i => (y i : ℚ)) = x by
          funext i
          exact hy i]

/-- A polynomial identity between explicit binomial expressions can be
checked on integer tuples and then evaluated in every binomial ring. -/
theorem eval_int
    {ι R : Type*} [CommRing R] [BinomialRing R]
    (x : ι → R) {p q : BPoly ι}
    (hpq : ∀ y : ι → ℤ, eval y p = eval y q) :
    eval x p = eval x q :=
  eval_mv_polynomial x
    (mv_eval_int hpq)

end BPoly

/-- Compositional binomial expressions. Unlike `BPoly`,
whose atoms are binomial coefficients of individual variables, these
expressions are closed under taking binomial coefficients of previously
constructed expressions. This is the working syntax for recursively
substituting Hall coordinate formulas. -/
inductive BExpr (ι : Type*) where
  | const (z : ℤ)
  | var (i : ι)
  | add (p q : BExpr ι)
  | mul (p q : BExpr ι)
  | choose (p : BExpr ι) (n : ℕ)

namespace BExpr

def zero {ι : Type*} : BExpr ι :=
  .const 0

def one {ι : Type*} : BExpr ι :=
  .const 1

def neg {ι : Type*} (p : BExpr ι) : BExpr ι :=
  .mul (.const (-1)) p

def sub {ι : Type*} (p q : BExpr ι) : BExpr ι :=
  .add p (neg q)

instance {ι : Type*} : Zero (BExpr ι) :=
  ⟨zero⟩

instance {ι : Type*} : One (BExpr ι) :=
  ⟨one⟩

instance {ι : Type*} : Add (BExpr ι) :=
  ⟨.add⟩

instance {ι : Type*} : Mul (BExpr ι) :=
  ⟨.mul⟩

instance {ι : Type*} : Neg (BExpr ι) :=
  ⟨neg⟩

instance {ι : Type*} : Sub (BExpr ι) :=
  ⟨sub⟩

/-- Evaluate a compositional binomial expression in an arbitrary
binomial ring. -/
def eval {ι R : Type*} [CommRing R] [BinomialRing R]
    (x : ι → R) : BExpr ι → R
  | .const z => z
  | .var i => x i
  | .add p q => eval x p + eval x q
  | .mul p q => eval x p * eval x q
  | .choose p n => Ring.choose (eval x p) n

@[simp]
lemma eval_const {ι R : Type*} [CommRing R] [BinomialRing R]
    (x : ι → R) (z : ℤ) :
    eval x (.const z) = z :=
  rfl

@[simp]
lemma eval_var {ι R : Type*} [CommRing R] [BinomialRing R]
    (x : ι → R) (i : ι) :
    eval x (.var i) = x i :=
  rfl

@[simp]
lemma eval_add {ι R : Type*} [CommRing R] [BinomialRing R]
    (x : ι → R) (p q : BExpr ι) :
    eval x (p + q) = eval x p + eval x q :=
  rfl

@[simp]
lemma eval_mul {ι R : Type*} [CommRing R] [BinomialRing R]
    (x : ι → R) (p q : BExpr ι) :
    eval x (p * q) = eval x p * eval x q :=
  rfl

@[simp]
lemma eval_choose {ι R : Type*} [CommRing R] [BinomialRing R]
    (x : ι → R) (p : BExpr ι) (n : ℕ) :
    eval x (.choose p n) = Ring.choose (eval x p) n :=
  rfl

@[simp]
lemma eval_zero {ι R : Type*} [CommRing R] [BinomialRing R]
    (x : ι → R) :
    eval x (0 : BExpr ι) = 0 := by
  rw [show (0 : BExpr ι) = zero by rfl, zero, eval_const]
  norm_num

@[simp]
lemma eval_one {ι R : Type*} [CommRing R] [BinomialRing R]
    (x : ι → R) :
    eval x (1 : BExpr ι) = 1 := by
  rw [show (1 : BExpr ι) = one by rfl, one, eval_const]
  norm_num

@[simp]
lemma eval_neg {ι R : Type*} [CommRing R] [BinomialRing R]
    (x : ι → R) (p : BExpr ι) :
    eval x (-p) = -eval x p := by
  rw [show -p = neg p by rfl, neg, eval, eval_const]
  norm_num

@[simp]
lemma eval_sub {ι R : Type*} [CommRing R] [BinomialRing R]
    (x : ι → R) (p q : BExpr ι) :
    eval x (p - q) = eval x p - eval x q := by
  rw [show p - q = sub p q by rfl, sub, eval, neg, eval, eval_const]
  rw [sub_eq_add_neg]
  simp

/-- Substitute compositional binomial expressions for the variables in
another compositional binomial expression. -/
def substitute {ι κ : Type*} (q : ι → BExpr κ) :
    BExpr ι → BExpr κ
  | .const z => .const z
  | .var i => q i
  | .add p r => .add (substitute q p) (substitute q r)
  | .mul p r => .mul (substitute q p) (substitute q r)
  | .choose p n => .choose (substitute q p) n

@[simp]
lemma eval_substitute {ι κ R : Type*} [CommRing R] [BinomialRing R]
    (x : κ → R) (q : ι → BExpr κ) :
    ∀ p : BExpr ι,
      eval x (substitute q p) = eval (fun i => eval x (q i)) p
  | .const _ => rfl
  | .var _ => rfl
  | .add p r => by
      simp only [substitute, eval, eval_substitute x q p,
        eval_substitute x q r]
  | .mul p r => by
      simp only [substitute, eval, eval_substitute x q p,
        eval_substitute x q r]
  | .choose p n => by
      simp only [substitute, eval, eval_substitute x q p]

/-- Rename the variables of a compositional binomial expression. -/
def rename {ι κ : Type*} (f : ι → κ) (p : BExpr ι) :
    BExpr κ :=
  substitute (fun i => .var (f i)) p

@[simp]
lemma eval_rename {ι κ R : Type*} [CommRing R] [BinomialRing R]
    (f : ι → κ) (x : κ → R) (p : BExpr ι) :
    eval x (rename f p) = eval (fun i => x (f i)) p := by
  simp [rename]

/-- Evaluation of compositional binomial expressions commutes with maps
of binomial rings. -/
theorem map_eval {ι R S F : Type*} [CommRing R] [CommRing S]
    [BinomialRing R] [BinomialRing S] [FunLike F R S]
    [RingHomClass F R S] (f : F) (x : ι → R) :
    ∀ p : BExpr ι,
      f (eval x p) = eval (fun i => f (x i)) p
  | .const z => by simp [eval]
  | .var i => rfl
  | .add p q => by simp [eval, map_eval f x p, map_eval f x q]
  | .mul p q => by simp [eval, map_eval f x p, map_eval f x q]
  | .choose p n => by simp [eval, Ring.map_choose, map_eval f x p]

/-- Regard a normalized binomial-basis polynomial as a compositional
binomial expression. -/
def ofPolynomial {ι : Type*} :
    BPoly ι → BExpr ι
  | .const z => .const z
  | .add p q => .add (ofPolynomial p) (ofPolynomial q)
  | .mul p q => .mul (ofPolynomial p) (ofPolynomial q)
  | .choose i n => .choose (.var i) n

@[simp]
lemma eval_ofPolynomial {ι R : Type*} [CommRing R] [BinomialRing R]
    (x : ι → R) :
    ∀ p : BPoly ι,
      eval x (ofPolynomial p) = BPoly.eval x p
  | .const _ => rfl
  | .add p q => by
      simp only [ofPolynomial, eval, BPoly.eval,
        eval_ofPolynomial x p, eval_ofPolynomial x q]
  | .mul p q => by
      simp only [ofPolynomial, eval, BPoly.eval,
        eval_ofPolynomial x p, eval_ofPolynomial x q]
  | .choose i n => rfl

/-- The rational multivariate polynomial obtained by applying a
binomial coefficient to a rational multivariate polynomial. -/
noncomputable def chooseMvPolynomial {ι : Type*}
    (p : MvPolynomial ι ℚ) (n : ℕ) : MvPolynomial ι ℚ :=
  Polynomial.eval₂ MvPolynomial.C p (descPochhammer ℚ n) *
    MvPolynomial.C (n.factorial : ℚ)⁻¹

/-- Forget the compositional binomial operations and retain the
underlying rational multivariate polynomial. -/
noncomputable def toMvPolynomial {ι : Type*} :
    BExpr ι → MvPolynomial ι ℚ
  | .const z => MvPolynomial.C z
  | .var i => MvPolynomial.X i
  | .add p q => toMvPolynomial p + toMvPolynomial q
  | .mul p q => toMvPolynomial p * toMvPolynomial q
  | .choose p n => chooseMvPolynomial (toMvPolynomial p) n

/-- Evaluation commutes with substituting a multivariate polynomial into
an ordinary polynomial. -/
lemma eval_polynomialEval₂ {ι : Type*} (x : ι → ℚ)
    (p : MvPolynomial ι ℚ) (q : Polynomial ℚ) :
    MvPolynomial.eval x (Polynomial.eval₂ MvPolynomial.C p q) =
      Polynomial.eval (MvPolynomial.eval x p) q := by
  rw [Polynomial.hom_eval₂, Polynomial.eval₂_eq_eval_map]
  congr 1
  ext r
  simp

/-- The rational multivariate polynomial semantics agrees with
binomial-ring evaluation over `ℚ`. -/
lemma eval_mvPolynomial {ι : Type*} (x : ι → ℚ) :
    ∀ p : BExpr ι,
      MvPolynomial.eval x (toMvPolynomial p) = eval x p
  | .const z => by simp [toMvPolynomial, eval]
  | .var i => by simp [toMvPolynomial, eval]
  | .add p q => by
      simp [toMvPolynomial, eval, eval_mvPolynomial x p,
        eval_mvPolynomial x q]
  | .mul p q => by
      simp [toMvPolynomial, eval, eval_mvPolynomial x p,
        eval_mvPolynomial x q]
  | .choose p n => by
      rw [toMvPolynomial, chooseMvPolynomial, MvPolynomial.eval_mul,
        MvPolynomial.eval_C, eval_polynomialEval₂,
        eval_mvPolynomial, Polynomial.eval_eq_smeval, eval,
        Ring.choose_eq_smul]
      rw [BPoly.desc_pochhammer_smeval]
      simp [smul_eq_mul, mul_comm]

/-- A descending Pochhammer product with each linear factor scaled by
the common denominator `d`. -/
noncomputable def scaledDescPochhammer {ι R : Type*} [CommRing R]
    (d : R) (p : MvPolynomial ι R) : ℕ → MvPolynomial ι R
  | 0 => 1
  | n + 1 => scaledDescPochhammer d p n *
      (p - MvPolynomial.C (n • d))

/-- Mapping coefficients commutes with scaled descending Pochhammer
products. -/
lemma desc_pochhammer {ι R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (d : R) (p : MvPolynomial ι R) :
    ∀ n : ℕ,
      MvPolynomial.map f (scaledDescPochhammer d p n) =
        scaledDescPochhammer (f d) (MvPolynomial.map f p) n
  | 0 => by simp [scaledDescPochhammer]
  | n + 1 => by
      simp [scaledDescPochhammer, desc_pochhammer f d p n]

/-- Pulling a scalar factor out of every scaled descending Pochhammer
factor produces the expected power of that scalar. -/
lemma scaled_desc_pochhammer {ι R : Type*} [CommRing R]
    (d : R) (p : MvPolynomial ι R) :
    ∀ n : ℕ,
      scaledDescPochhammer d (MvPolynomial.C d * p) n =
        MvPolynomial.C (d ^ n) *
          Polynomial.eval₂ MvPolynomial.C p (descPochhammer R n)
  | 0 => by simp [scaledDescPochhammer]
  | n + 1 => by
      rw [scaledDescPochhammer, scaled_desc_pochhammer d p n,
        descPochhammer_succ_right, Polynomial.eval₂_mul,
        Polynomial.eval₂_sub, Polynomial.eval₂_X,
        Polynomial.eval₂_natCast]
      simp only [pow_succ, nsmul_eq_mul, MvPolynomial.C_mul]
      rw [← map_natCast MvPolynomial.C n]
      ring

/-- Evaluating a scaled descending Pochhammer product after a
denominator-clearing equation pulls out the corresponding scalar
power. -/
lemma eval₂_scaledDescPochhammer {ι R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (x : ι → S) (d : R) (p : MvPolynomial ι R) (a : S)
    (hp : MvPolynomial.eval₂ f x p = f d * a) :
    ∀ n : ℕ,
      MvPolynomial.eval₂ f x (scaledDescPochhammer d p n) =
        (f d) ^ n * Polynomial.eval₂ f a (descPochhammer R n)
  | 0 => by simp [scaledDescPochhammer]
  | n + 1 => by
      rw [scaledDescPochhammer, MvPolynomial.eval₂_mul,
        eval₂_scaledDescPochhammer f x d p a hp n,
        descPochhammer_succ_right, Polynomial.eval₂_mul,
        Polynomial.eval₂_sub, Polynomial.eval₂_X,
        Polynomial.eval₂_natCast, MvPolynomial.eval₂_sub,
        MvPolynomial.eval₂_C, hp]
      simp only [pow_succ, nsmul_eq_mul, map_mul, map_natCast]
      ring

/-- A common positive denominator for the rational multivariate
polynomial underlying a compositional binomial expression. -/
def denominator {ι : Type*} : BExpr ι → ℕ
  | .const _ => 1
  | .var _ => 1
  | .add p q => denominator p * denominator q
  | .mul p q => denominator p * denominator q
  | .choose p n => denominator p ^ n * n.factorial

lemma denominator_ne_zero {ι : Type*} :
    ∀ p : BExpr ι, denominator p ≠ 0
  | .const _ => by simp [denominator]
  | .var _ => by simp [denominator]
  | .add p q =>
      Nat.mul_ne_zero (denominator_ne_zero p) (denominator_ne_zero q)
  | .mul p q =>
      Nat.mul_ne_zero (denominator_ne_zero p) (denominator_ne_zero q)
  | .choose p n =>
      Nat.mul_ne_zero (pow_ne_zero n (denominator_ne_zero p))
        (Nat.factorial_ne_zero n)

/-- Clear all rational denominators in the monomial polynomial
underlying a compositional binomial expression. -/
noncomputable def clearDenominator {ι : Type*} :
    BExpr ι → MvPolynomial ι ℤ
  | .const z => MvPolynomial.C z
  | .var i => MvPolynomial.X i
  | .add p q =>
      MvPolynomial.C (denominator q : ℤ) * clearDenominator p +
        MvPolynomial.C (denominator p : ℤ) * clearDenominator q
  | .mul p q => clearDenominator p * clearDenominator q
  | .choose p n =>
      scaledDescPochhammer (denominator p : ℤ) (clearDenominator p) n

/-- Clearing denominators in the compositional integral monomial model
agrees with multiplying its rational monomial model by the recorded
denominator. -/
lemma map_clearDenominator {ι : Type*} :
    ∀ p : BExpr ι,
      MvPolynomial.map (Int.castRingHom ℚ) (clearDenominator p) =
        MvPolynomial.C (denominator p : ℚ) * toMvPolynomial p
  | .const z => by simp [clearDenominator, denominator, toMvPolynomial]
  | .var i => by simp [clearDenominator, denominator, toMvPolynomial]
  | .add p q => by
      simp only [clearDenominator, denominator, toMvPolynomial,
        map_add, map_mul, map_clearDenominator p, map_clearDenominator q,
        Nat.cast_mul, map_natCast]
      ring
  | .mul p q => by
      simp only [clearDenominator, denominator, toMvPolynomial,
        map_mul, map_clearDenominator p, map_clearDenominator q,
        Nat.cast_mul]
      ring
  | .choose p n => by
      rw [clearDenominator, desc_pochhammer,
        map_clearDenominator p]
      have hcast :
          (Int.castRingHom ℚ) (denominator p : ℤ) =
            (denominator p : ℚ) := by
        simp
      rw [hcast]
      rw [scaled_desc_pochhammer, denominator, toMvPolynomial,
        chooseMvPolynomial]
      simp only [Nat.cast_mul, Nat.cast_pow]
      have hfac : (n.factorial : ℚ) ≠ 0 := by
        exact_mod_cast Nat.factorial_ne_zero n
      have hfactor :
          (MvPolynomial.C ((denominator p : ℚ) ^ n * n.factorial) :
              MvPolynomial ι ℚ) *
              MvPolynomial.C (n.factorial : ℚ)⁻¹ =
            MvPolynomial.C ((denominator p : ℚ) ^ n) := by
        rw [map_mul, mul_assoc, ← map_mul, mul_inv_cancel₀ hfac,
          map_one, mul_one]
      calc
        MvPolynomial.C ((denominator p : ℚ) ^ n) *
              Polynomial.eval₂ MvPolynomial.C (toMvPolynomial p)
                (descPochhammer ℚ n) =
            Polynomial.eval₂ MvPolynomial.C (toMvPolynomial p)
                (descPochhammer ℚ n) *
              MvPolynomial.C ((denominator p : ℚ) ^ n) := by
                rw [mul_comm]
        _ = Polynomial.eval₂ MvPolynomial.C (toMvPolynomial p)
              (descPochhammer ℚ n) *
            (MvPolynomial.C ((denominator p : ℚ) ^ n * n.factorial) *
              MvPolynomial.C (n.factorial : ℚ)⁻¹) := by
                rw [hfactor]
        _ = MvPolynomial.C ((denominator p : ℚ) ^ n * n.factorial) *
            (Polynomial.eval₂ MvPolynomial.C (toMvPolynomial p)
              (descPochhammer ℚ n) *
                MvPolynomial.C (n.factorial : ℚ)⁻¹) := by
                  ring

/-- Evaluation of an integral polynomial at an element of a ring agrees
with scalar evaluation. -/
lemma eval₂_intCast_eq_smeval {R : Type*} [CommRing R]
    (p : Polynomial ℤ) (x : R) :
    Polynomial.eval₂ (Int.castRingHom R) x p = p.smeval x := by
  rw [← Polynomial.eval₂_smulOneHom_eq_smeval]
  congr 1
  ext z
  simp

/-- Evaluating the cleared compositional integral monomial polynomial
agrees with multiplying evaluation of the expression by the recorded
denominator. -/
lemma eval₂_clearDenominator {ι R : Type*} [CommRing R] [BinomialRing R]
    (x : ι → R) :
    ∀ p : BExpr ι,
      MvPolynomial.eval₂ (Int.castRingHom R) x (clearDenominator p) =
        (denominator p : R) * eval x p
  | .const z => by
      rw [clearDenominator, denominator, eval, MvPolynomial.eval₂_C]
      simp
  | .var i => by simp [clearDenominator, denominator, eval]
  | .add p q => by
      simp only [clearDenominator, denominator, eval, MvPolynomial.eval₂_add,
        MvPolynomial.eval₂_mul, eval₂_clearDenominator x p,
        eval₂_clearDenominator x q, Nat.cast_mul, map_natCast,
        MvPolynomial.eval₂_natCast]
      ring
  | .mul p q => by
      simp only [clearDenominator, denominator, eval, MvPolynomial.eval₂_mul,
        eval₂_clearDenominator x p, eval₂_clearDenominator x q,
        Nat.cast_mul]
      ring
  | .choose p n => by
      have hp :
          MvPolynomial.eval₂ (Int.castRingHom R) x (clearDenominator p) =
            (Int.castRingHom R) (denominator p : ℤ) * eval x p := by
        simpa using eval₂_clearDenominator x p
      rw [clearDenominator,
        eval₂_scaledDescPochhammer (Int.castRingHom R) x
          (denominator p : ℤ) (clearDenominator p) (eval x p)
          hp n,
        eval₂_intCast_eq_smeval,
        Ring.descPochhammer_eq_factorial_smul_choose]
      simp only [denominator, Nat.cast_mul, Nat.cast_pow, nsmul_eq_mul,
        map_natCast, eval]
      ring

/-- A rational polynomial identity between compositional binomial
expressions remains valid after evaluation in every binomial ring. -/
theorem eval_mv_polynomial
    {ι R : Type*} [CommRing R] [BinomialRing R]
    (x : ι → R) {p q : BExpr ι}
    (hpq : toMvPolynomial p = toMvPolynomial q) :
    eval x p = eval x q := by
  letI : IsAddTorsionFree R := BinomialRing.toIsAddTorsionFree
  let d := denominator p * denominator q
  have hd : d ≠ 0 :=
    Nat.mul_ne_zero (denominator_ne_zero p) (denominator_ne_zero q)
  apply nsmul_right_injective hd
  have hclear :
      MvPolynomial.C (denominator q : ℤ) * clearDenominator p =
        MvPolynomial.C (denominator p : ℤ) * clearDenominator q := by
    apply MvPolynomial.map_injective (Int.castRingHom ℚ) Int.cast_injective
    simp only [map_mul, map_clearDenominator, map_natCast]
    rw [hpq]
    ring
  calc
    (denominator p * denominator q) • eval x p =
        (denominator q : R) * ((denominator p : R) * eval x p) := by
          simp only [nsmul_eq_mul, Nat.cast_mul]
          ring
    _ = MvPolynomial.eval₂ (Int.castRingHom R) x
          (MvPolynomial.C (denominator q : ℤ) * clearDenominator p) := by
        rw [MvPolynomial.eval₂_mul, MvPolynomial.eval₂_C,
          eval₂_clearDenominator, map_natCast]
    _ = MvPolynomial.eval₂ (Int.castRingHom R) x
          (MvPolynomial.C (denominator p : ℤ) * clearDenominator q) := by
        rw [hclear]
    _ = (denominator p : R) * ((denominator q : R) * eval x q) := by
        rw [MvPolynomial.eval₂_mul, MvPolynomial.eval₂_C,
          eval₂_clearDenominator, map_natCast]
    _ = (denominator p * denominator q) • eval x q := by
        simp only [nsmul_eq_mul, Nat.cast_mul]
        ring

/-- Compositional binomial expressions agreeing on all integer tuples
have the same rational multivariate polynomial semantics. -/
theorem mv_eval_int
    {ι : Type*} {p q : BExpr ι}
    (hpq : ∀ x : ι → ℤ, eval x p = eval x q) :
    toMvPolynomial p = toMvPolynomial q := by
  apply MvPolynomial.funext_set
    (fun _ ↦ Set.range fun z : ℤ => (z : ℚ))
  · intro _
    exact Set.infinite_range_of_injective Int.cast_injective
  · intro x hx
    choose y hy using fun i ↦ hx i (Set.mem_univ i)
    calc
      MvPolynomial.eval x (toMvPolynomial p) =
          MvPolynomial.eval (fun i => (y i : ℚ)) (toMvPolynomial p) := by
            rw [show x = (fun i => (y i : ℚ)) by
              funext i
              exact (hy i).symm]
      _ = eval (fun i => (y i : ℚ)) p := eval_mvPolynomial _ p
      _ = (Int.castRingHom ℚ) (eval y p) := by
        simpa using (map_eval (Int.castRingHom ℚ) y p).symm
      _ = (Int.castRingHom ℚ) (eval y q) := by rw [hpq]
      _ = eval (fun i => (y i : ℚ)) q := by
        simpa using map_eval (Int.castRingHom ℚ) y q
      _ = MvPolynomial.eval (fun i => (y i : ℚ)) (toMvPolynomial q) :=
        (eval_mvPolynomial _ q).symm
      _ = MvPolynomial.eval x (toMvPolynomial q) := by
        rw [show (fun i => (y i : ℚ)) = x by
          funext i
          exact hy i]

/-- An identity between compositional binomial expressions can be
checked on integer tuples and then evaluated in every binomial ring. -/
theorem eval_int
    {ι R : Type*} [CommRing R] [BinomialRing R]
    (x : ι → R) {p q : BExpr ι}
    (hpq : ∀ y : ι → ℤ, eval y p = eval y q) :
    eval x p = eval x q :=
  eval_mv_polynomial x
    (mv_eval_int hpq)

end BExpr

/-- Substitute a family of rational multivariate polynomials into another
rational multivariate polynomial. -/
noncomputable def MvPolynomial.substitute {ι κ : Type*}
    (p : MvPolynomial ι ℚ) (q : ι → MvPolynomial κ ℚ) :
    MvPolynomial κ ℚ :=
  MvPolynomial.eval₂Hom MvPolynomial.C q p

lemma MvPolynomial.eval_substitute {ι κ : Type*}
    (x : κ → ℚ) (p : MvPolynomial ι ℚ)
    (q : ι → MvPolynomial κ ℚ) :
    MvPolynomial.eval x (MvPolynomial.substitute p q) =
      MvPolynomial.eval (fun i => MvPolynomial.eval x (q i)) p := by
  change
    MvPolynomial.eval x (MvPolynomial.eval₂ MvPolynomial.C q p) =
      MvPolynomial.eval (fun i => MvPolynomial.eval x (q i)) p
  rw [← MvPolynomial.eval_assoc]
  rfl

/-- An integer-valued function on an integer affine space is polynomial
when it is represented by a rational multivariate polynomial whose values
on integer inputs are the given integers. The rational coefficient ring is
essential: Hall's preferred basis consists of binomial polynomials such as
`X * (X - 1) / 2`, which are integer-valued but need not have integer
coefficients in the monomial basis. -/
def IVPolya {ι : Type*} (f : (ι → ℤ) → ℤ) : Prop :=
  ∃ p : MvPolynomial ι ℚ, ∀ x,
    MvPolynomial.eval (fun i => (x i : ℚ)) p = (f x : ℚ)

/-- Coordinate projections are rational polynomial maps. -/
theorem integer_valued_polynomial {ι : Type*} (i : ι) :
    IVPolya (fun x : ι → ℤ => x i) := by
  exact ⟨MvPolynomial.X i, fun x => by simp⟩

/-- Constant functions are rational polynomial maps. -/
theorem integer_valued_const {ι : Type*} (z : ℤ) :
    IVPolya (fun _ : ι → ℤ => z) := by
  exact ⟨MvPolynomial.C z, fun _ => by simp⟩

/-- Sums of rational polynomial maps are rational polynomial maps. -/
theorem IVPolya.add
    {ι : Type*} {f g : (ι → ℤ) → ℤ}
    (hf : IVPolya f)
    (hg : IVPolya g) :
    IVPolya (fun x => f x + g x) := by
  obtain ⟨p, hp⟩ := hf
  obtain ⟨q, hq⟩ := hg
  exact ⟨p + q, fun x => by simp [hp, hq]⟩

/-- Products of rational polynomial maps are rational polynomial maps. -/
theorem IVPolya.mul
    {ι : Type*} {f g : (ι → ℤ) → ℤ}
    (hf : IVPolya f)
    (hg : IVPolya g) :
    IVPolya (fun x => f x * g x) := by
  obtain ⟨p, hp⟩ := hf
  obtain ⟨q, hq⟩ := hg
  exact ⟨p * q, fun x => by simp [hp, hq]⟩

/-- Negatives of rational polynomial maps are rational polynomial maps. -/
theorem IVPolya.neg
    {ι : Type*} {f : (ι → ℤ) → ℤ}
    (hf : IVPolya f) :
    IVPolya (fun x => -f x) := by
  obtain ⟨p, hp⟩ := hf
  exact ⟨-p, fun x => by simp [hp]⟩

/-- Differences of rational polynomial maps are rational polynomial maps. -/
theorem IVPolya.sub
    {ι : Type*} {f g : (ι → ℤ) → ℤ}
    (hf : IVPolya f)
    (hg : IVPolya g) :
    IVPolya (fun x => f x - g x) := by
  obtain ⟨p, hp⟩ := hf
  obtain ⟨q, hq⟩ := hg
  exact ⟨p - q, fun x => by simp [hp, hq]⟩

/-- Reindexing the input variables preserves rational polynomial maps. -/
theorem IVPolya.reindex
    {ι κ : Type*} {f : (ι → ℤ) → ℤ}
    (hf : IVPolya f) (e : ι → κ) :
    IVPolya (fun x : κ → ℤ => f (fun i => x (e i))) := by
  obtain ⟨p, hp⟩ := hf
  refine ⟨MvPolynomial.rename e p, fun x => ?_⟩
  rw [MvPolynomial.eval_rename]
  simpa [Function.comp_def] using hp (fun i => x (e i))

/-- Substitution of rational polynomial maps into a rational polynomial map
preserves polynomiality. -/
theorem IVPolya.comp
    {ι κ : Type*} {f : (ι → ℤ) → ℤ} {g : ι → (κ → ℤ) → ℤ}
    (hf : IVPolya f)
    (hg : ∀ i, IVPolya (g i)) :
    IVPolya (fun x => f (fun i => g i x)) := by
  obtain ⟨p, hp⟩ := hf
  choose q hq using hg
  refine ⟨MvPolynomial.substitute p q, fun x => ?_⟩
  rw [MvPolynomial.eval_substitute]
  simp_rw [hq]
  rw [hp]

/-- Polynomial maps agreeing on an integer box with infinitely many
allowed values in every coordinate agree everywhere. This is the
polynomial-identity principle used to extend Hall's positive-power formula
to arbitrary integer exponents. -/
theorem IVPolya.eq_eq_infinite
    {ι : Type*} {f g : (ι → ℤ) → ℤ}
    (hf : IVPolya f)
    (hg : IVPolya g)
    (S : ι → Set ℤ) (hS : ∀ i, (S i).Infinite)
    (hfg : ∀ x, (∀ i, x i ∈ S i) → f x = g x) :
    f = g := by
  obtain ⟨p, hp⟩ := hf
  obtain ⟨q, hq⟩ := hg
  have hpq : p = q := by
    apply MvPolynomial.funext_set
      (fun i ↦ ((fun z : ℤ => (z : ℚ)) '' S i))
    · intro i
      exact (hS i).image (Set.injOn_of_injective Int.cast_injective)
    · intro x hx
      choose y hyS hy using fun i ↦ hx i (Set.mem_univ i)
      calc
        MvPolynomial.eval x p =
            MvPolynomial.eval (fun i => (y i : ℚ)) p := by
              rw [show x = (fun i => (y i : ℚ)) by
                funext i
                exact (hy i).symm]
        _ = (f y : ℚ) := hp y
        _ = (g y : ℚ) := by rw [hfg y hyS]
        _ = MvPolynomial.eval (fun i => (y i : ℚ)) q := (hq y).symm
        _ = MvPolynomial.eval x q := by
              rw [show (fun i => (y i : ℚ)) = x by
                funext i
                exact hy i]
  funext x
  exact Int.cast_injective (α := ℚ) (by rw [← hp x, ← hq x, hpq])

/-- A tuple-valued function is polynomial when each of its coordinates is
an integer-valued rational polynomial. -/
def CIValued {ι κ : Type*}
    (f : (κ → ℤ) → (ι → ℤ)) : Prop :=
  ∀ i, IVPolya (fun x => f x i)

/-- Coordinatewise polynomial tuples can be substituted into
coordinatewise polynomial tuples. -/
theorem CIValued.comp
    {ι κ τ : Type*} {f : (ι → ℤ) → (κ → ℤ)}
    {g : (τ → ℤ) → (ι → ℤ)}
    (hf : CIValued f)
    (hg : CIValued g) :
    CIValued (fun x => f (g x)) := by
  intro i
  exact (hf i).comp hg

/-- Combining two coordinatewise polynomial tuples in disjoint variable
families produces a coordinatewise polynomial tuple on their sum. -/
theorem coordinatewise_valued_elim
    {ι κ τ : Type*} {f : (τ → ℤ) → (ι → ℤ)}
    {g : (τ → ℤ) → (κ → ℤ)}
    (hf : CIValued f)
    (hg : CIValued g) :
    CIValued
      (fun x => Sum.elim (f x) (g x)) := by
  intro i
  cases i with
  | inl i => exact hf i
  | inr i => exact hg i

/-- Adding one polynomial scalar to a coordinatewise polynomial tuple
produces a polynomial tuple on `Option`. -/
theorem coordinatewise_valued_option
    {ι τ : Type*} {a : (τ → ℤ) → ℤ}
    {f : (τ → ℤ) → (ι → ℤ)}
    (ha : IVPolya a)
    (hf : CIValued f) :
    CIValued
      (fun x j => match j with
        | none => a x
        | some i => f x i) := by
  intro i
  cases i with
  | none => exact ha
  | some i => exact hf i

/-- The stronger polynomial property used in Hall's completion
construction: the representing formula is explicitly written in the
binomial basis, so it can be evaluated over any binomial ring. -/
def IBMap {ι : Type*} (f : (ι → ℤ) → ℤ) : Prop :=
  ∃ p : BPoly ι, ∀ x, BPoly.eval x p = f x

theorem IBMap.integer_valued_polymap
    {ι : Type*} {f : (ι → ℤ) → ℤ}
    (hf : IBMap f) :
    IVPolya f := by
  obtain ⟨p, hp⟩ := hf
  refine ⟨p.toMvPolynomial, fun x => ?_⟩
  rw [BPoly.eval_mvPolynomial]
  change
    BPoly.eval (fun i => (Int.castRingHom ℚ) (x i)) p =
      (Int.castRingHom ℚ) (f x)
  rw [← BPoly.map_eval (Int.castRingHom ℚ) x p, hp]

/-- Coordinate projections are binomial-polynomial maps. -/
theorem binomial_polynomial {ι : Type*} (i : ι) :
    IBMap (fun x : ι → ℤ => x i) := by
  exact ⟨.var i, fun x => by simp⟩

/-- Constant functions are binomial-polynomial maps. -/
theorem binomial_polynomial_const {ι : Type*} (z : ℤ) :
    IBMap (fun _ : ι → ℤ => z) := by
  exact ⟨.const z, fun _ => rfl⟩

/-- Sums of binomial-polynomial maps are binomial-polynomial maps. -/
theorem IBMap.add
    {ι : Type*} {f g : (ι → ℤ) → ℤ}
    (hf : IBMap f) (hg : IBMap g) :
    IBMap (fun x => f x + g x) := by
  obtain ⟨p, hp⟩ := hf
  obtain ⟨q, hq⟩ := hg
  exact ⟨p + q, fun x => by simp [hp, hq]⟩

/-- Products of binomial-polynomial maps are binomial-polynomial maps. -/
theorem IBMap.mul
    {ι : Type*} {f g : (ι → ℤ) → ℤ}
    (hf : IBMap f) (hg : IBMap g) :
    IBMap (fun x => f x * g x) := by
  obtain ⟨p, hp⟩ := hf
  obtain ⟨q, hq⟩ := hg
  exact ⟨p * q, fun x => by simp [hp, hq]⟩

/-- Negatives of binomial-polynomial maps are binomial-polynomial maps. -/
theorem IBMap.neg
    {ι : Type*} {f : (ι → ℤ) → ℤ}
    (hf : IBMap f) :
    IBMap (fun x => -f x) := by
  obtain ⟨p, hp⟩ := hf
  exact ⟨-p, fun x => by simp [hp]⟩

/-- Differences of binomial-polynomial maps are binomial-polynomial maps. -/
theorem IBMap.sub
    {ι : Type*} {f g : (ι → ℤ) → ℤ}
    (hf : IBMap f) (hg : IBMap g) :
    IBMap (fun x => f x - g x) := by
  obtain ⟨p, hp⟩ := hf
  obtain ⟨q, hq⟩ := hg
  exact ⟨p - q, fun x => by simp [hp, hq]⟩

/-- Reindexing the input variables preserves binomial-polynomial maps. -/
theorem IBMap.reindex
    {ι κ : Type*} {f : (ι → ℤ) → ℤ}
    (hf : IBMap f) (e : ι → κ) :
    IBMap (fun x : κ → ℤ => f (fun i => x (e i))) := by
  obtain ⟨p, hp⟩ := hf
  exact ⟨p.rename e, fun x => by rw [BPoly.eval_rename, hp]⟩

/-- A map on integer coordinate tuples is represented by a compositional
binomial expression. Such a formula can be substituted recursively and
evaluated over every binomial ring. -/
def IEMap {ι : Type*} (f : (ι → ℤ) → ℤ) : Prop :=
  ∃ p : BExpr ι, ∀ x, BExpr.eval x p = f x

/-- A normalized binomial-basis formula is, in particular, a
compositional binomial formula. -/
theorem IBMap.binomial_expression_map
    {ι : Type*} {f : (ι → ℤ) → ℤ}
    (hf : IBMap f) :
    IEMap f := by
  obtain ⟨p, hp⟩ := hf
  exact ⟨BExpr.ofPolynomial p, fun x => by
    rw [BExpr.eval_ofPolynomial, hp]⟩

/-- Coordinate projections are compositional binomial maps. -/
theorem binomial_expression {ι : Type*} (i : ι) :
    IEMap (fun x : ι → ℤ => x i) :=
  ⟨.var i, fun _ => rfl⟩

/-- Constant functions are compositional binomial maps. -/
theorem binomial_expression_const {ι : Type*} (z : ℤ) :
    IEMap (fun _ : ι → ℤ => z) :=
  ⟨.const z, fun _ => rfl⟩

/-- Sums of compositional binomial maps are compositional binomial
maps. -/
theorem IEMap.add
    {ι : Type*} {f g : (ι → ℤ) → ℤ}
    (hf : IEMap f) (hg : IEMap g) :
    IEMap (fun x => f x + g x) := by
  obtain ⟨p, hp⟩ := hf
  obtain ⟨q, hq⟩ := hg
  exact ⟨p + q, fun x => by simp [hp, hq]⟩

/-- Products of compositional binomial maps are compositional binomial
maps. -/
theorem IEMap.mul
    {ι : Type*} {f g : (ι → ℤ) → ℤ}
    (hf : IEMap f) (hg : IEMap g) :
    IEMap (fun x => f x * g x) := by
  obtain ⟨p, hp⟩ := hf
  obtain ⟨q, hq⟩ := hg
  exact ⟨p * q, fun x => by simp [hp, hq]⟩

/-- Negatives of compositional binomial maps are compositional binomial
maps. -/
theorem IEMap.neg
    {ι : Type*} {f : (ι → ℤ) → ℤ}
    (hf : IEMap f) :
    IEMap (fun x => -f x) := by
  obtain ⟨p, hp⟩ := hf
  exact ⟨-p, fun x => by simp [hp]⟩

/-- Differences of compositional binomial maps are compositional
binomial maps. -/
theorem IEMap.sub
    {ι : Type*} {f g : (ι → ℤ) → ℤ}
    (hf : IEMap f) (hg : IEMap g) :
    IEMap (fun x => f x - g x) := by
  obtain ⟨p, hp⟩ := hf
  obtain ⟨q, hq⟩ := hg
  exact ⟨p - q, fun x => by simp [hp, hq]⟩

/-- Applying a binomial coefficient to a compositional binomial map
produces another compositional binomial map. -/
theorem IEMap.choose
    {ι : Type*} {f : (ι → ℤ) → ℤ}
    (hf : IEMap f) (n : ℕ) :
    IEMap (fun x => Ring.choose (f x) n) := by
  obtain ⟨p, hp⟩ := hf
  exact ⟨.choose p n, fun x => by simp [hp]⟩

/-- Reindexing the input variables preserves compositional binomial
maps. -/
theorem IEMap.reindex
    {ι κ : Type*} {f : (ι → ℤ) → ℤ}
    (hf : IEMap f) (e : ι → κ) :
    IEMap (fun x : κ → ℤ => f (fun i => x (e i))) := by
  obtain ⟨p, hp⟩ := hf
  exact ⟨p.rename e, fun x => by rw [BExpr.eval_rename, hp]⟩

/-- Substitution of compositional binomial maps into another
compositional binomial map preserves representability. -/
theorem IEMap.comp
    {ι κ : Type*} {f : (ι → ℤ) → ℤ} {g : ι → (κ → ℤ) → ℤ}
    (hf : IEMap f)
    (hg : ∀ i, IEMap (g i)) :
    IEMap (fun x => f (fun i => g i x)) := by
  obtain ⟨p, hp⟩ := hf
  choose q hq using hg
  refine ⟨p.substitute q, fun x => ?_⟩
  rw [BExpr.eval_substitute]
  simp_rw [hq]
  rw [hp]

/-- Every compositional binomial expression gives an integer-valued
rational polynomial map. -/
theorem BExpr.eval_integervalued_polymap {ι : Type*} :
    ∀ p : BExpr ι,
      IVPolya (fun x : ι → ℤ =>
        BExpr.eval x p)
  | .const z => integer_valued_const z
  | .var i => integer_valued_polynomial i
  | .add p q =>
      (eval_integervalued_polymap p).add
        (eval_integervalued_polymap q)
  | .mul p q =>
      (eval_integervalued_polymap p).mul
        (eval_integervalued_polymap q)
  | .choose p n => by
      have hatom :
          IVPolya
            (fun x : Unit → ℤ => Ring.choose (x ()) n) :=
        (show IBMap
            (fun x : Unit → ℤ => Ring.choose (x ()) n) from
          ⟨.choose () n, fun _ => rfl⟩).integer_valued_polymap
      exact hatom.comp fun _ => eval_integervalued_polymap p

/-- A compositional binomial formula is an integer-valued rational
polynomial map after forgetting its reusable expression. -/
theorem IEMap.integer_valued_polymap
    {ι : Type*} {f : (ι → ℤ) → ℤ}
    (hf : IEMap f) :
    IVPolya f := by
  obtain ⟨p, hp⟩ := hf
  simpa only [hp] using p.eval_integervalued_polymap

/-- An identity between compositional binomial expressions can be checked
on any integer box having infinitely many allowed values in every
coordinate, then evaluated in every binomial ring. -/
theorem BExpr.evaleq_evalint_eqinfinite
    {ι R : Type*} [CommRing R] [BinomialRing R]
    (x : ι → R) {p q : BExpr ι}
    (S : ι → Set ℤ) (hS : ∀ i, (S i).Infinite)
    (hpq : ∀ y : ι → ℤ, (∀ i, y i ∈ S i) →
      BExpr.eval y p = BExpr.eval y q) :
    BExpr.eval x p = BExpr.eval x q := by
  apply BExpr.eval_mv_polynomial x
  apply BExpr.mv_eval_int
  have hfun :
      (fun y : ι → ℤ => BExpr.eval y p) =
        fun y : ι → ℤ => BExpr.eval y q :=
    IVPolya.eq_eq_infinite
      p.eval_integervalued_polymap q.eval_integervalued_polymap
      S hS hpq
  intro y
  exact congrFun hfun y

/-- A tuple-valued function is compositionally binomial when each
coordinate is represented by a compositional binomial expression. -/
def CBExpr {ι κ : Type*}
    (f : (κ → ℤ) → (ι → ℤ)) : Prop :=
  ∀ i, IEMap (fun x => f x i)

/-- Coordinatewise compositional binomial tuples can be substituted
into one another. -/
theorem CBExpr.comp
    {ι κ τ : Type*} {f : (ι → ℤ) → (κ → ℤ)}
    {g : (τ → ℤ) → (ι → ℤ)}
    (hf : CBExpr f)
    (hg : CBExpr g) :
    CBExpr (fun x => f (g x)) := by
  intro i
  exact (hf i).comp hg

/-- Combining coordinatewise compositional binomial tuples produces a
tuple on a sum type. -/
theorem coordinatewise_expression_elim
    {ι κ τ : Type*} {f : (τ → ℤ) → (ι → ℤ)}
    {g : (τ → ℤ) → (κ → ℤ)}
    (hf : CBExpr f)
    (hg : CBExpr g) :
    CBExpr
      (fun x => Sum.elim (f x) (g x)) := by
  intro i
  cases i with
  | inl i => exact hf i
  | inr i => exact hg i

/-- Adding one compositional binomial scalar to a coordinatewise tuple
produces a tuple on `Option`. -/
theorem coordinatewise_expression_option
    {ι τ : Type*} {a : (τ → ℤ) → ℤ}
    {f : (τ → ℤ) → (ι → ℤ)}
    (ha : IEMap a)
    (hf : CBExpr f) :
    CBExpr
      (fun x j => match j with
        | none => a x
        | some i => f x i) := by
  intro i
  cases i with
  | none => exact ha
  | some i => exact hf i

/-- The second binomial coefficient on an arbitrary integer. -/
def integerChooseTwo (z : ℤ) : ℤ :=
  z * (z - 1) / 2

/-- The elementary integer formula agrees with the binomial-ring
coefficient. -/
lemma integer_choose_ring (z : ℤ) :
    integerChooseTwo z = Ring.choose z 2 := by
  apply Int.cast_injective (α := ℚ)
  rw [integerChooseTwo, Int.cast_div
    (Int.even_mul_pred_self z |>.two_dvd) (by norm_num)]
  norm_num only [Int.cast_mul, Int.cast_sub, Int.cast_one, Int.cast_ofNat]
  change
    (z : ℚ) * ((z : ℚ) - 1) / 2 =
      (Int.castRingHom ℚ) (Ring.choose z 2)
  rw [Ring.map_choose (Int.castRingHom ℚ), Ring.choose_eq_smul]
  norm_num [descPochhammer, Polynomial.smeval_mul, Polynomial.smeval_sub]
  ring

/-- Hall's basic binomial polynomial is represented in the stronger
binomial-basis model. -/
theorem integer_choose_binomial :
    IBMap
      (fun x : Unit → ℤ => integerChooseTwo (x ())) := by
  refine ⟨.choose () 2, fun x => ?_⟩
  change Ring.choose (x ()) 2 = integerChooseTwo (x ())
  exact (integer_choose_ring _).symm

/-- The polynomial model admits Hall's basic binomial polynomial
`X * (X - 1) / 2`, despite its nonintegral monomial coefficient. -/
theorem integer_choose_valued :
    IVPolya
      (fun x : Unit → ℤ => integerChooseTwo (x ())) := by
  exact
    integer_choose_binomial.integer_valued_polymap

/-- Ordinary torsion-freeness implies Hall's absolute `ω`-torsion-freeness
when `ω` is the set of all primes. -/
lemma omega_torsion_univ
    [IsMulTorsionFree G] :
    OmegaTorsionFree Set.univ G := by
  intro x hx
  exact hx.1.eq_one'

/-- In a quotient by an absolutely isolated normal subgroup, every
finite-order element is trivial. -/
lemma omega_isolated_univ
    (N : Subgroup G) [N.Normal]
    (hN : IsOmegaIsolated Set.univ N)
    (q : G ⧸ N) (hq : IsOfFinOrder q) :
    q = 1 := by
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective N q
  apply (QuotientGroup.eq_one_iff x).mpr
  obtain ⟨n, hn, hpow⟩ := hq.exists_pow_eq_one
  apply hN x n
  · exact ⟨hn.ne', by simp⟩
  · apply (QuotientGroup.eq_one_iff (x ^ n)).mp
    simpa using hpow

/-- A finitely generated torsion-free abelian group has a finite basis over
the infinite cyclic group. -/
theorem CommGroup.exists_pimul_fgtor
    (A : Type*) [CommGroup A] [Group.FG A] [IsMulTorsionFree A] :
    ∃ n : ℕ, Nonempty (A ≃* (Fin n → Multiplicative ℤ)) := by
  classical
  obtain ⟨ι, j, hι, hj, p, hp, e, ⟨f⟩⟩ :=
    CommGroup.equiv_free_prod_prod_multiplicative_zmod A
  letI : Fintype ι := hι
  letI : Fintype j := hj
  letI : ∀ i, NeZero (p i ^ e i) :=
    fun i ↦ ⟨pow_ne_zero _ (hp i).ne_zero⟩
  let F : Type := j → Multiplicative ℤ
  let T : Type := (i : ι) → Multiplicative (ZMod (p i ^ e i))
  letI : Finite T := by
    dsimp [T]
    infer_instance
  let proj : A →* F :=
    (MonoidHom.fst F T).comp f.toMonoidHom
  have hprojSurjective :
      Function.Surjective proj := by
    intro y
    refine ⟨f.symm (y, 1), ?_⟩
    simp [proj]
  have hprojInjective :
      Function.Injective proj := by
    intro a b hab
    have hfst :
        (f (a / b)).1 = 1 := by
      change proj (a / b) = 1
      simp [map_div, hab]
    have hfiniteImage :
        IsOfFinOrder (f (a / b)) := by
      have himage :
          f (a / b) = (1, (f (a / b)).2) :=
        Prod.ext hfst rfl
      rw [himage]
      exact IsOfFinOrder.prod_mk IsOfFinOrder.one
        (isOfFinOrder_of_finite _)
    have hfinite :
        IsOfFinOrder (a / b) :=
      by
        obtain ⟨n, hn, hpow⟩ := hfiniteImage.exists_pow_eq_one
        apply isOfFinOrder_iff_pow_eq_one.mpr
        refine ⟨n, hn, ?_⟩
        apply f.injective
        simpa using hpow
    exact div_eq_one.mp hfinite.eq_one'
  let freeEquiv : A ≃* F :=
    MulEquiv.ofBijective proj ⟨hprojInjective, hprojSurjective⟩
  let indexEquiv : j ≃ Fin (Fintype.card j) :=
    Fintype.equivFin j
  exact
    ⟨Fintype.card j,
      ⟨freeEquiv.trans
        (MulEquiv.arrowCongr indexEquiv (MulEquiv.refl (Multiplicative ℤ)))⟩⟩

/-- Isolation is preserved when the ambient group is restricted to a
subgroup containing the isolated subgroup. -/
lemma omega_isolated_subgroup
    (ω : Set ℕ) {K H : Subgroup G}
    (hK : IsOmegaIsolated ω K) :
    IsOmegaIsolated ω (K.subgroupOf H) := by
  intro x n hn hx
  exact hK x n hn hx

/-- A quotient `H / K` is commutative when the commutator subgroup of `H`
lies in `K`. -/
@[reducible]
noncomputable def subgroupCommCommutator
    {H K : Subgroup G} (hK_le_H : K ≤ H)
    (hcomm : ⁅H, H⁆ ≤ K) :
    CommGroup (H ⧸ K.subgroupOf H) := by
  letI : (K.subgroupOf H).Normal :=
    normal_subgroup_commutator hK_le_H hcomm
  let base : Group (H ⧸ K.subgroupOf H) := inferInstance
  exact
    { base with
      mul_comm := by
        intro a b
        obtain ⟨a, rfl⟩ :=
          QuotientGroup.mk'_surjective (K.subgroupOf H) a
        obtain ⟨b, rfl⟩ :=
          QuotientGroup.mk'_surjective (K.subgroupOf H) b
        rw [← commutatorElement_eq_one_iff_mul_comm,
          ← map_commutatorElement]
        exact
          (QuotientGroup.eq_one_iff (N := K.subgroupOf H) ⁅a, b⁆).mpr
            (hcomm (Subgroup.commutator_mem_commutator a.2 b.2)) }

/-- Every adjacent factor of the upper central series of a finitely generated
torsion-free nilpotent group is a finite product of infinite cyclic groups. -/
theorem upper_pi_multiplicative
    [Group.FG G] [Group.IsNilpotent G] [IsMulTorsionFree G]
    (n : ℕ) :
    ∃ r : ℕ,
      Nonempty
        ((Subgroup.upperCentralSeries G (n + 1) ⧸
            (Subgroup.upperCentralSeries G n).subgroupOf
              (Subgroup.upperCentralSeries G (n + 1))) ≃*
          (Fin r → Multiplicative ℤ)) := by
  let K : Subgroup G := Subgroup.upperCentralSeries G n
  let H : Subgroup G := Subgroup.upperCentralSeries G (n + 1)
  have hK_le_H : K ≤ H :=
    Subgroup.upperCentralSeries_mono G (Nat.le_succ n)
  have hcomm : ⁅H, H⁆ ≤ K :=
    (Subgroup.commutator_mono le_rfl le_top).trans
      (upper_series_commutator n)
  letI : (K.subgroupOf H).Normal :=
    normal_subgroup_commutator hK_le_H hcomm
  letI : CommGroup (H ⧸ K.subgroupOf H) :=
    subgroupCommCommutator hK_le_H hcomm
  have hHfg : H.FG :=
    fg_nilpotent Group.FG.out le_top
  letI : Group.FG H := (Group.fg_iff_subgroup_fg H).mpr hHfg
  letI : Group.FG (H ⧸ K.subgroupOf H) := QuotientGroup.fg _
  have hKisolated : IsOmegaIsolated Set.univ K :=
    upper_omega_isolated
      (locally_nilpotent
        (inferInstance : Group.IsNilpotent G))
      Set.univ omega_torsion_univ n
  have hKsubisolated : IsOmegaIsolated Set.univ (K.subgroupOf H) :=
    omega_isolated_subgroup Set.univ hKisolated
  letI : IsMulTorsionFree (H ⧸ K.subgroupOf H) :=
    IsMulTorsionFree.of_not_isOfFinOrder fun q hqne hqfin ↦
      hqne (omega_isolated_univ
        (K.subgroupOf H) hKsubisolated q hqfin)
  exact CommGroup.exists_pimul_fgtor
    (H ⧸ K.subgroupOf H)

/-- The rank of a chosen integer-coordinate basis for an adjacent
upper-central factor. -/
noncomputable def upperSeriesRank
    [Group.FG G] [Group.IsNilpotent G] [IsMulTorsionFree G]
    (n : ℕ) : ℕ :=
  Classical.choose
    (upper_pi_multiplicative
      (G := G) n)

/-- A chosen integer-coordinate basis for an adjacent upper-central factor. -/
noncomputable def upperSeriesFactor
    [Group.FG G] [Group.IsNilpotent G] [IsMulTorsionFree G]
    (n : ℕ) :
    (Subgroup.upperCentralSeries G (n + 1) ⧸
        (Subgroup.upperCentralSeries G n).subgroupOf
          (Subgroup.upperCentralSeries G (n + 1))) ≃*
      (Fin (upperSeriesRank (G := G) n) → Multiplicative ℤ) :=
  Classical.choice
    (Classical.choose_spec
      (upper_pi_multiplicative
        (G := G) n))

/-- The ordered product represented by a tuple of canonical parameters. -/
def canonicalBasisProduct {n : ℕ} (u : Fin n → G) (x : Fin n → ℤ) : G :=
  orderedZPow u x (List.finRange n)

/-- A canonical basis in Hall's sense. The subgroup `tail k` represents
`G_k`: its elements are precisely those whose first `k` canonical
parameters vanish. The commutator condition records that every adjacent
factor is central in the ambient quotient. -/
structure HCBasis (G : Type u) [Group G] (n : ℕ) where
  generators : Fin n → G
  coord : G ≃ (Fin n → ℤ)
  symm_apply : ∀ x, coord.symm x = canonicalBasisProduct generators x
  generator_coord : ∀ i j, coord (generators i) j = if i = j then 1 else 0
  tail : ℕ → Subgroup G
  tail_zero : tail 0 = ⊤
  tail_length : tail n = ⊥
  tail_succ_le : ∀ k, tail (k + 1) ≤ tail k
  tail_normal : ∀ k, (tail k).Normal
  tail_central : ∀ k, ⁅tail k, (⊤ : Subgroup G)⁆ ≤ tail (k + 1)
  mem_tail_iff : ∀ {k} (_ : k ≤ n) {g : G},
    g ∈ tail k ↔ ∀ i : Fin n, (i : ℕ) < k → coord g i = 0

namespace HCBasis

lemma coord_basis_product {n : ℕ} (b : HCBasis G n)
    (x : Fin n → ℤ) :
    b.coord (canonicalBasisProduct b.generators x) = x := by
  rw [← b.symm_apply, b.coord.apply_symm_apply]

lemma canonical_basis_coord {n : ℕ} (b : HCBasis G n)
    (g : G) :
    canonicalBasisProduct b.generators (b.coord g) = g := by
  rw [← b.symm_apply, b.coord.symm_apply_apply]

lemma mem_iff_le {n k : ℕ} (b : HCBasis G n)
    (hk : k ≤ n) {g : G} :
    g ∈ b.tail k ↔
      ∀ i : Fin n, (i : ℕ) < k → b.coord g i = 0 :=
  b.mem_tail_iff hk

lemma generator_succ_tail {n : ℕ}
    (b : HCBasis G (n + 1)) (i : Fin n) :
    b.generators i.succ ∈ b.tail 1 := by
  rw [b.mem_tail_iff (by omega)]
  intro j hj
  rw [b.generator_coord]
  have hne : i.succ ≠ j := by
    intro h
    subst j
    simp only [Fin.val_succ] at hj
    omega
  simp [hne]

/-- The coordinate equivalence on the first tail subgroup is obtained by
dropping the initial zero coordinate. -/
def tailCoordEquiv {n : ℕ} (b : HCBasis G (n + 1)) :
    b.tail 1 ≃ (Fin n → ℤ) where
  toFun g i := b.coord g.1 i.succ
  invFun x :=
    ⟨b.coord.symm (Fin.cons 0 x), by
      rw [b.mem_tail_iff (by omega)]
      intro i hi
      have hi0 : i = 0 := by
        apply Fin.ext
        simp only [Fin.val_zero]
        omega
      subst i
      simp⟩
  left_inv g := by
    apply Subtype.ext
    apply b.coord.injective
    rw [b.coord.apply_symm_apply]
    funext i
    refine Fin.cases ?_ (fun _ => rfl) i
    simpa using
      ((b.mem_tail_iff (by omega)).mp g.property
        (0 : Fin (n + 1)) (by simp)).symm
  right_inv x := by
    funext i
    simp

/-- Splitting off the first canonical parameter splits the corresponding
ordered product into its first factor and the shifted tail product. -/
lemma canonical_basis_cons {n : ℕ} (u : Fin (n + 1) → G)
    (a : ℤ) (x : Fin n → ℤ) :
    canonicalBasisProduct u (Fin.cons a x) =
      u 0 ^ a * canonicalBasisProduct (fun i => u i.succ) x := by
  simp [canonicalBasisProduct, orderedZPow, List.finRange_succ,
    Function.comp_def]

/-- A finite ambient-central series ending in the trivial subgroup, with
every adjacent factor infinite cyclic. The witness `x` generates `H / K`,
and `hinfinite` says that no nonzero power of `x` falls back into `K`. -/
inductive ICSeries (G : Type u) [Group G] :
    Subgroup G → Type u
  | bot : ICSeries G ⊥
  | step {H K : Subgroup G}
      (hK_le_H : K ≤ H)
      (hK_normal : K.Normal)
      (hcentral : ⁅H, (⊤ : Subgroup G)⁆ ≤ K)
      (x : G) (hx : x ∈ H)
      (hgenerate : H = Subgroup.closure ((K : Set G) ∪ {x}))
      (hinfinite : ∀ a : ℤ, x ^ a ∈ K → a = 0)
      (tail : ICSeries G K) :
      ICSeries G H

/-- A later canonical generator belongs to every earlier recorded tail. -/
lemma generator_tail {n k : ℕ} (b : HCBasis G n)
    (hk : k ≤ n) (j : Fin n) (hkj : k ≤ (j : ℕ)) :
    b.generators j ∈ b.tail k := by
  rw [b.mem_tail_iff hk]
  intro i hi
  rw [b.generator_coord]
  simp only [ite_eq_right_iff]
  intro hji
  subst i
  omega

/-- Each canonical-basis tail is generated by its successor and its
designated generator. -/
lemma tail_union_generator {n : ℕ}
    (b : HCBasis G n) (i : Fin n) :
    b.tail i = Subgroup.closure (((b.tail ((i : ℕ) + 1) : Subgroup G) : Set G) ∪
      {b.generators i}) := by
  apply le_antisymm
  · intro g hg
    rw [← b.canonical_basis_coord g]
    unfold canonicalBasisProduct orderedZPow
    apply (Subgroup.closure _).list_prod_mem
    intro z hz
    simp only [List.mem_map] at hz
    obtain ⟨j, _, rfl⟩ := hz
    by_cases hjlt : (j : ℕ) < (i : ℕ)
    · have hcoord := (b.mem_tail_iff (Nat.le_of_lt i.isLt)).mp hg j hjlt
      rw [hcoord, zpow_zero]
      exact Subgroup.one_mem _
    · by_cases hji : j = i
      · subst j
        exact (Subgroup.closure _).zpow_mem
          (Subgroup.subset_closure
            (show b.generators i ∈
              ((b.tail ((i : ℕ) + 1) : Subgroup G) : Set G) ∪
                {b.generators i} by simp)) _
      · have hij : (i : ℕ) + 1 ≤ (j : ℕ) := by omega
        exact (Subgroup.closure _).zpow_mem
          (Subgroup.subset_closure
            (show b.generators j ∈
              ((b.tail ((i : ℕ) + 1) : Subgroup G) : Set G) ∪
                {b.generators i} by
              exact Or.inl
                (b.generator_tail (by omega) j hij))) _
  · rw [Subgroup.closure_le]
    rintro g (hg | hg)
    · exact b.tail_succ_le i hg
    · rw [Set.mem_singleton_iff.mp hg]
      exact b.generator_tail (Nat.le_of_lt i.isLt) i le_rfl

/-- An ordered product supported at one position is the corresponding
power, provided the displayed positions have no duplicates. -/
lemma ordered_z_single {ι : Type*} [DecidableEq ι]
    (u : ι → G) (a : ℤ) (l : List ι) (hl : l.Nodup)
    (i : ι) (hi : i ∈ l) :
    orderedZPow u (fun j => if i = j then a else 0) l =
      u i ^ a := by
  induction l with
  | nil => simp at hi
  | cons j l ih =>
      have hjnotmem : j ∉ l := (List.nodup_cons.mp hl).1
      have hlnodup : l.Nodup := (List.nodup_cons.mp hl).2
      rw [show orderedZPow u (fun j => if i = j then a else 0)
          (j :: l) =
        u j ^ (if i = j then a else 0) *
          orderedZPow u (fun j => if i = j then a else 0) l by
            rfl]
      by_cases hji : i = j
      · subst j
        rw [if_pos rfl]
        have hzero :
            ∀ k ∈ l, (if i = k then a else 0) = 0 := by
          intro k hk
          rw [if_neg]
          intro hik
          subst k
          exact hjnotmem hk
        rw [ordered_z_zero _ _ _ hzero, mul_one]
      · rw [if_neg hji, zpow_zero, one_mul]
        apply ih hlnodup
        simpa [hji] using hi

/-- The coordinate of a power of an arbitrary canonical generator in its
own position is its exponent. -/
lemma coord_zpow_generator {n : ℕ}
    (b : HCBasis G n) (i : Fin n) (a : ℤ) :
    b.coord (b.generators i ^ a) i = a := by
  let x : Fin n → ℤ := fun j => if i = j then a else 0
  have hprod :
      canonicalBasisProduct b.generators x = b.generators i ^ a := by
    exact ordered_z_single b.generators a (List.finRange n)
      (List.nodup_finRange n) i (List.mem_finRange i)
  have hcoord := congrFun (b.coord_basis_product x) i
  rw [hprod] at hcoord
  simpa [x] using hcoord

/-- No nonzero power of a canonical generator lies in the following
recorded tail. -/
lemma generator_zpow_succ {n : ℕ}
    (b : HCBasis G n) (i : Fin n) (a : ℤ) :
    b.generators i ^ a ∈ b.tail ((i : ℕ) + 1) ↔ a = 0 := by
  constructor
  · intro h
    have hcoord := (b.mem_tail_iff (by omega)).mp h i (by omega)
    rw [b.coord_zpow_generator] at hcoord
    exact hcoord
  · rintro rfl
    simp

namespace ICSeries

/-- The recorded tails of any canonical basis themselves form ambient
infinite-cyclic central series. -/
noncomputable def canonicalBasisTail {n : ℕ}
    (b : HCBasis G n) :
    ∀ k : ℕ, k ≤ n → ICSeries G (b.tail k) :=
  fun k hk ↦ by
    have hbase :
        ICSeries G (b.tail n) := by
      simpa only [b.tail_length] using
        (ICSeries.bot :
          ICSeries G (⊥ : Subgroup G))
    exact
      Nat.decreasingInduction
        (motive := fun k _ ↦
          ICSeries G (b.tail k))
        (fun k hk ih ↦
          ICSeries.step
            (b.tail_succ_le k)
            (b.tail_normal (k + 1))
            (b.tail_central k)
            (b.generators ⟨k, hk⟩)
            (b.generator_tail (Nat.le_of_lt hk) ⟨k, hk⟩ le_rfl)
            (b.tail_union_generator ⟨k, hk⟩)
            (fun a ha ↦
              (b.generator_zpow_succ ⟨k, hk⟩ a).mp ha)
            ih)
        hbase hk

end ICSeries

/-- Coordinates on a free-abelian central factor, represented as
multiplicative integer tuples. -/
noncomputable def centralFactorCoordinates
    {K H : Subgroup G} [K.Normal] {r : ℕ}
    (e : H ⧸ K.subgroupOf H ≃* (Fin r → Multiplicative ℤ)) :
    H →* (Fin r → Multiplicative ℤ) :=
  e.toMonoidHom.comp (QuotientGroup.mk' (K.subgroupOf H))

/-- The subgroup whose first `k` coordinates in a free-abelian central
factor vanish. -/
noncomputable def centralCoordinateTail
    {K H : Subgroup G} [K.Normal] {r : ℕ}
    (e : H ⧸ K.subgroupOf H ≃* (Fin r → Multiplicative ℤ))
    (k : ℕ) : Subgroup G where
  carrier := {x | ∃ hx : x ∈ H,
    ∀ i : Fin r, (i : ℕ) < k → centralFactorCoordinates e ⟨x, hx⟩ i = 1}
  one_mem' := by
    refine ⟨H.one_mem, ?_⟩
    intro i hi
    change centralFactorCoordinates e (1 : H) i = 1
    rw [map_one]
    rfl
  mul_mem' := by
    rintro x y ⟨hx, hxc⟩ ⟨hy, hyc⟩
    refine ⟨H.mul_mem hx hy, ?_⟩
    intro i hi
    rw [show (⟨x * y, H.mul_mem hx hy⟩ : H) =
      ⟨x, hx⟩ * ⟨y, hy⟩ by rfl, map_mul]
    change centralFactorCoordinates e ⟨x, hx⟩ i *
      centralFactorCoordinates e ⟨y, hy⟩ i = 1
    rw [hxc i hi, hyc i hi, one_mul]
  inv_mem' := by
    rintro x ⟨hx, hxc⟩
    refine ⟨H.inv_mem hx, ?_⟩
    intro i hi
    rw [show (⟨x⁻¹, H.inv_mem hx⟩ : H) = (⟨x, hx⟩ : H)⁻¹ by rfl,
      map_inv]
    change (centralFactorCoordinates e ⟨x, hx⟩ i)⁻¹ = 1
    rw [hxc i hi, inv_one]

@[simp]
lemma central_coordinate_tail
    {K H : Subgroup G} [K.Normal] {r : ℕ}
    (e : H ⧸ K.subgroupOf H ≃* (Fin r → Multiplicative ℤ))
    (k : ℕ) (x : G) :
    x ∈ centralCoordinateTail e k ↔
      ∃ hx : x ∈ H,
        ∀ i : Fin r, (i : ℕ) < k →
          centralFactorCoordinates e ⟨x, hx⟩ i = 1 :=
  Iff.rfl

lemma central_tail_zero
    {K H : Subgroup G} [K.Normal] {r : ℕ}
    (e : H ⧸ K.subgroupOf H ≃* (Fin r → Multiplicative ℤ)) :
    centralCoordinateTail e 0 = H := by
  ext x
  simp

lemma central_tail_length
    {K H : Subgroup G} [K.Normal] {r : ℕ} (hK_le_H : K ≤ H)
    (e : H ⧸ K.subgroupOf H ≃* (Fin r → Multiplicative ℤ)) :
    centralCoordinateTail e r = K := by
  ext x
  constructor
  · rintro ⟨hx, hcoord⟩
    apply (QuotientGroup.eq_one_iff (N := K.subgroupOf H) ⟨x, hx⟩).mp
    apply e.injective
    funext i
    simpa using hcoord i i.isLt
  · intro hx
    refine ⟨hK_le_H hx, ?_⟩
    intro i hi
    simp [centralFactorCoordinates,
      (QuotientGroup.eq_one_iff
        (N := K.subgroupOf H) ⟨x, hK_le_H hx⟩).mpr hx]

lemma central_tail_succ
    {K H : Subgroup G} [K.Normal] {r : ℕ}
    (e : H ⧸ K.subgroupOf H ≃* (Fin r → Multiplicative ℤ))
    (k : ℕ) :
    centralCoordinateTail e (k + 1) ≤
      centralCoordinateTail e k := by
  rintro x ⟨hx, hcoord⟩
  exact ⟨hx, fun i hi ↦ hcoord i (by omega)⟩

lemma factor_coordinate_tail
    {K H : Subgroup G} [K.Normal] {r : ℕ}
    (e : H ⧸ K.subgroupOf H ≃* (Fin r → Multiplicative ℤ))
    (k : ℕ) :
    centralCoordinateTail e k ≤ H := by
  rintro x ⟨hx, _⟩
  exact hx

lemma central_factor_coordinate
    {K H : Subgroup G} [K.Normal] {r : ℕ} (hK_le_H : K ≤ H)
    (e : H ⧸ K.subgroupOf H ≃* (Fin r → Multiplicative ℤ))
    (k : ℕ) :
    K ≤ centralCoordinateTail e k := by
  intro x hx
  refine ⟨hK_le_H hx, ?_⟩
  intro i hi
  simp [centralFactorCoordinates,
    (QuotientGroup.eq_one_iff
      (N := K.subgroupOf H) ⟨x, hK_le_H hx⟩).mpr hx]

lemma central_factor_tail
    {K H : Subgroup G} [K.Normal] {r : ℕ} (hK_le_H : K ≤ H)
    (hcentral : ⁅H, (⊤ : Subgroup G)⁆ ≤ K)
    (e : H ⧸ K.subgroupOf H ≃* (Fin r → Multiplicative ℤ))
    (k : ℕ) :
    ⁅centralCoordinateTail e k, (⊤ : Subgroup G)⁆ ≤
      centralCoordinateTail e (k + 1) :=
  (Subgroup.commutator_mono (factor_coordinate_tail e k) le_rfl).trans
    (hcentral.trans (central_factor_coordinate hK_le_H e (k + 1)))

lemma central_tail_normal
    {K H : Subgroup G} [K.Normal] {r : ℕ} (hK_le_H : K ≤ H)
    (hcentral : ⁅H, (⊤ : Subgroup G)⁆ ≤ K)
    (e : H ⧸ K.subgroupOf H ≃* (Fin r → Multiplicative ℤ))
    (k : ℕ) :
    (centralCoordinateTail e k).Normal :=
  Subgroup.commutator_top_right_le_iff.mp
    ((central_factor_tail hK_le_H hcentral e k).trans
      (central_tail_succ e k))

/-- The `i`th standard basis vector of a multiplicative integer tuple. -/
def centralBasisVector {r : ℕ} (i : Fin r) :
    Fin r → Multiplicative ℤ :=
  Pi.mulSingle i (Multiplicative.ofAdd 1)

/-- A chosen lift to `H` of a standard basis vector in `H / K`. -/
noncomputable def centralBasisLift
    {K H : Subgroup G} [K.Normal] {r : ℕ}
    (e : H ⧸ K.subgroupOf H ≃* (Fin r → Multiplicative ℤ))
    (i : Fin r) : H :=
  Classical.choose
    (QuotientGroup.mk'_surjective (K.subgroupOf H)
      (e.symm (centralBasisVector i)))

lemma coordinates_basis_lift
    {K H : Subgroup G} [K.Normal] {r : ℕ}
    (e : H ⧸ K.subgroupOf H ≃* (Fin r → Multiplicative ℤ))
    (i : Fin r) :
    centralFactorCoordinates e (centralBasisLift e i) =
      centralBasisVector i := by
  change e ((QuotientGroup.mk' (K.subgroupOf H)) (centralBasisLift e i)) =
    centralBasisVector i
  rw [centralBasisLift,
    Classical.choose_spec
      (QuotientGroup.mk'_surjective (K.subgroupOf H)
        (e.symm (centralBasisVector i))), e.apply_symm_apply]

lemma basis_lift_tail
    {K H : Subgroup G} [K.Normal] {r : ℕ}
    (e : H ⧸ K.subgroupOf H ≃* (Fin r → Multiplicative ℤ))
    (i : Fin r) :
    (centralBasisLift e i : G) ∈ centralCoordinateTail e i := by
  refine ⟨(centralBasisLift e i).2, ?_⟩
  intro j hj
  rw [coordinates_basis_lift]
  exact Pi.mulSingle_eq_of_ne (by
    intro h
    subst j
    exact (Nat.lt_irrefl _ hj)) _

lemma lift_zpow_tail
    {K H : Subgroup G} [K.Normal] {r : ℕ}
    (e : H ⧸ K.subgroupOf H ≃* (Fin r → Multiplicative ℤ))
    (i : Fin r) (a : ℤ) :
    (centralBasisLift e i : G) ^ a ∈
        centralCoordinateTail e ((i : ℕ) + 1) ↔
      a = 0 := by
  constructor
  · rintro ⟨_, hcoord⟩
    have h := hcoord i (by omega)
    rw [show (⟨(centralBasisLift e i : G) ^ a, _⟩ : H) =
      (centralBasisLift e i) ^ a by rfl,
      map_zpow, coordinates_basis_lift] at h
    have hsame := congrArg Multiplicative.toAdd h
    simpa [centralBasisVector] using hsame
  · rintro rfl
    simp

/-- One coordinate tail is generated by the next one and the corresponding
standard basis lift. -/
lemma union_basis_lift
    {K H : Subgroup G} [K.Normal] {r : ℕ}
    (e : H ⧸ K.subgroupOf H ≃* (Fin r → Multiplicative ℤ))
    (i : Fin r) :
    centralCoordinateTail e i =
      Subgroup.closure
        (((centralCoordinateTail e ((i : ℕ) + 1) : Subgroup G) : Set G) ∪
          {(centralBasisLift e i : G)}) := by
  apply le_antisymm
  · intro y hy
    have hyH : y ∈ H := factor_coordinate_tail e i hy
    let a : ℤ := (centralFactorCoordinates e ⟨y, hyH⟩ i).toAdd
    have hremTail :
        y * (centralBasisLift e i : G) ^ (-a) ∈
          centralCoordinateTail e ((i : ℕ) + 1) := by
      refine
        ⟨H.mul_mem hyH (H.zpow_mem (centralBasisLift e i).2 (-a)), ?_⟩
      intro j hj
      rw [show (⟨y * (centralBasisLift e i : G) ^ (-a), _⟩ : H) =
        ⟨y, hyH⟩ * (centralBasisLift e i) ^ (-a) by rfl,
        map_mul, map_zpow, coordinates_basis_lift]
      change centralFactorCoordinates e ⟨y, hyH⟩ j *
        (centralBasisVector i j) ^ (-a) = 1
      by_cases hji : j = i
      · subst j
        rw [show centralFactorCoordinates e ⟨y, hyH⟩ i =
          Multiplicative.ofAdd a by exact (ofAdd_toAdd _).symm]
        rw [show centralBasisVector i i = Multiplicative.ofAdd 1 by
          simp [centralBasisVector], ← ofAdd_zsmul]
        simp
      · have hjlt : (j : ℕ) < (i : ℕ) := by omega
        rw [((central_coordinate_tail e i y).mp hy).choose_spec j hjlt]
        simp [centralBasisVector, Pi.mulSingle_eq_of_ne hji]
    have hremClosure :
        y * (centralBasisLift e i : G) ^ (-a) ∈
          Subgroup.closure
            (((centralCoordinateTail e ((i : ℕ) + 1) : Subgroup G) :
                Set G) ∪ {(centralBasisLift e i : G)}) :=
      Subgroup.subset_closure (Or.inl hremTail)
    have hxClosure :
        (centralBasisLift e i : G) ^ a ∈
          Subgroup.closure
            (((centralCoordinateTail e ((i : ℕ) + 1) : Subgroup G) :
                Set G) ∪ {(centralBasisLift e i : G)}) :=
      (Subgroup.closure
        (((centralCoordinateTail e ((i : ℕ) + 1) : Subgroup G) : Set G) ∪
          {(centralBasisLift e i : G)})).zpow_mem
        (Subgroup.subset_closure (Or.inr (Set.mem_singleton _))) a
    rw [show y = (y * (centralBasisLift e i : G) ^ (-a)) *
      (centralBasisLift e i : G) ^ a by group]
    exact (Subgroup.closure _).mul_mem hremClosure hxClosure
  · rw [Subgroup.closure_le]
    rintro y (hy | hy)
    · exact central_tail_succ e i hy
    · rw [Set.mem_singleton_iff.mp hy]
      exact basis_lift_tail e i

namespace ICSeries

/-- Refining a rank-`r` free-abelian central factor by its standard basis
extends an existing infinite-cyclic central series. -/
noncomputable def refineCentralFactor
    {K H : Subgroup G} (hK_normal : K.Normal) (hK_le_H : K ≤ H)
    (hcentral : ⁅H, (⊤ : Subgroup G)⁆ ≤ K)
    {r : ℕ}
    (e : H ⧸ K.subgroupOf H ≃* (Fin r → Multiplicative ℤ))
    (tail : ICSeries G K) :
    ICSeries G H := by
  letI : K.Normal := hK_normal
  have hbase :
      ICSeries G (centralCoordinateTail e r) := by
    simpa only [central_tail_length hK_le_H e] using tail
  have hseries :
      ICSeries G (centralCoordinateTail e 0) :=
    Nat.decreasingInduction
      (motive := fun k _ ↦
        ICSeries G (centralCoordinateTail e k))
      (fun k hk ih ↦
        ICSeries.step
          (central_tail_succ e k)
          (central_tail_normal hK_le_H hcentral e (k + 1))
          (central_factor_tail hK_le_H hcentral e k)
          (centralBasisLift e ⟨k, hk⟩)
          (basis_lift_tail e ⟨k, hk⟩)
          (union_basis_lift
            e ⟨k, hk⟩)
          (fun a ha ↦
            (lift_zpow_tail e ⟨k, hk⟩ a).mp ha)
          ih)
      hbase (Nat.zero_le r)
  simpa only [central_tail_zero e] using hseries

end ICSeries

/-- Canonical coordinates for a subgroup `H`, with all tails still recorded
as ambient subgroups of `G`. This relative form is the induction object for
constructing Hall canonical bases from infinite-cyclic central series. -/
structure RCBasis (G : Type u) [Group G]
    (H : Subgroup G) (n : ℕ) where
  generators : Fin n → G
  generators_mem : ∀ i, generators i ∈ H
  coord : H ≃ (Fin n → ℤ)
  symm_apply :
    ∀ x, (coord.symm x : G) = canonicalBasisProduct generators x
  generator_coord :
    ∀ i j, coord ⟨generators i, generators_mem i⟩ j =
      if i = j then 1 else 0
  tail : ℕ → Subgroup G
  tail_zero : tail 0 = H
  tail_length : tail n = ⊥
  tail_succ_le : ∀ k, tail (k + 1) ≤ tail k
  tail_normal : ∀ k, (tail k).Normal
  tail_central : ∀ k, ⁅tail k, (⊤ : Subgroup G)⁆ ≤ tail (k + 1)
  mem_tail_iff : ∀ {k} (_ : k ≤ n) {g : H},
    (g : G) ∈ tail k ↔
      ∀ i : Fin n, (i : ℕ) < k → coord g i = 0

namespace RCBasis

/-- Every relative tail lies below the starting subgroup. -/
lemma tail_le_start {H : Subgroup G} {n : ℕ}
    (b : RCBasis G H n) :
    ∀ k, b.tail k ≤ H := by
  intro k
  induction k with
  | zero =>
      rw [b.tail_zero]
  | succ k ih =>
      exact (b.tail_succ_le k).trans ih

/-- The zero coordinate tuple represents the identity. -/
lemma symm_zero {H : Subgroup G} {n : ℕ}
    (b : RCBasis G H n) :
    b.coord.symm 0 = 1 := by
  apply Subtype.ext
  rw [b.symm_apply]
  simp [canonicalBasisProduct, orderedZPow]

/-- The product map for one infinite-cyclic central-series step. -/
def cyclicStepProduct {H K : Subgroup G}
    (hK_le_H : K ≤ H) (x : G) (hx : x ∈ H) :
    ℤ × K → H :=
  fun ak ↦
    ⟨x ^ ak.1 * ak.2, H.mul_mem (H.zpow_mem hx ak.1) (hK_le_H ak.2.2)⟩

/-- Generation modulo `K`, together with the infinite-order condition,
makes the one-step product map bijective. -/
lemma cyclic_step_bijective {H K : Subgroup G}
    (hK_le_H : K ≤ H) (hK_normal : K.Normal)
    (x : G) (hx : x ∈ H)
    (hgenerate : H = Subgroup.closure ((K : Set G) ∪ {x}))
    (hinfinite : ∀ a : ℤ, x ^ a ∈ K → a = 0) :
    Function.Bijective (cyclicStepProduct hK_le_H x hx) := by
  letI : K.Normal := hK_normal
  have hHK :
      H = Subgroup.zpowers x ⊔ K := by
    rw [hgenerate, Subgroup.closure_union, Subgroup.closure_eq,
      ← Subgroup.zpowers_eq_closure, sup_comm]
  constructor
  · rintro ⟨a, k⟩ ⟨b, l⟩ h
    have hval :
        x ^ a * (k : G) = x ^ b * (l : G) :=
      congrArg Subtype.val h
    have hpow :
        x ^ (a - b) ∈ K := by
      have heq :
          x ^ (-b) * x ^ a = (l : G) * (k : G)⁻¹ := by
        calc
          x ^ (-b) * x ^ a =
              x ^ (-b) * (x ^ a * (k : G)) * (k : G)⁻¹ := by
                group
          _ = x ^ (-b) * (x ^ b * (l : G)) * (k : G)⁻¹ := by
                rw [hval]
          _ = (l : G) * (k : G)⁻¹ := by
                group
      rw [show a - b = -b + a by omega, zpow_add, heq]
      exact K.mul_mem l.2 (K.inv_mem k.2)
    have hab : a = b := by
      have := hinfinite (a - b) hpow
      omega
    subst b
    have hkl : k = l := by
      apply Subtype.ext
      exact mul_left_cancel hval
    subst l
    rfl
  · intro g
    have hg :
        (g : G) ∈ Subgroup.zpowers x ⊔ K := by
      rw [← hHK]
      exact g.2
    obtain ⟨y, hy, k, hk, hyk⟩ :=
      Subgroup.mem_sup_of_normal_right.mp hg
    obtain ⟨a, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    refine ⟨(a, ⟨k, hk⟩), ?_⟩
    exact Subtype.ext hyk

/-- The equivalence supplied by one infinite-cyclic central-series step. -/
noncomputable def cyclicStepEquiv {H K : Subgroup G}
    (hK_le_H : K ≤ H) (hK_normal : K.Normal)
    (x : G) (hx : x ∈ H)
    (hgenerate : H = Subgroup.closure ((K : Set G) ∪ {x}))
    (hinfinite : ∀ a : ℤ, x ^ a ∈ K → a = 0) :
    ℤ × K ≃ H :=
  Equiv.ofBijective (cyclicStepProduct hK_le_H x hx)
    (cyclic_step_bijective hK_le_H hK_normal x hx hgenerate hinfinite)

@[simp]
lemma coe_cyclic_step {H K : Subgroup G}
    (hK_le_H : K ≤ H) (hK_normal : K.Normal)
    (x : G) (hx : x ∈ H)
    (hgenerate : H = Subgroup.closure ((K : Set G) ∪ {x}))
    (hinfinite : ∀ a : ℤ, x ^ a ∈ K → a = 0)
    (a : ℤ) (k : K) :
    (cyclicStepEquiv hK_le_H hK_normal x hx hgenerate hinfinite (a, k) : G) =
      x ^ a * k :=
  rfl

/-- Coordinates formed by adjoining one infinite-cyclic head factor to an
existing relative canonical basis on the first tail. -/
noncomputable def consCoord {H K : Subgroup G} {n : ℕ}
    (b : RCBasis G K n)
    (hK_le_H : K ≤ H) (hK_normal : K.Normal)
    (x : G) (hx : x ∈ H)
    (hgenerate : H = Subgroup.closure ((K : Set G) ∪ {x}))
    (hinfinite : ∀ a : ℤ, x ^ a ∈ K → a = 0) :
    H ≃ (Fin (n + 1) → ℤ) := by
  let e : ℤ × K ≃ H :=
    cyclicStepEquiv hK_le_H hK_normal x hx hgenerate hinfinite
  exact
    { toFun := fun g ↦
        Fin.cons (e.symm g).1 (b.coord (e.symm g).2)
      invFun := fun z ↦
        e (z 0, b.coord.symm (Fin.tail z))
      left_inv := by
        intro g
        simp [e]
      right_inv := by
        intro z
        simp }

@[simp]
lemma cons_coord_symm {H K : Subgroup G} {n : ℕ}
    (b : RCBasis G K n)
    (hK_le_H : K ≤ H) (hK_normal : K.Normal)
    (x : G) (hx : x ∈ H)
    (hgenerate : H = Subgroup.closure ((K : Set G) ∪ {x}))
    (hinfinite : ∀ a : ℤ, x ^ a ∈ K → a = 0)
    (z : Fin (n + 1) → ℤ) :
    (consCoord b hK_le_H hK_normal x hx hgenerate hinfinite).symm z =
      cyclicStepEquiv hK_le_H hK_normal x hx hgenerate hinfinite
        (z 0, b.coord.symm (Fin.tail z)) :=
  rfl

/-- An element already in the first tail has initial coordinate zero and
its remaining coordinates are the old tail coordinates. -/
lemma cons_coord {H K : Subgroup G} {n : ℕ}
    (b : RCBasis G K n)
    (hK_le_H : K ≤ H) (hK_normal : K.Normal)
    (x : G) (hx : x ∈ H)
    (hgenerate : H = Subgroup.closure ((K : Set G) ∪ {x}))
    (hinfinite : ∀ a : ℤ, x ^ a ∈ K → a = 0)
    (g : H) (hg : (g : G) ∈ K) :
    consCoord b hK_le_H hK_normal x hx hgenerate hinfinite g =
      Fin.cons 0 (b.coord ⟨g, hg⟩) := by
  apply
    (consCoord b hK_le_H hK_normal x hx hgenerate hinfinite).symm.injective
  rw [Equiv.symm_apply_apply, cons_coord_symm]
  apply Subtype.ext
  simp

/-- The initial coordinate vanishes exactly on the first tail. -/
lemma cons_coord_zero {H K : Subgroup G} {n : ℕ}
    (b : RCBasis G K n)
    (hK_le_H : K ≤ H) (hK_normal : K.Normal)
    (x : G) (hx : x ∈ H)
    (hgenerate : H = Subgroup.closure ((K : Set G) ∪ {x}))
    (hinfinite : ∀ a : ℤ, x ^ a ∈ K → a = 0)
    (g : H) :
    consCoord b hK_le_H hK_normal x hx hgenerate hinfinite g 0 = 0 ↔
      (g : G) ∈ K := by
  constructor
  · intro hzero
    rw [← (consCoord b hK_le_H hK_normal x hx hgenerate hinfinite).symm_apply_apply g]
    rw [cons_coord_symm]
    simp [hzero]
  · intro hg
    rw [cons_coord b hK_le_H hK_normal x hx hgenerate
      hinfinite g hg]
    simp

/-- Adjoining one infinite-cyclic central factor extends a relative
canonical basis by one generator. -/
noncomputable def cons {H K : Subgroup G} {n : ℕ}
    (b : RCBasis G K n)
    (hH_normal : H.Normal)
    (hK_le_H : K ≤ H) (hK_normal : K.Normal)
    (hcentral : ⁅H, (⊤ : Subgroup G)⁆ ≤ K)
    (x : G) (hx : x ∈ H)
    (hgenerate : H = Subgroup.closure ((K : Set G) ∪ {x}))
    (hinfinite : ∀ a : ℤ, x ^ a ∈ K → a = 0) :
    RCBasis G H (n + 1) where
  generators := Fin.cases x b.generators
  generators_mem := by
    intro i
    refine Fin.cases hx (fun j ↦ ?_) i
    exact hK_le_H (b.generators_mem j)
  coord := consCoord b hK_le_H hK_normal x hx hgenerate hinfinite
  symm_apply := by
    intro z
    rw [show z = Fin.cons (z 0) (Fin.tail z) by
      exact (Fin.cons_self_tail z).symm]
    rw [cons_coord_symm, canonical_basis_cons]
    change x ^ z 0 * (b.coord.symm (Fin.tail z) : G) =
      x ^ z 0 * canonicalBasisProduct b.generators (Fin.tail z)
    rw [b.symm_apply]
  generator_coord := by
    intro i j
    cases i using Fin.cases with
    | zero =>
        have hcoord :
            consCoord b hK_le_H hK_normal x hx hgenerate hinfinite ⟨x, hx⟩ =
              Fin.cons 1 0 := by
          apply
            (consCoord b hK_le_H hK_normal x hx hgenerate
              hinfinite).symm.injective
          rw [Equiv.symm_apply_apply, cons_coord_symm]
          apply Subtype.ext
          simp [b.symm_zero]
        change
          consCoord b hK_le_H hK_normal x hx hgenerate hinfinite ⟨x, hx⟩ j =
            if 0 = j then 1 else 0
        rw [hcoord]
        cases j using Fin.cases with
        | zero => simp
        | succ j => simp [Ne.symm (Fin.succ_ne_zero j)]
    | succ i =>
        have hcoord :=
          cons_coord b hK_le_H hK_normal x hx hgenerate
            hinfinite
            ⟨b.generators i, hK_le_H (b.generators_mem i)⟩
            (b.generators_mem i)
        change
          consCoord b hK_le_H hK_normal x hx hgenerate hinfinite
              ⟨b.generators i, hK_le_H (b.generators_mem i)⟩ j =
            if i.succ = j then 1 else 0
        rw [hcoord]
        cases j using Fin.cases with
        | zero => simp
        | succ j =>
            simpa using b.generator_coord i j
  tail
    | 0 => H
    | k + 1 => b.tail k
  tail_zero := rfl
  tail_length := b.tail_length
  tail_succ_le := by
    intro k
    cases k with
    | zero =>
        simpa [b.tail_zero] using hK_le_H
    | succ k =>
        exact b.tail_succ_le k
  tail_normal := by
    intro k
    cases k with
    | zero => exact hH_normal
    | succ k => exact b.tail_normal k
  tail_central := by
    intro k
    cases k with
    | zero => simpa [b.tail_zero] using hcentral
    | succ k => exact b.tail_central k
  mem_tail_iff := by
    intro k hk g
    cases k with
    | zero =>
        simp
    | succ k =>
        have hkn : k ≤ n := by omega
        constructor
        · intro hg
          have hgK : (g : G) ∈ K :=
            b.tail_le_start k hg
          have hcoord :=
            cons_coord b hK_le_H hK_normal x hx hgenerate
              hinfinite g hgK
          have htail :=
            (b.mem_tail_iff hkn (g := ⟨g, hgK⟩)).mp hg
          intro i hi
          cases i using Fin.cases with
          | zero =>
              rw [hcoord]
              simp
          | succ i =>
              rw [hcoord]
              simp only [Fin.cons_succ]
              apply htail i
              simpa only [Fin.val_succ, Nat.add_lt_add_iff_right] using hi
        · intro hz
          have hzero :
              consCoord b hK_le_H hK_normal x hx hgenerate hinfinite g 0 = 0 :=
            hz 0 (by simp)
          have hgK :
              (g : G) ∈ K :=
            (cons_coord_zero b hK_le_H hK_normal x hx
              hgenerate hinfinite g).mp hzero
          apply (b.mem_tail_iff hkn (g := ⟨g, hgK⟩)).mpr
          intro i hi
          have hs := hz i.succ (by simp only [Fin.val_succ]; omega)
          rw [cons_coord b hK_le_H hK_normal x hx hgenerate
            hinfinite g hgK] at hs
          simpa using hs

/-- The trivial subgroup has the empty relative canonical basis. -/
noncomputable def bot :
    RCBasis G (⊥ : Subgroup G) 0 where
  generators := Fin.elim0
  generators_mem := fun i ↦ Fin.elim0 i
  coord := Equiv.ofUnique _ _
  symm_apply := by
    intro z
    have hbot :
        (((Equiv.ofUnique (⊥ : Subgroup G) (Fin 0 → ℤ)).symm z :
            (⊥ : Subgroup G)) : G) = 1 :=
      Subgroup.mem_bot.mp
        ((Equiv.ofUnique (⊥ : Subgroup G) (Fin 0 → ℤ)).symm z).2
    simpa [canonicalBasisProduct, orderedZPow] using hbot
  generator_coord := by
    intro i
    exact Fin.elim0 i
  tail := fun _ ↦ ⊥
  tail_zero := rfl
  tail_length := rfl
  tail_succ_le := fun _ ↦ le_rfl
  tail_normal := fun _ ↦ inferInstance
  tail_central := by simp
  mem_tail_iff := by
    intro k hk g
    have hkzero : k = 0 := Nat.eq_zero_of_le_zero hk
    subst k
    simp

/-- A relative basis starting at `G` itself is an ordinary Hall canonical
basis. -/
noncomputable def hallCanonicalBasis {n : ℕ}
    (b : RCBasis G (⊤ : Subgroup G) n) :
    HCBasis G n where
  generators := b.generators
  coord := Subgroup.topEquiv.symm.toEquiv.trans b.coord
  symm_apply := by
    intro z
    exact b.symm_apply z
  generator_coord := by
    intro i j
    exact b.generator_coord i j
  tail := b.tail
  tail_zero := b.tail_zero
  tail_length := b.tail_length
  tail_succ_le := b.tail_succ_le
  tail_normal := b.tail_normal
  tail_central := b.tail_central
  mem_tail_iff := by
    intro k hk g
    exact b.mem_tail_iff hk (g := ⟨g, Subgroup.mem_top g⟩)

end RCBasis

namespace ICSeries

/-- Refining consecutive upper-central factors from `Z₀ = 1` upward gives an
infinite-cyclic central series for every upper-central term. -/
noncomputable def upperSeries
    [Group.FG G] [Group.IsNilpotent G] [IsMulTorsionFree G] :
    ∀ n : ℕ, ICSeries G (Subgroup.upperCentralSeries G n)
  | 0 => by
      simpa only [Subgroup.upperCentralSeries_zero] using
        (ICSeries.bot :
          ICSeries G (⊥ : Subgroup G))
  | n + 1 => by
      exact refineCentralFactor
        (inferInstance : (Subgroup.upperCentralSeries G n).Normal)
        (Subgroup.upperCentralSeries_mono G (Nat.le_succ n))
        (upper_series_commutator n)
        (upperSeriesFactor (G := G) n)
        (upperSeries n)

/-- The refined upper central series reaches the whole group at its
nilpotency class. -/
noncomputable def fgTorsionNilpotent
    [Group.FG G] [Group.IsNilpotent G] [IsMulTorsionFree G] :
    ICSeries G (⊤ : Subgroup G) := by
  simpa only [Subgroup.upperCentralSeries_nilpotencyClass] using
    (upperSeries (G := G) (Group.nilpotencyClass G))

/-- An infinite-cyclic central series ending in `1` recursively supplies a
relative Hall canonical basis. -/
noncomputable def relativeBasis {H : Subgroup G}
    (hH_normal : H.Normal) (s : ICSeries G H) :
    Σ n : ℕ, RCBasis G H n := by
  induction s with
  | bot =>
      exact ⟨0, RCBasis.bot⟩
  | @step H K hK_le_H hK_normal hcentral x hx hgenerate hinfinite tail ih =>
      obtain ⟨n, b⟩ := ih hK_normal
      exact
        ⟨n + 1,
          b.cons hH_normal hK_le_H hK_normal hcentral x hx hgenerate
            hinfinite⟩

/-- A central series with infinite-cyclic factors from `G` to `1`
constructs an honest Hall canonical basis. -/
theorem hall_canonical_basis
    (s : ICSeries G (⊤ : Subgroup G)) :
    ∃ n : ℕ, Nonempty (HCBasis G n) := by
  obtain ⟨n, b⟩ :=
    s.relativeBasis (inferInstance : (⊤ : Subgroup G).Normal)
  exact ⟨n, ⟨b.hallCanonicalBasis⟩⟩

end ICSeries

/-- Every finitely generated torsion-free nilpotent group has a Hall
canonical basis. -/
theorem fg_torsion_nilpotent
    [Group.FG G] [Group.IsNilpotent G] [IsMulTorsionFree G] :
    ∃ n : ℕ, Nonempty (HCBasis G n) :=
  ICSeries.hall_canonical_basis
    (ICSeries.fgTorsionNilpotent (G := G))

/-- Embed an index for a suffix of a canonical basis back into the full
index set. -/
def suffixIndex {n : ℕ} (k : ℕ) (_ : k ≤ n) (j : Fin (n - k)) : Fin n :=
  ⟨k + j, by omega⟩

/-- Extend a suffix tuple by `k` initial zero coordinates. -/
def suffixTuple {n : ℕ} (k : ℕ) (_ : k ≤ n)
    (x : Fin (n - k) → ℤ) : Fin n → ℤ :=
  fun i ↦ if hi : k ≤ (i : ℕ) then x ⟨(i : ℕ) - k, by omega⟩ else 0

@[simp]
lemma suffix_tuple_index {n : ℕ} (k : ℕ) (hk : k ≤ n)
    (x : Fin (n - k) → ℤ) (j : Fin (n - k)) :
    suffixTuple k hk x (suffixIndex k hk j) = x j := by
  simp only [suffixTuple, suffixIndex]
  rw [dif_pos (by omega)]
  congr 1
  apply Fin.ext
  simp

/-- Canonical coordinates restricted to a recorded suffix tail. -/
def suffixCoordEquiv {n : ℕ} (b : HCBasis G n)
    (k : ℕ) (hk : k ≤ n) :
    b.tail k ≃ (Fin (n - k) → ℤ) where
  toFun g j := b.coord g (suffixIndex k hk j)
  invFun x := ⟨b.coord.symm (suffixTuple k hk x), by
    rw [b.mem_tail_iff hk]
    intro i hi
    rw [b.coord.apply_symm_apply]
    simp [suffixTuple, show ¬ k ≤ (i : ℕ) by omega]⟩
  left_inv g := by
    apply Subtype.ext
    apply b.coord.injective
    rw [b.coord.apply_symm_apply]
    funext i
    by_cases hi : (i : ℕ) < k
    · rw [suffixTuple, dif_neg (by omega)]
      exact ((b.mem_tail_iff hk).mp g.property i hi).symm
    · rw [suffixTuple, dif_pos (by omega)]
      change b.coord g (suffixIndex k hk ⟨(i : ℕ) - k, by omega⟩) =
        b.coord g i
      rw [show suffixIndex k hk ⟨(i : ℕ) - k, by omega⟩ = i by
        apply Fin.ext
        simp [suffixIndex]
        omega]
  right_inv x := by
    funext j
    simp [suffix_tuple_index]

/-- Extending a suffix tuple by zero coordinates does not alter its
ordered canonical product. -/
lemma canonical_suffix_tuple {n : ℕ} (u : Fin n → G)
    (k : ℕ) (hk : k ≤ n) (x : Fin (n - k) → ℤ) :
    canonicalBasisProduct u (suffixTuple k hk x) =
      canonicalBasisProduct (fun j ↦ u (suffixIndex k hk j)) x := by
  unfold canonicalBasisProduct orderedZPow
  rw [← List.ofFn_eq_map, ← List.ofFn_eq_map]
  rw [List.ofFn_congr (Nat.add_sub_of_le hk).symm]
  rw [show
      (fun i : Fin (k + (n - k)) ↦
          u (Fin.cast (Nat.add_sub_of_le hk) i) ^
            suffixTuple k hk x (Fin.cast (Nat.add_sub_of_le hk) i)) =
        Fin.append (fun _ : Fin k ↦ (1 : G))
          (fun j : Fin (n - k) ↦ u (suffixIndex k hk j) ^ x j) by
    funext i
    refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) i
    · simp [suffixTuple, show ¬ k ≤ (j : ℕ) by omega]
    · rw [show Fin.cast (Nat.add_sub_of_le hk) (Fin.natAdd k j) =
          suffixIndex k hk j by
        apply Fin.ext
        rfl]
      simp [suffix_tuple_index]]
  simp

/-- Removing any initial segment of generators produces the exact
canonical basis on the corresponding suffix tail. -/
noncomputable def suffixBasis {n : ℕ} (b : HCBasis G n)
    (k : ℕ) (hk : k ≤ n) :
    HCBasis (b.tail k) (n - k) where
  generators j :=
    ⟨b.generators (suffixIndex k hk j),
      b.generator_tail hk _ (by simp [suffixIndex])⟩
  coord := suffixCoordEquiv b k hk
  symm_apply x := by
    apply Subtype.ext
    change (b.coord.symm (suffixTuple k hk x) : G) =
      ((canonicalBasisProduct
        (fun j ↦ (⟨b.generators (suffixIndex k hk j), _⟩ : b.tail k)) x :
          b.tail k) : G)
    rw [b.symm_apply, canonical_suffix_tuple]
    symm
    unfold canonicalBasisProduct
    exact ordered_z_list (b.tail k).subtype
      (fun j ↦ (⟨b.generators (suffixIndex k hk j), _⟩ : b.tail k))
      (fun j ↦ b.generators (suffixIndex k hk j)) x (List.finRange (n - k))
      (fun _ _ ↦ rfl)
  generator_coord i j := by
    change b.coord (b.generators (suffixIndex k hk i)) (suffixIndex k hk j) =
      if i = j then 1 else 0
    rw [b.generator_coord]
    by_cases hij : i = j
    · subst j
      simp
    · rw [if_neg hij, if_neg]
      intro hsuffix
      apply hij
      apply Fin.ext
      simpa [suffixIndex] using congrArg Fin.val hsuffix
  tail j := (b.tail (k + j)).comap (b.tail k).subtype
  tail_zero := by
    ext g
    simp
  tail_length := by
    calc
      (b.tail (k + (n - k))).comap (b.tail k).subtype =
          (b.tail n).comap (b.tail k).subtype := by
            rw [Nat.add_sub_of_le hk]
      _ = (⊥ : Subgroup G).comap (b.tail k).subtype :=
        congrArg (fun H => H.comap (b.tail k).subtype) b.tail_length
      _ = ⊥ := by rw [MonoidHom.comap_bot, Subgroup.ker_subtype]
  tail_succ_le j := by
    apply Subgroup.comap_mono
    simpa [Nat.add_assoc] using b.tail_succ_le (k + j)
  tail_normal j :=
    (b.tail_normal (k + j)).comap (b.tail k).subtype
  tail_central j := by
    rw [Subgroup.commutator_le]
    intro x hx y _
    change ⁅(x : G), (y : G)⁆ ∈ b.tail (k + (j + 1))
    apply b.tail_central (k + j)
      (Subgroup.commutator_mem_commutator hx (Subgroup.mem_top y))
  mem_tail_iff {j} hj {g} := by
    change
      (g : G) ∈ b.tail (k + j) ↔
        ∀ i : Fin (n - k), (i : ℕ) < j →
          b.coord g (suffixIndex k hk i) = 0
    rw [b.mem_tail_iff (by omega)]
    constructor
    · intro h i hi
      apply h
      simp [suffixIndex]
      omega
    · intro h i hi
      by_cases hik : (i : ℕ) < k
      · exact (b.mem_tail_iff hk).mp g.property i hik
      · let q : Fin (n - k) := ⟨(i : ℕ) - k, by omega⟩
        have hq : (q : ℕ) < j := by
          dsimp [q]
          omega
        have hsuffix : suffixIndex k hk q = i := by
          apply Fin.ext
          simp [suffixIndex, q]
          omega
        have hh := h q hq
        rw [hsuffix] at hh
        exact hh

/-- The suffix basis as an ambient relative basis. This is convenient when
adjoining one selected earlier generator. -/
noncomputable def suffixRelativeBasis {n : ℕ} (b : HCBasis G n)
    (k : ℕ) (hk : k ≤ n) :
    RCBasis G (b.tail k) (n - k) where
  generators j := b.generators (suffixIndex k hk j)
  generators_mem j :=
    b.generator_tail hk _ (by simp [suffixIndex])
  coord := suffixCoordEquiv b k hk
  symm_apply x := by
    change b.coord.symm (suffixTuple k hk x) =
      canonicalBasisProduct (fun j ↦ b.generators (suffixIndex k hk j)) x
    rw [b.symm_apply, canonical_suffix_tuple]
  generator_coord i j := by
    change b.coord (b.generators (suffixIndex k hk i)) (suffixIndex k hk j) =
      if i = j then 1 else 0
    rw [b.generator_coord]
    by_cases hij : i = j
    · subst j
      simp
    · rw [if_neg hij, if_neg]
      intro hsuffix
      apply hij
      apply Fin.ext
      simpa [suffixIndex] using congrArg Fin.val hsuffix
  tail j := b.tail (k + j)
  tail_zero := by simp
  tail_length := by simpa [Nat.add_sub_of_le hk] using b.tail_length
  tail_succ_le j := by
    simpa [Nat.add_assoc] using b.tail_succ_le (k + j)
  tail_normal j := b.tail_normal (k + j)
  tail_central j := by
    simpa [Nat.add_assoc] using b.tail_central (k + j)
  mem_tail_iff {j} hj {g} := by
    change
      (g : G) ∈ b.tail (k + j) ↔
        ∀ i : Fin (n - k), (i : ℕ) < j →
          b.coord g (suffixIndex k hk i) = 0
    rw [b.mem_tail_iff (by omega)]
    constructor
    · intro h i hi
      apply h
      simp [suffixIndex]
      omega
    · intro h i hi
      by_cases hik : (i : ℕ) < k
      · exact (b.mem_tail_iff hk).mp g.property i hik
      · let q : Fin (n - k) := ⟨(i : ℕ) - k, by omega⟩
        have hq : (q : ℕ) < j := by
          dsimp [q]
          omega
        have hsuffix : suffixIndex k hk q = i := by
          apply Fin.ext
          simp [suffixIndex, q]
          omega
        have hh := h q hq
        rw [hsuffix] at hh
        exact hh

/-- Hall's selected subgroup generated by the first canonical generator
and one recorded suffix tail. -/
def headSuffixSubgroup {n : ℕ} (b : HCBasis G (n + 1))
    (k : ℕ) : Subgroup G :=
  Subgroup.closure (((b.tail k : Subgroup G) : Set G) ∪ {b.generators 0})

lemma tail_head_suffix {n : ℕ} (b : HCBasis G (n + 1))
    (k : ℕ) :
    b.tail k ≤ b.headSuffixSubgroup k := by
  intro g hg
  exact Subgroup.subset_closure (Or.inl hg)

lemma head_suffix_subgroup {n : ℕ}
    (b : HCBasis G (n + 1)) (k : ℕ) :
    b.generators 0 ∈ b.headSuffixSubgroup k :=
  Subgroup.subset_closure (Or.inr (Set.mem_singleton _))

lemma head_zpow_tail {n : ℕ}
    (b : HCBasis G (n + 1)) (k : ℕ)
    (hk : k ≤ n + 1) (hkpos : 0 < k) (a : ℤ)
    (ha : b.generators 0 ^ a ∈ b.tail k) :
    a = 0 := by
  have hcoord := (b.mem_tail_iff hk).mp ha (0 : Fin (n + 1)) (by
    simpa using hkpos)
  rw [b.coord_zpow_generator] at hcoord
  exact hcoord

/-- Coordinates on Hall's head-plus-suffix subgroup. -/
noncomputable def headSuffixCoord {n : ℕ}
    (b : HCBasis G (n + 1)) (k : ℕ)
    (hk : k ≤ n + 1) (hkpos : 0 < k) :
    b.headSuffixSubgroup k ≃ (Fin ((n + 1 - k) + 1) → ℤ) :=
  RCBasis.consCoord
    (b.suffixRelativeBasis k hk)
    (b.tail_head_suffix k)
    (b.tail_normal k)
    (b.generators 0)
    (b.head_suffix_subgroup k)
    rfl
    (b.head_zpow_tail k hk hkpos)

/-- The first factor of a head-plus-suffix subgroup is cyclic, so its
derived subgroup lies in the selected suffix tail. -/
lemma head_suffix_tail {n : ℕ}
    (b : HCBasis G (n + 1)) (k : ℕ)
    (hk : k ≤ n + 1) (hkpos : 0 < k) :
    ⁅b.headSuffixSubgroup k, b.headSuffixSubgroup k⁆ ≤ b.tail k := by
  let K : Subgroup G := b.tail k
  let H : Subgroup G := b.headSuffixSubgroup k
  letI : K.Normal := b.tail_normal k
  let e : ℤ × K ≃ H :=
    RCBasis.cyclicStepEquiv
      (b.tail_head_suffix k)
      (b.tail_normal k)
      (b.generators 0)
      (b.head_suffix_subgroup k)
      rfl
      (b.head_zpow_tail k hk hkpos)
  rw [Subgroup.commutator_le]
  intro x hx y hy
  let ex := e.symm ⟨x, hx⟩
  let ey := e.symm ⟨y, hy⟩
  have hxrepr : x = b.generators 0 ^ ex.1 * ex.2 := by
    have h := congrArg Subtype.val (e.apply_symm_apply ⟨x, hx⟩)
    exact h.symm
  have hyrepr : y = b.generators 0 ^ ey.1 * ey.2 := by
    have h := congrArg Subtype.val (e.apply_symm_apply ⟨y, hy⟩)
    exact h.symm
  apply (QuotientGroup.eq_one_iff ⁅x, y⁆).mp
  change (QuotientGroup.mk' K) ⁅x, y⁆ = 1
  rw [map_commutatorElement, hxrepr, hyrepr, map_mul, map_mul, map_zpow,
    map_zpow]
  have hex :
      (QuotientGroup.mk' K) (ex.2 : G) = 1 :=
    (QuotientGroup.eq_one_iff (ex.2 : G)).mpr ex.2.2
  have hey :
      (QuotientGroup.mk' K) (ey.2 : G) = 1 :=
    (QuotientGroup.eq_one_iff (ey.2 : G)).mpr ey.2.2
  rw [hex, hey]
  simp only [mul_one]
  rw [commutatorElement_eq_one_iff_mul_comm]
  exact
    (Commute.refl ((QuotientGroup.mk' K) (b.generators 0))).zpow_zpow _ _

/-- The canonical basis on Hall's subgroup
`⟨u₁, u_k, ..., u_n⟩`, retaining the original selected generators. -/
noncomputable def headSuffixBasis {n : ℕ}
    (b : HCBasis G (n + 1)) (k : ℕ)
    (hk : k ≤ n + 1) (hkpos : 0 < k) :
    HCBasis (b.headSuffixSubgroup k) ((n + 1 - k) + 1) where
  generators :=
    Fin.cases
      ⟨b.generators 0, b.head_suffix_subgroup k⟩
      (fun j ↦
        ⟨b.generators (suffixIndex k hk j),
          b.tail_head_suffix k
            (b.generator_tail hk _ (by simp [suffixIndex]))⟩)
  coord := b.headSuffixCoord k hk hkpos
  symm_apply := by
    intro z
    apply Subtype.ext
    rw [show z = Fin.cons (z 0) (Fin.tail z) by
      exact (Fin.cons_self_tail z).symm]
    unfold headSuffixCoord
    rw [RCBasis.cons_coord_symm,
      RCBasis.coe_cyclic_step,
      canonical_basis_cons]
    simp only [Fin.cons_zero, Fin.tail_cons, Fin.cases_zero, Fin.cases_succ]
    change
      b.generators 0 ^ z 0 *
          ((b.suffixCoordEquiv k hk).symm (Fin.tail z) : G) =
        b.generators 0 ^ z 0 *
          ((canonicalBasisProduct
            (fun j ↦
              (⟨b.generators (suffixIndex k hk j),
                b.tail_head_suffix k
                  (b.generator_tail hk _
                    (by simp [suffixIndex]))⟩ :
                b.headSuffixSubgroup k))
            (Fin.tail z) : b.headSuffixSubgroup k) : G)
    congr 1
    rw [show ((b.suffixCoordEquiv k hk).symm (Fin.tail z) : G) =
        canonicalBasisProduct
          (fun j ↦ b.generators (suffixIndex k hk j)) (Fin.tail z) by
      exact (b.suffixRelativeBasis k hk).symm_apply (Fin.tail z)]
    symm
    unfold canonicalBasisProduct
    exact ordered_z_list
      (b.headSuffixSubgroup k).subtype
      (fun j ↦
        (⟨b.generators (suffixIndex k hk j),
          b.tail_head_suffix k
            (b.generator_tail hk _ (by simp [suffixIndex]))⟩ :
          b.headSuffixSubgroup k))
      (fun j ↦ b.generators (suffixIndex k hk j))
      (Fin.tail z) (List.finRange (n + 1 - k)) (fun _ _ ↦ rfl)
  generator_coord := by
    intro i j
    cases i using Fin.cases with
    | zero =>
        have hcoord :
            b.headSuffixCoord k hk hkpos
                ⟨b.generators 0, b.head_suffix_subgroup k⟩ =
              Fin.cons 1 0 := by
          apply (b.headSuffixCoord k hk hkpos).symm.injective
          unfold headSuffixCoord
          rw [Equiv.symm_apply_apply,
            RCBasis.cons_coord_symm]
          apply Subtype.ext
          simp [RCBasis.symm_zero]
        change
          b.headSuffixCoord k hk hkpos
              ⟨b.generators 0, b.head_suffix_subgroup k⟩ j =
            if 0 = j then 1 else 0
        rw [hcoord]
        cases j using Fin.cases with
        | zero => simp
        | succ j => simp [Ne.symm (Fin.succ_ne_zero j)]
    | succ i =>
        have hcoord :=
          RCBasis.cons_coord
            (b.suffixRelativeBasis k hk)
            (b.tail_head_suffix k)
            (b.tail_normal k)
            (b.generators 0)
            (b.head_suffix_subgroup k)
            rfl
            (b.head_zpow_tail k hk hkpos)
            ⟨b.generators (suffixIndex k hk i),
              b.tail_head_suffix k
                (b.generator_tail hk _
                  (by simp [suffixIndex]))⟩
            (b.generator_tail hk _ (by simp [suffixIndex]))
        change
          b.headSuffixCoord k hk hkpos
              ⟨b.generators (suffixIndex k hk i),
                b.tail_head_suffix k
                  (b.generator_tail hk _
                    (by simp [suffixIndex]))⟩ j =
            if i.succ = j then 1 else 0
        unfold headSuffixCoord
        rw [hcoord]
        cases j using Fin.cases with
        | zero => simp
        | succ j =>
            simpa using (b.suffixRelativeBasis k hk).generator_coord i j
  tail
    | 0 => ⊤
    | j + 1 => (b.tail (k + j)).comap (b.headSuffixSubgroup k).subtype
  tail_zero := rfl
  tail_length := by
    calc
      (b.tail (k + (n + 1 - k))).comap (b.headSuffixSubgroup k).subtype =
          (b.tail (n + 1)).comap (b.headSuffixSubgroup k).subtype := by
            rw [Nat.add_sub_of_le hk]
      _ = (⊥ : Subgroup G).comap (b.headSuffixSubgroup k).subtype :=
        congrArg
          (fun H => H.comap (b.headSuffixSubgroup k).subtype) b.tail_length
      _ = ⊥ := by rw [MonoidHom.comap_bot, Subgroup.ker_subtype]
  tail_succ_le := by
    intro j
    cases j with
    | zero => exact le_top
    | succ j =>
        apply Subgroup.comap_mono
        simpa [Nat.add_assoc] using b.tail_succ_le (k + j)
  tail_normal := by
    intro j
    cases j with
    | zero => exact inferInstance
    | succ j =>
        exact (b.tail_normal (k + j)).comap (b.headSuffixSubgroup k).subtype
  tail_central := by
    intro j
    rw [Subgroup.commutator_le]
    cases j with
    | zero =>
        intro x _ y _
        change ⁅(x : G), (y : G)⁆ ∈ b.tail k
        apply b.head_suffix_tail k hk hkpos
        exact Subgroup.commutator_mem_commutator x.property y.property
    | succ j =>
        intro x hx y _
        change ⁅(x : G), (y : G)⁆ ∈ b.tail (k + (j + 1))
        apply b.tail_central (k + j)
        exact
          Subgroup.commutator_mem_commutator hx (Subgroup.mem_top (y : G))
  mem_tail_iff := by
    intro j hj g
    cases j with
    | zero => simp
    | succ j =>
        have hjtail : j ≤ n + 1 - k := by omega
        let r := b.suffixRelativeBasis k hk
        change
          (g : G) ∈ b.tail (k + j) ↔
            ∀ i : Fin ((n + 1 - k) + 1), (i : ℕ) < j + 1 →
              b.headSuffixCoord k hk hkpos g i = 0
        constructor
        · intro hg
          have hgK : (g : G) ∈ b.tail k :=
            r.tail_le_start j hg
          have hcoord :=
            RCBasis.cons_coord
              r
              (b.tail_head_suffix k)
              (b.tail_normal k)
              (b.generators 0)
              (b.head_suffix_subgroup k)
              rfl
              (b.head_zpow_tail k hk hkpos)
              g hgK
          have htail := (r.mem_tail_iff hjtail (g := ⟨g, hgK⟩)).mp hg
          intro i hi
          cases i using Fin.cases with
          | zero =>
              unfold headSuffixCoord
              change
                (r.consCoord
                  (b.tail_head_suffix k)
                  (b.tail_normal k)
                  (b.generators 0)
                  (b.head_suffix_subgroup k)
                  rfl
                  (b.head_zpow_tail k hk hkpos)) g 0 = 0
              rw [hcoord]
              simp
          | succ i =>
              unfold headSuffixCoord
              change
                (r.consCoord
                  (b.tail_head_suffix k)
                  (b.tail_normal k)
                  (b.generators 0)
                  (b.head_suffix_subgroup k)
                  rfl
                  (b.head_zpow_tail k hk hkpos)) g i.succ = 0
              rw [hcoord]
              apply htail i
              simpa only [Fin.val_succ] using Nat.lt_of_succ_lt_succ hi
        · intro h
          have hzero := h (0 : Fin ((n + 1 - k) + 1)) (by simp)
          unfold headSuffixCoord at hzero
          have hgK : (g : G) ∈ b.tail k := by
            apply
              (RCBasis.cons_coord_zero
                (b.suffixRelativeBasis k hk)
                (b.tail_head_suffix k)
                (b.tail_normal k)
                (b.generators 0)
                (b.head_suffix_subgroup k)
                rfl
                (b.head_zpow_tail k hk hkpos)
                g).mp
            exact hzero
          have hcoord :=
            RCBasis.cons_coord
              r
              (b.tail_head_suffix k)
              (b.tail_normal k)
              (b.generators 0)
              (b.head_suffix_subgroup k)
              rfl
              (b.head_zpow_tail k hk hkpos)
              g hgK
          apply (r.mem_tail_iff hjtail (g := ⟨g, hgK⟩)).mpr
          intro i hi
          have hs := h i.succ (by
            simp only [Fin.val_succ]
            omega)
          unfold headSuffixCoord at hs
          change
            (r.consCoord
              (b.tail_head_suffix k)
              (b.tail_normal k)
              (b.generators 0)
              (b.head_suffix_subgroup k)
              rfl
              (b.head_zpow_tail k hk hkpos)) g i.succ = 0 at hs
          rw [hcoord] at hs
          exact hs

/-- Removing the first generator and passing to `G₁` produces the shifted
canonical basis used by Hall's induction. -/
noncomputable def tailBasis {n : ℕ} (b : HCBasis G (n + 1)) :
    HCBasis (b.tail 1) n where
  generators i := ⟨b.generators i.succ, b.generator_succ_tail i⟩
  coord := b.tailCoordEquiv
  symm_apply x := by
    apply Subtype.ext
    change b.coord.symm (Fin.cons 0 x) =
      ((canonicalBasisProduct
        (fun i => (⟨b.generators i.succ,
          b.generator_succ_tail i⟩ : b.tail 1)) x : b.tail 1) : G)
    rw [b.symm_apply, canonical_basis_cons]
    simp [canonicalBasisProduct, orderedZPow, Function.comp_def]
  generator_coord i j := by
    change b.coord (b.generators i.succ) j.succ =
      if i = j then 1 else 0
    rw [b.generator_coord]
    simp only [Fin.succ_inj]
  tail k := (b.tail (k + 1)).comap (b.tail 1).subtype
  tail_zero := by
    ext g
    simp
  tail_length := by
    calc
      (b.tail (n + 1)).comap (b.tail 1).subtype =
          (⊥ : Subgroup G).comap (b.tail 1).subtype :=
        congrArg (fun H => H.comap (b.tail 1).subtype) b.tail_length
      _ = ⊥ := by rw [MonoidHom.comap_bot, Subgroup.ker_subtype]
  tail_succ_le k := by
    apply Subgroup.comap_mono
    exact b.tail_succ_le (k + 1)
  tail_normal k :=
    (b.tail_normal (k + 1)).comap (b.tail 1).subtype
  tail_central k := by
    rw [Subgroup.commutator_le]
    intro x hx y _
    change ⁅(x : G), (y : G)⁆ ∈ b.tail (k + 1 + 1)
    exact b.tail_central (k + 1)
      (Subgroup.commutator_mem_commutator hx (Subgroup.mem_top y))
  mem_tail_iff {k} _ {g} := by
    change
      (g : G) ∈ b.tail (k + 1) ↔
        ∀ i : Fin n, (i : ℕ) < k → b.coord g i.succ = 0
    rw [b.mem_tail_iff (by omega)]
    constructor
    · intro h i hi
      exact h i.succ (by simp only [Fin.val_succ]; omega)
    · intro h i hi
      cases i using Fin.cases with
      | zero =>
        exact
          (b.mem_tail_iff (by omega)).mp g.property
            (0 : Fin (n + 1)) (by simp)
      | succ j =>
        apply h j
        have hj : (j : ℕ) + 1 < k + 1 := by
          simpa only [Fin.val_succ] using hi
        omega

/-- An element of the first tail has a zero head coordinate, followed by
its coordinates in the shifted tail basis. -/
lemma coord_coe_cons {n : ℕ}
    (b : HCBasis G (n + 1)) (g : b.tail 1) :
    b.coord (g : G) = Fin.cons 0 (b.tailBasis.coord g) := by
  funext i
  cases i using Fin.cases with
  | zero =>
      exact
        (b.mem_tail_iff (by omega)).mp g.property
          (0 : Fin (n + 1)) (by simp)
  | succ i => rfl

/-- The coordinates of a power of the first canonical generator have only
their initial entry nonzero. -/
lemma zpow_generator_zero {n : ℕ}
    (b : HCBasis G (n + 1)) (a : ℤ) :
    b.coord (b.generators 0 ^ a) = Fin.cons a 0 := by
  rw [← b.coord.apply_symm_apply (Fin.cons a 0)]
  congr 1
  rw [b.symm_apply, canonical_basis_cons]
  simp [canonicalBasisProduct, orderedZPow]

/-- Every canonical expression splits into its first generator power and
an element of the first tail subgroup. -/
lemma symm_head_tail {n : ℕ}
    (b : HCBasis G (n + 1)) (x : Fin (n + 1) → ℤ) :
    b.coord.symm x =
      b.generators 0 ^ x 0 * (b.tailCoordEquiv.symm (Fin.tail x) : G) := by
  rw [show x = Fin.cons (x 0) (Fin.tail x) by
    exact (Fin.cons_self_tail x).symm]
  rw [b.symm_apply, canonical_basis_cons]
  congr 1
  change canonicalBasisProduct (fun i => b.generators i.succ) (Fin.tail x) =
    b.coord.symm (Fin.cons 0 (Fin.tail x))
  rw [b.symm_apply, canonical_basis_cons]
  simp

/-- The first canonical parameter is additive under multiplication. -/
lemma coord_mul_zero {n : ℕ} (b : HCBasis G (n + 1))
    (x y : Fin (n + 1) → ℤ) :
    b.coord (b.coord.symm x * b.coord.symm y) 0 = x 0 + y 0 := by
  let u := b.generators 0
  let kx : b.tail 1 := b.tailCoordEquiv.symm (Fin.tail x)
  let ky : b.tail 1 := b.tailCoordEquiv.symm (Fin.tail y)
  let k : G := u ^ (-y 0) * kx * u ^ y 0 * ky
  have hk : k ∈ b.tail 1 := by
    apply (b.tail 1).mul_mem
    · simpa [zpow_neg] using
        (b.tail_normal 1).conj_mem (kx : G) kx.property (u ^ (-y 0))
    · exact ky.property
  have hxy :
      b.coord.symm x * b.coord.symm y =
        u ^ (x 0 + y 0) * k := by
    rw [b.symm_head_tail, b.symm_head_tail]
    dsimp only [u, kx, ky, k]
    rw [zpow_add]
    group
  let z := b.coord (b.coord.symm x * b.coord.symm y)
  let kz : b.tail 1 := b.tailCoordEquiv.symm (Fin.tail z)
  have hz :
      b.coord.symm x * b.coord.symm y =
        u ^ z 0 * kz := by
    rw [← b.coord.symm_apply_apply
      (b.coord.symm x * b.coord.symm y)]
    exact b.symm_head_tail z
  have hpow : u ^ (z 0 - (x 0 + y 0)) ∈ b.tail 1 := by
    rw [show z 0 - (x 0 + y 0) = -(x 0 + y 0) + z 0 by omega,
      zpow_add]
    have heq :
        u ^ (-(x 0 + y 0)) * u ^ z 0 =
          k * (kz : G)⁻¹ := by
      have heq0 :
          u ^ z 0 * (kz : G) = u ^ (x 0 + y 0) * k :=
        hz.symm.trans hxy
      calc
        u ^ (-(x 0 + y 0)) * u ^ z 0 =
            u ^ (-(x 0 + y 0)) *
              (u ^ z 0 * (kz : G)) * (kz : G)⁻¹ := by group
        _ = u ^ (-(x 0 + y 0)) *
              (u ^ (x 0 + y 0) * k) * (kz : G)⁻¹ := by rw [heq0]
        _ = k * (kz : G)⁻¹ := by group
    rw [heq]
    exact (b.tail 1).mul_mem hk ((b.tail 1).inv_mem kz.property)
  have hzero :=
    (b.mem_tail_iff (by omega)).mp hpow (0 : Fin (n + 1)) (by simp)
  rw [b.zpow_generator_zero] at hzero
  have hdiff : z 0 - (x 0 + y 0) = 0 := by
    simpa using hzero
  change z 0 = x 0 + y 0
  omega

/-- The first canonical parameter of the identity is zero. -/
lemma coord_one_zero {n : ℕ} (b : HCBasis G (n + 1)) :
    b.coord 1 0 = 0 := by
  have h := congrFun (b.zpow_generator_zero 0) (0 : Fin (n + 1))
  simpa using h

/-- Inversion negates the first canonical parameter. -/
lemma coord_inv_zero {n : ℕ} (b : HCBasis G (n + 1))
    (x : Fin (n + 1) → ℤ) :
    b.coord (b.coord.symm x)⁻¹ 0 = -x 0 := by
  have h := b.coord_mul_zero x (b.coord (b.coord.symm x)⁻¹)
  rw [b.coord.symm_apply_apply] at h
  simp [b.coord_one_zero] at h
  omega

/-- Natural powers multiply the first canonical parameter. -/
lemma coord_npow_zero {n m : ℕ} (b : HCBasis G (n + 1))
    (x : Fin (n + 1) → ℤ) :
    b.coord ((b.coord.symm x) ^ m) 0 = (m : ℤ) * x 0 := by
  induction m with
  | zero =>
      simp [b.coord_one_zero]
  | succ m ih =>
      rw [pow_succ]
      have h := b.coord_mul_zero
        (b.coord ((b.coord.symm x) ^ m)) x
      rw [b.coord.symm_apply_apply, ih] at h
      simpa [Nat.cast_succ, add_mul] using h

/-- Integer powers multiply the first canonical parameter. -/
lemma coord_zpow_zero {n : ℕ} (b : HCBasis G (n + 1))
    (x : Fin (n + 1) → ℤ) (a : ℤ) :
    b.coord ((b.coord.symm x) ^ a) 0 = a * x 0 := by
  cases a with
  | ofNat m =>
      simpa using b.coord_npow_zero (m := m) x
  | negSucc m =>
      rw [zpow_negSucc]
      have h := b.coord_inv_zero
        (b.coord ((b.coord.symm x) ^ (m + 1)))
      rw [b.coord.symm_apply_apply, b.coord_npow_zero (m := m + 1)] at h
      simpa [Int.negSucc_eq, add_mul] using h

/-- Two elements congruent modulo `G₁` have the same first canonical
parameter. -/
lemma coord_div_tail {n : ℕ}
    (b : HCBasis G (n + 1)) {x y : G}
    (hxy : x / y ∈ b.tail 1) :
    b.coord x 0 = b.coord y 0 := by
  have hmul := b.coord_mul_zero (b.coord x) (b.coord y⁻¹)
  rw [b.coord.symm_apply_apply, b.coord.symm_apply_apply] at hmul
  have hinv := b.coord_inv_zero (b.coord y)
  rw [b.coord.symm_apply_apply] at hinv
  rw [hinv] at hmul
  have hzero :=
    (b.mem_tail_iff (by omega)).mp hxy (0 : Fin (n + 1)) (by simp)
  rw [div_eq_mul_inv, hmul] at hzero
  omega

/-- Conjugating an element of `G₁` by a power of the first canonical
generator remains in `G₁`. -/
def conjugateTail {n : ℕ} (b : HCBasis G (n + 1))
    (a : ℤ) (k : b.tail 1) : b.tail 1 :=
  ⟨b.generators 0 ^ (-a) * k * b.generators 0 ^ a, by
    simpa [zpow_neg] using
      (b.tail_normal 1).conj_mem (k : G) k.property
        (b.generators 0 ^ (-a))⟩

@[simp]
lemma coe_conjugateTail {n : ℕ} (b : HCBasis G (n + 1))
    (a : ℤ) (k : b.tail 1) :
    (b.conjugateTail a k : G) =
      b.generators 0 ^ (-a) * k * b.generators 0 ^ a :=
  rfl

/-- Conjugating an element of `G₁` changes it only by an element of
`G₂`. -/
lemma conjugate_div_two {n : ℕ}
    (b : HCBasis G (n + 2)) (a : ℤ) (k : b.tail 1) :
    (b.conjugateTail a k : G) / k ∈ b.tail 2 := by
  have hc :
      hallCommutator (k : G) (b.generators 0 ^ a) ∈ b.tail 2 := by
    apply b.tail_central 1
    exact hall_commutator k.property (Subgroup.mem_top _)
  have hconj :
      (k : G) * hallCommutator (k : G) (b.generators 0 ^ a) * (k : G)⁻¹ ∈
        b.tail 2 :=
    (b.tail_normal 2).conj_mem _ hc (k : G)
  rw [div_eq_mul_inv, b.coe_conjugateTail]
  rw [zpow_neg]
  change
    hallConjugate (k : G) (b.generators 0 ^ a) * (k : G)⁻¹ ∈ b.tail 2
  rw [hall_conjugate_commutator]
  exact hconj

/-- Conjugating the first generator by a later one places it in Hall's
smaller head-plus-suffix subgroup. -/
lemma conjugated_head_suffix {n : ℕ}
    (b : HCBasis G (n + 1)) (i : Fin n) :
    b.generators i.succ * b.generators 0 * (b.generators i.succ)⁻¹ ∈
      b.headSuffixSubgroup ((i : ℕ) + 2) := by
  have hv :
      b.generators i.succ ∈ b.tail ((i : ℕ) + 1) :=
    b.generator_tail (by omega) i.succ (by simp)
  have hc :
      ⁅b.generators i.succ, b.generators 0⁆ ∈ b.tail ((i : ℕ) + 2) := by
    apply b.tail_central ((i : ℕ) + 1)
    exact Subgroup.commutator_mem_commutator hv (Subgroup.mem_top _)
  rw [show b.generators i.succ * b.generators 0 *
      (b.generators i.succ)⁻¹ =
        ⁅b.generators i.succ, b.generators 0⁆ * b.generators 0 by
    simp [commutatorElement_def, mul_assoc]]
  exact (b.headSuffixSubgroup ((i : ℕ) + 2)).mul_mem
    (b.tail_head_suffix ((i : ℕ) + 2) hc)
    (b.head_suffix_subgroup ((i : ℕ) + 2))

/-- Conjugating a later canonical generator by a power of the first one
changes it only in the following recorded tail. -/
lemma conjugate_div_succ {n : ℕ}
    (b : HCBasis G (n + 1)) (i : Fin n) (a : ℤ) :
    b.generators 0 ^ (-a) * b.generators i.succ *
          b.generators 0 ^ a / b.generators i.succ ∈
      b.tail ((i : ℕ) + 2) := by
  have hv :
      b.generators i.succ ∈ b.tail ((i : ℕ) + 1) :=
    b.generator_tail (by omega) i.succ (by simp)
  have hc :
      hallCommutator (b.generators i.succ) (b.generators 0 ^ a) ∈
        b.tail ((i : ℕ) + 2) := by
    apply b.tail_central ((i : ℕ) + 1)
    exact hall_commutator hv (Subgroup.mem_top _)
  have hconj :
      b.generators i.succ *
            hallCommutator (b.generators i.succ) (b.generators 0 ^ a) *
            (b.generators i.succ)⁻¹ ∈
        b.tail ((i : ℕ) + 2) :=
    (b.tail_normal ((i : ℕ) + 2)).conj_mem _
      hc (b.generators i.succ)
  rw [div_eq_mul_inv, zpow_neg]
  change
    hallConjugate (b.generators i.succ) (b.generators 0 ^ a) *
        (b.generators i.succ)⁻¹ ∈
      b.tail ((i : ℕ) + 2)
  rw [hall_conjugate_commutator]
  exact hconj

/-- The conjugate of a later generator factors through a power inside
Hall's smaller head-plus-suffix subgroup. -/
lemma conjugate_generator_eq {n : ℕ}
    (b : HCBasis G (n + 1)) (i : Fin n) (a : ℤ) :
    b.generators 0 ^ (-a) * b.generators i.succ * b.generators 0 ^ a =
      (b.generators 0 ^ (-a) *
        (b.generators i.succ * b.generators 0 *
          (b.generators i.succ)⁻¹) ^ a) *
        b.generators i.succ := by
  rw [conj_zpow]
  group

/-- The correction term relating a conjugated later generator to that
generator itself, regarded as an element of the first tail. -/
noncomputable def conjugateGeneratorCorrection {n : ℕ}
    (b : HCBasis G (n + 1)) (i : Fin n) (a : ℤ) :
    b.tail 1 :=
  ⟨b.generators 0 ^ (-a) * b.generators i.succ *
      b.generators 0 ^ a / b.generators i.succ, by
    have hv : b.generators i.succ ∈ b.tail 1 :=
      b.generator_tail (by omega) i.succ (by simp)
    rw [div_eq_mul_inv]
    apply (b.tail 1).mul_mem
    · simpa [zpow_neg] using
        (b.tail_normal 1).conj_mem (b.generators i.succ) hv
          (b.generators 0 ^ (-a))
    · exact (b.tail 1).inv_mem hv⟩

/-- The same correction term factored inside Hall's smaller
head-plus-suffix subgroup. -/
noncomputable def conjugateHeadSuffix {n : ℕ}
    (b : HCBasis G (n + 1)) (i : Fin n) (a : ℤ) :
    b.headSuffixSubgroup ((i : ℕ) + 2) :=
  ⟨b.generators 0 ^ (-a) *
      (b.generators i.succ * b.generators 0 *
        (b.generators i.succ)⁻¹) ^ a,
    (b.headSuffixSubgroup ((i : ℕ) + 2)).mul_mem
      ((b.headSuffixSubgroup ((i : ℕ) + 2)).zpow_mem
        (b.head_suffix_subgroup ((i : ℕ) + 2)) (-a))
      ((b.headSuffixSubgroup ((i : ℕ) + 2)).zpow_mem
        (b.conjugated_head_suffix i) a)⟩

@[simp]
lemma coe_head_suffix {n : ℕ}
    (b : HCBasis G (n + 1)) (i : Fin n) (a : ℤ) :
    (b.conjugateHeadSuffix i a : G) =
      b.conjugateGeneratorCorrection i a := by
  simp only [conjugateHeadSuffix,
    conjugateGeneratorCorrection, Subgroup.coe_mk]
  rw [conj_zpow]
  simp [div_eq_mul_inv, mul_assoc]

/-- Beyond its head coordinate, the head-plus-suffix coordinate system is
the original suffix coordinate system. -/
lemma head_suffix_succ {n : ℕ}
    (b : HCBasis G (n + 1)) (k : ℕ)
    (hk : k ≤ n + 1) (hkpos : 0 < k)
    (g : b.headSuffixSubgroup k) (hg : (g : G) ∈ b.tail k)
    (q : Fin (n + 1 - k)) :
    b.headSuffixCoord k hk hkpos g q.succ =
      b.coord g (suffixIndex k hk q) := by
  have hcoord :=
    RCBasis.cons_coord
      (b.suffixRelativeBasis k hk)
      (b.tail_head_suffix k)
      (b.tail_normal k)
      (b.generators 0)
      (b.head_suffix_subgroup k)
      rfl
      (b.head_zpow_tail k hk hkpos)
      g hg
  have h := congrFun hcoord q.succ
  simpa [headSuffixCoord, suffixRelativeBasis, suffixCoordEquiv] using h

/-- Early tail coordinates of a conjugation correction vanish. -/
lemma tail_coord_conjugate {n : ℕ}
    (b : HCBasis G (n + 1)) (i j : Fin n)
    (hj : (j : ℕ) < (i : ℕ) + 1) (a : ℤ) :
    (b.tailBasis).coord (b.conjugateGeneratorCorrection i a) j = 0 := by
  change b.coord (b.conjugateGeneratorCorrection i a : G) j.succ = 0
  apply (b.mem_tail_iff (by omega)).mp
      (b.conjugate_div_succ i a) j.succ
  simp only [Fin.val_succ]
  omega

/-- Remaining tail coordinates of a correction are coordinates in Hall's
smaller head-plus-suffix basis. -/
lemma conjugate_head_suffix {n : ℕ}
    (b : HCBasis G (n + 1)) (i j : Fin n)
    (hj : (i : ℕ) + 1 ≤ (j : ℕ)) (a : ℤ) :
    (b.tailBasis).coord (b.conjugateGeneratorCorrection i a) j =
      (b.headSuffixBasis ((i : ℕ) + 2) (by omega) (by omega)).coord
        (b.conjugateHeadSuffix i a)
        ⟨(j : ℕ) - ((i : ℕ) + 1) + 1, by omega⟩ := by
  change b.coord (b.conjugateGeneratorCorrection i a : G) j.succ = _
  rw [← b.coe_head_suffix]
  change b.coord (b.conjugateHeadSuffix i a : G) j.succ =
    b.headSuffixCoord ((i : ℕ) + 2) (by omega) (by omega)
      (b.conjugateHeadSuffix i a)
      ⟨(j : ℕ) - ((i : ℕ) + 1) + 1, by omega⟩
  let q : Fin (n + 1 - ((i : ℕ) + 2)) :=
    ⟨(j : ℕ) - ((i : ℕ) + 1), by omega⟩
  rw [show (⟨(j : ℕ) - ((i : ℕ) + 1) + 1, by omega⟩ :
      Fin ((n + 1 - ((i : ℕ) + 2)) + 1)) = q.succ by
    apply Fin.ext
    simp [q]]
  rw [b.head_suffix_succ
    ((i : ℕ) + 2) (by omega) (by omega)
    (b.conjugateHeadSuffix i a)
    (by
      rw [b.coe_head_suffix]
      exact b.conjugate_div_succ i a)
    q]
  rw [show suffixIndex ((i : ℕ) + 2) (by omega) q = j.succ by
    apply Fin.ext
    simp [suffixIndex, q]
    omega]

/-- A conjugated later generator, regarded as an element of the first
tail. -/
noncomputable def conjugateGeneratorTail {n : ℕ}
    (b : HCBasis G (n + 1)) (i : Fin n) (a : ℤ) :
    b.tail 1 :=
  ⟨b.generators 0 ^ (-a) * b.generators i.succ * b.generators 0 ^ a, by
    have hv : b.generators i.succ ∈ b.tail 1 :=
      b.generator_tail (by omega) i.succ (by simp)
    simpa [zpow_neg] using
      (b.tail_normal 1).conj_mem (b.generators i.succ) hv
        (b.generators 0 ^ (-a))⟩

lemma conjugate_generator_tail {n : ℕ}
    (b : HCBasis G (n + 1)) (i : Fin n) (a : ℤ) :
    b.conjugateGeneratorTail i a =
      b.conjugateGeneratorCorrection i a *
        ⟨b.generators i.succ,
          b.generator_tail (by omega) i.succ (by simp)⟩ := by
  apply Subtype.ext
  simp [conjugateGeneratorTail, conjugateGeneratorCorrection,
    div_eq_mul_inv, mul_assoc]

/-- Conjugation by a head-generator power restricts to an endomorphism of
the first tail. -/
def conjugateTailHom {n : ℕ} (b : HCBasis G (n + 1))
    (a : ℤ) : b.tail 1 →* b.tail 1 where
  toFun := b.conjugateTail a
  map_one' := by
    apply Subtype.ext
    simp [conjugateTail]
  map_mul' x y := by
    apply Subtype.ext
    simp [conjugateTail, mul_assoc]

@[simp]
lemma conjugate_tail_hom {n : ℕ} (b : HCBasis G (n + 1))
    (a : ℤ) (x : b.tail 1) :
    b.conjugateTailHom a x = b.conjugateTail a x :=
  rfl

@[simp]
lemma conjugate_tail_generator {n : ℕ}
    (b : HCBasis G (n + 1)) (a : ℤ) (i : Fin n) :
    b.conjugateTailHom a
        ⟨b.generators i.succ,
          b.generator_tail (by omega) i.succ (by simp)⟩ =
      b.conjugateGeneratorTail i a :=
  rfl

/-- The ordered product of individually conjugated later-generator
powers. -/
noncomputable def conjugatedGeneratorProduct {n : ℕ}
    (b : HCBasis G (n + 1)) (l : List (Fin n))
    (z : Option (Fin n) → ℤ) : b.tail 1 :=
  orderedZPow
    (fun i ↦ b.conjugateGeneratorTail i (z none))
    (fun i ↦ z (some i)) l

lemma conjugate_tail_conjugated {n : ℕ}
    (b : HCBasis G (n + 1)) (z : Option (Fin n) → ℤ) :
    b.conjugateTail (z none)
        ((b.tailBasis).coord.symm fun i ↦ z (some i)) =
      b.conjugatedGeneratorProduct (List.finRange n) z := by
  change
    b.conjugateTailHom (z none)
        ((b.tailBasis).coord.symm fun i ↦ z (some i)) =
      b.conjugatedGeneratorProduct (List.finRange n) z
  rw [(b.tailBasis).symm_apply]
  unfold canonicalBasisProduct conjugatedGeneratorProduct
  apply ordered_z_list
  intro i hi
  exact b.conjugate_tail_generator (z none) i

/-- Multiplication in canonical coordinates reduces on the tail to
multiplication in `G₁`, after conjugating the left tail by the right head
parameter. -/
lemma tailCoord_mul {n : ℕ} (b : HCBasis G (n + 1))
    (x y : Fin (n + 1) → ℤ) :
    Fin.tail (b.coord (b.coord.symm x * b.coord.symm y)) =
      (b.tailBasis).coord
        (b.conjugateTail (y 0) (b.tailCoordEquiv.symm (Fin.tail x)) *
          b.tailCoordEquiv.symm (Fin.tail y)) := by
  let u := b.generators 0
  let kx : b.tail 1 := b.tailCoordEquiv.symm (Fin.tail x)
  let ky : b.tail 1 := b.tailCoordEquiv.symm (Fin.tail y)
  let k : b.tail 1 := b.conjugateTail (y 0) kx * ky
  let z := b.coord (b.coord.symm x * b.coord.symm y)
  let kz : b.tail 1 := b.tailCoordEquiv.symm (Fin.tail z)
  have hxy :
      b.coord.symm x * b.coord.symm y =
        u ^ (x 0 + y 0) * k := by
    rw [b.symm_head_tail, b.symm_head_tail]
    dsimp only [u, kx, ky, k, conjugateTail]
    simp only [Subgroup.coe_mul]
    rw [zpow_add]
    group
  have hz :
      b.coord.symm x * b.coord.symm y =
        u ^ z 0 * kz := by
    rw [← b.coord.symm_apply_apply
      (b.coord.symm x * b.coord.symm y)]
    exact b.symm_head_tail z
  have hkz : kz = k := by
    apply Subtype.ext
    have hhead : z 0 = x 0 + y 0 := b.coord_mul_zero x y
    rw [hhead] at hz
    exact mul_left_cancel (hz.symm.trans hxy)
  change Fin.tail z = (b.tailCoordEquiv) k
  rw [← hkz]
  exact (b.tailCoordEquiv.apply_symm_apply _).symm

@[simp]
lemma canonical_basis_fin (u : Fin 1 → G) (x : Fin 1 → ℤ) :
    canonicalBasisProduct u x = u 0 ^ x 0 := by
  rw [canonicalBasisProduct, orderedZPow, List.finRange_succ_last]
  simp

@[simp]
lemma symm_fin_one (b : HCBasis G 1) (x : Fin 1 → ℤ) :
    b.coord.symm x = b.generators 0 ^ x 0 := by
  rw [b.symm_apply, canonical_basis_fin]

lemma coord_fin_one (b : HCBasis G 1) (x y : Fin 1 → ℤ) :
    b.coord (b.coord.symm x * b.coord.symm y) 0 = x 0 + y 0 := by
  rw [b.symm_fin_one, b.symm_fin_one, ← zpow_add,
    ← b.symm_fin_one (fun _ => x 0 + y 0), b.coord.apply_symm_apply]

lemma coord_zpow_fin (b : HCBasis G 1)
    (x : Fin 1 → ℤ) (a : ℤ) :
    b.coord ((b.coord.symm x) ^ a) 0 = a * x 0 := by
  rw [b.symm_fin_one, ← zpow_mul, mul_comm,
    ← b.symm_fin_one (fun _ => a * x 0), b.coord.apply_symm_apply]

end HCBasis

/-- The `i`th coordinate of multiplication, expressed entirely in
canonical-coordinate variables. -/
def canonicalMulCoordinate {ι : Type*} (coord : G ≃ (ι → ℤ)) (i : ι)
    (z : Sum ι ι → ℤ) : ℤ :=
  coord
    (coord.symm (fun j => z (Sum.inl j)) *
      coord.symm (fun j => z (Sum.inr j))) i

/-- Assignment of the exponent and the canonical coordinates of an element
to the variables used for a power-coordinate polynomial. -/
def canonicalPowAssignment {ι : Type*} (a : ℤ) (x : ι → ℤ) :
    Option ι → ℤ
  | none => a
  | some i => x i

/-- The `i`th coordinate of an integer power, expressed in the exponent and
canonical-coordinate variables. -/
def canonicalPowCoordinate {ι : Type*} (coord : G ≃ (ι → ℤ)) (i : ι)
    (z : Option ι → ℤ) : ℤ :=
  coord ((coord.symm fun j => z (some j)) ^ z none) i

/-- Substituting polynomial coordinate tuples into canonical multiplication
preserves coordinatewise polynomiality. -/
theorem coordinatewise_integer_valued
    {ι κ : Type*} (coord : G ≃ (ι → ℤ))
    (hmul : ∀ i, IVPolya (canonicalMulCoordinate coord i))
    {f g : (κ → ℤ) → (ι → ℤ)}
    (hf : CIValued f)
    (hg : CIValued g) :
    CIValued
      (fun x => coord (coord.symm (f x) * coord.symm (g x))) := by
  intro i
  simpa [canonicalMulCoordinate] using
    (hmul i).comp
      (coordinatewise_valued_elim hf hg)

/-- Substituting a polynomial exponent and polynomial coordinate tuple into
canonical integer powering preserves coordinatewise polynomiality. -/
theorem coordinatewise_valued_pow
    {ι κ : Type*} (coord : G ≃ (ι → ℤ))
    (hpow : ∀ i, IVPolya (canonicalPowCoordinate coord i))
    {a : (κ → ℤ) → ℤ} {f : (κ → ℤ) → (ι → ℤ)}
    (ha : IVPolya a)
    (hf : CIValued f) :
    CIValued
      (fun x => coord ((coord.symm (f x)) ^ a x)) := by
  intro i
  simpa [canonicalPowCoordinate] using
    (hpow i).comp (coordinatewise_valued_option ha hf)

/-- Substituting compositional binomial expressions into canonical
multiplication preserves expression-valued coordinates. -/
theorem coordinatewise_expression_canonical
    {ι κ : Type*} (coord : G ≃ (ι → ℤ))
    (hmul : ∀ i, IEMap (canonicalMulCoordinate coord i))
    {f g : (κ → ℤ) → (ι → ℤ)}
    (hf : CBExpr f)
    (hg : CBExpr g) :
    CBExpr
      (fun x => coord (coord.symm (f x) * coord.symm (g x))) := by
  intro i
  simpa [canonicalMulCoordinate] using
    (hmul i).comp
      (coordinatewise_expression_elim hf hg)

/-- Substituting a compositional binomial exponent and coordinate tuple
into canonical integer powering preserves expression-valued coordinates. -/
theorem coordinatewise_expression_pow
    {ι κ : Type*} (coord : G ≃ (ι → ℤ))
    (hpow : ∀ i, IEMap (canonicalPowCoordinate coord i))
    {a : (κ → ℤ) → ℤ} {f : (κ → ℤ) → (ι → ℤ)}
    (ha : IEMap a)
    (hf : CBExpr f) :
    CBExpr
      (fun x => coord ((coord.symm (f x)) ^ a x)) := by
  intro i
  simpa [canonicalPowCoordinate] using
    (hpow i).comp (coordinatewise_expression_option ha hf)

namespace HCBasis

/-- The tail coordinates of conjugation by an arbitrary power of the first
canonical generator. These are the remaining recursive inputs in Hall's
multiplication argument. -/
noncomputable def conjugateTailCoordinate {n : ℕ}
    (b : HCBasis G (n + 1)) (i : Fin n)
    (z : Option (Fin n) → ℤ) : ℤ :=
  (b.tailBasis).coord
    (b.conjugateTail (z none)
      ((b.tailBasis).coord.symm fun j => z (some j))) i

/-- The first tail coordinate is unchanged by conjugation by the head
generator. -/
lemma conjugate_tail_zero {n : ℕ}
    (b : HCBasis G (n + 2)) (z : Option (Fin (n + 1)) → ℤ) :
    b.conjugateTailCoordinate 0 z = z (some 0) := by
  change
    (b.tailBasis).coord
        (b.conjugateTail (z none)
          ((b.tailBasis).coord.symm fun j => z (some j))) 0 =
      z (some 0)
  rw [← congrFun ((b.tailBasis).coord.apply_symm_apply
    (fun j => z (some j))) 0]
  apply (b.tailBasis).coord_div_tail
  change
    (b.conjugateTail (z none)
      ((b.tailBasis).coord.symm fun j => z (some j)) :
        b.tail 1) /
      (b.tailBasis).coord.symm (fun j => z (some j)) ∈
        (b.tailBasis).tail 1
  exact b.conjugate_div_two _ _

/-- Consequently, the first tail conjugation coordinate is a projection
polynomial. -/
theorem conjugate_integer_valued {n : ℕ}
    (b : HCBasis G (n + 2)) :
    IVPolya (b.conjugateTailCoordinate 0) := by
  have h :
      IVPolya
        (fun z : Option (Fin (n + 1)) → ℤ => z (some 0)) :=
    integer_valued_polynomial _
  rw [show b.conjugateTailCoordinate 0 =
    (fun z : Option (Fin (n + 1)) → ℤ => z (some 0)) by
      funext z
      exact b.conjugate_tail_zero z]
  exact h

/-- The first multiplication coordinate of any nonempty canonical basis is
the sum of the two first input coordinates. -/
theorem canonical_binomial_polynomial {n : ℕ}
    (b : HCBasis G (n + 1)) :
    IBMap (canonicalMulCoordinate b.coord 0) := by
  have hleft :
      IBMap
        (fun z : Sum (Fin (n + 1)) (Fin (n + 1)) → ℤ => z (Sum.inl 0)) :=
    binomial_polynomial _
  have hright :
      IBMap
        (fun z : Sum (Fin (n + 1)) (Fin (n + 1)) → ℤ => z (Sum.inr 0)) :=
    binomial_polynomial _
  have hcoord :
      canonicalMulCoordinate b.coord 0 =
        fun z : Sum (Fin (n + 1)) (Fin (n + 1)) → ℤ =>
          z (Sum.inl 0) + z (Sum.inr 0) := by
    funext z
    exact b.coord_mul_zero
      (fun j => z (Sum.inl j)) (fun j => z (Sum.inr j))
  rw [hcoord]
  exact hleft.add hright

/-- The first power coordinate of any nonempty canonical basis is the
product of the exponent and the first input coordinate. -/
theorem canonical_coordinate_binomial {n : ℕ}
    (b : HCBasis G (n + 1)) :
    IBMap (canonicalPowCoordinate b.coord 0) := by
  have ha :
      IBMap
        (fun z : Option (Fin (n + 1)) → ℤ => z none) :=
    binomial_polynomial _
  have hx :
      IBMap
        (fun z : Option (Fin (n + 1)) → ℤ => z (some 0)) :=
    binomial_polynomial _
  have hcoord :
      canonicalPowCoordinate b.coord 0 =
        fun z : Option (Fin (n + 1)) → ℤ => z none * z (some 0) := by
    funext z
    exact b.coord_zpow_zero (fun j => z (some j)) (z none)
  rw [hcoord]
  exact ha.mul hx

/-- The correction term has polynomial coordinates in Hall's smaller
head-plus-suffix subgroup, assuming the smaller multiplication and power
cases. -/
theorem head_suffix_coordinatewise
    {n : ℕ} (b : HCBasis G (n + 1)) (i : Fin n)
    (hmul :
      ∀ j, IVPolya
        (canonicalMulCoordinate
          (b.headSuffixBasis ((i : ℕ) + 2) (by omega) (by omega)).coord j))
    (hpow :
      ∀ j, IVPolya
        (canonicalPowCoordinate
          (b.headSuffixBasis ((i : ℕ) + 2) (by omega) (by omega)).coord j)) :
    CIValued
      (fun z : (Option (Fin n) → ℤ) =>
        (b.headSuffixBasis ((i : ℕ) + 2) (by omega) (by omega)).coord
          (b.conjugateHeadSuffix i (z none))) := by
  let hb := b.headSuffixBasis ((i : ℕ) + 2) (by omega) (by omega)
  let head : b.headSuffixSubgroup ((i : ℕ) + 2) :=
    ⟨b.generators 0, b.head_suffix_subgroup ((i : ℕ) + 2)⟩
  let c : b.headSuffixSubgroup ((i : ℕ) + 2) :=
    ⟨b.generators i.succ * b.generators 0 * (b.generators i.succ)⁻¹,
      b.conjugated_head_suffix i⟩
  have ha :
      IVPolya
        (fun z : Option (Fin n) → ℤ => z none) :=
    integer_valued_polynomial _
  have hhead :
      CIValued
        (fun _ : Option (Fin n) → ℤ => hb.coord head) := by
    intro j
    exact integer_valued_const _
  have hc :
      CIValued
        (fun _ : Option (Fin n) → ℤ => hb.coord c) := by
    intro j
    exact integer_valued_const _
  have hleft :=
    coordinatewise_valued_pow hb.coord hpow
      ha.neg hhead
  have hright :=
    coordinatewise_valued_pow hb.coord hpow
      ha hc
  have hproduct :=
    coordinatewise_integer_valued hb.coord hmul
      hleft hright
  have heq :
      (fun z : Option (Fin n) → ℤ =>
        hb.coord (b.conjugateHeadSuffix i (z none))) =
        (fun z : Option (Fin n) → ℤ =>
          hb.coord (head ^ (-(z none)) * c ^ (z none))) := by
    funext z
    apply congrArg hb.coord
    apply Subtype.ext
    simp only [conjugateHeadSuffix, head, c,
      Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_zpow, Subgroup.coe_mk,
      zpow_neg]
  rw [heq]
  simpa only [Equiv.symm_apply_apply] using hproduct

/-- The correction term consequently has polynomial coordinates in the
first tail basis. -/
theorem conjugate_generator_coordinatewise
    {n : ℕ} (b : HCBasis G (n + 1)) (i : Fin n)
    (hmul :
      ∀ j, IVPolya
        (canonicalMulCoordinate
          (b.headSuffixBasis ((i : ℕ) + 2) (by omega) (by omega)).coord j))
    (hpow :
      ∀ j, IVPolya
        (canonicalPowCoordinate
          (b.headSuffixBasis ((i : ℕ) + 2) (by omega) (by omega)).coord j)) :
    CIValued
      (fun z : (Option (Fin n) → ℤ) =>
        (b.tailBasis).coord (b.conjugateGeneratorCorrection i (z none))) := by
  have hheadSuffix :=
    b.head_suffix_coordinatewise
      i hmul hpow
  intro j
  by_cases hj : (j : ℕ) < (i : ℕ) + 1
  · rw [show
      (fun z : Option (Fin n) → ℤ =>
        (b.tailBasis).coord (b.conjugateGeneratorCorrection i (z none)) j) =
          (fun _ : Option (Fin n) → ℤ => 0) by
      funext z
      exact b.tail_coord_conjugate
        i j hj (z none)]
    exact integer_valued_const 0
  · have hji : (i : ℕ) + 1 ≤ (j : ℕ) := by omega
    rw [show
      (fun z : Option (Fin n) → ℤ =>
        (b.tailBasis).coord (b.conjugateGeneratorCorrection i (z none)) j) =
          (fun z : Option (Fin n) → ℤ =>
            (b.headSuffixBasis ((i : ℕ) + 2) (by omega) (by omega)).coord
              (b.conjugateHeadSuffix i (z none))
              ⟨(j : ℕ) - ((i : ℕ) + 1) + 1, by omega⟩) by
      funext z
      exact
        b.conjugate_head_suffix
          i j hji (z none)]
    exact hheadSuffix ⟨(j : ℕ) - ((i : ℕ) + 1) + 1, by omega⟩

/-- Every individually conjugated later generator has polynomial
coordinates in the first tail basis. -/
theorem conjug_coord_coord
    {n : ℕ} (b : HCBasis G (n + 1)) (i : Fin n)
    (htailMul :
      ∀ j, IVPolya
        (canonicalMulCoordinate (b.tailBasis).coord j))
    (hmul :
      ∀ j, IVPolya
        (canonicalMulCoordinate
          (b.headSuffixBasis ((i : ℕ) + 2) (by omega) (by omega)).coord j))
    (hpow :
      ∀ j, IVPolya
        (canonicalPowCoordinate
          (b.headSuffixBasis ((i : ℕ) + 2) (by omega) (by omega)).coord j)) :
    CIValued
      (fun z : (Option (Fin n) → ℤ) =>
        (b.tailBasis).coord (b.conjugateGeneratorTail i (z none))) := by
  have hcorrection :=
    b.conjugate_generator_coordinatewise i hmul hpow
  have hgenerator :
      CIValued
        (fun _ : Option (Fin n) → ℤ =>
          (b.tailBasis).coord
            ⟨b.generators i.succ,
              b.generator_tail (by omega) i.succ (by simp)⟩) := by
    intro j
    exact integer_valued_const _
  have hproduct :=
    coordinatewise_integer_valued
      (b.tailBasis).coord htailMul hcorrection hgenerator
  have heq :
      (fun z : Option (Fin n) → ℤ =>
        (b.tailBasis).coord (b.conjugateGeneratorTail i (z none))) =
        (fun z : Option (Fin n) → ℤ =>
          (b.tailBasis).coord
            (b.conjugateGeneratorCorrection i (z none) *
              ⟨b.generators i.succ,
                b.generator_tail (by omega) i.succ (by simp)⟩)) := by
    funext z
    rw [b.conjugate_generator_tail]
  rw [heq]
  simpa only [Equiv.symm_apply_apply] using hproduct

/-- Finite ordered products of individually conjugated generator powers
have polynomial coordinates. -/
theorem conjugated_generator_coordinatewise
    {n : ℕ} (b : HCBasis G (n + 1))
    (htailMul :
      ∀ j, IVPolya
        (canonicalMulCoordinate (b.tailBasis).coord j))
    (htailPow :
      ∀ j, IVPolya
        (canonicalPowCoordinate (b.tailBasis).coord j))
    (hgenerator :
      ∀ i, CIValued
        (fun z : Option (Fin n) → ℤ =>
          (b.tailBasis).coord (b.conjugateGeneratorTail i (z none)))) :
    ∀ l : List (Fin n),
      CIValued
        (fun z : Option (Fin n) → ℤ =>
          (b.tailBasis).coord (b.conjugatedGeneratorProduct l z))
  | [] => by
      intro j
      simpa [conjugatedGeneratorProduct, orderedZPow] using
        (integer_valued_const ((b.tailBasis).coord 1 j) :
          IVPolya
            (fun _ : Option (Fin n) → ℤ => (b.tailBasis).coord 1 j))
  | i :: l => by
      have hexponent :
          IVPolya
            (fun z : Option (Fin n) → ℤ => z (some i)) :=
        integer_valued_polynomial _
      have hpower :=
        coordinatewise_valued_pow
          (b.tailBasis).coord htailPow hexponent (hgenerator i)
      have htail :=
        b.conjugated_generator_coordinatewise
          htailMul htailPow hgenerator l
      have hproduct :=
        coordinatewise_integer_valued
          (b.tailBasis).coord htailMul hpower htail
      simpa [conjugatedGeneratorProduct, orderedZPow] using hproduct

/-- Conjugating an arbitrary first-tail element by a head-generator power
has polynomial first-tail coordinates. -/
theorem conjugate_tail_coordinatewise
    {n : ℕ} (b : HCBasis G (n + 1))
    (htailMul :
      ∀ j, IVPolya
        (canonicalMulCoordinate (b.tailBasis).coord j))
    (htailPow :
      ∀ j, IVPolya
        (canonicalPowCoordinate (b.tailBasis).coord j))
    (hmul :
      ∀ i : Fin n, ∀ j, IVPolya
        (canonicalMulCoordinate
          (b.headSuffixBasis ((i : ℕ) + 2) (by omega) (by omega)).coord j))
    (hpow :
      ∀ i : Fin n, ∀ j, IVPolya
        (canonicalPowCoordinate
          (b.headSuffixBasis ((i : ℕ) + 2) (by omega) (by omega)).coord j)) :
    CIValued
      (fun z : Option (Fin n) → ℤ =>
        (b.tailBasis).coord
          (b.conjugateTail (z none)
            ((b.tailBasis).coord.symm fun i ↦ z (some i)))) := by
  have hgenerator :
      ∀ i, CIValued
        (fun z : Option (Fin n) → ℤ =>
          (b.tailBasis).coord (b.conjugateGeneratorTail i (z none))) :=
    fun i ↦
      b.conjug_coord_coord
        i htailMul (hmul i) (hpow i)
  have hproduct :=
    b.conjugated_generator_coordinatewise
      htailMul htailPow hgenerator (List.finRange n)
  rw [show
    (fun z : Option (Fin n) → ℤ =>
      (b.tailBasis).coord
        (b.conjugateTail (z none)
          ((b.tailBasis).coord.symm fun i ↦ z (some i)))) =
      (fun z : Option (Fin n) → ℤ =>
        (b.tailBasis).coord
          (b.conjugatedGeneratorProduct (List.finRange n) z)) by
    funext z
    rw [b.conjugate_tail_conjugated]]
  exact hproduct

/-- Coordinate form of the preceding tuple-valued conjugation theorem. -/
theorem conjugate_coordinates_valued
    {n : ℕ} (b : HCBasis G (n + 1))
    (htailMul :
      ∀ j, IVPolya
        (canonicalMulCoordinate (b.tailBasis).coord j))
    (htailPow :
      ∀ j, IVPolya
        (canonicalPowCoordinate (b.tailBasis).coord j))
    (hmul :
      ∀ i : Fin n, ∀ j, IVPolya
        (canonicalMulCoordinate
          (b.headSuffixBasis ((i : ℕ) + 2) (by omega) (by omega)).coord j))
    (hpow :
      ∀ i : Fin n, ∀ j, IVPolya
        (canonicalPowCoordinate
          (b.headSuffixBasis ((i : ℕ) + 2) (by omega) (by omega)).coord j)) :
    ∀ j, IVPolya (b.conjugateTailCoordinate j) := by
  have h :=
    b.conjugate_tail_coordinatewise htailMul htailPow hmul hpow
  intro j
  exact h j

/-- Polynomial multiplication coordinates on `G₁`, together with
polynomial coordinates for conjugation by the head generator, lift to
polynomial multiplication coordinates on the whole canonical basis. -/
theorem canonical_coordinates_tail {n : ℕ}
    (b : HCBasis G (n + 1))
    (htail :
      ∀ i, IVPolya
        (canonicalMulCoordinate (b.tailBasis).coord i))
    (hconj :
      ∀ i, IVPolya (b.conjugateTailCoordinate i)) :
    ∀ i, IVPolya (canonicalMulCoordinate b.coord i) := by
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact b.canonical_binomial_polynomial
      |>.integer_valued_polymap
  · let leftTail :
        (Sum (Fin (n + 1)) (Fin (n + 1)) → ℤ) → (Fin n → ℤ) :=
      fun z j => z (Sum.inl j.succ)
    let rightTail :
        (Sum (Fin (n + 1)) (Fin (n + 1)) → ℤ) → (Fin n → ℤ) :=
      fun z j => z (Sum.inr j.succ)
    let conjugatedLeftTail :
        (Sum (Fin (n + 1)) (Fin (n + 1)) → ℤ) → (Fin n → ℤ) :=
      fun z =>
        (b.tailBasis).coord
          (b.conjugateTail (z (Sum.inr 0))
            ((b.tailBasis).coord.symm (leftTail z)))
    have hleft :
        CIValued leftTail := by
      intro k
      exact integer_valued_polynomial _
    have hright :
        CIValued rightTail := by
      intro k
      exact integer_valued_polynomial _
    have hconjugated :
        CIValued conjugatedLeftTail := by
      intro k
      have hk := (hconj k).reindex
        (fun z : Option (Fin n) =>
          match z with
          | none => Sum.inr (0 : Fin (n + 1))
          | some l => Sum.inl l.succ)
      simpa [conjugateTailCoordinate, conjugatedLeftTail, leftTail] using hk
    have hproduct :=
      coordinatewise_integer_valued
        (b.tailBasis).coord htail hconjugated hright
    have hcoord :
        canonicalMulCoordinate b.coord j.succ =
          fun z =>
            (b.tailBasis).coord
              ((b.tailBasis).coord.symm (conjugatedLeftTail z) *
                (b.tailBasis).coord.symm (rightTail z)) j := by
      funext z
      rw [canonicalMulCoordinate]
      have htailcoord := congrFun
        (b.tailCoord_mul (fun k => z (Sum.inl k)) (fun k => z (Sum.inr k))) j
      simpa [conjugatedLeftTail, leftTail, rightTail] using htailcoord
    rw [hcoord]
    exact hproduct j

/-- Hall's multiplication induction step: all smaller multiplication and
power cases imply the multiplication case for the current basis. -/
theorem canonical_coordinates_smaller {n : ℕ}
    (b : HCBasis G (n + 1))
    (hsmaller :
      ∀ {H : Type u} [Group H] {m : ℕ}, m < n + 1 →
        (c : HCBasis H m) →
        (∀ j, IVPolya
          (canonicalMulCoordinate c.coord j)) ∧
        ∀ j, IVPolya
          (canonicalPowCoordinate c.coord j)) :
    ∀ j, IVPolya (canonicalMulCoordinate b.coord j) := by
  have htail :=
    hsmaller (Nat.lt_succ_self n) b.tailBasis
  apply b.canonical_coordinates_tail htail.1
  apply b.conjugate_coordinates_valued htail.1 htail.2
  · intro i
    exact (hsmaller (by omega)
      (b.headSuffixBasis ((i : ℕ) + 2) (by omega) (by omega))).1
  · intro i
    exact (hsmaller (by omega)
      (b.headSuffixBasis ((i : ℕ) + 2) (by omega) (by omega))).2

/-- The coordinates of a power of one canonical generator are supported
at that generator's index. -/
lemma coord_zpow {n : ℕ}
    (b : HCBasis G n) (i : Fin n) (a : ℤ) :
    b.coord (b.generators i ^ a) = fun j => if i = j then a else 0 := by
  let x : Fin n → ℤ := fun j => if i = j then a else 0
  have hprod :
      canonicalBasisProduct b.generators x = b.generators i ^ a := by
    exact ordered_z_single b.generators a (List.finRange n)
      (List.nodup_finRange n) i (List.mem_finRange i)
  rw [← hprod, b.coord_basis_product]

/-- An ordered product of canonical generators with polynomial exponents
has polynomial canonical coordinates. -/
theorem z_coordinates_coordinatewise
    {n : ℕ} (b : HCBasis G n)
    (hmul :
      ∀ j, IVPolya
        (canonicalMulCoordinate b.coord j))
    {κ : Type v} (a : Fin n → (κ → ℤ) → ℤ)
    (ha : ∀ i, IVPolya (a i)) :
    ∀ l : List (Fin n),
      CIValued
        (fun z => b.coord (orderedZPow b.generators (fun i => a i z) l))
  | [] => by
      intro j
      simpa [orderedZPow] using
        (integer_valued_const (b.coord 1 j) :
          IVPolya (fun _ : κ → ℤ => b.coord 1 j))
  | i :: l => by
      have hfactor :
          CIValued
            (fun z => b.coord (b.generators i ^ a i z)) := by
        intro j
        by_cases hij : i = j
        · subst j
          simpa [b.coord_zpow] using ha i
        · rw [show
            (fun z => b.coord (b.generators i ^ a i z) j) =
              (fun _ : κ → ℤ => 0) by
            funext z
            rw [b.coord_zpow]
            simp [hij]]
          exact integer_valued_const 0
      have htail :=
        b.z_coordinates_coordinatewise hmul a ha l
      have hproduct :=
        coordinatewise_integer_valued
          b.coord hmul hfactor htail
      simpa [orderedZPow] using hproduct

/-- Inverting a canonical-basis product reverses the generator order and
negates all exponents. -/
lemma inv_basis_reverse {n : ℕ}
    (b : HCBasis G n) (x : Fin n → ℤ) :
    (b.coord.symm x)⁻¹ =
      orderedZPow b.generators (fun i => -x i)
        (List.finRange n).reverse := by
  rw [b.symm_apply]
  unfold canonicalBasisProduct orderedZPow
  rw [List.prod_inv_reverse]
  rw [List.map_reverse, List.map_map]
  apply congrArg List.prod
  apply congrArg List.reverse
  apply List.map_congr_left
  intro i hi
  exact (zpow_neg _ _).symm

/-- Inverse coordinates are polynomial once multiplication coordinates
are polynomial. -/
theorem inv_coordinates_coordinatewise {n : ℕ}
    (b : HCBasis G n)
    (hmul :
      ∀ j, IVPolya
        (canonicalMulCoordinate b.coord j)) :
    CIValued
      (fun x => b.coord ((b.coord.symm x)⁻¹)) := by
  rw [show
    (fun x => b.coord ((b.coord.symm x)⁻¹)) =
      (fun x => b.coord
        (orderedZPow b.generators (fun i => -x i)
          (List.finRange n).reverse)) by
    funext x
    rw [b.inv_basis_reverse]]
  apply b.z_coordinates_coordinatewise hmul
  intro i
  exact (integer_valued_polynomial i).neg

/-- Pointwise products of polynomially parameterized group elements have
polynomial canonical coordinates. -/
theorem polynomialElement_mul {n : ℕ} (b : HCBasis G n)
    (hmul :
      ∀ j, IVPolya
        (canonicalMulCoordinate b.coord j))
    {κ : Type v} {f g : (κ → ℤ) → G}
    (hf : CIValued (fun z => b.coord (f z)))
    (hg : CIValued (fun z => b.coord (g z))) :
    CIValued
      (fun z => b.coord (f z * g z)) := by
  simpa only [Equiv.symm_apply_apply] using
    (coordinatewise_integer_valued
      b.coord hmul hf hg)

/-- Pointwise inverses of polynomially parameterized group elements have
polynomial canonical coordinates. -/
theorem polynomialElement_inv {n : ℕ} (b : HCBasis G n)
    (hmul :
      ∀ j, IVPolya
        (canonicalMulCoordinate b.coord j))
    {κ : Type v} {f : (κ → ℤ) → G}
    (hf : CIValued (fun z => b.coord (f z))) :
    CIValued
      (fun z => b.coord (f z)⁻¹) := by
  have hinv := (b.inv_coordinates_coordinatewise hmul).comp hf
  simpa only [Equiv.symm_apply_apply] using hinv

/-- Fixed natural powers of polynomially parameterized group elements
have polynomial canonical coordinates. -/
theorem polynomialElement_npow {n : ℕ} (b : HCBasis G n)
    (hmul :
      ∀ j, IVPolya
        (canonicalMulCoordinate b.coord j))
    {κ : Type v} {f : (κ → ℤ) → G}
    (hf : CIValued (fun z => b.coord (f z))) :
    ∀ m : ℕ, CIValued
      (fun z => b.coord ((f z) ^ m))
  | 0 => by
      intro j
      simpa using
        (integer_valued_const (b.coord 1 j) :
          IVPolya (fun _ : κ → ℤ => b.coord 1 j))
  | m + 1 => by
      rw [show
        (fun z => b.coord ((f z) ^ (m + 1))) =
          (fun z => b.coord ((f z) ^ m * f z)) by
        funext z
        rw [pow_succ]]
      exact b.polynomialElement_mul hmul (b.polynomialElement_npow hmul hf m) hf

/-- Finite products of polynomially parameterized group elements have
polynomial canonical coordinates. -/
theorem polynomial_element_prod {n : ℕ} (b : HCBasis G n)
    (hmul :
      ∀ j, IVPolya
        (canonicalMulCoordinate b.coord j))
    {κ X : Type*} {f : X → (κ → ℤ) → G}
    (hf : ∀ i, CIValued
      (fun z => b.coord (f i z))) :
    ∀ l : List X, CIValued
      (fun z => b.coord ((l.map fun i => f i z).prod))
  | [] => by
      intro j
      simpa using
        (integer_valued_const (b.coord 1 j) :
          IVPolya (fun _ : κ → ℤ => b.coord 1 j))
  | i :: l => by
      simpa only [List.map_cons, List.prod_cons] using
        b.polynomialElement_mul hmul (hf i)
          (b.polynomial_element_prod hmul hf l)

/-- Every recursively defined Petresco term has polynomial canonical
coordinates when its input factors do. -/
theorem petresco_term_coordinatewise {n : ℕ}
    (b : HCBasis G n)
    (hmul :
      ∀ j, IVPolya
        (canonicalMulCoordinate b.coord j))
    {κ X : Type*} (f : X → (κ → ℤ) → G)
    (hf : ∀ i, CIValued
      (fun z => b.coord (f i z)))
    (l : List X) :
    ∀ w : ℕ, CIValued
      (fun z => b.coord (petrescoTerm (l.map fun i => f i z) w)) := by
  intro w
  induction w using Nat.strong_induction_on with
  | h w ih =>
      cases w with
      | zero =>
          intro j
          simpa using
            (integer_valued_const (b.coord 1 j) :
              IVPolya (fun _ : κ → ℤ => b.coord 1 j))
      | succ w =>
          have hpriorFactors :
              ∀ j : Fin w, CIValued
                (fun z => b.coord
                  ((petrescoTerm (l.map fun i => f i z) ((j : ℕ) + 1)) ^
                    Nat.choose (w + 1) ((j : ℕ) + 1))) := by
            intro j
            exact b.polynomialElement_npow hmul (ih ((j : ℕ) + 1) (by omega))
              (Nat.choose (w + 1) ((j : ℕ) + 1))
          have hpriorProduct :=
            b.polynomial_element_prod hmul hpriorFactors (List.finRange w)
          have hpriorInv :=
            b.polynomialElement_inv hmul hpriorProduct
          have hinputPowers :
              ∀ i, CIValued
                (fun z => b.coord ((f i z) ^ (w + 1))) := by
            intro i
            exact b.polynomialElement_npow hmul (hf i) (w + 1)
          have hinputProduct :=
            b.polynomial_element_prod hmul hinputPowers l
          have hproduct :=
            b.polynomialElement_mul hmul hpriorInv hinputProduct
          rw [show
            (fun z => b.coord
              (petrescoTerm (l.map fun i => f i z) (w + 1))) =
              (fun z => b.coord
                ((petrescoPriorProduct
                    (petrescoTerm (l.map fun i => f i z)) (w + 1))⁻¹ *
                  ((l.map fun i => f i z).map fun g => g ^ (w + 1)).prod)) by
            funext z
            rw [petrescoTerm_succ]]
          unfold petrescoPriorProduct
          simpa only [Nat.add_sub_cancel, List.map_map] using hproduct

/-- The lower central series is bounded by every recorded canonical-basis
tail series. -/
lemma lower_series_tail {n : ℕ}
    (b : HCBasis G n) :
    ∀ k : ℕ, Subgroup.lowerCentralSeries G k ≤ b.tail k
  | 0 => by rw [Subgroup.lowerCentralSeries_zero, b.tail_zero]
  | k + 1 => by
      change ⁅Subgroup.lowerCentralSeries G k, (⊤ : Subgroup G)⁆ ≤ b.tail (k + 1)
      exact le_trans
        (Subgroup.commutator_mono (b.lower_series_tail k) le_rfl)
        (b.tail_central k)

/-- Petresco terms lie in the corresponding recorded canonical-basis tail. -/
lemma petresco_tail {n : ℕ} (b : HCBasis G n)
    (x : List G) (w : ℕ) :
    petrescoTerm x w ∈ b.tail (w - 1) :=
  b.lower_series_tail (w - 1)
    (petresco_lower_series x w)

/-- An individual generalized binomial coefficient is an
integer-valued polynomial map. -/
theorem ring_choose_valued
    {κ : Type*} (i : κ) (m : ℕ) :
    IVPolya
      (fun z : κ → ℤ => Ring.choose (z i) m) := by
  exact
    (show IBMap
      (fun z : κ → ℤ => Ring.choose (z i) m) from
      ⟨.choose i m, fun _ => rfl⟩).integer_valued_polymap

/-- Variable integer powers of polynomially parameterized group elements
have polynomial coordinates once the basis power coordinates are
polynomial. -/
theorem polynomialElement_zpow {n : ℕ} (b : HCBasis G n)
    (hpow :
      ∀ j, IVPolya
        (canonicalPowCoordinate b.coord j))
    {κ : Type v} {f : (κ → ℤ) → G} {a : (κ → ℤ) → ℤ}
    (hf : CIValued (fun z => b.coord (f z)))
    (ha : IVPolya a) :
    CIValued
      (fun z => b.coord ((f z) ^ (a z))) := by
  simpa only [Equiv.symm_apply_apply] using
    (coordinatewise_valued_pow
      b.coord hpow ha hf)

/-- The recorded canonical-basis tails form an antitone sequence. -/
lemma tail_antitone {n : ℕ} (b : HCBasis G n) :
    Antitone b.tail :=
  antitone_nat_of_succ_le b.tail_succ_le

/-- Every Petresco term of weight at least two belongs to the first tail. -/
lemma petresco_term_tail {n : ℕ} (b : HCBasis G n)
    (x : List G) {w : ℕ} (hw : 2 ≤ w) :
    petrescoTerm x w ∈ b.tail 1 :=
  b.tail_antitone (by omega) (b.petresco_tail x w)

/-- Canonical generator powers regarded as the Petresco input factors for
Hall's power-coordinate argument. -/
def canonicalPowerFactors {n : ℕ} (b : HCBasis G n)
    (z : Option (Fin n) → ℤ) : List G :=
  (List.finRange n).map fun i => b.generators i ^ z (some i)

/-- A positive-weight Petresco correction, regarded as an element of the
first canonical-basis tail. -/
def canonicalPetrescoTerm {n : ℕ} (b : HCBasis G n)
    (z : Option (Fin n) → ℤ) (w : ℕ) (hw : 2 ≤ w) :
    b.tail 1 :=
  ⟨petrescoTerm (b.canonicalPowerFactors z) w,
    b.petresco_term_tail _ hw⟩

/-- The finite tail correction in Hall's rearranged power formula. Terms
beyond the basis length vanish, so weights `2, ..., n + 1` suffice for a
basis of length `n + 1`. -/
def canonicalPetrescoCorrection {n : ℕ} (b : HCBasis G (n + 1))
    (z : Option (Fin (n + 1)) → ℤ) : b.tail 1 :=
  ((List.range n).map fun j =>
    b.canonicalPetrescoTerm z (j + 2) (by omega) ^
      Ring.choose (z none) (j + 2)).prod

/-- Hall's rearranged Petresco candidate for the coordinates of an
arbitrary integer power. -/
def canonicalPowCandidate {n : ℕ} (b : HCBasis G (n + 1))
    (z : Option (Fin (n + 1)) → ℤ) : G :=
  orderedZPow b.generators
      (fun i => z none * z (some i)) (List.finRange (n + 1)) *
    (b.canonicalPetrescoCorrection z : G)⁻¹

/-- A variable power of a fixed canonical generator has polynomial
canonical coordinates. -/
theorem canoni_coord_coord {n : ℕ}
    (b : HCBasis G n) (i : Fin n) :
    CIValued
      (fun z : Option (Fin n) → ℤ =>
        b.coord (b.generators i ^ z (some i))) := by
  intro j
  by_cases hij : i = j
  · subst j
    simpa [b.coord_zpow] using
      (integer_valued_polynomial (some i) :
        IVPolya
          (fun z : Option (Fin n) → ℤ => z (some i)))
  · rw [show
      (fun z : Option (Fin n) → ℤ =>
        b.coord (b.generators i ^ z (some i)) j) =
        (fun _ : Option (Fin n) → ℤ => 0) by
      funext z
      rw [b.coord_zpow]
      simp [hij]]
    exact integer_valued_const 0

/-- Polynomial coordinates for a tail-valued family imply polynomial
ambient coordinates. -/
theorem element_coordinates_coordinatewise {n : ℕ}
    (b : HCBasis G (n + 1))
    {κ : Type v} {f : (κ → ℤ) → b.tail 1}
    (hf : CIValued
      (fun z => (b.tailBasis).coord (f z))) :
    CIValued
      (fun z => b.coord (f z : G)) := by
  intro j
  cases j using Fin.cases with
  | zero =>
      rw [show
        (fun z => b.coord (f z : G) 0) =
          (fun _ : κ → ℤ => 0) by
        funext z
        exact (b.mem_tail_iff (show 1 ≤ n + 1 by omega)).mp
          (f z).property (0 : Fin (n + 1)) (by simp)]
      exact integer_valued_const 0
  | succ j =>
      exact hf j

/-- The finite Petresco tail correction has polynomial coordinates,
assuming the smaller multiplication and power cases for the first tail. -/
theorem petresco_coordinates_coordinatewise {n : ℕ}
    (b : HCBasis G (n + 1))
    (hmul :
      ∀ j, IVPolya
        (canonicalMulCoordinate b.coord j))
    (htailMul :
      ∀ j, IVPolya
        (canonicalMulCoordinate (b.tailBasis).coord j))
    (htailPow :
      ∀ j, IVPolya
        (canonicalPowCoordinate (b.tailBasis).coord j)) :
    CIValued
      (fun z => (b.tailBasis).coord (b.canonicalPetrescoCorrection z)) := by
  have hpetresco :
      ∀ w : ℕ, CIValued
        (fun z : Option (Fin (n + 1)) → ℤ =>
          b.coord (petrescoTerm (b.canonicalPowerFactors z) w)) := by
    intro w
    exact b.petresco_term_coordinatewise hmul
      (fun i z => b.generators i ^ z (some i))
      (fun i => b.canoni_coord_coord i)
      (List.finRange (n + 1)) w
  have htailTerm :
      ∀ j : ℕ, CIValued
        (fun z : Option (Fin (n + 1)) → ℤ =>
          (b.tailBasis).coord
            (b.canonicalPetrescoTerm z (j + 2) (by omega))) := by
    intro j k
    exact hpetresco (j + 2) k.succ
  apply (b.tailBasis).polynomial_element_prod htailMul
  intro j
  apply (b.tailBasis).polynomialElement_zpow htailPow (htailTerm j)
  exact ring_choose_valued none (j + 2)

/-- Hall's rearranged Petresco power candidate has polynomial ambient
canonical coordinates. -/
theorem candid_coord_coord {n : ℕ}
    (b : HCBasis G (n + 1))
    (hmul :
      ∀ j, IVPolya
        (canonicalMulCoordinate b.coord j))
    (htailMul :
      ∀ j, IVPolya
        (canonicalMulCoordinate (b.tailBasis).coord j))
    (htailPow :
      ∀ j, IVPolya
        (canonicalPowCoordinate (b.tailBasis).coord j)) :
    CIValued
      (fun z => b.coord (b.canonicalPowCandidate z)) := by
  have hbase :
      CIValued
        (fun z : Option (Fin (n + 1)) → ℤ =>
          b.coord
            (orderedZPow b.generators
              (fun i => z none * z (some i)) (List.finRange (n + 1)))) := by
    apply b.z_coordinates_coordinatewise hmul
    intro i
    exact (integer_valued_polynomial none).mul
      (integer_valued_polynomial (some i))
  have hcorrectionTail :=
    b.petresco_coordinates_coordinatewise
      hmul htailMul htailPow
  have hcorrection :
      CIValued
        (fun z : Option (Fin (n + 1)) → ℤ =>
          b.coord ((b.canonicalPetrescoCorrection z : G)⁻¹)) := by
    apply b.polynomialElement_inv hmul
    exact b.element_coordinates_coordinatewise hcorrectionTail
  exact b.polynomialElement_mul hmul hbase hcorrection

/-- A product indexed by an initial range is unchanged when every
additional factor is the identity. -/
lemma list_prod_range {f : ℕ → G} {n m : ℕ}
    (hnm : n ≤ m) (hf : ∀ j, n ≤ j → f j = 1) :
    ((List.range m).map f).prod = ((List.range n).map f).prod := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hnm
  induction d with
  | zero => rfl
  | succ d ih =>
      rw [show n + (d + 1) = (n + d) + 1 by omega, List.range_succ,
        List.map_append, List.prod_append, ih (by omega)]
      simp [hf]

/-- Once all terms above `c` are trivial, a Petresco binomial product can
be uniformly truncated at `c`, independently of its exponent. -/
lemma petresco_binomial_range
    (tau : ℕ → G) (a c : ℕ)
    (htau : ∀ w, c < w → tau w = 1) :
    petrescoBinomialProduct tau a =
      ((List.range c).map fun j =>
        tau (j + 1) ^ Nat.choose a (j + 1)).prod := by
  let m := max a c
  calc
    petrescoBinomialProduct tau a =
        ((List.range m).map fun j =>
          tau (j + 1) ^ Nat.choose a (j + 1)).prod :=
      (choose_petresco_binomial tau
        (show a ≤ m by exact le_max_left _ _)).symm
    _ = ((List.range c).map fun j =>
          tau (j + 1) ^ Nat.choose a (j + 1)).prod := by
      apply list_prod_range
        (show c ≤ m by exact le_max_right _ _)
      intro j hj
      rw [htau (j + 1) (by omega)]
      simp

/-- Petresco terms strictly above the basis length vanish. -/
lemma petresco_term_length {n : ℕ}
    (b : HCBasis G n) (x : List G) {w : ℕ} (hw : n < w) :
    petrescoTerm x w = 1 := by
  apply Subgroup.mem_bot.mp
  rw [← b.tail_length]
  apply b.tail_antitone (show n ≤ w - 1 by omega)
  exact b.petresco_tail x w

/-- Package one exponent and one canonical-coordinate tuple into the input
shape used by `canonicalPowCoordinate`. -/
def canonicalPowParameters {n : ℕ} (a : ℤ) (x : Fin n → ℤ) :
    Option (Fin n) → ℤ
  | none => a
  | some i => x i

@[simp]
lemma canonical_parameters_none {n : ℕ} (a : ℤ) (x : Fin n → ℤ) :
    canonicalPowParameters a x none = a :=
  rfl

@[simp]
lemma canonical_parameters_some {n : ℕ} (a : ℤ) (x : Fin n → ℤ)
    (i : Fin n) :
    canonicalPowParameters a x (some i) = x i :=
  rfl

/-- The visibly polynomial Hall candidate agrees with ordinary powering
for natural exponents. -/
theorem canonical_candidate_cast {n : ℕ}
    (b : HCBasis G (n + 1))
    (x : Fin (n + 1) → ℤ) (a : ℕ) :
    b.canonicalPowCandidate (canonicalPowParameters (a : ℤ) x) =
      (b.coord.symm x) ^ a := by
  let factors : List G :=
    (List.finRange (n + 1)).map fun i => b.generators i ^ x i
  let correction : G :=
    ((List.range n).map fun j =>
      petrescoTerm factors (j + 2) ^ Nat.choose a (j + 2)).prod
  have hfamily := petresco_term_family factors a
  have htrunc :
      (factors.map fun g => g ^ a).prod =
        petrescoTerm factors 1 ^ a * correction := by
    rw [hfamily]
    rw [petresco_binomial_range
      (petrescoTerm factors) a (n + 1) (fun w hw =>
        b.petresco_term_length factors hw)]
    rw [List.prod_range_succ']
    simp only [zero_add, Nat.choose_one_right, Nat.succ_eq_add_one]
    rfl
  have hbase :
      orderedZPow b.generators
          (fun i => (a : ℤ) * x i) (List.finRange (n + 1)) =
        (factors.map fun g => g ^ a).prod := by
    unfold orderedZPow factors
    rw [List.map_map]
    apply congrArg List.prod
    apply List.map_congr_left
    intro i hi
    change b.generators i ^ ((a : ℤ) * x i) =
      (b.generators i ^ x i) ^ a
    rw [← zpow_natCast]
    rw [← zpow_mul]
    rw [mul_comm]
  have hcorrection :
      ((b.canonicalPetrescoCorrection
          (canonicalPowParameters (a : ℤ) x) : b.tail 1) : G) =
        correction := by
    change
      (b.tail 1).subtype
          (((List.range n).map fun j =>
            b.canonicalPetrescoTerm
                (canonicalPowParameters (a : ℤ) x) (j + 2) (by omega) ^
              Ring.choose (canonicalPowParameters (a : ℤ) x none)
                (j + 2)).prod) =
        ((List.range n).map fun j =>
          petrescoTerm factors (j + 2) ^ Nat.choose a (j + 2)).prod
    rw [map_list_prod, List.map_map]
    apply congrArg List.prod
    apply List.map_congr_left
    intro j hj
    change
      petrescoTerm
            (b.canonicalPowerFactors (canonicalPowParameters (a : ℤ) x))
            (j + 2) ^
          Ring.choose (canonicalPowParameters (a : ℤ) x none) (j + 2) =
        petrescoTerm factors (j + 2) ^ Nat.choose a (j + 2)
    simp only [canonical_parameters_none, Ring.choose_natCast]
    rw [zpow_natCast]
    rfl
  rw [canonicalPowCandidate]
  simp only [canonical_parameters_none, canonical_parameters_some]
  rw [hbase, hcorrection, htrunc]
  simp only [petrescoTerm_one]
  rw [show factors.prod = b.coord.symm x by
    rw [b.symm_apply]
    rfl]
  simp

/-- The candidate agrees with ordinary integer powering for positive
integer exponents. -/
theorem candidate_zpow_pos {n : ℕ}
    (b : HCBasis G (n + 1))
    (x : Fin (n + 1) → ℤ) {a : ℤ} (ha : 0 < a) :
    b.canonicalPowCandidate (canonicalPowParameters a x) =
      (b.coord.symm x) ^ a := by
  have h := b.canonical_candidate_cast x a.toNat
  rw [← zpow_natCast] at h
  simpa [Int.toNat_of_nonneg ha.le] using h

/-- The polynomial Petresco candidate satisfies the additive law for all
integer exponents. The polynomial-identity step extends the positive
natural-power calculation to arbitrary integer pairs. -/
theorem canonical_candidate_add {n : ℕ}
    (b : HCBasis G (n + 1))
    (hmul :
      ∀ j, IVPolya
        (canonicalMulCoordinate b.coord j))
    (htailMul :
      ∀ j, IVPolya
        (canonicalMulCoordinate (b.tailBasis).coord j))
    (htailPow :
      ∀ j, IVPolya
        (canonicalPowCoordinate (b.tailBasis).coord j))
    (a c : ℤ) (x : Fin (n + 1) → ℤ) :
    b.canonicalPowCandidate (canonicalPowParameters (a + c) x) =
      b.canonicalPowCandidate (canonicalPowParameters a x) *
        b.canonicalPowCandidate (canonicalPowParameters c x) := by
  let coords :
      (Option (Option (Fin (n + 1))) → ℤ) → (Fin (n + 1) → ℤ) :=
    fun z i => z (some (some i))
  let leftInput :
      (Option (Option (Fin (n + 1))) → ℤ) →
        (Option (Fin (n + 1)) → ℤ) :=
    fun z => canonicalPowParameters (z none) (coords z)
  let rightInput :
      (Option (Option (Fin (n + 1))) → ℤ) →
        (Option (Fin (n + 1)) → ℤ) :=
    fun z => canonicalPowParameters (z (some none)) (coords z)
  let sumInput :
      (Option (Option (Fin (n + 1))) → ℤ) →
        (Option (Fin (n + 1)) → ℤ) :=
    fun z => canonicalPowParameters (z none + z (some none)) (coords z)
  have hcoords :
      CIValued coords := by
    intro i
    exact integer_valued_polynomial (some (some i))
  have hleftInput :
      CIValued leftInput := by
    intro i
    cases i with
    | none => exact integer_valued_polynomial none
    | some i => exact hcoords i
  have hrightInput :
      CIValued rightInput := by
    intro i
    cases i with
    | none => exact integer_valued_polynomial (some none)
    | some i => exact hcoords i
  have hsumInput :
      CIValued sumInput := by
    intro i
    cases i with
    | none =>
        exact (integer_valued_polynomial none).add
          (integer_valued_polynomial (some none))
    | some i => exact hcoords i
  have hcandidate :=
    b.candid_coord_coord
      hmul htailMul htailPow
  have hlhs := hcandidate.comp hsumInput
  have hleft := hcandidate.comp hleftInput
  have hright := hcandidate.comp hrightInput
  have hrhs := b.polynomialElement_mul hmul hleft hright
  apply b.coord.injective
  funext j
  let S : Option (Option (Fin (n + 1))) → Set ℤ
    | none => Set.Ioi 0
    | some none => Set.Ioi 0
    | some (some _) => Set.univ
  have hS : ∀ i, (S i).Infinite := by
    intro i
    rcases i with (_ | _ | i)
    · change (Set.Ioi (0 : ℤ)).Infinite
      exact Set.Ioi_infinite 0
    · change (Set.Ioi (0 : ℤ)).Infinite
      exact Set.Ioi_infinite 0
    · exact Set.infinite_univ
  have heq :=
    IVPolya.eq_eq_infinite
      (hlhs j) (hrhs j) S hS (by
        intro z hz
        have ha : 0 < z none := hz none
        have hc : 0 < z (some none) := hz (some none)
        have hadd : 0 < z none + z (some none) := by omega
        have hgroup :
            b.canonicalPowCandidate (sumInput z) =
              b.canonicalPowCandidate (leftInput z) *
                b.canonicalPowCandidate (rightInput z) := by
          rw [show sumInput z =
              canonicalPowParameters (z none + z (some none)) (coords z) by
                rfl]
          rw [show leftInput z =
              canonicalPowParameters (z none) (coords z) by rfl]
          rw [show rightInput z =
              canonicalPowParameters (z (some none)) (coords z) by rfl]
          rw [b.candidate_zpow_pos (coords z) hadd,
            b.candidate_zpow_pos (coords z) ha,
            b.candidate_zpow_pos (coords z) hc,
            zpow_add]
        exact congrFun (congrArg b.coord hgroup) j)
  have hj := congrFun heq
    (fun
      | none => a
      | some none => c
      | some (some i) => x i)
  simpa [sumInput, leftInput, rightInput, coords] using hj

/-- Hall's polynomial Petresco candidate agrees with ordinary integer
powering for every exponent. -/
theorem canonical_candidate_zpow {n : ℕ}
    (b : HCBasis G (n + 1))
    (hmul :
      ∀ j, IVPolya
        (canonicalMulCoordinate b.coord j))
    (htailMul :
      ∀ j, IVPolya
        (canonicalMulCoordinate (b.tailBasis).coord j))
    (htailPow :
      ∀ j, IVPolya
        (canonicalPowCoordinate (b.tailBasis).coord j))
    (a : ℤ) (x : Fin (n + 1) → ℤ) :
    b.canonicalPowCandidate (canonicalPowParameters a x) =
      (b.coord.symm x) ^ a := by
  let t : ℤ := (a.natAbs : ℤ) + 1
  have ht : 0 < t := by
    dsimp [t]
    omega
  have hat : 0 < a + t := by
    have ha : a ≤ (a.natAbs : ℤ) := Int.le_natAbs
    dsimp [t]
    omega
  have hadd := b.canonical_candidate_add hmul htailMul htailPow a t x
  rw [b.candidate_zpow_pos x hat,
    b.candidate_zpow_pos x ht, zpow_add] at hadd
  exact (mul_right_cancel hadd).symm

/-- Hall's power-coordinate induction step: polynomial multiplication in
the current basis and polynomial multiplication and powering in the first
tail imply polynomial powering in the current basis. -/
theorem pow_coordinates_tail {n : ℕ}
    (b : HCBasis G (n + 1))
    (hmul :
      ∀ j, IVPolya
        (canonicalMulCoordinate b.coord j))
    (htailMul :
      ∀ j, IVPolya
        (canonicalMulCoordinate (b.tailBasis).coord j))
    (htailPow :
      ∀ j, IVPolya
        (canonicalPowCoordinate (b.tailBasis).coord j)) :
    ∀ j, IVPolya
      (canonicalPowCoordinate b.coord j) := by
  intro j
  have hcandidate :=
    b.candid_coord_coord
      hmul htailMul htailPow
  rw [show
    canonicalPowCoordinate b.coord j =
      fun z => b.coord (b.canonicalPowCandidate z) j by
    funext z
    have hpow :=
      b.canonical_candidate_zpow hmul htailMul htailPow
        (z none) (fun i => z (some i))
    exact congrFun (congrArg b.coord (by
      simpa [canonicalPowParameters] using hpow.symm)) j]
  exact hcandidate j

/-- Hall's power-coordinate induction step expressed only through the
simultaneous smaller-length hypothesis. -/
theorem pow_coordinates_smaller {n : ℕ}
    (b : HCBasis G (n + 1))
    (hsmaller :
      ∀ {H : Type u} [Group H] {m : ℕ}, m < n + 1 →
        (c : HCBasis H m) →
        (∀ j, IVPolya
          (canonicalMulCoordinate c.coord j)) ∧
        ∀ j, IVPolya
          (canonicalPowCoordinate c.coord j)) :
    ∀ j, IVPolya
      (canonicalPowCoordinate b.coord j) := by
  have hmul := b.canonical_coordinates_smaller hsmaller
  have htail := hsmaller (Nat.lt_succ_self n) b.tailBasis
  exact b.pow_coordinates_tail hmul htail.1 htail.2

/-- **Hall, Theorem 6.5.** Multiplication and arbitrary integer powering
have integer-valued polynomial coordinates in every Hall canonical
basis. -/
theorem integer_valued_polynomials {n : ℕ} (b : HCBasis G n) :
    (∀ j, IVPolya
      (canonicalMulCoordinate b.coord j)) ∧
    ∀ j, IVPolya
      (canonicalPowCoordinate b.coord j) := by
  induction n using Nat.strong_induction_on generalizing G with
  | h n ih =>
      cases n with
      | zero =>
          constructor <;> intro j <;> exact Fin.elim0 j
      | succ n =>
          let hsmaller :
              ∀ {H : Type u} [Group H] {m : ℕ}, m < n + 1 →
                (c : HCBasis H m) →
                (∀ j, IVPolya
                  (canonicalMulCoordinate c.coord j)) ∧
                ∀ j, IVPolya
                  (canonicalPowCoordinate c.coord j) :=
            fun {_} [_] {_} hm c => ih _ hm c
          exact
            ⟨b.canonical_coordinates_smaller hsmaller,
              b.pow_coordinates_smaller hsmaller⟩

/-- The first tail conjugation coordinate is represented by a
compositional binomial expression. -/
theorem conjugate_tail_expression {n : ℕ}
    (b : HCBasis G (n + 2)) :
    IEMap (b.conjugateTailCoordinate 0) := by
  have h :
      IEMap
        (fun z : Option (Fin (n + 1)) → ℤ => z (some 0)) :=
    binomial_expression _
  rw [show b.conjugateTailCoordinate 0 =
    (fun z : Option (Fin (n + 1)) → ℤ => z (some 0)) by
      funext z
      exact b.conjugate_tail_zero z]
  exact h

/-- Expression-valued analogue of the head-plus-suffix correction
coordinate construction. -/
theorem head_suffix_expression
    {n : ℕ} (b : HCBasis G (n + 1)) (i : Fin n)
    (hmul :
      ∀ j, IEMap
        (canonicalMulCoordinate
          (b.headSuffixBasis ((i : ℕ) + 2) (by omega) (by omega)).coord j))
    (hpow :
      ∀ j, IEMap
        (canonicalPowCoordinate
          (b.headSuffixBasis ((i : ℕ) + 2) (by omega) (by omega)).coord j)) :
    CBExpr
      (fun z : (Option (Fin n) → ℤ) =>
        (b.headSuffixBasis ((i : ℕ) + 2) (by omega) (by omega)).coord
          (b.conjugateHeadSuffix i (z none))) := by
  let hb := b.headSuffixBasis ((i : ℕ) + 2) (by omega) (by omega)
  let head : b.headSuffixSubgroup ((i : ℕ) + 2) :=
    ⟨b.generators 0, b.head_suffix_subgroup ((i : ℕ) + 2)⟩
  let c : b.headSuffixSubgroup ((i : ℕ) + 2) :=
    ⟨b.generators i.succ * b.generators 0 * (b.generators i.succ)⁻¹,
      b.conjugated_head_suffix i⟩
  have ha :
      IEMap
        (fun z : Option (Fin n) → ℤ => z none) :=
    binomial_expression _
  have hhead :
      CBExpr
        (fun _ : Option (Fin n) → ℤ => hb.coord head) := by
    intro j
    exact binomial_expression_const _
  have hc :
      CBExpr
        (fun _ : Option (Fin n) → ℤ => hb.coord c) := by
    intro j
    exact binomial_expression_const _
  have hleft :=
    coordinatewise_expression_pow hb.coord hpow
      ha.neg hhead
  have hright :=
    coordinatewise_expression_pow hb.coord hpow
      ha hc
  have hproduct :=
    coordinatewise_expression_canonical hb.coord hmul
      hleft hright
  have heq :
      (fun z : Option (Fin n) → ℤ =>
        hb.coord (b.conjugateHeadSuffix i (z none))) =
        (fun z : Option (Fin n) → ℤ =>
          hb.coord (head ^ (-(z none)) * c ^ (z none))) := by
    funext z
    apply congrArg hb.coord
    apply Subtype.ext
    simp only [conjugateHeadSuffix, head, c,
      Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_zpow, Subgroup.coe_mk,
      zpow_neg]
  rw [heq]
  simpa only [Equiv.symm_apply_apply] using hproduct

/-- Expression-valued correction coordinates in the first tail basis. -/
theorem conjugate_binomial_expression
    {n : ℕ} (b : HCBasis G (n + 1)) (i : Fin n)
    (hmul :
      ∀ j, IEMap
        (canonicalMulCoordinate
          (b.headSuffixBasis ((i : ℕ) + 2) (by omega) (by omega)).coord j))
    (hpow :
      ∀ j, IEMap
        (canonicalPowCoordinate
          (b.headSuffixBasis ((i : ℕ) + 2) (by omega) (by omega)).coord j)) :
    CBExpr
      (fun z : (Option (Fin n) → ℤ) =>
        (b.tailBasis).coord (b.conjugateGeneratorCorrection i (z none))) := by
  have hheadSuffix :=
    b.head_suffix_expression
      i hmul hpow
  intro j
  by_cases hj : (j : ℕ) < (i : ℕ) + 1
  · rw [show
      (fun z : Option (Fin n) → ℤ =>
        (b.tailBasis).coord (b.conjugateGeneratorCorrection i (z none)) j) =
          (fun _ : Option (Fin n) → ℤ => 0) by
      funext z
      exact b.tail_coord_conjugate
        i j hj (z none)]
    exact binomial_expression_const 0
  · have hji : (i : ℕ) + 1 ≤ (j : ℕ) := by omega
    rw [show
      (fun z : Option (Fin n) → ℤ =>
        (b.tailBasis).coord (b.conjugateGeneratorCorrection i (z none)) j) =
          (fun z : Option (Fin n) → ℤ =>
            (b.headSuffixBasis ((i : ℕ) + 2) (by omega) (by omega)).coord
              (b.conjugateHeadSuffix i (z none))
              ⟨(j : ℕ) - ((i : ℕ) + 1) + 1, by omega⟩) by
      funext z
      exact
        b.conjugate_head_suffix
          i j hji (z none)]
    exact hheadSuffix ⟨(j : ℕ) - ((i : ℕ) + 1) + 1, by omega⟩

/-- Expression-valued coordinates for one conjugated later generator. -/
theorem conjugate_coordinatewise_expression
    {n : ℕ} (b : HCBasis G (n + 1)) (i : Fin n)
    (htailMul :
      ∀ j, IEMap
        (canonicalMulCoordinate (b.tailBasis).coord j))
    (hmul :
      ∀ j, IEMap
        (canonicalMulCoordinate
          (b.headSuffixBasis ((i : ℕ) + 2) (by omega) (by omega)).coord j))
    (hpow :
      ∀ j, IEMap
        (canonicalPowCoordinate
          (b.headSuffixBasis ((i : ℕ) + 2) (by omega) (by omega)).coord j)) :
    CBExpr
      (fun z : (Option (Fin n) → ℤ) =>
        (b.tailBasis).coord (b.conjugateGeneratorTail i (z none))) := by
  have hcorrection :=
    b.conjugate_binomial_expression
      i hmul hpow
  have hgenerator :
      CBExpr
        (fun _ : Option (Fin n) → ℤ =>
          (b.tailBasis).coord
            ⟨b.generators i.succ,
              b.generator_tail (by omega) i.succ (by simp)⟩) := by
    intro j
    exact binomial_expression_const _
  have hproduct :=
    coordinatewise_expression_canonical
      (b.tailBasis).coord htailMul hcorrection hgenerator
  have heq :
      (fun z : Option (Fin n) → ℤ =>
        (b.tailBasis).coord (b.conjugateGeneratorTail i (z none))) =
        (fun z : Option (Fin n) → ℤ =>
          (b.tailBasis).coord
            (b.conjugateGeneratorCorrection i (z none) *
              ⟨b.generators i.succ,
                b.generator_tail (by omega) i.succ (by simp)⟩)) := by
    funext z
    rw [b.conjugate_generator_tail]
  rw [heq]
  simpa only [Equiv.symm_apply_apply] using hproduct

/-- Expression-valued coordinates for finite ordered products of
conjugated generator powers. -/
theorem conjug_coord_expre
    {n : ℕ} (b : HCBasis G (n + 1))
    (htailMul :
      ∀ j, IEMap
        (canonicalMulCoordinate (b.tailBasis).coord j))
    (htailPow :
      ∀ j, IEMap
        (canonicalPowCoordinate (b.tailBasis).coord j))
    (hgenerator :
      ∀ i, CBExpr
        (fun z : Option (Fin n) → ℤ =>
          (b.tailBasis).coord (b.conjugateGeneratorTail i (z none)))) :
    ∀ l : List (Fin n),
      CBExpr
        (fun z : Option (Fin n) → ℤ =>
          (b.tailBasis).coord (b.conjugatedGeneratorProduct l z))
  | [] => by
      intro j
      simpa [conjugatedGeneratorProduct, orderedZPow] using
        (binomial_expression_const ((b.tailBasis).coord 1 j) :
          IEMap
            (fun _ : Option (Fin n) → ℤ => (b.tailBasis).coord 1 j))
  | i :: l => by
      have hexponent :
          IEMap
            (fun z : Option (Fin n) → ℤ => z (some i)) :=
        binomial_expression _
      have hpower :=
        coordinatewise_expression_pow
          (b.tailBasis).coord htailPow hexponent (hgenerator i)
      have htail :=
        b.conjug_coord_expre
          htailMul htailPow hgenerator l
      have hproduct :=
        coordinatewise_expression_canonical
          (b.tailBasis).coord htailMul hpower htail
      simpa [conjugatedGeneratorProduct, orderedZPow] using hproduct

/-- Expression-valued coordinates for conjugation of an arbitrary
first-tail element by a power of the head generator. -/
theorem conjugate_coordinates_expression
    {n : ℕ} (b : HCBasis G (n + 1))
    (htailMul :
      ∀ j, IEMap
        (canonicalMulCoordinate (b.tailBasis).coord j))
    (htailPow :
      ∀ j, IEMap
        (canonicalPowCoordinate (b.tailBasis).coord j))
    (hmul :
      ∀ i : Fin n, ∀ j, IEMap
        (canonicalMulCoordinate
          (b.headSuffixBasis ((i : ℕ) + 2) (by omega) (by omega)).coord j))
    (hpow :
      ∀ i : Fin n, ∀ j, IEMap
        (canonicalPowCoordinate
          (b.headSuffixBasis ((i : ℕ) + 2) (by omega) (by omega)).coord j)) :
    CBExpr
      (fun z : Option (Fin n) → ℤ =>
        (b.tailBasis).coord
          (b.conjugateTail (z none)
            ((b.tailBasis).coord.symm fun i ↦ z (some i)))) := by
  have hgenerator :
      ∀ i, CBExpr
        (fun z : Option (Fin n) → ℤ =>
          (b.tailBasis).coord (b.conjugateGeneratorTail i (z none))) :=
    fun i ↦
      b.conjugate_coordinatewise_expression
        i htailMul (hmul i) (hpow i)
  have hproduct :=
    b.conjug_coord_expre
      htailMul htailPow hgenerator (List.finRange n)
  rw [show
    (fun z : Option (Fin n) → ℤ =>
      (b.tailBasis).coord
        (b.conjugateTail (z none)
          ((b.tailBasis).coord.symm fun i ↦ z (some i)))) =
      (fun z : Option (Fin n) → ℤ =>
        (b.tailBasis).coord
          (b.conjugatedGeneratorProduct (List.finRange n) z)) by
    funext z
    rw [b.conjugate_tail_conjugated]]
  exact hproduct

/-- Coordinate form of the expression-valued tail-conjugation theorem. -/
theorem tail_coordinates_expression
    {n : ℕ} (b : HCBasis G (n + 1))
    (htailMul :
      ∀ j, IEMap
        (canonicalMulCoordinate (b.tailBasis).coord j))
    (htailPow :
      ∀ j, IEMap
        (canonicalPowCoordinate (b.tailBasis).coord j))
    (hmul :
      ∀ i : Fin n, ∀ j, IEMap
        (canonicalMulCoordinate
          (b.headSuffixBasis ((i : ℕ) + 2) (by omega) (by omega)).coord j))
    (hpow :
      ∀ i : Fin n, ∀ j, IEMap
        (canonicalPowCoordinate
          (b.headSuffixBasis ((i : ℕ) + 2) (by omega) (by omega)).coord j)) :
    ∀ j, IEMap (b.conjugateTailCoordinate j) := by
  have h :=
    b.conjugate_coordinates_expression
      htailMul htailPow hmul hpow
  intro j
  exact h j

/-- Expression-valued multiplication coordinates lift from the first
tail and the tail-conjugation coordinates. -/
theorem coordinates_binomial_expression {n : ℕ}
    (b : HCBasis G (n + 1))
    (htail :
      ∀ i, IEMap
        (canonicalMulCoordinate (b.tailBasis).coord i))
    (hconj :
      ∀ i, IEMap (b.conjugateTailCoordinate i)) :
    ∀ i, IEMap (canonicalMulCoordinate b.coord i) := by
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact b.canonical_binomial_polynomial
      |>.binomial_expression_map
  · let leftTail :
        (Sum (Fin (n + 1)) (Fin (n + 1)) → ℤ) → (Fin n → ℤ) :=
      fun z j => z (Sum.inl j.succ)
    let rightTail :
        (Sum (Fin (n + 1)) (Fin (n + 1)) → ℤ) → (Fin n → ℤ) :=
      fun z j => z (Sum.inr j.succ)
    let conjugatedLeftTail :
        (Sum (Fin (n + 1)) (Fin (n + 1)) → ℤ) → (Fin n → ℤ) :=
      fun z =>
        (b.tailBasis).coord
          (b.conjugateTail (z (Sum.inr 0))
            ((b.tailBasis).coord.symm (leftTail z)))
    have hleft :
        CBExpr leftTail := by
      intro k
      exact binomial_expression _
    have hright :
        CBExpr rightTail := by
      intro k
      exact binomial_expression _
    have hconjugated :
        CBExpr conjugatedLeftTail := by
      intro k
      have hk := (hconj k).reindex
        (fun z : Option (Fin n) =>
          match z with
          | none => Sum.inr (0 : Fin (n + 1))
          | some l => Sum.inl l.succ)
      simpa [conjugateTailCoordinate, conjugatedLeftTail, leftTail] using hk
    have hproduct :=
      coordinatewise_expression_canonical
        (b.tailBasis).coord htail hconjugated hright
    have hcoord :
        canonicalMulCoordinate b.coord j.succ =
          fun z =>
            (b.tailBasis).coord
              ((b.tailBasis).coord.symm (conjugatedLeftTail z) *
                (b.tailBasis).coord.symm (rightTail z)) j := by
      funext z
      rw [canonicalMulCoordinate]
      have htailcoord := congrFun
        (b.tailCoord_mul (fun k => z (Sum.inl k)) (fun k => z (Sum.inr k))) j
      simpa [conjugatedLeftTail, leftTail, rightTail] using htailcoord
    rw [hcoord]
    exact hproduct j

/-- Hall's multiplication induction step with explicit compositional
binomial expressions. -/
theorem smaller_binomial_expression {n : ℕ}
    (b : HCBasis G (n + 1))
    (hsmaller :
      ∀ {H : Type u} [Group H] {m : ℕ}, m < n + 1 →
        (c : HCBasis H m) →
        (∀ j, IEMap
          (canonicalMulCoordinate c.coord j)) ∧
        ∀ j, IEMap
          (canonicalPowCoordinate c.coord j)) :
    ∀ j, IEMap (canonicalMulCoordinate b.coord j) := by
  have htail :=
    hsmaller (Nat.lt_succ_self n) b.tailBasis
  apply b.coordinates_binomial_expression htail.1
  apply b.tail_coordinates_expression htail.1 htail.2
  · intro i
    exact (hsmaller (by omega)
      (b.headSuffixBasis ((i : ℕ) + 2) (by omega) (by omega))).1
  · intro i
    exact (hsmaller (by omega)
      (b.headSuffixBasis ((i : ℕ) + 2) (by omega) (by omega))).2

/-- Expression-valued coordinates for an ordered product of canonical
generator powers with expression-valued exponents. -/
theorem coordinatewise_binomial_expression
    {n : ℕ} (b : HCBasis G n)
    (hmul :
      ∀ j, IEMap
        (canonicalMulCoordinate b.coord j))
    {κ : Type v} (a : Fin n → (κ → ℤ) → ℤ)
    (ha : ∀ i, IEMap (a i)) :
    ∀ l : List (Fin n),
      CBExpr
        (fun z => b.coord (orderedZPow b.generators (fun i => a i z) l))
  | [] => by
      intro j
      simpa [orderedZPow] using
        (binomial_expression_const (b.coord 1 j) :
          IEMap (fun _ : κ → ℤ => b.coord 1 j))
  | i :: l => by
      have hfactor :
          CBExpr
            (fun z => b.coord (b.generators i ^ a i z)) := by
        intro j
        by_cases hij : i = j
        · subst j
          simpa [b.coord_zpow] using ha i
        · rw [show
            (fun z => b.coord (b.generators i ^ a i z) j) =
              (fun _ : κ → ℤ => 0) by
            funext z
            rw [b.coord_zpow]
            simp [hij]]
          exact binomial_expression_const 0
      have htail :=
        b.coordinatewise_binomial_expression
          hmul a ha l
      have hproduct :=
        coordinatewise_expression_canonical
          b.coord hmul hfactor htail
      simpa [orderedZPow] using hproduct

/-- Expression-valued inverse coordinates. -/
theorem inv_coordinatewise_expression {n : ℕ}
    (b : HCBasis G n)
    (hmul :
      ∀ j, IEMap
        (canonicalMulCoordinate b.coord j)) :
    CBExpr
      (fun x => b.coord ((b.coord.symm x)⁻¹)) := by
  rw [show
    (fun x => b.coord ((b.coord.symm x)⁻¹)) =
      (fun x => b.coord
        (orderedZPow b.generators (fun i => -x i)
          (List.finRange n).reverse)) by
    funext x
    rw [b.inv_basis_reverse]]
  apply b.coordinatewise_binomial_expression
    hmul
  intro i
  exact (binomial_expression i).neg

/-- Pointwise products preserve expression-valued canonical coordinates. -/
theorem binomial_expression_mul {n : ℕ} (b : HCBasis G n)
    (hmul :
      ∀ j, IEMap
        (canonicalMulCoordinate b.coord j))
    {κ : Type v} {f g : (κ → ℤ) → G}
    (hf : CBExpr (fun z => b.coord (f z)))
    (hg : CBExpr (fun z => b.coord (g z))) :
    CBExpr
      (fun z => b.coord (f z * g z)) := by
  simpa only [Equiv.symm_apply_apply] using
    (coordinatewise_expression_canonical
      b.coord hmul hf hg)

/-- Pointwise inverses preserve expression-valued canonical coordinates. -/
theorem binomial_expression_inv {n : ℕ} (b : HCBasis G n)
    (hmul :
      ∀ j, IEMap
        (canonicalMulCoordinate b.coord j))
    {κ : Type v} {f : (κ → ℤ) → G}
    (hf : CBExpr (fun z => b.coord (f z))) :
    CBExpr
      (fun z => b.coord (f z)⁻¹) := by
  have hinv := (b.inv_coordinatewise_expression hmul).comp hf
  simpa only [Equiv.symm_apply_apply] using hinv

/-- Fixed natural powers preserve expression-valued canonical
coordinates. -/
theorem binomial_expression_npow {n : ℕ} (b : HCBasis G n)
    (hmul :
      ∀ j, IEMap
        (canonicalMulCoordinate b.coord j))
    {κ : Type v} {f : (κ → ℤ) → G}
    (hf : CBExpr (fun z => b.coord (f z))) :
    ∀ m : ℕ, CBExpr
      (fun z => b.coord ((f z) ^ m))
  | 0 => by
      intro j
      simpa using
        (binomial_expression_const (b.coord 1 j) :
          IEMap (fun _ : κ → ℤ => b.coord 1 j))
  | m + 1 => by
      rw [show
        (fun z => b.coord ((f z) ^ (m + 1))) =
          (fun z => b.coord ((f z) ^ m * f z)) by
        funext z
        rw [pow_succ]]
      exact b.binomial_expression_mul hmul
        (b.binomial_expression_npow hmul hf m) hf

/-- Finite products preserve expression-valued canonical coordinates. -/
theorem binomial_expression_element {n : ℕ}
    (b : HCBasis G n)
    (hmul :
      ∀ j, IEMap
        (canonicalMulCoordinate b.coord j))
    {κ X : Type*} {f : X → (κ → ℤ) → G}
    (hf : ∀ i, CBExpr
      (fun z => b.coord (f i z))) :
    ∀ l : List X, CBExpr
      (fun z => b.coord ((l.map fun i => f i z).prod))
  | [] => by
      intro j
      simpa using
        (binomial_expression_const (b.coord 1 j) :
          IEMap (fun _ : κ → ℤ => b.coord 1 j))
  | i :: l => by
      simpa only [List.map_cons, List.prod_cons] using
        b.binomial_expression_mul hmul (hf i)
          (b.binomial_expression_element hmul hf l)

/-- Recursive Petresco terms preserve expression-valued canonical
coordinates. -/
theorem petresco_binomial_expression
    {n : ℕ} (b : HCBasis G n)
    (hmul :
      ∀ j, IEMap
        (canonicalMulCoordinate b.coord j))
    {κ X : Type*} (f : X → (κ → ℤ) → G)
    (hf : ∀ i, CBExpr
      (fun z => b.coord (f i z)))
    (l : List X) :
    ∀ w : ℕ, CBExpr
      (fun z => b.coord (petrescoTerm (l.map fun i => f i z) w)) := by
  intro w
  induction w using Nat.strong_induction_on with
  | h w ih =>
      cases w with
      | zero =>
          intro j
          simpa using
            (binomial_expression_const (b.coord 1 j) :
              IEMap (fun _ : κ → ℤ => b.coord 1 j))
      | succ w =>
          have hpriorFactors :
              ∀ j : Fin w, CBExpr
                (fun z => b.coord
                  ((petrescoTerm (l.map fun i => f i z) ((j : ℕ) + 1)) ^
                    Nat.choose (w + 1) ((j : ℕ) + 1))) := by
            intro j
            exact b.binomial_expression_npow hmul
              (ih ((j : ℕ) + 1) (by omega))
              (Nat.choose (w + 1) ((j : ℕ) + 1))
          have hpriorProduct :=
            b.binomial_expression_element hmul hpriorFactors
              (List.finRange w)
          have hpriorInv :=
            b.binomial_expression_inv hmul hpriorProduct
          have hinputPowers :
              ∀ i, CBExpr
                (fun z => b.coord ((f i z) ^ (w + 1))) := by
            intro i
            exact b.binomial_expression_npow hmul (hf i) (w + 1)
          have hinputProduct :=
            b.binomial_expression_element hmul hinputPowers l
          have hproduct :=
            b.binomial_expression_mul hmul hpriorInv hinputProduct
          rw [show
            (fun z => b.coord
              (petrescoTerm (l.map fun i => f i z) (w + 1))) =
              (fun z => b.coord
                ((petrescoPriorProduct
                    (petrescoTerm (l.map fun i => f i z)) (w + 1))⁻¹ *
                  ((l.map fun i => f i z).map fun g => g ^ (w + 1)).prod)) by
            funext z
            rw [petrescoTerm_succ]]
          unfold petrescoPriorProduct
          simpa only [Nat.add_sub_cancel, List.map_map] using hproduct

/-- An individual generalized binomial coefficient is represented by a
compositional binomial expression. -/
theorem choose_binomial_expression
    {κ : Type*} (i : κ) (m : ℕ) :
    IEMap
      (fun z : κ → ℤ => Ring.choose (z i) m) :=
  (binomial_expression i).choose m

/-- Variable integer powers preserve expression-valued canonical
coordinates when the basis power coordinates are expression-valued. -/
theorem binomial_expression_zpow {n : ℕ} (b : HCBasis G n)
    (hpow :
      ∀ j, IEMap
        (canonicalPowCoordinate b.coord j))
    {κ : Type v} {f : (κ → ℤ) → G} {a : (κ → ℤ) → ℤ}
    (hf : CBExpr (fun z => b.coord (f z)))
    (ha : IEMap a) :
    CBExpr
      (fun z => b.coord ((f z) ^ (a z))) := by
  simpa only [Equiv.symm_apply_apply] using
    (coordinatewise_expression_pow
      b.coord hpow ha hf)

/-- Variable powers of one canonical generator have expression-valued
canonical coordinates. -/
theorem canonical_coordinatewise_expression
    {n : ℕ} (b : HCBasis G n) (i : Fin n) :
    CBExpr
      (fun z : Option (Fin n) → ℤ =>
        b.coord (b.generators i ^ z (some i))) := by
  intro j
  by_cases hij : i = j
  · subst j
    simpa [b.coord_zpow] using
      (binomial_expression (some i) :
        IEMap
          (fun z : Option (Fin n) → ℤ => z (some i)))
  · rw [show
      (fun z : Option (Fin n) → ℤ =>
        b.coord (b.generators i ^ z (some i)) j) =
        (fun _ : Option (Fin n) → ℤ => 0) by
      funext z
      rw [b.coord_zpow]
      simp [hij]]
    exact binomial_expression_const 0

/-- Expression-valued coordinates in the first tail imply
expression-valued ambient coordinates. -/
theorem tail_coordinatewise_expression
    {n : ℕ} (b : HCBasis G (n + 1))
    {κ : Type v} {f : (κ → ℤ) → b.tail 1}
    (hf : CBExpr
      (fun z => (b.tailBasis).coord (f z))) :
    CBExpr
      (fun z => b.coord (f z : G)) := by
  intro j
  cases j using Fin.cases with
  | zero =>
      rw [show
        (fun z => b.coord (f z : G) 0) =
          (fun _ : κ → ℤ => 0) by
        funext z
        exact (b.mem_tail_iff (show 1 ≤ n + 1 by omega)).mp
          (f z).property (0 : Fin (n + 1)) (by simp)]
      exact binomial_expression_const 0
  | succ j =>
      exact hf j

/-- The finite Petresco tail correction has expression-valued
coordinates. -/
theorem petresco_coordinatewise_expression
    {n : ℕ} (b : HCBasis G (n + 1))
    (hmul :
      ∀ j, IEMap
        (canonicalMulCoordinate b.coord j))
    (htailMul :
      ∀ j, IEMap
        (canonicalMulCoordinate (b.tailBasis).coord j))
    (htailPow :
      ∀ j, IEMap
        (canonicalPowCoordinate (b.tailBasis).coord j)) :
    CBExpr
      (fun z => (b.tailBasis).coord (b.canonicalPetrescoCorrection z)) := by
  have hpetresco :
      ∀ w : ℕ, CBExpr
        (fun z : Option (Fin (n + 1)) → ℤ =>
          b.coord (petrescoTerm (b.canonicalPowerFactors z) w)) := by
    intro w
    exact b.petresco_binomial_expression hmul
      (fun i z => b.generators i ^ z (some i))
      (fun i =>
        b.canonical_coordinatewise_expression i)
      (List.finRange (n + 1)) w
  have htailTerm :
      ∀ j : ℕ, CBExpr
        (fun z : Option (Fin (n + 1)) → ℤ =>
          (b.tailBasis).coord
            (b.canonicalPetrescoTerm z (j + 2) (by omega))) := by
    intro j k
    exact hpetresco (j + 2) k.succ
  apply (b.tailBasis).binomial_expression_element htailMul
  intro j
  apply (b.tailBasis).binomial_expression_zpow htailPow (htailTerm j)
  exact choose_binomial_expression none (j + 2)

/-- Hall's rearranged Petresco power candidate has expression-valued
ambient canonical coordinates. -/
theorem candidate_coordinatewise_expression
    {n : ℕ} (b : HCBasis G (n + 1))
    (hmul :
      ∀ j, IEMap
        (canonicalMulCoordinate b.coord j))
    (htailMul :
      ∀ j, IEMap
        (canonicalMulCoordinate (b.tailBasis).coord j))
    (htailPow :
      ∀ j, IEMap
        (canonicalPowCoordinate (b.tailBasis).coord j)) :
    CBExpr
      (fun z => b.coord (b.canonicalPowCandidate z)) := by
  have hbase :
      CBExpr
        (fun z : Option (Fin (n + 1)) → ℤ =>
          b.coord
            (orderedZPow b.generators
              (fun i => z none * z (some i)) (List.finRange (n + 1)))) := by
    apply b.coordinatewise_binomial_expression
      hmul
    intro i
    exact (binomial_expression none).mul
      (binomial_expression (some i))
  have hcorrectionTail :=
    b.petresco_coordinatewise_expression
      hmul htailMul htailPow
  have hcorrection :
      CBExpr
        (fun z : Option (Fin (n + 1)) → ℤ =>
          b.coord ((b.canonicalPetrescoCorrection z : G)⁻¹)) := by
    apply b.binomial_expression_inv hmul
    exact b.tail_coordinatewise_expression
      hcorrectionTail
  exact b.binomial_expression_mul hmul hbase hcorrection

/-- Hall's power-coordinate induction step with explicit compositional
binomial expressions. -/
theorem canonical_binomial_expression {n : ℕ}
    (b : HCBasis G (n + 1))
    (hmul :
      ∀ j, IEMap
        (canonicalMulCoordinate b.coord j))
    (htailMul :
      ∀ j, IEMap
        (canonicalMulCoordinate (b.tailBasis).coord j))
    (htailPow :
      ∀ j, IEMap
        (canonicalPowCoordinate (b.tailBasis).coord j)) :
    ∀ j, IEMap
      (canonicalPowCoordinate b.coord j) := by
  intro j
  have hcandidate :=
    b.candidate_coordinatewise_expression
      hmul htailMul htailPow
  rw [show
    canonicalPowCoordinate b.coord j =
      fun z => b.coord (b.canonicalPowCandidate z) j by
    funext z
    have hpow :=
      b.canonical_candidate_zpow
        (fun i => (hmul i).integer_valued_polymap)
        (fun i => (htailMul i).integer_valued_polymap)
        (fun i => (htailPow i).integer_valued_polymap)
        (z none) (fun i => z (some i))
    exact congrFun (congrArg b.coord (by
      simpa [canonicalPowParameters] using hpow.symm)) j]
  exact hcandidate j

/-- Hall's expression-valued power induction step expressed through the
simultaneous smaller-length hypothesis. -/
theorem coordinates_smaller_expression {n : ℕ}
    (b : HCBasis G (n + 1))
    (hsmaller :
      ∀ {H : Type u} [Group H] {m : ℕ}, m < n + 1 →
        (c : HCBasis H m) →
        (∀ j, IEMap
          (canonicalMulCoordinate c.coord j)) ∧
        ∀ j, IEMap
          (canonicalPowCoordinate c.coord j)) :
    ∀ j, IEMap
      (canonicalPowCoordinate b.coord j) := by
  have hmul := b.smaller_binomial_expression
    hsmaller
  have htail := hsmaller (Nat.lt_succ_self n) b.tailBasis
  exact b.canonical_binomial_expression
    hmul htail.1 htail.2

/-- Strengthened form of Hall's Theorem 6.5: multiplication and arbitrary
integer powering are represented by compositional binomial expressions.
These expressions can be evaluated in every binomial ring. -/
theorem canonical_coordinate_expressions {n : ℕ}
    (b : HCBasis G n) :
    (∀ j, IEMap
      (canonicalMulCoordinate b.coord j)) ∧
    ∀ j, IEMap
      (canonicalPowCoordinate b.coord j) := by
  induction n using Nat.strong_induction_on generalizing G with
  | h n ih =>
      cases n with
      | zero =>
          constructor <;> intro j <;> exact Fin.elim0 j
      | succ n =>
          let hsmaller :
              ∀ {H : Type u} [Group H] {m : ℕ}, m < n + 1 →
                (c : HCBasis H m) →
                (∀ j, IEMap
                  (canonicalMulCoordinate c.coord j)) ∧
                ∀ j, IEMap
                  (canonicalPowCoordinate c.coord j) :=
            fun {_} [_] {_} hm c => ih _ hm c
          exact
            ⟨b.smaller_binomial_expression
                hsmaller,
              b.coordinates_smaller_expression
                hsmaller⟩

/-- Multiplication coordinates are polynomial for every two-generator
canonical basis. This is the first nontrivial instance of the recursive
lifting theorem. -/
theorem coordinates_fin_two (b : HCBasis G 2) :
    ∀ i, IVPolya (canonicalMulCoordinate b.coord i) := by
  apply b.canonical_coordinates_tail
  · intro i
    rw [show i = 0 by exact Fin.eq_zero i]
    exact (b.tailBasis).canonical_binomial_polynomial
      |>.integer_valued_polymap
  · intro i
    rw [show i = 0 by exact Fin.eq_zero i]
    exact b.conjugate_integer_valued

/-- In a two-generator canonical basis, the first tail subgroup is central. -/
lemma tail_commute_fin (b : HCBasis G 2)
    (k : b.tail 1) (g : G) :
    Commute (k : G) g := by
  apply commutatorElement_eq_one_iff_commute.mp
  apply Subgroup.mem_bot.mp
  rw [← b.tail_length]
  apply b.tail_central 1
  exact Subgroup.commutator_mem_commutator k.property (Subgroup.mem_top g)

/-- In a two-generator canonical basis, integer powers multiply both
canonical parameters by the exponent. -/
lemma coord_zpow_two (b : HCBasis G 2)
    (x : Fin 2 → ℤ) (a : ℤ) :
    b.coord ((b.coord.symm x) ^ a) = fun i => a * x i := by
  apply b.coord.symm.injective
  rw [b.coord.symm_apply_apply]
  rw [b.symm_head_tail (x := x)]
  rw [b.symm_head_tail (x := fun i => a * x i)]
  rw [(b.tail_commute_fin
    (b.tailCoordEquiv.symm (Fin.tail x)) (b.generators 0 ^ x 0)).symm.mul_zpow]
  rw [← zpow_mul, mul_comm (x 0) a]
  congr 1
  rw [← Subgroup.coe_zpow]
  apply congrArg Subtype.val
  apply (b.tailBasis).coord.injective
  funext i
  change
    (b.tailBasis).coord
        (((b.tailBasis).coord.symm (Fin.tail x)) ^ a) i =
      (b.tailBasis).coord
        ((b.tailBasis).coord.symm (Fin.tail fun i => a * x i)) i
  rw [show i = 0 by exact Fin.eq_zero i]
  rw [(b.tailBasis).coord_zpow_fin]
  rw [(b.tailBasis).coord.apply_symm_apply]
  rfl

/-- Power coordinates are polynomial for every two-generator canonical
basis. -/
theorem canonical_coordinates_fin (b : HCBasis G 2) :
    ∀ i, IVPolya (canonicalPowCoordinate b.coord i) := by
  intro i
  have ha :
      IVPolya
        (fun z : Option (Fin 2) → ℤ => z none) :=
    integer_valued_polynomial _
  have hx :
      IVPolya
        (fun z : Option (Fin 2) → ℤ => z (some i)) :=
    integer_valued_polynomial _
  have hcoord :
      canonicalPowCoordinate b.coord i =
        fun z : Option (Fin 2) → ℤ => z none * z (some i) := by
    funext z
    rw [canonicalPowCoordinate, b.coord_zpow_two]
  rw [hcoord]
  exact ha.mul hx

/-- Hall's multiplication and power coordinate conclusion for every
two-generator canonical basis. -/
theorem polynomials_fin_two (b : HCBasis G 2) :
    (∀ i, IVPolya (canonicalMulCoordinate b.coord i)) ∧
      ∀ i, IVPolya (canonicalPowCoordinate b.coord i) :=
  ⟨b.coordinates_fin_two, b.canonical_coordinates_fin⟩

/-- The empty canonical basis has no coordinate assertions to prove. -/
theorem canonical_polynomials_fin (b : HCBasis G 0) :
    (∀ i, IBMap (canonicalMulCoordinate b.coord i)) ∧
      ∀ i, IBMap (canonicalPowCoordinate b.coord i) := by
  constructor <;> intro i <;> exact Fin.elim0 i

/-- Hall's canonical-coordinate theorem for a one-generator canonical
basis. Multiplication adds exponents and integer powering multiplies them. -/
theorem canonical_coordinate_polynomials (b : HCBasis G 1) :
    (∀ i, IBMap (canonicalMulCoordinate b.coord i)) ∧
      ∀ i, IBMap (canonicalPowCoordinate b.coord i) := by
  constructor
  · intro i
    rw [show i = 0 by exact Fin.eq_zero i]
    have hleft :
        IBMap
          (fun z : Sum (Fin 1) (Fin 1) → ℤ => z (Sum.inl 0)) :=
      binomial_polynomial _
    have hright :
        IBMap
          (fun z : Sum (Fin 1) (Fin 1) → ℤ => z (Sum.inr 0)) :=
      binomial_polynomial _
    have hcoord :
        canonicalMulCoordinate b.coord 0 =
          fun z : Sum (Fin 1) (Fin 1) → ℤ =>
            z (Sum.inl 0) + z (Sum.inr 0) := by
      funext z
      exact b.coord_fin_one
        (fun j => z (Sum.inl j)) (fun j => z (Sum.inr j))
    rw [hcoord]
    exact hleft.add hright
  · intro i
    rw [show i = 0 by exact Fin.eq_zero i]
    have ha :
        IBMap
          (fun z : Option (Fin 1) → ℤ => z none) :=
      binomial_polynomial _
    have hx :
        IBMap
          (fun z : Option (Fin 1) → ℤ => z (some 0)) :=
      binomial_polynomial _
    have hcoord :
        canonicalPowCoordinate b.coord 0 =
          fun z : Option (Fin 1) → ℤ => z none * z (some 0) := by
      funext z
      exact b.coord_zpow_fin (fun j => z (some j)) (z none)
    rw [hcoord]
    exact ha.mul hx

end HCBasis

/-- Package supplied binomial-coordinate proofs for multiplication and
integer powers. The substantive canonical-basis induction for Hall's
Theorem 6.5 is developed above. -/
theorem polynomials_binomial_coordinates {ι : Type*}
    (coord : G ≃ (ι → ℤ))
    (hmul :
      ∀ i, IBMap (canonicalMulCoordinate coord i))
    (hpow :
      ∀ i, IBMap (canonicalPowCoordinate coord i)) :
    (∀ i, IBMap (canonicalMulCoordinate coord i)) ∧
      ∀ i, IBMap (canonicalPowCoordinate coord i) :=
  ⟨hmul, hpow⟩

/-- Evaluation form of the multiplication-coordinate assertion in
Theorem 6.5. -/
theorem canonical_coordinate_polynomial {ι : Type*}
    (coord : G ≃ (ι → ℤ)) (i : ι)
    (h : IVPolya (canonicalMulCoordinate coord i)) :
    ∃ p : MvPolynomial (Sum ι ι) ℚ, ∀ (x y : ι → ℤ),
      MvPolynomial.eval (fun j => ((Sum.elim x y j : ℤ) : ℚ)) p =
        (coord (coord.symm x * coord.symm y) i : ℚ) := by
  obtain ⟨p, hp⟩ := h
  refine ⟨p, fun x y => ?_⟩
  simpa [canonicalMulCoordinate] using hp (Sum.elim x y)

/-- Evaluation form of the power-coordinate assertion in Theorem 6.5. -/
theorem canonical_pow_coordinate {ι : Type*}
    (coord : G ≃ (ι → ℤ)) (i : ι)
    (h : IVPolya (canonicalPowCoordinate coord i)) :
    ∃ p : MvPolynomial (Option ι) ℚ, ∀ (x : ι → ℤ) (a : ℤ),
      MvPolynomial.eval
          (fun j => (canonicalPowAssignment a x j : ℚ)) p =
        (coord ((coord.symm x) ^ a) i : ℚ) := by
  obtain ⟨p, hp⟩ := h
  refine ⟨p, fun x a => ?_⟩
  simpa [canonicalPowCoordinate, canonicalPowAssignment] using
    hp (canonicalPowAssignment a x)

/-- Hall's coordinate completion over a binomial ring. The basis remains
an index of the type so that distinct canonical bases induce distinct
completion group instances. -/
structure HComp {n : ℕ} (b : HCBasis G n) (ν : Type v)
    where
  coord : Fin n → ν

namespace HCBasis

/-- A selected compositional expression for each multiplication
coordinate. -/
noncomputable def mulExpression {n : ℕ} (b : HCBasis G n)
    (i : Fin n) :
    BExpr (Sum (Fin n) (Fin n)) :=
  Classical.choose (b.canonical_coordinate_expressions.1 i)

/-- The selected multiplication expression agrees with the original
integer coordinate operation. -/
lemma eval_expression_int {n : ℕ} (b : HCBasis G n)
    (i : Fin n) (z : Sum (Fin n) (Fin n) → ℤ) :
    BExpr.eval z (b.mulExpression i) =
      canonicalMulCoordinate b.coord i z :=
  Classical.choose_spec (b.canonical_coordinate_expressions.1 i) z

/-- A selected compositional expression for each integer-power
coordinate. -/
noncomputable def powExpression {n : ℕ} (b : HCBasis G n)
    (i : Fin n) :
    BExpr (Option (Fin n)) :=
  Classical.choose (b.canonical_coordinate_expressions.2 i)

/-- The selected power expression agrees with the original integer
coordinate operation. -/
lemma pow_expression_int {n : ℕ} (b : HCBasis G n)
    (i : Fin n) (z : Option (Fin n) → ℤ) :
    BExpr.eval z (b.powExpression i) =
      canonicalPowCoordinate b.coord i z :=
  Classical.choose_spec (b.canonical_coordinate_expressions.2 i) z

end HCBasis

namespace HComp

instance {n : ℕ} {b : HCBasis G n} {ν : Type v} :
    CoeFun (HComp b ν) fun _ => Fin n → ν :=
  ⟨HComp.coord⟩

@[ext]
lemma ext {n : ℕ} {b : HCBasis G n} {ν : Type v}
    {x y : HComp b ν} (h : ∀ i, x.coord i = y.coord i) :
    x = y := by
  cases x with
  | mk x =>
      cases y with
      | mk y =>
          congr
          funext i
          exact h i

/-- Evaluate a tuple of compositional expressions coordinatewise. -/
def evalTuple {ι κ R : Type*} [CommRing R] [BinomialRing R]
    (x : κ → R) (p : ι → BExpr κ) : ι → R :=
  fun i => BExpr.eval x (p i)

/-- The tuple of variable expressions selected by an index map. -/
def varTuple {ι κ : Type*} (e : ι → κ) : ι → BExpr κ :=
  fun i => .var (e i)

/-- The constant tuple given by the integer coordinates of the identity
element. -/
def oneTuple {n : ℕ} (b : HCBasis G n) {κ : Type*} :
    Fin n → BExpr κ :=
  fun i => .const (b.coord 1 i)

/-- Substitute expression-valued coordinate tuples into Hall's selected
multiplication formulas. -/
noncomputable def mulTuple {n : ℕ} (b : HCBasis G n)
    {κ : Type*} (x y : Fin n → BExpr κ) :
    Fin n → BExpr κ :=
  fun i => (b.mulExpression i).substitute (Sum.elim x y)

/-- Substitute an expression-valued scalar and coordinate tuple into
Hall's selected power formulas. -/
noncomputable def powTuple {n : ℕ} (b : HCBasis G n)
    {κ : Type*} (a : BExpr κ)
    (x : Fin n → BExpr κ) :
    Fin n → BExpr κ :=
  fun i => (b.powExpression i).substitute fun
    | none => a
    | some j => x j

/-- Evaluate Hall's selected multiplication formulas in an arbitrary
binomial ring. -/
noncomputable def mul {n : ℕ} (b : HCBasis G n)
    {ν : Type v} [CommRing ν] [BinomialRing ν]
    (x y : HComp b ν) : HComp b ν :=
  ⟨evalTuple (Sum.elim x.coord y.coord) fun i => b.mulExpression i⟩

/-- Evaluate Hall's selected power formulas in an arbitrary binomial
ring. -/
noncomputable def pow {n : ℕ} (b : HCBasis G n)
    {ν : Type v} [CommRing ν] [BinomialRing ν]
    (x : HComp b ν) (a : ν) : HComp b ν :=
  ⟨evalTuple
    (fun z => match z with
      | none => a
      | some i => x.coord i)
    fun i => b.powExpression i⟩

/-- The completion identity is the cast of the integer coordinate tuple
of the original group identity. -/
def one {n : ℕ} (b : HCBasis G n)
    {ν : Type v} [CommRing ν] :
    HComp b ν :=
  ⟨fun i => (b.coord 1 i : ν)⟩

/-- Completion inversion is evaluation of Hall's power formula at
the scalar `-1`. -/
noncomputable def inv {n : ℕ} (b : HCBasis G n)
    {ν : Type v} [CommRing ν] [BinomialRing ν]
    (x : HComp b ν) : HComp b ν :=
  pow b x (-1)

@[simp]
lemma eval_tuple_var {ι κ R : Type*} [CommRing R] [BinomialRing R]
    (x : κ → R) (e : ι → κ) :
    evalTuple x (varTuple e) = fun i => x (e i) :=
  rfl

@[simp]
lemma eval_tuple_one {n : ℕ} (b : HCBasis G n)
    {κ R : Type*} [CommRing R] [BinomialRing R] (x : κ → R) :
    evalTuple x (oneTuple b : Fin n → BExpr κ) =
      (one b).coord := by
  funext i
  simp [evalTuple, oneTuple, one]

@[simp]
lemma one_int {n : ℕ} (b : HCBasis G n) :
    (one b : HComp b ℤ).coord = b.coord 1 := by
  funext i
  simp [one]

@[simp]
lemma eval_tuple_mul {n : ℕ} (b : HCBasis G n)
    {κ ν : Type*} [CommRing ν] [BinomialRing ν]
    (z : κ → ν) (x y : Fin n → BExpr κ) :
    evalTuple z (mulTuple b x y) =
      (mul b ⟨evalTuple z x⟩ ⟨evalTuple z y⟩).coord := by
  funext i
  simp only [evalTuple, mulTuple, mul, BExpr.eval_substitute]
  congr 1
  funext j
  cases j <;> rfl

@[simp]
lemma eval_tuple_pow {n : ℕ} (b : HCBasis G n)
    {κ ν : Type*} [CommRing ν] [BinomialRing ν]
    (z : κ → ν) (a : BExpr κ)
    (x : Fin n → BExpr κ) :
    evalTuple z (powTuple b a x) =
      (pow b ⟨evalTuple z x⟩ (BExpr.eval z a)).coord := by
  funext i
  simp only [evalTuple, powTuple, pow, BExpr.eval_substitute]
  congr 1
  funext j
  cases j <;> rfl

/-- Over integer coordinates, evaluating a substituted multiplication
tuple is exactly multiplication in the original group followed by its
canonical-coordinate equivalence. -/
lemma tuple_mul_int {n : ℕ} (b : HCBasis G n)
    {κ : Type*} (z : κ → ℤ)
    (x y : Fin n → BExpr κ) :
    evalTuple z (mulTuple b x y) =
      b.coord (b.coord.symm (evalTuple z x) *
        b.coord.symm (evalTuple z y)) := by
  funext i
  simp only [evalTuple, mulTuple, BExpr.eval_substitute,
    b.eval_expression_int, canonicalMulCoordinate, Sum.elim_inl,
    Sum.elim_inr]
  rfl

/-- Over integer coordinates, evaluating a substituted power tuple is
exactly integer powering in the original group followed by coordinates. -/
lemma tuple_pow_int {n : ℕ} (b : HCBasis G n)
    {κ : Type*} (z : κ → ℤ) (a : BExpr κ)
    (x : Fin n → BExpr κ) :
    evalTuple z (powTuple b a x) =
      b.coord ((b.coord.symm (evalTuple z x)) ^
        BExpr.eval z a) := by
  funext i
  simp only [evalTuple, powTuple, BExpr.eval_substitute,
    b.pow_expression_int, canonicalPowCoordinate]
  rfl

/-- Coordinatewise expression identities can be checked over integers
and then evaluated in every binomial ring. -/
lemma eval_tuple_int
    {ι κ R : Type*} [CommRing R] [BinomialRing R]
    (z : κ → R) {p q : ι → BExpr κ}
    (hpq : ∀ x : κ → ℤ, evalTuple x p = evalTuple x q) :
    evalTuple z p = evalTuple z q := by
  funext i
  exact BExpr.eval_int z fun x =>
    congrFun (hpq x) i

/-- Tuple-valued expression identities can also be checked on an
integer box with infinitely many allowed values in every coordinate. -/
lemma tuple_int_infinite
    {ι κ R : Type*} [CommRing R] [BinomialRing R]
    (z : κ → R) {p q : ι → BExpr κ}
    (S : κ → Set ℤ) (hS : ∀ i, (S i).Infinite)
    (hpq : ∀ x : κ → ℤ, (∀ i, x i ∈ S i) →
      evalTuple x p = evalTuple x q) :
    evalTuple z p = evalTuple z q := by
  funext i
  exact BExpr.evaleq_evalint_eqinfinite z S hS
    fun x hx => congrFun (hpq x hx) i

/-- The evaluated Hall multiplication formulas have the expected left
identity over every binomial ring. -/
lemma one_mul {n : ℕ} (b : HCBasis G n)
    {ν : Type v} [CommRing ν] [BinomialRing ν]
    (x : HComp b ν) :
    mul b (one b) x = x := by
  let vars : Fin n → BExpr (Fin n) :=
    varTuple fun i => i
  have h :=
    eval_tuple_int x.coord
      (p := mulTuple b (oneTuple b) vars) (q := vars) (by
        intro z
        rw [tuple_mul_int]
        rw [eval_tuple_one, one_int, b.coord.symm_apply_apply,
          _root_.one_mul, b.coord.apply_symm_apply])
  apply HComp.ext
  simpa [vars] using congrFun h

/-- The evaluated Hall multiplication formulas have the expected right
identity over every binomial ring. -/
lemma mul_one {n : ℕ} (b : HCBasis G n)
    {ν : Type v} [CommRing ν] [BinomialRing ν]
    (x : HComp b ν) :
    mul b x (one b) = x := by
  let vars : Fin n → BExpr (Fin n) :=
    varTuple fun i => i
  have h :=
    eval_tuple_int x.coord
      (p := mulTuple b vars (oneTuple b)) (q := vars) (by
        intro z
        rw [tuple_mul_int]
        rw [eval_tuple_one, one_int, b.coord.symm_apply_apply,
          _root_.mul_one, b.coord.apply_symm_apply])
  apply HComp.ext
  simpa [vars] using congrFun h

/-- Associativity of the evaluated Hall multiplication formulas follows
from associativity on integer coordinates. -/
lemma mul_assoc {n : ℕ} (b : HCBasis G n)
    {ν : Type v} [CommRing ν] [BinomialRing ν]
    (x y z : HComp b ν) :
    mul b (mul b x y) z = mul b x (mul b y z) := by
  let xvars :
      Fin n → BExpr (Sum (Sum (Fin n) (Fin n)) (Fin n)) :=
    varTuple fun i => Sum.inl (Sum.inl i)
  let yvars :
      Fin n → BExpr (Sum (Sum (Fin n) (Fin n)) (Fin n)) :=
    varTuple fun i => Sum.inl (Sum.inr i)
  let zvars :
      Fin n → BExpr (Sum (Sum (Fin n) (Fin n)) (Fin n)) :=
    varTuple fun i => Sum.inr i
  have h :=
    eval_tuple_int
      (Sum.elim (Sum.elim x.coord y.coord) z.coord)
      (p := mulTuple b (mulTuple b xvars yvars) zvars)
      (q := mulTuple b xvars (mulTuple b yvars zvars)) (by
        intro a
        rw [tuple_mul_int, tuple_mul_int,
          tuple_mul_int, tuple_mul_int]
        simp only [b.coord.symm_apply_apply]
        rw [_root_.mul_assoc])
  apply HComp.ext
  simpa [xvars, yvars, zvars] using congrFun h

/-- Inversion by Hall powering at `-1` satisfies inverse cancellation
over every binomial ring. -/
lemma inv_mul_cancel {n : ℕ} (b : HCBasis G n)
    {ν : Type v} [CommRing ν] [BinomialRing ν]
    (x : HComp b ν) :
    mul b (inv b x) x = one b := by
  let vars : Fin n → BExpr (Fin n) :=
    varTuple fun i => i
  have h :=
    eval_tuple_int x.coord
      (p := mulTuple b (powTuple b (.const (-1)) vars) vars)
      (q := oneTuple b) (by
        intro z
        rw [tuple_mul_int, tuple_pow_int]
        rw [b.coord.symm_apply_apply]
        norm_num only [BExpr.eval_const, Int.cast_neg,
          Int.cast_one]
        rw [zpow_neg_one, _root_.inv_mul_cancel, eval_tuple_one,
          one_int])
  apply HComp.ext
  simpa [vars, inv] using congrFun h

/-- Hall's evaluated coordinate formulas define a group over every
binomial ring. -/
noncomputable instance instGroup {n : ℕ} (b : HCBasis G n)
    {ν : Type v} [CommRing ν] [BinomialRing ν] :
    Group (HComp b ν) where
  mul := mul b
  one := one b
  inv := inv b
  mul_assoc := mul_assoc b
  one_mul := one_mul b
  mul_one := mul_one b
  inv_mul_cancel := inv_mul_cancel b

@[simp]
lemma explicit_one {n : ℕ} (b : HCBasis G n)
    {ν : Type v} [CommRing ν] [BinomialRing ν] :
    (one b : HComp b ν) = 1 :=
  rfl

@[simp]
lemma explicit_mul {n : ℕ} (b : HCBasis G n)
    {ν : Type v} [CommRing ν] [BinomialRing ν]
    (x y : HComp b ν) :
    mul b x y = x * y :=
  rfl

@[simp]
lemma explicit_inv {n : ℕ} (b : HCBasis G n)
    {ν : Type v} [CommRing ν] [BinomialRing ν]
    (x : HComp b ν) :
    inv b x = x⁻¹ :=
  rfl

/-- Embed the original group into the integer points of its coordinate
completion. -/
def ofInt {n : ℕ} (b : HCBasis G n) (g : G) :
    HComp b ℤ :=
  ⟨b.coord g⟩

@[simp]
lemma ofInt_coord {n : ℕ} (b : HCBasis G n) (g : G) :
    (ofInt b g).coord = b.coord g :=
  rfl

@[simp]
lemma ofInt_mul {n : ℕ} (b : HCBasis G n) (g h : G) :
    ofInt b (g * h) = ofInt b g * ofInt b h := by
  apply HComp.ext
  intro i
  change
    b.coord (g * h) i =
      BExpr.eval (Sum.elim (b.coord g) (b.coord h))
        (b.mulExpression i)
  rw [b.eval_expression_int]
  simp [canonicalMulCoordinate]

@[simp]
lemma ofInt_zpow {n : ℕ} (b : HCBasis G n) (g : G) (a : ℤ) :
    ofInt b (g ^ a) = pow b (ofInt b g) a := by
  apply HComp.ext
  intro i
  change
    b.coord (g ^ a) i =
      BExpr.eval
        (fun z => match z with
          | none => a
          | some j => b.coord g j)
        (b.powExpression i)
  rw [b.pow_expression_int]
  simp [canonicalPowCoordinate]

/-- Integer coordinates recover the original group multiplicatively. -/
noncomputable def intEquiv {n : ℕ} (b : HCBasis G n) :
    G ≃* HComp b ℤ where
  toFun := ofInt b
  invFun x := b.coord.symm x.coord
  left_inv g := by simp [ofInt]
  right_inv x := by
    apply HComp.ext
    simp [ofInt]
  map_mul' := ofInt_mul b

/-- Embed the original group into the points of its coordinate completion
over an arbitrary binomial ring by casting its integer coordinates. -/
def ofIntCast {n : ℕ} (b : HCBasis G n)
    {ν : Type v} [CommRing ν] (g : G) :
    HComp b ν :=
  ⟨fun i => (b.coord g i : ν)⟩

@[simp]
lemma int_cast_coord {n : ℕ} (b : HCBasis G n)
    {ν : Type v} [CommRing ν] (g : G) :
    (ofIntCast b g : HComp b ν).coord =
      fun i => (b.coord g i : ν) :=
  rfl

@[simp]
lemma int_cast_one {n : ℕ} (b : HCBasis G n)
    {ν : Type v} [CommRing ν] [BinomialRing ν] :
    ofIntCast b (1 : G) = (1 : HComp b ν) :=
  rfl

@[simp]
lemma int_cast_mul {n : ℕ} (b : HCBasis G n)
    {ν : Type v} [CommRing ν] [BinomialRing ν] (g h : G) :
    (ofIntCast b (g * h) : HComp b ν) =
      ofIntCast b g * ofIntCast b h := by
  apply HComp.ext
  intro i
  change
    (b.coord (g * h) i : ν) =
      BExpr.eval
        (Sum.elim
          (fun j => (b.coord g j : ν))
          (fun j => (b.coord h j : ν)))
        (b.mulExpression i)
  calc
    (b.coord (g * h) i : ν) =
        (BExpr.eval (Sum.elim (b.coord g) (b.coord h))
          (b.mulExpression i) : ℤ) := by
      rw [b.eval_expression_int]
      simp [canonicalMulCoordinate]
    _ = BExpr.eval
        (fun j => (Int.castRingHom ν)
          (Sum.elim (b.coord g) (b.coord h) j))
        (b.mulExpression i) :=
      BExpr.map_eval (Int.castRingHom ν)
        (Sum.elim (b.coord g) (b.coord h)) (b.mulExpression i)
    _ = BExpr.eval
        (Sum.elim
          (fun j => (b.coord g j : ν))
          (fun j => (b.coord h j : ν)))
        (b.mulExpression i) := by
      congr 1
      funext j
      cases j <;> rfl

/-- The coordinatewise cast embeds the original group multiplicatively
into its completion over every binomial ring. -/
noncomputable def embedding {n : ℕ} (b : HCBasis G n)
    {ν : Type v} [CommRing ν] [BinomialRing ν] :
    G →* HComp b ν where
  toFun := ofIntCast b
  map_one' := int_cast_one b
  map_mul' := int_cast_mul b

lemma embedding_injective {n : ℕ} (b : HCBasis G n)
    {ν : Type v} [CommRing ν] [BinomialRing ν] [Nontrivial ν] :
    Function.Injective (embedding b : G → HComp b ν) := by
  letI : IsAddTorsionFree ν := BinomialRing.toIsAddTorsionFree
  letI : CharZero ν := CharZero.of_isAddTorsionFree ν ν
  intro g h hgh
  apply b.coord.injective
  funext i
  apply Int.cast_injective (α := ν)
  exact congrArg (fun x : HComp b ν => x.coord i) hgh

/-- Every integer completion point is the embedded original element with
the corresponding canonical coordinates. -/
lemma embedding_coord_int {n : ℕ} (b : HCBasis G n)
    (x : HComp b ℤ) :
    (embedding b : G → HComp b ℤ) (b.coord.symm x.coord) = x := by
  apply HComp.ext
  intro i
  simp [embedding, ofIntCast]

/-- Symbolic completion inversion. -/
noncomputable def invTuple {n : ℕ} (b : HCBasis G n)
    {κ : Type*} (x : Fin n → BExpr κ) :
    Fin n → BExpr κ :=
  powTuple b (.const (-1)) x

/-- Symbolic fixed natural powers in the completion. -/
noncomputable def npowTuple {n : ℕ} (b : HCBasis G n)
    {κ : Type*} (x : Fin n → BExpr κ) :
    ℕ → Fin n → BExpr κ
  | 0 => oneTuple b
  | m + 1 => mulTuple b (npowTuple b x m) x

/-- Symbolic finite products in the completion. -/
noncomputable def listProdTuple {n : ℕ} (b : HCBasis G n)
    {κ : Type*} :
    List (Fin n → BExpr κ) →
      Fin n → BExpr κ
  | [] => oneTuple b
  | x :: l => mulTuple b x (listProdTuple b l)

/-- Symbolic Petresco terms in the completion. -/
noncomputable def petrescoTermTuple {n : ℕ} (b : HCBasis G n)
    {κ : Type*} (x : List (Fin n → BExpr κ)) :
    ℕ → Fin n → BExpr κ :=
  Nat.strongRec fun w previous =>
    match w with
    | 0 => oneTuple b
    | m + 1 =>
        mulTuple b
          (invTuple b
            (listProdTuple b
              ((List.finRange m).map fun (j : Fin m) =>
                npowTuple b
                  (previous ((j : ℕ) + 1) (Nat.succ_lt_succ j.isLt))
                  (Nat.choose (m + 1) ((j : ℕ) + 1)))))
          (listProdTuple b (x.map fun g => npowTuple b g (m + 1)))

/-- Variable tuples for a finite list of completion elements. -/
def listVarTuples {n m : ℕ} {κ : Type*}
    (e : Fin m → Fin n → κ) :
    List (Fin n → BExpr κ) :=
  List.ofFn fun k i => .var (e k i)

@[simp]
lemma mk_var_tuples {n m : ℕ} (b : HCBasis G n)
    {κ ν : Type*} [CommRing ν] [BinomialRing ν]
    (z : κ → ν) (e : Fin m → Fin n → κ) :
    (listVarTuples e).map
        (fun p => (⟨evalTuple z p⟩ : HComp b ν)) =
      List.ofFn fun k => (⟨fun i => z (e k i)⟩ : HComp b ν) := by
  unfold listVarTuples
  rw [List.map_ofFn]
  apply congrArg List.ofFn
  funext k
  apply HComp.ext
  intro i
  rfl

/-- Substituting the coordinates of a concrete completion-element list
into its variable tuples reconstructs the list. -/
@[simp]
lemma var_tuples_coords {n : ℕ}
    (b : HCBasis G n) {ν : Type*}
    [CommRing ν] [BinomialRing ν] (x : List (HComp b ν)) :
    (listVarTuples (fun (k : Fin x.length) (i : Fin n) => (k, i))).map
        (fun p => (⟨evalTuple
          (fun ki => (x.get ki.1).coord ki.2) p⟩ : HComp b ν)) =
      x := by
  rw [mk_var_tuples]
  exact List.ofFn_get x

@[simp]
lemma petresco_term_tuple {n : ℕ} (b : HCBasis G n)
    {κ : Type*} (x : List (Fin n → BExpr κ)) :
    petrescoTermTuple b x 0 = oneTuple b := by
  rw [petrescoTermTuple, Nat.strongRec_eq]

@[simp]
lemma petresco_tuple_succ {n : ℕ} (b : HCBasis G n)
    {κ : Type*} (x : List (Fin n → BExpr κ)) (m : ℕ) :
    petrescoTermTuple b x (m + 1) =
      mulTuple b
        (invTuple b
          (listProdTuple b
            ((List.finRange m).map fun (j : Fin m) =>
              npowTuple b (petrescoTermTuple b x ((j : ℕ) + 1))
                (Nat.choose (m + 1) ((j : ℕ) + 1)))))
        (listProdTuple b (x.map fun g => npowTuple b g (m + 1))) := by
  rw [petrescoTermTuple, Nat.strongRec_eq]
  rfl

@[simp]
lemma eval_tuple_inv {n : ℕ} (b : HCBasis G n)
    {κ ν : Type*} [CommRing ν] [BinomialRing ν]
    (z : κ → ν) (x : Fin n → BExpr κ) :
    evalTuple z (invTuple b x) =
      (inv b ⟨evalTuple z x⟩).coord := by
  simp [invTuple, inv]

@[simp]
lemma eval_tuple_npow {n : ℕ} (b : HCBasis G n)
    {κ ν : Type*} [CommRing ν] [BinomialRing ν]
    (z : κ → ν) (x : Fin n → BExpr κ) :
    ∀ m : ℕ, evalTuple z (npowTuple b x m) =
      ((⟨evalTuple z x⟩ : HComp b ν) ^ m).coord
  | 0 => by
      simp [npowTuple]
  | m + 1 => by
      rw [npowTuple, eval_tuple_mul, eval_tuple_npow, pow_succ]
      rfl

@[simp]
lemma eval_tuple_prod {n : ℕ} (b : HCBasis G n)
    {κ ν : Type*} [CommRing ν] [BinomialRing ν] (z : κ → ν) :
    ∀ l : List (Fin n → BExpr κ),
      evalTuple z (listProdTuple b l) =
        ((l.map fun x =>
          (⟨evalTuple z x⟩ : HComp b ν)).prod).coord
  | [] => by
      simp [listProdTuple]
  | x :: l => by
      rw [listProdTuple, eval_tuple_mul, List.map_cons, List.prod_cons,
        eval_tuple_prod]
      rfl

@[simp]
lemma mk_tuple_one {n : ℕ} (b : HCBasis G n)
    {κ ν : Type*} [CommRing ν] [BinomialRing ν] (z : κ → ν) :
    (⟨evalTuple z (oneTuple b)⟩ : HComp b ν) = 1 := by
  apply HComp.ext
  simp

@[simp]
lemma mk_tuple_mul {n : ℕ} (b : HCBasis G n)
    {κ ν : Type*} [CommRing ν] [BinomialRing ν]
    (z : κ → ν) (x y : Fin n → BExpr κ) :
    (⟨evalTuple z (mulTuple b x y)⟩ : HComp b ν) =
      ⟨evalTuple z x⟩ * ⟨evalTuple z y⟩ := by
  apply HComp.ext
  simp

@[simp]
lemma mk_tuple_pow {n : ℕ} (b : HCBasis G n)
    {κ ν : Type*} [CommRing ν] [BinomialRing ν]
    (z : κ → ν) (a : BExpr κ)
    (x : Fin n → BExpr κ) :
    (⟨evalTuple z (powTuple b a x)⟩ : HComp b ν) =
      pow b ⟨evalTuple z x⟩ (BExpr.eval z a) := by
  apply HComp.ext
  simp

@[simp]
lemma mk_tuple_inv {n : ℕ} (b : HCBasis G n)
    {κ ν : Type*} [CommRing ν] [BinomialRing ν]
    (z : κ → ν) (x : Fin n → BExpr κ) :
    (⟨evalTuple z (invTuple b x)⟩ : HComp b ν) =
      (⟨evalTuple z x⟩ : HComp b ν)⁻¹ := by
  apply HComp.ext
  simp

@[simp]
lemma mk_tuple_npow {n : ℕ} (b : HCBasis G n)
    {κ ν : Type*} [CommRing ν] [BinomialRing ν]
    (z : κ → ν) (x : Fin n → BExpr κ) (m : ℕ) :
    (⟨evalTuple z (npowTuple b x m)⟩ : HComp b ν) =
      (⟨evalTuple z x⟩ : HComp b ν) ^ m := by
  apply HComp.ext
  simp

@[simp]
lemma mk_tuple_prod {n : ℕ} (b : HCBasis G n)
    {κ ν : Type*} [CommRing ν] [BinomialRing ν] (z : κ → ν)
    (l : List (Fin n → BExpr κ)) :
    (⟨evalTuple z (listProdTuple b l)⟩ : HComp b ν) =
      (l.map fun x => (⟨evalTuple z x⟩ : HComp b ν)).prod := by
  apply HComp.ext
  simp

/-- Symbolic Petresco terms evaluate to the corresponding Petresco terms
in the completion group. -/
@[simp]
lemma mk_tuple_petresco {n : ℕ} (b : HCBasis G n)
    {κ ν : Type*} [CommRing ν] [BinomialRing ν]
    (z : κ → ν) (x : List (Fin n → BExpr κ)) :
    ∀ w : ℕ,
      (⟨evalTuple z (petrescoTermTuple b x w)⟩ : HComp b ν) =
        petrescoTerm
          (x.map fun p => (⟨evalTuple z p⟩ : HComp b ν)) w := by
  intro w
  induction w using Nat.strong_induction_on with
  | h w ih =>
      cases w with
      | zero =>
          rw [petresco_term_tuple, petrescoTerm_zero]
          exact mk_tuple_one b z
      | succ m =>
          rw [petresco_tuple_succ, petrescoTerm_succ,
            mk_tuple_mul, mk_tuple_inv,
            mk_tuple_prod, mk_tuple_prod]
          simp only [List.map_map]
          congr 2
          · unfold petrescoPriorProduct
            congr 1
            apply List.map_congr_left
            intro j _
            change
              (⟨evalTuple z
                (npowTuple b (petrescoTermTuple b x ((j : ℕ) + 1))
                  (Nat.choose (m + 1) ((j : ℕ) + 1)))⟩ :
                  HComp b ν) =
                petrescoTerm
                    (x.map fun p => (⟨evalTuple z p⟩ : HComp b ν))
                    ((j : ℕ) + 1) ^
                  Nat.choose (m + 1) ((j : ℕ) + 1)
            rw [mk_tuple_npow, ih ((j : ℕ) + 1) (by omega)]
          · apply List.map_congr_left
            intro g _
            change
              (⟨evalTuple z (npowTuple b g (m + 1))⟩ :
                  HComp b ν) =
                (⟨evalTuple z g⟩ : HComp b ν) ^ (m + 1)
            exact mk_tuple_npow b z g (m + 1)

@[simp]
lemma tuple_petresco_term {n : ℕ} (b : HCBasis G n)
    {κ ν : Type*} [CommRing ν] [BinomialRing ν]
    (z : κ → ν) (x : List (Fin n → BExpr κ)) (w : ℕ) :
    evalTuple z (petrescoTermTuple b x w) =
      (petrescoTerm
        (x.map fun p => (⟨evalTuple z p⟩ : HComp b ν)) w).coord := by
  exact congrArg HComp.coord
    (mk_tuple_petresco b z x w)

/-- Petresco terms above the canonical-basis length vanish at the integer
points of the completion. -/
lemma petresco_int_length {n : ℕ}
    (b : HCBasis G n) (x : List (HComp b ℤ))
    {w : ℕ} (hw : n < w) :
    petrescoTerm x w = 1 := by
  let e := intEquiv b
  have h := congrArg e
    (b.petresco_term_length (x.map e.symm) hw)
  calc
    petrescoTerm x w =
        petrescoTerm ((x.map e.symm).map e) w := by
          simp [List.map_map]
    _ = e (petrescoTerm (x.map e.symm) w) :=
      (map_petrescoTerm e.toMonoidHom (x.map e.symm) w).symm
    _ = e 1 := h
    _ = 1 := e.map_one

/-- Petresco terms above the canonical-basis length vanish throughout
the completion over every binomial ring. -/
lemma petresco_term_length {n : ℕ}
    (b : HCBasis G n) {ν : Type v}
    [CommRing ν] [BinomialRing ν] (x : List (HComp b ν))
    {w : ℕ} (hw : n < w) :
    petrescoTerm x w = 1 := by
  let vars :
      List (Fin n → BExpr (Fin x.length × Fin n)) :=
    listVarTuples fun k i => (k, i)
  let assignment : (Fin x.length × Fin n) → ν :=
    fun ki => (x.get ki.1).coord ki.2
  have h :=
    eval_tuple_int assignment
      (p := petrescoTermTuple b vars w) (q := oneTuple b) (by
        intro z
        rw [tuple_petresco_term, eval_tuple_one]
        simpa using congrArg HComp.coord
          (petresco_int_length b
            (vars.map fun p =>
              (⟨evalTuple z p⟩ : HComp b ℤ)) hw))
  have hs :
      (⟨evalTuple assignment (petrescoTermTuple b vars w)⟩ :
          HComp b ν) =
        ⟨evalTuple assignment (oneTuple b)⟩ := by
    apply HComp.ext
    exact congrFun h
  rw [mk_tuple_petresco, mk_tuple_one] at hs
  have hvars :
      vars.map
          (fun p => (⟨evalTuple assignment p⟩ : HComp b ν)) =
        x := by
    simp [vars, assignment]
  rw [hvars] at hs
  exact hs

end HComp

/-- A minimal interface for exponentiation of a group by scalars from
`ν`. Hall's full definition imposes his axioms (I)--(III); the following
Section 6 constructions only need the identity-power consequence. -/
class NuPoweredGroup (ν : Type v) (G : Type u) [Group G] where
  pow : G → ν → G
  one_pow : ∀ a : ν, pow 1 a = 1

namespace HComp

/-- Hall powering sends the completion identity to itself. -/
lemma pow_one {n : ℕ} (b : HCBasis G n)
    {ν : Type v} [CommRing ν] [BinomialRing ν] (a : ν) :
    pow b (one b) a = one b := by
  let scalar : BExpr Unit := .var ()
  have h :=
    eval_tuple_int (fun _ : Unit => a)
      (p := powTuple b scalar (oneTuple b)) (q := oneTuple b) (by
        intro z
        rw [tuple_pow_int, eval_tuple_one, one_int,
          b.coord.symm_apply_apply, one_zpow])
  apply HComp.ext
  simpa [scalar] using congrFun h

/-- Hall's evaluated coordinate power formulas supply the minimal
powered-group interface on the completion. -/
noncomputable instance instNuPowered {n : ℕ}
    (b : HCBasis G n)
    {ν : Type v} [CommRing ν] [BinomialRing ν] :
    NuPoweredGroup ν (HComp b ν) where
  pow := pow b
  one_pow := pow_one b

/-- Hall powering by scalar one is the identity. -/
lemma pow_scalar_one {n : ℕ} (b : HCBasis G n)
    {ν : Type v} [CommRing ν] [BinomialRing ν]
    (x : HComp b ν) :
    pow b x 1 = x := by
  let vars : Fin n → BExpr (Fin n) :=
    varTuple fun i => i
  have h :=
    eval_tuple_int x.coord
      (p := powTuple b (.const 1) vars) (q := vars) (by
        intro z
        rw [tuple_pow_int]
        norm_num only [BExpr.eval_const, Int.cast_one, zpow_one]
        rw [b.coord.apply_symm_apply])
  apply HComp.ext
  simpa [vars] using congrFun h

/-- Hall powering by scalar zero is the identity element. -/
lemma pow_zero {n : ℕ} (b : HCBasis G n)
    {ν : Type v} [CommRing ν] [BinomialRing ν]
    (x : HComp b ν) :
    pow b x 0 = 1 := by
  let vars : Fin n → BExpr (Fin n) :=
    varTuple fun i => i
  have h :=
    eval_tuple_int x.coord
      (p := powTuple b (.const 0) vars) (q := oneTuple b) (by
        intro z
        rw [tuple_pow_int, eval_tuple_one, one_int]
        norm_num only [BExpr.eval_const, Int.cast_zero,
          zpow_zero])
  apply HComp.ext
  simpa [vars] using congrFun h

/-- Hall powering turns addition of scalars into multiplication. -/
lemma pow_add {n : ℕ} (b : HCBasis G n)
    {ν : Type v} [CommRing ν] [BinomialRing ν]
    (x : HComp b ν) (a c : ν) :
    pow b x (a + c) = mul b (pow b x a) (pow b x c) := by
  let xvars :
      Fin n → BExpr (Sum (Fin n) (Sum Unit Unit)) :=
    varTuple fun i => Sum.inl i
  let avar : BExpr (Sum (Fin n) (Sum Unit Unit)) :=
    .var (Sum.inr (Sum.inl ()))
  let cvar : BExpr (Sum (Fin n) (Sum Unit Unit)) :=
    .var (Sum.inr (Sum.inr ()))
  have h :=
    eval_tuple_int
      (Sum.elim x.coord (Sum.elim (fun _ : Unit => a) (fun _ : Unit => c)))
      (p := powTuple b (avar + cvar) xvars)
      (q := mulTuple b (powTuple b avar xvars) (powTuple b cvar xvars)) (by
        intro z
        rw [tuple_pow_int, tuple_mul_int,
          tuple_pow_int, tuple_pow_int]
        simp only [BExpr.eval_add, b.coord.symm_apply_apply]
        rw [zpow_add])
  apply HComp.ext
  simpa [xvars, avar, cvar] using congrFun h

/-- Hall powering by a natural-number scalar agrees with the ordinary
natural group power. -/
lemma pow_natCast {n : ℕ} (b : HCBasis G n)
    {ν : Type v} [CommRing ν] [BinomialRing ν]
    (x : HComp b ν) :
    ∀ m : ℕ, pow b x (m : ν) = x ^ m
  | 0 => by simpa using pow_zero b x
  | m + 1 => by
      rw [Nat.cast_succ, pow_add, pow_scalar_one, pow_natCast, pow_succ]
      rfl

/-- Hall powering turns multiplication of scalars into iterated
powering. -/
lemma pow_mul {n : ℕ} (b : HCBasis G n)
    {ν : Type v} [CommRing ν] [BinomialRing ν]
    (x : HComp b ν) (a c : ν) :
    pow b x (a * c) = pow b (pow b x a) c := by
  let xvars :
      Fin n → BExpr (Sum (Fin n) (Sum Unit Unit)) :=
    varTuple fun i => Sum.inl i
  let avar : BExpr (Sum (Fin n) (Sum Unit Unit)) :=
    .var (Sum.inr (Sum.inl ()))
  let cvar : BExpr (Sum (Fin n) (Sum Unit Unit)) :=
    .var (Sum.inr (Sum.inr ()))
  have h :=
    eval_tuple_int
      (Sum.elim x.coord (Sum.elim (fun _ : Unit => a) (fun _ : Unit => c)))
      (p := powTuple b (avar * cvar) xvars)
      (q := powTuple b cvar (powTuple b avar xvars)) (by
        intro z
        rw [tuple_pow_int, tuple_pow_int,
          tuple_pow_int]
        simp only [BExpr.eval_mul, b.coord.symm_apply_apply]
        rw [zpow_mul])
  apply HComp.ext
  simpa [xvars, avar, cvar] using congrFun h

/-- Hall powering commutes with conjugation. -/
lemma conj_pow {n : ℕ} (b : HCBasis G n)
    {ν : Type v} [CommRing ν] [BinomialRing ν]
    (x y : HComp b ν) (a : ν) :
    mul b (mul b (inv b y) (pow b x a)) y =
      pow b (mul b (mul b (inv b y) x) y) a := by
  let xvars :
      Fin n → BExpr (Sum (Sum (Fin n) (Fin n)) Unit) :=
    varTuple fun i => Sum.inl (Sum.inl i)
  let yvars :
      Fin n → BExpr (Sum (Sum (Fin n) (Fin n)) Unit) :=
    varTuple fun i => Sum.inl (Sum.inr i)
  let avar : BExpr (Sum (Sum (Fin n) (Fin n)) Unit) :=
    .var (Sum.inr ())
  let invY := powTuple b (.const (-1)) yvars
  have h :=
    eval_tuple_int
      (Sum.elim (Sum.elim x.coord y.coord) (fun _ : Unit => a))
      (p := mulTuple b (mulTuple b invY (powTuple b avar xvars)) yvars)
      (q := powTuple b avar (mulTuple b (mulTuple b invY xvars) yvars)) (by
        intro z
        dsimp only [invY]
        simp only [tuple_mul_int, tuple_pow_int,
          b.coord.symm_apply_apply]
        norm_num only [BExpr.eval_const, Int.cast_neg,
          Int.cast_one]
        rw [zpow_neg_one]
        apply congrArg b.coord
        simpa only [inv_inv] using
          (conj_zpow
            (i := BExpr.eval z avar)
            (a := (b.coord.symm (evalTuple z yvars))⁻¹)
            (b := b.coord.symm (evalTuple z xvars))).symm)
  apply HComp.ext
  simpa [xvars, yvars, avar, invY, inv] using congrFun h

end HComp

/-- Exponentiation in a `ν`-powered group. -/
def nuPow {ν : Type v} {G : Type u} [Group G] [NuPoweredGroup ν G]
    (x : G) (a : ν) : G :=
  NuPoweredGroup.pow x a

@[simp]
lemma nuPow_one {ν : Type v} {G : Type u} [Group G] [NuPoweredGroup ν G]
    (a : ν) :
    nuPow (ν := ν) (1 : G) a = 1 :=
  NuPoweredGroup.one_pow a

namespace HComp

@[simp]
lemma nu_pow {n : ℕ} (b : HCBasis G n)
    {ν : Type v} [CommRing ν] [BinomialRing ν]
    (x : HComp b ν) (a : ν) :
    nuPow (ν := ν) x a = pow b x a :=
  rfl

/-- The first completion coordinate is additive under multiplication. -/
lemma coord_mul_zero {n : ℕ} (b : HCBasis G (n + 1))
    {ν : Type v} [CommRing ν] [BinomialRing ν]
    (x y : HComp b ν) :
    (x * y).coord 0 = x.coord 0 + y.coord 0 := by
  change
    BExpr.eval (Sum.elim x.coord y.coord)
        (b.mulExpression 0) =
      x.coord 0 + y.coord 0
  have h :=
    BExpr.eval_int
      (Sum.elim x.coord y.coord)
      (p := b.mulExpression 0)
      (q := .var (Sum.inl 0) + .var (Sum.inr 0)) (by
        intro z
        rw [b.eval_expression_int]
        exact b.coord_mul_zero
          (fun i => z (Sum.inl i)) (fun i => z (Sum.inr i)))
  simpa using h

/-- The first completion coordinate is multiplied by scalar powering. -/
lemma coord_nu_zero {n : ℕ} (b : HCBasis G (n + 1))
    {ν : Type v} [CommRing ν] [BinomialRing ν]
    (x : HComp b ν) (a : ν) :
    (nuPow (ν := ν) x a).coord 0 = a * x.coord 0 := by
  rw [nu_pow]
  unfold pow evalTuple
  have h :=
    BExpr.eval_int
      (fun
        | none => a
        | some i => x.coord i)
      (p := b.powExpression 0)
      (q := .var none * .var (some 0)) (by
        intro z
        rw [b.pow_expression_int]
        exact b.coord_zpow_zero (fun i => z (some i)) (z none))
  convert h using 1
  · dsimp only
    congr 1
    funext z
    cases z <;> rfl

/-- The first coordinate of a nonempty Hall completion is an additive
coordinate homomorphism, written multiplicatively. -/
def headCoordHom {n : ℕ} (b : HCBasis G (n + 1))
    {ν : Type v} [CommRing ν] [BinomialRing ν] :
    HComp b ν →* Multiplicative ν where
  toFun x := Multiplicative.ofAdd (x.coord 0)
  map_one' := by
    change ((1 : HComp b ν).coord 0) = 0
    rw [← int_cast_one b]
    change (b.coord 1 0 : ν) = 0
    rw [b.coord_one_zero]
    simp
  map_mul' x y := by
    change (x * y).coord 0 = x.coord 0 + y.coord 0
    exact coord_mul_zero b x y

/-- Every Petresco term of weight at least two has zero head coordinate in
a nonempty Hall completion. -/
lemma petresco_term_coord {n : ℕ}
    (b : HCBasis G (n + 1))
    {ν : Type v} [CommRing ν] [BinomialRing ν]
    (x : List (HComp b ν)) {w : ℕ} (hw : 2 ≤ w) :
    (petrescoTerm x w).coord 0 = 0 := by
  have h := map_petrescoTerm (headCoordHom b) x w
  rw [petresco_comm_group (x.map (headCoordHom b)) hw] at h
  exact h

end HComp

/-- A subgroup closed under all `ν`-powers. -/
def NuPoweredSubgroup (ν : Type v) {G : Type u} [Group G]
    [NuPoweredGroup ν G] (H : Subgroup G) : Prop :=
  ∀ x ∈ H, ∀ a : ν, nuPow (ν := ν) x a ∈ H

/-- A group homomorphism which preserves all `ν`-powers. -/
structure NPHom (ν : Type v) (G : Type u) (H : Type*)
    [Group G] [Group H] [NuPoweredGroup ν G] [NuPoweredGroup ν H]
    extends G →* H where
  map_nuPow' : ∀ (x : G) (a : ν),
    toMonoidHom (nuPow (ν := ν) x a) =
      nuPow (ν := ν) (toMonoidHom x) a

namespace NPHom

variable {ν : Type v} {H : Type*} [Group H]
  [NuPoweredGroup ν G] [NuPoweredGroup ν H]

instance : CoeFun (NPHom ν G H) fun _ => G → H :=
  ⟨fun f => f.toMonoidHom⟩

@[simp]
lemma map_nuPow (f : NPHom ν G H) (x : G) (a : ν) :
    f (nuPow (ν := ν) x a) = nuPow (ν := ν) (f x) a :=
  f.map_nuPow' x a

@[simp]
lemma map_one (f : NPHom ν G H) :
    f (1 : G) = 1 :=
  f.toMonoidHom.map_one

@[ext]
lemma ext {f g : NPHom ν G H} (h : ∀ x, f x = g x) : f = g := by
  cases f with
  | mk f hf =>
      cases g with
      | mk g hg =>
          congr
          apply MonoidHom.ext
          exact h

/-- Composition of powered homomorphisms. -/
def comp {K : Type*} [Group K] [NuPoweredGroup ν K]
    (g : NPHom ν H K) (f : NPHom ν G H) :
    NPHom ν G K where
  toMonoidHom := g.toMonoidHom.comp f.toMonoidHom
  map_nuPow' x a := by
    simp

@[simp]
lemma comp_apply {K : Type*} [Group K] [NuPoweredGroup ν K]
    (g : NPHom ν H K) (f : NPHom ν G H) (x : G) :
    g.comp f x = g (f x) :=
  rfl

/-- **Hall, Lemma 6.6, kernel clause.** The kernel of a
`ν`-homomorphism is a normal `ν`-powered subgroup. -/
theorem nu_powered_kernel (f : NPHom ν G H) :
    f.toMonoidHom.ker.Normal ∧
      NuPoweredSubgroup ν f.toMonoidHom.ker := by
  constructor
  · infer_instance
  · intro x hx a
    rw [MonoidHom.mem_ker] at hx ⊢
    rw [f.map_nuPow, hx, nuPow_one]

end NPHom

/-- Scalar powers are compatible modulo `K` if congruent representatives
have congruent scalar powers. Hall derives this condition for every normal
powered subgroup from axioms (I)--(III) in Lemma 6.6. -/
def NCMod {ν : Type v} {G : Type u} [Group G]
    [NuPoweredGroup ν G] (K : Subgroup G) : Prop :=
  ∀ x y : G, ∀ a : ν, x / y ∈ K →
    nuPow (ν := ν) x a / nuPow (ν := ν) y a ∈ K

/-- Hall's finite scalar Petresco product
`τ₁(x)^a τ₂(x)^(a choose 2) ... τ_c(x)^(a choose c)`. -/
def nuPetrescoBinomial
    {ν : Type v} {G : Type u} [CommRing ν] [BinomialRing ν]
    [Group G] [NuPoweredGroup ν G]
    (tau : ℕ → G) (a : ν) (c : ℕ) : G :=
  ((List.finRange c).map fun (j : Fin c) =>
    nuPow (ν := ν) (tau ((j : ℕ) + 1))
      (Ring.choose a ((j : ℕ) + 1))).prod

/-- The positive-weight Petresco factors strictly after `τ₁^a`. -/
def nuPetrescoTail
    {ν : Type v} {G : Type u} [CommRing ν] [BinomialRing ν]
    [Group G] [NuPoweredGroup ν G]
    (tau : ℕ → G) (a : ν) (c : ℕ) : G :=
  ((List.finRange c).map fun (j : Fin c) =>
    nuPow (ν := ν) (tau ((j : ℕ) + 2))
      (Ring.choose a ((j : ℕ) + 2))).prod

/-- Splitting off the weight-one factor of a finite scalar Petresco
product. -/
lemma nu_petresco_succ
    {ν : Type v} {G : Type u} [CommRing ν] [BinomialRing ν]
    [Group G] [NuPoweredGroup ν G]
    (tau : ℕ → G) (a : ν) (c : ℕ) :
    nuPetrescoBinomial tau a (c + 1) =
      nuPow (ν := ν) (tau 1) a * nuPetrescoTail tau a c := by
  simp [nuPetrescoBinomial, nuPetrescoTail,
    List.finRange_succ, Function.comp_def]

/-- Extending a tail-only scalar Petresco product by one appends its final
weight factor. -/
lemma nu_tail_succ
    {ν : Type v} {G : Type u} [CommRing ν] [BinomialRing ν]
    [Group G] [NuPoweredGroup ν G]
    (tau : ℕ → G) (a : ν) (c : ℕ) :
    nuPetrescoTail tau a (c + 1) =
      nuPetrescoTail tau a c *
        nuPow (ν := ν) (tau (c + 2)) (Ring.choose a (c + 2)) := by
  unfold nuPetrescoTail
  rw [List.finRange_succ_last, List.map_append, List.prod_append]
  simp only [List.map_singleton, List.prod_singleton]
  rw [List.map_map]
  congr 1

/-- Extending a finite scalar Petresco product by one appends its final
weight factor. -/
lemma nu_petresco_last
    {ν : Type v} {G : Type u} [CommRing ν] [BinomialRing ν]
    [Group G] [NuPoweredGroup ν G]
    (tau : ℕ → G) (a : ν) (c : ℕ) :
    nuPetrescoBinomial tau a (c + 1) =
      nuPetrescoBinomial tau a c *
        nuPow (ν := ν) (tau (c + 1)) (Ring.choose a (c + 1)) := by
  unfold nuPetrescoBinomial
  rw [List.finRange_succ_last, List.map_append, List.prod_append]
  simp only [List.map_singleton, List.prod_singleton]
  rw [List.map_map]
  congr 1

/-- Once later Petresco terms vanish, extending the cutoff does not change
the tail-only scalar product. -/
lemma nu_petresco_tail
    {ν : Type v} {G : Type u} [CommRing ν] [BinomialRing ν]
    [Group G] [NuPoweredGroup ν G]
    (tau : ℕ → G) (a : ν) {c d : ℕ} (hcd : c ≤ d)
    (htau : ∀ w, c + 1 < w → tau w = 1) :
    nuPetrescoTail tau a d = nuPetrescoTail tau a c := by
  obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_le hcd
  induction e with
  | zero => rfl
  | succ e ih =>
      rw [show c + (e + 1) = (c + e) + 1 by omega,
        nu_tail_succ, ih (by omega),
        htau (c + e + 2) (by omega),
        nuPow_one, mul_one]

/-- Once later Petresco terms vanish, extending the cutoff does not change
the finite scalar Petresco product. -/
lemma nu_petresco_binomial
    {ν : Type v} {G : Type u} [CommRing ν] [BinomialRing ν]
    [Group G] [NuPoweredGroup ν G]
    (tau : ℕ → G) (a : ν) {c d : ℕ} (hcd : c ≤ d)
    (htau : ∀ w, c < w → tau w = 1) :
    nuPetrescoBinomial tau a d =
      nuPetrescoBinomial tau a c := by
  obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_le hcd
  induction e with
  | zero => rfl
  | succ e ih =>
      rw [show c + (e + 1) = (c + e) + 1 by omega,
        nu_petresco_last, ih (by omega),
        htau (c + e + 1) (by omega),
        nuPow_one, mul_one]

namespace HComp

/-- For natural scalars, the completion satisfies Hall's finite Petresco
formula, uniformly truncated at the canonical-basis length. -/
lemma scalar_petresco_cast {n : ℕ} (b : HCBasis G n)
    {ν : Type v} [CommRing ν] [BinomialRing ν]
    (x : List (HComp b ν)) (m : ℕ) :
    (x.map fun g => pow b g (m : ν)).prod =
      nuPetrescoBinomial (petrescoTerm x) (m : ν) n := by
  calc
    (x.map fun g => pow b g (m : ν)).prod =
        (x.map fun g => g ^ m).prod := by
          apply congrArg List.prod
          apply List.map_congr_left
          intro g _
          rw [pow_natCast]
    _ = petrescoBinomialProduct (petrescoTerm x) m :=
      petresco_term_family x m
    _ = ((List.range n).map fun j =>
          petrescoTerm x (j + 1) ^ Nat.choose m (j + 1)).prod :=
      HCBasis.petresco_binomial_range
        (petrescoTerm x) m n fun w hw =>
          petresco_term_length b x hw
    _ = nuPetrescoBinomial (petrescoTerm x) (m : ν) n := by
      unfold nuPetrescoBinomial
      rw [← List.map_coe_finRange_eq_range]
      simp only [List.map_map]
      apply congrArg List.prod
      apply List.map_congr_left
      intro j _
      rw [Ring.choose_natCast]
      change
        petrescoTerm x ((j : ℕ) + 1) ^
            Nat.choose m ((j : ℕ) + 1) =
          pow b (petrescoTerm x ((j : ℕ) + 1))
            (Nat.choose m ((j : ℕ) + 1) : ν)
      rw [pow_natCast]

/-- The completion satisfies Hall's finite scalar Petresco formula for
every scalar in the binomial ring. -/
lemma scalar_petresco {n : ℕ} (b : HCBasis G n)
    {ν : Type v} [CommRing ν] [BinomialRing ν]
    (x : List (HComp b ν)) (a : ν) :
    (x.map fun g => pow b g a).prod =
      nuPetrescoBinomial (petrescoTerm x) a n := by
  let vars :
      List (Fin n →
        BExpr (Option (Fin x.length × Fin n))) :=
    listVarTuples fun k i => some (k, i)
  let scalar : BExpr (Option (Fin x.length × Fin n)) :=
    .var none
  let lhs := listProdTuple b (vars.map fun g => powTuple b scalar g)
  let rhs :=
    listProdTuple b
      ((List.finRange n).map fun (j : Fin n) =>
        powTuple b (.choose scalar ((j : ℕ) + 1))
          (petrescoTermTuple b vars ((j : ℕ) + 1)))
  let assignment : Option (Fin x.length × Fin n) → ν
    | none => a
    | some ki => (x.get ki.1).coord ki.2
  let S : Option (Fin x.length × Fin n) → Set ℤ
    | none => Set.range fun m : ℕ => (m : ℤ)
    | some _ => Set.univ
  have hS : ∀ i, (S i).Infinite := by
    intro i
    cases i with
    | none =>
        exact Set.infinite_range_of_injective Int.ofNat_injective
    | some _ =>
        exact Set.infinite_univ
  have h :=
    tuple_int_infinite assignment
      (p := lhs) (q := rhs) S hS (by
        intro z hz
        obtain ⟨m, hm⟩ := hz none
        have hn := scalar_petresco_cast b
          (vars.map fun p =>
            (⟨evalTuple z p⟩ : HComp b ℤ)) m
        have hs :
            (⟨evalTuple z lhs⟩ : HComp b ℤ) =
              ⟨evalTuple z rhs⟩ := by
          simpa only [lhs, rhs, scalar, mk_tuple_prod,
            List.map_map, Function.comp_def, mk_tuple_pow,
            BExpr.eval_var, hm, mk_tuple_petresco,
            BExpr.eval_choose, nuPetrescoBinomial,
            nu_pow] using hn
        exact congrArg HComp.coord hs)
  have hs :
      (⟨evalTuple assignment lhs⟩ : HComp b ν) =
        ⟨evalTuple assignment rhs⟩ := by
    apply HComp.ext
    exact congrFun h
  have hvars :
      vars.map
          (fun p => (⟨evalTuple assignment p⟩ : HComp b ν)) =
        x := by
    simp [vars, assignment]
  have hlhs :
      (vars.map fun p =>
        pow b (⟨evalTuple assignment p⟩ : HComp b ν) a).prod =
        (x.map fun g => pow b g a).prod := by
    simpa only [List.map_map, Function.comp_def] using
      congrArg
        (fun y : List (HComp b ν) =>
          (y.map fun g => pow b g a).prod)
        hvars
  calc
    (x.map fun g => pow b g a).prod =
        (vars.map fun p =>
          pow b (⟨evalTuple assignment p⟩ : HComp b ν) a).prod :=
      hlhs.symm
    _ = nuPetrescoBinomial (petrescoTerm x) a n := by
      simpa only [lhs, rhs, scalar, assignment,
        mk_tuple_prod, List.map_map, Function.comp_def,
        mk_tuple_pow, BExpr.eval_var,
        mk_tuple_petresco, BExpr.eval_choose,
        hvars, nuPetrescoBinomial, nu_pow] using hs

end HComp

/-- Powered homomorphisms commute with finite scalar Petresco products. -/
lemma nu_petresco_product
    {ν : Type v} {G : Type u} {H : Type w}
    [CommRing ν] [BinomialRing ν] [Group G] [Group H]
    [NuPoweredGroup ν G] [NuPoweredGroup ν H]
    (f : NPHom ν G H) (tau : ℕ → G) (a : ν) (c : ℕ) :
    f (nuPetrescoBinomial tau a c) =
      nuPetrescoBinomial (fun j => f (tau j)) a c := by
  unfold nuPetrescoBinomial
  rw [map_list_prod, List.map_map]
  congr 1
  apply List.map_congr_left
  intro j _
  exact f.map_nuPow _ _

/-- Powered homomorphisms commute with tail-only scalar Petresco
products. -/
lemma nu_tail_product
    {ν : Type v} {G : Type u} {H : Type w}
    [CommRing ν] [BinomialRing ν] [Group G] [Group H]
    [NuPoweredGroup ν G] [NuPoweredGroup ν H]
    (f : NPHom ν G H) (tau : ℕ → G) (a : ν) (c : ℕ) :
    f (nuPetrescoTail tau a c) =
      nuPetrescoTail (fun j => f (tau j)) a c := by
  unfold nuPetrescoTail
  rw [map_list_prod, List.map_map]
  congr 1
  apply List.map_congr_left
  intro j _
  exact f.map_nuPow _ _

/-- Hall's powered-group axioms. Fields `pow_one`, `pow_add`, and
`pow_mul` are axiom (I), `conj_pow` is axiom (II), and
`scalar_petresco` is the finite form of axiom (III). -/
class SatisfiesPoweredAxioms (ν : Type v) (G : Type u)
    [CommRing ν] [BinomialRing ν] [Group G] [NuPoweredGroup ν G] : Prop where
  pow_one : ∀ x : G, nuPow (ν := ν) x 1 = x
  pow_add : ∀ (x : G) (a b : ν),
    nuPow (ν := ν) x (a + b) =
      nuPow (ν := ν) x a * nuPow (ν := ν) x b
  pow_mul : ∀ (x : G) (a b : ν),
    nuPow (ν := ν) x (a * b) =
      nuPow (ν := ν) (nuPow (ν := ν) x a) b
  conj_pow : ∀ (x y : G) (a : ν),
    y⁻¹ * nuPow (ν := ν) x a * y =
      nuPow (ν := ν) (y⁻¹ * x * y) a
  scalar_petresco : ∀ (x : List G) (a : ν), ∃ c : ℕ,
    (∀ w, c < w → petrescoTerm x w = 1) ∧
      (x.map fun g => nuPow (ν := ν) g a).prod =
        nuPetrescoBinomial (petrescoTerm x) a c

namespace HComp

noncomputable instance instPoweredAxioms {n : ℕ}
    (b : HCBasis G n)
    {ν : Type v} [CommRing ν] [BinomialRing ν] :
    SatisfiesPoweredAxioms ν (HComp b ν) where
  pow_one := by
    intro x
    simpa only [nu_pow] using pow_scalar_one b x
  pow_add := by
    intro x a c
    simpa only [nu_pow] using pow_add b x a c
  pow_mul := by
    intro x a c
    simpa only [nu_pow] using pow_mul b x a c
  conj_pow := by
    intro x y a
    simpa only [nu_pow] using conj_pow b x y a
  scalar_petresco := by
    intro x a
    exact ⟨n, fun w hw => petresco_term_length b x hw, by
      simpa only [nu_pow] using scalar_petresco b x a⟩

end HComp

@[simp]
lemma nu_pow_scalar {ν : Type v} {G : Type u} [CommRing ν]
    [BinomialRing ν] [Group G]
    [NuPoweredGroup ν G] [SatisfiesPoweredAxioms ν G] (x : G) :
    nuPow (ν := ν) x 1 = x :=
  SatisfiesPoweredAxioms.pow_one x

@[simp]
lemma nuPow_zero {ν : Type v} {G : Type u} [CommRing ν]
    [BinomialRing ν] [Group G]
    [NuPoweredGroup ν G] [SatisfiesPoweredAxioms ν G] (x : G) :
    nuPow (ν := ν) x 0 = 1 := by
  have h := SatisfiesPoweredAxioms.pow_add (ν := ν) x 0 0
  have hcancel := congrArg
    (fun z : G => (nuPow (ν := ν) x 0)⁻¹ * z) h
  simpa [mul_assoc] using hcancel.symm

@[simp]
lemma nuPow_neg {ν : Type v} {G : Type u} [CommRing ν]
    [BinomialRing ν] [Group G]
    [NuPoweredGroup ν G] [SatisfiesPoweredAxioms ν G]
    (x : G) (a : ν) :
    nuPow (ν := ν) x (-a) = (nuPow (ν := ν) x a)⁻¹ := by
  apply eq_inv_of_mul_eq_one_right
  calc
    nuPow (ν := ν) x a * nuPow (ν := ν) x (-a) =
        nuPow (ν := ν) x (a + -a) :=
      (SatisfiesPoweredAxioms.pow_add x a (-a)).symm
    _ = 1 := by simp

/-- Scalar powering by a natural number agrees with ordinary natural
powering. -/
@[simp]
lemma nu_nat_cast {ν : Type v} {G : Type u} [CommRing ν]
    [BinomialRing ν] [Group G]
    [NuPoweredGroup ν G] [SatisfiesPoweredAxioms ν G]
    (x : G) (m : ℕ) :
    nuPow (ν := ν) x (m : ν) = x ^ m := by
  induction m with
  | zero =>
      simp
  | succ m ih =>
      rw [Nat.cast_succ, SatisfiesPoweredAxioms.pow_add, ih,
        nu_pow_scalar, pow_succ]

/-- Scalar powering by an integer agrees with ordinary integer powering. -/
@[simp]
lemma nu_pow_cast {ν : Type v} {G : Type u} [CommRing ν]
    [BinomialRing ν] [Group G]
    [NuPoweredGroup ν G] [SatisfiesPoweredAxioms ν G]
    (x : G) (a : ℤ) :
    nuPow (ν := ν) x (a : ν) = x ^ a := by
  cases a with
  | ofNat m =>
      rw [Int.ofNat_eq_natCast, Int.cast_natCast, nu_nat_cast, zpow_natCast]
  | negSucc m =>
      rw [Int.cast_negSucc, nuPow_neg, nu_nat_cast, zpow_negSucc]

/-- Scalar powers preserve group inverses. -/
@[simp]
lemma nuPow_inv {ν : Type v} {G : Type u} [CommRing ν]
    [BinomialRing ν] [Group G]
    [NuPoweredGroup ν G] [SatisfiesPoweredAxioms ν G]
    (x : G) (a : ν) :
    nuPow (ν := ν) x⁻¹ a = (nuPow (ν := ν) x a)⁻¹ := by
  calc
    nuPow (ν := ν) x⁻¹ a =
        nuPow (ν := ν) (nuPow (ν := ν) x (-1)) a := by simp
    _ = nuPow (ν := ν) x ((-1) * a) :=
      (SatisfiesPoweredAxioms.pow_mul x (-1) a).symm
    _ = nuPow (ν := ν) x (-a) := by rw [neg_one_mul]
    _ = (nuPow (ν := ν) x a)⁻¹ := nuPow_neg x a

/-- Conjugation by `y` as a powered automorphism, written in Hall's
orientation `x ↦ y⁻¹ * x * y`. -/
def conjugationNuPowered {ν : Type v} {G : Type u}
    [CommRing ν] [BinomialRing ν] [Group G]
    [NuPoweredGroup ν G] [SatisfiesPoweredAxioms ν G]
    (y : G) : NPHom ν G G where
  toMonoidHom := (MulAut.conj y⁻¹).toMonoidHom
  map_nuPow' x a := by
    simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] using
      SatisfiesPoweredAxioms.conj_pow x y a

@[simp]
lemma conjugation_nu_powered {ν : Type v} {G : Type u}
    [CommRing ν] [BinomialRing ν] [Group G]
    [NuPoweredGroup ν G] [SatisfiesPoweredAxioms ν G]
    (y x : G) :
    conjugationNuPowered (ν := ν) y x = y⁻¹ * x * y := by
  simp [conjugationNuPowered]

/-- If `x / y` lies in a normal subgroup, every Petresco term for the
pair `x, y⁻¹` lies in that subgroup. This is the induction at the heart
of Hall's proof of Lemma 6.6. -/
lemma petresco_pair_div
    {G : Type u} [Group G] (K : Subgroup G) [K.Normal]
    {x y : G} (hxy : x / y ∈ K) :
    ∀ n : ℕ, petrescoTerm [x, y⁻¹] n ∈ K := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      cases n with
      | zero =>
          simp
      | succ w =>
          rw [petrescoTerm_succ]
          apply K.mul_mem
          · apply K.inv_mem
            unfold petrescoPriorProduct
            apply K.list_prod_mem
            intro z hz
            simp only [List.mem_map] at hz
            obtain ⟨j, _, rfl⟩ := hz
            apply K.pow_mem
            exact ih ((j : ℕ) + 1) (by omega)
          · have hquot : (x : G ⧸ K) = y :=
              QuotientGroup.eq_iff_div_mem.mpr hxy
            have hpowquot :=
              congrArg (fun z : G ⧸ K => z ^ (w + 1)) hquot
            have hdiv : x ^ (w + 1) / y ^ (w + 1) ∈ K := by
              apply QuotientGroup.eq_iff_div_mem.mp
              simpa only [QuotientGroup.mk_pow] using hpowquot
            simpa [div_eq_mul_inv] using hdiv

/-- A normal powered subgroup satisfies the congruence condition needed
to put scalar powers on its quotient. -/
theorem powered_nu_mod
    {ν : Type v} {G : Type u} [CommRing ν] [BinomialRing ν] [Group G]
    [NuPoweredGroup ν G] [SatisfiesPoweredAxioms ν G]
    (K : Subgroup G) [K.Normal] (hK : NuPoweredSubgroup ν K) :
    NCMod (ν := ν) K := by
  intro x y a hxy
  obtain ⟨c, _, hc⟩ :=
    SatisfiesPoweredAxioms.scalar_petresco [x, y⁻¹] a
  have hprod :
      nuPetrescoBinomial (petrescoTerm [x, y⁻¹]) a c ∈ K := by
    unfold nuPetrescoBinomial
    apply K.list_prod_mem
    intro z hz
    simp only [List.mem_map] at hz
    obtain ⟨j, _, rfl⟩ := hz
    apply hK
    exact petresco_pair_div K hxy ((j : ℕ) + 1)
  rw [← hc] at hprod
  simpa [div_eq_mul_inv] using hprod

namespace NPHom

variable {ν : Type v} {H : Type*} [Group H]
  [NuPoweredGroup ν G] [NuPoweredGroup ν H]

/-- The kernel congruence of a powered homomorphism respects scalar powers. -/
theorem nu_compatible_mod (f : NPHom ν G H) :
    NCMod (ν := ν) f.toMonoidHom.ker := by
  intro x y a hxy
  rw [MonoidHom.mem_ker] at hxy ⊢
  have hfxy : f x = f y := by
    apply div_eq_one.mp
    simpa using hxy
  simp [f.map_nuPow, hfxy]

end NPHom

namespace NCMod

variable {ν : Type v} {K : Subgroup G} [K.Normal]
  [NuPoweredGroup ν G]

/-- Congruent representatives have congruent scalar powers. This is the
second assertion of Hall's Lemma 6.6, isolated as the well-definedness
criterion for quotient exponentiation. -/
theorem pow_congr (hK : NCMod (ν := ν) K)
    {x y : G} (hxy : (x : G ⧸ K) = y) (a : ν) :
    ((nuPow (ν := ν) x a : G) : G ⧸ K) =
      nuPow (ν := ν) y a :=
  QuotientGroup.eq_iff_div_mem.mpr
    (hK x y a (QuotientGroup.eq_iff_div_mem.mp hxy))

end NCMod

/-- Scalar exponentiation induced on a quotient by a compatible normal
subgroup. -/
def quotientNuPow {ν : Type v} {G : Type u} [Group G]
    [NuPoweredGroup ν G] (K : Subgroup G) [K.Normal]
    (hK : NCMod (ν := ν) K) (q : G ⧸ K) (a : ν) :
    G ⧸ K :=
  Quotient.liftOn q
    (fun x : G => ((nuPow (ν := ν) x a : G) : G ⧸ K))
    (fun _ _ hxy => hK.pow_congr (Quotient.sound hxy) a)

@[simp]
lemma nu_pow_mk {ν : Type v} {G : Type u} [Group G]
    [NuPoweredGroup ν G] (K : Subgroup G) [K.Normal]
    (hK : NCMod (ν := ν) K) (x : G) (a : ν) :
    quotientNuPow K hK (x : G ⧸ K) a =
      ((nuPow (ν := ν) x a : G) : G ⧸ K) :=
  rfl

/-- The powered-group structure on the quotient from Hall's Lemma 6.6. -/
@[reducible]
def nuPoweredGroup {ν : Type v} {G : Type u} [Group G]
    [NuPoweredGroup ν G] (K : Subgroup G) [K.Normal]
    (hK : NCMod (ν := ν) K) :
    NuPoweredGroup ν (G ⧸ K) where
  pow := quotientNuPow K hK
  one_pow a := by
    change ((nuPow (ν := ν) (1 : G) a : G) : G ⧸ K) = 1
    rw [nuPow_one]
    rfl

/-- The natural quotient map, regarded as a powered homomorphism. -/
def nuPoweredHom {ν : Type v} {G : Type u} [Group G]
    [NuPoweredGroup ν G] (K : Subgroup G) [K.Normal]
    (hK : NCMod (ν := ν) K) :
    letI : NuPoweredGroup ν (G ⧸ K) := nuPoweredGroup K hK
    NPHom ν G (G ⧸ K) := by
  letI : NuPoweredGroup ν (G ⧸ K) := nuPoweredGroup K hK
  exact
    { toMonoidHom := QuotientGroup.mk' K
      map_nuPow' := fun _ _ => rfl }

/-- Hall's powered axioms descend to the powered quotient. -/
@[reducible]
def satisfiesPoweredAxioms
    {ν : Type v} {G : Type u} [CommRing ν] [BinomialRing ν]
    [Group G] [NuPoweredGroup ν G] [SatisfiesPoweredAxioms ν G]
    (K : Subgroup G) [K.Normal]
    (hK : NCMod (ν := ν) K) :
    letI : NuPoweredGroup ν (G ⧸ K) := nuPoweredGroup K hK
    SatisfiesPoweredAxioms ν (G ⧸ K) := by
  letI : NuPoweredGroup ν (G ⧸ K) := nuPoweredGroup K hK
  let q : NPHom ν G (G ⧸ K) := nuPoweredHom K hK
  exact
    { pow_one := by
        intro x
        induction x using Quotient.inductionOn' with
        | _ x =>
            change ((nuPow (ν := ν) x 1 : G) : G ⧸ K) = x
            rw [nu_pow_scalar]
      pow_add := by
        intro x a b
        induction x using Quotient.inductionOn' with
        | _ x =>
            change
              ((nuPow (ν := ν) x (a + b) : G) : G ⧸ K) =
                ((nuPow (ν := ν) x a : G) : G ⧸ K) *
                  ((nuPow (ν := ν) x b : G) : G ⧸ K)
            rw [SatisfiesPoweredAxioms.pow_add]
            rfl
      pow_mul := by
        intro x a b
        induction x using Quotient.inductionOn' with
        | _ x =>
            change
              ((nuPow (ν := ν) x (a * b) : G) : G ⧸ K) =
                ((nuPow (ν := ν) (nuPow (ν := ν) x a) b : G) :
                  G ⧸ K)
            rw [SatisfiesPoweredAxioms.pow_mul]
      conj_pow := by
        intro x y a
        induction x, y using Quotient.inductionOn₂' with
        | _ x y =>
            change
              ((y⁻¹ * nuPow (ν := ν) x a * y : G) : G ⧸ K) =
                ((nuPow (ν := ν) (y⁻¹ * x * y) a : G) : G ⧸ K)
            rw [SatisfiesPoweredAxioms.conj_pow]
      scalar_petresco := by
        intro x a
        have hsurj :
            Function.Surjective (List.map (QuotientGroup.mk' K)) :=
          List.map_surjective_iff.mpr (QuotientGroup.mk'_surjective K)
        obtain ⟨xs, rfl⟩ := hsurj x
        obtain ⟨c, htrivial, hc⟩ :=
          SatisfiesPoweredAxioms.scalar_petresco xs a
        refine ⟨c, ?_, ?_⟩
        · intro w hw
          rw [← map_petrescoTerm (QuotientGroup.mk' K) xs w, htrivial w hw]
          exact map_one (QuotientGroup.mk' K)
        have hmapped := congrArg q hc
        rw [map_list_prod, nu_petresco_product] at hmapped
        have hterm :
            (fun j => q (petrescoTerm xs j)) =
              petrescoTerm (xs.map q) := by
          funext j
          exact map_petrescoTerm q.toMonoidHom xs j
        rw [hterm] at hmapped
        simpa only [List.map_map, q.map_nuPow] using hmapped }

/-- **Hall, Lemma 6.6, quotient clause.** Under the compatibility condition
proved by Hall from the full powered-group axioms, the quotient is powered
and its natural projection is a surjective powered homomorphism with kernel
`K`. -/
theorem nu_powered_spec {ν : Type v} {G : Type u} [Group G]
    [NuPoweredGroup ν G] (K : Subgroup G) [K.Normal]
    (hK : NCMod (ν := ν) K) :
    letI : NuPoweredGroup ν (G ⧸ K) := nuPoweredGroup K hK
    Function.Surjective (nuPoweredHom K hK) ∧
      (nuPoweredHom K hK).toMonoidHom.ker = K := by
  letI : NuPoweredGroup ν (G ⧸ K) := nuPoweredGroup K hK
  constructor
  · simpa [nuPoweredHom] using QuotientGroup.mk'_surjective K
  · simp [nuPoweredHom]

/-- **Hall, Lemma 6.6.** Every normal powered subgroup of a group
satisfying Hall's powered axioms admits the induced powered quotient, and
the natural map is a surjective powered homomorphism with that kernel. -/
theorem nu_powered_group
    {ν : Type v} {G : Type u} [CommRing ν] [BinomialRing ν] [Group G]
    [NuPoweredGroup ν G] [SatisfiesPoweredAxioms ν G]
    (K : Subgroup G) [K.Normal] (hK : NuPoweredSubgroup ν K) :
    ∃ hcompat : NCMod (ν := ν) K,
      letI : NuPoweredGroup ν (G ⧸ K) := nuPoweredGroup K hcompat
      SatisfiesPoweredAxioms ν (G ⧸ K) ∧
        Function.Surjective (nuPoweredHom K hcompat) ∧
          (nuPoweredHom K hcompat).toMonoidHom.ker = K := by
  let hcompat := powered_nu_mod K hK
  exact
    ⟨hcompat, satisfiesPoweredAxioms K hcompat,
      nu_powered_spec K hcompat⟩

/-- The ordered product `c₁^a₁ ... cₙ^aₙ` using scalar powers in a
`ν`-powered group. -/
def orderedNuProduct {ν : Type v} {H : Type w} {ι : Type*}
    [Group H] [NuPoweredGroup ν H]
    (c : ι → H) (a : ι → ν) (l : List ι) : H :=
  (l.map fun i => nuPow (ν := ν) (c i) (a i)).prod

/-- The ordered scalar-powered product associated to a finite Hall
coordinate tuple. -/
def nuBasisProduct {ν : Type v} {H : Type w} {n : ℕ}
    [Group H] [NuPoweredGroup ν H]
    (c : Fin n → H) (a : Fin n → ν) : H :=
  orderedNuProduct c a (List.finRange n)

/-- Conjugation distributes over ordered scalar-powered products. -/
lemma conjugate_nu_product
    {ν : Type v} {H : Type w} {ι : Type*}
    [CommRing ν] [BinomialRing ν] [Group H]
    [NuPoweredGroup ν H] [SatisfiesPoweredAxioms ν H]
    (u : H) (c : ι → H) (a : ι → ν) :
    ∀ l : List ι,
      u⁻¹ * orderedNuProduct c a l * u =
        orderedNuProduct (fun i => u⁻¹ * c i * u) a l
  | [] => by
      simp [orderedNuProduct]
  | i :: l => by
      rw [show
        orderedNuProduct c a (i :: l) =
          nuPow (ν := ν) (c i) (a i) *
            orderedNuProduct c a l by
        simp [orderedNuProduct]]
      rw [show
        orderedNuProduct (fun i => u⁻¹ * c i * u) a (i :: l) =
          nuPow (ν := ν) (u⁻¹ * c i * u) (a i) *
            orderedNuProduct (fun i => u⁻¹ * c i * u) a l by
        simp [orderedNuProduct]]
      calc
        u⁻¹ * (nuPow (ν := ν) (c i) (a i) *
              orderedNuProduct c a l) * u =
            (u⁻¹ * nuPow (ν := ν) (c i) (a i) * u) *
              (u⁻¹ * orderedNuProduct c a l * u) := by
          group
        _ = nuPow (ν := ν) (u⁻¹ * c i * u) (a i) *
              orderedNuProduct (fun i => u⁻¹ * c i * u) a l := by
          rw [SatisfiesPoweredAxioms.conj_pow,
            conjugate_nu_product u c a l]

/-- Axiom (II) gives Hall's factorization of one generator conjugated by
a scalar power of a head element. -/
lemma nu_conjugate_generator
    {ν : Type v} {H : Type w}
    [CommRing ν] [BinomialRing ν] [Group H]
    [NuPoweredGroup ν H] [SatisfiesPoweredAxioms ν H]
    (u v : H) (a : ν) :
    nuPow (ν := ν) u (-a) * v * nuPow (ν := ν) u a =
      (nuPow (ν := ν) u (-a) *
        nuPow (ν := ν) (v * u * v⁻¹) a) * v := by
  have h := SatisfiesPoweredAxioms.conj_pow u v⁻¹ a
  simp only [inv_inv] at h
  rw [← h]
  group

@[simp]
lemma nu_canonical_basis {ν : Type v} {H : Type w}
    [Group H] [NuPoweredGroup ν H]
    (c : Fin 0 → H) (a : Fin 0 → ν) :
    nuBasisProduct c a = 1 := by
  simp [nuBasisProduct, orderedNuProduct]

/-- Splitting off the first coordinate splits an ordered scalar-powered
product into its head factor and its tail product. -/
lemma nu_basis_succ {ν : Type v} {H : Type w} {n : ℕ}
    [Group H] [NuPoweredGroup ν H]
    (c : Fin (n + 1) → H) (a : Fin (n + 1) → ν) :
    nuBasisProduct c a =
      nuPow (ν := ν) (c 0) (a 0) *
        nuBasisProduct (fun i => c i.succ) (Fin.tail a) := by
  simp [nuBasisProduct, orderedNuProduct, List.finRange_succ,
    Function.comp_def, Fin.tail]

@[simp]
lemma nu_basis_one {ν : Type v} {H : Type w}
    [Group H] [NuPoweredGroup ν H]
    (c : Fin 1 → H) (a : Fin 1 → ν) :
    nuBasisProduct c a = nuPow (ν := ν) (c 0) (a 0) := by
  rw [nu_basis_succ]
  simp

/-- At integer scalars, the powered ordered product is the ordinary
integer-powered ordered product. -/
lemma ordered_nu_cast
    {ν : Type v} {H : Type w} {ι : Type*}
    [CommRing ν] [BinomialRing ν] [Group H]
    [NuPoweredGroup ν H] [SatisfiesPoweredAxioms ν H]
    (c : ι → H) (a : ι → ℤ) (l : List ι) :
    orderedNuProduct c (fun i => (a i : ν)) l =
      orderedZPow c a l := by
  unfold orderedNuProduct orderedZPow
  apply congrArg List.prod
  apply List.map_congr_left
  intro i _
  rw [nu_pow_cast]

/-- At integer coordinates, the powered canonical product is the ordinary
canonical product. -/
lemma nu_int_cast
    {ν : Type v} {H : Type w} {n : ℕ}
    [CommRing ν] [BinomialRing ν] [Group H]
    [NuPoweredGroup ν H] [SatisfiesPoweredAxioms ν H]
    (c : Fin n → H) (a : Fin n → ℤ) :
    nuBasisProduct c (fun i => (a i : ν)) =
      canonicalBasisProduct c a :=
  ordered_nu_cast c a (List.finRange n)

/-- Ordinary homomorphisms commute with canonical integer-powered
products. -/
lemma canonical_basis_product
    {G : Type u} {H : Type w} [Group G] [Group H] {n : ℕ}
    (f : G →* H) (c : Fin n → G) (a : Fin n → ℤ) :
    f (canonicalBasisProduct c a) =
      canonicalBasisProduct (fun i => f (c i)) a := by
  unfold canonicalBasisProduct
  apply ordered_z_list
  intro i _
  rfl

/-- An ordinary homomorphism out of a group with a Hall canonical basis is
determined by its values on the selected canonical generators. -/
lemma monoid_ext_generators
    {G : Type u} {H : Type w} [Group G] [Group H] {n : ℕ}
    (b : HCBasis G n) (f g : G →* H)
    (h : ∀ i, f (b.generators i) = g (b.generators i)) :
    f = g := by
  apply MonoidHom.ext
  intro x
  rw [← b.canonical_basis_coord x,
    canonical_basis_product, canonical_basis_product]
  unfold canonicalBasisProduct orderedZPow
  apply congrArg List.prod
  apply List.map_congr_left
  intro i _
  change f (b.generators i) ^ b.coord x i =
    g (b.generators i) ^ b.coord x i
  rw [h i]

namespace HComp

/-- Candidate for Hall's extension theorem: evaluate a completion point by
replacing each canonical generator with its image and using scalar powers. -/
def extensionCandidate {n : ℕ} (b : HCBasis G n)
    {ν : Type v} {H : Type w} [Group H] [NuPoweredGroup ν H]
    (f : G →* H) (x : HComp b ν) : H :=
  nuBasisProduct (fun i => f (b.generators i)) x.coord

/-- Remove the head coordinate from a completion point. -/
def tailPoint {n : ℕ} (b : HCBasis G (n + 1))
    {ν : Type v} (x : HComp b ν) :
    HComp b.tailBasis ν :=
  ⟨Fin.tail x.coord⟩

@[simp]
lemma tailPoint_coord {n : ℕ} (b : HCBasis G (n + 1))
    {ν : Type v} (x : HComp b ν) :
    (tailPoint b x).coord = Fin.tail x.coord :=
  rfl

/-- Prefix a zero head coordinate to a first-tail completion point. -/
def tailLift {n : ℕ} (b : HCBasis G (n + 1))
    {ν : Type v} [Zero ν] (x : HComp b.tailBasis ν) :
    HComp b ν :=
  ⟨Fin.cons 0 x.coord⟩

@[simp]
lemma tail_lift_coord {n : ℕ} (b : HCBasis G (n + 1))
    {ν : Type v} [Zero ν] (x : HComp b.tailBasis ν) :
    (tailLift b x).coord 0 = 0 := by
  simp [tailLift]

@[simp]
lemma tail_point_lift {n : ℕ} (b : HCBasis G (n + 1))
    {ν : Type v} [Zero ν] (x : HComp b.tailBasis ν) :
    tailPoint b (tailLift b x) = x := by
  apply HComp.ext
  simp [tailPoint, tailLift]

lemma tail_point_coord {n : ℕ}
    (b : HCBasis G (n + 1))
    {ν : Type v} [Zero ν] (x : HComp b ν)
    (hx : x.coord 0 = 0) :
    tailLift b (tailPoint b x) = x := by
  apply HComp.ext
  intro i
  cases i using Fin.cases with
  | zero => simpa using hx.symm
  | succ i => rfl

/-- Prefix a zero expression to an expression-valued first-tail tuple. -/
def tailLiftTuple {n : ℕ} {κ : Type*}
    (x : Fin n → BExpr κ) :
    Fin (n + 1) → BExpr κ :=
  Fin.cons 0 x

@[simp]
lemma tuple_tail_lift {n : ℕ} {κ R : Type*}
    [CommRing R] [BinomialRing R]
    (z : κ → R) (x : Fin n → BExpr κ) :
    evalTuple z (tailLiftTuple x) = Fin.cons 0 (evalTuple z x) := by
  funext i
  cases i using Fin.cases <;> simp [tailLiftTuple, evalTuple]

/-- The zero-prefix inclusion of the first-tail completion is
multiplicative. -/
@[simp]
lemma tailLift_mul {n : ℕ} (b : HCBasis G (n + 1))
    {ν : Type v} [CommRing ν] [BinomialRing ν]
    (x y : HComp b.tailBasis ν) :
    tailLift b (x * y) = tailLift b x * tailLift b y := by
  let xvars :
      Fin n → BExpr (Sum (Fin n) (Fin n)) :=
    varTuple fun i => Sum.inl i
  let yvars :
      Fin n → BExpr (Sum (Fin n) (Fin n)) :=
    varTuple fun i => Sum.inr i
  have h :=
    eval_tuple_int (Sum.elim x.coord y.coord)
      (p := tailLiftTuple (mulTuple b.tailBasis xvars yvars))
      (q := mulTuple b (tailLiftTuple xvars) (tailLiftTuple yvars)) (by
        intro z
        rw [tuple_tail_lift, tuple_mul_int,
          tuple_mul_int, tuple_tail_lift,
          tuple_tail_lift]
        rw [show
          b.coord.symm (Fin.cons 0 (evalTuple z xvars)) =
            ((b.tailBasis.coord.symm (evalTuple z xvars) : b.tail 1) : G) by
              rfl]
        rw [show
          b.coord.symm (Fin.cons 0 (evalTuple z yvars)) =
            ((b.tailBasis.coord.symm (evalTuple z yvars) : b.tail 1) : G) by
              rfl]
        exact
          (b.coord_coe_cons
            (b.tailBasis.coord.symm (evalTuple z xvars) *
              b.tailBasis.coord.symm (evalTuple z yvars))).symm)
  apply HComp.ext
  intro i
  simpa [tailLift, xvars, yvars] using congrFun h i

/-- The zero-prefix inclusion preserves scalar powering. -/
@[simp]
lemma tail_lift_nu {n : ℕ} (b : HCBasis G (n + 1))
    {ν : Type v} [CommRing ν] [BinomialRing ν]
    (x : HComp b.tailBasis ν) (a : ν) :
    tailLift b (nuPow (ν := ν) x a) =
      nuPow (ν := ν) (tailLift b x) a := by
  let vars : Fin n → BExpr (Option (Fin n)) :=
    varTuple some
  let scalar : BExpr (Option (Fin n)) := .var none
  let assignment : Option (Fin n) → ν
    | none => a
    | some i => x.coord i
  have h :=
    eval_tuple_int assignment
      (p := tailLiftTuple (powTuple b.tailBasis scalar vars))
      (q := powTuple b scalar (tailLiftTuple vars)) (by
        intro z
        rw [tuple_tail_lift, tuple_pow_int,
          tuple_pow_int, tuple_tail_lift]
        rw [show
          b.coord.symm (Fin.cons 0 (evalTuple z vars)) =
            ((b.tailBasis.coord.symm (evalTuple z vars) : b.tail 1) : G) by
              rfl]
        exact
          (b.coord_coe_cons
            (b.tailBasis.coord.symm (evalTuple z vars) ^
              BExpr.eval z scalar)).symm)
  apply HComp.ext
  intro i
  simpa [tailLift, vars, scalar, assignment] using congrFun h i

/-- The zero-prefix inclusion preserves the identity. -/
@[simp]
lemma tailLift_one {n : ℕ} (b : HCBasis G (n + 1))
    {ν : Type v} [CommRing ν] [BinomialRing ν] :
    tailLift b (1 : HComp b.tailBasis ν) = 1 := by
  apply mul_left_cancel (a := tailLift b (1 : HComp b.tailBasis ν))
  simpa using
    (tailLift_mul b (1 : HComp b.tailBasis ν) 1).symm

/-- The zero-prefix inclusion of the first-tail completion as a powered
homomorphism. -/
noncomputable def tailLiftHom {n : ℕ}
    (b : HCBasis G (n + 1))
    {ν : Type v} [CommRing ν] [BinomialRing ν] :
    NPHom ν (HComp b.tailBasis ν) (HComp b ν) where
  toFun := tailLift b
  map_one' := tailLift_one b
  map_mul' := tailLift_mul b
  map_nuPow' := tail_lift_nu b

/-- On integer points, the powered tail inclusion extends the original
subgroup inclusion. -/
@[simp]
lemma tail_comp_embedding {n : ℕ}
    (b : HCBasis G (n + 1))
    {ν : Type v} [CommRing ν] [BinomialRing ν] :
    (tailLiftHom b : NPHom ν
        (HComp b.tailBasis ν) (HComp b ν)).toMonoidHom.comp
        (embedding b.tailBasis) =
      (embedding b).comp (b.tail 1).subtype := by
  apply MonoidHom.ext
  intro g
  apply HComp.ext
  intro i
  cases i using Fin.cases with
  | zero =>
      change (0 : ν) = (b.coord (g : G) 0 : ν)
      rw [b.coord_coe_cons]
      simp
  | succ i =>
      change ((b.tailBasis).coord g i : ν) =
        (b.coord (g : G) i.succ : ν)
      rfl

/-- Conjugate a first-tail completion point by a scalar power of the
embedded head generator, then remove the resulting zero head coordinate. -/
noncomputable def conjugateTailCompletion {n : ℕ}
    (b : HCBasis G (n + 1))
    {ν : Type v} [CommRing ν] [BinomialRing ν]
    (a : ν) (x : HComp b.tailBasis ν) :
    HComp b.tailBasis ν :=
  tailPoint b
    (nuPow (ν := ν)
        ((embedding b : G → HComp b ν) (b.generators 0)) (-a) *
      tailLift b x *
      nuPow (ν := ν)
        ((embedding b : G → HComp b ν) (b.generators 0)) a)

/-- Lifting scalar head-conjugation recovers the corresponding
conjugation in the full completion. -/
lemma tail_lift_conjugate {n : ℕ}
    (b : HCBasis G (n + 1))
    {ν : Type v} [CommRing ν] [BinomialRing ν]
    (a : ν) (x : HComp b.tailBasis ν) :
    tailLift b (conjugateTailCompletion b a x) =
      nuPow (ν := ν)
          ((embedding b : G → HComp b ν) (b.generators 0)) (-a) *
        tailLift b x *
        nuPow (ν := ν)
          ((embedding b : G → HComp b ν) (b.generators 0)) a := by
  apply tail_point_coord
  rw [coord_mul_zero, coord_mul_zero, coord_nu_zero,
    coord_nu_zero, tail_lift_coord]
  simp

/-- The zero-prefix tail inclusion is injective. -/
lemma tailLift_injective {n : ℕ}
    (b : HCBasis G (n + 1))
    {ν : Type v} [Zero ν] :
    Function.Injective (tailLift b :
      HComp b.tailBasis ν → HComp b ν) :=
  Function.LeftInverse.injective (tail_point_lift b)

/-- Scalar head-conjugation fixes the identity tail point. -/
@[simp]
lemma conjugate_tail_completion {n : ℕ}
    (b : HCBasis G (n + 1))
    {ν : Type v} [CommRing ν] [BinomialRing ν] (a : ν) :
    conjugateTailCompletion b a (1 : HComp b.tailBasis ν) = 1 := by
  apply tailLift_injective b
  rw [tail_lift_conjugate, tailLift_one]
  simp

/-- Scalar head-conjugation is multiplicative on the tail completion. -/
lemma conjugate_tail_mul {n : ℕ}
    (b : HCBasis G (n + 1))
    {ν : Type v} [CommRing ν] [BinomialRing ν]
    (a : ν) (x y : HComp b.tailBasis ν) :
    conjugateTailCompletion b a (x * y) =
      conjugateTailCompletion b a x * conjugateTailCompletion b a y := by
  apply tailLift_injective b
  rw [tail_lift_conjugate, tailLift_mul, tailLift_mul,
    tail_lift_conjugate, tail_lift_conjugate]
  rw [nuPow_neg]
  group

/-- Scalar head-conjugation preserves scalar powering on the tail
completion. -/
lemma conjugate_nu_pow {n : ℕ}
    (b : HCBasis G (n + 1))
    {ν : Type v} [CommRing ν] [BinomialRing ν]
    (a c : ν) (x : HComp b.tailBasis ν) :
    conjugateTailCompletion b a (nuPow (ν := ν) x c) =
      nuPow (ν := ν) (conjugateTailCompletion b a x) c := by
  apply tailLift_injective b
  rw [tail_lift_conjugate, tail_lift_nu, tail_lift_nu,
    tail_lift_conjugate, nuPow_neg,
    SatisfiesPoweredAxioms.conj_pow]

/-- Scalar head-conjugation as a powered endomorphism of the first-tail
completion. -/
noncomputable def conjugateCompletionHom {n : ℕ}
    (b : HCBasis G (n + 1))
    {ν : Type v} [CommRing ν] [BinomialRing ν] (a : ν) :
    NPHom ν (HComp b.tailBasis ν)
      (HComp b.tailBasis ν) where
  toFun := conjugateTailCompletion b a
  map_one' := conjugate_tail_completion b a
  map_mul' := conjugate_tail_mul b a
  map_nuPow' := fun x c => conjugate_nu_pow b a c x

/-- The constant symbolic tuple of an original group element. -/
def constantTuple {n : ℕ} (b : HCBasis G n)
    {κ : Type*} (g : G) :
    Fin n → BExpr κ :=
  fun i => .const (b.coord g i)

@[simp]
lemma mk_tuple_constant {n : ℕ}
    (b : HCBasis G n)
    {κ R : Type*} [CommRing R] [BinomialRing R]
    (z : κ → R) (g : G) :
    (⟨evalTuple z (constantTuple b g)⟩ : HComp b R) =
      embedding b g := by
  apply HComp.ext
  intro i
  simp [evalTuple, constantTuple, embedding, ofIntCast]

/-- Symbolic tuple for the completion map induced by an ordinary
homomorphism between groups with Hall bases. -/
noncomputable def homTuple
    {A : Type u} {B : Type w} [Group A] [Group B]
    {m n : ℕ} (c : HCBasis A m)
    (b : HCBasis B n) (f : A →* B)
    {κ : Type*} (x : Fin m → BExpr κ) :
    Fin n → BExpr κ :=
  listProdTuple b
    ((List.finRange m).map fun i =>
      powTuple b (x i) (constantTuple b (f (c.generators i))))

/-- Evaluating an induced-homomorphism tuple is the corresponding
candidate extension into the target completion. -/
@[simp]
lemma mk_tuple_hom
    {A : Type u} {B : Type w} [Group A] [Group B]
    {m n : ℕ} (c : HCBasis A m)
    (b : HCBasis B n) (f : A →* B)
    {κ R : Type*} [CommRing R] [BinomialRing R]
    (z : κ → R) (x : Fin m → BExpr κ) :
    (⟨evalTuple z (homTuple c b f x)⟩ : HComp b R) =
      extensionCandidate c ((embedding b).comp f)
        ⟨evalTuple z x⟩ := by
  unfold homTuple extensionCandidate nuBasisProduct
    orderedNuProduct
  rw [mk_tuple_prod]
  simp only [List.map_map, nu_pow]
  apply congrArg List.prod
  apply List.map_congr_left
  intro i _
  change
    (⟨evalTuple z
      (powTuple b (x i) (constantTuple b (f (c.generators i))))⟩ :
        HComp b R) =
      pow b (((embedding b).comp f) (c.generators i)) (evalTuple z x i)
  rw [mk_tuple_pow, mk_tuple_constant]
  rfl

/-- The constant symbolic tuple of one original canonical generator. -/
def canonicalGeneratorTuple {n : ℕ} (b : HCBasis G n)
    {κ : Type*} (i : Fin n) :
    Fin n → BExpr κ :=
  fun j => .const (b.coord (b.generators i) j)

/-- The symbolic completion tuple obtained by multiplying canonical
generator powers with expression-valued exponents. -/
noncomputable def canonicalProductTuple {n : ℕ}
    (b : HCBasis G n) {κ : Type*}
    (a : Fin n → BExpr κ) :
    Fin n → BExpr κ :=
  listProdTuple b
    ((List.finRange n).map fun i =>
      powTuple b (a i) (canonicalGeneratorTuple b i))

@[simp]
lemma mk_tuple_generator {n : ℕ}
    (b : HCBasis G n) {κ R : Type*}
    [CommRing R] [BinomialRing R] (z : κ → R) (i : Fin n) :
    (⟨evalTuple z (canonicalGeneratorTuple b i)⟩ :
      HComp b R) =
        embedding b (b.generators i) := by
  apply HComp.ext
  intro j
  simp [evalTuple, canonicalGeneratorTuple, embedding, ofIntCast]

/-- Evaluating the symbolic canonical-product tuple gives the ordered
powered product of the embedded canonical generators. -/
lemma mk_tuple_product {n : ℕ}
    (b : HCBasis G n) {κ R : Type*}
    [CommRing R] [BinomialRing R] (z : κ → R)
    (a : Fin n → BExpr κ) :
    (⟨evalTuple z (canonicalProductTuple b a)⟩ :
      HComp b R) =
        nuBasisProduct
          (fun i => (embedding b : G → HComp b R)
            (b.generators i))
          (fun i => BExpr.eval z (a i)) := by
  unfold canonicalProductTuple nuBasisProduct orderedNuProduct
  rw [mk_tuple_prod]
  simp only [List.map_map, Function.comp_def, mk_tuple_pow,
    nu_pow, mk_tuple_generator]

/-- Over integer assignments, multiplying the canonical generator powers
recovers the assigned coordinate tuple. -/
lemma tuple_var_int {n : ℕ}
    (b : HCBasis G n) (z : Fin n → ℤ) :
    evalTuple z (canonicalProductTuple b fun i => .var i) = z := by
  have h := mk_tuple_product b z (fun i => .var i)
  have hprod :
      nuBasisProduct
          (fun i => (embedding b : G → HComp b ℤ)
            (b.generators i))
          z =
        (embedding b : G → HComp b ℤ)
          (canonicalBasisProduct b.generators z) := by
    calc
      nuBasisProduct
          (fun i => (embedding b : G → HComp b ℤ)
            (b.generators i))
          z =
          canonicalBasisProduct
            (fun i => (embedding b : G → HComp b ℤ)
              (b.generators i))
            z := by
        simpa using
          (nu_int_cast
            (ν := ℤ)
            (fun i => (embedding b : G → HComp b ℤ)
              (b.generators i))
            z)
      _ = (embedding b : G → HComp b ℤ)
          (canonicalBasisProduct b.generators z) :=
        (canonical_basis_product (embedding b) b.generators z).symm
  simp only [BExpr.eval_var] at h
  rw [hprod] at h
  apply congrArg HComp.coord at h
  simpa [evalTuple, embedding, ofIntCast, b.coord_basis_product] using h

/-- Multiplying the canonical generator powers recovers every completion
point over every binomial ring. -/
lemma tuple_canonical_var {n : ℕ}
    (b : HCBasis G n)
    {ν : Type v} [CommRing ν] [BinomialRing ν] (z : Fin n → ν) :
    evalTuple z (canonicalProductTuple b fun i => .var i) = z := by
  have h :=
    eval_tuple_int z
      (p := canonicalProductTuple b fun i => .var i)
      (q := fun i => .var i) (by
        intro x
        rw [tuple_var_int]
        rfl)
  simpa [evalTuple] using h

/-- Every completion point is the ordered scalar-powered product of its
embedded Hall generators. -/
lemma nu_basis_generators {n : ℕ}
    (b : HCBasis G n)
    {ν : Type v} [CommRing ν] [BinomialRing ν]
    (x : HComp b ν) :
    nuBasisProduct
        (fun i => (embedding b : G → HComp b ν)
          (b.generators i))
        x.coord =
      x := by
  have h := mk_tuple_product b x.coord (fun i => .var i)
  rw [tuple_canonical_var] at h
  simpa only [BExpr.eval_var] using h.symm

/-- A scalar power of the embedded head generator has just its head
coordinate nonzero. -/
lemma nu_embedding_generator {n : ℕ}
    (b : HCBasis G (n + 1))
    {ν : Type v} [CommRing ν] [BinomialRing ν] (a : ν) :
    nuPow (ν := ν)
        ((embedding b : G → HComp b ν) (b.generators 0)) a =
      ⟨Fin.cons a 0⟩ := by
  have h :=
    nu_basis_generators b
      (⟨Fin.cons a 0⟩ : HComp b ν)
  rw [nu_basis_succ] at h
  simpa [nuBasisProduct, orderedNuProduct] using h

/-- Lifting a first-tail point is the ordered scalar-powered product of
the embedded later generators. -/
lemma nu_embedding_generators {n : ℕ}
    (b : HCBasis G (n + 1))
    {ν : Type v} [CommRing ν] [BinomialRing ν]
    (x : HComp b.tailBasis ν) :
    nuBasisProduct
        (fun i => (embedding b : G → HComp b ν)
          (b.generators i.succ))
        x.coord =
      tailLift b x := by
  have h :=
    nu_basis_generators b (tailLift b x)
  rw [nu_basis_succ] at h
  simpa [tailLift] using h

/-- Every completion point splits as its scalar head power times a lifted
first-tail point. -/
lemma nu_head_lift {n : ℕ}
    (b : HCBasis G (n + 1))
    {ν : Type v} [CommRing ν] [BinomialRing ν]
    (x : HComp b ν) :
    x =
      nuPow (ν := ν)
          ((embedding b : G → HComp b ν) (b.generators 0))
          (x.coord 0) *
        tailLift b (tailPoint b x) := by
  have h := nu_basis_generators b x
  rw [nu_basis_succ,
    nu_embedding_generators] at h
  exact h.symm

/-- The tail coordinates of multiplication are obtained by conjugating
the left tail by the right head scalar, then multiplying the right tail. -/
lemma tailPoint_mul {n : ℕ}
    (b : HCBasis G (n + 1))
    {ν : Type v} [CommRing ν] [BinomialRing ν]
    (x y : HComp b ν) :
    tailPoint b (x * y) =
      conjugateTailCompletion b (y.coord 0) (tailPoint b x) *
        tailPoint b y := by
  apply (Function.LeftInverse.injective (tail_point_lift b))
  apply mul_left_cancel
    (a := nuPow (ν := ν)
      ((embedding b : G → HComp b ν) (b.generators 0))
      (x.coord 0 + y.coord 0))
  calc
    nuPow (ν := ν)
          ((embedding b : G → HComp b ν) (b.generators 0))
          (x.coord 0 + y.coord 0) *
        tailLift b (tailPoint b (x * y)) =
      x * y := by
        rw [← coord_mul_zero b x y]
        exact (nu_head_lift b (x * y)).symm
    _ =
        nuPow (ν := ν)
            ((embedding b : G → HComp b ν) (b.generators 0))
            (x.coord 0 + y.coord 0) *
          tailLift b
            (conjugateTailCompletion b (y.coord 0) (tailPoint b x) *
              tailPoint b y) := by
      calc
        x * y =
            (nuPow (ν := ν)
                ((embedding b : G → HComp b ν) (b.generators 0))
                (x.coord 0) *
              tailLift b (tailPoint b x)) *
            (nuPow (ν := ν)
                ((embedding b : G → HComp b ν) (b.generators 0))
                (y.coord 0) *
              tailLift b (tailPoint b y)) := by
          rw [← nu_head_lift b x,
            ← nu_head_lift b y]
        _ =
            nuPow (ν := ν)
                ((embedding b : G → HComp b ν) (b.generators 0))
                (x.coord 0 + y.coord 0) *
              ((nuPow (ν := ν)
                    ((embedding b : G → HComp b ν) (b.generators 0))
                    (-y.coord 0) *
                  tailLift b (tailPoint b x) *
                  nuPow (ν := ν)
                    ((embedding b : G → HComp b ν)
                      (b.generators 0))
                    (y.coord 0)) *
                tailLift b (tailPoint b y)) := by
          rw [SatisfiesPoweredAxioms.pow_add, nuPow_neg]
          group
        _ =
            nuPow (ν := ν)
                ((embedding b : G → HComp b ν) (b.generators 0))
                (x.coord 0 + y.coord 0) *
              tailLift b
                (conjugateTailCompletion b (y.coord 0) (tailPoint b x) *
                  tailPoint b y) := by
          rw [tailLift_mul, tail_lift_conjugate]

/-- Evaluating the candidate extension in the completion itself is the
identity. -/
@[simp]
lemma candidate_embedding_self {n : ℕ}
    (b : HCBasis G n)
    {ν : Type v} [CommRing ν] [BinomialRing ν]
    (x : HComp b ν) :
    extensionCandidate b (embedding b) x = x :=
  nu_basis_generators b x

/-- The candidate extension agrees with the original homomorphism on the
embedded integer points. -/
@[simp]
lemma extensionCandidate_embedding {n : ℕ} (b : HCBasis G n)
    {ν : Type v} {H : Type w}
    [CommRing ν] [BinomialRing ν] [Group H]
    [NuPoweredGroup ν H] [SatisfiesPoweredAxioms ν H]
    (f : G →* H) (g : G) :
    extensionCandidate b f
      (embedding b g : HComp b ν) = f g := by
  calc
    extensionCandidate b f (embedding b g : HComp b ν) =
        canonicalBasisProduct (fun i => f (b.generators i)) (b.coord g) := by
      exact nu_int_cast _ _
    _ = f (canonicalBasisProduct b.generators (b.coord g)) :=
      (canonical_basis_product f b.generators (b.coord g)).symm
    _ = f g := by rw [b.canonical_basis_coord]

/-- The map on coordinate completions induced by an ordinary
homomorphism between the original groups. -/
noncomputable def completionMap
    {A : Type u} {B : Type w} [Group A] [Group B]
    {m n : ℕ} (c : HCBasis A m)
    (b : HCBasis B n) (f : A →* B)
    {R : Type*} [CommRing R] [BinomialRing R]
    (x : HComp c R) :
    HComp b R :=
  extensionCandidate c ((embedding b).comp f) x

/-- If an ordinary homomorphism acts on canonical coordinates by inserting
zeros and reindexing, its induced completion map has the same coordinate
formula over every binomial ring. -/
lemma completion_coord_reindex
    {A : Type u} {B : Type w} [Group A] [Group B]
    {m n : ℕ} (c : HCBasis A m)
    (b : HCBasis B n) (f : A →* B)
    (e : Fin n → Option (Fin m))
    (he : ∀ (g : A) (i : Fin n),
      b.coord (f g) i =
        match e i with
        | none => 0
        | some j => c.coord g j)
    {R : Type*} [CommRing R] [BinomialRing R]
    (x : HComp c R) (i : Fin n) :
    (completionMap c b f x).coord i =
      match e i with
      | none => 0
      | some j => x.coord j := by
  let vars : Fin m → BExpr (Fin m) := varTuple id
  let rhs : BExpr (Fin m) :=
    match e i with
    | none => 0
    | some j => .var j
  have h :=
    BExpr.eval_int x.coord
      (p := homTuple c b f vars i) (q := rhs) (by
        intro z
        have hs :
            (⟨evalTuple z (homTuple c b f vars)⟩ :
                HComp b ℤ) =
              embedding b (f (c.coord.symm z)) := by
          rw [mk_tuple_hom]
          have hz :
              (⟨evalTuple z vars⟩ : HComp c ℤ) =
                embedding c (c.coord.symm z) := by
            apply HComp.ext
            intro j
            simp [vars, embedding, ofIntCast]
          rw [hz, extensionCandidate_embedding]
          rfl
        have hi := congrFun (congrArg HComp.coord hs) i
        change
          BExpr.eval z (homTuple c b f vars i) =
            (b.coord (f (c.coord.symm z)) i : ℤ) at hi
        rw [he] at hi
        cases hE : e i with
        | none => simpa [rhs, hE] using hi
        | some j => simpa [rhs, hE] using hi)
  have hs := mk_tuple_hom c b f x.coord vars
  have hi := congrFun (congrArg HComp.coord hs) i
  calc
    (completionMap c b f x).coord i =
        BExpr.eval x.coord (homTuple c b f vars i) := by
      simpa [completionMap, vars] using hi.symm
    _ =
        match e i with
        | none => 0
        | some j => x.coord j := by
      cases hE : e i with
      | none => simpa [rhs, hE] using h
      | some j => simpa [rhs, hE] using h

/-- Induced completion maps preserve multiplication. -/
lemma completionMap_mul
    {A : Type u} {B : Type w} [Group A] [Group B]
    {m n : ℕ} (c : HCBasis A m)
    (b : HCBasis B n) (f : A →* B)
    {R : Type*} [CommRing R] [BinomialRing R]
    (x y : HComp c R) :
    completionMap c b f (x * y) =
      completionMap c b f x * completionMap c b f y := by
  let xvars :
      Fin m → BExpr (Sum (Fin m) (Fin m)) :=
    varTuple fun i => Sum.inl i
  let yvars :
      Fin m → BExpr (Sum (Fin m) (Fin m)) :=
    varTuple fun i => Sum.inr i
  have h :=
    eval_tuple_int (Sum.elim x.coord y.coord)
      (p := homTuple c b f (mulTuple c xvars yvars))
      (q := mulTuple b (homTuple c b f xvars) (homTuple c b f yvars)) (by
        intro z
        have hs :
            (⟨evalTuple z (homTuple c b f (mulTuple c xvars yvars))⟩ :
                HComp b ℤ) =
              ⟨evalTuple z
                (mulTuple b (homTuple c b f xvars)
                  (homTuple c b f yvars))⟩ := by
          rw [mk_tuple_hom, mk_tuple_mul,
            mk_tuple_mul,
            mk_tuple_hom, mk_tuple_hom]
          let X : HComp c ℤ := ⟨evalTuple z xvars⟩
          let Y : HComp c ℤ := ⟨evalTuple z yvars⟩
          change
            extensionCandidate c ((embedding b).comp f) (X * Y) =
              extensionCandidate c ((embedding b).comp f) X *
                extensionCandidate c ((embedding b).comp f) Y
          rw [← embedding_coord_int c X,
            ← embedding_coord_int c Y,
            ← (embedding c).map_mul]
          rw [extensionCandidate_embedding c (ν := ℤ)]
          simp
        exact congrArg HComp.coord hs)
  have hs :
      (⟨evalTuple (Sum.elim x.coord y.coord)
        (homTuple c b f (mulTuple c xvars yvars))⟩ :
          HComp b R) =
        ⟨evalTuple (Sum.elim x.coord y.coord)
          (mulTuple b (homTuple c b f xvars)
            (homTuple c b f yvars))⟩ := by
    apply HComp.ext
    exact congrFun h
  simpa [completionMap, xvars, yvars] using hs

/-- Induced completion maps preserve scalar powering. -/
lemma completion_nu_pow
    {A : Type u} {B : Type w} [Group A] [Group B]
    {m n : ℕ} (c : HCBasis A m)
    (b : HCBasis B n) (f : A →* B)
    {R : Type*} [CommRing R] [BinomialRing R]
    (x : HComp c R) (a : R) :
    completionMap c b f (nuPow (ν := R) x a) =
      nuPow (ν := R) (completionMap c b f x) a := by
  let vars : Fin m → BExpr (Option (Fin m)) :=
    varTuple some
  let scalar : BExpr (Option (Fin m)) := .var none
  let assignment : Option (Fin m) → R
    | none => a
    | some i => x.coord i
  have h :=
    eval_tuple_int assignment
      (p := homTuple c b f (powTuple c scalar vars))
      (q := powTuple b scalar (homTuple c b f vars)) (by
        intro z
        have hs :
            (⟨evalTuple z (homTuple c b f (powTuple c scalar vars))⟩ :
                HComp b ℤ) =
              ⟨evalTuple z (powTuple b scalar (homTuple c b f vars))⟩ := by
          rw [mk_tuple_hom, mk_tuple_pow,
            mk_tuple_pow, mk_tuple_hom]
          let X : HComp c ℤ := ⟨evalTuple z vars⟩
          let s : ℤ := BExpr.eval z scalar
          change
            extensionCandidate c ((embedding b).comp f)
                (nuPow (ν := ℤ) X s) =
              nuPow (ν := ℤ)
                (extensionCandidate c ((embedding b).comp f) X) s
          rw [show nuPow (ν := ℤ) X s = X ^ s by
                simpa using nu_pow_cast (ν := ℤ) X s,
            show nuPow (ν := ℤ)
                (extensionCandidate c ((embedding b).comp f) X) s =
                extensionCandidate c ((embedding b).comp f) X ^ s by
              simpa using nu_pow_cast (ν := ℤ)
                (extensionCandidate c ((embedding b).comp f) X) s,
            ← embedding_coord_int c X,
            ← (embedding (ν := ℤ) c).map_zpow]
          rw [extensionCandidate_embedding c (ν := ℤ)]
          simp
        exact congrArg HComp.coord hs)
  have hs :
      (⟨evalTuple assignment (homTuple c b f (powTuple c scalar vars))⟩ :
          HComp b R) =
        ⟨evalTuple assignment (powTuple b scalar (homTuple c b f vars))⟩ := by
    apply HComp.ext
    exact congrFun h
  simpa [completionMap, vars, scalar, assignment] using hs

/-- Induced completion maps preserve the identity. -/
@[simp]
lemma completionMap_one
    {A : Type u} {B : Type w} [Group A] [Group B]
    {m n : ℕ} (c : HCBasis A m)
    (b : HCBasis B n) (f : A →* B)
    {R : Type*} [CommRing R] [BinomialRing R] :
    completionMap c b f (1 : HComp c R) = 1 := by
  simpa [completionMap] using
    extensionCandidate_embedding c (ν := R) ((embedding b).comp f) (1 : A)

/-- The powered homomorphism on completions induced by an ordinary
homomorphism between the original groups. -/
noncomputable def completionMapHom
    {A : Type u} {B : Type w} [Group A] [Group B]
    {m n : ℕ} (c : HCBasis A m)
    (b : HCBasis B n) (f : A →* B)
    {R : Type*} [CommRing R] [BinomialRing R] :
    NPHom R (HComp c R) (HComp b R) where
  toFun := completionMap c b f
  map_one' := completionMap_one c b f
  map_mul' := completionMap_mul c b f
  map_nuPow' := fun x a => completion_nu_pow c b f x a

/-- The induced completion map extends its original homomorphism on
embedded integer points. -/
@[simp]
lemma completion_comp_embedding
    {A : Type u} {B : Type w} [Group A] [Group B]
    {m n : ℕ} (c : HCBasis A m)
    (b : HCBasis B n) (f : A →* B)
    {R : Type*} [CommRing R] [BinomialRing R] :
    (completionMapHom c b f : NPHom R
      (HComp c R) (HComp b R)).toMonoidHom.comp
        (embedding c) =
      (embedding b).comp f := by
  apply MonoidHom.ext
  intro g
  exact extensionCandidate_embedding c (ν := R)
    ((embedding (ν := R) b).comp f) g

/-- The first tail of a head-plus-suffix basis maps canonically into the
original first tail. -/
def headSuffixHom {n : ℕ}
    (b : HCBasis G (n + 1)) (k : ℕ)
    (hk : k ≤ n + 1) (hkpos : 0 < k) :
    (b.headSuffixBasis k hk hkpos).tail 1 →* b.tail 1 where
  toFun g :=
    ⟨(g : b.headSuffixSubgroup k), by
      exact b.tail_antitone (show 1 ≤ k by omega) (by
        exact g.property)⟩
  map_one' := by
    apply Subtype.ext
    rfl
  map_mul' x y := by
    apply Subtype.ext
    rfl

@[simp]
lemma extensionCandidate_one {n : ℕ} (b : HCBasis G n)
    {ν : Type v} {H : Type w}
    [CommRing ν] [BinomialRing ν] [Group H]
    [NuPoweredGroup ν H] [SatisfiesPoweredAxioms ν H]
    (f : G →* H) :
    extensionCandidate b f (1 : HComp b ν) = 1 := by
  simpa using extensionCandidate_embedding b (ν := ν) f (1 : G)

/-- The candidate extension splits into the image of the head generator
and the candidate ordered product on the tail coordinates. -/
lemma extensionCandidate_succ {n : ℕ} (b : HCBasis G (n + 1))
    {ν : Type v} {H : Type w} [Group H] [NuPoweredGroup ν H]
    (f : G →* H) (x : HComp b ν) :
    extensionCandidate b f x =
      nuPow (ν := ν) (f (b.generators 0)) (x.coord 0) *
        nuBasisProduct
          (fun i => f (b.generators i.succ)) (Fin.tail x.coord) := by
  exact nu_basis_succ _ _

/-- The candidate extension splits through the first-tail candidate. -/
lemma candidate_head_tail {n : ℕ}
    (b : HCBasis G (n + 1))
    {ν : Type v} {H : Type w} [Group H] [NuPoweredGroup ν H]
    (f : G →* H) (x : HComp b ν) :
    extensionCandidate b f x =
      nuPow (ν := ν) (f (b.generators 0)) (x.coord 0) *
        extensionCandidate b.tailBasis
          (f.comp (b.tail 1).subtype) (tailPoint b x) := by
  exact extensionCandidate_succ b f x

@[simp]
lemma extensionCandidate_zero (b : HCBasis G 0)
    {ν : Type v} {H : Type w} [Group H] [NuPoweredGroup ν H]
    (f : G →* H) (x : HComp b ν) :
    extensionCandidate b f x = 1 := by
  simp [extensionCandidate]

@[simp]
lemma extension_candidate_generator (b : HCBasis G 1)
    {ν : Type v} {H : Type w} [Group H] [NuPoweredGroup ν H]
    (f : G →* H) (x : HComp b ν) :
    extensionCandidate b f x =
      nuPow (ν := ν) (f (b.generators 0)) (x.coord 0) := by
  exact nu_basis_one _ _

/-- A powered homomorphism extending the canonical embedding is forced to
be the candidate coordinate formula. -/
lemma nu_powered_candidate {n : ℕ}
    (b : HCBasis G n)
    {ν : Type v} {H : Type w}
    [CommRing ν] [BinomialRing ν] [Group H] [NuPoweredGroup ν H]
    (F : NPHom ν (HComp b ν) H)
    (f : G →* H)
    (hF : F.toMonoidHom.comp (embedding b) = f)
    (x : HComp b ν) :
    F x = extensionCandidate b f x := by
  calc
    F x =
        F (nuBasisProduct
          (fun i => (embedding b : G → HComp b ν)
            (b.generators i))
          x.coord) := by
      rw [nu_basis_generators b x]
    _ = extensionCandidate b f x := by
      unfold nuBasisProduct orderedNuProduct extensionCandidate
      rw [map_list_prod, List.map_map]
      apply congrArg List.prod
      apply List.map_congr_left
      intro i _
      simp only [Function.comp_apply, F.map_nuPow]
      have hi :=
        congrArg (fun q : G →* H => q (b.generators i)) hF
      exact congrArg (fun y : H => nuPow (ν := ν) y (x.coord i)) hi

/-- A powered homomorphism out of a completion is determined by its
restriction to the embedded original group. -/
lemma nu_ext_embedding {n : ℕ}
    (b : HCBasis G n)
    {ν : Type v} {H : Type w}
    [CommRing ν] [BinomialRing ν] [Group H] [NuPoweredGroup ν H]
    (F K : NPHom ν (HComp b ν) H)
    (h :
      F.toMonoidHom.comp (embedding b) =
        K.toMonoidHom.comp (embedding b)) :
    F = K := by
  ext x
  calc
    F x =
        extensionCandidate b
          (F.toMonoidHom.comp (embedding b)) x :=
      nu_powered_candidate b F _ rfl x
    _ =
        extensionCandidate b
          (K.toMonoidHom.comp (embedding b)) x := by rw [h]
    _ = K x :=
      (nu_powered_candidate b K _ rfl x).symm

/-- Completing the first tail of a head-plus-suffix basis and then including
it into the ambient completion agrees with first including it into the
original first-tail completion and then applying the zero-prefix lift. -/
lemma head_suffix_coherence {n : ℕ}
    (b : HCBasis G (n + 1)) (k : ℕ)
    (hk : k ≤ n + 1) (hkpos : 0 < k)
    {ν : Type v} [CommRing ν] [BinomialRing ν] :
    (completionMapHom (b.headSuffixBasis k hk hkpos) b
        (b.headSuffixSubgroup k).subtype :
      NPHom ν
        (HComp (b.headSuffixBasis k hk hkpos) ν)
        (HComp b ν)).comp
      (tailLiftHom (b.headSuffixBasis k hk hkpos)) =
    (tailLiftHom b).comp
      (completionMapHom
        (b.headSuffixBasis k hk hkpos).tailBasis b.tailBasis
        (headSuffixHom b k hk hkpos)) := by
  apply nu_ext_embedding
    (b.headSuffixBasis k hk hkpos).tailBasis
  apply MonoidHom.ext
  intro g
  let hb := b.headSuffixBasis k hk hkpos
  have hleftTail :
      (tailLiftHom hb : NPHom ν
        (HComp hb.tailBasis ν) (HComp hb ν))
          ((embedding hb.tailBasis) g) =
        (embedding hb) ((hb.tail 1).subtype g) := by
    exact congrArg (fun q : (hb.tail 1) →* HComp hb ν => q g)
      (tail_comp_embedding hb)
  have hleftCompletion :
      (completionMapHom hb b (b.headSuffixSubgroup k).subtype :
        NPHom ν (HComp hb ν) (HComp b ν))
          ((embedding hb) ((hb.tail 1).subtype g)) =
        (embedding b)
          ((b.headSuffixSubgroup k).subtype ((hb.tail 1).subtype g)) := by
    exact congrArg
      (fun q : b.headSuffixSubgroup k →* HComp b ν =>
        q ((hb.tail 1).subtype g))
      (completion_comp_embedding hb b
        (b.headSuffixSubgroup k).subtype)
  have hrightCompletion :
      (completionMapHom hb.tailBasis b.tailBasis
        (headSuffixHom b k hk hkpos) :
          NPHom ν
            (HComp hb.tailBasis ν)
            (HComp b.tailBasis ν))
          ((embedding hb.tailBasis) g) =
        (embedding b.tailBasis) (headSuffixHom b k hk hkpos g) := by
    exact congrArg
      (fun q : (hb.tail 1) →* HComp b.tailBasis ν => q g)
      (completion_comp_embedding hb.tailBasis b.tailBasis
        (headSuffixHom b k hk hkpos))
  have hrightTail :
      (tailLiftHom b : NPHom ν
        (HComp b.tailBasis ν) (HComp b ν))
          ((embedding b.tailBasis) (headSuffixHom b k hk hkpos g)) =
        (embedding b)
          ((b.tail 1).subtype (headSuffixHom b k hk hkpos g)) := by
    exact congrArg (fun q : b.tail 1 →* HComp b ν =>
      q (headSuffixHom b k hk hkpos g))
      (tail_comp_embedding b)
  change
    (completionMapHom hb b (b.headSuffixSubgroup k).subtype :
      NPHom ν (HComp hb ν) (HComp b ν))
        ((tailLiftHom hb) ((embedding hb.tailBasis) g)) =
      (tailLiftHom b)
        ((completionMapHom hb.tailBasis b.tailBasis
          (headSuffixHom b k hk hkpos))
            ((embedding hb.tailBasis) g))
  rw [hleftTail, hleftCompletion, hrightCompletion, hrightTail]
  rfl

/-- Recursively constructed extensions on the first tail and on a
head-plus-suffix subgroup agree on their common completed suffix. -/
lemma extension_suffix_coherence {n : ℕ}
    (b : HCBasis G (n + 1)) (k : ℕ)
    (hk : k ≤ n + 1) (hkpos : 0 < k)
    {ν : Type v} {H : Type w}
    [CommRing ν] [BinomialRing ν] [Group H]
    [NuPoweredGroup ν H] [SatisfiesPoweredAxioms ν H]
    (f : G →* H)
    (Ftail : NPHom ν (HComp b.tailBasis ν) H)
    (Fhs : NPHom ν
      (HComp (b.headSuffixBasis k hk hkpos) ν) H)
    (hFtail :
      Ftail.toMonoidHom.comp (embedding b.tailBasis) =
        f.comp (b.tail 1).subtype)
    (hFhs :
      Fhs.toMonoidHom.comp (embedding (b.headSuffixBasis k hk hkpos)) =
        f.comp (b.headSuffixSubgroup k).subtype) :
    Ftail.comp
        (completionMapHom
          (b.headSuffixBasis k hk hkpos).tailBasis b.tailBasis
          (headSuffixHom b k hk hkpos)) =
      Fhs.comp (tailLiftHom (b.headSuffixBasis k hk hkpos)) := by
  apply nu_ext_embedding
    (b.headSuffixBasis k hk hkpos).tailBasis
  apply MonoidHom.ext
  intro g
  let hb := b.headSuffixBasis k hk hkpos
  have hleftCompletion :
      (completionMapHom hb.tailBasis b.tailBasis
        (headSuffixHom b k hk hkpos) :
          NPHom ν
            (HComp hb.tailBasis ν)
            (HComp b.tailBasis ν))
          ((embedding hb.tailBasis) g) =
        (embedding b.tailBasis) (headSuffixHom b k hk hkpos g) := by
    exact congrArg
      (fun q : (hb.tail 1) →* HComp b.tailBasis ν => q g)
      (completion_comp_embedding hb.tailBasis b.tailBasis
        (headSuffixHom b k hk hkpos))
  have hleftF :
      Ftail ((embedding b.tailBasis)
          (headSuffixHom b k hk hkpos g)) =
        f ((b.tail 1).subtype (headSuffixHom b k hk hkpos g)) := by
    exact congrArg (fun q : b.tail 1 →* H =>
      q (headSuffixHom b k hk hkpos g)) hFtail
  have hrightTail :
      (tailLiftHom hb : NPHom ν
        (HComp hb.tailBasis ν) (HComp hb ν))
          ((embedding hb.tailBasis) g) =
        (embedding hb) ((hb.tail 1).subtype g) := by
    exact congrArg (fun q : (hb.tail 1) →* HComp hb ν => q g)
      (tail_comp_embedding hb)
  have hrightF :
      Fhs ((embedding hb) ((hb.tail 1).subtype g)) =
        f ((b.headSuffixSubgroup k).subtype ((hb.tail 1).subtype g)) := by
    exact congrArg
      (fun q : b.headSuffixSubgroup k →* H => q ((hb.tail 1).subtype g))
      hFhs
  change
    Ftail
        ((completionMapHom hb.tailBasis b.tailBasis
          (headSuffixHom b k hk hkpos))
            ((embedding hb.tailBasis) g)) =
      Fhs ((tailLiftHom hb) ((embedding hb.tailBasis) g))
  rw [hleftCompletion, hleftF, hrightTail, hrightF]
  rfl

/-- The scalar correction attached to a later generator, formed in Hall's
smaller head-plus-suffix completion. -/
noncomputable def headSuffixPoint {n : ℕ}
    (b : HCBasis G (n + 1)) (i : Fin n)
    {ν : Type v} [CommRing ν] [BinomialRing ν] (a : ν) :
    HComp
      (b.headSuffixBasis ((i : ℕ) + 2) (by omega) (by omega)) ν :=
  let hk : (i : ℕ) + 2 ≤ n + 1 := Nat.succ_le_succ i.isLt
  let hkpos : 0 < (i : ℕ) + 2 := Nat.zero_lt_succ _
  let hb := b.headSuffixBasis ((i : ℕ) + 2) hk hkpos
  let head : b.headSuffixSubgroup ((i : ℕ) + 2) :=
    ⟨b.generators 0, b.head_suffix_subgroup ((i : ℕ) + 2)⟩
  let conjugatedHead : b.headSuffixSubgroup ((i : ℕ) + 2) :=
    ⟨b.generators i.succ * b.generators 0 * (b.generators i.succ)⁻¹,
      b.conjugated_head_suffix i⟩
  nuPow (ν := ν) ((embedding hb) head) (-a) *
    nuPow (ν := ν) ((embedding hb) conjugatedHead) a

/-- The scalar correction lies in the completed first tail of the smaller
head-plus-suffix completion. -/
lemma head_suffix_coord {n : ℕ}
    (b : HCBasis G (n + 1)) (i : Fin n)
    {ν : Type v} [CommRing ν] [BinomialRing ν] (a : ν) :
    (headSuffixPoint b i a).coord 0 = 0 := by
  let hk : (i : ℕ) + 2 ≤ n + 1 := Nat.succ_le_succ i.isLt
  let hkpos : 0 < (i : ℕ) + 2 := Nat.zero_lt_succ _
  let hb := b.headSuffixBasis ((i : ℕ) + 2) hk hkpos
  let head : b.headSuffixSubgroup ((i : ℕ) + 2) :=
    ⟨b.generators 0, b.head_suffix_subgroup ((i : ℕ) + 2)⟩
  let conjugatedHead : b.headSuffixSubgroup ((i : ℕ) + 2) :=
    ⟨b.generators i.succ * b.generators 0 * (b.generators i.succ)⁻¹,
      b.conjugated_head_suffix i⟩
  have hhead : hb.coord head 0 = 1 := by
    change hb.coord (hb.generators 0) 0 = 1
    rw [hb.generator_coord]
    simp
  have hdivAmbient :
      b.generators i.succ * b.generators 0 * (b.generators i.succ)⁻¹ /
          b.generators 0 ∈
        b.tail ((i : ℕ) + 2) := by
    rw [show
      b.generators i.succ * b.generators 0 * (b.generators i.succ)⁻¹ /
          b.generators 0 =
        ⁅b.generators i.succ, b.generators 0⁆ by
      simp [div_eq_mul_inv, commutatorElement_def]]
    apply b.tail_central ((i : ℕ) + 1)
    exact Subgroup.commutator_mem_commutator
      (b.generator_tail (by omega) i.succ (by simp))
      (Subgroup.mem_top _)
  have hdiv : conjugatedHead / head ∈ hb.tail 1 := by
    exact hdivAmbient
  have hconjugatedHead : hb.coord conjugatedHead 0 = 1 := by
    rw [hb.coord_div_tail hdiv, hhead]
  rw [headSuffixPoint, coord_mul_zero, coord_nu_zero,
    coord_nu_zero]
  simp [embedding, ofIntCast, hb, head, conjugatedHead, hhead,
    hconjugatedHead]

/-- The same scalar correction, transported through the common completed
suffix into the original first-tail completion. -/
noncomputable def tailCorrectionPoint {n : ℕ}
    (b : HCBasis G (n + 1)) (i : Fin n)
    {ν : Type v} [CommRing ν] [BinomialRing ν] (a : ν) :
    HComp b.tailBasis ν :=
  let hk : (i : ℕ) + 2 ≤ n + 1 := Nat.succ_le_succ i.isLt
  let hkpos : 0 < (i : ℕ) + 2 := Nat.zero_lt_succ _
  let hb := b.headSuffixBasis ((i : ℕ) + 2) hk hkpos
  completionMap hb.tailBasis b.tailBasis
    (headSuffixHom b ((i : ℕ) + 2) hk hkpos)
    (tailPoint hb (headSuffixPoint b i a))

/-- Lifting the transported tail correction recovers the correction formed
inside the smaller head-plus-suffix completion and then included ambiently. -/
lemma tail_lift_point {n : ℕ}
    (b : HCBasis G (n + 1)) (i : Fin n)
    {ν : Type v} [CommRing ν] [BinomialRing ν] (a : ν) :
    tailLift b (tailCorrectionPoint b i a) =
      completionMap
        (b.headSuffixBasis ((i : ℕ) + 2) (by omega) (by omega)) b
        (b.headSuffixSubgroup ((i : ℕ) + 2)).subtype
        (headSuffixPoint b i a) := by
  let hk : (i : ℕ) + 2 ≤ n + 1 := Nat.succ_le_succ i.isLt
  let hkpos : 0 < (i : ℕ) + 2 := Nat.zero_lt_succ _
  let hb := b.headSuffixBasis ((i : ℕ) + 2) hk hkpos
  let z := tailPoint hb (headSuffixPoint b i a)
  have h := congrArg
    (fun F : NPHom ν (HComp hb.tailBasis ν)
      (HComp b ν) => F z)
    (head_suffix_coherence b ((i : ℕ) + 2) hk hkpos
      (ν := ν))
  change
    completionMap hb b (b.headSuffixSubgroup ((i : ℕ) + 2)).subtype
        (tailLift hb z) =
      tailLift b
        (completionMap hb.tailBasis b.tailBasis
          (headSuffixHom b ((i : ℕ) + 2) hk hkpos) z) at h
  rw [tail_point_coord hb
    (headSuffixPoint b i a)
    (head_suffix_coord b i a)] at h
  exact h.symm

/-- Ambient inclusion evaluates the smaller head-suffix correction as the
expected two scalar-powered factors. -/
lemma head_suffix_point {n : ℕ}
    (b : HCBasis G (n + 1)) (i : Fin n)
    {ν : Type v} [CommRing ν] [BinomialRing ν] (a : ν) :
    completionMap
        (b.headSuffixBasis ((i : ℕ) + 2) (by omega) (by omega)) b
        (b.headSuffixSubgroup ((i : ℕ) + 2)).subtype
        (headSuffixPoint b i a) =
      nuPow (ν := ν) ((embedding b) (b.generators 0)) (-a) *
        nuPow (ν := ν) ((embedding b)
          (b.generators i.succ * b.generators 0 *
            (b.generators i.succ)⁻¹)) a := by
  let hk : (i : ℕ) + 2 ≤ n + 1 := Nat.succ_le_succ i.isLt
  let hkpos : 0 < (i : ℕ) + 2 := Nat.zero_lt_succ _
  let hb := b.headSuffixBasis ((i : ℕ) + 2) hk hkpos
  let head : b.headSuffixSubgroup ((i : ℕ) + 2) :=
    ⟨b.generators 0, b.head_suffix_subgroup ((i : ℕ) + 2)⟩
  let conjugatedHead : b.headSuffixSubgroup ((i : ℕ) + 2) :=
    ⟨b.generators i.succ * b.generators 0 * (b.generators i.succ)⁻¹,
      b.conjugated_head_suffix i⟩
  have hhead :
      completionMap hb b (b.headSuffixSubgroup ((i : ℕ) + 2)).subtype
          ((embedding (ν := ν) hb) head) =
        (embedding (ν := ν) b) (b.generators 0) := by
    exact congrArg
      (fun q : b.headSuffixSubgroup ((i : ℕ) + 2) →*
        HComp b ν => q head)
      (completion_comp_embedding hb b
        (b.headSuffixSubgroup ((i : ℕ) + 2)).subtype)
  have hconjugatedHead :
      completionMap hb b (b.headSuffixSubgroup ((i : ℕ) + 2)).subtype
          ((embedding (ν := ν) hb) conjugatedHead) =
        (embedding (ν := ν) b)
          (b.generators i.succ * b.generators 0 *
            (b.generators i.succ)⁻¹) := by
    exact congrArg
      (fun q : b.headSuffixSubgroup ((i : ℕ) + 2) →*
        HComp b ν => q conjugatedHead)
      (completion_comp_embedding hb b
        (b.headSuffixSubgroup ((i : ℕ) + 2)).subtype)
  change
    completionMap hb b (b.headSuffixSubgroup ((i : ℕ) + 2)).subtype
        (nuPow (ν := ν) ((embedding (ν := ν) hb) head) (-a) *
          nuPow (ν := ν) ((embedding (ν := ν) hb) conjugatedHead) a) =
      _
  rw [completionMap_mul, completion_nu_pow, completion_nu_pow,
    hhead, hconjugatedHead]

/-- Scalar head-conjugation of an embedded later generator factors in the
completed first tail as its transported correction times that generator. -/
lemma conjugate_tail_embedding {n : ℕ}
    (b : HCBasis G (n + 1)) (i : Fin n)
    {ν : Type v} [CommRing ν] [BinomialRing ν] (a : ν) :
    conjugateTailCompletion b a
        ((embedding b.tailBasis) (b.tailBasis.generators i)) =
      tailCorrectionPoint b i a *
        (embedding b.tailBasis) (b.tailBasis.generators i) := by
  apply tailLift_injective b
  have hgenerator :
      tailLift b ((embedding (ν := ν) b.tailBasis)
          (b.tailBasis.generators i)) =
        (embedding (ν := ν) b) (b.generators i.succ) := by
    exact congrArg (fun q : b.tail 1 →* HComp b ν =>
      q (b.tailBasis.generators i)) (tail_comp_embedding b)
  rw [tail_lift_conjugate, tailLift_mul,
    tail_lift_point, head_suffix_point,
    hgenerator]
  simpa using
    (nu_conjugate_generator
      ((embedding (ν := ν) b) (b.generators 0))
      ((embedding (ν := ν) b) (b.generators i.succ)) a)

/-- Compatible recursive extensions evaluate the transported tail
correction as the expected two scalar-powered target factors. -/
lemma extension_tail_point {n : ℕ}
    (b : HCBasis G (n + 1)) (i : Fin n)
    {ν : Type v} {H : Type w}
    [CommRing ν] [BinomialRing ν] [Group H]
    [NuPoweredGroup ν H] [SatisfiesPoweredAxioms ν H]
    (f : G →* H)
    (Ftail : NPHom ν (HComp b.tailBasis ν) H)
    (Fhs : NPHom ν
      (HComp
        (b.headSuffixBasis ((i : ℕ) + 2) (by omega) (by omega)) ν) H)
    (hFtail :
      Ftail.toMonoidHom.comp (embedding b.tailBasis) =
        f.comp (b.tail 1).subtype)
    (hFhs :
      Fhs.toMonoidHom.comp
          (embedding
            (b.headSuffixBasis ((i : ℕ) + 2) (by omega) (by omega))) =
        f.comp (b.headSuffixSubgroup ((i : ℕ) + 2)).subtype)
    (a : ν) :
    Ftail (tailCorrectionPoint b i a) =
      nuPow (ν := ν) (f (b.generators 0)) (-a) *
        nuPow (ν := ν)
          (f (b.generators i.succ * b.generators 0 *
            (b.generators i.succ)⁻¹)) a := by
  let hk : (i : ℕ) + 2 ≤ n + 1 := Nat.succ_le_succ i.isLt
  let hkpos : 0 < (i : ℕ) + 2 := Nat.zero_lt_succ _
  let hb := b.headSuffixBasis ((i : ℕ) + 2) hk hkpos
  let head : b.headSuffixSubgroup ((i : ℕ) + 2) :=
    ⟨b.generators 0, b.head_suffix_subgroup ((i : ℕ) + 2)⟩
  let conjugatedHead : b.headSuffixSubgroup ((i : ℕ) + 2) :=
    ⟨b.generators i.succ * b.generators 0 * (b.generators i.succ)⁻¹,
      b.conjugated_head_suffix i⟩
  let z := tailPoint hb (headSuffixPoint b i a)
  have hcoherence := congrArg
    (fun F : NPHom ν (HComp hb.tailBasis ν) H => F z)
    (extension_suffix_coherence b ((i : ℕ) + 2) hk hkpos
      f Ftail Fhs hFtail hFhs)
  change
    Ftail
        (completionMap hb.tailBasis b.tailBasis
          (headSuffixHom b ((i : ℕ) + 2) hk hkpos) z) =
      Fhs (tailLift hb z) at hcoherence
  rw [tail_point_coord hb
    (headSuffixPoint b i a)
    (head_suffix_coord b i a)] at hcoherence
  have hhead :
      Fhs ((embedding (ν := ν) hb) head) = f (b.generators 0) := by
    exact congrArg
      (fun q : b.headSuffixSubgroup ((i : ℕ) + 2) →* H => q head) hFhs
  have hconjugatedHead :
      Fhs ((embedding (ν := ν) hb) conjugatedHead) =
        f (b.generators i.succ * b.generators 0 *
          (b.generators i.succ)⁻¹) := by
    exact congrArg
      (fun q : b.headSuffixSubgroup ((i : ℕ) + 2) →* H =>
        q conjugatedHead) hFhs
  rw [show tailCorrectionPoint b i a =
      completionMap hb.tailBasis b.tailBasis
        (headSuffixHom b ((i : ℕ) + 2) hk hkpos) z by rfl,
    hcoherence]
  change
    Fhs
        (nuPow (ν := ν) ((embedding (ν := ν) hb) head) (-a) *
          nuPow (ν := ν) ((embedding (ν := ν) hb) conjugatedHead) a) =
      _
  rw [Fhs.toMonoidHom.map_mul, Fhs.map_nuPow, Fhs.map_nuPow,
    hhead, hconjugatedHead]

/-- Compatible recursive extensions intertwine scalar head-conjugation on
each embedded later canonical generator. -/
lemma conjugate_embedding_generator {n : ℕ}
    (b : HCBasis G (n + 1)) (i : Fin n)
    {ν : Type v} {H : Type w}
    [CommRing ν] [BinomialRing ν] [Group H]
    [NuPoweredGroup ν H] [SatisfiesPoweredAxioms ν H]
    (f : G →* H)
    (Ftail : NPHom ν (HComp b.tailBasis ν) H)
    (Fhs : NPHom ν
      (HComp
        (b.headSuffixBasis ((i : ℕ) + 2) (by omega) (by omega)) ν) H)
    (hFtail :
      Ftail.toMonoidHom.comp (embedding b.tailBasis) =
        f.comp (b.tail 1).subtype)
    (hFhs :
      Fhs.toMonoidHom.comp
          (embedding
            (b.headSuffixBasis ((i : ℕ) + 2) (by omega) (by omega))) =
        f.comp (b.headSuffixSubgroup ((i : ℕ) + 2)).subtype)
    (a : ν) :
    (nuPow (ν := ν) (f (b.generators 0)) a)⁻¹ *
          Ftail ((embedding b.tailBasis) (b.tailBasis.generators i)) *
        nuPow (ν := ν) (f (b.generators 0)) a =
      Ftail (conjugateTailCompletion b a
        ((embedding b.tailBasis) (b.tailBasis.generators i))) := by
  have hgenerator :
      Ftail ((embedding (ν := ν) b.tailBasis)
          (b.tailBasis.generators i)) =
        f (b.generators i.succ) := by
    exact congrArg (fun q : b.tail 1 →* H => q (b.tailBasis.generators i))
      hFtail
  rw [conjugate_tail_embedding,
    Ftail.toMonoidHom.map_mul,
    extension_tail_point b i f Ftail Fhs hFtail hFhs,
    hgenerator, ← nuPow_neg]
  simpa using
    (nu_conjugate_generator
      (f (b.generators 0)) (f (b.generators i.succ)) a)

/-- Compatible recursive extensions intertwine scalar head-conjugation on
the entire completed first tail. -/
lemma extension_conjugate_completion {n : ℕ}
    (b : HCBasis G (n + 1))
    {ν : Type v} {H : Type w}
    [CommRing ν] [BinomialRing ν] [Group H]
    [NuPoweredGroup ν H] [SatisfiesPoweredAxioms ν H]
    (f : G →* H)
    (Ftail : NPHom ν (HComp b.tailBasis ν) H)
    (hFtail :
      Ftail.toMonoidHom.comp (embedding b.tailBasis) =
        f.comp (b.tail 1).subtype)
    (Fhs : ∀ i : Fin n, NPHom ν
      (HComp
        (b.headSuffixBasis ((i : ℕ) + 2) (by omega) (by omega)) ν) H)
    (hFhs : ∀ i : Fin n,
      (Fhs i).toMonoidHom.comp
          (embedding
            (b.headSuffixBasis ((i : ℕ) + 2) (by omega) (by omega))) =
        f.comp (b.headSuffixSubgroup ((i : ℕ) + 2)).subtype)
    (a : ν) :
    (conjugationNuPowered (ν := ν)
      (nuPow (ν := ν) (f (b.generators 0)) a)).comp Ftail =
      Ftail.comp (conjugateCompletionHom b a) := by
  apply nu_ext_embedding b.tailBasis
  apply monoid_ext_generators b.tailBasis
  intro i
  simpa only [MonoidHom.comp_apply, NPHom.comp_apply,
    conjugation_nu_powered] using
      (conjugate_embedding_generator
        b i f Ftail (Fhs i) hFtail (hFhs i) a)

/-- The preceding powered-map equality is exactly the tail-conjugation
hypothesis needed to make the full candidate multiplicative. -/
lemma candidate_conjugation_extensions {n : ℕ}
    (b : HCBasis G (n + 1))
    {ν : Type v} {H : Type w}
    [CommRing ν] [BinomialRing ν] [Group H]
    [NuPoweredGroup ν H] [SatisfiesPoweredAxioms ν H]
    (f : G →* H)
    (Ftail : NPHom ν (HComp b.tailBasis ν) H)
    (hFtail :
      Ftail.toMonoidHom.comp (embedding b.tailBasis) =
        f.comp (b.tail 1).subtype)
    (Fhs : ∀ i : Fin n, NPHom ν
      (HComp
        (b.headSuffixBasis ((i : ℕ) + 2) (by omega) (by omega)) ν) H)
    (hFhs : ∀ i : Fin n,
      (Fhs i).toMonoidHom.comp
          (embedding
            (b.headSuffixBasis ((i : ℕ) + 2) (by omega) (by omega))) =
        f.comp (b.headSuffixSubgroup ((i : ℕ) + 2)).subtype) :
    ∀ (a : ν) (z : HComp b.tailBasis ν),
      (nuPow (ν := ν) (f (b.generators 0)) a)⁻¹ *
            extensionCandidate b.tailBasis
              (f.comp (b.tail 1).subtype) z *
          nuPow (ν := ν) (f (b.generators 0)) a =
        extensionCandidate b.tailBasis
          (f.comp (b.tail 1).subtype)
          (conjugateTailCompletion b a z) := by
  intro a z
  have h := congrArg
    (fun F : NPHom ν (HComp b.tailBasis ν) H => F z)
    (extension_conjugate_completion b f Ftail hFtail Fhs hFhs a)
  have h' :
      (nuPow (ν := ν) (f (b.generators 0)) a)⁻¹ * Ftail z *
            nuPow (ν := ν) (f (b.generators 0)) a =
        Ftail (conjugateTailCompletion b a z) := by
    simpa only [NPHom.comp_apply, conjugation_nu_powered] using h
  rw [nu_powered_candidate b.tailBasis Ftail
      (f.comp (b.tail 1).subtype) hFtail z,
    nu_powered_candidate b.tailBasis Ftail
      (f.comp (b.tail 1).subtype) hFtail
      (conjugateTailCompletion b a z)] at h'
  exact h'

/-- Multiplicativity of the full candidate reduces to a powered extension
on the first tail which intertwines scalar head conjugation. -/
lemma extension_candidate_conjugation {n : ℕ}
    (b : HCBasis G (n + 1))
    {ν : Type v} {H : Type w}
    [CommRing ν] [BinomialRing ν] [Group H]
    [NuPoweredGroup ν H] [SatisfiesPoweredAxioms ν H]
    (f : G →* H)
    (Ftail : NPHom ν (HComp b.tailBasis ν) H)
    (hFtail :
      Ftail.toMonoidHom.comp (embedding b.tailBasis) =
        f.comp (b.tail 1).subtype)
    (hconj : ∀ (a : ν) (z : HComp b.tailBasis ν),
      (nuPow (ν := ν) (f (b.generators 0)) a)⁻¹ *
            extensionCandidate b.tailBasis
              (f.comp (b.tail 1).subtype) z *
          nuPow (ν := ν) (f (b.generators 0)) a =
        extensionCandidate b.tailBasis
          (f.comp (b.tail 1).subtype)
          (conjugateTailCompletion b a z))
    (x y : HComp b ν) :
    extensionCandidate b f (x * y) =
      extensionCandidate b f x * extensionCandidate b f y := by
  let ftail : b.tail 1 →* H := f.comp (b.tail 1).subtype
  have htail (z : HComp b.tailBasis ν) :
      Ftail z = extensionCandidate b.tailBasis ftail z :=
    nu_powered_candidate b.tailBasis Ftail ftail hFtail z
  calc
    extensionCandidate b f (x * y) =
        nuPow (ν := ν) (f (b.generators 0)) (x.coord 0 + y.coord 0) *
          extensionCandidate b.tailBasis ftail
            (conjugateTailCompletion b (y.coord 0) (tailPoint b x) *
              tailPoint b y) := by
      rw [candidate_head_tail, coord_mul_zero, tailPoint_mul]
    _ =
        nuPow (ν := ν) (f (b.generators 0)) (x.coord 0 + y.coord 0) *
          (extensionCandidate b.tailBasis ftail
              (conjugateTailCompletion b (y.coord 0) (tailPoint b x)) *
            extensionCandidate b.tailBasis ftail (tailPoint b y)) := by
      rw [← htail, Ftail.toMonoidHom.map_mul, htail, htail]
    _ =
        nuPow (ν := ν) (f (b.generators 0)) (x.coord 0 + y.coord 0) *
          (((nuPow (ν := ν) (f (b.generators 0)) (y.coord 0))⁻¹ *
                extensionCandidate b.tailBasis ftail (tailPoint b x) *
              nuPow (ν := ν) (f (b.generators 0)) (y.coord 0)) *
            extensionCandidate b.tailBasis ftail (tailPoint b y)) := by
      rw [← hconj]
    _ = extensionCandidate b f x * extensionCandidate b f y := by
      rw [candidate_head_tail,
        candidate_head_tail,
        SatisfiesPoweredAxioms.pow_add]
      dsimp only [ftail]
      group

/-- Recursive extensions on the first tail and all smaller head-suffix
subgroups make the full candidate multiplicative. -/
lemma extension_candidate_extensions {n : ℕ}
    (b : HCBasis G (n + 1))
    {ν : Type v} {H : Type w}
    [CommRing ν] [BinomialRing ν] [Group H]
    [NuPoweredGroup ν H] [SatisfiesPoweredAxioms ν H]
    (f : G →* H)
    (Ftail : NPHom ν (HComp b.tailBasis ν) H)
    (hFtail :
      Ftail.toMonoidHom.comp (embedding b.tailBasis) =
        f.comp (b.tail 1).subtype)
    (Fhs : ∀ i : Fin n, NPHom ν
      (HComp
        (b.headSuffixBasis ((i : ℕ) + 2) (by omega) (by omega)) ν) H)
    (hFhs : ∀ i : Fin n,
      (Fhs i).toMonoidHom.comp
          (embedding
            (b.headSuffixBasis ((i : ℕ) + 2) (by omega) (by omega))) =
        f.comp (b.headSuffixSubgroup ((i : ℕ) + 2)).subtype)
    (x y : HComp b ν) :
    extensionCandidate b f (x * y) =
      extensionCandidate b f x * extensionCandidate b f y :=
  extension_candidate_conjugation b f Ftail hFtail
    (candidate_conjugation_extensions
      b f Ftail hFtail Fhs hFhs) x y

/-- A multiplicative candidate extension, packaged as an ordinary
homomorphism while scalar preservation is proved separately. -/
noncomputable def extensionCandidateMonoid {n : ℕ}
    (b : HCBasis G n)
    {ν : Type v} {H : Type w}
    [CommRing ν] [BinomialRing ν] [Group H]
    [NuPoweredGroup ν H] [SatisfiesPoweredAxioms ν H]
    (f : G →* H)
    (hmul : ∀ x y : HComp b ν,
      extensionCandidate b f (x * y) =
        extensionCandidate b f x * extensionCandidate b f y) :
    HComp b ν →* H where
  toFun := extensionCandidate b f
  map_one' := extensionCandidate_one b f
  map_mul' := hmul

/-- The full candidate agrees with a recursive powered extension on a
zero-prefixed first-tail point. -/
lemma extension_candidate_lift {n : ℕ}
    (b : HCBasis G (n + 1))
    {ν : Type v} {H : Type w}
    [CommRing ν] [BinomialRing ν] [Group H]
    [NuPoweredGroup ν H] [SatisfiesPoweredAxioms ν H]
    (f : G →* H)
    (Ftail : NPHom ν (HComp b.tailBasis ν) H)
    (hFtail :
      Ftail.toMonoidHom.comp (embedding b.tailBasis) =
        f.comp (b.tail 1).subtype)
    (z : HComp b.tailBasis ν) :
    extensionCandidate b f (tailLift b z) = Ftail z := by
  rw [candidate_head_tail, tail_lift_coord,
    tail_point_lift, nuPow_zero, _root_.one_mul]
  exact
    (nu_powered_candidate b.tailBasis Ftail
      (f.comp (b.tail 1).subtype) hFtail z).symm

/-- The full candidate preserves a further scalar power of a scalar-powered
embedded head generator. -/
lemma candidate_nu_head {n : ℕ}
    (b : HCBasis G (n + 1))
    {ν : Type v} {H : Type w}
    [CommRing ν] [BinomialRing ν] [Group H]
    [NuPoweredGroup ν H] [SatisfiesPoweredAxioms ν H]
    (f : G →* H) (s a : ν) :
    extensionCandidate b f
        (nuPow (ν := ν)
          (nuPow (ν := ν) ((embedding (ν := ν) b) (b.generators 0)) s) a) =
      nuPow (ν := ν)
        (extensionCandidate b f
          (nuPow (ν := ν) ((embedding (ν := ν) b) (b.generators 0)) s)) a := by
  rw [← SatisfiesPoweredAxioms.pow_mul,
    nu_embedding_generator, candidate_head_tail,
    nu_embedding_generator, candidate_head_tail]
  simp [tailPoint, extensionCandidate, nuBasisProduct,
    orderedNuProduct, SatisfiesPoweredAxioms.pow_mul]

/-- The full candidate preserves scalar powers of zero-prefixed first-tail
points whenever the recursive tail extension is available. -/
lemma candidate_nu_lift {n : ℕ}
    (b : HCBasis G (n + 1))
    {ν : Type v} {H : Type w}
    [CommRing ν] [BinomialRing ν] [Group H]
    [NuPoweredGroup ν H] [SatisfiesPoweredAxioms ν H]
    (f : G →* H)
    (Ftail : NPHom ν (HComp b.tailBasis ν) H)
    (hFtail :
      Ftail.toMonoidHom.comp (embedding b.tailBasis) =
        f.comp (b.tail 1).subtype)
    (z : HComp b.tailBasis ν) (a : ν) :
    extensionCandidate b f (nuPow (ν := ν) (tailLift b z) a) =
      nuPow (ν := ν) (extensionCandidate b f (tailLift b z)) a := by
  rw [← tail_lift_nu, extension_candidate_lift b f Ftail
    hFtail, extension_candidate_lift b f Ftail hFtail,
    Ftail.map_nuPow]

/-- The full candidate preserves scalar powers of every higher Petresco
term because those terms lie in the completed first tail. -/
lemma extension_candidate_nu {n : ℕ}
    (b : HCBasis G (n + 1))
    {ν : Type v} {H : Type w}
    [CommRing ν] [BinomialRing ν] [Group H]
    [NuPoweredGroup ν H] [SatisfiesPoweredAxioms ν H]
    (f : G →* H)
    (Ftail : NPHom ν (HComp b.tailBasis ν) H)
    (hFtail :
      Ftail.toMonoidHom.comp (embedding b.tailBasis) =
        f.comp (b.tail 1).subtype)
    (factors : List (HComp b ν)) {j : ℕ} (hj : 2 ≤ j) (a : ν) :
    extensionCandidate b f
        (nuPow (ν := ν) (petrescoTerm factors j) a) =
      nuPow (ν := ν) (extensionCandidate b f (petrescoTerm factors j)) a := by
  rw [← tail_point_coord b (petrescoTerm factors j)
    (petresco_term_coord b factors hj)]
  exact candidate_nu_lift b f Ftail hFtail _ a

/-- The full candidate transports a finite higher-weight Petresco
correction through its recursive first-tail extension. -/
lemma candidate_nu_petresco {n : ℕ}
    (b : HCBasis G (n + 1))
    {ν : Type v} {H : Type w}
    [CommRing ν] [BinomialRing ν] [Group H]
    [NuPoweredGroup ν H] [SatisfiesPoweredAxioms ν H]
    (f : G →* H)
    (Ftail : NPHom ν (HComp b.tailBasis ν) H)
    (hFtail :
      Ftail.toMonoidHom.comp (embedding b.tailBasis) =
        f.comp (b.tail 1).subtype)
    (hmul : ∀ x y : HComp b ν,
      extensionCandidate b f (x * y) =
        extensionCandidate b f x * extensionCandidate b f y)
    (factors : List (HComp b ν)) (a : ν) (c : ℕ) :
    extensionCandidate b f
        (nuPetrescoTail (petrescoTerm factors) a c) =
      nuPetrescoTail
        (petrescoTerm (factors.map (extensionCandidateMonoid b f hmul)))
        a c := by
  let M := extensionCandidateMonoid b f hmul
  change M (nuPetrescoTail (petrescoTerm factors) a c) =
    nuPetrescoTail (petrescoTerm (factors.map M)) a c
  unfold nuPetrescoTail
  rw [map_list_prod, List.map_map]
  apply congrArg List.prod
  apply List.map_congr_left
  intro j _
  change
    extensionCandidate b f
        (nuPow (ν := ν) (petrescoTerm factors ((j : ℕ) + 2))
          (Ring.choose a ((j : ℕ) + 2))) =
      nuPow (ν := ν)
        (petrescoTerm (factors.map M) ((j : ℕ) + 2))
        (Ring.choose a ((j : ℕ) + 2))
  rw [extension_candidate_nu b f Ftail hFtail
    factors (by omega)]
  exact congrArg
    (fun y : H => nuPow (ν := ν) y (Ring.choose a ((j : ℕ) + 2)))
    (map_petrescoTerm M factors ((j : ℕ) + 2))

/-- Recursive extensions on the first tail and all smaller head-suffix
subgroups make the full candidate preserve scalar powers. -/
lemma candidate_nu_extensions {n : ℕ}
    (b : HCBasis G (n + 1))
    {ν : Type v} {H : Type w}
    [CommRing ν] [BinomialRing ν] [Group H]
    [NuPoweredGroup ν H] [SatisfiesPoweredAxioms ν H]
    (f : G →* H)
    (Ftail : NPHom ν (HComp b.tailBasis ν) H)
    (hFtail :
      Ftail.toMonoidHom.comp (embedding b.tailBasis) =
        f.comp (b.tail 1).subtype)
    (Fhs : ∀ i : Fin n, NPHom ν
      (HComp
        (b.headSuffixBasis ((i : ℕ) + 2) (by omega) (by omega)) ν) H)
    (hFhs : ∀ i : Fin n,
      (Fhs i).toMonoidHom.comp
          (embedding
            (b.headSuffixBasis ((i : ℕ) + 2) (by omega) (by omega))) =
        f.comp (b.headSuffixSubgroup ((i : ℕ) + 2)).subtype)
    (x : HComp b ν) (a : ν) :
    extensionCandidate b f (nuPow (ν := ν) x a) =
      nuPow (ν := ν) (extensionCandidate b f x) a := by
  let hmul : ∀ y z : HComp b ν,
      extensionCandidate b f (y * z) =
        extensionCandidate b f y * extensionCandidate b f z :=
    extension_candidate_extensions b f Ftail hFtail Fhs hFhs
  let M := extensionCandidateMonoid b f hmul
  let head :=
    nuPow (ν := ν) ((embedding (ν := ν) b) (b.generators 0)) (x.coord 0)
  let tail := tailLift b (tailPoint b x)
  let factors : List (HComp b ν) := [head, tail]
  let targetFactors : List H := factors.map M
  have hprod : factors.prod = x := by
    simp only [factors, List.prod_cons, List.prod_nil, _root_.mul_one]
    exact (nu_head_lift b x).symm
  have htargetProd : targetFactors.prod = M x := by
    change (factors.map M).prod = M x
    rw [← map_list_prod, hprod]
  obtain ⟨c, htargetTrivial, htargetFormula⟩ :=
    SatisfiesPoweredAxioms.scalar_petresco targetFactors a
  let d := max (n + 1) c
  have hnd : n + 1 ≤ d := le_max_left _ _
  have hcd : c ≤ d := le_max_right _ _
  have hdpos : 0 < d := lt_of_lt_of_le (by omega) hnd
  have hd : d = (d - 1) + 1 := (Nat.sub_add_cancel (by omega)).symm
  have hsource :
      (factors.map fun g => nuPow (ν := ν) g a).prod =
        nuPow (ν := ν) x a *
          nuPetrescoTail (petrescoTerm factors) a (d - 1) := by
    calc
      (factors.map fun g => nuPow (ν := ν) g a).prod =
          nuPetrescoBinomial (petrescoTerm factors) a (n + 1) := by
        simpa only [nu_pow] using scalar_petresco b factors a
      _ = nuPetrescoBinomial (petrescoTerm factors) a d :=
        (nu_petresco_binomial
          (petrescoTerm factors) a hnd
          (fun w hw => petresco_term_length b factors hw)).symm
      _ = nuPow (ν := ν) x a *
          nuPetrescoTail (petrescoTerm factors) a (d - 1) := by
        conv_lhs => rw [hd]
        rw [nu_petresco_succ, petrescoTerm_one, hprod]
  have htarget :
      (targetFactors.map fun g => nuPow (ν := ν) g a).prod =
        nuPow (ν := ν) (M x) a *
          nuPetrescoTail (petrescoTerm targetFactors) a (d - 1) := by
    calc
      (targetFactors.map fun g => nuPow (ν := ν) g a).prod =
          nuPetrescoBinomial (petrescoTerm targetFactors) a c :=
        htargetFormula
      _ = nuPetrescoBinomial (petrescoTerm targetFactors) a d :=
        (nu_petresco_binomial
          (petrescoTerm targetFactors) a hcd htargetTrivial).symm
      _ = nuPow (ν := ν) (M x) a *
          nuPetrescoTail (petrescoTerm targetFactors) a (d - 1) := by
        conv_lhs => rw [hd]
        rw [nu_petresco_succ, petrescoTerm_one, htargetProd]
  have hmapped :
      (targetFactors.map fun g => nuPow (ν := ν) g a).prod =
        M (nuPow (ν := ν) x a) *
          nuPetrescoTail (petrescoTerm targetFactors) a (d - 1) := by
    calc
      (targetFactors.map fun g => nuPow (ν := ν) g a).prod =
          M ((factors.map fun g => nuPow (ν := ν) g a).prod) := by
        simp only [targetFactors, factors, List.map_cons, List.map_nil,
          List.prod_cons, List.prod_nil, _root_.mul_one]
        rw [M.map_mul]
        change
          nuPow (ν := ν) (extensionCandidate b f head) a *
                nuPow (ν := ν) (extensionCandidate b f tail) a =
            extensionCandidate b f (nuPow (ν := ν) head a) *
              extensionCandidate b f (nuPow (ν := ν) tail a)
        rw [candidate_nu_head,
          candidate_nu_lift b f Ftail hFtail]
      _ = M (nuPow (ν := ν) x a *
          nuPetrescoTail (petrescoTerm factors) a (d - 1)) := by
        rw [hsource]
      _ = M (nuPow (ν := ν) x a) *
          M (nuPetrescoTail (petrescoTerm factors) a (d - 1)) := by
        rw [M.map_mul]
      _ = M (nuPow (ν := ν) x a) *
          nuPetrescoTail (petrescoTerm targetFactors) a (d - 1) := by
        rw [show
          M (nuPetrescoTail (petrescoTerm factors) a (d - 1)) =
            extensionCandidate b f
              (nuPetrescoTail (petrescoTerm factors) a (d - 1)) by
            rfl]
        exact congrArg (M (nuPow (ν := ν) x a) * ·)
          (candidate_nu_petresco
            b f Ftail hFtail hmul factors a (d - 1))
  exact mul_right_cancel (hmapped.symm.trans htarget)

/-- Hall's extension theorem for the empty canonical basis. -/
noncomputable def extensionZero (b : HCBasis G 0)
    {ν : Type v} {H : Type w}
    [CommRing ν] [BinomialRing ν] [Group H]
    [NuPoweredGroup ν H] [SatisfiesPoweredAxioms ν H]
    (f : G →* H) :
    NPHom ν (HComp b ν) H where
  toFun := extensionCandidate b f
  map_one' := extensionCandidate_one b f
  map_mul' x y := by simp
  map_nuPow' x a := by simp

/-- Hall's extension theorem for a one-generator canonical basis. -/
noncomputable def extensionOne (b : HCBasis G 1)
    {ν : Type v} {H : Type w}
    [CommRing ν] [BinomialRing ν] [Group H]
    [NuPoweredGroup ν H] [SatisfiesPoweredAxioms ν H]
    (f : G →* H) :
    NPHom ν (HComp b ν) H where
  toFun := extensionCandidate b f
  map_one' := extensionCandidate_one b f
  map_mul' x y := by
    rw [extension_candidate_generator,
      extension_candidate_generator, extension_candidate_generator,
      coord_mul_zero, SatisfiesPoweredAxioms.pow_add]
  map_nuPow' x a := by
    change
      extensionCandidate b f (nuPow (ν := ν) x a) =
        nuPow (ν := ν) (extensionCandidate b f x) a
    rw [extension_candidate_generator,
      extension_candidate_generator, coord_nu_zero, mul_comm,
      SatisfiesPoweredAxioms.pow_mul]

@[simp]
lemma extension_zero_embedding (b : HCBasis G 0)
    {ν : Type v} {H : Type w}
    [CommRing ν] [BinomialRing ν] [Group H]
    [NuPoweredGroup ν H] [SatisfiesPoweredAxioms ν H]
    (f : G →* H) :
    (extensionZero b f).toMonoidHom.comp (embedding (ν := ν) b) = f := by
  ext g
  exact extensionCandidate_embedding b (ν := ν) f g

@[simp]
lemma extension_one_embedding (b : HCBasis G 1)
    {ν : Type v} {H : Type w}
    [CommRing ν] [BinomialRing ν] [Group H]
    [NuPoweredGroup ν H] [SatisfiesPoweredAxioms ν H]
    (f : G →* H) :
    (extensionOne b f).toMonoidHom.comp (embedding (ν := ν) b) = f := by
  ext g
  exact extensionCandidate_embedding b (ν := ν) f g

/-- Every Hall coordinate completion has the powered extension required in
Hall's Theorem 6.7. The strong induction simultaneously supplies the first
tail and every smaller head-plus-suffix extension used by the successor
step. -/
theorem exists_extension {n : ℕ} (b : HCBasis G n)
    {ν : Type v} {H : Type w}
    [CommRing ν] [BinomialRing ν] [Group H]
    [NuPoweredGroup ν H] [SatisfiesPoweredAxioms ν H]
    (f : G →* H) :
    ∃ F : NPHom ν (HComp b ν) H,
      F.toMonoidHom.comp (embedding b) = f := by
  induction n using Nat.strong_induction_on generalizing G with
  | h n ih =>
      cases n with
      | zero =>
          exact ⟨extensionZero b f, extension_zero_embedding b f⟩
      | succ n =>
          let ftail : b.tail 1 →* H := f.comp (b.tail 1).subtype
          obtain ⟨Ftail, hFtail⟩ := ih n (by omega) b.tailBasis ftail
          have hexistsFhs : ∀ i : Fin n, ∃ Fhs : NPHom ν
              (HComp
                (b.headSuffixBasis ((i : ℕ) + 2) (by omega) (by omega)) ν) H,
              Fhs.toMonoidHom.comp
                  (embedding
                    (b.headSuffixBasis ((i : ℕ) + 2) (by omega) (by omega))) =
                f.comp (b.headSuffixSubgroup ((i : ℕ) + 2)).subtype := by
            intro i
            exact ih _ (by omega)
              (b.headSuffixBasis ((i : ℕ) + 2) (by omega) (by omega))
              (f.comp (b.headSuffixSubgroup ((i : ℕ) + 2)).subtype)
          choose Fhs hFhs using hexistsFhs
          let F : NPHom ν (HComp b ν) H :=
            { toFun := extensionCandidate b f
              map_one' := extensionCandidate_one b f
              map_mul' :=
                extension_candidate_extensions b f Ftail hFtail Fhs hFhs
              map_nuPow' :=
                candidate_nu_extensions b f Ftail hFtail Fhs hFhs }
          refine ⟨F, ?_⟩
          apply MonoidHom.ext
          intro g
          exact extensionCandidate_embedding b (ν := ν) f g

end HComp

/-- **Hall, Theorem 6.7, universal-property form.** The canonical embedding
into the Hall coordinate completion extends every ordinary homomorphism to a
Hall-powered target. -/
theorem hall_completion_extension
    {ν : Type v} [CommRing ν] [BinomialRing ν]
    {G : Type u} {H : Type w} [Group G] [Group H]
    [NuPoweredGroup ν H] [SatisfiesPoweredAxioms ν H]
    {n : ℕ} (b : HCBasis G n) (f : G →* H) :
    ∃ F : NPHom ν (HComp b ν) H,
      F.toMonoidHom.comp (HComp.embedding b) = f :=
  HComp.exists_extension b f

/-- The set of all scalar powers of elements of `S`. -/
def nuPowerSet {ν : Type v} {G : Type u} [Group G] [NuPoweredGroup ν G]
    (S : Set G) : Set G :=
  {y | ∃ x ∈ S, ∃ a : ν, nuPow (ν := ν) x a = y}

/-- The ordinary subgroup generated by all scalar powers of elements of
`S`. Hall's corollary says that this is already powered when `S` is a
subgroup with a Hall canonical basis. -/
def nuGeneratedSubgroup
    {ν : Type v} {G : Type u} [Group G] [NuPoweredGroup ν G]
    (S : Set G) : Subgroup G :=
  Subgroup.closure (nuPowerSet (ν := ν) S)

lemma subset_nu_generated
    {ν : Type v} {G : Type u} [CommRing ν] [BinomialRing ν]
    [Group G] [NuPoweredGroup ν G] [SatisfiesPoweredAxioms ν G]
    (S : Set G) :
    S ⊆ nuGeneratedSubgroup (ν := ν) S := by
  intro x hx
  apply Subgroup.subset_closure
  exact ⟨x, hx, 1, nu_pow_scalar x⟩

lemma nu_generated_subgroup
    {ν : Type v} {G : Type u} [Group G] [NuPoweredGroup ν G]
    {S : Set G} {K : Subgroup G}
    (hS : S ⊆ K) (hK : NuPoweredSubgroup ν K) :
    nuGeneratedSubgroup (ν := ν) S ≤ K := by
  rw [nuGeneratedSubgroup, Subgroup.closure_le]
  rintro y ⟨x, hx, a, rfl⟩
  exact hK x (hS hx) a

/-- The extension theorem identifies the subgroup generated by scalar powers
with the range of the extended inclusion map, so it is already powered. -/
theorem nu_powered_basis
    {ν : Type v} {H : Type w} [CommRing ν] [BinomialRing ν]
    [Group H] [NuPoweredGroup ν H] [SatisfiesPoweredAxioms ν H]
    (X : Subgroup H) {n : ℕ} (b : HCBasis X n) :
    NuPoweredSubgroup ν (nuGeneratedSubgroup (ν := ν) (X : Set H)) := by
  obtain ⟨F, hF⟩ :=
    hall_completion_extension (ν := ν) b X.subtype
  have hrange :
      nuGeneratedSubgroup (ν := ν) (X : Set H) =
        F.toMonoidHom.range := by
    apply le_antisymm
    · rw [nuGeneratedSubgroup, Subgroup.closure_le]
      rintro y ⟨x, hx, a, rfl⟩
      let xX : X := ⟨x, hx⟩
      refine ⟨nuPow (ν := ν)
        ((HComp.embedding (ν := ν) b) xX) a, ?_⟩
      rw [F.map_nuPow]
      exact congrArg (fun z : H => nuPow (ν := ν) z a)
        (congrArg (fun q : X →* H => q xX) hF)
    · rintro y ⟨z, rfl⟩
      rw [HComp.nu_powered_candidate
        b F X.subtype hF z]
      unfold HComp.extensionCandidate nuBasisProduct
        orderedNuProduct
      apply (nuGeneratedSubgroup (ν := ν) (X : Set H)).list_prod_mem
      intro y hy
      simp only [List.mem_map] at hy
      obtain ⟨i, _, rfl⟩ := hy
      apply Subgroup.subset_closure
      exact ⟨(b.generators i : H), (b.generators i).property, z.coord i, rfl⟩
  rw [hrange]
  intro y hy a
  obtain ⟨z, rfl⟩ := hy
  rw [← F.map_nuPow]
  exact ⟨nuPow (ν := ν) z a, rfl⟩

/-- The intersection of all `ν`-powered subgroups containing `S`. -/
def nuPoweredClosure {ν : Type v} {G : Type u} [Group G]
    [NuPoweredGroup ν G] (S : Set G) : Subgroup G :=
  sInf {H : Subgroup G | S ⊆ H ∧ NuPoweredSubgroup ν H}

lemma subset_nu_powered {ν : Type v} {G : Type u} [Group G]
    [NuPoweredGroup ν G] (S : Set G) :
    S ⊆ nuPoweredClosure (ν := ν) S := by
  intro x hx
  change x ∈ sInf {H : Subgroup G | S ⊆ H ∧ NuPoweredSubgroup ν H}
  exact Subgroup.mem_sInf.mpr fun H hH => hH.1 hx

lemma nu_powered_subgroup
    {ν : Type v} {G : Type u} [Group G] [NuPoweredGroup ν G]
    (S : Set G) :
    NuPoweredSubgroup ν (nuPoweredClosure (ν := ν) S) := by
  intro x hx a
  change x ∈ sInf {H : Subgroup G | S ⊆ H ∧ NuPoweredSubgroup ν H} at hx
  change nuPow (ν := ν) x a ∈
    sInf {H : Subgroup G | S ⊆ H ∧ NuPoweredSubgroup ν H}
  exact Subgroup.mem_sInf.mpr fun H hH =>
    hH.2 x (Subgroup.mem_sInf.mp hx H hH) a

lemma nu_powered
    {ν : Type v} {G : Type u} [Group G] [NuPoweredGroup ν G]
    {S : Set G} {H : Subgroup G}
    (hS : S ⊆ H) (hH : NuPoweredSubgroup ν H) :
    nuPoweredClosure (ν := ν) S ≤ H :=
  sInf_le ⟨hS, hH⟩

/-- The powered closure is the smallest powered subgroup containing a given
set. -/
theorem nu_closure_spec
    {ν : Type v} {G : Type u} [Group G] [NuPoweredGroup ν G]
    (S : Set G) :
    S ⊆ nuPoweredClosure (ν := ν) S ∧
      NuPoweredSubgroup ν (nuPoweredClosure (ν := ν) S) ∧
        ∀ H : Subgroup G, S ⊆ H → NuPoweredSubgroup ν H →
          nuPoweredClosure (ν := ν) S ≤ H :=
  ⟨subset_nu_powered (ν := ν) S,
    nu_powered_subgroup (ν := ν) S,
    fun _ hS hH => nu_powered (ν := ν) hS hH⟩

/-- **Corollary to Hall's Theorem 6.7.** If `X` has a Hall canonical basis,
the ordinary subgroup generated by its scalar powers is the smallest
`ν`-powered subgroup of `H` containing `X`. -/
theorem nu_powered_closure
    {ν : Type v} {H : Type w} [CommRing ν] [BinomialRing ν]
    [Group H] [NuPoweredGroup ν H] [SatisfiesPoweredAxioms ν H]
    (X : Subgroup H) {n : ℕ} (b : HCBasis X n) :
    X ≤ nuGeneratedSubgroup (ν := ν) (X : Set H) ∧
      NuPoweredSubgroup ν
        (nuGeneratedSubgroup (ν := ν) (X : Set H)) ∧
        ∀ K : Subgroup H, X ≤ K → NuPoweredSubgroup ν K →
          nuGeneratedSubgroup (ν := ν) (X : Set H) ≤ K :=
  ⟨subset_nu_generated (ν := ν) (X : Set H),
    nu_powered_basis
      (ν := ν) X b,
    fun _ hX hK => nu_generated_subgroup (ν := ν) hX hK⟩

end Edmonton
end Submission
