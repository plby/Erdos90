import Submission.Group.Zassenhaus.InversePolynomials

/-!
# Finite signed formulas for product and inverse Hall collection

The Hall-Petresco collector does not emit only one generalized-binomial
monomial at a time.  Higher corrections carry finite integral linear
combinations of such monomials.  This file packages that coefficient language
constructively and proves that it is closed under the operations used by a
packet-level collector.

The file is intentionally not imported by the existing collection proof.
-/

namespace Submission
namespace TCTex

universe u

/-- One integer-weighted Claim 8 generalized-binomial monomial. -/
abbrev WBTerm
    {d : ℕ}
    (H : ∀ r : ℕ, BCWta.{u} d r)
    (ι : Type)
    (targetWeight : ℕ) :=
  ℤ × WHMono H ι targetWeight

namespace WBTerm

/-- Evaluate one signed generalized-binomial recipe term. -/
def eval
    {d targetWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (term : WBTerm H ι targetWeight)
    (e : ι → HEFam H) :
    ℤ :=
  term.1 * term.2.eval e

/-- Reuse one signed recipe term at a larger target weight. -/
def weaken
    {d targetWeight largerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (term : WBTerm H ι targetWeight)
    (hweight : targetWeight ≤ largerWeight) :
    WBTerm H ι largerWeight :=
  (term.1, term.2.weaken hweight)

@[simp]
lemma eval_weaken
    {d targetWeight largerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (term : WBTerm H ι targetWeight)
    (hweight : targetWeight ≤ largerWeight)
    (e : ι → HEFam H) :
    (term.weaken hweight).eval e = term.eval e := by
  simp [weaken, eval]

/-- Relabel the input blocks occurring in one signed recipe term. -/
def mapInput
    {d targetWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι κ : Type}
    (f : ι → κ)
    (term : WBTerm H ι targetWeight) :
    WBTerm H κ targetWeight :=
  (term.1, term.2.mapInput f)

@[simp]
lemma eval_mapInput
    {d targetWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι κ : Type}
    (e : κ → HEFam H)
    (f : ι → κ)
    (term : WBTerm H ι targetWeight) :
    (term.mapInput f).eval e = term.eval (e ∘ f) := by
  simp [mapInput, eval]

/--
Multiply two signed recipe terms by appending their independent histories.
-/
def mul
    {d leftWeight rightWeight targetWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (left : WBTerm H ι leftWeight)
    (right : WBTerm H ι rightWeight)
    (hweight : leftWeight + rightWeight ≤ targetWeight) :
    WBTerm H ι targetWeight :=
  (left.1 * right.1, left.2.append right.2 hweight)

@[simp]
lemma eval_mul
    {d leftWeight rightWeight targetWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (left : WBTerm H ι leftWeight)
    (right : WBTerm H ι rightWeight)
    (hweight : leftWeight + rightWeight ≤ targetWeight)
    (e : ι → HEFam H) :
    (left.mul right hweight).eval e = left.eval e * right.eval e := by
  simp [mul, eval]
  ring

/-- Distribute one fixed signed recipe term across a finite row of terms. -/
lemma sum_eval_mul
    {d leftWeight rightWeight targetWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (left : WBTerm H ι leftWeight)
    (rightTerms : List (WBTerm H ι rightWeight))
    (hweight : leftWeight + rightWeight ≤ targetWeight)
    (e : ι → HEFam H) :
    (rightTerms.map fun right => (left.mul right hweight).eval e).sum =
      left.eval e * (rightTerms.map fun right => right.eval e).sum := by
  induction rightTerms with
  | nil =>
      simp
  | cons right rightTerms ih =>
      calc
        ((right :: rightTerms).map fun nextRight =>
            (left.mul nextRight hweight).eval e).sum =
            (left.mul right hweight).eval e +
              (rightTerms.map fun nextRight =>
                (left.mul nextRight hweight).eval e).sum := by
              rfl
        _ =
            left.eval e * right.eval e +
              left.eval e *
                (rightTerms.map fun nextRight => nextRight.eval e).sum := by
              rw [WBTerm.eval_mul, ih]
        _ =
            left.eval e *
              ((right :: rightTerms).map fun nextRight =>
                nextRight.eval e).sum := by
              rw [List.map_cons, List.sum_cons, mul_add]

/-- Every signed recipe term lies in the Claim 8 integer span. -/
lemma combination_weighted_monomials
    {d targetWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (term : WBTerm H ι targetWeight)
    (e : ι → HEFam H) :
    ICMonomi
      H targetWeight e (term.eval e) := by
  exact
    ICMonomi.smul term.1
      (Submodule.subset_span ⟨term.2, rfl⟩)

end WBTerm

/--
A finite integral linear combination of Claim 8 generalized-binomial
monomials with one common target weight.
-/
structure WBForm
    {d : ℕ}
    (H : ∀ r : ℕ, BCWta.{u} d r)
    (ι : Type)
    (targetWeight : ℕ) where
  terms :
    List (WBTerm H ι targetWeight)

namespace WBForm

/-- Evaluate a finite signed Claim 8 formula. -/
def eval
    {d targetWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (formula : WBForm H ι targetWeight)
    (e : ι → HEFam H) :
    ℤ :=
  (formula.terms.map fun term => term.eval e).sum

/-- The zero coefficient formula. -/
def zero
    {d : ℕ}
    (H : ∀ r : ℕ, BCWta.{u} d r)
    (ι : Type)
    (targetWeight : ℕ) :
    WBForm H ι targetWeight where
  terms := []

/-- A formula containing one signed generalized-binomial term. -/
def singleton
    {d targetWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (term : WBTerm H ι targetWeight) :
    WBForm H ι targetWeight where
  terms := [term]

/-- Concatenate two finite signed formulas. -/
def append
    {d targetWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (left right : WBForm H ι targetWeight) :
    WBForm H ι targetWeight where
  terms := left.terms ++ right.terms

/-- Reuse a signed formula at a larger target weight. -/
def weaken
    {d targetWeight largerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (formula : WBForm H ι targetWeight)
    (hweight : targetWeight ≤ largerWeight) :
    WBForm H ι largerWeight where
  terms := formula.terms.map fun term => term.weaken hweight

/-- Relabel every input block occurring in a signed formula. -/
def mapInput
    {d targetWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι κ : Type}
    (f : ι → κ)
    (formula : WBForm H ι targetWeight) :
    WBForm H κ targetWeight where
  terms := formula.terms.map fun term => term.mapInput f

/--
Multiply two finite signed formulas by distributing over every pair of
appended recipe histories.
-/
def mul
    {d leftWeight rightWeight targetWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (left : WBForm H ι leftWeight)
    (right : WBForm H ι rightWeight)
    (hweight : leftWeight + rightWeight ≤ targetWeight) :
    WBForm H ι targetWeight where
  terms :=
    left.terms.flatMap fun leftTerm =>
      right.terms.map fun rightTerm => leftTerm.mul rightTerm hweight

@[simp]
lemma eval_zero
    {d : ℕ}
    (H : ∀ r : ℕ, BCWta.{u} d r)
    (ι : Type)
    (targetWeight : ℕ)
    (e : ι → HEFam H) :
    (zero H ι targetWeight).eval e = 0 := by
  simp [zero, eval]

@[simp]
lemma eval_singleton
    {d targetWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (term : WBTerm H ι targetWeight)
    (e : ι → HEFam H) :
    (singleton term).eval e = term.eval e := by
  simp [singleton, eval]

@[simp]
lemma eval_append
    {d targetWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (left right : WBForm H ι targetWeight)
    (e : ι → HEFam H) :
    (left.append right).eval e = left.eval e + right.eval e := by
  simp [append, eval]

@[simp]
lemma eval_weaken
    {d targetWeight largerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (formula : WBForm H ι targetWeight)
    (hweight : targetWeight ≤ largerWeight)
    (e : ι → HEFam H) :
    (formula.weaken hweight).eval e = formula.eval e := by
  simp [weaken, eval, Function.comp_def]

@[simp]
lemma eval_mapInput
    {d targetWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι κ : Type}
    (e : κ → HEFam H)
    (f : ι → κ)
    (formula : WBForm H ι targetWeight) :
    (formula.mapInput f).eval e = formula.eval (e ∘ f) := by
  simp [mapInput, eval, Function.comp_def]

@[simp]
lemma eval_mul
    {d leftWeight rightWeight targetWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (left : WBForm H ι leftWeight)
    (right : WBForm H ι rightWeight)
    (hweight : leftWeight + rightWeight ≤ targetWeight)
    (e : ι → HEFam H) :
    (left.mul right hweight).eval e = left.eval e * right.eval e := by
  cases left with
  | mk leftTerms =>
    induction leftTerms with
    | nil =>
        simp [mul, eval]
    | cons leftTerm leftTerms ih =>
        have hrow :
            ((right.terms.map fun rightTerm =>
                leftTerm.mul rightTerm hweight).map fun term =>
                  term.eval e).sum =
              leftTerm.eval e * right.eval e := by
          simpa [eval, List.map_map, Function.comp_def] using
            WBTerm.sum_eval_mul
              leftTerm right.terms hweight e
        have ih' :
            ((leftTerms.flatMap fun nextLeftTerm =>
                right.terms.map fun rightTerm =>
                  nextLeftTerm.mul rightTerm hweight).map fun term =>
                    term.eval e).sum =
              (leftTerms.map fun term => term.eval e).sum * right.eval e := by
          simpa [mul, eval] using ih
        change
          (List.map (fun term => term.eval e)
              ((right.terms.map fun rightTerm =>
                  leftTerm.mul rightTerm hweight) ++
                (leftTerms.flatMap fun nextLeftTerm =>
                  right.terms.map fun rightTerm =>
                    nextLeftTerm.mul rightTerm hweight))).sum =
            (leftTerm.eval e +
                (leftTerms.map fun term => term.eval e).sum) *
              right.eval e
        rw [List.map_append, List.sum_append]
        rw [hrow, ih', add_mul]

/-- Every finite signed formula lies in the Claim 8 integer span. -/
lemma combination_weighted_monomials
    {d targetWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (formula : WBForm H ι targetWeight)
    (e : ι → HEFam H) :
    ICMonomi
      H targetWeight e (formula.eval e) := by
  cases formula with
  | mk terms =>
    induction terms with
    | nil =>
        simpa [eval] using
          (ICMonomi.zero
            (s := targetWeight) e)
    | cons term terms ih =>
        simpa [eval] using
          ICMonomi.add
            (term.combination_weighted_monomials e) ih

/-- The raw source exponent formula `choose(e_j,a, 1)`. -/
def inputExponent
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (j : ι)
    (a : HEAddres H) :
    WBForm H ι a.1 :=
  singleton (1, WHMono.single j a le_rfl)

@[simp]
lemma eval_inputExponent
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (e : ι → HEFam H)
    (j : ι)
    (a : HEAddres H) :
    (inputExponent j a).eval e = e j a.1 a.2 := by
  simp [inputExponent, WBTerm.eval]

end WBForm

end TCTex
end Submission
