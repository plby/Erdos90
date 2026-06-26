import Towers.Group.Zassenhaus.CollectionSteps

/-!
# Coordinate output from symbolic repeated-power factors

A completed symbolic collector groups signed packet families by Hall
coordinate.  This file forgets the Hall decorations of one such finite group
and retains the explicit repeated-block expansion needed by Claim 5.

The file is intentionally not imported by the existing collection proof.
-/

namespace Towers
namespace TCTex

universe u

namespace BBRecipe

/-- Reuse a bounded recipe at any larger target weight. -/
def weaken
    {inputWeight targetWeight largerWeight : ℕ}
    (recipe : BBRecipe inputWeight targetWeight)
    (hweight : targetWeight ≤ largerWeight) :
    BBRecipe inputWeight largerWeight where
  toPBRecipe := recipe.toPBRecipe
  outputWeight_le := recipe.outputWeight_le.trans hweight

@[simp]
lemma eval_weaken
    {inputWeight targetWeight largerWeight : ℕ}
    (recipe : BBRecipe inputWeight targetWeight)
    (hweight : targetWeight ≤ largerWeight) :
    (recipe.weaken hweight).eval = recipe.eval :=
  rfl

end BBRecipe

/--
One signed symbolic packet family selected as a contribution to a coordinate
at `targetWeight`.

The grouping step of a concrete Hall collector supplies `word_weight_le`.
Usually it is an equality because the final factor is a weight-`targetWeight`
Hall atom.
-/
structure SCContri
    {d : ℕ}
    (H : ∀ r : ℕ, BCWta.{u} d r)
    (inputWeight targetWeight : ℕ) where
  factor :
    SPFactora H inputWeight
  word_weight_le :
    factor.word.weight PEAddres.weight ≤ targetWeight

namespace SCContri

/-- Forget Hall decorations while retaining the signed repeated-block term. -/
def term
    {d inputWeight targetWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (contribution :
      SCContri H inputWeight targetWeight) :
    BRTerm inputWeight targetWeight :=
  (contribution.factor.coefficient,
    contribution.factor.recipe.weaken contribution.word_weight_le)

@[simp]
lemma term_eval
    {d inputWeight targetWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (contribution :
      SCContri H inputWeight targetWeight) :
    contribution.term.eval = contribution.factor.exponent := by
  ext q
  rfl

/-- Sum the exponents of a finite list of coordinate contributions. -/
def listEval
    {d inputWeight targetWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (contributions :
      List (SCContri H inputWeight targetWeight)) :
    ℕ → ℤ :=
  (contributions.map fun contribution => contribution.term.eval).sum

lemma list_sum_exponents
    {d inputWeight targetWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (contributions :
      List (SCContri H inputWeight targetWeight)) :
    listEval contributions =
      (contributions.map fun contribution => contribution.factor.exponent).sum := by
  simp [listEval]

/-- The explicit repeated-block expansion obtained from finite contributions. -/
def coordinateExpansion
    {d inputWeight targetWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (contributions :
      List (SCContri H inputWeight targetWeight)) :
    BCExp inputWeight targetWeight where
  terms := contributions.map term

@[simp]
lemma coordinateExpansion_eval
    {d inputWeight targetWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (contributions :
      List (SCContri H inputWeight targetWeight)) :
    (coordinateExpansion contributions).eval = listEval contributions := by
  ext q
  simp [coordinateExpansion, BCExp.eval, listEval,
    Function.comp_def]

/--
Every finite list of signed symbolic coordinate contributions gives an
integer-valued polynomial with the Claim 5 degree bound.
-/
lemma list_valued_most
    {d inputWeight targetWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (hinputWeight : 0 < inputWeight)
    (contributions :
      List (SCContri H inputWeight targetWeight)) :
    IVMost
      (listEval contributions) (targetWeight / inputWeight) := by
  rw [← coordinateExpansion_eval contributions]
  exact (coordinateExpansion contributions).integerValuedMost
    hinputWeight

end SCContri

/--
Collector-facing output in terms of finite signed symbolic contribution lists.

A concrete repeated-block Hall collector only needs to provide these lists and
the recollected product identity.  The conversion to explicit coordinate
expansions and then to Claim 5 polynomials is automatic.
-/
def CCData
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
                ∃ contributions :
                    List (SCContri H r s),
                  SCContri.listEval contributions =
                    fun q : ℕ => E q s i

/-- Finite signed contribution lists supply explicit coordinate expansions. -/
lemma CCData.toExpansionData
    {d n r : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    {e : HEFam H}
    (hdata : CCData (n := n) H e r) :
    CEData (n := n) H e r := by
  intro heBelow
  obtain ⟨E, hEproduct, hEcoordinate⟩ := hdata heBelow
  refine ⟨E, hEproduct, ?_⟩
  intro s hs hsn i
  obtain ⟨contributions, hcontributions⟩ := hEcoordinate s hs hsn i
  exact ⟨SCContri.coordinateExpansion contributions,
    (SCContri.coordinateExpansion_eval
      contributions).trans hcontributions⟩

/--
Finite signed symbolic contribution lists therefore imply the polynomial data
consumed by Claim 5.
-/
lemma CCData.toPolynomialData
    {d n r : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    {e : HEFam H}
    (hr : 1 ≤ r)
    (hdata : CCData (n := n) H e r) :
    CollectedPolynomialData (n := n) H e r :=
  hdata.toExpansionData.toPolynomialData hr

end TCTex
end Towers
