import Submission.Group.Zassenhaus.PowerPolynomials

universe u

/-!
# Repeated-block collector output for Hall powers

This file gives the missing Hall power collector a smaller target than an
arbitrary rational polynomial.  It is enough to express every collected
coordinate as an integer linear combination of weighted repeated-block
binomial monomials.  The polynomial package used by Claim 5 then follows from
the arithmetic developed in `PowerCollectionPolynomials`.

The file is intentionally not imported by the existing collection proof.
-/

namespace Submission
namespace TCTex

/--
Collector-facing output for powers of one collected Hall normal form.

The coordinate at target weight `s` is recorded as an integer combination of
repeated-block recipes whose total selected-block degree costs at most `s`.
-/
def CBData
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
                CombinationBinomialMonomials
                  r s
                  (fun q : ℕ => E q s i)

/--
Weighted repeated-block collector output implies the polynomial data consumed
by Claim 5.
-/
lemma CBData.toPolynomialData
    {d n r : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    {e : HEFam H}
    (hr : 1 ≤ r)
    (hdata : CBData (n := n) H e r) :
    CollectedPolynomialData (n := n) H e r := by
  intro heBelow
  obtain ⟨E, hEproduct, hEcoordinate⟩ := hdata heBelow
  refine ⟨E, hEproduct, ?_⟩
  intro s hs hsn i
  exact
    valued_most_combination
      (by omega)
      (hEcoordinate s hs hsn i)

/--
A uniform repeated-block collector supplies the existing polynomial input for
all initial weights.
-/
theorem collected_data_binomial
    {d n : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    (hpower :
      ∀ (e : HEFam H) (r : ℕ),
        1 ≤ r →
          CBData (n := n) H e r) :
    ∀ (e : HEFam H) (r : ℕ),
      1 ≤ r →
        CollectedPolynomialData (n := n) H e r := by
  intro e r hr
  exact (hpower e r hr).toPolynomialData hr

/--
Claim 5 can be invoked directly from weighted repeated-block collector output.
-/
theorem coordinate_binomial_data
    {d n r s : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ t : ℕ, BCWta.{u} d t)
    (hH :
      ∀ t : ℕ,
        1 ≤ t →
          t < n →
            (H t).FormsAssocGradedbasis (n := n))
    (hpower :
      ∀ (e : HEFam H) (t : ℕ),
        1 ≤ t →
          CBData (n := n) H e t)
    (u : LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
    (hu :
      u ∈ Subgroup.lowerCentralSeries
        (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n) (r - 1))
    (hr : 1 ≤ r)
    (hs : 1 ≤ s)
    (hsn : s < n)
    (i : (H s).index) :
    IVMost
      (fun q : ℕ => hallCoordinate hn H hH (u ^ q) i)
      (s / r) := by
  exact integer_valued_most
    hn H hH
    (collected_data_binomial hpower)
    u hu hr hs hsn i

end TCTex
end Submission
