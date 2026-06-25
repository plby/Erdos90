import Submission.Group.Zassenhaus.Truncation

/-!
# Well-founded recursion for truncated symbolic Hall power collection

Repeated-power Hall collection replaces an obstruction by correction factors of
strictly higher word weight.  Below a fixed nilpotent cutoff this is a
well-founded process: cutoff-minus-weight strictly decreases.

This file packages that termination argument independently of a particular
powered-commutator packet constructor.

The file is intentionally not imported by the existing collection proof.
-/

namespace Submission
namespace TCTex

universe u

namespace SPFactora

/-- A power correction descends from a parent when its remaining cutoff defect is smaller. -/
def CorrectionDescends
    {d inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (n : ℕ)
    (child parent : SPFactora H inputWeight) :
    Prop :=
  cutoffDefect n child < cutoffDefect n parent

/-- Power-correction descent is well-founded because it is measured in `ℕ`. -/
lemma correction_well_founded
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r} :
    WellFounded (@CorrectionDescends d inputWeight H n) := by
  unfold CorrectionDescends
  exact InvImage.wf (cutoffDefect n) Nat.lt_wfRel.wf

/-- The recursion principle used by a cutoff-specific repeated-power collector. -/
theorem correctionDescends_induction
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {motive : SPFactora H inputWeight → Prop}
    (step :
      ∀ parent,
        (∀ child, CorrectionDescends n child parent → motive child) →
          motive parent)
    (x : SPFactora H inputWeight) :
    motive x :=
  correction_well_founded.induction x step

/-- Positive cutoff defect is equivalent to lying strictly below the cutoff. -/
lemma cutoff_defect_pos
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (x : SPFactora H inputWeight) :
    0 < cutoffDefect n x ↔
      x.word.weight PEAddres.weight < n := by
  simp [cutoffDefect]

/-- Zero cutoff defect is equivalent to having reached or crossed the cutoff. -/
lemma cutoff_defect_weight
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (x : SPFactora H inputWeight) :
    cutoffDefect n x = 0 ↔
      n ≤ x.word.weight PEAddres.weight :=
  Nat.sub_eq_zero_iff_le

end SPFactora

namespace TCPkt

/-- Every retained repeated-power correction descends from the left parent. -/
lemma descends_left_factors
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {B A : SPFactora H inputWeight}
    (C : TCPkt n B A)
    {x : SPFactora H inputWeight}
    (hx : x ∈ C.factors) :
    SPFactora.CorrectionDescends n x B :=
  C.defect_left_factors hx

/-- Every retained repeated-power correction descends from the right parent. -/
lemma correction_descends_factors
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {B A : SPFactora H inputWeight}
    (C : TCPkt n B A)
    {x : SPFactora H inputWeight}
    (hx : x ∈ C.factors) :
    SPFactora.CorrectionDescends n x A :=
  C.cutoff_defect_factors hx

/--
If the left parent has at most one unit of cutoff defect, no retained
correction factor can remain.
-/
lemma nil_defect_left
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {B A : SPFactora H inputWeight}
    (C : TCPkt n B A)
    (hB : SPFactora.cutoffDefect n B ≤ 1) :
    C.factors = [] := by
  apply List.eq_nil_iff_forall_not_mem.2
  intro x hx
  have hxPos := C.defect_pos_factors hx
  have hxLt := C.defect_left_factors hx
  omega

/--
If the right parent has at most one unit of cutoff defect, no retained
correction factor can remain.
-/
lemma factors_nil_defect
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {B A : SPFactora H inputWeight}
    (C : TCPkt n B A)
    (hA : SPFactora.cutoffDefect n A ≤ 1) :
    C.factors = [] := by
  apply List.eq_nil_iff_forall_not_mem.2
  intro x hx
  have hxPos := C.defect_pos_factors hx
  have hxLt := C.cutoff_defect_factors hx
  omega

end TCPkt

end TCTex
end Submission
