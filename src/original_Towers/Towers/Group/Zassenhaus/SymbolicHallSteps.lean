import Towers.Group.Zassenhaus.SymbolicHallFactors
import Towers.Group.Zassenhaus.SymbolicHallCollection

/-!
# Cutoff-specific steps for signed polynomial Hall collection

Nonterminal Hall-Petresco expansion emits Hall words carrying finite signed
generalized-binomial formulas.  This file packages the exact correction packet
required for one adjacent swap and the resulting finite rewrite relation.

The packet fields isolate the remaining group-theoretic task cleanly: construct
one finite higher-word list whose ordered evaluation is the commutator of the
two parent factors.  Every retained child is physically below the nilpotent
cutoff and has strictly higher ordinary weight than both parents.

The file is intentionally not imported by the existing collection proof.
-/

namespace Towers
namespace TCTex

universe u

open scoped commutatorElement

/-- Exact cutoff-specific higher corrections for one signed polynomial swap. -/
structure TSPkt
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (n : ℕ)
    (B A : SPFactor H ι) where
  factors :
    List (SPFactor H ι)
  listEval_eq :
    ∀ e : ι → HEFam H,
      SPFactor.listEval (n := n) e factors =
        ⁅B.eval (n := n) e, A.eval (n := n) e⁆
  word_weight_left :
    ∀ x ∈ factors,
      B.word.weight HEAddres.weight <
        x.word.weight HEAddres.weight
  word_weight_right :
    ∀ x ∈ factors,
      A.word.weight HEAddres.weight <
        x.word.weight HEAddres.weight
  word_weight_cutoff :
    ∀ x ∈ factors,
      x.word.weight HEAddres.weight < n

namespace TSPkt

/-- Packet evaluation is exactly the correction needed for its adjacent swap. -/
lemma list_mul_swap
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {B A : SPFactor H ι}
    (C : TSPkt n B A)
    (e : ι → HEFam H) :
    SPFactor.listEval (n := n) e C.factors *
          A.eval (n := n) e * B.eval (n := n) e =
      B.eval (n := n) e * A.eval (n := n) e := by
  rw [C.listEval_eq]
  simp [commutatorElement_def, mul_assoc]

/--
Embed an earlier one-monomial packet into the richer signed polynomial packet
state.  This keeps all terminal packet constructors available to the
nonterminal collector.
-/
def ofMonomial
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {B A : SCFactor H ι}
    (C : SCPkta n B A) :
    TSPkt n
      (.ofMonomial B) (.ofMonomial A) where
  factors := C.factors.map SPFactor.ofMonomial
  listEval_eq := by
    intro e
    rw [SPFactor.list_eval_monomial, C.listEval_eq,
      SPFactor.eval_ofMonomial,
      SPFactor.eval_ofMonomial]
  word_weight_left := by
    intro x hx
    rcases List.mem_map.mp hx with ⟨y, hy, rfl⟩
    exact C.word_weight_left y hy
  word_weight_right := by
    intro x hx
    rcases List.mem_map.mp hx with ⟨y, hy, rfl⟩
    exact C.word_weight_right y hy
  word_weight_cutoff := by
    intro x hx
    rcases List.mem_map.mp hx with ⟨y, hy, rfl⟩
    exact C.word_weight_cutoff y hy

/-- Remaining room below the nilpotent cutoff for one signed factor. -/
def cutoffDefect
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (n : ℕ)
    (x : SPFactor H ι) :
    ℕ :=
  n - x.word.weight HEAddres.weight

/-- Every retained correction strictly lowers the left-parent recursion measure. -/
lemma defect_left_factors
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {B A : SPFactor H ι}
    (C : TSPkt n B A)
    {x : SPFactor H ι}
    (hx : x ∈ C.factors) :
    cutoffDefect n x < cutoffDefect n B := by
  simp only [cutoffDefect]
  have hleft := C.word_weight_left x hx
  have hcutoff := C.word_weight_cutoff x hx
  omega

/-- Every retained correction strictly lowers the right-parent recursion measure. -/
lemma cutoff_defect_factors
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {B A : SPFactor H ι}
    (C : TSPkt n B A)
    {x : SPFactor H ι}
    (hx : x ∈ C.factors) :
    cutoffDefect n x < cutoffDefect n A := by
  simp only [cutoffDefect]
  have hright := C.word_weight_right x hx
  have hcutoff := C.word_weight_cutoff x hx
  omega

end TSPkt

namespace SPFactor

/-- A higher correction descends when its cutoff-minus-weight defect decreases. -/
def CorrectionDescends
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (n : ℕ)
    (child parent : SPFactor H ι) :
    Prop :=
  TSPkt.cutoffDefect n child <
    TSPkt.cutoffDefect n parent

/-- Signed polynomial correction descent is well-founded. -/
lemma correction_well_founded
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type} :
    WellFounded (@CorrectionDescends d H ι n) := by
  unfold CorrectionDescends
  exact InvImage.wf
    (TSPkt.cutoffDefect n)
    Nat.lt_wfRel.wf

/-- Recursion principle for a nonterminal signed polynomial packet builder. -/
theorem correctionDescends_induction
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {motive : SPFactor H ι → Prop}
    (step :
      ∀ parent,
        (∀ child, CorrectionDescends n child parent → motive child) →
          motive parent)
    (x : SPFactor H ι) :
    motive x :=
  correction_well_founded.induction x step

end SPFactor

/-- One sound adjacent signed polynomial Hall-collection move. -/
inductive TCStepa
    {d n : ℕ}
    (H : ∀ r : ℕ, BCWta.{u} d r)
    (ι : Type) :
    List (SPFactor H ι) →
      List (SPFactor H ι) → Prop where
  | obstruction
      (P S : List (SPFactor H ι))
      (B A : SPFactor H ι)
      (C : TSPkt n B A) :
      TCStepa H ι
        (P ++ [B, A] ++ S)
        (P ++ C.factors ++ [A, B] ++ S)

/-- Finite sequence of sound cutoff-specific signed polynomial swaps. -/
abbrev TCRw
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (L R : List (SPFactor H ι)) :
    Prop :=
  Relation.ReflTransGen
    (TCStepa (n := n) H ι) L R

/-- One signed polynomial collection move preserves evaluated products. -/
lemma TCStepa.listEval_eq
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {L R : List (SPFactor H ι)}
    (h : TCStepa (n := n) H ι L R)
    (e : ι → HEFam H) :
    SPFactor.listEval (n := n) e R =
      SPFactor.listEval (n := n) e L := by
  cases h with
  | obstruction P S B A C =>
      calc
        SPFactor.listEval (n := n) e
              (P ++ C.factors ++ [A, B] ++ S) =
            SPFactor.listEval e P *
                (SPFactor.listEval e C.factors *
                  A.eval e * B.eval e) *
              SPFactor.listEval e S := by
            simp [mul_assoc]
        _ =
            SPFactor.listEval e P *
                (B.eval e * A.eval e) *
              SPFactor.listEval e S := by
            rw [C.list_mul_swap]
        _ =
            SPFactor.listEval (n := n) e
              (P ++ [B, A] ++ S) := by
            simp [mul_assoc]

/-- Any finite signed polynomial collection run preserves evaluated products. -/
lemma TCRw.listEval_eq
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {L R : List (SPFactor H ι)}
    (h : TCRw (n := n) L R)
    (e : ι → HEFam H) :
    SPFactor.listEval (n := n) e R =
      SPFactor.listEval (n := n) e L := by
  induction h with
  | refl =>
      rfl
  | tail hLR hstep ih =>
      exact (hstep.listEval_eq e).trans ih

end TCTex
end Towers
