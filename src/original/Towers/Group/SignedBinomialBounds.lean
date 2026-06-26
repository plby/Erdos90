import Towers.Group.HallPetrescoCore

open scoped commutatorElement

namespace Towers
namespace HACoeff

open PPColl
open PPColl.RCColl.RPAggreg

/--
One bare powered commutator factor in the finite Hall-Petresco collection from
Lemma 4.  The coefficient retains its admissible-coefficient provenance.
-/
structure Factor
    (M N : ℕ) where
  word :
    CWord HPAtom
  coefficient :
    ℤ
  positive :
    word.PBPos
  coefficient_admissible :
    coefficient ∈
      submodule M N word.pairLeftDegree word.pairRightDegree

namespace Factor

/-- Evaluate one bare powered factor at a chosen Hall pair. -/
def eval
    {M N : ℕ}
    {G : Type*} [Group G]
    (x y : G)
    (F : Factor M N) :
    G :=
  F.word.eval (HPAtom.eval x y) ^ F.coefficient

/-- Forget provenance and regard a bare factor as a trace raw factor. -/
def toRFactor
    {M N : ℕ}
    {G : Type*} [Group G]
    (F : Factor M N) :
    PPColl.RFactor G where
  word := F.word
  multiplicity := F.coefficient
  conjugator := 1

@[simp]
lemma eval_raw_factor
    {M N : ℕ}
    {G : Type*} [Group G]
    (x y : G)
    (F : Factor M N) :
    F.toRFactor.eval x y = F.eval x y := by
  simp [toRFactor, eval, PPColl.RFactor.eval]

/-- Lemma 3 turns prime-power admissibility into the trace `Good` condition. -/
lemma good_raw_pow
    {p A B : ℕ}
    {G : Type*} [Group G]
    (F : Factor (p ^ A) (p ^ B)) :
    (F.toRFactor (G := G)).Good p A B := by
  exact
    good_submodule_pow
      F.positive.left F.positive.right F.coefficient_admissible

/-- The simplest Lemma 4 factor: the bare commutator `[X, Y]`. -/
def hallPair :
    Factor 1 1 where
  word := CWord.hallPairBase
  coefficient := 1
  positive := by
    simp [CWord.PBPos]
  coefficient_admissible := by
    apply Submodule.subset_span
    refine
      ⟨[{ sign := .positive, degree := 1 }],
        [{ sign := .positive, degree := 1 }], ?_, ?_, ?_⟩
    all_goals simp [degreeSum, blockProduct, signedChoose]

end Factor

/-- Appending one signed left source block preserves admissible coefficient
provenance while increasing the left bidegree by the number of selected
labels. -/
lemma signed_submodule_left
    {M N r s : ℕ}
    (sign : Sign)
    (k : ℕ)
    {E : ℤ}
    (hE : E ∈ submodule M N r s) :
    signedChoose sign M k * E ∈
      submodule M N (k + r) s := by
  induction hE using Submodule.span_induction with
  | mem E hE =>
      rcases hE with ⟨left, right, hr, hs, rfl⟩
      apply Submodule.subset_span
      refine ⟨{ sign := sign, degree := k } :: left, right, ?_, hs, ?_⟩
      · simpa only [degreeSum] using congrArg (fun n => k + n) hr
      · simp [blockProduct]
        ring
  | zero =>
      simp
  | add E F _hE _hF ihE ihF =>
      simpa [mul_add] using (submodule M N (k + r) s).add_mem ihE ihF
  | smul c E _hE ihE =>
      convert (submodule M N (k + r) s).smul_mem c ihE using 1
      simp
      ring

/-- Appending one signed right source block preserves admissible coefficient
provenance while increasing the right bidegree by the number of selected
labels. -/
lemma signed_choose_submodule
    {M N r s : ℕ}
    (sign : Sign)
    (k : ℕ)
    {E : ℤ}
    (hE : E ∈ submodule M N r s) :
    signedChoose sign N k * E ∈
      submodule M N r (k + s) := by
  induction hE using Submodule.span_induction with
  | mem E hE =>
      rcases hE with ⟨left, right, hr, hs, rfl⟩
      apply Submodule.subset_span
      refine ⟨left, { sign := sign, degree := k } :: right, hr, ?_, ?_⟩
      · simpa only [degreeSum] using congrArg (fun n => k + n) hs
      · simp [blockProduct]
        ring
  | zero =>
      simp
  | add E F _hE _hF ihE ihF =>
      simpa [mul_add] using (submodule M N r (k + s)).add_mem ihE ihF
  | smul c E _hE ihE =>
      convert (submodule M N r (k + s)).smul_mem c ihE using 1
      simp
      ring

/-- The empty production pattern has coefficient one and bidegree `(0, 0)`. -/
lemma one_submodule_zero
    (M N : ℕ) :
    (1 : ℤ) ∈ submodule M N 0 0 := by
  apply Submodule.subset_span
  exact ⟨[], [], by simp [degreeSum], by simp [degreeSum],
    by simp [blockProduct]⟩

/-- Positive left-block specialization of
`signed_submodule_left`. -/
lemma choose_submodule_left
    {M N r s : ℕ}
    (k : ℕ)
    {E : ℤ}
    (hE : E ∈ submodule M N r s) :
    (Nat.choose M k : ℤ) * E ∈
      submodule M N (k + r) s := by
  simpa [signedChoose] using
    signed_submodule_left Sign.positive k hE

/-- Positive right-block specialization of
`signed_choose_submodule`. -/
lemma choose_submodule_right
    {M N r s : ℕ}
    (k : ℕ)
    {E : ℤ}
    (hE : E ∈ submodule M N r s) :
    (Nat.choose N k : ℤ) * E ∈
      submodule M N r (k + s) := by
  simpa [signedChoose] using
    signed_choose_submodule Sign.positive k hE

/-- Products of admissible coefficients remain admissible after adding their
bidegrees.  This is the arithmetic rule used when two collected correction
patterns interact. -/
lemma mul_mem_submodule
    {M N r s r' s' : ℕ}
    {E F : ℤ}
    (hE : E ∈ submodule M N r s)
    (hF : F ∈ submodule M N r' s') :
    E * F ∈ submodule M N (r + r') (s + s') := by
  induction hE using Submodule.span_induction with
  | mem E hE =>
      rcases hE with ⟨left, right, hr, hs, rfl⟩
      induction hF using Submodule.span_induction with
      | mem F hF =>
          rcases hF with ⟨left', right', hr', hs', rfl⟩
          apply Submodule.subset_span
          refine ⟨left ++ left', right ++ right', ?_, ?_, ?_⟩
          · simp only [degreeSum, List.map_append, List.sum_append]
            exact congrArg₂ Nat.add hr hr'
          · simp only [degreeSum, List.map_append, List.sum_append]
            exact congrArg₂ Nat.add hs hs'
          · simp [blockProduct]
            ring
      | zero =>
          simp
      | add E F _hE _hF ihE ihF =>
          simpa [mul_add] using
            (submodule M N (r + r') (s + s')).add_mem ihE ihF
      | smul c E _hE ihE =>
          convert (submodule M N (r + r') (s + s')).smul_mem c ihE using 1
          simp
          ring
  | zero =>
      simp
  | add E F _hE _hF ihE ihF =>
      simpa [add_mul] using
        (submodule M N (r + r') (s + s')).add_mem ihE ihF
  | smul c E _hE ihE =>
      convert (submodule M N (r + r') (s + s')).smul_mem c ihE using 1
      simp
      ring

/-- Ordered evaluation of a finite list of bare powered factors. -/
def listEval
    {M N : ℕ}
    {G : Type*} [Group G]
    (x y : G)
    (L : List (Factor M N)) :
    G :=
  (L.map (Factor.eval x y)).prod

@[simp]
lemma listEval_nil
    {M N : ℕ}
    {G : Type*} [Group G]
    (x y : G) :
    listEval x y ([] : List (Factor M N)) = 1 :=
  rfl

@[simp]
lemma listEval_cons
    {M N : ℕ}
    {G : Type*} [Group G]
    (x y : G)
    (F : Factor M N)
    (L : List (Factor M N)) :
    listEval x y (F :: L) =
      F.eval x y * listEval x y L :=
  rfl

/--
The exact finite free-group witness asserted by Lemma 4.

Every factor is a bare powered formal commutator with admissible coefficient
provenance, and the ordered product is exactly `[X^M, Y^N]`.
-/
structure FExp
    (M N : ℕ) where
  factors :
    List (Factor M N)
  eval_eq :
    listEval universalLeft universalRight factors =
      ⁅universalLeft ^ M, universalRight ^ N⁆

namespace FExp

open PPColl
open RCColl.RPAggreg

/-- The base instance of Lemma 4. -/
def one_one :
    FExp 1 1 where
  factors := [Factor.hallPair]
  eval_eq := by
    simp [listEval, Factor.hallPair, Factor.eval]

/-- Evaluation of a formal factor commutes with specialization of the two
universal Hall-pair generators. -/
lemma specialize_factor_eval
    {M N : ℕ}
    {G : Type*} [Group G]
    (x y : G)
    (F : Factor M N) :
    specialize x y (F.eval universalLeft universalRight) =
      F.eval x y := by
  have hatoms :
      (fun a =>
        specialize x y (HPAtom.eval universalLeft universalRight a)) =
        HPAtom.eval x y := by
    funext a
    cases a <;> simp [HPAtom.eval]
  rw [Factor.eval, Factor.eval, map_zpow, CWord.map_eval]
  rw [hatoms]

/-- Ordered evaluation of a formal factor list commutes with specialization. -/
lemma specialize_listEval
    {M N : ℕ}
    {G : Type*} [Group G]
    (x y : G) :
    ∀ L : List (Factor M N),
      specialize x y (listEval universalLeft universalRight L) =
        listEval x y L
  | [] => by simp
  | F :: L => by
      simp [specialize_factor_eval, specialize_listEval x y L]

/-- Lemma 5: specialize a universal Lemma 4 expansion to an arbitrary group. -/
lemma list_commutator_pow
    {M N : ℕ}
    {G : Type*} [Group G]
    (E : FExp M N)
    (x y : G) :
    listEval x y E.factors = ⁅x ^ M, y ^ N⁆ := by
  rw [← specialize_listEval x y E.factors, E.eval_eq]
  simp [map_commutatorElement, map_pow]

/-- Forget provenance on a list of bare factors. -/
def rawFactors
    {M N : ℕ}
    {G : Type*} [Group G]
    (L : List (Factor M N)) :
    List (RFactor G) :=
  L.map Factor.toRFactor

@[simp]
lemma list_raw_factors
    {M N : ℕ}
    {G : Type*} [Group G]
    (x y : G) :
    ∀ L : List (Factor M N),
      PPColl.listEval x y (rawFactors L) =
        listEval x y L
  | [] => by simp [rawFactors]
  | F :: L => by
      change
        (F.toRFactor (G := G)).eval x y *
              PPColl.listEval x y (rawFactors L) =
          F.eval x y * listEval x y L
      rw [Factor.eval_raw_factor, list_raw_factors x y L]

/-- Prime-power specialization of Lemma 4 produces the trace requested by
`nonempty_trace`. -/
def toTrace
    {p A B : ℕ}
    {G : Type*} [Group G]
    (E : FExp (p ^ A) (p ^ B))
    (x y : G) :
    Trace p x y A B where
  factors :=
    rawFactors E.factors
  eval_eq := by
    rw [list_raw_factors, E.list_commutator_pow]
  factors_good := by
    intro F hF
    rcases List.mem_map.mp hF with ⟨D, _hD, rfl⟩
    exact D.good_raw_pow

end FExp

/--
A trace-compatible form of the Lemma 4 conclusion.  Unlike `FExp`,
this permits outer conjugators on the powered commutator factors.  The
arithmetic provenance is unchanged.
-/
structure CExp
    (M N : ℕ)
    {G : Type*} [Group G]
    (x y : G) where
  factors :
    List (PPColl.RFactor G)
  eval_eq :
    PPColl.listEval x y factors =
      ⁅x ^ M, y ^ N⁆
  factors_admissible :
    ∀ F ∈ factors,
      F.word.PBPos ∧
        F.multiplicity ∈
          submodule M N
            F.word.pairLeftDegree F.word.pairRightDegree

namespace CExp

/-- A faithful bare Lemma 4 expansion is also a trace-compatible collected
expansion. -/
def ofFreeExpansion
    {M N : ℕ}
    {G : Type*} [Group G]
    (E : FExp M N)
    (x y : G) :
    CExp M N x y where
  factors :=
    FExp.rawFactors E.factors
  eval_eq := by
    rw [FExp.list_raw_factors,
      E.list_commutator_pow]
  factors_admissible := by
    intro F hF
    rcases List.mem_map.mp hF with ⟨D, _hD, rfl⟩
    exact ⟨D.positive, D.coefficient_admissible⟩

/-- Prime-power admissibility turns a collected expansion into the public
trace object. -/
def toTrace
    {p A B : ℕ}
    {G : Type*} [Group G]
    {x y : G}
    (E : CExp (p ^ A) (p ^ B) x y) :
    PPColl.Trace p x y A B where
  factors :=
    E.factors
  eval_eq :=
    E.eval_eq
  factors_good := by
    intro F hF
    have h := E.factors_admissible F hF
    exact
      good_submodule_pow
        h.1.left h.1.right h.2

end CExp

namespace ANClos

/-- Arithmetic provenance carried by a raw factor in the conjugator-aware form
of Lemma 4. -/
def RawFactorAdmissible
    (M N : ℕ)
    {G : Type*} [Group G]
    (F : PPColl.RFactor G) :
    Prop :=
  F.word.PBPos ∧
    F.multiplicity ∈
      submodule M N
        F.word.pairLeftDegree F.word.pairRightDegree

/-- Outer conjugation does not change the arithmetic provenance of a factor. -/
lemma raw_admissible_conjugate
    {M N : ℕ}
    {G : Type*} [Group G]
    {F : PPColl.RFactor G}
    (hF : RawFactorAdmissible M N F)
    (q : G) :
    RawFactorAdmissible M N (F.conjugate q) :=
  hF

/-- Inversion preserves admissibility because each admissible coefficient set
is a submodule. -/
lemma raw_admissible_inv
    {M N : ℕ}
    {G : Type*} [Group G]
    {F : PPColl.RFactor G}
    (hF : RawFactorAdmissible M N F) :
    RawFactorAdmissible M N F.inv := by
  exact ⟨hF.1, (submodule M N _ _).neg_mem hF.2⟩

/-- Reversal and factorwise inversion preserve pointwise admissibility. -/
lemma forall_admissible_inv
    {M N : ℕ}
    {G : Type*} [Group G]
    {L : List (PPColl.RFactor G)}
    (hL : ∀ F ∈ L, RawFactorAdmissible M N F) :
    ∀ F ∈ PPColl.listInv L,
      RawFactorAdmissible M N F := by
  intro F hF
  induction L with
  | nil =>
      change F ∈ ([] : List (PPColl.RFactor G)) at hF
      contradiction
  | cons E L ih =>
      change
        F ∈ PPColl.listInv L ++ [E.inv] at hF
      rw [List.mem_append, List.mem_singleton] at hF
      rcases hF with hF | hF
      · exact ih (fun Z hZ => hL Z (by simp [hZ])) hF
      · subst F
        exact raw_admissible_inv (hL E (by simp))

/-- Evaluations of admissible factors. -/
def generatorSet
    (M N : ℕ)
    {G : Type*} [Group G]
    (x y : G) :
    Set G :=
  { g |
    ∃ F : PPColl.RFactor G,
      RawFactorAdmissible M N F ∧
        F.eval x y = g }

/-- Normal closure of the factors allowed by the conjugator-aware form of
Lemma 4. -/
def subgroup
    (M N : ℕ)
    {G : Type*} [Group G]
    (x y : G) :
    Subgroup G :=
  Subgroup.normalClosure (generatorSet M N x y)

instance subgro_normal
    (M N : ℕ)
    {G : Type*} [Group G]
    (x y : G) :
    (subgroup M N x y).Normal :=
  Subgroup.normalClosure_normal

/-- One admissible raw factor belongs to the admissible normal closure. -/
lemma raw_factor_eval
    {M N : ℕ}
    {G : Type*} [Group G]
    {x y : G}
    {F : PPColl.RFactor G}
    (hF : RawFactorAdmissible M N F) :
    F.eval x y ∈ subgroup M N x y := by
  apply Subgroup.subset_normalClosure
  exact ⟨F, hF, rfl⟩

/-- Transporting the ambient group leaves factor arithmetic provenance
unchanged. -/
lemma raw_admissible_hom
    {M N : ℕ}
    {G H : Type*} [Group G] [Group H]
    (φ : G →* H)
    (F : PPColl.RFactor G) :
    RawFactorAdmissible M N (F.mapHom φ) ↔
      RawFactorAdmissible M N F :=
  Iff.rfl

/-- Admissible normal-closure membership is functorial in the ambient group. -/
lemma map_mem
    {M N : ℕ}
    {G H : Type*} [Group G] [Group H]
    (φ : G →* H)
    {x y g : G}
    (hg : g ∈ subgroup M N x y) :
    φ g ∈ subgroup M N (φ x) (φ y) := by
  have hsubgroup :
      subgroup M N x y ≤
        (subgroup M N (φ x) (φ y)).comap φ := by
    apply Subgroup.normalClosure_le_normal
    intro z hz
    rcases hz with ⟨F, hF, rfl⟩
    change φ (F.eval x y) ∈ subgroup M N (φ x) (φ y)
    rw [← F.eval_mapHom φ x y]
    exact raw_factor_eval ((raw_admissible_hom φ F).2 hF)
  exact hsubgroup hg

/-- A bare powered Hall word belongs to the admissible normal closure when its
coefficient has the matching provenance. -/
lemma zpow_word_eval
    {M N : ℕ}
    {G : Type*} [Group G]
    (x y : G)
    (w : CWord HPAtom)
    (c : ℤ)
    (hpositive : w.PBPos)
    (hc :
      c ∈
        submodule M N
          w.pairLeftDegree w.pairRightDegree) :
    w.eval (HPAtom.eval x y) ^ c ∈
      subgroup M N x y := by
  simpa [PPColl.RFactor.eval] using
    (raw_factor_eval (x := x) (y := y)
      (F := {
        word := w
        multiplicity := c
        conjugator := 1 })
      ⟨hpositive, hc⟩)

/-- Admissible normal-closure membership is stable under conjugation. -/
lemma conj_mem
    {M N : ℕ}
    {G : Type*} [Group G]
    {x y g : G}
    (hg : g ∈ subgroup M N x y)
    (q : G) :
    q * g * q⁻¹ ∈ subgroup M N x y :=
  (inferInstance : (subgroup M N x y).Normal).conj_mem g hg q

/-- A commutator belongs to the admissible normal closure as soon as its left
input does. -/
lemma commutator_mem_left
    {M N : ℕ}
    {G : Type*} [Group G]
    {x y g : G}
    (hg : g ∈ subgroup M N x y)
    (q : G) :
    ⁅g, q⁆ ∈ subgroup M N x y :=
  Subgroup.commutator_le_left (subgroup M N x y) ⊤
    (Subgroup.commutator_mem_commutator hg (Subgroup.mem_top q))

/-- A commutator belongs to the admissible normal closure as soon as its right
input does. -/
lemma commutator_mem_right
    {M N : ℕ}
    {G : Type*} [Group G]
    {x y g : G}
    (q : G)
    (hg : g ∈ subgroup M N x y) :
    ⁅q, g⁆ ∈ subgroup M N x y :=
  Subgroup.commutator_le_right ⊤ (subgroup M N x y)
    (Subgroup.commutator_mem_commutator (Subgroup.mem_top q) hg)

/-- An ordered product of admissible raw factors belongs to the admissible
normal closure. -/
lemma listEval_mem
    {M N : ℕ}
    {G : Type*} [Group G]
    {x y : G} :
    ∀ {L : List (PPColl.RFactor G)},
      (∀ F ∈ L, RawFactorAdmissible M N F) →
        PPColl.listEval x y L ∈
          subgroup M N x y
  | [], _ =>
      (subgroup M N x y).one_mem
  | F :: L, hL =>
      (subgroup M N x y).mul_mem
        (raw_factor_eval (hL F (by simp)))
        (listEval_mem (fun E hE => hL E (by simp [hE])))

/-- Membership in the admissible normal closure extracts an exact ordered list
of admissible raw factors. -/
lemma list_eval
    {M N : ℕ}
    {G : Type*} [Group G]
    {x y g : G}
    (hg : g ∈ subgroup M N x y) :
    ∃ L : List (PPColl.RFactor G),
      PPColl.listEval x y L = g ∧
        ∀ F ∈ L, RawFactorAdmissible M N F := by
  change
    g ∈ Subgroup.closure
      (Group.conjugatesOfSet (generatorSet M N x y)) at hg
  induction hg using Subgroup.closure_induction with
  | mem z hz =>
      rcases Group.mem_conjugatesOfSet_iff.mp hz with ⟨v, hv, hconj⟩
      rcases hv with ⟨F, hF, hEval⟩
      rcases isConj_iff.mp hconj with ⟨q, rfl⟩
      refine ⟨[F.conjugate q], ?_, ?_⟩
      · simp [hEval]
      · intro E hE
        simp only [List.mem_singleton] at hE
        subst E
        exact raw_admissible_conjugate hF q
  | one =>
      exact ⟨[], rfl, by simp⟩
  | mul u v _hu _hv ihu ihv =>
      rcases ihu with ⟨L, hL, hLadmissible⟩
      rcases ihv with ⟨K, hK, hKadmissible⟩
      refine ⟨L ++ K, by simp [hL, hK], ?_⟩
      intro F hF
      rcases List.mem_append.mp hF with hF | hF
      · exact hLadmissible F hF
      · exact hKadmissible F hF
  | inv u _hu ihu =>
      rcases ihu with ⟨L, hL, hLadmissible⟩
      exact
        ⟨PPColl.listInv L, by simp [hL],
          forall_admissible_inv hLadmissible⟩

/-- The conjugator-aware normal-closure form of Lemma 4 produces an explicit
collected expansion. -/
lemma nonempty_expansion
    {M N : ℕ}
    {G : Type*} [Group G]
    (x y : G)
    (h :
      ⁅x ^ M, y ^ N⁆ ∈
        subgroup M N x y) :
    Nonempty (CExp M N x y) := by
  rcases list_eval h with ⟨L, hL, hLadmissible⟩
  exact ⟨{
    factors := L
    eval_eq := hL
    factors_admissible := hLadmissible }⟩

/-- A collected expansion witnesses membership of its target commutator in the
admissible normal closure. -/
lemma collected_expansion
    {M N : ℕ}
    {G : Type*} [Group G]
    {x y : G}
    (E : CExp M N x y) :
    ⁅x ^ M, y ^ N⁆ ∈
      subgroup M N x y := by
  rw [← E.eval_eq]
  exact listEval_mem E.factors_admissible

/-- The conjugator-aware form of Lemma 4 is exactly an admissible
normal-closure membership statement. -/
lemma nonempty_collected_expansion
    {M N : ℕ}
    {G : Type*} [Group G]
    (x y : G) :
    Nonempty (CExp M N x y) ↔
      ⁅x ^ M, y ^ N⁆ ∈
        subgroup M N x y := by
  constructor
  · rintro ⟨E⟩
    exact collected_expansion E
  · exact nonempty_expansion x y

/-- The admissible normal-closure statement at prime powers is sufficient for
the public trace theorem. -/
lemma trace_of_mem
    (p : ℕ)
    {G : Type*} [Group G]
    (x y : G)
    (A B : ℕ)
    (h :
      ⁅x ^ (p ^ A), y ^ (p ^ B)⁆ ∈
        subgroup (p ^ A) (p ^ B) x y) :
    Nonempty (PPColl.Trace p x y A B) := by
  obtain ⟨E⟩ := nonempty_expansion x y h
  exact ⟨E.toTrace⟩

end ANClos

/--
A proof of Lemma 4 immediately gives the public `nonempty_trace` theorem.
-/
lemma nonempty_trace
    (collectionExistence :
      ∀ M N : ℕ, 0 < M → 0 < N →
        Nonempty (FExp M N))
    (p : ℕ) [Fact p.Prime]
    {G : Type*} [Group G]
    (x y : G)
    (A B : ℕ) :
    Nonempty (PPColl.Trace p x y A B) := by
  obtain ⟨E⟩ :=
    collectionExistence (p ^ A) (p ^ B)
      (pow_pos (Fact.out : Nat.Prime p).pos A)
      (pow_pos (Fact.out : Nat.Prime p).pos B)
  exact ⟨E.toTrace x y⟩

end HACoeff
end Towers
