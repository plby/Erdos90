import Submission.Group.HallPetrescoCore

open scoped commutatorElement

namespace Submission
namespace PPColl

namespace TNClos

/-- Evaluations of factors carrying the exact two-sided Hall-Petresco
certificate required by a trace. -/
def generatorSet
    (p a b : ℕ)
    {G : Type*} [Group G]
    (x y : G) :
    Set G :=
  { g |
    ∃ F : RFactor G,
      F.Good p a b ∧
        F.eval x y = g }

/-- Normal closure of the factors permitted in a trace. -/
def subgroup
    (p a b : ℕ)
    {G : Type*} [Group G]
    (x y : G) :
    Subgroup G :=
  Subgroup.normalClosure (generatorSet p a b x y)

instance subgro_normal
    (p a b : ℕ)
    {G : Type*} [Group G]
    (x y : G) :
    (subgroup p a b x y).Normal :=
  Subgroup.normalClosure_normal

/-- Every element of the trace normal closure can be extracted as an exact
ordered list of certified raw factors. -/
lemma list_eval
    {p a b : ℕ}
    {G : Type*} [Group G]
    {x y g : G}
    (hg : g ∈ subgroup p a b x y) :
    ∃ L : List (RFactor G),
      listEval x y L = g ∧
        ∀ F ∈ L, F.Good p a b := by
  change
    g ∈ Subgroup.closure
      (Group.conjugatesOfSet (generatorSet p a b x y)) at hg
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
        exact hF.conjugate q
  | one =>
      exact ⟨[], rfl, by simp⟩
  | mul u v _hu _hv ihu ihv =>
      rcases ihu with ⟨L, hL, hLgood⟩
      rcases ihv with ⟨M, hM, hMgood⟩
      refine ⟨L ++ M, by simp [hL, hM], ?_⟩
      intro F hF
      rcases List.mem_append.mp hF with hF | hF
      · exact hLgood F hF
      · exact hMgood F hF
  | inv u _hu ihu =>
      rcases ihu with ⟨L, hL, hLgood⟩
      exact ⟨listInv L, by simp [hL], forall_good_inv hLgood⟩

/-- Membership of the target commutator in the trace normal closure is the
remaining pure group-theoretic statement needed for `nonempty_trace`. -/
lemma trace_of_mem
    (p : ℕ)
    {G : Type*} [Group G]
    (x y : G)
    (a b : ℕ)
    (h :
      ⁅x ^ (p ^ a), y ^ (p ^ b)⁆ ∈
        subgroup p a b x y) :
    Nonempty (Trace p x y a b) := by
  rcases list_eval h with ⟨L, hL, hLgood⟩
  exact ⟨{
    factors := L
    eval_eq := hL
    factors_good := hLgood }⟩

end TNClos

namespace CRList

/-- Repeat an exact raw-factor list without distributing the outer power over
its noncommuting entries. -/
def pow
    {G : Type*} [Group G]
    (L : List (RFactor G)) :
    ℕ → List (RFactor G)
  | 0 => []
  | n + 1 => pow L n ++ L

@[simp]
lemma listEval_pow
    {G : Type*} [Group G]
    (x y : G)
    (L : List (RFactor G))
    (n : ℕ) :
    listEval x y (pow L n) = (listEval x y L) ^ n := by
  induction n with
  | zero =>
      simp [pow]
  | succ n ih =>
      simp [pow, ih, pow_succ]

/-- Repeat or reverse-and-invert an exact raw-factor list according to an
integral outer multiplicity. -/
def zpow
    {G : Type*} [Group G]
    (L : List (RFactor G)) :
    ℤ → List (RFactor G)
  | Int.ofNat n => pow L n
  | Int.negSucc n => listInv (pow L (n + 1))

@[simp]
lemma listEval_zpow
    {G : Type*} [Group G]
    (x y : G)
    (L : List (RFactor G))
    (c : ℤ) :
    listEval x y (zpow L c) = (listEval x y L) ^ c := by
  cases c with
  | ofNat n =>
      simp [zpow]
  | negSucc n =>
      simp [zpow]

/-- Repetition preserves a pointwise Hall-Petresco certificate already
attached to every raw factor. -/
lemma forall_good_pow
    {p a b : ℕ}
    {G : Type*} [Group G]
    {L : List (RFactor G)}
    (hL : ∀ E ∈ L, E.Good p a b) :
    ∀ n E, E ∈ pow L n → E.Good p a b := by
  intro n
  induction n with
  | zero =>
      simp [pow]
  | succ n ih =>
      intro E hE
      rw [pow, List.mem_append] at hE
      rcases hE with hE | hE
      · exact ih E hE
      · exact hL E hE

/-- An outer integral multiplicity preserves existing pointwise
certificates while keeping the represented product correlated. -/
lemma forall_good_zpow
    {p a b : ℕ}
    {G : Type*} [Group G]
    {L : List (RFactor G)}
    (hL : ∀ E ∈ L, E.Good p a b)
    (c : ℤ) :
    ∀ E ∈ zpow L c, E.Good p a b := by
  cases c with
  | ofNat n =>
      exact forall_good_pow hL n
  | negSucc n =>
      exact forall_good_inv (forall_good_pow hL (n + 1))

end CRList

namespace RCColl
namespace RPAggreg
namespace BNClos

/-- Weakening either coordinate divisor enlarges the bidegree normal
closure. -/
lemma subgroup_mono_dvd
    {A A' B B' : ℤ}
    (hA : A' ∣ A)
    (hB : B' ∣ B) :
    subgroup A B ≤ subgroup A' B' := by
  apply Subgroup.normalClosure_mono
  rintro g ⟨u, c, hpositive, hleft, hright, rfl⟩
  exact
    ⟨u, c, hpositive, dvd_trans hA hleft, dvd_trans hB hright, rfl⟩

/-- Every element of a bidegree normal closure remains there after
conjugation by an arbitrary universal word. -/
lemma conj_mem
    {A B : ℤ}
    {g : UniversalGroup}
    (hg : g ∈ subgroup A B)
    (q : UniversalGroup) :
    q * g * q⁻¹ ∈ subgroup A B :=
  (inferInstance : (subgroup A B).Normal).conj_mem g hg q

/-- A commutator belongs to a bidegree normal closure as soon as its left
input does. -/
lemma commutator_mem_left
    {A B : ℤ}
    {g : UniversalGroup}
    (hg : g ∈ subgroup A B)
    (q : UniversalGroup) :
    ⁅g, q⁆ ∈ subgroup A B := by
  exact
    Subgroup.commutator_le_left (subgroup A B) ⊤
      (Subgroup.commutator_mem_commutator hg (Subgroup.mem_top q))

/-- A commutator belongs to a bidegree normal closure as soon as its right
input does. -/
lemma commutator_mem_right
    {A B : ℤ}
    (q : UniversalGroup)
    {g : UniversalGroup}
    (hg : g ∈ subgroup A B) :
    ⁅q, g⁆ ∈ subgroup A B := by
  exact
    Subgroup.commutator_le_right ⊤ (subgroup A B)
      (Subgroup.commutator_mem_commutator (Subgroup.mem_top q) hg)

/-- A one-hole context for replacing one branch inside a Hall-pair
commutator word. -/
inductive WContex where
  | hole : WContex
  | commutatorLeft :
      WContex → CWord HPAtom → WContex
  | commutatorRight :
      CWord HPAtom → WContex → WContex

namespace WContex

/-- Fill the unique hole of a commutator-word context. -/
def plug :
    WContex → CWord HPAtom →
      CWord HPAtom
  | .hole, u =>
      u
  | .commutatorLeft K v, u =>
      .commutator (K.plug u) v
  | .commutatorRight u K, v =>
      .commutator u (K.plug v)

/-- Normal-closure membership is absorbed by every surrounding
commutator-word context. -/
lemma eval_plug
    {A B : ℤ}
    (f : HPAtom → UniversalGroup)
    (K : WContex)
    {u : CWord HPAtom}
    (hu : u.eval f ∈ subgroup A B) :
    (K.plug u).eval f ∈ subgroup A B := by
  induction K generalizing u with
  | hole =>
      exact hu
  | commutatorLeft K v ih =>
      exact commutator_mem_left (ih hu) (v.eval f)
  | commutatorRight v K ih =>
      exact commutator_mem_right (v.eval f) (ih hu)

end WContex

/-!
### Quotient-level transport experiment

The next helpers deliberately stay at normal-closure membership.  They test
whether grouped powers and commutators can replace the abandoned leafwise
marked-factor traversal.
-/

/-- Products, inverses, and conjugates of target members stay in the target
normal closure. -/
lemma mul_mem
    {A B : ℤ}
    {g h : UniversalGroup}
    (hg : g ∈ subgroup A B)
    (hh : h ∈ subgroup A B) :
    g * h ∈ subgroup A B :=
  (subgroup A B).mul_mem hg hh

lemma inv_mem
    {A B : ℤ}
    {g : UniversalGroup}
    (hg : g ∈ subgroup A B) :
    g⁻¹ ∈ subgroup A B :=
  (subgroup A B).inv_mem hg

/-- Integral powers of a target member remain in the target normal closure. -/
lemma zpow_mem
    {A B : ℤ}
    {g : UniversalGroup}
    (hg : g ∈ subgroup A B)
    (c : ℤ) :
    g ^ c ∈ subgroup A B :=
  (subgroup A B).zpow_mem hg c

/-- An ordered product remains in the target when every list entry does. -/
lemma list_prod_mem
    {A B : ℤ} :
    ∀ {L : List UniversalGroup},
      (∀ g ∈ L, g ∈ subgroup A B) →
        L.prod ∈ subgroup A B
  | [], _ => (subgroup A B).one_mem
  | g :: L, hL =>
      (subgroup A B).mul_mem
        (hL g (by simp))
        (list_prod_mem (fun h hh => hL h (by simp [hh])))

/-- The existing Hall-orbit criterion can be used directly with a bidegree
target normal closure, without extracting its pairwise-error prefix into
independent raw factors. -/
lemma left_conjugate_product
    {A B : ℤ}
    {x c : UniversalGroup}
    (n : ℕ)
    (hcomm :
      ∀ r s : ℕ,
        ⁅leftIteratedElement x c r,
            leftIteratedElement x c s⁆ ∈ subgroup A B)
    (hfactor :
      ∀ r : ℕ, r < n →
        leftIteratedElement x c r ^ Nat.choose n (r + 1) ∈
          subgroup A B) :
    leftConjugateProduct x c n ∈ subgroup A B :=
  conjugate_pairwise_choose
    (subgroup A B) n hcomm hfactor

/-- It is enough to prove the right-prime image of each normalized
bidegree generator. -/
lemma right_prime_generator
    (p : ℕ)
    {A B : ℤ}
    (hgenerator :
      ∀ (u : CWord HPAtom) (c : ℤ),
        u.PBPos →
          A ∣ (u.pairLeftDegree : ℤ) * c →
            B ∣ (u.pairRightDegree : ℤ) * c →
              rightPrimeHom p
                  (u.eval
                      (HPAtom.eval universalLeft universalRight) ^ c) ∈
                subgroup A ((p : ℤ) * B)) :
    ∀ {g : UniversalGroup},
      g ∈ subgroup A B →
      rightPrimeHom p g ∈ subgroup A ((p : ℤ) * B) :=
  right_hom_generator p hgenerator

/-- The swapped basic orbit has separated coordinates: its `k`th repeated-left
suffix factor has left degree one and right degree `k`.  The elementary
identity `p ∣ k * choose p k` therefore gives the exact bidegree certificate
needed by the right-prime target normal closure. -/
lemma swapped_choose_suffix
    (p : ℕ) [Fact p.Prime]
    {A B c : ℤ}
    (hleft : A ∣ c)
    (hright : B ∣ c)
    (r : ℕ) :
    (CWord.hallPairBind
          (.atom HPAtom.right)
          (.atom HPAtom.left)
          (CWord.pairLeftIterate r)).eval
        (HPAtom.eval universalLeft universalRight) ^
          (((Nat.choose p (r + 1) : ℕ) : ℤ) * c) ∈
      subgroup A ((p : ℤ) * B) := by
  apply zpow_word_eval
  · simp [CWord.PBPos]
  · simpa using dvd_mul_of_dvd_right hleft ((Nat.choose p (r + 1) : ℕ) : ℤ)
  · have hpNat : p ∣ (r + 1) * Nat.choose p (r + 1) := by
      simpa using
        (HPGood.dvd_choose_nat
          (p := p) (A := 1) (k := r + 1))
    have hp :
        (p : ℤ) ∣ ((r + 1 : ℕ) : ℤ) * ((Nat.choose p (r + 1) : ℕ) : ℤ) := by
      exact_mod_cast hpNat
    simpa [mul_assoc] using mul_dvd_mul hp hright

/-- Extracted choose terms retain an additional integral multiplicity.  It
can be absorbed into the source coefficient without weakening either exact
coordinate certificate. -/
lemma swapped_choose_zpow
    (p : ℕ) [Fact p.Prime]
    {A B c : ℤ}
    (hleft : A ∣ c)
    (hright : B ∣ c)
    (T :
      CPTerm
        universalRight
        ⁅universalRight, universalLeft⁆
        p) :
    T.eval ^ c ∈ subgroup A ((p : ℤ) * B) := by
  simpa [CPTerm.eval, ← zpow_natCast, ← zpow_mul, mul_assoc] using
    (swapped_choose_suffix p
      (dvd_mul_of_dvd_right hleft T.multiplicity)
      (dvd_mul_of_dvd_right hright T.multiplicity)
      T.index)

/-- The pairwise errors generated while collecting the swapped basic orbit
have original Hall-pair bidegree `(2, r + s + 2)`.  Unlike the choose suffix,
an individual error need not gain a right-hand factor of `p`. -/
lemma swapped_error_bidegree
    (r s : ℕ) :
    let u :=
      CWord.hallPairBind
        (.atom HPAtom.right)
        (.atom HPAtom.left)
        (CWord.iteratePairwiseError r s)
    u.pairLeftDegree = 2 ∧
      u.pairRightDegree = r + s + 2 := by
  simp

/-- At `p = 3`, the `(r,s) = (0,2)` swapped pairwise error is a concrete
example that fails the leafwise right-divisibility target. -/
lemma swapped_error_leafwise :
    let u :=
      CWord.hallPairBind
        (.atom HPAtom.right)
        (.atom HPAtom.left)
        (CWord.iteratePairwiseError 0 2)
    ¬ (3 : ℤ) ∣ (u.pairRightDegree : ℤ) := by
  norm_num

/-- A swapped basic iterate enters the exact right target as soon as its
right degree `r + 1` is divisible by `p`. -/
lemma swapped_iterate_dvd
    (p r : ℕ)
    (hright : (p : ℤ) ∣ ((r + 1 : ℕ) : ℤ)) :
    (CWord.hallPairBind
          (.atom HPAtom.right)
          (.atom HPAtom.left)
          (CWord.pairLeftIterate r)).eval
        (HPAtom.eval universalLeft universalRight) ∈
      subgroup 1 (p : ℤ) := by
  simpa using
    (zpow_word_eval
      (CWord.hallPairBind
        (.atom HPAtom.right)
        (.atom HPAtom.left)
        (CWord.pairLeftIterate r))
      1
      (by simp [CWord.PBPos])
      (by simp)
      (by simpa using hright))

/-- A swapped pairwise error is absorbed whenever its first iterated input
already lies in the target normal closure. -/
lemma swapped_error_dvd
    (p r s : ℕ)
    (hright : (p : ℤ) ∣ ((r + 1 : ℕ) : ℤ)) :
    (CWord.hallPairBind
          (.atom HPAtom.right)
          (.atom HPAtom.left)
          (CWord.iteratePairwiseError r s)).eval
        (HPAtom.eval universalLeft universalRight) ∈
      subgroup 1 (p : ℤ) := by
  exact
    commutator_mem_left
      (swapped_iterate_dvd p r hright)
      ((CWord.hallPairBind
          (.atom HPAtom.right)
          (.atom HPAtom.left)
          (CWord.pairLeftIterate s)).eval
        (HPAtom.eval universalLeft universalRight))

/-- A swapped pairwise error is absorbed whenever its second iterated input
already lies in the target normal closure. -/
lemma swapped_pairwise_error
    (p r s : ℕ)
    (hright : (p : ℤ) ∣ ((s + 1 : ℕ) : ℤ)) :
    (CWord.hallPairBind
          (.atom HPAtom.right)
          (.atom HPAtom.left)
          (CWord.iteratePairwiseError r s)).eval
        (HPAtom.eval universalLeft universalRight) ∈
      subgroup 1 (p : ℤ) := by
  exact
    commutator_mem_right
      ((CWord.hallPairBind
          (.atom HPAtom.right)
          (.atom HPAtom.left)
          (CWord.pairLeftIterate r)).eval
        (HPAtom.eval universalLeft universalRight))
      (swapped_iterate_dvd p s hright)

/-- Even when neither iterated input is separately absorbed, a swapped
pairwise error enters the target directly when its total right degree is
divisible by `p`. -/
lemma swapped_pairwise_dvd
    (p r s : ℕ)
    (hright : (p : ℤ) ∣ ((r + s + 2 : ℕ) : ℤ)) :
    (CWord.hallPairBind
          (.atom HPAtom.right)
          (.atom HPAtom.left)
          (CWord.iteratePairwiseError r s)).eval
        (HPAtom.eval universalLeft universalRight) ∈
      subgroup 1 (p : ℤ) := by
  simpa using
    (zpow_word_eval
      (CWord.hallPairBind
        (.atom HPAtom.right)
        (.atom HPAtom.left)
        (CWord.iteratePairwiseError r s))
      1
      (by simp [CWord.PBPos])
      (by simp)
      (by simpa using hright))

namespace ERDegree

/-- Evaluated positive Hall words with one fixed right Hall-pair degree. -/
def generatorSet
    (r : ℕ) :
    Set UniversalGroup :=
  { g |
    ∃ u : CWord HPAtom,
      u.PBPos ∧
        u.pairRightDegree = r ∧
          u.eval (HPAtom.eval universalLeft universalRight) = g }

/-- Normal closure of the positive Hall words with one fixed right degree. -/
def subgroup
    (r : ℕ) :
    Subgroup UniversalGroup :=
  Subgroup.normalClosure (generatorSet r)

instance subgro_normal
    (r : ℕ) :
    (subgroup r).Normal :=
  Subgroup.normalClosure_normal

/-- A positive Hall word belongs to its exact-right-degree normal closure. -/
lemma wordEval_mem
    (u : CWord HPAtom)
    (hpositive : u.PBPos) :
    u.eval (HPAtom.eval universalLeft universalRight) ∈
      subgroup u.pairRightDegree := by
  apply Subgroup.subset_normalClosure
  exact ⟨u, hpositive, rfl, rfl⟩

/-- An exact right-degree layer divisible by `p` is contained in the
coordinatewise target normal closure `subgroup 1 p`. -/
lemma subg_bide_one
    (p r : ℕ)
    (hr : (p : ℤ) ∣ (r : ℤ)) :
    subgroup r ≤
      BNClos.subgroup 1 (p : ℤ) := by
  apply Subgroup.normalClosure_le_normal
  rintro _ ⟨u, hpositive, hdegree, rfl⟩
  simpa using
    (BNClos.zpow_word_eval
      (A := 1) (B := (p : ℤ)) u 1 hpositive
      (by simp)
      (by simpa [hdegree] using hr))

/-- Bracketing two exact-degree Hall generators produces a generator in the
summed exact-degree layer. -/
lemma comm_word_eva
    {u v : CWord HPAtom}
    (hu : u.PBPos)
    (_hv : v.PBPos) :
    ⁅u.eval (HPAtom.eval universalLeft universalRight),
        v.eval (HPAtom.eval universalLeft universalRight)⁆ ∈
      subgroup (u.pairRightDegree + v.pairRightDegree) := by
  exact
    wordEval_mem (.commutator u v)
      ⟨Nat.add_pos_left hu.left _, Nat.add_pos_left hu.right _⟩

end ERDegree

namespace HRDegree

/-- Evaluated positive Hall words whose right Hall-pair degree is at least a
chosen cutoff. -/
def generatorSet
    (cutoff : ℕ) :
    Set UniversalGroup :=
  { g |
    ∃ u : CWord HPAtom,
      u.PBPos ∧
        cutoff ≤ u.pairRightDegree ∧
          u.eval (HPAtom.eval universalLeft universalRight) = g }

/-- Normal closure of positive Hall words above a right-degree cutoff. -/
def subgroup
    (cutoff : ℕ) :
    Subgroup UniversalGroup :=
  Subgroup.normalClosure (generatorSet cutoff)

instance subgro_normal
    (cutoff : ℕ) :
    (subgroup cutoff).Normal :=
  Subgroup.normalClosure_normal

/-- A positive Hall word belongs to every high-right-degree layer below its
own right degree. -/
lemma wordEval_mem
    {cutoff : ℕ}
    (u : CWord HPAtom)
    (hpositive : u.PBPos)
    (hdegree : cutoff ≤ u.pairRightDegree) :
    u.eval (HPAtom.eval universalLeft universalRight) ∈
      subgroup cutoff := by
  apply Subgroup.subset_normalClosure
  exact ⟨u, hpositive, hdegree, rfl⟩

/-- Raising the right-degree cutoff shrinks the high-degree normal closure. -/
lemma antitone :
    Antitone subgroup := by
  intro r s hrs
  apply Subgroup.normalClosure_mono
  rintro _ ⟨u, hpositive, hdegree, rfl⟩
  exact ⟨u, hpositive, hrs.trans hdegree, rfl⟩

/-- An exact-right-degree layer lies in the corresponding high-degree
filtration layer. -/
lemma exac_righ_deg
    (r : ℕ) :
    ERDegree.subgroup r ≤ subgroup r := by
  apply Subgroup.normalClosure_le_normal
  rintro _ ⟨u, hpositive, hdegree, rfl⟩
  exact wordEval_mem u hpositive (by simp [hdegree])

end HRDegree

end BNClos
end RPAggreg
end RCColl

end PPColl
end Submission
